//! One step of a four-channel command-word comparison scheme.
//!
//! Consistent with the open-source description of "Biser-4" (NIIAP): four
//! machines run the same programs in lock-step, an output comparison scheme
//! blocks a channel that has failed, and the design is rated for two
//! failures (degradation 4 -> 3 -> 2). The source does **not** say how the
//! comparison scheme decides which channel is at fault, nor what it does
//! when only a disagreeing pair remains; those two points are this crate's
//! own modelling choices ("OURS" below), not facts about "Biser-4". See
//! `README.md` and `reports/PROOF.md` for the full source/ours breakdown
//! and for what this crate does **not** prove.
//!
//! [`step`] is the only public entry point Aeneas extracts a no-panic and
//! functional-correctness claim about. It has no loop, no recursion, no
//! allocation, and no `unsafe`: every branch is a fixed comparison among the
//! four fixed-size input slots, so Charon/Aeneas see a finite decision tree.
//! A multi-step trace is not a Rust loop in this crate — `reports/PROOF.md`
//! builds it in Lean as a fold over the extracted [`step`], which the
//! specification explicitly allows.

#![no_std]
#![forbid(unsafe_code)]
#![deny(missing_docs)]

/// Command word carried by one channel in a single comparison cycle.
///
/// SOURCE: the "Biser-4" command words to peripheral devices ("kodogrammy"
/// in the source) are described as 36 bits wide.
///
/// OURS: no built-in Rust integer type is exactly 36 bits. `u64` is the
/// smallest built-in type that represents every 36-bit value without
/// truncation (`u32::MAX` is smaller than `2^36 - 1`). The model compares
/// words only for whole-word equality and never inspects individual bits or
/// a numeric range, so using a 64-bit container instead of a hypothetical
/// 36-bit one changes no property proved in `reports/PROOF.md`. The type
/// does not enforce a `< 2^36` range.
pub type Word = u64;

/// Which of the four channels (indices `0..=3`) are currently active.
/// `active[i]` is `true` iff channel `i` is still switched on.
///
/// SOURCE: "Biser-4" is a four-channel scheme with 4 -> 3 -> 2 degradation
/// as channels are switched off.
///
/// OURS: a channel switched off by [`step`] never comes back — there is no
/// rule in this model that turns a `false` back into a `true`. This is a
/// deliberate divergence from the "Biser" family, where "Biser-2" restored
/// a faulty grain by copying RAM across the inter-channel link after a
/// transient upset (NB); this model represents permanent failures, not
/// transient upsets with recovery. See `reports/PROOF.md`.
pub type ActiveSet = [bool; 4];

/// Outcome of one comparison-scheme step over the current [`ActiveSet`] and
/// one command word per channel.
///
/// Every variant carries the active set the scheme continues with after the
/// step (`active` field), so a trace is simply repeated application of
/// [`step`] threading this field through.
// `Debug` is `#[cfg_attr(test, derive(Debug))]`, not unconditional: an
// unconditional derive pulls in `core::fmt` array-formatting machinery
// during Charon extraction for no reason this crate's proof needs. Not the
// cause of this crate's hundred-megabyte-scale LLBC bloat (that was an
// `&&`-chained `if`/`else if` ladder — see the note on `triple_step` and
// `reports/EXTRACT.md`): isolated by comparing two `&&`-chain runs, an
// unconditional `Debug` derive changed the LLBC by only 120,158 bytes
// (≈0.018% of a ≈662 MB file) — real, but not why that file was ≈662 MB.
// Gated anyway, for the same reason `cose-parse-nopanic` avoids `Debug` on
// types with slices: no unused `core::fmt` axiom surface.
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(test, derive(Debug))]
pub enum StepResult {
    /// Every active channel produced the same word.
    ///
    /// SOURCE: this is the ordinary case — all channels agree, nothing is
    /// switched off. OURS: generalised without contradiction to zero or one
    /// active channel, where "agreement" holds vacuously; the zero-channel
    /// case is otherwise the separate [`StepResult::NoActiveChannels`]
    /// variant so that callers cannot confuse "one real vote" with "no
    /// vote at all".
    Agreed {
        /// The value every active channel produced (or, for one active
        /// channel, that channel's own value).
        command: Word,
        /// Active set after the step: identical to the input.
        active: ActiveSet,
    },
    /// At least three channels were active; exactly one active channel
    /// disagreed with the rest, who agreed among themselves.
    ///
    /// SOURCE: "Biser-4" blocks the output of a channel that has failed.
    ///
    /// OURS: identification of *which* channel is at fault is by simple
    /// majority among the active channels. The primary source for
    /// "Biser-4" says only that the scheme "blocks" a failed channel and
    /// does not say how it decides which one; a majority rule is this
    /// crate's own reconstruction, not a documented mechanism. See
    /// `reports/PROOF.md`.
    Majority {
        /// The value the surviving majority produced.
        command: Word,
        /// Index (`0..=3`) of the channel this step switches off.
        disabled: u8,
        /// Active set after the step: the input with `disabled` cleared.
        active: ActiveSet,
    },
    /// Exactly two channels were active and they disagreed.
    ///
    /// OURS: the source does not describe pair behaviour at all, so this
    /// crate reports an explicit "not determined by the source" result
    /// instead of guessing a tie-breaking rule. No command is produced and
    /// the active set is unchanged (this model does not go below two
    /// channels).
    Undetermined {
        /// Active set after the step: identical to the input (still both
        /// channels active).
        active: ActiveSet,
    },
    /// A disagreement pattern that is neither "all agree" nor "exactly one
    /// disagrees with an agreeing rest": a 2-2 or 2-1-1 split among four
    /// active channels, or three active channels that are all pairwise
    /// different.
    ///
    /// OURS: this crate's own decision to report an explicit "outside the
    /// failure hypothesis" result with no chosen command and no channel
    /// switched off, rather than pick a command by an undocumented
    /// tie-break. Not a behaviour attributed to "Biser-4".
    OutsideHypothesis {
        /// Active set after the step: identical to the input.
        active: ActiveSet,
    },
    /// No channel was active in the input.
    ///
    /// OURS: kept as its own variant, distinct from [`StepResult::Agreed`],
    /// purely so [`step`] is a total function over every possible
    /// [`ActiveSet`], including ones that cannot arise from a trace
    /// starting at four active channels (see `reports/PROOF.md`). No
    /// theorem in `reports/PROOF.md` is stated about this variant.
    NoActiveChannels {
        /// Active set after the step: identical to the input (still empty).
        active: ActiveSet,
    },
}

/// Clears index `index` (`0..=3`) of `active` and returns the result.
///
/// `index` is always one of the four fixed channel indices at every call
/// site in this crate; the `else` arm covers index `3` so the function is
/// total without an out-of-range case.
fn disable(mut active: ActiveSet, index: u8) -> ActiveSet {
    if index == 0 {
        active[0] = false;
    } else if index == 1 {
        active[1] = false;
    } else if index == 2 {
        active[2] = false;
    } else {
        active[3] = false;
    }
    active
}

/// Resolves a step in which exactly two channels are active.
fn pair_step(wa: Word, wb: Word, active: ActiveSet) -> StepResult {
    if wa == wb {
        StepResult::Agreed {
            command: wa,
            active,
        }
    } else {
        StepResult::Undetermined { active }
    }
}

/// Resolves a step in which exactly three channels — indices `ia`, `ib`,
/// `ic` with words `wa`, `wb`, `wc` — are active.
///
/// Implementation note: the three pairwise comparisons are computed once
/// into named booleans and then dispatched with a `match` on the `(bool,
/// bool, bool)` tuple, rather than a chain of `if wa == wb && wb == wc`
/// conditions. An `&&`-chained `if`/`else if` ladder of this shape made
/// Charon's extracted control-flow graph for [`step`] hundreds of megabytes
/// (see `reports/EXTRACT.md`); the `match` form does not.
#[allow(clippy::too_many_arguments)]
fn triple_step(
    ia: u8,
    wa: Word,
    ib: u8,
    wb: Word,
    ic: u8,
    wc: Word,
    active: ActiveSet,
) -> StepResult {
    let eq_ab = wa == wb;
    let eq_ac = wa == wc;
    let eq_bc = wb == wc;
    match (eq_ab, eq_ac, eq_bc) {
        (true, true, true) => StepResult::Agreed {
            command: wa,
            active,
        },
        // wa == wb, wa != wc (so wb != wc too): `ic` is the odd one out.
        (true, false, false) => StepResult::Majority {
            command: wa,
            disabled: ic,
            active: disable(active, ic),
        },
        // wa == wc, wa != wb: `ib` is the odd one out.
        (false, true, false) => StepResult::Majority {
            command: wa,
            disabled: ib,
            active: disable(active, ib),
        },
        // wb == wc, wa != wb: `ia` is the odd one out.
        (false, false, true) => StepResult::Majority {
            command: wb,
            disabled: ia,
            active: disable(active, ia),
        },
        // Every other combination of the three pairwise-equality flags is
        // unreachable for real `==` (equality is transitive: e.g.
        // `eq_ab && eq_bc` forces `eq_ac`), and the only reachable case left
        // over — all three flags false — is "all pairwise different". Both
        // fall through to the same no-command result, so no case is missed.
        _ => StepResult::OutsideHypothesis { active },
    }
}

/// Resolves a step in which all four channels are active.
///
/// Implementation note: same reasoning as [`triple_step`] — the six
/// pairwise comparisons are named booleans, dispatched with a `match`
/// instead of an `&&`-chained `if`/`else if` ladder.
fn quad_step(words: [Word; 4], active: ActiveSet) -> StepResult {
    let w0 = words[0];
    let w1 = words[1];
    let w2 = words[2];
    let w3 = words[3];
    let eq01 = w0 == w1;
    let eq02 = w0 == w2;
    let eq03 = w0 == w3;
    let eq12 = w1 == w2;
    let eq13 = w1 == w3;
    let eq23 = w2 == w3;
    match (eq01, eq02, eq03, eq12, eq13, eq23) {
        // w0 == w1 == w2 == w3 (eq12/eq13/eq23 follow from eq01/eq02/eq03
        // by transitivity, so they are not tested here).
        (true, true, true, _, _, _) => StepResult::Agreed {
            command: w0,
            active,
        },
        // {0,1,2} agree on w0; channel 3 differs.
        (true, true, false, _, _, _) => StepResult::Majority {
            command: w0,
            disabled: 3,
            active: disable(active, 3),
        },
        // {0,1,3} agree on w0; channel 2 differs.
        (true, false, true, _, _, _) => StepResult::Majority {
            command: w0,
            disabled: 2,
            active: disable(active, 2),
        },
        // {0,2,3} agree on w0; channel 1 differs.
        (false, true, true, _, _, _) => StepResult::Majority {
            command: w0,
            disabled: 1,
            active: disable(active, 1),
        },
        // {1,2,3} agree on w1, w0 differs from all three of them.
        (false, false, false, true, true, true) => StepResult::Majority {
            command: w1,
            disabled: 0,
            active: disable(active, 0),
        },
        // Every other combination: a 2-2 split, a 2-1-1 split, all four
        // different, or (for the six-flag tuple) a combination that real
        // `==` can never actually produce. All fall through to the same
        // no-command result.
        _ => StepResult::OutsideHypothesis { active },
    }
}

/// One comparison-scheme step: given which channels are currently active
/// and the command word each of the four channels produced this cycle,
/// returns the chosen command (if any), which channel (if any) is switched
/// off, and the active set to continue with.
///
/// No loop, no recursion, no allocation, no `unsafe`; every input has a
/// well-defined output ([`StepResult`] is never a panic — see `T1` in
/// `reports/PROOF.md`).
///
/// # Examples
///
/// `StepResult` derives `Debug` only under `cfg(test)` (see the note on the
/// type), so these examples match on the result instead of using
/// `assert_eq!`, which would require `Debug` here too.
///
/// ```
/// use quad_voter_proof::{step, StepResult};
///
/// // All four channels agree: command 7, nobody switched off.
/// let result = step([true, true, true, true], [7, 7, 7, 7]);
/// assert!(matches!(
///     result,
///     StepResult::Agreed {
///         command: 7,
///         active: [true, true, true, true]
///     }
/// ));
///
/// // Channel 2 disagrees with the other three: it is switched off.
/// let result = step([true, true, true, true], [7, 7, 9, 7]);
/// assert!(matches!(
///     result,
///     StepResult::Majority {
///         command: 7,
///         disabled: 2,
///         active: [true, true, false, true]
///     }
/// ));
///
/// // A disagreeing pair: the source does not say what happens.
/// let result = step([true, false, false, true], [1, 0, 0, 2]);
/// assert!(matches!(
///     result,
///     StepResult::Undetermined {
///         active: [true, false, false, true]
///     }
/// ));
/// ```
///
/// Implementation note: dispatch on the active pattern is a `match` on the
/// `(bool, bool, bool, bool)` tuple of `active`, not an `&&`-chained
/// `if`/`else if` ladder — see the note on [`triple_step`].
#[must_use]
pub fn step(active: ActiveSet, words: [Word; 4]) -> StepResult {
    let a0 = active[0];
    let a1 = active[1];
    let a2 = active[2];
    let a3 = active[3];
    match (a0, a1, a2, a3) {
        (true, true, true, true) => quad_step(words, active),
        (true, true, true, false) => triple_step(0, words[0], 1, words[1], 2, words[2], active),
        (true, true, false, true) => triple_step(0, words[0], 1, words[1], 3, words[3], active),
        (true, false, true, true) => triple_step(0, words[0], 2, words[2], 3, words[3], active),
        (false, true, true, true) => triple_step(1, words[1], 2, words[2], 3, words[3], active),
        (true, true, false, false) => pair_step(words[0], words[1], active),
        (true, false, true, false) => pair_step(words[0], words[2], active),
        (true, false, false, true) => pair_step(words[0], words[3], active),
        (false, true, true, false) => pair_step(words[1], words[2], active),
        (false, true, false, true) => pair_step(words[1], words[3], active),
        (false, false, true, true) => pair_step(words[2], words[3], active),
        (true, false, false, false) => StepResult::Agreed {
            command: words[0],
            active,
        },
        (false, true, false, false) => StepResult::Agreed {
            command: words[1],
            active,
        },
        (false, false, true, false) => StepResult::Agreed {
            command: words[2],
            active,
        },
        (false, false, false, true) => StepResult::Agreed {
            command: words[3],
            active,
        },
        (false, false, false, false) => StepResult::NoActiveChannels { active },
    }
}

#[cfg(test)]
mod tests {
    use super::{step, ActiveSet, StepResult, Word};

    /// Independent reference implementation of the same rules, written by
    /// counting value multiplicities among the active channels instead of
    /// `step`'s branch-by-branch case split. Used only by
    /// [`step_matches_oracle_exhaustively`]; not part of the extracted
    /// crate (test-only, `cfg(test)`).
    fn oracle(active: ActiveSet, words: [Word; 4]) -> StepResult {
        let mut count = 0usize;
        let mut idxs = [0usize; 4];
        let mut vals = [0u64; 4];
        for i in 0..4 {
            if active[i] {
                idxs[count] = i;
                vals[count] = words[i];
                count += 1;
            }
        }
        match count {
            0 => StepResult::NoActiveChannels { active },
            1 => StepResult::Agreed {
                command: vals[0],
                active,
            },
            2 => {
                if vals[0] == vals[1] {
                    StepResult::Agreed {
                        command: vals[0],
                        active,
                    }
                } else {
                    StepResult::Undetermined { active }
                }
            }
            3 => {
                let mut cnt = [0u8; 3];
                for i in 0..3 {
                    for j in 0..3 {
                        if vals[i] == vals[j] {
                            cnt[i] += 1;
                        }
                    }
                }
                if cnt[0] == 3 {
                    StepResult::Agreed {
                        command: vals[0],
                        active,
                    }
                } else if let Some(maj) = (0..3).find(|&i| cnt[i] == 2) {
                    // Exactly one other slot shares `maj`'s value (cnt == 2);
                    // the remaining slot (cnt == 1) is the odd one out.
                    let odd = (0..3).find(|&i| cnt[i] == 1).expect("one odd slot");
                    let mut next = active;
                    next[idxs[odd]] = false;
                    StepResult::Majority {
                        command: vals[maj],
                        disabled: idxs[odd] as u8,
                        active: next,
                    }
                } else {
                    // All three cnt == 1: pairwise different.
                    StepResult::OutsideHypothesis { active }
                }
            }
            4 => {
                let mut cnt = [0u8; 4];
                for i in 0..4 {
                    for j in 0..4 {
                        if vals[i] == vals[j] {
                            cnt[i] += 1;
                        }
                    }
                }
                if cnt[0] == 4 {
                    StepResult::Agreed {
                        command: vals[0],
                        active,
                    }
                } else if let Some(maj) = (0..4).find(|&i| cnt[i] == 3) {
                    // Exactly one slot has cnt == 1: the odd one out. A
                    // cnt == 3 slot cannot coexist with a 2-2 or 2-1-1
                    // split, so this is unambiguous.
                    let odd = (0..4).find(|&i| cnt[i] == 1).expect("one odd slot");
                    let mut next = active;
                    next[idxs[odd]] = false;
                    StepResult::Majority {
                        command: vals[maj],
                        disabled: idxs[odd] as u8,
                        active: next,
                    }
                } else {
                    // 2-2, 2-1-1, or all four different.
                    StepResult::OutsideHypothesis { active }
                }
            }
            _ => unreachable!("count is the number of set bits in a 4-element array"),
        }
    }

    /// `step` and the independently-written `oracle` agree on every active
    /// set (all 16 subsets of the four channels) and every word assignment
    /// drawn from a 3-value alphabet (`3^4 = 81` combinations per active
    /// set, `1296` cases total): an exhaustive test over a small value
    /// alphabet for every active set.
    #[test]
    fn step_matches_oracle_exhaustively() {
        let alphabet: [Word; 3] = [0, 1, 2];
        for a0 in [false, true] {
            for a1 in [false, true] {
                for a2 in [false, true] {
                    for a3 in [false, true] {
                        let active = [a0, a1, a2, a3];
                        for &w0 in &alphabet {
                            for &w1 in &alphabet {
                                for &w2 in &alphabet {
                                    for &w3 in &alphabet {
                                        let words = [w0, w1, w2, w3];
                                        assert_eq!(
                                            step(active, words),
                                            oracle(active, words),
                                            "active={active:?} words={words:?}"
                                        );
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn all_four_agree() {
        assert_eq!(
            step([true, true, true, true], [5, 5, 5, 5]),
            StepResult::Agreed {
                command: 5,
                active: [true, true, true, true]
            }
        );
    }

    #[test]
    fn one_of_four_disagrees_each_position() {
        assert_eq!(
            step([true, true, true, true], [9, 1, 1, 1]),
            StepResult::Majority {
                command: 1,
                disabled: 0,
                active: [false, true, true, true]
            }
        );
        assert_eq!(
            step([true, true, true, true], [1, 9, 1, 1]),
            StepResult::Majority {
                command: 1,
                disabled: 1,
                active: [true, false, true, true]
            }
        );
        assert_eq!(
            step([true, true, true, true], [1, 1, 9, 1]),
            StepResult::Majority {
                command: 1,
                disabled: 2,
                active: [true, true, false, true]
            }
        );
        assert_eq!(
            step([true, true, true, true], [1, 1, 1, 9]),
            StepResult::Majority {
                command: 1,
                disabled: 3,
                active: [true, true, true, false]
            }
        );
    }

    #[test]
    fn two_two_split_is_outside_hypothesis() {
        assert_eq!(
            step([true, true, true, true], [1, 1, 2, 2]),
            StepResult::OutsideHypothesis {
                active: [true, true, true, true]
            }
        );
    }

    #[test]
    fn two_one_one_split_is_outside_hypothesis() {
        assert_eq!(
            step([true, true, true, true], [1, 1, 2, 3]),
            StepResult::OutsideHypothesis {
                active: [true, true, true, true]
            }
        );
    }

    #[test]
    fn all_four_different_is_outside_hypothesis() {
        assert_eq!(
            step([true, true, true, true], [1, 2, 3, 4]),
            StepResult::OutsideHypothesis {
                active: [true, true, true, true]
            }
        );
    }

    #[test]
    fn three_active_all_different_is_outside_hypothesis() {
        assert_eq!(
            step([true, true, true, false], [1, 2, 3, 0]),
            StepResult::OutsideHypothesis {
                active: [true, true, true, false]
            }
        );
    }

    #[test]
    fn three_active_majority_disables_the_odd_one() {
        assert_eq!(
            step([true, false, true, true], [4, 0, 9, 4]),
            StepResult::Majority {
                command: 4,
                disabled: 2,
                active: [true, false, false, true]
            }
        );
    }

    #[test]
    fn pair_agreeing_is_agreed() {
        assert_eq!(
            step([false, true, false, true], [0, 3, 0, 3]),
            StepResult::Agreed {
                command: 3,
                active: [false, true, false, true]
            }
        );
    }

    #[test]
    fn pair_disagreeing_is_undetermined() {
        assert_eq!(
            step([true, false, false, true], [1, 0, 0, 2]),
            StepResult::Undetermined {
                active: [true, false, false, true]
            }
        );
    }

    #[test]
    fn single_active_channel_is_agreed() {
        assert_eq!(
            step([false, false, true, false], [0, 0, 42, 0]),
            StepResult::Agreed {
                command: 42,
                active: [false, false, true, false]
            }
        );
    }

    #[test]
    fn no_active_channels_is_its_own_variant() {
        assert_eq!(
            step([false, false, false, false], [1, 2, 3, 4]),
            StepResult::NoActiveChannels {
                active: [false, false, false, false]
            }
        );
    }
}
