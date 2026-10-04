import Mathlib
import Submission.Work.Diff.EXT.evolX.mulOpJetsDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The shuffle calculus: an `A`-position does not touch the `B`-sub-tuple

This module proves `Work.Diff.EXT.evolX.wTupUntouchedA`: updating the level-`(m+1)` tuple at an
`A`-position of the word `w : Word (m+1)` leaves the `B`-sub-tuple `wTupB K₁ K₂ (m+1) w` unchanged.

The content is the *disjointness of the position maps*: the `A`-positions `wPosA` and the
`B`-positions `wPosB` never coincide on the index ranges `[0, K₁ + wCntT w)` resp.
`[0, K₂ + wCntF w)` (`wPosA_ne_wPosB_of_lt`).  Indeed the level-`(n+1)` tuple positions
`0, …, K₁+K₂+n` are split between the `A`-tuple (the `wCntT w` derivative directions routed to the
first factor, followed by its `K₁` tensor slots) and the `B`-tuple (the `wCntF w` directions routed
to the second factor, followed by its `K₂` tensor slots), and the two position maps are the
corresponding injections; the induction is on the level `n`, Peeling the newest direction
(`Word.cons`).

The companion statements (`wTupUpdateA`: an `A`-update does change the `A`-tuple, and the
`wTupConsTrue`/`wTupConsFalse`/`wTupBConsTrue`/`wTupBConsFalse` recursions) are proved separately;
`Work.Diff.EXT.evolX.wTupB_update_wPA` in `mulOpJetsPos` derives the present statement from the
disjointness in the `wPA`/`wPB` language.
-/

namespace Work.Diff.EXT.evolX

/-- **Disjointness of the `A`- and `B`-position maps of the word shuffle.**  For a word
`w : Word (n+1)` (a word of `n+1` derivative directions, of which the newest is at position `0` of
the tuple) the `r₁`-th entry of the `A`-tuple and the `r₂`-th entry of the `B`-tuple occupy distinct
positions of the level-`n` tuple, as long as the indices are in range
(`r₁ < K₁ + wCntT w`, `r₂ < K₂ + wCntF w`). -/
theorem wPosA_ne_wPosB_of_lt (K₁ K₂ : ℕ) : ∀ (n : ℕ) (w : Word (n + 1)) (r₁ r₂ : ℕ),
    r₁ < K₁ + wCntT w → r₂ < K₂ + wCntF w →
    wPosA K₁ K₂ n w r₁ ≠ wPosB K₁ K₂ n w r₂ := by
  intro n
  induction n with
  | zero =>
    -- level `1`: the word has a single letter, which occupies position `0`
    intro w r₁ r₂ h₁ h₂
    cases w with
    | cons b w0 =>
      cases w0
      cases b
      · -- the only direction goes to `B`
        simp only [wCntT_cons_false, wCntF_cons_false, wCntT.eq_1, wCntF.eq_1] at h₁ h₂
        rw [wPosA_zero_cons_false, wPosB_zero_cons_false]
        intro hcon
        have hv := congrArg Fin.val hcon
        cases r₂ with
        | zero =>
          rw [if_pos rfl] at hv
          simp only [Fin.val_mk, Fin.val_zero] at hv
          rw [Nat.min_eq_left (by omega)] at hv
          omega
        | succ q =>
          rw [if_neg (by omega : ¬ (q + 1 = 0))] at hv
          simp only [Fin.val_mk] at hv
          rw [Nat.min_eq_left (by omega), Nat.min_eq_left (by omega)] at hv
          omega
      · -- the only direction goes to `A`
        simp only [wCntT_cons_true, wCntF_cons_true, wCntT.eq_1, wCntF.eq_1] at h₁ h₂
        rw [wPosA_zero_cons_true, wPosB_zero_cons_true]
        intro hcon
        have hv := congrArg Fin.val hcon
        cases r₁ with
        | zero =>
          rw [if_pos rfl] at hv
          simp only [Fin.val_mk, Fin.val_zero] at hv
          rw [Nat.min_eq_left (by omega)] at hv
          omega
        | succ p =>
          rw [if_neg (by omega : ¬ (p + 1 = 0))] at hv
          simp only [Fin.val_mk] at hv
          rw [Nat.min_eq_left (by omega), Nat.min_eq_left (by omega)] at hv
          omega
  | succ n ih =>
    -- level `n + 2`: peel the newest direction, which occupies position `0` of the tuple
    intro w r₁ r₂ h₁ h₂
    cases w with
    | cons b w0 =>
      cases b
      · -- the newest direction goes to `B`: the `A`-positions are all shifted successors
        simp only [wCntT_cons_false] at h₁
        simp only [wCntF_cons_false] at h₂
        rw [wPosA_cons_false]
        intro hcon
        have hv := congrArg Fin.val hcon
        cases r₂ with
        | zero =>
          rw [wPosB_cons_false_zero] at hv
          simp only [Fin.val_mk, Fin.val_zero, Fin.val_succ] at hv
          omega
        | succ q =>
          rw [wPosB_cons_false_succ] at hv
          simp only [Fin.val_succ] at hv
          refine ih w0 r₁ q h₁ (by omega) (Fin.ext ?_)
          omega
      · -- the newest direction goes to `A`: it takes position `0`, the rest is shifted
        simp only [wCntT_cons_true] at h₁
        simp only [wCntF_cons_true] at h₂
        rw [wPosB_cons_true]
        intro hcon
        have hv := congrArg Fin.val hcon
        cases r₁ with
        | zero =>
          rw [wPosA_cons_true_zero] at hv
          simp only [Fin.val_mk, Fin.val_zero, Fin.val_succ] at hv
          omega
        | succ p =>
          rw [wPosA_cons_true_succ] at hv
          simp only [Fin.val_succ] at hv
          refine ih w0 p r₂ (by omega) h₂ (Fin.ext ?_)
          omega

theorem wTupUntouchedA
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (K₁ K₂ m : ℕ) (w : Work.Diff.EXT.evolX.Word (m + 1))
    (F : Fin (K₁ + K₂ + (m + 1)) → Work.Diff.EXT.TField (I := I) (M := M))
    (v : Work.Diff.EXT.TField (I := I) (M := M))
    (ρ : Fin (K₁ + Work.Diff.EXT.evolX.wCntT w)) :
    Work.Diff.EXT.evolX.wTupB (I := I) (M := M) K₁ K₂ (m + 1) w
        (Function.update F (Work.Diff.EXT.evolX.wPosA K₁ K₂ m w ρ.val) v)
      = Work.Diff.EXT.evolX.wTupB (I := I) (M := M) K₁ K₂ (m + 1) w F := by
  funext i
  change Function.update F (wPosA K₁ K₂ m w ρ.val) v (wPosB K₁ K₂ m w i.val)
      = F (wPosB K₁ K₂ m w i.val)
  rw [Function.update_apply,
    if_neg (Ne.symm (wPosA_ne_wPosB_of_lt K₁ K₂ m w ρ.val i.val ρ.isLt i.isLt))]

end Work.Diff.EXT.evolX
