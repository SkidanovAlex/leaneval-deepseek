import Mathlib
import Submission.Work.Mostow.cosh_hdist_fermi
import Submission.Work.Mostow.fermi_inv
import Submission.Work.Mostow.stab_fermi_foot

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity

/-! `sinhc` is positive (`sinhc s = sinh s / s` for `s ≠ 0`, `sinhc 0 = 1`). -/
private lemma sinhc_pos_indep (s : ℝ) : 0 < Submission.Mostow.sinhc s := by
  rw [Submission.Mostow.sinhc]
  by_cases h : s = 0
  · simp [h]
  · simp only [h, ↓reduceIte]
    by_cases hs : 0 < s
    · exact div_pos (Real.sinh_pos_iff.mpr hs) hs
    · have hs' : s < 0 := lt_of_le_of_ne (not_lt.mp hs) h
      exact div_pos_of_neg_of_neg (Real.sinh_neg_iff.mpr hs') hs'

/-! Normal part of a stratum-pointwise-fixing isometry `g'` does not depend on the foot: the second
Fermi coordinate of `g' • fermi k m v w` is the same for every `v`, namely the one for `v = 0`.

Guidance.  Inside the proof you will need (and may reprove as private lemmas) the "foot" facts,
which are also stated separately as `Work.Mostow.stab_fermi_foot`:
  `(fermiInv k m (g' • fermi k m v w)).1 = v` and `‖(fermiInv k m (g' • fermi k m v w)).2‖ = ‖w‖`
for every `v w` (prove them from `Work.Mostow.cosh_hdist_fermi` with `w' = 0` and the equality of
`cosh (hdist (g' • fermi k m v w) (coordEmb k m v'))` with `cosh ‖w‖ * cosh (hdist v v')`,
using `hg'` and the isometry clause of `HypIsometryProp (k+m)`).
Then put `W := (fermiInv k m (g' • fermi k m v w)).2` and `R0 := (fermiInv k m (g' • fermi k m 0 w)).2`,
so that `g' • fermi k m v w = fermi k m v W` and `g' • fermi k m 0 w = fermi k m 0 R0`
(`Work.Mostow.fermi_inv`) with `‖W‖ = ‖w‖ = ‖R0‖`.  The isometry clause of `HypIsometryProp (k+m)`
gives `hdist (fermi k m v W) (fermi k m 0 R0) = hdist (fermi k m v w) (fermi k m 0 w)`; take `cosh`
and expand both sides with `Work.Mostow.cosh_hdist_fermi`.  The terms involving `cosh (hdist v 0)`
cancel and, since `sinhc` is positive on `[0,∞)` (`sinhc s = sinh s / s` for `s ≠ 0`, `sinhc 0 = 1`)
and `inner ℝ w w = ‖w‖ ^ 2`, one gets `inner ℝ W R0 = ‖w‖ ^ 2 = ‖W‖ * ‖R0‖`; finally
`‖W - R0‖ ^ 2 = ‖W‖ ^ 2 + ‖R0‖ ^ 2 - 2 * inner ℝ W R0 = 0`, so `W = R0`
(`real_inner_self_eq_norm_sq`, `inner_sub_left`, `inner_sub_right`, `inner_self_eq_zero`). -/
theorem stab_fermi_normal_indep (k m : ℕ) (hA : Submission.Mostow.POActionProp (k + m))
    (hI : Submission.Mostow.HypIsometryProp (k + m))
    (g' : LeanEval.Geometry.MostowRigidity.PO (k + m) 1)
    (hg' : ∀ v : Submission.Mostow.E k,
      g' • Submission.Mostow.coordEmb k m v = Submission.Mostow.coordEmb k m v) :
    ∀ (v : Submission.Mostow.E k) (w : Submission.Mostow.E m),
      (Submission.Mostow.fermiInv k m (g' • Submission.Mostow.fermi k m v w)).2 =
        (Submission.Mostow.fermiInv k m (g' • Submission.Mostow.fermi k m 0 w)).2 := by
  intro v w
  have hiso := hI.2.2.2.2.2.2.1
  have hfv := stab_fermi_foot k m hA hI g' hg' v w
  have hf0 := stab_fermi_foot k m hA hI g' hg' (0 : Submission.Mostow.E k) w
  set p : Submission.Mostow.E k :=
    (Submission.Mostow.fermiInv k m (g' • Submission.Mostow.fermi k m v w)).1 with hp
  set q : Submission.Mostow.E m :=
    (Submission.Mostow.fermiInv k m (g' • Submission.Mostow.fermi k m v w)).2 with hq
  set p0 : Submission.Mostow.E k :=
    (Submission.Mostow.fermiInv k m (g' • Submission.Mostow.fermi k m 0 w)).1 with hp0
  set r0 : Submission.Mostow.E m :=
    (Submission.Mostow.fermiInv k m (g' • Submission.Mostow.fermi k m 0 w)).2 with hr0
  have hpv : p = v := by rw [hp]; exact hfv.1
  have hp0z : p0 = 0 := by rw [hp0]; exact hf0.1
  have hqn : ‖q‖ = ‖w‖ := by rw [hq]; exact hfv.2
  have hrn : ‖r0‖ = ‖w‖ := by rw [hr0]; exact hf0.2
  have hrecv : Submission.Mostow.fermi k m
      (Submission.Mostow.fermiInv k m (g' • Submission.Mostow.fermi k m v w)).1
      (Submission.Mostow.fermiInv k m (g' • Submission.Mostow.fermi k m v w)).2
      = g' • Submission.Mostow.fermi k m v w := (Work.Mostow.fermi_inv k m).2.1 _
  have hrec0 : Submission.Mostow.fermi k m
      (Submission.Mostow.fermiInv k m (g' • Submission.Mostow.fermi k m 0 w)).1
      (Submission.Mostow.fermiInv k m (g' • Submission.Mostow.fermi k m 0 w)).2
      = g' • Submission.Mostow.fermi k m 0 w := (Work.Mostow.fermi_inv k m).2.1 _
  -- the isometry equation, with the left-hand side rewritten in Fermi coordinates
  have hL : Real.cosh (hdist (g' • Submission.Mostow.fermi k m v w)
        (g' • Submission.Mostow.fermi k m 0 w))
      = Real.cosh ‖q‖ * Real.cosh ‖r0‖ * Real.cosh (hdist p p0)
        - Submission.Mostow.sinhc ‖q‖ * Submission.Mostow.sinhc ‖r0‖ * inner ℝ q r0 := by
    rw [← hrecv, ← hrec0, ← hp, ← hq, ← hp0, ← hr0, Work.Mostow.cosh_hdist_fermi]
  have hR : Real.cosh (hdist (Submission.Mostow.fermi k m v w)
        (Submission.Mostow.fermi k m 0 w))
      = Real.cosh ‖w‖ * Real.cosh ‖w‖ * Real.cosh (hdist v 0)
        - Submission.Mostow.sinhc ‖w‖ * Submission.Mostow.sinhc ‖w‖ * inner ℝ w w :=
    Work.Mostow.cosh_hdist_fermi k m v 0 w w
  have hcosh : Real.cosh (hdist (g' • Submission.Mostow.fermi k m v w)
        (g' • Submission.Mostow.fermi k m 0 w))
      = Real.cosh (hdist (Submission.Mostow.fermi k m v w)
        (Submission.Mostow.fermi k m 0 w)) :=
    congrArg Real.cosh (hiso g' _ _)
  have hmain : Real.cosh ‖q‖ * Real.cosh ‖r0‖ * Real.cosh (hdist p p0)
        - Submission.Mostow.sinhc ‖q‖ * Submission.Mostow.sinhc ‖r0‖ * inner ℝ q r0
      = Real.cosh ‖w‖ * Real.cosh ‖w‖ * Real.cosh (hdist v 0)
        - Submission.Mostow.sinhc ‖w‖ * Submission.Mostow.sinhc ‖w‖ * inner ℝ w w :=
    hL.symm.trans (hcosh.trans hR)
  rw [hpv, hp0z, hqn, hrn] at hmain
  -- cancel the `cosh (hdist v 0)` terms and the two positive `sinhc` factors
  have hinner_eq : Submission.Mostow.sinhc ‖w‖ * Submission.Mostow.sinhc ‖w‖ * inner ℝ q r0
      = Submission.Mostow.sinhc ‖w‖ * Submission.Mostow.sinhc ‖w‖ * inner ℝ w w := by
    linarith [hmain]
  have hpos : 0 < Submission.Mostow.sinhc ‖w‖ * Submission.Mostow.sinhc ‖w‖ :=
    mul_pos (sinhc_pos_indep _) (sinhc_pos_indep _)
  have hinner : inner ℝ q r0 = inner ℝ w w := mul_left_cancel₀ hpos.ne' hinner_eq
  have hinner2 : inner ℝ q r0 = ‖w‖ ^ 2 := by
    rw [hinner, real_inner_self_eq_norm_sq]
  -- hence `q = r0`
  have hqr : q = r0 := by
    have hzero : inner ℝ (q - r0) (q - r0) = 0 := by
      rw [inner_sub_left, inner_sub_right, inner_sub_right, real_inner_comm q r0,
        real_inner_self_eq_norm_sq q, real_inner_self_eq_norm_sq r0, hinner2, hqn, hrn]
      ring
    exact sub_eq_zero.mp (inner_self_eq_zero.mp hzero)
  exact hqr

end Work.Mostow
