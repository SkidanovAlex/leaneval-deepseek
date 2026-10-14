import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.Nonlinear.Pieces.splitsDiff
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bPrep
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkShiftHigh_shiftF
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.StarSlotPcs.DzdIterBound
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBoundCore
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.leibnizRem6
import Submission.Work.FTS.StrongPersist.hasDerivAt_wip_family
import Submission.Work.FTS_EllLimOK.LimTower_identify3
import Submission.Work.FTS_MuLamOK.Main
import Submission.Work.FTS_RegExport.RXT.jc3_aux
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Row6.RowFKfAux2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Row6

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

/-! ## Linearity of the iterates in a constant factor -/

/-- `D_θ^n (c · g) = c · D_θ^n g`. -/
theorem DthIter_const_mul_row (c : ℝ) (g : ℝ → ℝ → ℝ) (n : ℕ) :
    Work.Spaces.DthIter n (fun z θ => c * g z θ)
      = fun z θ => c * Work.Spaces.DthIter n g z θ := by
  funext z θ
  induction n generalizing z θ with
  | zero => rfl
  | succ k ih =>
      show Real.sin (2 * θ)
          * deriv (fun θ' => Work.Spaces.DthIter k (fun z θ => c * g z θ) z θ') θ
        = c * (Real.sin (2 * θ) * deriv (fun θ' => Work.Spaces.DthIter k g z θ') θ)
      rw [funext (fun θ' => ih z θ'), deriv_const_mul_field]
      ring

/-- `D_z^n (c · g) = c · D_z^n g`. -/
theorem DzIter_const_mul_row (c : ℝ) (g : ℝ → ℝ → ℝ) (n : ℕ) :
    Work.Spaces.DzIter n (fun z θ => c * g z θ)
      = fun z θ => c * Work.Spaces.DzIter n g z θ := by
  funext z θ
  induction n generalizing z θ with
  | zero => rfl
  | succ k ih =>
      show z * deriv (fun z' => Work.Spaces.DzIter k (fun z θ => c * g z θ) z' θ) z
        = c * (z * deriv (fun z' => Work.Spaces.DzIter k g z' θ) z)
      rw [funext (fun z' => ih z' θ), deriv_const_mul_field]
      ring

/-- `D_z^jD_θ^i (c · g) = c · D_z^jD_θ^i g`. -/
theorem mixed_const_mul_row (c : ℝ) (g : ℝ → ℝ → ℝ) (j i : ℕ) :
    Work.Spaces.mixed j i (fun z θ => c * g z θ)
      = fun z θ => c * Work.Spaces.mixed j i g z θ := by
  rw [Work.Spaces.mixed, DthIter_const_mul_row, Work.Spaces.mixed, DzIter_const_mul_row]

/-! ## A leaf-weighted slot against the `ℋ^m`-integrand -/

/-- Every leaf weight vanishes at `z = 0` (the radial factor `w 0` is `0`). -/
theorem leafW_zero_row {α : ℝ} {a : ℕ} {ρ : ℝ → ℝ → ℝ}
    (hρ : Work.FTS.TransportS.IsLeafW α a ρ) (θ : ℝ) : ρ 0 θ = 0 := by
  rcases hρ with h | h | h
  · rw [h, Work.FTS.TransportS.leafEta, Work.Spaces.w]; norm_num
  · rw [h, Work.FTS.TransportS.leafOne, Work.Spaces.w]; norm_num
  · rw [h.2, Work.FTS.TransportS.leafGam, Work.Spaces.w]; norm_num

/-- `HkIntegrand` vanishes at `z = 0` (both weights carry a factor `w 0 = 0`). -/
theorem HkIntegrand_zero_row (α : ℝ) (m : ℕ) (f : ℝ → ℝ → ℝ) (θ : ℝ) :
    Work.Spaces.HkIntegrand α m f 0 θ = 0 := by
  unfold Work.Spaces.HkIntegrand
  have hw : Work.Spaces.w 0 = 0 := by rw [Work.Spaces.w]; norm_num
  have hWt : Work.Spaces.Wt α 0 θ = 0 := by rw [Work.Spaces.Wt, hw, zero_mul]
  simp only [hw, zero_div, hWt, mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, Finset.sum_const_zero, add_zero, ite_self]

/-- **The pointwise domination of a leaf-weighted slot by `HkIntegrand α m f`**, for any
`m ≥ i + j` and any leaf weight `ρ` of a slot `a ≤ i` (so that `ρ ≤ slotW α i`). -/
theorem domLeaf_le_row {α : ℝ} (hα : 0 < α) {a i j m : ℕ} {ρ : ℝ → ℝ → ℝ}
    (hρ : Work.FTS.TransportS.IsLeafW α a ρ) (hai : a ≤ i) (hij : i + j ≤ m)
    {f : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    ρ z θ * (Work.Spaces.mixed j i f z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α m f z θ := by
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · rw [← hz0, leafW_zero_row hρ θ, zero_mul, HkIntegrand_zero_row]
  · have h1 : ρ z θ ≤ Work.FTS.TransportS.slotW α i z θ :=
      Work.FTS.StrongPersist.H6Pair6Aux.leaf_le_slotW_of_le hα hρ hai z θ hzpos hθ
    have h2 : Work.FTS.TransportS.slotW α i z θ * (Work.Spaces.mixed j i f z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α m f z θ :=
      Work.FTS.StrongPersist.H6Pair6Aux.slotW_slot_le hα hθ hij
    exact le_trans (mul_le_mul_of_nonneg_right h1 (sq_nonneg _)) h2

/-! ## Integrability of a leaf-weighted slot, at an arbitrary level -/

/-- The leaf-weighted slot integrand is continuous on the open quadrant. -/
theorem leafSlot_continuousOn_row {α : ℝ} {a i j : ℕ} {ρ : ℝ → ℝ → ℝ}
    {f : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen f)
    (hρ : Work.FTS.TransportS.IsLeafW α a ρ) :
    ContinuousOn (fun p : ℝ × ℝ => ρ p.1 p.2 * (Work.Spaces.mixed j i f p.1 p.2) ^ 2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
  (Work.FTS.StrongPersist.H6Pair6Aux.continuousOn_leaf hρ).mul
    ((hsm.mixed j i).continuousOn.pow 2)

/-- **The angular slice of a leaf-weighted slot is integrable**, and so is its `z`-marginal,
for an `ℋ^m`-datum and a slot with `a ≤ a'`, `a' + j ≤ m`. -/
theorem slotIntegrable_row {α : ℝ} (hα0 : 0 < α) {f : ℝ → ℝ → ℝ} {m : ℕ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hm : Work.Spaces.HkMem α m f)
    {a a' j : ℕ} {ρ : ℝ → ℝ → ℝ} (hρ : Work.FTS.TransportS.IsLeafW α a ρ)
    (hai : a ≤ a') (haj : a' + j ≤ m) :
    MeasureTheory.IntegrableOn
        (fun z => ∫ θ in Work.Spaces.Iθ, ρ z θ * (Work.Spaces.mixed j a' f z θ) ^ 2)
        Work.Spaces.Iz ∧
      (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn
        (fun θ => ρ z θ * (Work.Spaces.mixed j a' f z θ) ^ 2) Work.Spaces.Iθ) := by
  have haeθ : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    Work.FTS.IPGen.ip_ae_mem_Ioo_Iθ
  have hslice : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn
      (fun θ => ρ z θ * (Work.Spaces.mixed j a' f z θ) ^ 2) Work.Spaces.Iθ := by
    intro z hz
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
    · have hzero : (fun θ : ℝ => ρ z θ * (Work.Spaces.mixed j a' f z θ) ^ 2)
          = fun _ : ℝ => (0 : ℝ) := by
        funext θ
        rw [← hz0, leafW_zero_row hρ θ, zero_mul]
      rw [hzero]
      exact integrableOn_zero
    · refine MeasureTheory.Integrable.mono' (hm.1 z hz)
        (Work.Spaces.aesm_slice_of_continuousOn_Qd _
          (leafSlot_continuousOn_row hsm hρ) hzpos) ?_
      filter_upwards [haeθ] with θ hθ
      rw [Real.norm_of_nonneg (mul_nonneg
        (Work.FTS.StrongPersist.H6Pair6Aux.leaf_nonneg hρ z
          ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩) (sq_nonneg _))]
      exact domLeaf_le_row hα0 hρ hai haj hz hθ
  refine ⟨?_, hslice⟩
  have hX : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => ρ p.1 p.2 * (Work.Spaces.mixed j a' f p.1 p.2) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ (leafSlot_continuousOn_row hsm hρ)
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, ρ z θ * (Work.Spaces.mixed j a' f z θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have h := hX.integral_prod_right' (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    simpa using h
  refine MeasureTheory.Integrable.mono' hm.2 haesm ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
  have h1 : ‖∫ θ in Work.Spaces.Iθ, ρ z θ * (Work.Spaces.mixed j a' f z θ) ^ 2‖
      ≤ ∫ θ in Work.Spaces.Iθ, ρ z θ * (Work.Spaces.mixed j a' f z θ) ^ 2 := by
    refine (MeasureTheory.norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [haeθ] with θ hθ
    exact Real.norm_of_nonneg (mul_nonneg
      (Work.FTS.StrongPersist.H6Pair6Aux.leaf_nonneg hρ z
        ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩) (sq_nonneg _))
  have h2 : (∫ θ in Work.Spaces.Iθ, ρ z θ * (Work.Spaces.mixed j a' f z θ) ^ 2)
      ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α m f z θ := by
    refine MeasureTheory.integral_mono_of_nonneg ?_ (hm.1 z hz) ?_
    · filter_upwards [haeθ] with θ hθ
      exact mul_nonneg (Work.FTS.StrongPersist.H6Pair6Aux.leaf_nonneg hρ z
        ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩) (sq_nonneg _)
    · filter_upwards [haeθ] with θ hθ
      exact domLeaf_le_row hα0 hρ hai haj hz hθ
  linarith

/-! ## The arithmetic of the target shape -/


/-- `1 ≤ α^{-3}` on `Ioc 0 1`. -/
theorem one_le_rpow_neg_three_row {α : ℝ} (hα : α ∈ Set.Ioc 0 1) :
    (1 : ℝ) ≤ α ^ (-(3 : ℝ)) := by
  have h0 : 0 < α := hα.1
  have h3 : α ^ (3 : ℝ) ≤ 1 := by
    calc α ^ (3 : ℝ) ≤ 1 ^ (3 : ℝ) := Real.rpow_le_rpow h0.le hα.2 (by norm_num)
      _ = 1 := Real.one_rpow 3
  calc (1 : ℝ) ≤ (α ^ (3 : ℝ))⁻¹ := (one_le_inv₀ (Real.rpow_pos_of_pos h0 3)).mpr h3
    _ = α ^ (-(3 : ℝ)) := (Real.rpow_neg h0.le 3).symm

end

end Work.FTS.StrongPersist.H6Row6
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.psi6LowMixedHalf =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux

open MeasureTheory

/-- **The `γ`-weighted angular half of the level-`m` slice sum, `m ≤ 2`.**

For a datum `f` of the open class lying in `ℋ⁴`, every `m ≤ 2` and every `z > 0`, the angular
slice of the active `(D_z^j D_θ^i f)² · sin(2θ)^{-γ(α)}`-sum (those slots with `1 ≤ i` and
`i + j ≤ m`) is bounded by `27 · HkSq α 4 f`.

Route. The double `Finset.range (m+1)`-sum is a finite sum of `(m+1)² ≤ 9` terms, each of which
is either identically `0` (when `1 ≤ i` or `i + j ≤ m` fails) or the plain slot integrand
`(D_z^j D_θ^i f z ·)² · sin(2·)^{-γ(α)}`; every term is integrable on `Iθ` by
`lowGamSlotIntegrable` (`1 ≤ i`, `i + j ≤ m ≤ 2 ≤ 4`), so `MeasureTheory.integral_finsetSum`
splits the integral over the terms.  Each active slot obeys
`Work.FTS.StrongPersist.H6Row6Gam.mixed_slice_z_le_three` (`i + j ≤ m ≤ 2 ≤ 3`), while the
inactive ones are `≤ 0 ≤ 3 · HkSq α 4 f`.  Summing the resulting `≤ 3 · HkSq α 4 f` bounds over
the `(m+1)² ≤ 9` summands gives `≤ 27 · HkSq α 4 f`. -/
theorem psi6LowMixedHalf {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    {m : ℕ} (hm : m ≤ 2) {z : ℝ} (hz : 0 < z) :
    (∫ θ in Work.Spaces.Iθ, ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
        if 1 ≤ i ∧ i + j ≤ m then (Work.Spaces.mixed j i f z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) else 0)
      ≤ 27 * Work.Spaces.HkSq α 4 f := by
  classical
  have hHk : 0 ≤ Work.Spaces.HkSq α 4 f := Work.Spaces.HkSq_nonneg α 4 f
  -- Every one of the `(m+1)²` summands of the double sum is integrable on `Iθ`.
  have hterm : ∀ i ∈ Finset.range (m + 1), ∀ j ∈ Finset.range (m + 1),
      MeasureTheory.IntegrableOn (fun θ : ℝ =>
        if 1 ≤ i ∧ i + j ≤ m then (Work.Spaces.mixed j i f z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) else 0) Work.Spaces.Iθ := by
    intro i hi j hj
    by_cases hc : 1 ≤ i ∧ i + j ≤ m
    · have hij4 : i + j ≤ 4 := by
        have hi2 : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        have hj2 : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        omega
      simpa only [if_pos hc] using
        (Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.lowGamSlotIntegrable hα hα1 hF hmem
          (j := j) (i := i) hc.1 hij4 hz)
    · simpa only [if_neg hc] using
        (MeasureTheory.integrableOn_zero :
          MeasureTheory.IntegrableOn (fun θ : ℝ => (0 : ℝ)) Work.Spaces.Iθ)
  -- The same statement, indexed by a pair.
  have hIntP : ∀ p ∈ (Finset.range (m + 1)) ×ˢ (Finset.range (m + 1)),
      MeasureTheory.IntegrableOn (fun θ : ℝ =>
        if 1 ≤ p.1 ∧ p.1 + p.2 ≤ m then (Work.Spaces.mixed p.2 p.1 f z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) else 0) Work.Spaces.Iθ := by
    intro p hp
    exact hterm p.1 (Finset.mem_product.mp hp).1 p.2 (Finset.mem_product.mp hp).2
  -- Reindex the double sum as a sum over the product of the two ranges.
  have hprod : ∀ θ : ℝ,
      (∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
        (if 1 ≤ i ∧ i + j ≤ m then (Work.Spaces.mixed j i f z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) else 0))
      = ∑ p ∈ (Finset.range (m + 1)) ×ˢ (Finset.range (m + 1)),
          (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ m then (Work.Spaces.mixed p.2 p.1 f z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) else 0) := by
    intro θ
    rw [← Finset.sum_product (f := fun p : ℕ × ℕ => (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ m then
      (Work.Spaces.mixed p.2 p.1 f z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) else 0))]
  -- Push the integral through the (finite, integrable) sum.
  have hsplit : (∫ θ in Work.Spaces.Iθ, ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
        (if 1 ≤ i ∧ i + j ≤ m then (Work.Spaces.mixed j i f z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) else 0))
      = ∑ p ∈ (Finset.range (m + 1)) ×ˢ (Finset.range (m + 1)),
          ∫ θ in Work.Spaces.Iθ,
            (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ m then (Work.Spaces.mixed p.2 p.1 f z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) else 0) := by
    rw [show (fun θ : ℝ => ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
          (if 1 ≤ i ∧ i + j ≤ m then (Work.Spaces.mixed j i f z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) else 0))
        = (fun θ : ℝ => ∑ p ∈ (Finset.range (m + 1)) ×ˢ (Finset.range (m + 1)),
          (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ m then (Work.Spaces.mixed p.2 p.1 f z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) else 0)) from funext hprod]
    exact MeasureTheory.integral_finsetSum
      (s := (Finset.range (m + 1)) ×ˢ (Finset.range (m + 1)))
      (f := fun p : ℕ × ℕ => fun θ : ℝ =>
        (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ m then (Work.Spaces.mixed p.2 p.1 f z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) else 0)) hIntP
  -- Each term of the reindexed sum is bounded by `3 · HkSq α 4 f`.
  have hper : ∀ p ∈ (Finset.range (m + 1)) ×ˢ (Finset.range (m + 1)),
      (∫ θ in Work.Spaces.Iθ,
        (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ m then (Work.Spaces.mixed p.2 p.1 f z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) else 0))
        ≤ 3 * Work.Spaces.HkSq α 4 f := by
    intro p hp
    by_cases hc : 1 ≤ p.1 ∧ p.1 + p.2 ≤ m
    · have h3 : p.1 + p.2 ≤ 3 := by omega
      have h := Work.FTS.StrongPersist.H6Row6Gam.mixed_slice_z_le_three α f hα hα1 hF hmem
        p.2 p.1 hc.1 h3 z hz
      simpa only [if_pos hc] using h
    · have hz0 : (∫ θ in Work.Spaces.Iθ, (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ m then
            (Work.Spaces.mixed p.2 p.1 f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          else 0)) = 0 := by
        rw [show (fun θ : ℝ => (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ m then
            (Work.Spaces.mixed p.2 p.1 f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          else 0)) = (fun _ : ℝ => (0 : ℝ)) from funext (fun θ => if_neg hc)]
        simp
      rw [hz0]
      linarith
  calc (∫ θ in Work.Spaces.Iθ, ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
        (if 1 ≤ i ∧ i + j ≤ m then (Work.Spaces.mixed j i f z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) else 0))
      = ∑ p ∈ (Finset.range (m + 1)) ×ˢ (Finset.range (m + 1)),
          ∫ θ in Work.Spaces.Iθ,
            (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ m then (Work.Spaces.mixed p.2 p.1 f z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) else 0) := hsplit
    _ ≤ ∑ _p ∈ (Finset.range (m + 1)) ×ˢ (Finset.range (m + 1)),
          (3 * Work.Spaces.HkSq α 4 f) := Finset.sum_le_sum hper
    _ = ((Finset.range (m + 1)) ×ˢ (Finset.range (m + 1))).card •
          (3 * Work.Spaces.HkSq α 4 f) := Finset.sum_const _
    _ ≤ 27 * Work.Spaces.HkSq α 4 f := by
        rw [Finset.card_product, Finset.card_range, nsmul_eq_mul, Nat.cast_mul]
        have h3 : ((m + 1 : ℕ) : ℝ) ≤ 3 := by exact_mod_cast (by omega : m + 1 ≤ 3)
        have h0 : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by positivity
        have hstep : ((m + 1 : ℕ) : ℝ) * ((m + 1 : ℕ) : ℝ) * (3 * Work.Spaces.HkSq α 4 f)
            ≤ 9 * (3 * Work.Spaces.HkSq α 4 f) := by
          refine mul_le_mul_of_nonneg_right ?_ (by linarith [hHk])
          nlinarith
        linarith

end Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.NSplit6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Npair6SupAux/NSplit6` — the twenty-piece splitting of the level-six `N`-row

On the open quadrant `Qd` the nonlinear term of the modulated equation splits into the twenty
pieces of `NDefs`, because

* the straightened stream function splits, `Ξ = PhiTil α (F_* + f) (Φs + Ef) = Ξ₁ + Ξ₂` with
  `Ξ₁ = PhiTs α Φs`, `Ξ₂ = PhiTil α f Ef` (`XiOpsplit`), hence so do the three coefficient
  fields `ℛ(Ξ)`, `𝒰(Ξ)/sin 2θ`, `𝒱(Ξ)`;
* the angular moment splits, `FK (F_* + f) = FK F_* + FK f` (`L3RhsFKadd`);
* the two slots split, `D_θ(F_* + f) = D_θF_* + D_θf` and `D_z(F_* + f) = D_zF_* + D_zf`
  (additivity of `deriv` on the slices, from the interior smoothness of `F_*` and `f`).

Expanding the five terms of `N α (F_*+f) (Φs+Ef)` with these splits gives exactly the twenty
`nsP`-summands of `nsum`.  The second conjunct — the equality of the two `IP6`-pairings — is
`IP6_congr`, the congruence of the pairing in its first argument on the open quadrant.
-/


noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows.Npair6SupAux

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## Additivity of the partial derivatives over the split `F_* + f` -/

/-- The `θ`-slice of a function smooth on the open quadrant is differentiable at an interior
angle. -/
theorem nsplit6_difftheta {g : Fn} (hg : Work.FTS.EllipticEst.SmoothOpen g) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    DifferentiableAt ℝ (fun θ' : ℝ => g z θ') θ :=
  (((hg.curry_θ hz).differentiableOn (by simp)).differentiableAt (isOpen_Ioo.mem_nhds hθ))

/-- The `z`-slice of a function smooth on the open quadrant is differentiable at `z > 0`. -/
theorem nsplit6_diffz {g : Fn} (hg : Work.FTS.EllipticEst.SmoothOpen g) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    DifferentiableAt ℝ (fun z' : ℝ => g z' θ) z :=
  (((hg.curry_z hθ).differentiableOn (by simp)).differentiableAt (isOpen_Ioi.mem_nhds hz))

/-- `D_θ` is additive over the split `F_* + f`. -/
theorem nsplit6_dth_star_add {α : ℝ} {f : Fn} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Spaces.Dth (fun z θ => Work.Construction.Fstar α z θ + f z θ) z θ
      = Work.Spaces.Dth (Work.Construction.Fstar α) z θ + Work.Spaces.Dth f z θ := by
  have h : Work.Spaces.pth (fun z θ => Work.Construction.Fstar α z θ + f z θ) z θ
      = Work.Spaces.pth (Work.Construction.Fstar α) z θ + Work.Spaces.pth f z θ :=
    Work.FTS.Nonlinear.Pieces.pth_add_of_diff
      (nsplit6_difftheta (Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_Fstar α) hz hθ)
      (nsplit6_difftheta hf hz hθ)
  have e1 : Work.Spaces.Dth (fun z θ => Work.Construction.Fstar α z θ + f z θ) z θ
      = Real.sin (2 * θ)
          * Work.Spaces.pth (fun z θ => Work.Construction.Fstar α z θ + f z θ) z θ := rfl
  have e2 : Work.Spaces.Dth (Work.Construction.Fstar α) z θ
      = Real.sin (2 * θ) * Work.Spaces.pth (Work.Construction.Fstar α) z θ := rfl
  have e3 : Work.Spaces.Dth f z θ = Real.sin (2 * θ) * Work.Spaces.pth f z θ := rfl
  rw [e1, e2, e3, h]
  ring

/-- `D_z` is additive over the split `F_* + f`. -/
theorem nsplit6_dz_star_add {α : ℝ} {f : Fn} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Spaces.Dz (fun z θ => Work.Construction.Fstar α z θ + f z θ) z θ
      = Work.Spaces.Dz (Work.Construction.Fstar α) z θ + Work.Spaces.Dz f z θ := by
  have h : Work.Spaces.pz (fun z θ => Work.Construction.Fstar α z θ + f z θ) z θ
      = Work.Spaces.pz (Work.Construction.Fstar α) z θ + Work.Spaces.pz f z θ :=
    Work.FTS.Nonlinear.Pieces.pz_add_of_diff
      (nsplit6_diffz (Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_Fstar α) hz hθ)
      (nsplit6_diffz hf hz hθ)
  have e1 : Work.Spaces.Dz (fun z θ => Work.Construction.Fstar α z θ + f z θ) z θ
      = z * Work.Spaces.pz (fun z θ => Work.Construction.Fstar α z θ + f z θ) z θ := rfl
  have e2 : Work.Spaces.Dz (Work.Construction.Fstar α) z θ
      = z * Work.Spaces.pz (Work.Construction.Fstar α) z θ := rfl
  have e3 : Work.Spaces.Dz f z θ = z * Work.Spaces.pz f z θ := rfl
  rw [e1, e2, e3, h]
  ring

/-! ## The pointwise identity -/

/-- **The twenty-piece splitting of the level-six `N`-row.**  On the open quadrant,
`N α (F_* + f) (Φs + Ef)` is the sum `nsum α f Ef Φs` of the twenty pieces of `NDefs`. -/
theorem nsplit6_pt {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f Ef Φs : Fn}
    (hadm : Work.FTS.StrongPersist.H6Adm α f)
    (hEf : Work.FTS.EllipticEst.SmoothOpen Ef) (hΦs : Work.FTS.EllipticEst.SmoothOpen Φs) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Construction.N α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
          (fun z θ => Φs z θ + Ef z θ) z θ
        = nsum α f Ef Φs z θ := by
  have hαIoc : α ∈ Set.Ioc 0 1 := ⟨hα, hα1⟩
  have hso : Work.FTS.EllipticEst.SmoothOpen f := hadm.reg.1
  obtain ⟨_hXi, hR, hU, hV⟩ := XiOpsplit hα hα1 hadm hEf hΦs
  intro z θ hzθ
  obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hzθ
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hN := Work.FTS.StrongPersist.H6Pair6Aux.NZeroAux.nzs_N_form α
    (fun z θ => Work.Construction.Fstar α z θ + f z θ)
    (fun z θ => Φs z θ + Ef z θ) z θ hzθ
  have hK : Work.Construction.FK (fun z θ => Work.Construction.Fstar α z θ + f z θ) z
      = Work.Construction.FK (Work.Construction.Fstar α) z + Work.Construction.FK f z := by
    have h := Work.FTS.StrongPersist.L3Rhs.L3RhsFKadd α hαIoc f hadm z hz
    have hftot : Work.Construction.Ftot α f
        = (fun z θ : ℝ => Work.Construction.Fstar α z θ + f z θ) := rfl
    rw [hftot] at h
    exact h
  have hT := nsplit6_dth_star_add (α := α) hso hz hθ
  have hZ := nsplit6_dz_star_add (α := α) hso hz hθ
  rw [hN, hR z θ hzθ, hU z θ hzθ, hV z θ hzθ, hK, hT, hZ]
  simp only [nsum, nsP0, nsP1, nsP2, nsP3, nsP4, nsP5, nsP6, nsP7, nsP8, nsP9, nsP10,
    nsP11, nsP12, nsP13, nsP14, nsP15, nsP16, nsP17, nsP18, nsP19,
    coefR1, coefR2, coefU1, coefU2, coefV1, coefV2, coefKs, coefKf,
    slotFs, slotTs, slotZs, slotTf, slotZf, angSin2]
  ring

theorem NSplit6 {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f Ef Φs : Work.FTS.Galerkin.Fn}
    (hadm : Work.FTS.StrongPersist.H6Adm α f)
    (hEf : Work.FTS.EllipticEst.SmoothOpen Ef)
    (hΦs : Work.FTS.EllipticEst.SmoothOpen Φs) :
    (∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Construction.N α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
          (fun z θ => Φs z θ + Ef z θ) z θ
        = Work.FTS.StrongPersist.H6Rows.Npair6SupAux.nsum α f Ef Φs z θ) ∧
    (∀ w : Work.FTS.Galerkin.Fn,
      Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α
          (Work.Construction.N α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
            (fun z θ => Φs z θ + Ef z θ)) w
        = Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α
            (Work.FTS.StrongPersist.H6Rows.Npair6SupAux.nsum α f Ef Φs) w) := by
  have hmain := nsplit6_pt hα hα1 hadm hEf hΦs
  exact ⟨hmain, fun w =>
    Work.FTS.StrongPersist.IP6_congr 1 1 1 1 1 1 1 1 1 1 α hα hmain⟩

end Work.FTS.StrongPersist.H6Rows.Npair6SupAux
end
end
