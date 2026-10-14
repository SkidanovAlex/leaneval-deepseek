import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.SliceDecompDefs
import Submission.Work.FTS.H2.Transport1Aux
import Submission.Work.FTS.StrongPersist.N6.sliceAvg_le6
import Submission.Work.FTS.TransportS.sup_dz_le_hk
import Submission.Work.FTS_EllLimOK.SlotJets.slotPthSliceLe
import Submission.Work.FTS_RegExport.RXT.StarVopWlInf
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.ThetaAgmon.agmon_interval
import Submission.Work.Spaces.sq_mul_div_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.SlotSup

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# Pointwise (`L^∞`) bounds for the mixed jets of an `ℋ⁶`-datum

This file proves `slot_jets_sup_le`: for `0 < α ≤ 1` there is a constant `C = C(α)` such that
for every function `f` of class `C^∞` on the open quadrant `(0,∞) × (0,π/2)`
(`Work.FTS.EllipticEst.SmoothOpen`) lying in the weighted space `ℋ⁶`
(`Work.Spaces.HkMem α 6 f`, i.e. `HkNorm α 6 f < ∞`) one has

  `|D_z^b D_θ^a f (z,θ)| ≤ C · |f|_{ℋ⁶}`   for all `a + b ≤ 4`, `z > 0`, `0 < θ < π/2`.

This is the *uniform* (in `z` **and** `θ`) version of
`Work.FTS_EllLimOK.SlotJets.slot_jets_le`, whose constant contains the singular factor
`1/θ + 1/(π/2 - θ)`; here the pointwise bound is obtained by evaluating the oscillation of the
slot at the *globally* chosen minimiser `θ₀ ∈ [π/8, 3π/8]` of `|D_z^bD_θ^af(z,·)|` on the
middle half, and then integrating the derivative over the *whole* angular interval `Iθ`, so
that no factor involving the distance to the endpoints appears.

## Route

For a slot `(b,a)` with `a + b ≤ 4`, a radius `z > 0` and an angle `θ ∈ (0,π/2)`:

* (`avg`) some `θ₀ ∈ [π/8, 3π/8]` satisfies
  `(D_z^bD_θ^af(z,θ₀))² ≤ (4/π) ∫_{Iθ} (D_z^bD_θ^af(z,σ))²dσ`
  (`Work.FTS.TransportS.min_mid_le_avg`), and the integral is `≤ max Cs Cd · HkSq α 6 f`
  uniformly in `z`: for `a = 0` this is `supDzAvgLevel` (`Cd = 3`), for `a ≥ 1` it is
  `sliceAng_le6` (`Cs = 4`) together with `sin(2σ)^{-γ} ≥ 1`;
* (`osc`) `(D_z^bD_θ^af(z,θ) - D_z^bD_θ^af(z,θ₀))² ≤ (100/(γ-1)) ∫_{Iθ} (∂_θD_z^bD_θ^af(z,σ))²
  sin(2σ)^{2-γ}dσ` is `Work.FTS.H2.OscSqLe`, and the integral is `≤ Cp · HkSq α 6 f`
  uniformly in `z` by `Work.FTS_EllLimOK.SlotJets.slotPthSliceLe` (equivalently: the slot
  `(b, a+1)`, which is still an `ℋ⁶`-slot because `a + b ≤ 4 ⟹ a + 1 + b ≤ 6`);
* hence `(D_z^bD_θ^af(z,θ))² ≤ M · HkSq α 6 f` with
  `M = 2·(100/(γ-1))·Cp + 2·(4/π)·max Cs Cd`, and the result follows with `C = √M + 1`.
-/

/-! ## Elementary helpers -/

/-- `sin(2θ) > 0` on the open angular interval. -/
private lemma sin_two_pos_of_mem {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    0 < Real.sin (2 * x) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1]) (by linarith [hx.2, Real.pi_pos])

/-- The radial weight is at least `1` on `z > 0`. -/
private lemma one_le_w {z : ℝ} (hz : 0 < z) : 1 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w, le_div_iff₀ (by positivity : (0 : ℝ) < z ^ 2)]
  nlinarith [hz]

/-- `1 ≤ x ^ (-p)` for `0 < x ≤ 1`, `p ≥ 0`. -/
private lemma one_le_rpow_neg {x p : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (hp : 0 ≤ p) :
    1 ≤ x ^ (-p) := by
  rw [Real.rpow_neg hx0.le p]
  exact (one_le_inv₀ (Real.rpow_pos_of_pos hx0 p)).mpr (Real.rpow_le_one hx0.le hx1 hp)

/-- `(x ^ (-(c/2)))² = x ^ (-c)` for `x > 0`. -/
private lemma rpow_neg_half_sq (x c : ℝ) (hx : 0 < x) :
    (x ^ (-(c / 2))) ^ 2 = x ^ (-c) := by
  rw [pow_two, ← Real.rpow_add hx, show -(c / 2) + -(c / 2) = -c by ring]

/-- `1 ≤ W²` on the open quadrant, where `W = Wt α z θ = w(z)·sin(2θ)^{-γ/2}`. -/
private lemma one_le_Wt_sq {α : ℝ} (hα : 0 < α) {z θ : ℝ} (hz : 0 < z)
    (hsin : 0 < Real.sin (2 * θ)) : 1 ≤ (Work.Spaces.Wt α z θ) ^ 2 := by
  have hγ0 : 0 ≤ Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
  rw [Work.Spaces.Wt, Work.Spaces.wTheta, mul_pow,
    rpow_neg_half_sq (Real.sin (2 * θ)) (Work.Spaces.gam α) hsin]
  have h1 : 1 ≤ (Work.Spaces.w z) ^ 2 := one_le_pow₀ (one_le_w hz)
  have h2 : 1 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
    one_le_rpow_neg hsin (Real.sin_le_one _) hγ0
  nlinarith [h1, h2]

/-- **The unweighted mixed slot is dominated by the `ℋ⁶`-integrand.**  For `1 ≤ i`, `i + j ≤ 6`
and `z > 0`, `0 < sin(2θ)`, `(D_z^jD_θ^if)² ≤ HkIntegrand α 6 f` there: the weight
`W² = w²sin^{-γ}` of `HkIntegrand` is `≥ 1`. -/
private lemma mixed_sq_le_HkIntegrand {α : ℝ} {f : ℝ → ℝ → ℝ} {b a : ℕ} (hα : 0 < α)
    (hi : 1 ≤ a) (hij : a + b ≤ 6) {z θ : ℝ} (hz : 0 < z) (hsin : 0 < Real.sin (2 * θ)) :
    (Work.Spaces.mixed b a f z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 6 f z θ := by
  have hslot : (Work.Spaces.mixed b a f z θ * Work.Spaces.Wt α z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 6 f z θ :=
    Work.Spaces.sq_le_HkIntegrand_mixed α 6 f z θ a b hi hij
  calc (Work.Spaces.mixed b a f z θ) ^ 2
      = (Work.Spaces.mixed b a f z θ) ^ 2 * 1 := by ring
    _ ≤ (Work.Spaces.mixed b a f z θ) ^ 2 * (Work.Spaces.Wt α z θ) ^ 2 :=
        mul_le_mul_of_nonneg_left (one_le_Wt_sq hα hz hsin) (sq_nonneg _)
    _ = (Work.Spaces.mixed b a f z θ * Work.Spaces.Wt α z θ) ^ 2 := by ring
    _ ≤ Work.Spaces.HkIntegrand α 6 f z θ := hslot

/-- The squared mixed weight, in terms of `w` and `sin(2θ)`. -/
private lemma Wt_sq_eq {α : ℝ} {z θ : ℝ} (hsin : 0 < Real.sin (2 * θ)) :
    (Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  rw [Work.Spaces.Wt, Work.Spaces.wTheta, mul_pow,
    rpow_neg_half_sq (Real.sin (2 * θ)) (Work.Spaces.gam α) hsin]

/-- **The weighted mixed slot is dominated by the `ℋ⁶`-integrand.**  For `1 ≤ i`, `i + j ≤ 6`
and `z > 0`, `0 < sin(2θ)`, `(D_z^jD_θ^if)²·sin(2θ)^{-γ} ≤ HkIntegrand α 6 f` there (the weight
`w² ≥ 1` is dropped). -/
private lemma mixed_rpow_sq_le_HkIntegrand {α : ℝ} {f : ℝ → ℝ → ℝ} {b a : ℕ}
    (hi : 1 ≤ a) (hij : a + b ≤ 6) {z θ : ℝ} (hz : 0 < z) (hsin : 0 < Real.sin (2 * θ)) :
    (Work.Spaces.mixed b a f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      ≤ Work.Spaces.HkIntegrand α 6 f z θ := by
  have hw2 : 1 ≤ (Work.Spaces.w z) ^ 2 := one_le_pow₀ (one_le_w hz)
  have hwpos : 0 < Work.Spaces.w z := lt_of_lt_of_le zero_lt_one (one_le_w hz)
  have hkey : (Work.Spaces.mixed b a f z θ * Work.Spaces.Wt α z θ) ^ 2
        / (Work.Spaces.w z) ^ 2
      = (Work.Spaces.mixed b a f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
    rw [mul_pow, Wt_sq_eq (α := α) hsin, div_eq_iff (pow_ne_zero 2 hwpos.ne')]
    ring
  rw [← hkey]
  calc (Work.Spaces.mixed b a f z θ * Work.Spaces.Wt α z θ) ^ 2 / (Work.Spaces.w z) ^ 2
      ≤ (Work.Spaces.mixed b a f z θ * Work.Spaces.Wt α z θ) ^ 2 := by
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < (Work.Spaces.w z) ^ 2)]
        exact le_mul_of_one_le_right (sq_nonneg _) hw2
    _ ≤ Work.Spaces.HkIntegrand α 6 f z θ :=
        Work.Spaces.sq_le_HkIntegrand_mixed α 6 f z θ a b hi hij

/-- **`D_θ` of a mixed slot.**  On the open quadrant,
`sin(2θ)·∂_θ(D_z^bD_θ^af) = D_z^bD_θ^{a+1}f` (the slot `(b, a+1)`). -/
private lemma sin_mul_pth_mixed {f : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen f)
    (b a : ℕ) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.mixed b a f) z θ
      = Work.Spaces.mixed b (a + 1) f z θ := by
  have h := Work.FTS.EllipticEst.DthIter_DzIter_eq_mixed_open
    (f := Work.Spaces.DthIter a f) (fun n => (hF.DthIter a).forall n) b 1 hz hθ
  simpa only [Work.Spaces.Dth, Work.Spaces.mixed, Work.Spaces.DthIter_succ,
    Work.Spaces.DthIter_zero] using h

/-! ## Integrability of the angular slices -/

/-- **Integrability of the unweighted angular slice of a mixed slot.**  For `a + b ≤ 6`, the
slice `σ ↦ (D_z^bD_θ^af(z,σ))²` is integrable on `Iθ`, by domination with `HkIntegrand`. -/
private lemma integrableOn_mixed_sq_Iθ {α : ℝ} {f : ℝ → ℝ → ℝ} {b a : ℕ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (hα : 0 < α) (hab : a + b ≤ 6)
    {z : ℝ} (hz : 0 < z) (hmem : Work.Spaces.HkMem α 6 f) :
    IntegrableOn (fun θ => (Work.Spaces.mixed b a f z θ) ^ 2) Work.Spaces.Iθ := by
  have hsinpos : ∀ x ∈ Set.Ioo (0 : ℝ) (π / 2), 0 < Real.sin (2 * x) :=
    fun x hx => sin_two_pos_of_mem hx
  rcases Nat.eq_zero_or_pos a with ha | ha
  · -- `a = 0`: the slot is the pure radial derivative `D_z^b f`
    have hb : b ≤ 6 := by omega
    have hmain : IntegrableOn (fun θ => (Work.Spaces.DzIter b f z θ) ^ 2) Work.Spaces.Iθ := by
      refine MeasureTheory.Integrable.mono' (hmem.1 z hz.le) ?_ ?_
      · exact Work.Spaces.aesm_slice_of_continuousOn_Qd
          (fun p : ℝ × ℝ => (Work.Spaces.DzIter b f p.1 p.2) ^ 2)
          ((hF.DzIter b).continuousOn.pow 2) hz
      · rw [Work.FTS.TransportS.restrict_Iθ_eq]
        refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.avgDzIter_sq_le_k α 6 f z θ hz
          (hsinpos θ hθ) b hb
    simpa only [ha, Work.Spaces.mixed_zero_right] using hmain
  · refine MeasureTheory.Integrable.mono' (hmem.1 z hz.le) ?_ ?_
    · exact Work.Spaces.aesm_slice_of_continuousOn_Qd
        (fun p : ℝ × ℝ => (Work.Spaces.mixed b a f p.1 p.2) ^ 2)
        ((hF.mixed b a).continuousOn.pow 2) hz
    · rw [Work.FTS.TransportS.restrict_Iθ_eq]
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact mixed_sq_le_HkIntegrand hα ha (by omega) hz (hsinpos θ hθ)

/-- **Integrability of the weighted angular slice of `∂_θ(mixed b a f)`.**  For `a + b ≤ 4`
the slice `σ ↦ (∂_θ(D_z^bD_θ^af)(z,σ))² sin(2σ)^{2-γ}` is integrable on `Iθ`; on the open
interval it equals the `ℋ⁶`-slot `(mixed b (a+1) f)²·sin(2σ)^{-γ}`, dominated by
`HkIntegrand` since `w² ≥ 1`. -/
private lemma integrableOn_pth_rpow_Iθ {α : ℝ} {f : ℝ → ℝ → ℝ} {b a : ℕ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (_hα : 0 < α) (hab : a + b ≤ 4)
    {z : ℝ} (hz : 0 < z) (hmem : Work.Spaces.HkMem α 6 f) :
    IntegrableOn (fun θ => (Work.Spaces.pth (Work.Spaces.mixed b a f) z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) Work.Spaces.Iθ := by
  have hsinpos : ∀ x ∈ Set.Ioo (0 : ℝ) (π / 2), 0 < Real.sin (2 * x) :=
    fun x hx => sin_two_pos_of_mem hx
  have hcont : ContinuousOn (fun σ : ℝ => (Work.Spaces.pth (Work.Spaces.mixed b a f) z σ) ^ 2
      * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)) (Set.Ioo (0 : ℝ) (π / 2)) := by
    refine ContinuousOn.mul ((((hF.mixed b a).pth).curry_θ hz).continuousOn.pow 2) ?_
    refine ContinuousOn.rpow_const
      (Real.continuous_sin.comp_continuousOn (continuousOn_const.mul continuousOn_id)) ?_
    intro x hx
    exact Or.inl (ne_of_gt (hsinpos x hx))
  have hIoo : Integrable (fun σ : ℝ => (Work.Spaces.pth (Work.Spaces.mixed b a f) z σ) ^ 2
      * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α))
      (volume.restrict (Set.Ioo (0 : ℝ) (π / 2))) := by
    refine MeasureTheory.Integrable.mono'
      ((hmem.1 z hz.le).mono_set (fun σ hσ => ⟨hσ.1.le, hσ.2.le⟩))
      (hcont.aestronglyMeasurable measurableSet_Ioo) ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun σ hσ => ?_)
    have hsin := hsinpos σ hσ
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hsin.le _))]
    have hid := sin_mul_pth_mixed hF b a hz hσ
    have hpth : Work.Spaces.pth (Work.Spaces.mixed b a f) z σ
        = Work.Spaces.mixed b (a + 1) f z σ / Real.sin (2 * σ) := by
      rw [eq_div_iff hsin.ne', mul_comm]
      exact hid
    rw [hpth]
    have hsplit : (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)
        = (Real.sin (2 * σ)) ^ (2 : ℝ) * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) :=
      Real.rpow_add hsin 2 (-(Work.Spaces.gam α))
    rw [hsplit, ← mul_assoc]
    have hsq : (Work.Spaces.mixed b (a + 1) f z σ / Real.sin (2 * σ)) ^ 2
        * (Real.sin (2 * σ)) ^ (2 : ℝ) = (Work.Spaces.mixed b (a + 1) f z σ) ^ 2 := by
      rw [div_pow, Real.rpow_two, div_mul_cancel₀ _ (pow_ne_zero 2 hsin.ne')]
    rw [hsq]
    exact mixed_rpow_sq_le_HkIntegrand (α := α) (f := f) (b := b) (a := a + 1) (by omega) (by omega)
      hz hsin
  show Integrable (fun σ : ℝ => (Work.Spaces.pth (Work.Spaces.mixed b a f) z σ) ^ 2
      * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)) (volume.restrict Work.Spaces.Iθ)
  rw [Work.FTS.TransportS.restrict_Iθ_eq]
  exact hIoo

/-! ## From a squared bound to the `ℋ⁶`-norm -/

/-- If `u² ≤ M·HkSq α 6 f` with `M ≥ 0`, then `|u| ≤ (√M + 1)·|f|_{ℋ⁶}`. -/
private lemma sup_le_of_sq_le {α : ℝ} {f : ℝ → ℝ → ℝ} {b a : ℕ} {z θ M : ℝ} (hM0 : 0 ≤ M)
    (hb : (Work.Spaces.mixed b a f z θ) ^ 2 ≤ M * Work.Spaces.HkSq α 6 f) :
    |Work.Spaces.mixed b a f z θ| ≤ (Real.sqrt M + 1) * Work.Spaces.HkNorm α 6 f := by
  have h1 : |Work.Spaces.mixed b a f z θ| ≤ Real.sqrt (M * Work.Spaces.HkSq α 6 f) :=
    Real.abs_le_sqrt hb
  rw [Real.sqrt_mul hM0] at h1
  have h2 : 0 ≤ Real.sqrt (Work.Spaces.HkSq α 6 f) := Real.sqrt_nonneg _
  have h3 : Real.sqrt M * Real.sqrt (Work.Spaces.HkSq α 6 f)
      ≤ (Real.sqrt M + 1) * Real.sqrt (Work.Spaces.HkSq α 6 f) := by
    have h := mul_le_mul_of_nonneg_right (by linarith [Real.sqrt_nonneg M] :
      Real.sqrt M ≤ Real.sqrt M + 1) h2
    linarith
  calc |Work.Spaces.mixed b a f z θ|
      ≤ Real.sqrt M * Real.sqrt (Work.Spaces.HkSq α 6 f) := h1
    _ ≤ (Real.sqrt M + 1) * Real.sqrt (Work.Spaces.HkSq α 6 f) := h3
    _ = (Real.sqrt M + 1) * Work.Spaces.HkNorm α 6 f := rfl

/-! ## The main theorem -/

theorem slot_jets_sup_le : ∀ (α : ℝ), 0 < α → α ≤ 1 → ∃ C : ℝ, 0 < C ∧ ∀ (f : ℝ → ℝ → ℝ),
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
    ∀ b a : ℕ, a + b ≤ 4 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed b a f z θ| ≤ C * Work.Spaces.HkNorm α 6 f := by
  intro α hα hα1
  obtain ⟨Cs, hCs0, hCs⟩ := Work.FTS.StrongPersist.N6.sliceAng_le6
  obtain ⟨Cp, hCp0, hCp⟩ := Work.FTS_EllLimOK.SlotJets.slotPthSliceLe
  obtain ⟨Cd, hCd0, hCd⟩ :=
    Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.supDzAvgLevel
  have hγ1 : 1 < Work.Spaces.gam α := Work.Spaces.one_lt_gam hα
  have hγ1' : 0 < Work.Spaces.gam α - 1 := by linarith
  set M : ℝ := 2 * (100 / (Work.Spaces.gam α - 1)) * Cp + 2 * (4 / Real.pi) * max Cs Cd
    with hMdef
  have hM0 : 0 ≤ M := by
    rw [hMdef]
    have h1 : 0 ≤ 100 / (Work.Spaces.gam α - 1) := (div_pos (by norm_num) hγ1').le
    have h2 : 0 ≤ 4 / Real.pi := (by positivity : (0 : ℝ) < 4 / Real.pi).le
    have h3 : 0 ≤ max Cs Cd := le_trans hCs0.le (le_max_left _ _)
    have h4 : 0 ≤ 2 * (100 / (Work.Spaces.gam α - 1)) * Cp :=
      mul_nonneg (mul_nonneg (by norm_num) h1) hCp0.le
    have h5 : 0 ≤ 2 * (4 / Real.pi) * max Cs Cd :=
      mul_nonneg (mul_nonneg (by norm_num) h2) h3
    linarith
  refine ⟨Real.sqrt M + 1, by positivity, ?_⟩
  intro f hF hmem b a hab z θ hz hθ0 hθ2
  have hHknn : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ0.le, hθ2.le⟩
  have haeIθ : ∀ᵐ σ ∂(volume.restrict Work.Spaces.Iθ), σ ∈ Set.Ioo (0 : ℝ) (π / 2) :=
    Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.ae_mem_Ioo_Iθ_k
  -- ## Step 1: the angular average of the slot
  have hintφ : IntegrableOn (fun σ => (Work.Spaces.mixed b a f z σ) ^ 2) Work.Spaces.Iθ :=
    integrableOn_mixed_sq_Iθ hF hα (by omega) hz hmem
  have hIu : ∫ σ in Work.Spaces.Iθ, (Work.Spaces.mixed b a f z σ) ^ 2
      ≤ max Cs Cd * Work.Spaces.HkSq α 6 f := by
    rcases Nat.eq_zero_or_pos a with ha | ha
    · -- `a = 0`: the pure `D_z`-slots (`supDzAvgLevel`)
      have hb : b + 1 ≤ 6 := by omega
      have hz0 : ∫ σ in Work.Spaces.Iθ, (Work.Spaces.mixed b a f z σ) ^ 2
          = ∫ σ in Work.Spaces.Iθ, (Work.Spaces.DzIter b f z σ) ^ 2 := by
        rw [ha, Work.Spaces.mixed_zero_right]
      rw [hz0]
      exact le_trans (hCd α f 6 b hα hF hmem hb z hz)
        (mul_le_mul_of_nonneg_right (le_max_right _ _) hHknn)
    · -- `1 ≤ a`: the mixed slots (`sliceAng_le6`) and `sin(2σ)^{-γ} ≥ 1`
      have hγ0 : 0 ≤ Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
      have hcont1 : ContinuousOn (fun σ : ℝ => (Work.Spaces.mixed b a f z σ) ^ 2
          * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))) (Set.Ioo (0 : ℝ) (π / 2)) := by
        refine ContinuousOn.mul ((((hF.mixed b a).curry_θ hz).continuousOn).pow 2) ?_
        refine ContinuousOn.rpow_const
          (Real.continuous_sin.comp_continuousOn (continuousOn_const.mul continuousOn_id)) ?_
        intro x hx
        exact Or.inl (ne_of_gt (sin_two_pos_of_mem hx))
      have hint1 : IntegrableOn (fun σ : ℝ => (Work.Spaces.mixed b a f z σ) ^ 2
          * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ := by
        have hIoo : Integrable (fun σ : ℝ => (Work.Spaces.mixed b a f z σ) ^ 2
            * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)))
            (volume.restrict (Set.Ioo (0 : ℝ) (π / 2))) := by
          refine MeasureTheory.Integrable.mono'
            ((hmem.1 z hz.le).mono_set (fun σ hσ => ⟨hσ.1.le, hσ.2.le⟩))
            (hcont1.aestronglyMeasurable measurableSet_Ioo) ?_
          refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun σ hσ => ?_)
          have hsin := sin_two_pos_of_mem hσ
          rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hsin.le _))]
          exact mixed_rpow_sq_le_HkIntegrand (α := α) (f := f) (b := b) (a := a) ha (by omega) hz hsin
        show Integrable (fun σ : ℝ => (Work.Spaces.mixed b a f z σ) ^ 2
            * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))) (volume.restrict Work.Spaces.Iθ)
        rw [Work.FTS.TransportS.restrict_Iθ_eq]
        exact hIoo
      have hle_ae : (fun σ => (Work.Spaces.mixed b a f z σ) ^ 2)
          ≤ᵐ[volume.restrict Work.Spaces.Iθ]
          (fun σ => (Work.Spaces.mixed b a f z σ) ^ 2
            * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))) := by
        filter_upwards [haeIθ] with σ hσ
        exact le_mul_of_one_le_right (sq_nonneg _)
          (one_le_rpow_neg (sin_two_pos_of_mem hσ) (Real.sin_le_one _) hγ0)
      calc ∫ σ in Work.Spaces.Iθ, (Work.Spaces.mixed b a f z σ) ^ 2
          ≤ ∫ σ in Work.Spaces.Iθ, (Work.Spaces.mixed b a f z σ) ^ 2
              * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) :=
            integral_mono_ae hintφ hint1 hle_ae
        _ ≤ Cs * Work.Spaces.HkSq α 6 f := hCs α f b a hα hα1 hF hmem ha (by omega) z hz
        _ ≤ max Cs Cd * Work.Spaces.HkSq α 6 f :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) hHknn
  -- ## Step 2: the minimiser of the slot on the middle half
  have hsub_mid : Set.Icc (π / 8) (3 * π / 8) ⊆ Set.Ioo (0 : ℝ) (π / 2) := by
    intro x hx
    exact ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2, Real.pi_pos]⟩
  have hcontφ : ContinuousOn (fun σ => (Work.Spaces.mixed b a f z σ) ^ 2)
      (Set.Icc (π / 8) (3 * π / 8)) :=
    ((((hF.mixed b a).curry_θ hz).continuousOn).mono hsub_mid).pow 2
  obtain ⟨θ₀, hθ₀mem, hθ₀le⟩ :=
    Work.FTS.TransportS.min_mid_le_avg hcontφ hintφ (fun σ _ => sq_nonneg _)
  have hθ₀I : θ₀ ∈ Work.Spaces.Iθ :=
    ⟨by linarith [hθ₀mem.1, Real.pi_pos], by linarith [hθ₀mem.2, Real.pi_pos]⟩
  have havg : (Work.Spaces.mixed b a f z θ₀) ^ 2
      ≤ (4 / Real.pi) * max Cs Cd * Work.Spaces.HkSq α 6 f := by
    have hcoe : 0 ≤ 4 / Real.pi := (by positivity : (0 : ℝ) < 4 / Real.pi).le
    have hstep := mul_le_mul_of_nonneg_left hIu hcoe
    have heq : (4 / Real.pi) * (max Cs Cd * Work.Spaces.HkSq α 6 f)
        = (4 / Real.pi) * max Cs Cd * Work.Spaces.HkSq α 6 f := by ring
    linarith [hθ₀le, hstep, heq]
  -- ## Step 3: the oscillation of the slot relative to the minimiser
  have hsub_uIcc : Set.uIcc θ θ₀ ⊆ Set.Ioo (0 : ℝ) (π / 2) := by
    intro x hx
    rw [Set.mem_uIcc] at hx
    rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨by linarith [h1], by linarith [h2, hθ₀mem.2, Real.pi_pos]⟩
    · exact ⟨by linarith [hθ₀mem.1, Real.pi_pos, h1], by linarith [h2]⟩
  have hderiv : ∀ x ∈ Set.uIcc θ θ₀, HasDerivAt (fun σ => Work.Spaces.mixed b a f z σ)
      (deriv (fun σ => Work.Spaces.mixed b a f z σ) x) x := by
    intro x hx
    have hxI := hsub_uIcc hx
    have hc := ((hF.mixed b a).curry_θ hz).differentiableOn
      Work.FTS.LocData.smoothOrder_ne_zero
    exact (hc.differentiableAt (isOpen_Ioo.mem_nhds hxI)).hasDerivAt
  have hcontd : ContinuousOn (deriv (fun σ => Work.Spaces.mixed b a f z σ))
      (Set.uIcc θ θ₀) := by
    show ContinuousOn (fun σ => Work.Spaces.pth (Work.Spaces.mixed b a f) z σ)
      (Set.uIcc θ θ₀)
    exact (((hF.mixed b a).pth.curry_θ hz).continuousOn).mono hsub_uIcc
  have hint_pth : IntegrableOn (fun σ => (deriv (fun σ' => Work.Spaces.mixed b a f z σ') σ) ^ 2
      * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)) Work.Spaces.Iθ := by
    show IntegrableOn (fun σ => (Work.Spaces.pth (Work.Spaces.mixed b a f) z σ) ^ 2
      * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)) Work.Spaces.Iθ
    exact integrableOn_pth_rpow_Iθ hF hα hab hz hmem
  have hosc := Work.FTS.H2.OscSqLe α hα hα1 (fun σ => Work.Spaces.mixed b a f z σ)
    hθI hθ₀I hderiv hcontd hint_pth
  have hIh : ∫ σ in Work.Spaces.Iθ, (deriv (fun σ' => Work.Spaces.mixed b a f z σ') σ) ^ 2
      * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α) ≤ Cp * Work.Spaces.HkSq α 6 f := by
    have hsym : Work.Spaces.Iθ =ᵐ[volume] Set.Ioo (0 : ℝ) (π / 2) :=
      (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := Real.pi / 2)).symm
    rw [MeasureTheory.setIntegral_congr_set hsym]
    show ∫ σ in Set.Ioo (0 : ℝ) (π / 2), (Work.Spaces.pth (Work.Spaces.mixed b a f) z σ) ^ 2
      * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α) ≤ Cp * Work.Spaces.HkSq α 6 f
    exact hCp α f b a hα hα1 hF hmem hab z hz
  have hosc2 : 2 * (Work.Spaces.mixed b a f z θ - Work.Spaces.mixed b a f z θ₀) ^ 2
      ≤ 2 * (100 / (Work.Spaces.gam α - 1)) * Cp * Work.Spaces.HkSq α 6 f := by
    have hcoe : 0 ≤ 100 / (Work.Spaces.gam α - 1) := (div_pos (by norm_num) hγ1').le
    have hstep : (100 / (Work.Spaces.gam α - 1))
        * (∫ σ in Work.Spaces.Iθ, (deriv (fun σ' => Work.Spaces.mixed b a f z σ') σ) ^ 2
            * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α))
        ≤ (100 / (Work.Spaces.gam α - 1)) * (Cp * Work.Spaces.HkSq α 6 f) :=
      mul_le_mul_of_nonneg_left hIh hcoe
    have hchain := le_trans hosc hstep
    have h2 := mul_le_mul_of_nonneg_left hchain (by norm_num : (0 : ℝ) ≤ 2)
    have heq : 2 * ((100 / (Work.Spaces.gam α - 1)) * (Cp * Work.Spaces.HkSq α 6 f))
        = 2 * (100 / (Work.Spaces.gam α - 1)) * Cp * Work.Spaces.HkSq α 6 f := by ring
    linarith [h2, heq]
  have havg2 : 2 * (Work.Spaces.mixed b a f z θ₀) ^ 2
      ≤ 2 * (4 / Real.pi) * max Cs Cd * Work.Spaces.HkSq α 6 f := by
    have h2 := mul_le_mul_of_nonneg_left havg (by norm_num : (0 : ℝ) ≤ 2)
    have heq : 2 * ((4 / Real.pi) * max Cs Cd * Work.Spaces.HkSq α 6 f)
        = 2 * (4 / Real.pi) * max Cs Cd * Work.Spaces.HkSq α 6 f := by ring
    linarith [h2, heq]
  -- ## Step 4: assembly
  refine sup_le_of_sq_le hM0 ?_
  have hsplit : (Work.Spaces.mixed b a f z θ) ^ 2
      ≤ 2 * (Work.Spaces.mixed b a f z θ - Work.Spaces.mixed b a f z θ₀) ^ 2
        + 2 * (Work.Spaces.mixed b a f z θ₀) ^ 2 := by
    nlinarith [sq_nonneg (Work.Spaces.mixed b a f z θ
      - 2 * Work.Spaces.mixed b a f z θ₀)]
  calc (Work.Spaces.mixed b a f z θ) ^ 2
      ≤ 2 * (Work.Spaces.mixed b a f z θ - Work.Spaces.mixed b a f z θ₀) ^ 2
        + 2 * (Work.Spaces.mixed b a f z θ₀) ^ 2 := hsplit
    _ ≤ 2 * (100 / (Work.Spaces.gam α - 1)) * Cp * Work.Spaces.HkSq α 6 f
        + 2 * (4 / Real.pi) * max Cs Cd * Work.Spaces.HkSq α 6 f := add_le_add hosc2 havg2
    _ = M * Work.Spaces.HkSq α 6 f := by rw [hMdef]; ring

end Work.FTS_EllLimOK.SlotSup
