import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.H2.T1Q.Basic
import Submission.Work.FTS.H2.HQ.HardyZQ
import Submission.Work.FTS.H2.MinLeAvg
import Submission.Work.FTS.H2.OscSqLe
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.FTS.H2.HQ.DthDzIterComm
import Submission.Work.Spaces.bt_aux
import Submission.Work.H2.T1Q.SliceSupOpen
import Submission.Work.H2.T1Q.SupAbsThOAesm

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

namespace Work.H2.T1Q

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open scoped Real Topology
open MeasureTheory Set Filter
open Work.Spaces

/-! ## The interior-class weight identity for the `D_θ`-slot -/

/-- On the open quadrant, `D_z^b D_θ f = sin(2θ)·∂_θ(D_z^b f)` for `SmoothQuad` data
(immediate from the interior commutation `Work.FTS.H2.HQ.DthDzIterComm`, which is the
`SmoothQuad`-version of `Work.Spaces.Dth_DzIter_comm_eqOn`). -/
private theorem mixed_eq_sin_mul_pth_quad (f : ℝ → ℝ → ℝ) (hf : Work.FTS.LocData.SmoothQuad f)
    (b : ℕ) {z θ : ℝ} (hz : z ∈ Iz) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    mixed b 1 f z θ = Real.sin (2 * θ) * pth (DzIter b f) z θ := by
  rw [← Work.FTS.H2.HQ.DthDzIterComm b f hf z hz θ hθ]
  rfl

/-- The weight identity behind the angular Hardy inequality, in the interior class:
`(∂_θD_z^b f)² w² sin(2θ)^{2-γ} = (D_z^bD_θf · W)²` on the open quadrant.  This is
`Work.Spaces.bt_mixed_weight_id` with `SmoothNbhd` replaced by `SmoothQuad`. -/
private theorem pth_DzIter_weight_sq_quad (α : ℝ) (f : ℝ → ℝ → ℝ)
    (hf : Work.FTS.LocData.SmoothQuad f) (hα : 0 < α) (hα1 : α ≤ 1) (b : ℕ) {z θ : ℝ}
    (hz : z ∈ Iz) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    (pth (DzIter b f) z θ) ^ 2 * (w z) ^ 2 * (Real.sin (2 * θ)) ^ (2 - gam α)
      = (mixed b 1 f z θ * Wt α z θ) ^ 2 := by
  refine bt_mixed_weight_gen α z θ hα hα1 ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    (pth (DzIter b f) z θ) (mixed b 1 f z θ) ?_
  rw [← mixed_eq_sin_mul_pth_quad f hf b hz hθ]

/-! ## Almost-everywhere identifications of the intervals `Iθ` and `Iz` -/

/-- `Iθ = [0,π/2]` differs from the open interval `(0,π/2)` by the null set `{0,π/2}`. -/
private theorem Iθ_ae_eq_Ioo : (Iθ : Set ℝ) =ᵐ[volume] Set.Ioo 0 (π / 2) :=
  (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := π / 2)).symm

/-- `Iz = [0,∞)` differs from the open half-line `(0,∞)` by the null set `{0}`. -/
private theorem Iz_ae_eq_Ioi : (Iz : Set ℝ) =ᵐ[volume] Set.Ioi 0 :=
  (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0)).symm

private theorem restrict_Iθ : volume.restrict Iθ = volume.restrict (Set.Ioo 0 (π / 2)) :=
  MeasureTheory.Measure.restrict_congr_set Iθ_ae_eq_Ioo

private theorem restrict_Iz : volume.restrict Iz = volume.restrict (Set.Ioi 0) :=
  MeasureTheory.Measure.restrict_congr_set Iz_ae_eq_Ioi

/-! ## Integrability of the two angular slices -/

/-- On `z > 0`, `w z ≥ 1`. -/
private theorem one_le_w_of_pos {z : ℝ} (hz : 0 < z) : 1 ≤ w z := by
  rw [w, le_div_iff₀ (by positivity : (0 : ℝ) < z ^ 2)]
  nlinarith

/-- For `z > 0`, the slice `θ ↦ (D_z³f z θ)²` is integrable on `Iθ`, by domination by the
`ℋ⁴`-integrand (the light weight `w z / sin(2θ)^{η/2}` is `≥ 1` there). -/
private theorem integrableOn_sq_DzIter_three {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hsq : Work.FTS.LocData.SmoothQuad f) (hmem : HkMem α 4 f) {z : ℝ} (hz : z ∈ Iz)
    (hz0 : 0 < z) :
    IntegrableOn (fun θ => (DzIter 3 f z θ) ^ 2) Iθ := by
  have hz1 : z ∈ Set.Ioi (-1 : ℝ) := Set.mem_Ioi.mpr (by linarith)
  have hkey : Integrable (fun θ => (DzIter 3 f z θ) ^ 2)
      (volume.restrict (Set.Ioo 0 (π / 2))) := by
    refine MeasureTheory.Integrable.mono'
      ((hmem.1 z hz).mono_set Set.Ioo_subset_Icc_self) ?_ ?_
    · exact ((((hsq.DzIter 3).curry_θ hz1).continuousOn.aestronglyMeasurable
        measurableSet_Ioo).pow 2)
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      have hsin : 0 < Real.sin (2 * θ) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
      have hspos : 0 < (Real.sin (2 * θ)) ^ (eta / 2) := Real.rpow_pos_of_pos hsin _
      have hsle : (Real.sin (2 * θ)) ^ (eta / 2) ≤ 1 :=
        Real.rpow_le_one hsin.le (Real.sin_le_one _) (by norm_num [eta])
      have hw1 : 1 ≤ w z := one_le_w_of_pos hz0
      have hL : 1 ≤ w z / (Real.sin (2 * θ)) ^ (eta / 2) := by
        rw [le_div_iff₀ hspos]
        linarith
      have h1 : (DzIter 3 f z θ) ^ 2
          ≤ (DzIter 3 f z θ * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2 := by
        rw [mul_pow]
        exact le_mul_of_one_le_right (sq_nonneg _) (by nlinarith)
      exact h1.trans (sq_le_HkIntegrand_z α 4 f z θ 3 (by norm_num))
  show Integrable (fun θ => (DzIter 3 f z θ) ^ 2) (volume.restrict Iθ)
  rw [restrict_Iθ]
  exact hkey

/-- For `z > 0`, the weighted slice `(∂_θD_z³f z ·)² sin(2·)^{2-γ}` is integrable on `Iθ`:
after multiplying by `(w z)²` it is the mixed slot `(D_z³D_θf · W)²`, integrable by
`Work.FTS.H2.HQ.integrableOn_slice_mixed_Wt_sq`. -/
private theorem integrableOn_pth_weight {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hsq : Work.FTS.LocData.SmoothQuad f) (hmem : HkMem α 4 f) (hα : 0 < α) (hα1 : α ≤ 1)
    {z : ℝ} (hz : z ∈ Iz) (hz0 : 0 < z) :
    IntegrableOn
      (fun θ => (pth (DzIter 3 f) z θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - gam α)) Iθ := by
  have hW := Work.FTS.H2.HQ.integrableOn_slice_mixed_Wt_sq α f hsq hmem 3 1 le_rfl
    (by norm_num) hz
  have hW' : Integrable (fun θ => (mixed 3 1 f z θ * Wt α z θ) ^ 2) (volume.restrict Iθ) := hW
  have h2 : Integrable (fun θ => ((w z) ^ 2)⁻¹ * (mixed 3 1 f z θ * Wt α z θ) ^ 2)
      (volume.restrict Iθ) := hW'.const_mul _
  have h2' : Integrable (fun θ => ((w z) ^ 2)⁻¹ * (mixed 3 1 f z θ * Wt α z θ) ^ 2)
      (volume.restrict (Set.Ioo 0 (π / 2))) := by
    rw [← restrict_Iθ]
    exact h2
  have hw2 : (w z) ^ 2 ≠ 0 := by
    rw [w, div_pow]
    exact div_ne_zero (pow_ne_zero 2 (pow_ne_zero 2 (by linarith : (1 : ℝ) + z ≠ 0)))
      (pow_ne_zero 2 (pow_ne_zero 2 (ne_of_gt hz0)))
  have hae : (fun θ => (pth (DzIter 3 f) z θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - gam α))
      =ᵐ[volume.restrict (Set.Ioo 0 (π / 2))]
      (fun θ => ((w z) ^ 2)⁻¹ * (mixed 3 1 f z θ * Wt α z θ) ^ 2) := by
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    dsimp only
    have hX : (w z) ^ 2 * ((pth (DzIter 3 f) z θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - gam α))
        = (mixed 3 1 f z θ * Wt α z θ) ^ 2 := by
      rw [← pth_DzIter_weight_sq_quad α f hsq hα hα1 3 hz hθ]
      ring
    rw [← hX, inv_mul_cancel_left₀ hw2]
  have h3 : Integrable (fun θ => (pth (DzIter 3 f) z θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - gam α))
      (volume.restrict (Set.Ioo 0 (π / 2))) := h2'.congr hae.symm
  show Integrable
      (fun θ => (pth (DzIter 3 f) z θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - gam α))
      (volume.restrict Iθ)
  rw [restrict_Iθ]
  exact h3

/-! ## The two `H^k`-blocks -/

/-- The `D_z³`-block: multiplying the angular slice integral of `(D_z³f)²` by `w(z)²` costs
only the light weight, hence is dominated by the `ℋ⁴`-integrand. -/
private theorem block_z (α : ℝ) (f : ℝ → ℝ → ℝ) (hsq : Work.FTS.LocData.SmoothQuad f)
    (hmem : HkMem α 4 f) {z : ℝ} (hz : z ∈ Iz) (hz0 : 0 < z) :
    (∫ θ in Iθ, (DzIter 3 f z θ) ^ 2) * (w z) ^ 2 ≤ ∫ θ in Iθ, HkIntegrand α 4 f z θ := by
  have hwz_nn : 0 ≤ w z := div_nonneg (sq_nonneg _) (sq_nonneg _)
  have hsinpos : ∀ θ ∈ Set.Ioo 0 (π / 2), 0 < Real.sin (2 * θ) := fun θ hθ =>
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have e1 : (∫ θ in Iθ, (DzIter 3 f z θ) ^ 2) * (w z) ^ 2
      = ∫ θ in Iθ, (DzIter 3 f z θ * w z) ^ 2 := by
    rw [mul_comm, ← MeasureTheory.integral_const_mul]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun θ => by ring))
  calc (∫ θ in Iθ, (DzIter 3 f z θ) ^ 2) * (w z) ^ 2
      = ∫ θ in Iθ, (DzIter 3 f z θ * w z) ^ 2 := e1
    _ ≤ ∫ θ in Iθ, HkIntegrand α 4 f z θ := by
        refine MeasureTheory.integral_mono_of_nonneg
          (Filter.Eventually.of_forall (fun θ => sq_nonneg _)) (hmem.1 z hz) ?_
        rw [restrict_Iθ]
        refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => by
          have hsle : (Real.sin (2 * θ)) ^ (eta / 2) ≤ 1 :=
            Real.rpow_le_one (le_of_lt (hsinpos θ hθ)) (Real.sin_le_one _) (by norm_num [eta])
          have hspos : 0 < (Real.sin (2 * θ)) ^ (eta / 2) :=
            Real.rpow_pos_of_pos (hsinpos θ hθ) _
          have hL : w z ≤ w z / (Real.sin (2 * θ)) ^ (eta / 2) := by
            rw [le_div_iff₀ hspos]
            nlinarith [hwz_nn, hsle]
          have hstep : (DzIter 3 f z θ * w z) ^ 2
              ≤ (DzIter 3 f z θ * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2 := by
            rw [sq_le_sq, abs_mul, abs_mul, abs_of_nonneg hwz_nn,
              abs_of_nonneg (div_nonneg hwz_nn (le_of_lt hspos))]
            exact mul_le_mul_of_nonneg_left hL (abs_nonneg _)
          exact hstep.trans (sq_le_HkIntegrand_z α 4 f z θ 3 (by norm_num)))

/-- The mixed block: `∫_θ (∂_θD_z³f)² sin(2θ)^{2-γ} · w(z)²` is exactly the angular
integral of the `(D_z³D_θf · W)²` slot, dominated by the `ℋ⁴`-integrand. -/
private theorem block_mixed (α : ℝ) (f : ℝ → ℝ → ℝ) (hsq : Work.FTS.LocData.SmoothQuad f)
    (hmem : HkMem α 4 f) (hα : 0 < α) (hα1 : α ≤ 1) {z : ℝ} (hz : z ∈ Iz) (hz0 : 0 < z) :
    (∫ θ in Iθ, (pth (DzIter 3 f) z θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - gam α)) * (w z) ^ 2
      ≤ ∫ θ in Iθ, HkIntegrand α 4 f z θ := by
  have e2 : (∫ θ in Iθ, (pth (DzIter 3 f) z θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - gam α))
        * (w z) ^ 2 = ∫ θ in Iθ, (mixed 3 1 f z θ * Wt α z θ) ^ 2 := by
    rw [mul_comm, ← MeasureTheory.integral_const_mul]
    have h1 : (∫ θ in Iθ, (w z) ^ 2
        * ((pth (DzIter 3 f) z θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - gam α)))
        = ∫ θ in Set.Ioo 0 (π / 2), (w z) ^ 2
            * ((pth (DzIter 3 f) z θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - gam α)) :=
      MeasureTheory.setIntegral_congr_set Iθ_ae_eq_Ioo
    have h2 : (∫ θ in Iθ, (mixed 3 1 f z θ * Wt α z θ) ^ 2)
        = ∫ θ in Set.Ioo 0 (π / 2), (mixed 3 1 f z θ * Wt α z θ) ^ 2 :=
      MeasureTheory.setIntegral_congr_set Iθ_ae_eq_Ioo
    rw [h1, h2]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun θ hθ => ?_)
    rw [← pth_DzIter_weight_sq_quad α f hsq hα hα1 3 hz hθ]
    ring
  rw [e2]
  refine MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall (fun θ => sq_nonneg _))
    (hmem.1 z hz) (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
      (fun θ _ => sq_le_HkIntegrand_mixed α 4 f z θ 1 3 le_rfl (by norm_num)))

/-! ## The slicewise bound and its consequences -/

/-- The two-term majorant of the slice estimate at the fixed radius `z`. -/
private def Bfun (α : ℝ) (f : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  (4 / Real.pi) * (∫ θ in Iθ, (DzIter 3 f z θ) ^ 2)
    + (200 / (gam α - 1))
        * ∫ θ in Iθ, (pth (DzIter 3 f) z θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - gam α)

/-- The slicewise estimate of `Work.H2.T1Q.SliceSupOpen` instantiated at
`u = θ ↦ D_z³f z θ`. -/
private theorem slice_bound (α : ℝ) (f : ℝ → ℝ → ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hsq : Work.FTS.LocData.SmoothQuad f) (hmem : HkMem α 4 f) {z : ℝ} (hz0 : 0 < z) :
    ∀ θ ∈ Set.Ioo 0 (π / 2), (DzIter 3 f z θ) ^ 2 ≤ Bfun α f z := by
  have hzIz : z ∈ Iz := by rw [Iz, Set.mem_Ici]; linarith
  have hz1 : z ∈ Set.Ioi (-1 : ℝ) := Set.mem_Ioi.mpr (by linarith)
  have hslice : ContDiffOn ℝ 1 (fun θ => DzIter 3 f z θ) (Set.Ioo 0 (π / 2)) :=
    ((hsq.DzIter 3).curry_θ hz1).of_le (by simp [Work.Stability.smoothOrder])
  have hint2 := integrableOn_sq_DzIter_three hsq hmem hzIz hz0
  have hintp := integrableOn_pth_weight hsq hmem hα hα1 hzIz hz0
  exact SliceSupOpen α (fun θ => DzIter 3 f z θ) hα hα1 hslice hint2 hintp

/-- The boundedness of the angular slice of `D_z³f` at `z > 0`, needed by the countability
argument of `Work.H2.T1Q.SupAbsThOAesm`. -/
private theorem slice_bddAbove (α : ℝ) (f : ℝ → ℝ → ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hsq : Work.FTS.LocData.SmoothQuad f) (hmem : HkMem α 4 f) {z : ℝ} (hz0 : 0 < z) :
    BddAbove {y : ℝ | ∃ θ ∈ Set.Ioo 0 (π / 2), y = |DzIter 3 f z θ|} :=
  ⟨Real.sqrt (Bfun α f z), fun y hy => by
    obtain ⟨θ, hθ, rfl⟩ := hy
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (slice_bound α f hα hα1 hsq hmem hz0 θ hθ)⟩

/-- **The a.e. pointwise bound.**  For almost every `z ∈ Iz` (namely for `z > 0`) the squared
weighted angular supremum of `D_z³f` is dominated by
`(4/π + 200/(γ-1))·∫_θ HkIntegrand α 4 f z θ`. -/
private theorem ae_sup_bound (α : ℝ) (f : ℝ → ℝ → ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hsq : Work.FTS.LocData.SmoothQuad f) (hmem : HkMem α 4 f) :
    ∀ᵐ z ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      (Work.FTS.H2.supAbsThO (DzIter 3 f) z * w z) ^ 2
        ≤ (4 / Real.pi + 200 / (gam α - 1)) * ∫ θ in Iθ, HkIntegrand α 4 f z θ := by
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hzpos
  have hzIz : z ∈ Iz := by rw [Iz, Set.mem_Ici]; exact le_of_lt hzpos
  have hwz_nn : 0 ≤ w z := div_nonneg (sq_nonneg _) (sq_nonneg _)
  have hγpos : 0 < gam α - 1 := by rw [gam_sub_one]; linarith
  have hsinθ_nn : ∀ θ ∈ Iθ, 0 ≤ Real.sin (2 * θ) := fun θ hθ =>
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hBnn : 0 ≤ Bfun α f z := by
    rw [Bfun]
    refine add_nonneg (mul_nonneg (div_nonneg (by norm_num) Real.pi_pos.le)
      (MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ _ => sq_nonneg _))) ?_
    refine mul_nonneg (div_nonneg (by norm_num) (le_of_lt hγpos))
      (MeasureTheory.setIntegral_nonneg measurableSet_Icc
        (fun θ hθ => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hsinθ_nn θ hθ) _)))
  have hsup_nn : 0 ≤ Work.FTS.H2.supAbsThO (DzIter 3 f) z :=
    le_trans (abs_nonneg _) (le_csSup (slice_bddAbove α f hα hα1 hsq hmem hzpos)
      ⟨π / 4, ⟨by positivity, by linarith [Real.pi_pos]⟩, rfl⟩)
  have hsup_le : Work.FTS.H2.supAbsThO (DzIter 3 f) z ≤ Real.sqrt (Bfun α f z) :=
    Work.FTS.H2.supAbsThO_le (fun θ hθ => by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt (slice_bound α f hα hα1 hsq hmem hzpos θ hθ))
  have hstep : (Work.FTS.H2.supAbsThO (DzIter 3 f) z * w z) ^ 2
      ≤ Bfun α f z * (w z) ^ 2 := by
    have h1 : Work.FTS.H2.supAbsThO (DzIter 3 f) z * w z ≤ Real.sqrt (Bfun α f z) * w z :=
      mul_le_mul_of_nonneg_right hsup_le hwz_nn
    have h0 : 0 ≤ Work.FTS.H2.supAbsThO (DzIter 3 f) z * w z := mul_nonneg hsup_nn hwz_nn
    calc (Work.FTS.H2.supAbsThO (DzIter 3 f) z * w z) ^ 2
        ≤ (Real.sqrt (Bfun α f z) * w z) ^ 2 := pow_le_pow_left₀ h0 h1 2
      _ = Bfun α f z * (w z) ^ 2 := by rw [mul_pow, Real.sq_sqrt hBnn]
  calc (Work.FTS.H2.supAbsThO (DzIter 3 f) z * w z) ^ 2
      ≤ Bfun α f z * (w z) ^ 2 := hstep
    _ = (4 / Real.pi) * ((∫ θ in Iθ, (DzIter 3 f z θ) ^ 2) * (w z) ^ 2)
          + (200 / (gam α - 1)) * ((∫ θ in Iθ,
              (pth (DzIter 3 f) z θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - gam α)) * (w z) ^ 2) := by
        rw [Bfun]; ring
    _ ≤ (4 / Real.pi) * (∫ θ in Iθ, HkIntegrand α 4 f z θ)
          + (200 / (gam α - 1)) * (∫ θ in Iθ, HkIntegrand α 4 f z θ) :=
        add_le_add
          (mul_le_mul_of_nonneg_left (block_z α f hsq hmem hzIz hzpos) (by positivity))
          (mul_le_mul_of_nonneg_left (block_mixed α f hsq hmem hα hα1 hzIz hzpos) (by positivity))
    _ = (4 / Real.pi + 200 / (gam α - 1)) * (∫ θ in Iθ, HkIntegrand α 4 f z θ) := by ring

/-! ## The target -/

/-- The angular supremum of `D_z³f`, weighted by `w` and squared, is bounded in `L²(dz)` by
`C/(γ-1)·|f|²_{ℋ⁴}` — the interior-class replacement of `Work.FTS.H2.SupThetaInt` (which is
stated for analytic data and with the supremum over the *closed* interval `Iθ`).  Only the
supremum over the open interval `(0,π/2)` is meaningful for `SmoothQuad` data, whence
`Work.FTS.H2.supAbsThO`.

Route: at every `z ∈ Iz` the slice `θ ↦ D_z³f z θ` is `C^∞` on `(0,π/2)` and integrable, so
there is `θ₀` with `|D_z³f z θ₀|² ≤ (2/π)∫_θ (D_z³f z θ)²dθ`; the oscillation bound
`OscSqLe` gives, for every `θ`,
`(D_z³f z θ)² ≤ 2(D_z³f z θ₀)² + (200/(γ-1))·∫_σ (∂_θD_z³f z σ)²sin(2σ)^{2-γ}`.
The first integral is bounded by `HkSq α 4 f` (the radial Hardy inequality `HQ.HardyZQ` on the
`z`-slice at each `θ`, then the slot `D_z⁴f`), and `(∂_θD_z³f)²sin(2σ)^{2-γ} = (mixed 3 1 f)²·sin(2σ)^{-γ}`
is a single summand of `HkIntegrand α 4 f`, so the second integral contributes
`(200/(γ-1))·HkSq α 4 f`; multiplying by `w(z)²` and integrating in `z` gives the stated bound,
and the integrability follows by domination.  Note that the function
`z ↦ (supAbsThO (DzIter 3 f) z * w z)²` must itself be shown a.e. strongly measurable for
`volume.restrict Iz`: `supAbsThO u z` equals the supremum of `|u z θ|` over the countable
dense set `(0,π/2) ∩ ℚ` (continuity in `θ`), which is a countable supremum of functions
continuous on `Iz`. -/
theorem SupThetaIntQ : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : Work.FTS.Galerkin.Fn), 0 < α → α ≤ 1 →
    Work.FTS.LocData.SmoothQuad f → Work.Spaces.DecayAll 4 f → Work.Spaces.HkMem α 4 f →
    (MeasureTheory.IntegrableOn
        (fun z => (Work.FTS.H2.supAbsThO (Work.Spaces.DzIter 3 f) z * Work.Spaces.w z) ^ 2)
        Work.Spaces.Iz) ∧
      (∫ z in Work.Spaces.Iz, (Work.FTS.H2.supAbsThO (Work.Spaces.DzIter 3 f) z
          * Work.Spaces.w z) ^ 2 ≤ C / (Work.Spaces.gam α - 1) * Work.Spaces.HkSq α 4 f) := by
  refine ⟨1000, by norm_num, ?_⟩
  intro α f hα hα1 hsq _hdec hmem
  have hγpos : 0 < gam α - 1 := by rw [gam_sub_one]; linarith
  have hIθ_meas : MeasurableSet Iθ := measurableSet_Icc
  have hIz_meas : MeasurableSet Iz := measurableSet_Ici
  -- ## the a.e. pointwise bound, transported to `volume.restrict Iz`
  have hstep : ∀ᵐ z ∂(volume.restrict Iz),
      (Work.FTS.H2.supAbsThO (DzIter 3 f) z * w z) ^ 2
        ≤ (4 / Real.pi + 200 / (gam α - 1)) * ∫ θ in Iθ, HkIntegrand α 4 f z θ := by
    rw [restrict_Iz]
    exact ae_sup_bound α f hα hα1 hsq hmem
  -- ## the a.e. strong measurability of `z ↦ supAbsThO (DzIter 3 f) z`
  have hmeas_sup : AEMeasurable (fun z => Work.FTS.H2.supAbsThO (DzIter 3 f) z)
      (volume.restrict Iz) := by
    refine SupAbsThOAesm (DzIter 3 f) ?_ ?_ ?_
    · -- continuity of the angular slices
      intro z hz
      have hz1 : z ∈ Set.Ioi (-1 : ℝ) := by
        rw [Iz, Set.mem_Ici] at hz
        exact Set.mem_Ioi.mpr (by linarith)
      exact ((hsq.DzIter 3).curry_θ hz1).continuousOn
    · -- measurability of the `z`-slices at rational angles
      intro q hq
      have hcd : ContDiffOn ℝ Work.Stability.smoothOrder (fun z => DzIter 3 f z (q : ℝ))
          (Set.Ioi (-1 : ℝ)) := (hsq.DzIter 3).curry_z hq
      refine (hcd.continuousOn.mono ?_).aemeasurable hIz_meas
      intro z hz
      rw [Iz, Set.mem_Ici] at hz
      exact Set.mem_Ioi.mpr (by linarith)
    · -- a.e. boundedness of the angular slices
      rw [restrict_Iz]
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hzpos
      exact slice_bddAbove α f hα hα1 hsq hmem hzpos
  have hw_meas : AEMeasurable (fun z : ℝ => w z) (volume.restrict Iz) := by
    rw [restrict_Iz]
    change AEMeasurable (fun z : ℝ => (1 + z) ^ 2 / z ^ 2) (volume.restrict (Set.Ioi 0))
    exact (ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
      (continuousOn_id.pow 2) (fun z hz => pow_ne_zero 2 (ne_of_gt hz))).aemeasurable
        measurableSet_Ioi
  have hf_aesm : AEStronglyMeasurable
      (fun z => (Work.FTS.H2.supAbsThO (DzIter 3 f) z * w z) ^ 2) (volume.restrict Iz) :=
    ((hmeas_sup.mul hw_meas).pow_const 2).aestronglyMeasurable
  -- ## domination
  have hdom_nn : ∀ z, 0 ≤ (4 / Real.pi + 200 / (gam α - 1))
      * (∫ θ in Iθ, HkIntegrand α 4 f z θ) := fun z =>
    mul_nonneg (by positivity)
      (MeasureTheory.setIntegral_nonneg hIθ_meas (fun θ _ => HkIntegrand_nonneg α 4 f z θ))
  have hdom_int : Integrable (fun z => (4 / Real.pi + 200 / (gam α - 1))
      * (∫ θ in Iθ, HkIntegrand α 4 f z θ)) (volume.restrict Iz) := hmem.2.const_mul _
  have hf_int : IntegrableOn
      (fun z => (Work.FTS.H2.supAbsThO (DzIter 3 f) z * w z) ^ 2) Iz := by
    refine MeasureTheory.Integrable.mono' hdom_int hf_aesm ?_
    filter_upwards [hstep] with z hz
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hz
  refine ⟨hf_int, ?_⟩
  have hmain : ∫ z in Iz, (Work.FTS.H2.supAbsThO (DzIter 3 f) z * w z) ^ 2
      ≤ (4 / Real.pi + 200 / (gam α - 1)) * HkSq α 4 f := by
    calc ∫ z in Iz, (Work.FTS.H2.supAbsThO (DzIter 3 f) z * w z) ^ 2
        ≤ ∫ z in Iz, (4 / Real.pi + 200 / (gam α - 1))
            * (∫ θ in Iθ, HkIntegrand α 4 f z θ) :=
          MeasureTheory.integral_mono_of_nonneg
            (Filter.Eventually.of_forall (fun z => sq_nonneg _)) hdom_int hstep
      _ = (4 / Real.pi + 200 / (gam α - 1))
            * (∫ z in Iz, ∫ θ in Iθ, HkIntegrand α 4 f z θ) :=
          MeasureTheory.integral_const_mul _ _
      _ = (4 / Real.pi + 200 / (gam α - 1)) * HkSq α 4 f := rfl
  have hcoef : (4 / Real.pi + 200 / (gam α - 1)) ≤ 1000 / (gam α - 1) := by
    have heq : (4 / Real.pi + 200 / (gam α - 1))
        = (4 / Real.pi * (gam α - 1) + 200) / (gam α - 1) := by
      field_simp
    rw [heq]
    refine div_le_div_of_nonneg_right ?_ (le_of_lt hγpos)
    have h1 : (4 / Real.pi) * (gam α - 1) ≤ (4 / Real.pi) * 1 :=
      mul_le_mul_of_nonneg_left (by rw [gam]; linarith) (by positivity)
    have h2 : (4 : ℝ) / Real.pi ≤ 4 := by
      rw [div_le_iff₀ Real.pi_pos]
      nlinarith [Real.pi_gt_three]
    linarith
  calc ∫ z in Iz, (Work.FTS.H2.supAbsThO (DzIter 3 f) z * w z) ^ 2
      ≤ (4 / Real.pi + 200 / (gam α - 1)) * HkSq α 4 f := hmain
    _ ≤ 1000 / (gam α - 1) * HkSq α 4 f :=
        mul_le_mul_of_nonneg_right hcoef (HkSq_nonneg α 4 f)

end Work.H2.T1Q
