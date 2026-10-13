/-
Copyright: work module for the Elgindi finite-time singularity project.

# `F_*(F)·sin 2θ ∈ ℋ^k` for the source of an elliptic solution

The certificate `Work.FTS.EllipticEst.Cert.HkMem_Fstar_sin`:

  `EllHyp α k F Ψ`, `0 < α ≤ 1/4`  ⟹  `F_*(F)·sin 2θ ∈ ℋ^k`.

The mathematics is the membership half of §'Elliptic Regularity Estimates' (Elgindi,
Annals 194 (3) 2021): the angular moment `F_*(F)(z) = ∫_θ F(z,θ) sinθcos²θ dθ` is
controlled by the weighted `L²`-theory of the source `F`, so that the product
`F_*(F)(z)·sin 2θ` lies in the weighted Sobolev space `ℋ^k` as soon as `F` does.

## The route (and why the obvious one is blocked)

`EllHyp` does **not** provide `Work.Spaces.SmoothNbhd F`: it only gives the equation
`bslOp α Ψ = F` on the *open* quadrant, and Lean's `Real.tan` is totalised
(`Real.tan (π/2) = 0`), so `z ↦ bslOp α Ψ z θ` genuinely jumps at `θ = π/2`
(see `Submission/Work/FTS/EllipticEst/alphaDzW_Hk_le.lean`, audit point 3).  The
certificate is therefore proved in the open-quadrant class
`Work.FTS.EllipticEst.SmoothOpen` (`SmoothOpen_bslOp` produces it from `SmoothNbhd Ψ`
and the equation).

For a *separated* function `g z θ = R(z)·sin 2θ` the `ℋ^k`-integrand is an explicit
finite combination of the radial iterates `radIter R i z = (D_z^i R)(z)` with two fixed
angular profiles (`HkExp` of `Cert/Defs.lean`, `HkIntegrand_radial_sin`).  Its
`θ`-integral is therefore the fixed linear combination `integral_HkExp`, and — since
`F_*(D_z^i F)` is (a.e.) the `i`-th iterate `D_z^i(F_*(F))` of the moment
(`radIter_Bmom_ae`) — the slice integral is dominated by the slice integral of the
*source*:

  `∫_θ HkIntegrand α k (F_*·sin 2θ) z θ ≤ K_k ∫_θ HkIntegrand α k F z θ`   (a.e. `z`),

the radial content being Cauchy–Schwarz for the moment
(`FstarDzIter_sq_mul_w_le_open`) and the angular content the uniform bound
`(D_θ^i(sin 2θ))² sin(2θ)^{-γ} ≤ angK i` (`angK_bound`).

Membership follows: the slices are integrable (continuity + boundedness on the open
interval), the slice integral is a.e. equal to an explicitly measurable function of `z`
(a finite combination of the moments `Bmom F i`, `aestronglyMeasurable_integral_Itheta_Q0`),
and it is dominated by the integrable slice integral of `F` (`hmem.2`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.Cert.Defs
import Submission.Work.FTS.EllipticEst.Cert.SmoothOpen_bslOp
import Submission.Work.FTS.EllipticEst.Cert.HkIntegrand_radial_sin
import Submission.Work.FTS.EllipticEst.Cert.integral_HkExp
import Submission.Work.FTS.EllipticEst.Cert.radIter_Bmom_ae
import Submission.Work.FTS.EllipticEst.aestronglyMeasurable_integral_Itheta_Q0
import Submission.Work.FTS.EllipticEst.FstarDzIter_sq_mul_w_le_open
import Submission.Work.FTS.EllipticEst.OpenQAng
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cert

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-! ## The angular profiles -/

theorem continuous_angZ : Continuous angZ := by
  unfold angZ
  exact (Real.continuous_sin.comp (continuous_const.mul continuous_id)).rpow_const
    (fun θ => Or.inr (by rw [Work.Spaces.eta]; norm_num))

theorem angZ_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ angZ θ := by
  rw [angZ]
  exact Real.rpow_nonneg (FstarHkOpen.sin_two_nonneg hθ) _

theorem angZ_le_one {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : angZ θ ≤ 1 := by
  rw [angZ]
  exact Real.rpow_le_one (FstarHkOpen.sin_two_nonneg hθ) (FstarHkOpen.sin_two_le_one θ)
    (by rw [Work.Spaces.eta]; norm_num)

theorem integrableOn_angZ : MeasureTheory.IntegrableOn angZ Work.Spaces.Iθ :=
  FstarHkOpen.integrableOn_Iθ_of_abs_le
    (continuous_angZ.continuousOn.aestronglyMeasurable
      (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc))
    (fun θ hθ => by rw [abs_of_nonneg (angZ_nonneg hθ)]; exact angZ_le_one hθ)

theorem continuousOn_angA (α : ℝ) (i : ℕ) :
    ContinuousOn (angA α i) (Set.Ioo 0 (π / 2)) := by
  have hslice : ContDiffOn ℝ ⊤ (Work.FTS.EllipticEst.sinProf i)
      (Set.Ioo (-1) (Real.pi / 2 + 1)) := FstarHkOpen.smoothSlice_sinProf i
  have hsp : ContinuousOn (Work.FTS.EllipticEst.sinProf i) (Set.Ioo 0 (π / 2)) :=
    hslice.continuousOn.mono
      (fun θ hθ => ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩)
  have hsin : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      (Set.Ioo 0 (π / 2)) := by
    refine ContinuousOn.rpow_const
      ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn) ?_
    intro θ hθ
    exact Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])))
  change ContinuousOn (fun θ => (Work.FTS.EllipticEst.sinProf i θ) ^ 2
    * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) (Set.Ioo 0 (π / 2))
  exact (hsp.pow 2).mul hsin

theorem angA_nonneg (α : ℝ) (i : ℕ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ angA α i θ := by
  rw [angA]
  exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (FstarHkOpen.sin_two_nonneg hθ) _)

theorem angA_le_angK (α : ℝ) (i : ℕ) (h1 : 1 ≤ Work.Spaces.gam α)
    (h2 : Work.Spaces.gam α ≤ 2) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    angA α i θ ≤ FstarHkOpen.angK i :=
  FstarHkOpen.angK_bound i (Work.Spaces.gam α) h1 h2 hθ

theorem integrableOn_angA (α : ℝ) (i : ℕ) (hα : 0 < α) (hα1 : α ≤ 1) :
    MeasureTheory.IntegrableOn (angA α i) Work.Spaces.Iθ := by
  have hgam1 : 1 ≤ Work.Spaces.gam α := le_of_lt (Work.Spaces.one_lt_gam hα)
  have hgam2 : Work.Spaces.gam α ≤ 2 := by rw [Work.Spaces.gam]; linarith
  refine FstarHkOpen.integrableOn_Iθ_of_abs_le (C := FstarHkOpen.angK i) ?_ ?_
  · rw [show (MeasureTheory.volume : Measure ℝ).restrict Work.Spaces.Iθ
        = (MeasureTheory.volume : Measure ℝ).restrict (Set.Ioo 0 (π / 2)) from
      MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc.symm]
    exact (continuousOn_angA α i).aestronglyMeasurable measurableSet_Ioo
  · intro θ hθ
    rw [abs_of_nonneg (angA_nonneg α i hθ)]
    exact angA_le_angK α i hgam1 hgam2 hθ

/-! ## The crude bound for the slice integrand -/

/-- A crude bound for `HkExp α k R z` on `Iθ`: the angular factors `angZ` resp. `angA`
are replaced by their bounds `1` resp. `angK i`. -/
def sliceConst (k : ℕ) (R : ℝ → ℝ) (z : ℝ) : ℝ :=
  (∑ i ∈ Finset.range (k + 1),
      (Work.FTS.EllipticEst.radIter R i z) ^ 2 * (Work.Spaces.w z) ^ 2)
    + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        if 1 ≤ i ∧ i + j ≤ k then
          (Work.FTS.EllipticEst.radIter R j z) ^ 2 * (Work.Spaces.w z) ^ 2
            * FstarHkOpen.angK i
        else 0

/-- The constant of the domination `∫_θ HkIntegrand (F_*·sin 2θ) ≤ K ∫_θ HkIntegrand F`. -/
def sliceK (k : ℕ) : ℝ :=
  ((k : ℝ) + 1) * (π / 2) ^ 2 * (1 + ((k : ℝ) + 1) * FstarHkOpen.angKsum k) + 1

theorem sliceK_pos (k : ℕ) : 0 < sliceK k := by
  have hK : 0 ≤ FstarHkOpen.angKsum k := FstarHkOpen.angKsum_nonneg k
  have hk : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
  have h1 : (0 : ℝ) ≤ 1 + ((k : ℝ) + 1) * FstarHkOpen.angKsum k :=
    le_trans zero_le_one (le_add_of_nonneg_right (mul_nonneg hk hK))
  have h2 : (0 : ℝ) ≤ (π / 2) ^ 2 := sq_nonneg _
  have h3 : (0 : ℝ) ≤ ((k : ℝ) + 1) * (π / 2) ^ 2
      * (1 + ((k : ℝ) + 1) * FstarHkOpen.angKsum k) := mul_nonneg (mul_nonneg hk h2) h1
  rw [sliceK]
  linarith

theorem sliceK_nonneg (k : ℕ) : 0 ≤ sliceK k := (sliceK_pos k).le

theorem continuousOn_HkExp (α : ℝ) (k : ℕ) (R : ℝ → ℝ) (z : ℝ) :
    ContinuousOn (fun θ => HkExp α k R z θ) (Set.Ioo 0 (π / 2)) := by
  unfold HkExp
  refine ContinuousOn.add ?_ ?_
  · refine continuousOn_finsetSum _ fun i _ => ?_
    exact continuousOn_const.mul continuous_angZ.continuousOn
  · refine continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ => ?_
    by_cases hc : 1 ≤ i ∧ i + j ≤ k
    · simp only [if_pos hc]
      exact continuousOn_const.mul (continuousOn_angA α i)
    · simp only [if_neg hc]
      exact continuousOn_const

theorem HkExp_le_sliceConst (α : ℝ) (k : ℕ) (R : ℝ → ℝ) (z : ℝ) (hα : 0 < α)
    (hα1 : α ≤ 1) :
    ∀ θ ∈ Work.Spaces.Iθ, HkExp α k R z θ ≤ sliceConst k R z := by
  have hgam1 : 1 ≤ Work.Spaces.gam α := le_of_lt (Work.Spaces.one_lt_gam hα)
  have hgam2 : Work.Spaces.gam α ≤ 2 := by rw [Work.Spaces.gam]; linarith
  intro θ hθ
  have hZ1 : angZ θ ≤ 1 := angZ_le_one hθ
  unfold HkExp sliceConst
  refine add_le_add ?_ ?_
  · refine Finset.sum_le_sum fun i hi => ?_
    have h2 : 0 ≤ (Work.FTS.EllipticEst.radIter R i z) ^ 2 * (Work.Spaces.w z) ^ 2 :=
      mul_nonneg (sq_nonneg _) (sq_nonneg _)
    calc (Work.FTS.EllipticEst.radIter R i z) ^ 2 * (Work.Spaces.w z) ^ 2 * angZ θ
        ≤ (Work.FTS.EllipticEst.radIter R i z) ^ 2 * (Work.Spaces.w z) ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left hZ1 h2
      _ = (Work.FTS.EllipticEst.radIter R i z) ^ 2 * (Work.Spaces.w z) ^ 2 := by ring
  · refine Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => ?_
    by_cases hc : 1 ≤ i ∧ i + j ≤ k
    · rw [if_pos hc, if_pos hc]
      have h2 : 0 ≤ (Work.FTS.EllipticEst.radIter R j z) ^ 2 * (Work.Spaces.w z) ^ 2 :=
        mul_nonneg (sq_nonneg _) (sq_nonneg _)
      exact mul_le_mul_of_nonneg_left (angA_le_angK α i hgam1 hgam2 hθ) h2
    · rw [if_neg hc, if_neg hc]

/-! ## Integrability of a slice, from continuity and boundedness -/

theorem integrableOn_slice_of_bound (α : ℝ) (k : ℕ) (R : ℝ → ℝ) (z : ℝ) (hz : 0 < z)
    (C : ℝ)
    (hcont : ContinuousOn (fun θ => HkExp α k R z θ) (Set.Ioo 0 (π / 2)))
    (hbnd : ∀ θ ∈ Set.Ioo 0 (π / 2), HkExp α k R z θ ≤ C) :
    MeasureTheory.IntegrableOn (fun θ => Work.Spaces.HkIntegrand α k
        (fun z θ => R z * Real.sin (2 * θ)) z θ) Work.Spaces.Iθ := by
  have hcongr : ∀ θ ∈ Set.Ioo 0 (π / 2),
      Work.Spaces.HkIntegrand α k (fun z θ => R z * Real.sin (2 * θ)) z θ
        = HkExp α k R z θ :=
    fun θ hθ => HkIntegrand_radial_sin α k R z θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have haesm : AEStronglyMeasurable (fun θ => Work.Spaces.HkIntegrand α k
      (fun z θ => R z * Real.sin (2 * θ)) z θ)
      ((MeasureTheory.volume : Measure ℝ).restrict (Set.Ioo 0 (π / 2))) :=
    (hcont.aestronglyMeasurable measurableSet_Ioo).congr
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo fun θ hθ => (hcongr θ hθ).symm)
  have hconst : MeasureTheory.IntegrableOn (fun _ : ℝ => C) (Set.Ioo 0 (π / 2)) :=
    MeasureTheory.integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
  have hle : ∀ᵐ θ ∂((MeasureTheory.volume : Measure ℝ).restrict (Set.Ioo 0 (π / 2))),
      ‖Work.Spaces.HkIntegrand α k (fun z θ => R z * Real.sin (2 * θ)) z θ‖ ≤ C :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo fun θ hθ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Work.Spaces.HkIntegrand_nonneg α k _ z θ),
        hcongr θ hθ]
      exact hbnd θ hθ
  refine MeasureTheory.IntegrableOn.congr_set_ae (t := Set.Ioo 0 (π / 2))
    (MeasureTheory.Integrable.mono' hconst haesm hle) ?_
  exact MeasureTheory.Ioo_ae_eq_Icc.symm

/-! ## The explicit measurable majorant of the slice integral -/

/-- The a.e. value of the slice integral `z ↦ ∫_θ HkIntegrand α k (F_*·sin 2θ) z θ`:
the angular integrals are evaluated and the radial factors are the moments
`Bmom F i z = F_*(D_z^i F)(z)`. -/
def Psi (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  (∫ θ in Work.Spaces.Iθ, angZ θ)
      * (∑ i ∈ Finset.range (k + 1),
          (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.Bmom F i z) ^ 2)
    + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k then
            (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.Bmom F j z) ^ 2 else 0)
          * (∫ θ in Work.Spaces.Iθ, angA α i θ)

theorem aestronglyMeasurable_Bmom (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ)
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (i : ℕ) :
    AEStronglyMeasurable (fun z => Work.FTS.EllipticEst.Bmom F i z)
      ((MeasureTheory.volume : Measure ℝ).restrict Work.Spaces.Iz) := by
  have hsin : ContinuousOn Work.Elliptic.sinCos2 Work.Spaces.Iθ := by
    unfold Work.Elliptic.sinCos2
    fun_prop
  have h := aestronglyMeasurable_integral_Itheta_Q0 (Work.Spaces.DzIter i F)
    (hF.DzIter i).continuousOn Work.Elliptic.sinCos2 hsin
  rw [show ((MeasureTheory.volume : Measure ℝ).restrict Work.Spaces.Iz)
      = ((MeasureTheory.volume : Measure ℝ).restrict (Set.Ioi 0)) from by
    rw [Work.Spaces.Iz]
    exact MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0)).symm]
  simpa only [Work.FTS.EllipticEst.Bmom, Work.FTS.EllipticEst.PsiInt] using h

theorem aestronglyMeasurable_w_sq :
    AEStronglyMeasurable (fun z : ℝ => (Work.Spaces.w z) ^ 2)
      ((MeasureTheory.volume : Measure ℝ).restrict Work.Spaces.Iz) := by
  have hw : ContinuousOn (fun z : ℝ => Work.Spaces.w z) (Set.Ioi 0) := by
    rw [show Work.Spaces.w = fun z : ℝ => (1 + z) ^ 2 / z ^ 2 from rfl]
    exact ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
      (continuousOn_id.pow 2) (fun z hz => pow_ne_zero 2 (ne_of_gt hz))
  have h : ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi 0) := hw.pow 2
  rw [show ((MeasureTheory.volume : Measure ℝ).restrict Work.Spaces.Iz)
      = ((MeasureTheory.volume : Measure ℝ).restrict (Set.Ioi 0)) from by
    rw [Work.Spaces.Iz]
    exact MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0)).symm]
  exact h.aestronglyMeasurable measurableSet_Ioi

theorem aestronglyMeasurable_Psi (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ)
    (hF : Work.FTS.EllipticEst.SmoothOpen F) :
    AEStronglyMeasurable (Psi α k F)
      ((MeasureTheory.volume : Measure ℝ).restrict Work.Spaces.Iz) := by
  have hB : ∀ i : ℕ, AEStronglyMeasurable (fun z => Work.FTS.EllipticEst.Bmom F i z)
      ((MeasureTheory.volume : Measure ℝ).restrict Work.Spaces.Iz) :=
    fun i => aestronglyMeasurable_Bmom α k F hF i
  have hw := aestronglyMeasurable_w_sq
  have hsum1 : AEStronglyMeasurable (fun z : ℝ => ∑ i ∈ Finset.range (k + 1),
      (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.Bmom F i z) ^ 2)
      ((MeasureTheory.volume : Measure ℝ).restrict Work.Spaces.Iz) := by
    rw [show (fun z : ℝ => ∑ i ∈ Finset.range (k + 1),
          (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.Bmom F i z) ^ 2)
        = (∑ i ∈ Finset.range (k + 1),
            fun z : ℝ => (Work.Spaces.w z) ^ 2
              * (Work.FTS.EllipticEst.Bmom F i z) ^ 2) from by
      funext z
      rw [Finset.sum_apply]]
    exact Finset.aestronglyMeasurable_sum (Finset.range (k + 1))
      (fun i hi => hw.mul ((hB i).pow 2))
  have hsum2 : AEStronglyMeasurable (fun z : ℝ => ∑ i ∈ Finset.range (k + 1),
      ∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k then
            (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.Bmom F j z) ^ 2 else 0)
          * (∫ θ in Work.Spaces.Iθ, angA α i θ))
      ((MeasureTheory.volume : Measure ℝ).restrict Work.Spaces.Iz) := by
    rw [show (fun z : ℝ => ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k then
              (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.Bmom F j z) ^ 2 else 0)
            * (∫ θ in Work.Spaces.Iθ, angA α i θ))
        = (∑ i ∈ Finset.range (k + 1), fun z : ℝ => ∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k then
              (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.Bmom F j z) ^ 2 else 0)
            * (∫ θ in Work.Spaces.Iθ, angA α i θ)) from by
      funext z
      rw [Finset.sum_apply]]
    refine Finset.aestronglyMeasurable_sum (Finset.range (k + 1)) (fun i hi => ?_)
    rw [show (fun z : ℝ => ∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k then
              (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.Bmom F j z) ^ 2 else 0)
            * (∫ θ in Work.Spaces.Iθ, angA α i θ))
        = (∑ j ∈ Finset.range (k + 1), fun z : ℝ =>
          (if 1 ≤ i ∧ i + j ≤ k then
              (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.Bmom F j z) ^ 2 else 0)
            * (∫ θ in Work.Spaces.Iθ, angA α i θ)) from by
      funext z
      rw [Finset.sum_apply]]
    refine Finset.aestronglyMeasurable_sum (Finset.range (k + 1)) (fun j hj => ?_)
    by_cases hc : 1 ≤ i ∧ i + j ≤ k
    · simp only [if_pos hc]
      exact (hw.mul ((hB j).pow 2)).mul aestronglyMeasurable_const
    · refine (aestronglyMeasurable_const :
        AEStronglyMeasurable (fun _ : ℝ => (0 : ℝ)) _).congr ?_
      filter_upwards with z
      simp [if_neg hc]
  have hPsi : Psi α k F = fun z : ℝ =>
      (∫ θ in Work.Spaces.Iθ, angZ θ) * (∑ i ∈ Finset.range (k + 1),
        (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.Bmom F i z) ^ 2)
      + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k then
              (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.Bmom F j z) ^ 2 else 0)
            * (∫ θ in Work.Spaces.Iθ, angA α i θ) := rfl
  rw [hPsi]
  exact (aestronglyMeasurable_const.mul hsum1).add hsum2

/-! ## The a.e. evaluation of the slice integral -/

theorem ae_sliceIntegral_eq_Psi (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ) (hα : 0 < α)
    (hα1 : α ≤ 1) (hF : Work.FTS.EllipticEst.SmoothOpen F)
    (hmem : Work.Spaces.HkMem α k F) :
    (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k
        (fun z θ => Work.FTS.EllipticEst.Bmom F 0 z * Real.sin (2 * θ)) z θ)
      =ᵐ[(MeasureTheory.volume : Measure ℝ).restrict Work.Spaces.Iz] Psi α k F := by
  have hrad : ∀ᵐ z ∂((MeasureTheory.volume : Measure ℝ).restrict Work.Spaces.Iz),
      ∀ j : ℕ, j ≤ k →
        Work.FTS.EllipticEst.radIter (fun z => Work.FTS.EllipticEst.Bmom F 0 z) j z
          = Work.FTS.EllipticEst.Bmom F j z := by
    rw [show ((MeasureTheory.volume : Measure ℝ).restrict Work.Spaces.Iz)
        = ((MeasureTheory.volume : Measure ℝ).restrict (Set.Ioi 0)) from by
      rw [Work.Spaces.Iz]
      exact MeasureTheory.Measure.restrict_congr_set
        (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0)).symm]
    exact radIter_Bmom_ae α k F hF hmem
  have hInt : ∀ z : ℝ, (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k
        (fun z θ => Work.FTS.EllipticEst.Bmom F 0 z * Real.sin (2 * θ)) z θ)
      = (Work.Spaces.w z) ^ 2 * ((∫ θ in Work.Spaces.Iθ, angZ θ)
              * (∑ i ∈ Finset.range (k + 1),
                  (Work.FTS.EllipticEst.radIter
                    (fun z => Work.FTS.EllipticEst.Bmom F 0 z) i z) ^ 2)
            + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
                (if 1 ≤ i ∧ i + j ≤ k then
                    (Work.FTS.EllipticEst.radIter
                      (fun z => Work.FTS.EllipticEst.Bmom F 0 z) j z) ^ 2 else 0)
                  * (∫ θ in Work.Spaces.Iθ, angA α i θ)) := by
    intro z
    rw [MeasureTheory.setIntegral_congr_ae
      (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)
      (Eventually.of_forall fun θ hθ => HkIntegrand_radial_sin α k
        (fun z => Work.FTS.EllipticEst.Bmom F 0 z) z θ hθ)]
    exact integral_HkExp α k (fun z => Work.FTS.EllipticEst.Bmom F 0 z) z
      integrableOn_angZ (fun i => integrableOn_angA α i hα hα1)
  filter_upwards [hrad] with z hzrad
  rw [hInt z]
  have h1 : ∀ i ∈ Finset.range (k + 1),
      Work.FTS.EllipticEst.radIter (fun z => Work.FTS.EllipticEst.Bmom F 0 z) i z
        = Work.FTS.EllipticEst.Bmom F i z :=
    fun i hi => hzrad i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
  have hS1 : (∑ i ∈ Finset.range (k + 1),
        (Work.FTS.EllipticEst.radIter (fun z => Work.FTS.EllipticEst.Bmom F 0 z) i z) ^ 2)
      = ∑ i ∈ Finset.range (k + 1), (Work.FTS.EllipticEst.Bmom F i z) ^ 2 :=
    Finset.sum_congr rfl fun i hi => by rw [h1 i hi]
  have hS2 : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k then
            (Work.FTS.EllipticEst.radIter (fun z => Work.FTS.EllipticEst.Bmom F 0 z) j z) ^ 2
          else 0) * (∫ θ in Work.Spaces.Iθ, angA α i θ))
      = ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k then (Work.FTS.EllipticEst.Bmom F j z) ^ 2 else 0)
          * (∫ θ in Work.Spaces.Iθ, angA α i θ) := by
    refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
    by_cases hc : 1 ≤ i ∧ i + j ≤ k
    · rw [if_pos hc, if_pos hc, h1 j hj]
    · rw [if_neg hc, if_neg hc]
  rw [hS1, hS2, Psi]
  rw [mul_add]
  congr 1
  · simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i hi => by ring
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    by_cases hc : 1 ≤ i ∧ i + j ≤ k
    · simp only [if_pos hc]; ring
    · simp only [if_neg hc]; ring

/-! ## The pointwise bound on the majorant -/

theorem Phi_bound (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hmem : Work.Spaces.HkMem α k F)
    (z : ℝ) (hz : z ∈ Work.Spaces.Iz) :
    Psi α k F z ≤ sliceK k * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ) := by
  have hgam1 : 1 ≤ Work.Spaces.gam α := le_of_lt (Work.Spaces.one_lt_gam hα)
  have hgam2 : Work.Spaces.gam α ≤ 2 := by rw [Work.Spaces.gam]; linarith
  -- Cauchy--Schwarz for the moments
  have hCS : ∀ i : ℕ, i ≤ k →
      (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.Bmom F i z) ^ 2
        ≤ (π / 2) * FstarHkOpen.Uj F z i := by
    intro i hi
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with h0 | hpos
    · rw [← h0]
      have hw : Work.Spaces.w (0 : ℝ) = 0 := by rw [Work.Spaces.w]; norm_num
      have hU : FstarHkOpen.Uj F 0 i = 0 := by
        rw [FstarHkOpen.Uj, hw]
        simp
      rw [hU, hw]
      simp
    · have h := FstarDzIter_sq_mul_w_le_open α k F hF hmem i hi hpos
      rw [Work.FTS.EllipticEst.Bmom_eq_Fstar_DzIter]
      simpa only [FstarHkOpen.Uj, mul_comm] using h
  -- the sum of the angular masses is dominated by the slice integral of the source
  have hSG : (∑ i ∈ Finset.range (k + 1), FstarHkOpen.Uj F z i)
      ≤ (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ) := by
    have hint : ∀ i ∈ Finset.range (k + 1), MeasureTheory.IntegrableOn (fun θ : ℝ =>
        (Work.Spaces.DzIter i F z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        Work.Spaces.Iθ :=
      fun i hi => Work.FTS.EllipticEst.integrableOn_zSummand α k hF hmem i
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hz
    have hsum : (∑ i ∈ Finset.range (k + 1), FstarHkOpen.Uj F z i)
        = ∫ θ in Work.Spaces.Iθ, ∑ i ∈ Finset.range (k + 1),
            (Work.Spaces.DzIter i F z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
      simp only [FstarHkOpen.Uj]
      rw [← MeasureTheory.integral_finsetSum]
      exact hint
    rw [hsum]
    refine MeasureTheory.integral_mono_of_nonneg
      (Eventually.of_forall fun θ => Finset.sum_nonneg fun i _ => sq_nonneg _)
      (hmem.1 z hz) (Eventually.of_forall fun θ => ?_)
    rw [Work.Spaces.HkIntegrand]
    exact le_add_of_nonneg_right (Work.Spaces.hkMixedSum_nonneg α k F z θ)
  -- the angular integrals
  have hZnn : 0 ≤ (∫ θ in Work.Spaces.Iθ, angZ θ) :=
    MeasureTheory.integral_nonneg_of_ae (MeasureTheory.ae_restrict_of_forall_mem
      measurableSet_Icc fun θ hθ => angZ_nonneg hθ)
  have hZle : (∫ θ in Work.Spaces.Iθ, angZ θ) ≤ π / 2 := by
    have hone : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) Work.Spaces.Iθ :=
      MeasureTheory.integrableOn_const
        (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
    have h := MeasureTheory.integral_mono_of_nonneg
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ => angZ_nonneg hθ)
      hone
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ => angZ_le_one hθ)
    calc (∫ θ in Work.Spaces.Iθ, angZ θ) ≤ (∫ θ in Work.Spaces.Iθ, (1 : ℝ)) := h
      _ = π / 2 := FstarHkOpen.integral_Iθ_one
  have hAnn : ∀ i : ℕ, 0 ≤ (∫ θ in Work.Spaces.Iθ, angA α i θ) := fun i =>
    MeasureTheory.integral_nonneg_of_ae (MeasureTheory.ae_restrict_of_forall_mem
      measurableSet_Icc fun θ hθ => angA_nonneg α i hθ)
  have hAle : ∀ i : ℕ, (∫ θ in Work.Spaces.Iθ, angA α i θ)
      ≤ FstarHkOpen.angK i * (π / 2) := by
    intro i
    have hone : MeasureTheory.IntegrableOn (fun _ : ℝ => FstarHkOpen.angK i)
        Work.Spaces.Iθ :=
      MeasureTheory.integrableOn_const
        (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
    have h := MeasureTheory.integral_mono_of_nonneg
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
        fun θ hθ => angA_nonneg α i hθ)
      hone
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
        fun θ hθ => angA_le_angK α i hgam1 hgam2 hθ)
    have hvol : MeasureTheory.volume.real (Set.Icc 0 (π / 2)) = π / 2 := by
      rw [MeasureTheory.measureReal_def, Real.volume_Icc,
        ENNReal.toReal_ofReal (by linarith [Real.pi_pos]), sub_zero]
    calc (∫ θ in Work.Spaces.Iθ, angA α i θ)
        ≤ ∫ θ in Work.Spaces.Iθ, FstarHkOpen.angK i := h
      _ = MeasureTheory.volume.real (Set.Icc 0 (π / 2)) * FstarHkOpen.angK i := by
          rw [MeasureTheory.setIntegral_const, smul_eq_mul]
          rfl
      _ = FstarHkOpen.angK i * (π / 2) := by rw [hvol]; ring
  have hUjnn : ∀ i : ℕ, 0 ≤ FstarHkOpen.Uj F z i := fun i => FstarHkOpen.Uj_nonneg F z i
  have hSGu : 0 ≤ ∑ i ∈ Finset.range (k + 1), FstarHkOpen.Uj F z i :=
    Finset.sum_nonneg fun i _ => hUjnn i
  have hSKnn : 0 ≤ FstarHkOpen.angKsum k := FstarHkOpen.angKsum_nonneg k
  have hmFnn : 0 ≤ (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ) :=
    MeasureTheory.integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k F z θ
  -- every moment square is bounded by `(π/2) * (Σ Uj)`
  have hX : ∀ i ≤ k, (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.Bmom F i z) ^ 2
      ≤ (π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j) := by
    intro i hi
    refine le_trans (hCS i hi) (mul_le_mul_of_nonneg_left ?_ (by positivity))
    exact Finset.single_le_sum (fun j _ => hUjnn j) (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
  -- every angular integral is bounded by `(Σ angK) * (π/2)`
  have hY : ∀ i ≤ k, (∫ θ in Work.Spaces.Iθ, angA α i θ)
      ≤ FstarHkOpen.angKsum k * (π / 2) := by
    intro i hi
    refine le_trans (hAle i) (mul_le_mul_of_nonneg_right ?_ (by positivity))
    rw [FstarHkOpen.angKsum]
    exact Finset.single_le_sum (fun j _ => (FstarHkOpen.angK_pos j).le)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
  -- the pure sum
  have hS1 : (∫ θ in Work.Spaces.Iθ, angZ θ)
        * (∑ i ∈ Finset.range (k + 1),
            (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.Bmom F i z) ^ 2)
      ≤ ((k : ℝ) + 1) * (π / 2) ^ 2
          * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j) := by
    have hb : (∑ i ∈ Finset.range (k + 1),
          (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.Bmom F i z) ^ 2)
        ≤ ∑ i ∈ Finset.range (k + 1), (π / 2)
            * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j) :=
      Finset.sum_le_sum fun i hi =>
        hX i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
    have hb' : (∑ i ∈ Finset.range (k + 1), (π / 2)
          * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j))
        = ((k : ℝ) + 1) * ((π / 2)
            * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      push_cast
      ring
    have hsum_le : (∑ i ∈ Finset.range (k + 1),
          (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.Bmom F i z) ^ 2)
        ≤ ((k : ℝ) + 1) * ((π / 2)
            * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)) :=
      le_trans hb (le_of_eq hb')
    calc (∫ θ in Work.Spaces.Iθ, angZ θ)
          * (∑ i ∈ Finset.range (k + 1),
              (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.Bmom F i z) ^ 2)
        ≤ (π / 2) * (((k : ℝ) + 1) * ((π / 2)
            * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j))) :=
          mul_le_mul hZle hsum_le
            (Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
            (by positivity)
      _ = ((k : ℝ) + 1) * (π / 2) ^ 2
            * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j) := by ring
  -- the mixed sum
  have hCC : 0 ≤ ((π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j))
      * (FstarHkOpen.angKsum k * (π / 2)) :=
    mul_nonneg (mul_nonneg (by positivity) hSGu) (mul_nonneg hSKnn (by positivity))
  have hterm : ∀ i ∈ Finset.range (k + 1), ∀ j ∈ Finset.range (k + 1),
      (if 1 ≤ i ∧ i + j ≤ k then
          (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.Bmom F j z) ^ 2 else 0)
        * (∫ θ in Work.Spaces.Iθ, angA α i θ)
      ≤ ((π / 2) * (∑ j' ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j'))
          * (FstarHkOpen.angKsum k * (π / 2)) := by
    intro i hi j hj
    have hjle : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hile : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    by_cases hc : 1 ≤ i ∧ i + j ≤ k
    · rw [if_pos hc]
      exact mul_le_mul (hX j hjle) (hY i hile) (hAnn i)
        (mul_nonneg (by positivity) hSGu)
    · rw [if_neg hc, zero_mul]
      exact hCC
  have hS2 : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k then
            (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.Bmom F j z) ^ 2 else 0)
          * (∫ θ in Work.Spaces.Iθ, angA α i θ))
      ≤ ((k : ℝ) + 1) * (((k : ℝ) + 1)
          * (((π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j))
              * (FstarHkOpen.angKsum k * (π / 2)))) := by
    have h1 : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k then
            (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.Bmom F j z) ^ 2 else 0)
          * (∫ θ in Work.Spaces.Iθ, angA α i θ))
        ≤ ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            ((π / 2) * (∑ j' ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j'))
              * (FstarHkOpen.angKsum k * (π / 2)) :=
      Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hterm i hi j hj
    have h2 : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            ((π / 2) * (∑ j' ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j'))
              * (FstarHkOpen.angKsum k * (π / 2)))
        = ((k : ℝ) + 1) * (((k : ℝ) + 1)
            * (((π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j))
                * (FstarHkOpen.angKsum k * (π / 2)))) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      push_cast
      ring
    linarith [h1, h2.le]
  have hid : ((k : ℝ) + 1) * (((k : ℝ) + 1)
        * (((π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j))
            * (FstarHkOpen.angKsum k * (π / 2))))
      = ((k : ℝ) + 1) * (π / 2) ^ 2
          * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
          * (((k : ℝ) + 1) * FstarHkOpen.angKsum k) := by ring
  have htot : ((k : ℝ) + 1) * (π / 2) ^ 2
        * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
      + ((k : ℝ) + 1) * (π / 2) ^ 2
        * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
        * (((k : ℝ) + 1) * FstarHkOpen.angKsum k)
      ≤ sliceK k * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ) := by
    have hfac : 0 ≤ ((k : ℝ) + 1) * (π / 2) ^ 2
        * (1 + ((k : ℝ) + 1) * FstarHkOpen.angKsum k) :=
      mul_nonneg (mul_nonneg (by positivity) (sq_nonneg _))
        (by have := mul_nonneg (by positivity : (0 : ℝ) ≤ (k : ℝ) + 1) hSKnn; linarith)
    have heq : ((k : ℝ) + 1) * (π / 2) ^ 2
          * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
        + ((k : ℝ) + 1) * (π / 2) ^ 2
          * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
          * (((k : ℝ) + 1) * FstarHkOpen.angKsum k)
        = ((k : ℝ) + 1) * (π / 2) ^ 2
            * (1 + ((k : ℝ) + 1) * FstarHkOpen.angKsum k)
          * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j) := by ring
    rw [heq]
    refine le_trans (mul_le_mul_of_nonneg_left hSG hfac) ?_
    refine mul_le_mul_of_nonneg_right ?_ hmFnn
    rw [sliceK]
    linarith
  unfold Psi
  linarith [hS1, hS2, hid, htot]

/-! ## The a.e. domination of the slice integral -/

theorem slice_bound (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hmem : Work.Spaces.HkMem α k F) :
    ∀ᵐ z ∂((MeasureTheory.volume : Measure ℝ).restrict Work.Spaces.Iz),
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k
          (fun z θ => Work.FTS.EllipticEst.Bmom F 0 z * Real.sin (2 * θ)) z θ)
        ≤ sliceK k * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ) := by
  filter_upwards [ae_sliceIntegral_eq_Psi α k F hα hα1 hF hmem,
    MeasureTheory.ae_restrict_mem (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici)]
    with z hz hzI
  rw [hz]
  exact Phi_bound α k F hα hα1 hF hmem z hzI

/-! ## Membership in `ℋ^k` -/

theorem HkMem_bmom_sin_of_smoothOpen (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ) (hα : 0 < α)
    (hα1 : α ≤ 1) (hF : Work.FTS.EllipticEst.SmoothOpen F) (hmem : Work.Spaces.HkMem α k F) :
    Work.Spaces.HkMem α k (fun z θ => Work.FTS.EllipticEst.Bmom F 0 z * Real.sin (2 * θ)) := by
  have hslice : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn (fun θ =>
      Work.Spaces.HkIntegrand α k
        (fun z θ => Work.FTS.EllipticEst.Bmom F 0 z * Real.sin (2 * θ)) z θ)
      Work.Spaces.Iθ := by
    intro z hz
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with h0 | hpos
    · subst h0
      have hz0 : ∀ θ : ℝ, Work.Spaces.HkIntegrand α k
          (fun z θ => Work.FTS.EllipticEst.Bmom F 0 z * Real.sin (2 * θ)) 0 θ = 0 :=
        fun θ => by simp [Work.Spaces.HkIntegrand, Work.Spaces.Wt, Work.Spaces.w]
      refine MeasureTheory.IntegrableOn.congr_fun MeasureTheory.integrableOn_zero
        (fun θ _ => (hz0 θ).symm) (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)
    · exact integrableOn_slice_of_bound α k (fun z => Work.FTS.EllipticEst.Bmom F 0 z) z
        hpos (sliceConst k (fun z => Work.FTS.EllipticEst.Bmom F 0 z) z)
        (continuousOn_HkExp α k _ z)
        (fun θ hθ => HkExp_le_sliceConst α k _ z hα hα1 θ
          ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
  have haesm : AEStronglyMeasurable (fun z => ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k
        (fun z θ => Work.FTS.EllipticEst.Bmom F 0 z * Real.sin (2 * θ)) z θ)
      ((MeasureTheory.volume : Measure ℝ).restrict Work.Spaces.Iz) :=
    (aestronglyMeasurable_Psi α k F hF).congr
      (ae_sliceIntegral_eq_Psi α k F hα hα1 hF hmem).symm
  refine ⟨hslice, ?_⟩
  refine MeasureTheory.Integrable.mono' (hmem.2.const_mul (sliceK k)) haesm ?_
  filter_upwards [slice_bound α k F hα hα1 hF hmem] with z hz
  rw [Real.norm_of_nonneg (MeasureTheory.integral_nonneg fun θ =>
    Work.Spaces.HkIntegrand_nonneg α k _ z θ)]
  exact hz

theorem HkMem_Fstar_sin (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (hHyp : Work.FTS.EllipticEst.EllHyp α k F Ψ) :
    Work.Spaces.HkMem α k (fun z θ => Work.Elliptic.Fstar F z * Real.sin (2 * θ)) := by
  have hα1 : α ≤ 1 := by linarith
  have hF : Work.FTS.EllipticEst.SmoothOpen F := by
    refine Work.FTS.EllipticEst.smoothOpen_of_forall fun n => ?_
    refine (SmoothOpen_bslOp_int α Ψ hHyp.smooth).forall n |>.congr ?_
    intro p hp
    obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact (hHyp.sol.1 p.1 hz p.2 hθ0 hθ1).symm
  have hmain := HkMem_bmom_sin_of_smoothOpen α k F hα hα1 hF hHyp.memF
  have hfun : (fun z θ : ℝ => Work.Elliptic.Fstar F z * Real.sin (2 * θ))
      = fun z θ : ℝ => Work.FTS.EllipticEst.Bmom F 0 z * Real.sin (2 * θ) := by
    funext z θ
    rw [Work.FTS.EllipticEst.Bmom_zero]
  rw [hfun]
  exact hmain

end Work.FTS.EllipticEst.Cert
