import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Mathlib.LinearAlgebra.Trace
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.SliceDecompDefs
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.Galerkin.Inhabit.regPkg_zero
import Submission.Work.FTS.H2.STBasic
import Submission.Work.FTS.H2.Transport1Aux
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.OpenPkg.ProdOpen.Tools1d
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.SolutionDelivery.DatumOdd
import Submission.Work.SolutionDelivery.HolderInputs
import Submission.Work.SolutionDelivery.Slices
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.bt_prod_integrable
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.sup_mixed_le_H4
import Submission.Work.Spaces.uncurry_partial_c1
import Submission.Work.Stability.CutFactorFderivZero
import Submission.Work.Stability.Cutoff
import Submission.Work.Stability.holderWith_of_dist_le
-- ===== merged: Submission.Work.ConstructionInstance.A0_Pall_diff =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

/-- The axial coordinate is `1`-Lipschitz: `|x₂ - y₂| ≤ ‖x - y‖`. -/
private lemma abs_axial_sub_le_norm (x y : R3) : |x 2 - y 2| ≤ ‖x - y‖ := by
  have h := PiLp.norm_apply_le (x - y) (2 : Fin 3)
  simpa using h

/-- The absolute value of the axial coordinate is `1`-Lipschitz. -/
private lemma abs_abs_axial_sub_le_norm (x y : R3) : |(|x 2| - |y 2|)| ≤ ‖x - y‖ :=
  le_trans (abs_abs_sub_abs_le_abs_sub _ _) (abs_axial_sub_le_norm x y)

/-- The squared radial coordinate is `2M`-Lipschitz with `M = max (ρ x) (ρ y)`. -/
private lemma abs_radial_sq_sub_le (x y : R3) :
    |Work.Cyl.radial x ^ 2 - Work.Cyl.radial y ^ 2|
      ≤ 2 * max (Work.Cyl.rho x) (Work.Cyl.rho y) * ‖x - y‖ := by
  have hsub : |Work.Cyl.radial x - Work.Cyl.radial y| ≤ ‖x - y‖ := radial_dist_le x y
  have hsum : Work.Cyl.radial x + Work.Cyl.radial y
      ≤ 2 * max (Work.Cyl.rho x) (Work.Cyl.rho y) := by
    have h1 : Work.Cyl.radial x + Work.Cyl.radial y ≤ Work.Cyl.rho x + Work.Cyl.rho y :=
      add_le_add (Work.Cyl.radial_le_rho x) (Work.Cyl.radial_le_rho y)
    have h2 : Work.Cyl.rho x ≤ max (Work.Cyl.rho x) (Work.Cyl.rho y) := le_max_left _ _
    have h3 : Work.Cyl.rho y ≤ max (Work.Cyl.rho x) (Work.Cyl.rho y) := le_max_right _ _
    linarith
  have hsum0 : 0 ≤ Work.Cyl.radial x + Work.Cyl.radial y := by
    have := Work.Cyl.radial_nonneg x; have := Work.Cyl.radial_nonneg y; linarith
  calc |Work.Cyl.radial x ^ 2 - Work.Cyl.radial y ^ 2|
      = |(Work.Cyl.radial x - Work.Cyl.radial y) * (Work.Cyl.radial x + Work.Cyl.radial y)| := by
        congr 1; ring
    _ = |Work.Cyl.radial x - Work.Cyl.radial y| * (Work.Cyl.radial x + Work.Cyl.radial y) := by
        rw [abs_mul, abs_of_nonneg hsum0]
    _ ≤ ‖x - y‖ * (2 * max (Work.Cyl.rho x) (Work.Cyl.rho y)) :=
        mul_le_mul hsub hsum hsum0 (norm_nonneg _)
    _ = 2 * max (Work.Cyl.rho x) (Work.Cyl.rho y) * ‖x - y‖ := by ring

/-- **`Pall` is locally `3ρ²`-Lipschitz**: with `M = max (ρ x) (ρ y)`,
`|Pall x - Pall y| ≤ 3 M² ‖x - y‖`. -/
lemma A0_Pall_diff (x y : Work.ConstructionInstance.R3) :
    |Work.ConstructionInstance.Pall x - Work.ConstructionInstance.Pall y|
      ≤ 3 * (max (Work.Cyl.rho x) (Work.Cyl.rho y)) ^ 2 * ‖x - y‖ := by
  set M := max (Work.Cyl.rho x) (Work.Cyl.rho y) with hMdef
  have hMx : Work.Cyl.rho x ≤ M := le_max_left _ _
  have hMy : Work.Cyl.rho y ≤ M := le_max_right _ _
  have hM0 : 0 ≤ M := le_trans (Work.Cyl.rho_nonneg x) hMx
  have hax : |x 2| ≤ M := le_trans (Work.Cyl.abs_axial_le_rho x) hMx
  have hry : Work.Cyl.radial y ≤ M := le_trans (Work.Cyl.radial_le_rho y) hMy
  have hA : |Work.Cyl.radial x ^ 2 - Work.Cyl.radial y ^ 2| ≤ 2 * M * ‖x - y‖ := by
    have h := abs_radial_sq_sub_le x y
    rw [← hMdef] at h
    linarith [h]
  have hB : |(|x 2| - |y 2|)| ≤ ‖x - y‖ := abs_abs_axial_sub_le_norm x y
  have hsplit : Pall x - Pall y
      = |x 2| * (Work.Cyl.radial x ^ 2 - Work.Cyl.radial y ^ 2)
        + Work.Cyl.radial y ^ 2 * (|x 2| - |y 2|) := by
    simp only [Pall]; ring
  calc |Pall x - Pall y|
      = |(|x 2| * (Work.Cyl.radial x ^ 2 - Work.Cyl.radial y ^ 2)
          + Work.Cyl.radial y ^ 2 * (|x 2| - |y 2|))| := by rw [hsplit]
    _ ≤ |(|x 2| * (Work.Cyl.radial x ^ 2 - Work.Cyl.radial y ^ 2))|
          + |(Work.Cyl.radial y ^ 2 * (|x 2| - |y 2|))| := abs_add_le _ _
    _ = |x 2| * |Work.Cyl.radial x ^ 2 - Work.Cyl.radial y ^ 2|
          + Work.Cyl.radial y ^ 2 * |(|x 2| - |y 2|)| := by
        rw [abs_mul, abs_mul, abs_abs, abs_of_nonneg (sq_nonneg (Work.Cyl.radial y))]
    _ ≤ M * (2 * M * ‖x - y‖) + M ^ 2 * ‖x - y‖ := by
        refine add_le_add ?_ ?_
        · exact mul_le_mul hax hA (abs_nonneg _) hM0
        · exact mul_le_mul (by nlinarith [hry, Work.Cyl.radial_nonneg y]) hB (abs_nonneg _)
            (by positivity)
    _ = 3 * M ^ 2 * ‖x - y‖ := by ring

end Work.ConstructionInstance
end
-- ===== merged: Submission.Work.ConstructionInstance.Repair =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

namespace Work.ConstructionInstance

/-- **The cut-off preserves `α`-Hölder regularity** (for a *bounded* field, `α ≤ 1`): the
cut-off factor `x ↦ χ(ρ(x)/L)` is bounded and Lipschitz, and a bounded Lipschitz scalar times a
bounded `α`-Hölder field is `α`-Hölder. -/
theorem cutDatum_holder_of_holder {L : ℝ} (hL : 0 < L) {α : NNReal} (hα1 : α ≤ 1)
    {ω : R3 → R3} (hbdd : IsBoundedFun ω) (hω : Holder α ω) :
    Holder α (Work.SolutionDelivery.cutDatum L ω) := by
  have hcut : Work.SolutionDelivery.cutDatum L ω = Work.Stability.cutFactor L • ω :=
    Work.Stability.omegaCut_eq_smul L ω
  rw [hcut]
  obtain ⟨K, hK⟩ := Work.Stability.cutFactor_lipschitz hL
  exact Work.Stability.holder_smul_of_bounded_lipschitz hα1
    (Work.Stability.cutFactor_bounded L) hK hbdd hω


/-- **The Lichtenstein–Gunther datum classes of the cut-off datum, from `Holder α` only.**

This is `Work.SolutionDelivery.DatumCut.datumData_of_cut` with the hypothesis
`IsContDiffHolder ℝ α ω` weakened to `Holder α ω` (plus the boundedness used by the cut-off
lemma); it is the *only* place in the assembly chain where the `C^{1,α}` clause of `ωS` is
consumed. -/
theorem datumData_of_cut_of_holder {α : NNReal} (hlwp : Work.LWP.LWPInputs α) {L M : ℝ}
    (hL : 0 < L) (hM : 0 ≤ M) (hα : 0 < (α : ℝ)) (hα1 : (α : ℝ) ≤ 1)
    {ω : R3 → R3} (hmeas : MeasureTheory.AEStronglyMeasurable ω MeasureTheory.volume)
    (hbdd : ∀ x : R3, ‖ω x‖ ≤ M) (hholder : Holder α ω)
    (hdiv : ∀ x : R3, FiniteTimeSingularity.div (Work.SolutionDelivery.cutDatum L ω) x = 0)
    (hodd : FiniteTimeSingularity.IsOdd
      (Work.LWP.biotSavart (Work.SolutionDelivery.cutDatum L ω))) :
    Work.LWP.EulerData α (Work.LWP.biotSavart (Work.SolutionDelivery.cutDatum L ω)) ∧
      Work.LWP.EulerDataBS α (Work.LWP.biotSavart (Work.SolutionDelivery.cutDatum L ω)) := by
  have hα1' : α ≤ 1 := NNReal.coe_le_coe.mp hα1
  have hR : (0 : ℝ) ≤ 2 * L := by linarith
  have hint : Integrable (Work.SolutionDelivery.cutDatum L ω) :=
    Work.SolutionDelivery.cutDatum_integrable hL hmeas hbdd
  have hbfun : IsBoundedFun ω :=
    Work.Stability.isBoundedFun_of_forall_norm_le hbdd
  have hholder' : Holder α (Work.SolutionDelivery.cutDatum L ω) :=
    cutDatum_holder_of_holder hL hα1' hbfun hholder
  have hsupp : ∀ y : R3,
      Work.SolutionDelivery.cutDatum L ω y ≠ 0 → y ∈ Metric.closedBall 0 (2 * L) :=
    fun y hy => Work.SolutionDelivery.cutDatum_support (L := L) hL (ω := ω) y hy
  have hdec : Work.LWP.VorticityDecay α (Work.SolutionDelivery.cutDatum L ω) :=
    Work.SolutionDelivery.vorticityDecay_of_support_bdd hR hM hsupp
      (Work.SolutionDelivery.cutDatum_bdd hbdd)
  have h := Work.LWP.assembly_data hlwp hR hM hint (Work.SolutionDelivery.cutDatum_bdd hbdd)
    hholder' hdiv hsupp hodd hdec
  exact ⟨h.1, h.2.1⟩

/-- **The maximal solution exists from the weakened datum class.**  This is
`Work.SolutionDelivery.exists_maximal_of_datum` with `IsContDiffHolder ℝ α ωS` replaced by
`Holder α ωS` (plus boundedness); it shows that the `hmax` field of
`Work.SolutionDelivery.ConstructedSolution` is *not* the obstruction to the repair. -/
theorem exists_maximal_of_datum_of_holder {α : NNReal} (hlwp : Work.LWP.LWPInputs α) {L M : ℝ}
    (hL : 0 < L) (hM : 0 ≤ M) {ωS : R3 → R3}
    (hmeas : MeasureTheory.AEStronglyMeasurable ωS MeasureTheory.volume)
    (hbdd : ∀ x : R3, ‖ωS x‖ ≤ M) (hholder : Holder α ωS)
    (hα : 0 < (α : ℝ)) (hα1 : (α : ℝ) ≤ 1)
    (hdiv : ∀ x : R3, FiniteTimeSingularity.div (Work.SolutionDelivery.cutDatum L ωS) x = 0)
    (hodd : FiniteTimeSingularity.IsOdd
      (Work.LWP.biotSavart (Work.SolutionDelivery.cutDatum L ωS))) :
    ∃ T : ℝ, 0 < T ∧
      Nonempty (Work.LWP.MaximalSolution α
        (Work.LWP.biotSavart (Work.SolutionDelivery.cutDatum L ωS)) T) :=
  let h := datumData_of_cut_of_holder hlwp hL hM hα hα1 hmeas hbdd hholder hdiv hodd
  hlwp.maxExists _ h.1 h.2

end Work.ConstructionInstance
end
end
-- ===== merged: Submission.Work.ConstructionInstance.SelfSim =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

namespace Work.ConstructionInstance

/-- **The constructed (cut) self-similar vorticity**:

  `selfSimVort p g L lam x t = λ̄(t)⁻¹ · χ(ρ(x)/L) · F(ρ(x)^p/λ̄(t), θ(x)) · e_θ(x)`. -/
def selfSimVort (p : ℝ) (g : ℝ → ℝ → ℝ) (L : ℝ) (lam : ℝ → ℝ) : R3 → ℝ → R3 :=
  fun x t => (lam t)⁻¹ •
    (Work.Stability.chi (Work.Cyl.rho x / L) • omegaSz p g (Work.Cyl.rho x ^ p / lam t) x)

theorem selfSimVort_apply (p : ℝ) (g : ℝ → ℝ → ℝ) (L : ℝ) (lam : ℝ → ℝ) (x : R3) (t : ℝ) :
    selfSimVort p g L lam x t = (lam t)⁻¹ •
      (Work.Stability.chi (Work.Cyl.rho x / L) • omegaSz p g (Work.Cyl.rho x ^ p / lam t) x) :=
  rfl

/-- **The support box**: the cut-off makes the field vanish outside `B(0, 2L)`, so any `R ≥ 2L`
works — independently of the flow, of `λ̄` and of `t`. -/
theorem selfSimVort_support {p : ℝ} {g : ℝ → ℝ → ℝ} {L : ℝ} (hL : 0 < L) {R : ℝ}
    (hR : 2 * L ≤ R) {lam : ℝ → ℝ} :
    ∀ t : ℝ, ∀ y : R3, selfSimVort p g L lam y t ≠ 0 → y ∈ Metric.closedBall 0 R := by
  intro t y hy
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra hlt
  rw [not_le] at hlt
  have h2 : 2 ≤ Work.Cyl.rho y / L := by
    rw [Work.Cyl.rho_eq_norm, le_div_iff₀ hL]
    linarith
  rw [selfSimVort_apply, Work.Stability.chi_eq_zero (h2.trans (le_abs_self _)), zero_smul,
    smul_zero] at hy
  exact hy rfl

/-- **The self-similar box for the constructed vorticity**: for `λ̄(t) > 0`,
`λ̄(t)·‖ω(x,t)‖ ≤ 20p + Cg`, because the cut-off factor is in `[0,1]`. -/
theorem selfSimVort_bdd {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) {g : ℝ → ℝ → ℝ} {Cg : ℝ}
    (hCg : 0 ≤ Cg) (hgbdd : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → |g z θ| ≤ Cg)
    {L : ℝ} (hL : 0 < L) {lam : ℝ → ℝ} {t : ℝ} (ht : 0 < lam t) (x : R3) :
    lam t * ‖selfSimVort p g L lam x t‖ ≤ 20 * p + Cg := by
  have hz : 0 ≤ Work.Cyl.rho x ^ p / lam t :=
    div_nonneg (Real.rpow_nonneg (Work.Cyl.rho_nonneg x) p) ht.le
  have hbox := omegaSz_norm_le hp hp1 hCg hgbdd hz x
  have hchi : Work.Stability.chi (Work.Cyl.rho x / L) ≤ 1 := Work.Stability.chi_le_one _
  have hchi0 : 0 ≤ Work.Stability.chi (Work.Cyl.rho x / L) := Work.Stability.chi_nonneg _
  rw [selfSimVort_apply, mul_norm_inv_smul ht]
  calc ‖Work.Stability.chi (Work.Cyl.rho x / L) • omegaSz p g (Work.Cyl.rho x ^ p / lam t) x‖
      = |Work.Stability.chi (Work.Cyl.rho x / L)|
          * ‖omegaSz p g (Work.Cyl.rho x ^ p / lam t) x‖ := norm_smul _ _
    _ ≤ 1 * ‖omegaSz p g (Work.Cyl.rho x ^ p / lam t) x‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        rw [abs_of_nonneg hchi0]; exact hchi
    _ ≤ 20 * p + Cg := by rw [one_mul]; exact hbox

end Work.ConstructionInstance
end
end
-- ===== merged: Submission.Work.ConstructionInstance.div_selfSim_field =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

set_option linter.unusedVariables false

open FiniteTimeSingularity Work.Cyl

/-!
# `div (c⁻¹ • omegaSz p g (ρ^p/c)) = 0`

The time-dependent self-similar ansatz of the stability layer reads
`ω(x,t) = λ̄(t)⁻¹ • omegaSz p g (ρ(x)^p / λ̄(t)) x` (`Boxes.lean`): for *every* fixed value of the
scaling constant `c = λ̄(t)` this field must be divergence free, so that the Biot–Savart velocity
`u = BS ω` of the ansatz has the correct vorticity.

The field is a swirl field `A • e_θ` with scalar factor
`A(y) = c⁻¹ * profile p g (ρ(y)^p/c) (θ(y))`, so the two structural facts of the `Cyl` layer give
the result off the degeneracy set `{r = 0} ∪ {x₃ = 0}`:

* `div (A • e_θ) x = A x · div e_θ x + (fderiv A x)(e_θ x)` (`div_smul_eq`),
* `div e_θ = 0` off the axis (`div_eTheta`),
* `(fderiv A x)(e_θ x) = 0`: along the line `t ↦ x + t • e_θ(x)` both `ρ(x+t e_θ) = √(ρ(x)²+t²)`
  and `θ(x+t e_θ) = arctan(x₃/√(radSq(x)+t²))` are *even* functions of `t`
  (`rho_add_smul_eTheta`, `theta_add_smul_eTheta`), so the derivative of the (even) line function
  at `t = 0` vanishes (`deriv_zero_of_even`).

The profile is `C¹` at `(ρ(x)^p/c, θ(x))` only when `θ(x) ≠ 0` (the angular factor
`Γ(θ) = (sinθcos²θ)^{p/3}` is not differentiable at `θ = 0` for `p ≤ 1`), whence the on-axis and
in-plane cases are treated separately, by *not* differentiating at all: whenever the field happens
to be differentiable at `x`, each diagonal entry of its Jacobian is computed along a coordinate
line and vanishes, because on the axis, and on the plane, the paired coordinate of the field
vanishes identically along the paired coordinate line; and where the field is not differentiable
the Fréchet derivative is `0` in Mathlib (`fderiv_zero_of_not_differentiableAt`), hence so is its
trace.  This is the same dichotomy as in `div_omega0_all`.
-/

/-! ## The `e_θ`-derivative of the scalar factor vanishes

Along `t ↦ x + t • e_θ(x)` the *self-similar variable* `ρ^p/c` of the profile is even in `t`, and
so is the angle `θ`; hence the whole scalar factor is an even function of `t`. -/

private theorem selfSim_scalar_fderiv_eTheta {p c : ℝ} {g : ℝ → ℝ → ℝ} {x : R3}
    (hr : 0 < Work.Cyl.radial x)
    (hA : DifferentiableAt ℝ
      (fun y : R3 => c⁻¹ * Work.ConstructionInstance.profile p g (Work.Cyl.rho y ^ p / c)
        (Work.Cyl.theta y)) x) :
    fderiv ℝ
      (fun y : R3 => c⁻¹ * Work.ConstructionInstance.profile p g (Work.Cyl.rho y ^ p / c)
        (Work.Cyl.theta y)) x (Work.Cyl.eTheta x) = 0 := by
  rw [Work.Cyl.fderiv_apply_eq_deriv_line _ x _ hA]
  apply deriv_zero_of_even
  intro t
  rw [rho_add_smul_eTheta x hr (-t), rho_add_smul_eTheta x hr t,
    theta_add_smul_eTheta x hr (-t), theta_add_smul_eTheta x hr t, neg_sq]

/-- Divergence of a swirl field `F • e_θ` whose scalar factor has vanishing `e_θ`-derivative. -/
private theorem div_smul_eTheta_of_fderiv_zero {F : R3 → ℝ} {x : R3}
    (hF : DifferentiableAt ℝ F x) (hr : 0 < Work.Cyl.radial x)
    (h0 : fderiv ℝ F x (Work.Cyl.eTheta x) = 0) :
    FiniteTimeSingularity.div (fun y : R3 => F y • Work.Cyl.eTheta y) x = 0 := by
  change FiniteTimeSingularity.div (F • Work.Cyl.eTheta) x = 0
  rw [div_smul_eq F Work.Cyl.eTheta x hF (differentiableAt_eTheta x hr), div_eTheta x hr, h0,
    mul_zero, zero_add]

/-! ## Vanishing of the paired coordinate along the coordinate lines of the degenerate set

The two ingredients of the on-axis/in-plane branch are supplied by the fleet (and proved in
`selfSim_profile_eTheta_coord_eq_zero.lean`), so that this file stays an assembly:

* `selfSim_profile_eTheta_coord_eq_zero` — on the axis and on the plane the `i`-th coordinate of
  `profile p g (ρ^p/c) (θ) · e_θ` vanishes along the `i`-th coordinate line;
* `selfSim_scalar_differentiableAt` — the scalar factor `c⁻¹ * profile p g (ρ^p/c) (θ)` is
  differentiable off the axis at points where the profile is (used in the off-plane branch). -/

/-! ## The main theorem -/

theorem div_selfSim_field {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) {g : ℝ → ℝ → ℝ}
    (hvt : Work.Spaces.VanishTheta g) (hsmooth : Work.Stability.SmoothFar g) {c : ℝ} (hc : 0 < c) :
    ∀ x : Work.ConstructionInstance.R3,
      FiniteTimeSingularity.div
        (fun y : Work.ConstructionInstance.R3 =>
          c⁻¹ • Work.ConstructionInstance.omegaSz p g (Work.Cyl.rho y ^ p / c) y) x = 0 := by
  intro x
  have hfield : (fun y : R3 => c⁻¹ • omegaSz p g (Work.Cyl.rho y ^ p / c) y)
      = fun y : R3 =>
          (c⁻¹ * profile p g (Work.Cyl.rho y ^ p / c) (Work.Cyl.theta y)) • Work.Cyl.eTheta y := by
    funext y
    rw [omegaSz_apply, smul_smul]
  rw [hfield]
  by_cases hgen : 0 < Work.Cyl.radial x ∧ Work.Cyl.axial x ≠ 0
  · -- off the axis and off the plane: the swirl-field computation
    have hr : 0 < Work.Cyl.radial x := hgen.1
    have hρpos : 0 < Work.Cyl.rho x := lt_of_lt_of_le hr (Work.Cyl.radial_le_rho x)
    have hθ0 : Work.Cyl.theta x ≠ 0 := by
      intro h
      have h1 : Work.Cyl.axial x / Work.Cyl.radial x = 0 := by
        rw [← Real.arctan_eq_zero_iff]
        exact h
      rcases div_eq_zero_iff.mp h1 with h2 | h2
      · exact hgen.2 h2
      · exact absurd h2 (ne_of_gt hr)
    have hz : -1 < Work.Cyl.rho x ^ p / c := by
      have hpos : 0 < Work.Cyl.rho x ^ p / c :=
        div_pos (Real.rpow_pos_of_pos hρpos p) hc
      linarith
    have hθmem : Work.Cyl.theta x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
      ⟨Real.neg_pi_div_two_lt_arctan _, Real.arctan_lt_pi_div_two _⟩
    have hF : Work.Cyl.DiffAt2 (profile p g) (Work.Cyl.rho x ^ p / c) (Work.Cyl.theta x) :=
      (contDiffAt_uncurry_profile hsmooth hz hθmem hθ0).differentiableAt (by norm_num)
    have hA := selfSim_scalar_differentiableAt (p := p) (c := c) (g := g) hr hF
    exact div_smul_eTheta_of_fderiv_zero hA hr (selfSim_scalar_fderiv_eTheta hr hA)
  · -- on the axis or on the plane: differentiate along coordinate lines, or not at all
    have hcase : Work.Cyl.radial x = 0 ∨ Work.Cyl.axial x = 0 := by
      rcases not_and_or.mp hgen with h | h
      · exact Or.inl (le_antisymm (not_lt.mp h) (Work.Cyl.radial_nonneg x))
      · exact Or.inr (not_not.mp h)
    by_cases hd : DifferentiableAt ℝ
        (fun y : R3 => (c⁻¹ * profile p g (Work.Cyl.rho y ^ p / c) (Work.Cyl.theta y))
          • Work.Cyl.eTheta y) x
    · rw [Work.Cyl.div_eq_sum_partials _ x hd]
      apply Finset.sum_eq_zero
      intro i _
      have hline : (fun t : ℝ => ((fun y : R3 =>
          (c⁻¹ * profile p g (Work.Cyl.rho y ^ p / c) (Work.Cyl.theta y))
            • Work.Cyl.eTheta y) (x + t • Work.Cyl.basisVec i)) i) = fun _ : ℝ => 0 := by
        funext t
        simp only [PiLp.smul_apply, smul_eq_mul]
        rw [mul_assoc, selfSim_profile_eTheta_coord_eq_zero hp.ne' hvt.1 hcase i t, mul_zero]
      rw [hline]
      simp
    · rw [FiniteTimeSingularity.div, fderiv_zero_of_not_differentiableAt hd]
      simp

end Work.ConstructionInstance
end
-- ===== merged: Submission.Work.ConstructionInstance.eTheta_dist_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false

namespace Work.ConstructionInstance

open Work.Cyl

/-! # The `√2`-Lipschitz bound for the angular frame vector `e_θ`

Off the axis `r = 0` the vector `e_θ x = (-x₁, x₀, 0)/r(x)` is a unit vector, and the geometric
input used in the construction is the *sharp* quantitative continuity estimate

  `‖e_θ x - e_θ y‖ ≤ √2 ‖x - y‖ / min (r x) (r y)`  for `r x > 0`, `r y > 0`.

The weaker bound with constant `2` (single radius `r y`) is `Work.Cyl.eTheta_sub_norm_mul_le`;
the improvement to `√2` and to the *minimum* of the two radii comes from the exact angle formula
`‖u/‖u‖ - v/‖v‖‖² = 2 - 2⟪u,v⟫/(‖u‖‖v‖)` together with the identity
`‖u - v‖² = ‖u‖² + ‖v‖² - 2⟪u,v⟫`.

The proof is organised in two steps.

* `norm_unit_sub_le` is a purely Hilbert-space statement: for nonzero `u v` in a real inner
  product space, the normalised vectors satisfy `‖u/‖u‖ - v/‖v‖‖ ≤ √2 ‖u-v‖ / min ‖u‖ ‖v‖`.
  Writing `a = ‖u‖`, `b = ‖v‖`, `c = ⟪u,v⟫` and assuming `a ≤ b` (so `min = a`), multiplying by
  `a b` (both `> 0`) turns the claim into the polynomial inequality `0 ≤ b³ + c (a - 2b)`, which
  follows from `c ≤ a b` and `a ≤ b`:
  `b³ + c(a-2b) ≥ b³ + ab(a-2b) = b(a-b)² ≥ 0`.
* `eTheta x = ‖angularVec x‖⁻¹ • angularVec x` and `‖angularVec x - angularVec y‖ ≤ ‖x - y‖`
  (the map `angularVec` is the (isometric) rotation by `90°` of the projection onto the
  `(x₀,x₁)`-plane), so the Hilbert-space statement applies with `u = angularVec x`,
  `v = angularVec y`. -/

/-- The Hilbert-space core of the estimate, in the case `‖u‖ ≤ ‖v‖`: with `a = ‖u‖`, `b = ‖v‖`
and `c = ⟪u,v⟫`, `b e_θ`-style normalisation gives `‖u/a - v/b‖ ≤ √2 ‖u-v‖ / a`.

Multiplying by `a b > 0` and squaring reduces the claim to `0 ≤ b³ + c(a-2b)`, which holds
because `c ≤ a b` (`real_inner_le_norm`) and `a ≤ b`, whence
`b³ + c(a-2b) ≥ b³ + ab(a-2b) = b (a-b)² ≥ 0`. -/
private lemma norm_unit_sub_le_aux {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u v : E) (hu : u ≠ 0) (hab : ‖u‖ ≤ ‖v‖) :
    ‖(‖u‖⁻¹ : ℝ) • u - (‖v‖⁻¹ : ℝ) • v‖ ≤ Real.sqrt 2 * ‖u - v‖ / ‖u‖ := by
  have ha : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hb : 0 < ‖v‖ := lt_of_lt_of_le ha hab
  set L := ‖(‖u‖⁻¹ : ℝ) • u - (‖v‖⁻¹ : ℝ) • v‖ with hL
  have h1 : (‖u‖ * ‖v‖) * ‖u‖⁻¹ = ‖v‖ := by
    rw [mul_assoc, mul_comm ‖v‖ ‖u‖⁻¹, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt ha), one_mul]
  have h2 : (‖u‖ * ‖v‖) * ‖v‖⁻¹ = ‖u‖ := by
    rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt hb), mul_one]
  have hvec : (‖u‖ * ‖v‖) • ((‖u‖⁻¹ : ℝ) • u - (‖v‖⁻¹ : ℝ) • v) = ‖v‖ • u - ‖u‖ • v := by
    rw [smul_sub, smul_smul, smul_smul, h1, h2]
  have hLab : L * (‖u‖ * ‖v‖) = ‖‖v‖ • u - ‖u‖ • v‖ := by
    rw [hL, mul_comm, ← norm_smul_of_nonneg (mul_nonneg ha.le hb.le), hvec]
  have hsqL : ‖‖v‖ • u - ‖u‖ • v‖ ^ 2
      = 2 * ‖u‖ ^ 2 * ‖v‖ ^ 2 - 2 * ‖u‖ * ‖v‖ * (inner ℝ u v) := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
    rw [real_inner_comm v u, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
    ring
  have hsqR : ‖u - v‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 - 2 * (inner ℝ u v) := by
    rw [norm_sub_sq_real]; ring
  have hkey : 0 ≤ ‖v‖ ^ 3 + (inner ℝ u v) * (‖u‖ - 2 * ‖v‖) := by
    have hprod : 0 ≤ (‖u‖ * ‖v‖ - inner ℝ u v) * (2 * ‖v‖ - ‖u‖) :=
      mul_nonneg (by linarith [real_inner_le_norm u v]) (by linarith)
    have hsq2 : 0 ≤ ‖v‖ * (‖u‖ - ‖v‖) ^ 2 := mul_nonneg hb.le (sq_nonneg _)
    nlinarith [hprod, hsq2]
  have hsq : (L * (‖u‖ * ‖v‖)) ^ 2 ≤ (Real.sqrt 2 * ‖u - v‖ * ‖v‖) ^ 2 := by
    rw [hLab, hsqL]
    rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), hsqR]
    nlinarith [hkey, hb]
  have hfin : L * (‖u‖ * ‖v‖) ≤ Real.sqrt 2 * ‖u - v‖ * ‖v‖ := by
    have h := sq_le_sq.mp hsq
    rwa [abs_of_nonneg (mul_nonneg (norm_nonneg _) (mul_nonneg ha.le hb.le)),
      abs_of_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg 2) (norm_nonneg _)) hb.le)] at h
  have hfin2 : L * ‖u‖ ≤ Real.sqrt 2 * ‖u - v‖ := by
    refine le_of_mul_le_mul_right ?_ hb
    nlinarith [hfin]
  rw [le_div_iff₀ ha]
  exact hfin2

/-- **Hilbert-space core of the `√2`-Lipschitz bound.**  For nonzero `u v` in a real inner product
space, the normalised vectors satisfy
`‖u/‖u‖ - v/‖v‖‖ ≤ √2 ‖u - v‖ / min ‖u‖ ‖v‖`.

WLOG `‖u‖ ≤ ‖v‖` (`min = ‖u‖`), which is exactly `norm_unit_sub_le_aux`; the other case is
obtained by exchanging `u` and `v`, both sides being symmetric under the swap. -/
private lemma norm_unit_sub_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u v : E) (hu : u ≠ 0) (hv : v ≠ 0) :
    ‖(‖u‖⁻¹ : ℝ) • u - (‖v‖⁻¹ : ℝ) • v‖
      ≤ Real.sqrt 2 * ‖u - v‖ / min ‖u‖ ‖v‖ := by
  rcases le_total ‖u‖ ‖v‖ with h | h
  · rw [min_eq_left h]
    exact norm_unit_sub_le_aux u v hu h
  · rw [min_eq_right h]
    have hk := norm_unit_sub_le_aux v u hv h
    calc ‖(‖u‖⁻¹ : ℝ) • u - (‖v‖⁻¹ : ℝ) • v‖
        = ‖(‖v‖⁻¹ : ℝ) • v - (‖u‖⁻¹ : ℝ) • u‖ := norm_sub_rev _ _
      _ ≤ Real.sqrt 2 * ‖v - u‖ / ‖v‖ := hk
      _ = Real.sqrt 2 * ‖u - v‖ / ‖v‖ := by rw [norm_sub_rev]

/-- `angularVec` is the rotation by `90°` of the projection of `x` onto the `(x₀,x₁)`-plane, so
it does not increase distances. -/
private lemma norm_angularVec_sub_le_dist (x y : R3) :
    ‖Work.Cyl.angularVec x - Work.Cyl.angularVec y‖ ≤ ‖x - y‖ := by
  have h : ‖Work.Cyl.angularVec x - Work.Cyl.angularVec y‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, Work.Cyl.inner_eq,
      Work.Cyl.inner_eq]
    simp only [PiLp.sub_apply, Work.Cyl.angularVec_apply_zero, Work.Cyl.angularVec_apply_one,
      Work.Cyl.angularVec_apply_two]
    nlinarith [sq_nonneg (x 2 - y 2)]
  have := sq_le_sq.mp h
  rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)] at this

theorem eTheta_dist_le (x y : Work.ConstructionInstance.R3)
    (hx : 0 < Work.Cyl.radial x) (hy : 0 < Work.Cyl.radial y) :
    ‖Work.Cyl.eTheta x - Work.Cyl.eTheta y‖
      ≤ Real.sqrt 2 * ‖x - y‖
        / min (Work.Cyl.radial x) (Work.Cyl.radial y) := by
  have hx0 : Work.Cyl.angularVec x ≠ 0 := by
    rw [← norm_pos_iff, Work.Cyl.norm_angularVec]; exact hx
  have hy0 : Work.Cyl.angularVec y ≠ 0 := by
    rw [← norm_pos_iff, Work.Cyl.norm_angularVec]; exact hy
  have hkey := norm_unit_sub_le (Work.Cyl.angularVec x) (Work.Cyl.angularVec y) hx0 hy0
  have hEx : Work.Cyl.eTheta x = ‖Work.Cyl.angularVec x‖⁻¹ • Work.Cyl.angularVec x := by
    rw [Work.Cyl.eTheta, one_div, ← Work.Cyl.norm_angularVec]
  have hEy : Work.Cyl.eTheta y = ‖Work.Cyl.angularVec y‖⁻¹ • Work.Cyl.angularVec y := by
    rw [Work.Cyl.eTheta, one_div, ← Work.Cyl.norm_angularVec]
  rw [← hEx, ← hEy, Work.Cyl.norm_angularVec, Work.Cyl.norm_angularVec] at hkey
  have hm : 0 < min (Work.Cyl.radial x) (Work.Cyl.radial y) := lt_min hx hy
  have hnum : Real.sqrt 2 * ‖Work.Cyl.angularVec x - Work.Cyl.angularVec y‖
      ≤ Real.sqrt 2 * ‖x - y‖ :=
    mul_le_mul_of_nonneg_left (norm_angularVec_sub_le_dist x y) (Real.sqrt_nonneg 2)
  have h1 : ‖Work.Cyl.eTheta x - Work.Cyl.eTheta y‖
      * min (Work.Cyl.radial x) (Work.Cyl.radial y) ≤ Real.sqrt 2 * ‖x - y‖ :=
    le_trans ((le_div_iff₀ hm).mp hkey) hnum
  exact (le_div_iff₀ hm).mpr h1

end Work.ConstructionInstance
end
-- ===== merged: Submission.Work.ConstructionInstance.exists_omegaSz_low_radius =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

/-!
# The profile's lower bound at a prescribed self-similar scale, inside a ball of radius `L`

This is the radius-refined companion of `exists_omegaSz_low`: there we produced *some* point with
self-similar variable `1`; here we must additionally keep that point inside the cylinder of
radius `L`.  The witness is again on the ray `x = (t,0,t)` with `(√2 t)^p = s`, for which
`ρ(x) = √2 t = s^{1/p}`; the hypothesis `s^{1/p} ≤ L` is exactly the requirement `ρ(x) ≤ L`.
-/

theorem exists_omegaSz_low_radius {p L s : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) {g : ℝ → ℝ → ℝ}
    {Cg : ℝ} (hgbdd : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → |g z θ| ≤ Cg)
    (hsmall : Cg ≤ p * Work.Spaces.Gam p (Real.pi / 4) / (4 * Work.Spaces.c p))
    (hs : 0 < s) (hsL : s ^ (1 / p) ≤ L) :
    ∃ x : Work.ConstructionInstance.R3, Work.Cyl.rho x ≤ L ∧
      p * Work.Spaces.Gam p (Real.pi / 4) / (4 * Work.Spaces.c p)
        ≤ ‖Work.ConstructionInstance.omegaSz p g (Work.Cyl.rho x ^ p / s) x‖ := by
  -- The scale `t` with `√2 · t = s^{1/p}` (hence `(√2 t)^p = s`).
  have hspos : 0 < s ^ (1 / p) := Real.rpow_pos_of_pos hs (1 / p)
  have hsqrt2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  set t : ℝ := s ^ (1 / p) / Real.sqrt 2 with htdef
  have ht : 0 < t := by rw [htdef]; exact div_pos hspos hsqrt2
  have hbase : Real.sqrt 2 * t = s ^ (1 / p) := by
    rw [htdef]; field_simp
  -- `(√2 t)^p = s`.
  have htp : (Real.sqrt 2 * t) ^ p = s := by
    rw [hbase, ← Real.rpow_mul (le_of_lt hs) (1 / p) p, one_div,
      inv_mul_cancel₀ (ne_of_gt hp), Real.rpow_one]
  -- `ρ(t,0,t) = √2 · t = s^{1/p} ≤ L`.
  have hrho : Work.Cyl.rho (!₂[t, 0, t] : R3) = Real.sqrt 2 * t := by
    rw [Work.Cyl.rho, Work.Cyl.radSq, Work.Cyl.axial]
    simp
    rw [show t ^ 2 + t ^ 2 = 2 * t ^ 2 by ring, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
      Real.sqrt_sq ht.le]
  refine ⟨!₂[t, 0, t], ?_, ?_⟩
  · rw [hrho, hbase]; exact hsL
  · -- The self-similar variable of that point is `1`.
    have hz : Work.Cyl.rho (!₂[t, 0, t] : R3) ^ p / s = 1 := by
      rw [hrho, htp, div_self (ne_of_gt hs)]
    -- The value of the vorticity on the ray: `F(1,π/4) • e₁`, and `‖e₁‖ = 1`.
    have hray := omegaSz_ray_quad (p := p) (z := 1) (t := t) ht g
    have he1 : ‖(!₂[0, 1, 0] : R3)‖ = 1 := by
      rw [EuclideanSpace.norm_eq]
      simp only [Fin.sum_univ_three]
      norm_num
    have hnorm : ‖omegaSz p g (Work.Cyl.rho (!₂[t, 0, t] : R3) ^ p / s)
          (!₂[t, 0, t] : R3)‖ = |profile p g 1 (Real.pi / 4)| := by
      rw [hz, hray, norm_smul, Real.norm_eq_abs, he1, mul_one]
    calc p * Work.Spaces.Gam p (Real.pi / 4) / (4 * Work.Spaces.c p)
        ≤ |profile p g 1 (Real.pi / 4)| := profile_abs_lower_one hp hp1 hgbdd hsmall
      _ = ‖omegaSz p g (Work.Cyl.rho (!₂[t, 0, t] : R3) ^ p / s) (!₂[t, 0, t] : R3)‖ :=
          hnorm.symm

end Work.ConstructionInstance
end
-- ===== merged: Submission.Work.ConstructionInstance.gComp_abs_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

set_option linter.unusedVariables false

open Set Filter
open scoped Topology

/-- `(r/ρ)^{2α} ≤ r^α` for `0 ≤ r ≤ ρ²`.  Writing `r = s ρ` (`s = r/ρ ≤ ρ ≤ 1`), this is
`s^{2α} ≤ s^α ρ^α`, i.e. `s^α ≤ ρ^α`. -/
private lemma rpow_two_mul_le_of_le_sq {α r ρ : ℝ} (hα : 0 < α) (hr : 0 ≤ r) (hρ : 0 < ρ)
    (h : r ≤ ρ ^ 2) : (r / ρ) ^ (2 * α) ≤ r ^ α := by
  have hs0 : 0 ≤ r / ρ := div_nonneg hr hρ.le
  have hsρ : r / ρ ≤ ρ := by
    rw [div_le_iff₀ hρ]; nlinarith
  have h1 : (r / ρ) ^ α ≤ ρ ^ α := Real.rpow_le_rpow hs0 hsρ hα.le
  have h2 : (r / ρ) ^ (2 * α) = (r / ρ) ^ α * (r / ρ) ^ α := by
    rw [show 2 * α = α + α from by ring, Real.rpow_add' hs0 (by positivity)]
  rw [h2]
  calc (r / ρ) ^ α * (r / ρ) ^ α ≤ (r / ρ) ^ α * ρ ^ α :=
        mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hs0 α)
    _ = (r / ρ * ρ) ^ α := (Real.mul_rpow hs0 hρ.le).symm
    _ = r ^ α := by rw [div_mul_cancel₀ r hρ.ne']

/-- `ρ^{3α} ≤ r^α` for `0 < ρ ≤ 1` and `ρ² < r`.  Indeed `ρ^{3α} ≤ ρ^{2α} = (ρ²)^α ≤ r^α`. -/
private lemma rpow_three_mul_le_of_sq_lt {α r ρ : ℝ} (hα : 0 < α) (hr : 0 ≤ r) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) (h : ρ ^ 2 < r) : ρ ^ (3 * α) ≤ r ^ α := by
  have h1 : ρ ^ (3 * α) ≤ ρ ^ (2 * α) :=
    Real.rpow_le_rpow_of_exponent_ge hρ hρ1 (by linarith)
  have h2 : ρ ^ (2 * α) = (ρ ^ 2) ^ α := by
    rw [Real.rpow_mul hρ.le (2:ℝ) α, Real.rpow_two]
  calc ρ ^ (3 * α) ≤ ρ ^ (2 * α) := h1
    _ = (ρ ^ 2) ^ α := h2
    _ ≤ r ^ α := Real.rpow_le_rpow (sq_nonneg ρ) h.le hα.le

/-- The perturbation composite `ĝ : x ↦ g (ρ x ^ (3α)) (|θ x|)` vanishes at least like `r^α`,
`r = Cyl.radial` — the second input of `holder_smul_eTheta` (it is what absorbs the
discontinuity of `e_θ` on the axis `r = 0`).

Proof.  Write `r = Cyl.radial x`, `ρ = Cyl.rho x`, `θ' = |Cyl.theta x|`, `z = ρ^{3α}`.

On the axis (`r = 0`) we have `θ x = arctan (x₃/0) = 0` and `Cyl.radial x ^ α = 0`, so `ĝ x = 0`
by `Spaces.VanishTheta`.

Off the axis, `Γ(α,θ') ≤ (r/ρ)^{2α}` (the angular factor, `Gamma_abs_theta_le`), so `|g z θ'|`
is dominated by both

* `Cv · Γ(α,θ') ≤ Cv · (r/ρ)^{2α}` (`hvan`), and
* `K · ρ^{3α}` (`g_z_linear_bound`, available as long as `ρ ≤ 1`).

If `r ≤ ρ²`, or if `ρ ≥ 1`, then `(r/ρ)^{2α} ≤ r^α` and the first bound gives `|g| ≤ Cv r^α`.
If `r > ρ²` and `ρ ≤ 1`, the second gives `|g| ≤ K ρ^{3α} ≤ K r^α`.  Hence
`Ca = max K Cv` works. -/
theorem gComp_abs_le {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1/3) {g : ℝ → ℝ → ℝ}
    {Cv Lg Lθ : ℝ} (hCv : 0 ≤ Cv) (hLg : 0 ≤ Lg) (hLθ : 0 ≤ Lθ)
    (hvt : Work.Spaces.VanishTheta g)
    (hquad0 : ∀ θ : ℝ, g 0 θ = 0)
    (hquad1 : ∀ θ : ℝ, Work.Spaces.pz g 0 θ = 0)
    (hvan : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |g z θ| ≤ Cv * Work.ConstructionInstance.Gamma α θ)
    (hzk : ∀ z z' θ : ℝ, 0 ≤ z → 0 ≤ z' → θ ∈ Work.Spaces.Iθ →
      |g z θ - g z' θ| ≤ Lg * |z - z'| ^ α)
    (hzth : ∀ z θ θ' : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → θ' ∈ Work.Spaces.Iθ →
      |g z θ - g z θ'| ≤ Lθ * |θ - θ'| ^ α)
    (hsm : ContDiffOn ℝ 2 (Function.uncurry g)
      (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1))) :
    ∃ Ca : ℝ, 0 ≤ Ca ∧ ∀ x : R3,
      |g (Work.Cyl.rho x ^ (3 * α)) (|Work.Cyl.theta x|)| ≤ Ca * (Work.Cyl.radial x) ^ α := by
  obtain ⟨K, hK0, hKbd⟩ := g_z_linear_bound hquad0 hsm
  refine ⟨max K Cv, le_trans hK0 (le_max_left K Cv), ?_⟩
  intro x
  by_cases hr : Work.Cyl.radial x = 0
  · have hθ : |Work.Cyl.theta x| = 0 := by
      rw [Work.Cyl.theta, hr, div_zero, Real.arctan_zero, abs_zero]
    have hz : Work.Cyl.radial x ^ α = 0 := by rw [hr, Real.zero_rpow hα.ne']
    rw [hθ, hvt.1, abs_zero, hz, mul_zero]
  · have hrpos : 0 < Work.Cyl.radial x :=
      lt_of_le_of_ne (Work.Cyl.radial_nonneg x) (Ne.symm hr)
    have hρpos : 0 < Work.Cyl.rho x := lt_of_lt_of_le hrpos (Work.Cyl.radial_le_rho x)
    have hρnn : 0 ≤ Work.Cyl.rho x := hρpos.le
    have hrn : 0 ≤ Work.Cyl.radial x := hrpos.le
    have hIθ : |Work.Cyl.theta x| ∈ Work.Spaces.Iθ := by
      refine ⟨abs_nonneg _, ?_⟩
      rw [Work.Cyl.theta]
      exact abs_le.mpr ⟨le_of_lt (Real.neg_pi_div_two_lt_arctan _),
        le_of_lt (Real.arctan_lt_pi_div_two _)⟩
    have hvan' : |g (Work.Cyl.rho x ^ (3 * α)) (|Work.Cyl.theta x|)|
        ≤ Cv * (Work.Cyl.radial x / Work.Cyl.rho x) ^ (2 * α) := by
      calc |g (Work.Cyl.rho x ^ (3 * α)) (|Work.Cyl.theta x|)|
          ≤ Cv * Gamma α (|Work.Cyl.theta x|) :=
            hvan _ _ (Real.rpow_nonneg hρnn _) hIθ
        _ ≤ Cv * (Work.Cyl.radial x / Work.Cyl.rho x) ^ (2 * α) :=
            mul_le_mul_of_nonneg_left (Gamma_abs_theta_le hα hrpos) hCv
    by_cases hρ1 : Work.Cyl.rho x ≤ 1
    · by_cases hsub : Work.Cyl.radial x ≤ (Work.Cyl.rho x) ^ 2
      · calc |g (Work.Cyl.rho x ^ (3 * α)) (|Work.Cyl.theta x|)|
            ≤ Cv * (Work.Cyl.radial x / Work.Cyl.rho x) ^ (2 * α) := hvan'
          _ ≤ Cv * (Work.Cyl.radial x) ^ α :=
              mul_le_mul_of_nonneg_left
                (rpow_two_mul_le_of_le_sq hα hrn hρpos hsub) hCv
          _ ≤ max K Cv * (Work.Cyl.radial x) ^ α :=
              mul_le_mul_of_nonneg_right (le_max_right K Cv) (Real.rpow_nonneg hrn α)
      · have hz1 : Work.Cyl.rho x ^ (3 * α) ≤ 1 :=
          Real.rpow_le_one hρnn hρ1 (by positivity)
        have hKb := hKbd (|Work.Cyl.theta x|) hIθ (Work.Cyl.rho x ^ (3 * α))
          ⟨Real.rpow_nonneg hρnn _, hz1⟩
        have h3 : Work.Cyl.rho x ^ (3 * α) ≤ (Work.Cyl.radial x) ^ α :=
          rpow_three_mul_le_of_sq_lt hα hrn hρpos hρ1 (not_le.mp hsub)
        calc |g (Work.Cyl.rho x ^ (3 * α)) (|Work.Cyl.theta x|)|
            ≤ K * (Work.Cyl.rho x ^ (3 * α)) := hKb
          _ ≤ K * (Work.Cyl.radial x) ^ α := mul_le_mul_of_nonneg_left h3 hK0
          _ ≤ max K Cv * (Work.Cyl.radial x) ^ α :=
              mul_le_mul_of_nonneg_right (le_max_left K Cv) (Real.rpow_nonneg hrn α)
    · have hρge : 1 ≤ Work.Cyl.rho x := le_of_lt (not_le.mp hρ1)
      have hsub : Work.Cyl.radial x ≤ (Work.Cyl.rho x) ^ 2 := by
        have h1 : Work.Cyl.radial x ≤ Work.Cyl.rho x := Work.Cyl.radial_le_rho x
        nlinarith
      calc |g (Work.Cyl.rho x ^ (3 * α)) (|Work.Cyl.theta x|)|
          ≤ Cv * (Work.Cyl.radial x / Work.Cyl.rho x) ^ (2 * α) := hvan'
        _ ≤ Cv * (Work.Cyl.radial x) ^ α :=
            mul_le_mul_of_nonneg_left
              (rpow_two_mul_le_of_le_sq hα hrn hρpos hsub) hCv
        _ ≤ max K Cv * (Work.Cyl.radial x) ^ α :=
            mul_le_mul_of_nonneg_right (le_max_right K Cv) (Real.rpow_nonneg hrn α)

end Work.ConstructionInstance
end
-- ===== merged: Submission.Work.ConstructionInstance.isAxiNoSwirl_biotSavart =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

/-- **The Biot–Savart field of an axisymmetric toroidal (swirl) vorticity is axisymmetric
without swirl.**

The vorticity profile `ω x = f (radial x) (axial x) • e_θ(x)` is equivariant under every rotation
`rotLE φ` about the `x₃`-axis (`omega_rotLE`) and anti-invariant under the reflection
`flip1 : x ↦ (x₀,-x₁,x₃)` (`omega_flip1`).  Both properties pass to the Biot–Savart integral,
because substituting `y ↦ g y` (`g` a linear isometry of `ℝ³`) in the Newtonian-potential
integral turns the integrand into `g` of itself — this is `biotSavart_rotLE` for the rotations
and `biotSavart_flip1` for the reflection.  The two resulting symmetries of `u = biotSavart ω`,
together with the existence of the rotation taking a point of the meridian `x₁ = 0` to any point
off the axis (`exists_rotLE_eq`), give `IsAxiNoSwirl u` (`isAxiNoSwirl_of_rot_flip`). -/
theorem isAxiNoSwirl_biotSavart {ω : Work.ConstructionInstance.R3 → Work.ConstructionInstance.R3}
    {f : ℝ → ℝ → ℝ}
    (hω : ∀ x : Work.ConstructionInstance.R3,
      ω x = f (Work.Cyl.radial x) (Work.Cyl.axial x) • Work.Cyl.eTheta x) :
    Work.Cyl.IsAxiNoSwirl (Work.LWP.biotSavart ω) :=
  isAxiNoSwirl_of_rot_flip (Work.LWP.biotSavart ω)
    (fun φ x => biotSavart_rotLE (fun φ x => omega_rotLE hω φ x) φ x)
    (fun x => biotSavart_flip1 (fun x => omega_flip1 hω x) x)
    exists_rotLE_eq

end Work.ConstructionInstance
end
-- ===== merged: Submission.Work.ConstructionInstance.lam_sq_timeDeriv_le_Ioo =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance


end Work.ConstructionInstance
end
-- ===== merged: Submission.Work.ConstructionInstance.omegaStar_eq_Aom =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Topology NNReal ENNReal

namespace Work.ConstructionInstance

/-! ## `Real.rpow` algebra -/

/-- `(r³)^β = r^{3β}` for `r ≥ 0` (the cube analogue of `AuxOmegaStar.rpow_sq_mul`). -/
lemma rpow_cube_mul (β r : ℝ) (hr : 0 ≤ r) : ((r ^ 3 : ℝ)) ^ β = r ^ (3 * β) := by
  rcases eq_or_ne β 0 with h | h
  · subst h; simp
  · have h' : (r ^ 3 : ℝ) = r ^ 2 * r := by ring
    rw [h', Real.mul_rpow (by positivity) hr, rpow_sq_mul β r hr,
      ← Real.rpow_add' hr (by intro hc; exact h (by linarith))]
    congr 1
    ring

/-- **`Real.rpow` at the negative base `-a`**: for `0 ≤ a` and `β ≠ 0`,
`(-a)^β = a^β · cos (βπ)`.  This is the `Real.toReal`-free form of `Real.rpow_def_of_neg`
(`x^y = exp (y log x) cos (yπ)`), using `Real.log (-a) = Real.log a`; the case `a = 0` is the
trivial one `0^β = 0`. -/
lemma rpow_neg_base (a β : ℝ) (ha : 0 ≤ a) (hβ : β ≠ 0) :
    (-a) ^ β = a ^ β * Real.cos (β * Real.pi) := by
  rcases eq_or_lt_of_le ha with h | h
  · subst h; rw [neg_zero, Real.zero_rpow hβ, zero_mul]
  · rw [Real.rpow_def_of_neg (neg_lt_zero.mpr h), Real.rpow_def_of_pos h, Real.log_neg_eq_log]

/-! ## The amplitude of `Γ(θ)·F_*(ρ^{3β})` -/

/-- **The amplitude on a non-negative base.**  For `0 ≤ t`, `0 ≤ s`, `c > 0`,
`(t s²/c³)^β · F_*(c^{3β}) = 2 t^β s^{2β} / (1 + c^{3β})²`: the numerator collects
`(t s²)^β = t^β s^{2β}` (`Real.mul_rpow`, `rpow_sq_mul`) and the denominator
`c^{3β}` (`rpow_cube_mul`) cancels against the `c^{3β}` of `F_*`. -/
lemma amp_of_nonneg_base (β t s c : ℝ) (ht : 0 ≤ t) (hs : 0 ≤ s) (hc : 0 < c) :
    (t * s ^ 2 / c ^ 3) ^ β * Work.FM.Fstar (c ^ (3 * β))
      = 2 * t ^ β * s ^ (2 * β) / (1 + c ^ (3 * β)) ^ 2 := by
  have hc3 : 0 ≤ s ^ 2 / c ^ 3 := div_nonneg (sq_nonneg s) (by positivity)
  have hsplit : t * s ^ 2 / c ^ 3 = t * (s ^ 2 / c ^ 3) := by ring
  rw [hsplit, Real.mul_rpow ht hc3, Real.div_rpow (sq_nonneg s) (by positivity),
    rpow_sq_mul β s hs, rpow_cube_mul β c hc.le, Work.FM.Fstar]
  field_simp

/-- **The amplitude on a strictly negative base** `-t s²/c³`: `Real.rpow` produces the extra
factor `cos (βπ)`, which is precisely `cSign β` on the region `x₂ < 0`. -/
lemma amp_of_neg_base (β t s c : ℝ) (hβ : β ≠ 0) (ht : 0 ≤ t) (hs : 0 ≤ s) (hc : 0 < c) :
    (-(t * s ^ 2 / c ^ 3)) ^ β * Work.FM.Fstar (c ^ (3 * β))
      = 2 * Real.cos (β * Real.pi) * t ^ β * s ^ (2 * β) / (1 + c ^ (3 * β)) ^ 2 := by
  have hb : 0 ≤ t * s ^ 2 / c ^ 3 := div_nonneg (mul_nonneg ht (sq_nonneg s)) (by positivity)
  rw [rpow_neg_base _ β hb hβ]
  rw [show (t * s ^ 2 / c ^ 3) ^ β * Real.cos (β * Real.pi) * Work.FM.Fstar (c ^ (3 * β))
      = Real.cos (β * Real.pi) * ((t * s ^ 2 / c ^ 3) ^ β * Work.FM.Fstar (c ^ (3 * β)))
      by ring,
    amp_of_nonneg_base β t s c ht hs hc]
  ring

/-! ## The angular base `Γ = (x₂ r²/ρ³)^β` -/

/-- **The angular factor is the `β`-th power of the single quotient `x₂ r²/ρ³`.**

For `r(x) > 0` this is the polar dictionary `sin θ = x₂/ρ`, `cos θ = r/ρ`
(`Work.Cyl.sin_thetaP`, `Work.Cyl.cos_thetaP`, with `ρ = ρP (r) (x₂)`); on the axis `r = 0` both
sides are `0^β` (`θ = arctan 0 = 0` on the axis, so `sin θ cos²θ = 0`, and the quotient is
`x₂·0/ρ³ = 0`). -/
lemma Gamma_eq_rpow_base (β : ℝ) (x : R3) :
    Gamma β (Work.Cyl.theta x)
      = (x 2 * (Work.Cyl.radial x) ^ 2 / (Work.Cyl.rho x) ^ 3) ^ β := by
  rcases eq_or_lt_of_le (Work.Cyl.radial_nonneg x) with hr | hr
  · -- axis: `r = 0`, both sides are `0^β`
    have hr0 : Work.Cyl.radial x = 0 := hr.symm
    have hL : Gamma β (Work.Cyl.theta x) = (0:ℝ) ^ β := by
      have hθ : Work.Cyl.theta x = 0 := by
        rw [Work.Cyl.theta, hr0, div_zero, Real.arctan_zero]
      rw [hθ, Gamma]
      simp
    have hR : (x 2 * (Work.Cyl.radial x) ^ 2 / (Work.Cyl.rho x) ^ 3) ^ β = (0:ℝ) ^ β := by
      rw [hr0]; simp
    rw [hL, hR]
  · -- off the axis: the polar dictionary
    have hρP : Work.Cyl.rho x = Work.Cyl.rhoP (Work.Cyl.radial x) (Work.Cyl.axial x) := by
      rw [Work.Cyl.rho, Work.Cyl.rhoP, Work.Cyl.radial_sq]
    have hsin : Real.sin (Work.Cyl.theta x) = x 2 / Work.Cyl.rho x := by
      rw [show Work.Cyl.theta x = Work.Cyl.thetaP (Work.Cyl.radial x) (Work.Cyl.axial x)
            from rfl,
        Work.Cyl.sin_thetaP hr (Work.Cyl.axial x), ← hρP]
      rfl
    have hcos : Real.cos (Work.Cyl.theta x) = Work.Cyl.radial x / Work.Cyl.rho x := by
      rw [show Work.Cyl.theta x = Work.Cyl.thetaP (Work.Cyl.radial x) (Work.Cyl.axial x)
            from rfl,
        Work.Cyl.cos_thetaP hr (Work.Cyl.axial x), ← hρP]
    rw [Gamma, hsin, hcos]
    congr 1
    field_simp

/-! ## The scalar amplitude identity -/

/-- **`Γ(θ x) · F_*(ρ(x)^{3β}) = Aom β x`.**  `Aom β x = cSign β (x₂) · A0 β x` with
`A0 β x = 2 |x₂|^β r^{2β}/(1 + ρ^{3β})²`: on `x₂ ≥ 0` the `cSign` is `1` and the base
`x₂ r²/ρ³ ≥ 0`, so `amp_of_nonneg_base` applies; on `x₂ < 0` the base is
`-(|x₂| r²/ρ³)` and `rpow_neg_base`/`amp_of_neg_base` produce the factor `cos (βπ) = cSign β x₂`.
At the origin (`ρ = 0`) both sides vanish. -/
lemma Gamma_mul_Fstar_eq_Aom (β : ℝ) (hβ : 0 < β) (x : R3) :
    Gamma β (Work.Cyl.theta x) * Work.FM.Fstar (Work.Cyl.rho x ^ (3 * β)) = Aom β x := by
  have hβne : β ≠ 0 := ne_of_gt hβ
  rcases eq_or_lt_of_le (Work.Cyl.rho_nonneg x) with hρ0 | hρ
  · -- `ρ = 0` forces `x = 0`, where `Γ = 0` and `A0 = 0`
    have hρ0' : Work.Cyl.rho x = 0 := hρ0.symm
    have hx0 : x = 0 := by
      by_contra hx
      have hp := (Work.Cyl.rho_pos_iff x).mpr hx
      rw [hρ0'] at hp
      exact lt_irrefl 0 hp
    subst hx0
    have hΓ : Gamma β (Work.Cyl.theta (0:R3)) = 0 := by
      have hθ : Work.Cyl.theta (0:R3) = 0 := by
        rw [Work.Cyl.theta, Work.Cyl.axial]
        simp [Work.Cyl.radial, Work.Cyl.radSq]
      rw [hθ, Gamma]
      simp [Real.zero_rpow hβne]
    have hA : A0 β (0:R3) = 0 :=
      A0_eq_zero_of_radial_eq_zero β hβ (by simp [Work.Cyl.radial, Work.Cyl.radSq])
    rw [hΓ, zero_mul, Aom, cSign, hA, mul_zero]
  · rw [Gamma_eq_rpow_base β x]
    rcases lt_or_ge (x 2) 0 with hx2 | hx2
    · -- `x₂ < 0`: the negative base, `cSign = cos (βπ)`
      have hneg : x 2 * (Work.Cyl.radial x) ^ 2 / (Work.Cyl.rho x) ^ 3
          = -(|x 2| * (Work.Cyl.radial x) ^ 2 / (Work.Cyl.rho x) ^ 3) := by
        rw [abs_of_neg hx2]; ring
      rw [hneg, amp_of_neg_base β (|x 2|) (Work.Cyl.radial x) (Work.Cyl.rho x) hβne
          (abs_nonneg _) (Work.Cyl.radial_nonneg x) hρ,
        Aom, cSign, ite_eq_right (not_le.mpr hx2), A0, abs_of_neg hx2]
      ring
    · -- `x₂ ≥ 0`: the base is non-negative, `cSign = 1`
      rw [amp_of_nonneg_base β (x 2) (Work.Cyl.radial x) (Work.Cyl.rho x) hx2
        (Work.Cyl.radial_nonneg x) hρ,
      Aom, cSign, ite_eq_left hx2, A0, abs_of_nonneg hx2]
      ring

/-! ## The theorem -/

theorem omegaStar_eq_Aom (β : ℝ) (hβ : 0 < β) (x : Work.ConstructionInstance.R3) :
    Work.ConstructionInstance.omegaStar β x
      = Work.ConstructionInstance.Aom β x • Work.Cyl.eTheta x := by
  rw [omegaStar_apply, Gamma_mul_Fstar_eq_Aom β hβ x]

end Work.ConstructionInstance
end
end
-- ===== merged: Submission.Work.ConstructionInstance.psi_sub_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open Set

namespace Work.ConstructionInstance

/-- The normalized vectors of two points of norm `≥ ρ₀ > 0` are at distance at most
`2 ‖x - y‖ / ρ₀` (a generous form of `‖x/‖x‖ - y/‖y‖‖ ≤ 2 ‖x-y‖ / min ‖x‖ ‖y‖`). -/
theorem norm_normalize_sub_le {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {x y : V} {ρ₀ : ℝ} (h₀ : 0 < ρ₀) (hx : ρ₀ ≤ ‖x‖) (hy : ρ₀ ≤ ‖y‖) :
    ‖NormedSpace.normalize x - NormedSpace.normalize y‖ ≤ 2 * dist x y / ρ₀ := by
  have hx0 : 0 < ‖x‖ := lt_of_lt_of_le h₀ hx
  have hy0 : 0 < ‖y‖ := lt_of_lt_of_le h₀ hy
  have hsplit : ‖x‖⁻¹ • x - ‖y‖⁻¹ • y
      = ‖x‖⁻¹ • (x - y) + (‖x‖⁻¹ - ‖y‖⁻¹) • y := by
    rw [smul_sub, sub_smul]; abel
  have h2 : |‖x‖⁻¹ - ‖y‖⁻¹| * ‖y‖ = |‖y‖ - ‖x‖| / ‖x‖ := by
    rw [inv_sub_inv hx0.ne' hy0.ne', abs_div, abs_mul, abs_of_pos hx0, abs_of_pos hy0]
    field_simp
  have h1 : ‖‖x‖⁻¹ • (x - y)‖ = ‖x‖⁻¹ * ‖x - y‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hx0.le)]
  have hterm : ‖(‖x‖⁻¹ - ‖y‖⁻¹) • y‖ = |‖y‖ - ‖x‖| / ‖x‖ := by
    rw [norm_smul, Real.norm_eq_abs, h2]
  calc ‖NormedSpace.normalize x - NormedSpace.normalize y‖
      = ‖‖x‖⁻¹ • x - ‖y‖⁻¹ • y‖ := by rw [NormedSpace.normalize, NormedSpace.normalize]
    _ = ‖‖x‖⁻¹ • (x - y) + (‖x‖⁻¹ - ‖y‖⁻¹) • y‖ := by rw [hsplit]
    _ ≤ ‖‖x‖⁻¹ • (x - y)‖ + ‖(‖x‖⁻¹ - ‖y‖⁻¹) • y‖ := norm_add_le _ _
    _ = ‖x‖⁻¹ * ‖x - y‖ + |‖y‖ - ‖x‖| / ‖x‖ := by rw [h1, hterm]
    _ = ‖x - y‖ / ‖x‖ + |‖y‖ - ‖x‖| / ‖x‖ := by rw [inv_mul_eq_div]
    _ ≤ ‖x - y‖ / ‖x‖ + ‖x - y‖ / ‖x‖ := by
        gcongr
        rw [abs_sub_comm]
        exact abs_norm_sub_norm_le x y
    _ = 2 * ‖x - y‖ / ‖x‖ := by ring
    _ ≤ 2 * ‖x - y‖ / ρ₀ := div_le_div_of_nonneg_left (by positivity) h₀ hx
    _ = 2 * dist x y / ρ₀ := by rw [dist_eq_norm]

/-- **`psi` is `1/ρ`-Lipschitz on `ρ ≥ ρ₀`.**  Chain:
`|psi x - psi y| ≤ angle x y = angle (x/‖x‖) (y/‖y‖) ≤ 2 ‖x/‖x‖ - y/‖y‖‖ ≤ 4 dist x y / ρ₀`,
and `4 ≤ 4 π`. -/
theorem psi_sub_le (x y : R3) {ρ₀ : ℝ} (h₀ : 0 < ρ₀)
    (hx : ρ₀ ≤ Work.Cyl.rho x) (hy : ρ₀ ≤ Work.Cyl.rho y) :
    |psi x - psi y| ≤ 4 * Real.pi * dist x y / ρ₀ := by
  have hρx : 0 < Work.Cyl.rho x := lt_of_lt_of_le h₀ hx
  have hρy : 0 < Work.Cyl.rho y := lt_of_lt_of_le h₀ hy
  have hxn : x ≠ 0 := by
    intro h; rw [h, Work.Cyl.rho_eq_norm, norm_zero] at hρx; exact lt_irrefl 0 hρx
  have hyn : y ≠ 0 := by
    intro h; rw [h, Work.Cyl.rho_eq_norm, norm_zero] at hρy; exact lt_irrefl 0 hρy
  have hA : |psi x - psi y| ≤
      InnerProductGeometry.angle (NormedSpace.normalize x) (NormedSpace.normalize y) := by
    refine (abs_psi_sub_le_angle x y hρx hρy).trans_eq ?_
    rw [InnerProductGeometry.angle_normalize_left, InnerProductGeometry.angle_normalize_right]
  have hB : InnerProductGeometry.angle (NormedSpace.normalize x) (NormedSpace.normalize y)
      ≤ 2 * ‖NormedSpace.normalize x - NormedSpace.normalize y‖ :=
    angle_le_two_mul_norm_sub (NormedSpace.norm_normalize hxn) (NormedSpace.norm_normalize hyn)
  have hC : ‖NormedSpace.normalize x - NormedSpace.normalize y‖ ≤ 2 * dist x y / ρ₀ :=
    norm_normalize_sub_le h₀ (by rw [← Work.Cyl.rho_eq_norm]; exact hx)
      (by rw [← Work.Cyl.rho_eq_norm]; exact hy)
  calc |psi x - psi y|
      ≤ 2 * ‖NormedSpace.normalize x - NormedSpace.normalize y‖ := hA.trans hB
    _ ≤ 2 * (2 * dist x y / ρ₀) := mul_le_mul_of_nonneg_left hC (by norm_num)
    _ = 4 * dist x y / ρ₀ := by ring
    _ ≤ 4 * Real.pi * dist x y / ρ₀ := by
        have h1 : 4 * dist x y / ρ₀ = 4 * (dist x y / ρ₀) := by ring
        have h2 : 4 * Real.pi * dist x y / ρ₀ = (4 * Real.pi) * (dist x y / ρ₀) := by ring
        rw [h1, h2]
        exact mul_le_mul_of_nonneg_right (by linarith [Real.pi_gt_three])
          (div_nonneg dist_nonneg h₀.le)

end Work.ConstructionInstance
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AeCrux.AeVLib.Pullback =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open MeasureTheory Set Filter
open scoped Real Topology ENNReal

namespace Work.FTS.EllipticEst.AeCrux

local notation "Iθ" => Work.Spaces.Iθ
local notation "Iz" => Work.Spaces.Iz

set_option linter.unusedSimpArgs false

theorem contOn_expComp {f : ℝ → ℝ → ℝ}
    (hf : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2)
      ((Set.Ioi (0:ℝ)) ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    ContinuousOn (fun p : ℝ × ℝ => f (Real.exp p.1) p.2)
      ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  have hφ : Continuous (fun p : ℝ × ℝ => (Real.exp p.1, p.2)) := by fun_prop
  have hmap : Set.MapsTo (fun p : ℝ × ℝ => (Real.exp p.1, p.2))
      ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2))
      ((Set.Ioi (0:ℝ)) ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    fun p hp => ⟨Real.exp_pos p.1, hp.2⟩
  exact hf.comp (hφ.continuousOn (s := (Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2))) hmap

/-! ## 7. The pull-back datum and its mixed-derivative identities -/

def pb (u : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun t θ => u (Real.exp t) θ

theorem pb_contDiff {u : ℝ → ℝ → ℝ}
    (h : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (n : ℕ) :
    ContDiffOn ℝ n (Function.uncurry (pb u)) ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  have hφ : ContDiff ℝ n (fun p : ℝ × ℝ => (Real.exp p.1, p.2)) := by fun_prop
  have hmap : Set.MapsTo (fun p : ℝ × ℝ => (Real.exp p.1, p.2))
      ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2))
      ((Set.Ioi (0:ℝ)) ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    fun p hp => ⟨Real.exp_pos p.1, hp.2⟩
  exact (h n).comp hφ.contDiffOn hmap

theorem pb_pz {u : ℝ → ℝ → ℝ} (hSm : Work.FTS.EllipticEst.SmoothOpen u) {t θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.pz (pb u) t θ = Real.exp t * Work.Spaces.pz u (Real.exp t) θ := by
  have hd1 : DifferentiableAt ℝ (fun z : ℝ => u z θ) (Real.exp t) :=
    (hSm.hasDerivAt_slice hθ (Real.exp_pos t)).differentiableAt
  have hd2 : DifferentiableAt ℝ Real.exp t := (Real.hasDerivAt_exp t).differentiableAt
  rw [show Work.Spaces.pz (pb u) t θ
      = deriv ((fun z : ℝ => u z θ) ∘ Real.exp) t from rfl,
    deriv_comp t hd1 hd2, Real.deriv_exp, mul_comm]
  rfl


theorem pb_pthIter {u : ℝ → ℝ → ℝ} (t θ : ℝ) :
    Work.Spaces.pthIter 2 (pb u) t θ = Work.Spaces.pthIter 2 u (Real.exp t) θ := rfl

theorem pb_DzDz {u : ℝ → ℝ → ℝ} (hSm : Work.FTS.EllipticEst.SmoothOpen u) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.Dz (Work.Spaces.Dz u) z θ
      = Work.Spaces.Dz u z θ + z ^ 2 * Work.Spaces.pzIter 2 u z θ := by
  have hd : DifferentiableAt ℝ (fun t : ℝ => Work.Spaces.pz u t θ) z :=
    (hSm.pz.hasDerivAt_slice hθ hz).differentiableAt
  rw [Work.Spaces.Dz, Work.Spaces.pz_Dz_eq (G := u) hd]
  simp only [Work.Spaces.Dz, Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero]
  ring

theorem pb_pz2 {u : ℝ → ℝ → ℝ} (hSm : Work.FTS.EllipticEst.SmoothOpen u) {t θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.pz (Work.Spaces.pz (pb u)) t θ
      = Work.Spaces.Dz (Work.Spaces.Dz u) (Real.exp t) θ := by
  have hid : ∀ s : ℝ, Work.Spaces.pz (pb u) s θ = Work.Spaces.Dz u (Real.exp s) θ := by
    intro s
    rw [pb_pz hSm hθ, Work.Spaces.Dz]
  have hfun : (fun s : ℝ => Work.Spaces.pz (pb u) s θ)
      = (fun s : ℝ => Work.Spaces.Dz u (Real.exp s) θ) := funext hid
  have h1 : deriv (fun s : ℝ => Work.Spaces.Dz u (Real.exp s) θ) t
      = Real.exp t * Work.Spaces.pz (Work.Spaces.Dz u) (Real.exp t) θ := by
    rw [show (fun s : ℝ => Work.Spaces.Dz u (Real.exp s) θ)
        = ((fun z : ℝ => Work.Spaces.Dz u z θ) ∘ Real.exp) from rfl,
      deriv_comp t (hSm.Dz.hasDerivAt_slice hθ (Real.exp_pos t)).differentiableAt
        ((Real.hasDerivAt_exp t).differentiableAt), Real.deriv_exp]
    exact mul_comm _ _
  rw [show Work.Spaces.pz (Work.Spaces.pz (pb u)) t θ
      = deriv (fun s : ℝ => Work.Spaces.pz (pb u) s θ) t from rfl, hfun, h1]
  rfl

theorem pb_pth_pz {u : ℝ → ℝ → ℝ} (hSm : Work.FTS.EllipticEst.SmoothOpen u) {t θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.pth (Work.Spaces.pz (pb u)) t θ
      = Work.Spaces.Dz (Work.Spaces.pth u) (Real.exp t) θ := by
  have hev : (fun θ' : ℝ => Work.Spaces.pz (pb u) t θ')
      =ᶠ[𝓝 θ] (fun θ' : ℝ => Real.exp t * Work.Spaces.pz u (Real.exp t) θ') := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
    rw [pb_pz hSm hθ']
  have hcd : ContDiffAt ℝ 2 (Function.uncurry u) (Real.exp t, θ) :=
    (hSm.forall 2).contDiffAt (IsOpen.mem_nhds Work.FTS.EllipticEst.isOpen_Q0
      (Work.FTS.EllipticEst.mem_Q0.mpr ⟨Real.exp_pos t, hθ.1, hθ.2⟩))
  rw [show Work.Spaces.pth (Work.Spaces.pz (pb u)) t θ
      = deriv (fun θ' : ℝ => Work.Spaces.pz (pb u) t θ') θ from rfl, hev.deriv_eq,
    deriv_const_mul_field]
  rw [show deriv (fun θ' : ℝ => Work.Spaces.pz u (Real.exp t) θ') θ
      = Work.Spaces.pth (Work.Spaces.pz u) (Real.exp t) θ from rfl,
    ← Work.Spaces.pz_pth_comm hcd]
  rfl




end Work.FTS.EllipticEst.AeCrux
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cert.Defs =====
section

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

/-- `angZ θ = sin(2θ)^{2-η}`: the angular factor of a pure `D_z`-summand of the
`ℋ^k`-integrand of a function of the separated form `R(z)·sin 2θ`.

`2 - η = 101/100 > 0`, so `angZ` is continuous on `ℝ` and bounded by `1` on `Iθ`. -/
def angZ (θ : ℝ) : ℝ := (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta)

/-- `angA α i θ = (D_θ^i(sin 2θ))² · sin(2θ)^{-γ}`, `γ = gam α`: the angular factor of a
mixed summand of the `ℋ^k`-integrand of a function of the separated form `R(z)·sin 2θ`.
It is comparable to `angZ`: on `Iθ` it is bounded by the constant `angK i` of
`Work.FTS.EllipticEst.FstarHkOpen` (`angK_bound`), for every `γ ∈ [1,2]`. -/
def angA (α : ℝ) (i : ℕ) (θ : ℝ) : ℝ :=
  (Work.FTS.EllipticEst.sinProf i θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))

/-- **The `ℋ^k`-integrand of a separated function `R(z)·sin 2θ`**, with the radial factor
expressed through the iterates `radIter R i` of `R` (`radIter R i z = (D_z^i R)(z)`):

  `HkExp α k R z θ
     = ∑_{i≤k} (radIter R i z)² w(z)² angZ θ
       + ∑_{i,j≤k} [1 ≤ i, i+j ≤ k] (radIter R j z)² w(z)² angA α i θ`.

`HkIntegrand_radial_sin` identifies it with `HkIntegrand α k (fun z θ => R z * sin 2θ)`. -/
def HkExp (α : ℝ) (k : ℕ) (R : ℝ → ℝ) (z θ : ℝ) : ℝ :=
  (∑ i ∈ Finset.range (k + 1),
      (Work.FTS.EllipticEst.radIter R i z) ^ 2 * (Work.Spaces.w z) ^ 2 * angZ θ)
    + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        if 1 ≤ i ∧ i + j ≤ k then
          (Work.FTS.EllipticEst.radIter R j z) ^ 2 * (Work.Spaces.w z) ^ 2 * angA α i θ
        else 0

end Work.FTS.EllipticEst.Cert
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Endpt.boxIntegrable_pzIter2Psi =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.EllipticEst.Endpt

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-- **Pointwise domination of the `∂_z²Ψ`-term by the `ℋ⁰`-integrand of `z² ∂_z²Ψ`.**

For `z > 0` and `θ ∈ Iθ`,

  `(∂_z²Ψ)² · sin(2θ)^{-η}  ≤  HkIntegrand α 0 (z² ∂_z²Ψ)`,

because `z²·w(z) = (1+z)² ≥ 1`, so multiplying the left-hand side by the square of that
factor can only increase it, and `T1HardWeightAlg` identifies the result with the `i = 0`
summand `(z²·∂_z²Ψ · w(z)/sin(2θ)^{η/2})²` of the level-`0` integrand. -/
theorem pzIter2_sq_mul_sEta_le_HkIntegrand {α : ℝ} {Ψ : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.pzIter 2 Ψ z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      ≤ Work.Spaces.HkIntegrand α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ := by
  set a : ℝ := Work.Spaces.pzIter 2 Ψ z θ with ha
  have hS : 0 ≤ Real.sin (2 * θ) := Work.Spaces.sin_two_nonneg_of_Iθ hθ
  have hnn : 0 ≤ a ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
    mul_nonneg (sq_nonneg a) (Real.rpow_nonneg hS _)
  -- The `i = 0` slot of `HkIntegrand α 0 (z² a)` is `(z²·a·(w/sin(2θ)^{η/2}))²`, and
  -- `T1HardWeightAlg` rewrites that square as `w(z)²·((z²·a)²·sin(2θ)^{-η})`.
  refine le_trans ?_ (Work.Spaces.sq_le_HkIntegrand_z α 0
    (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ 0 (le_refl 0))
  have hkey := (Work.FTS.H2.T1HardWeightAlg α z θ (z ^ 2 * a) 0 (le_of_lt hz) hθ).1
  have hz0 : Work.Spaces.DzIter 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
      = z ^ 2 * a := by simp only [Work.Spaces.DzIter_zero, ha]
  rw [hz0, ← hkey]
  -- `(z²·w(z))²·(a²·sin(2θ)^{-η})` beats `a²·sin(2θ)^{-η}` since `z²·w(z) ≥ 1`.
  have h2 : (Work.Spaces.w z) ^ 2 * ((z ^ 2 * a) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      = (z ^ 2 * Work.Spaces.w z) ^ 2
        * (a ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by ring
  rw [h2]
  have hzw : 1 ≤ z ^ 2 * Work.Spaces.w z := by
    have hzw' : z ^ 2 * Work.Spaces.w z = (1 + z) ^ 2 := by
      rw [Work.Spaces.w, sq]
      field_simp
    rw [hzw']
    nlinarith [hz]
  exact le_mul_of_one_le_left hnn (one_le_pow₀ hzw)

theorem boxIntegrable_pzIter2Psi {α : ℝ} {Ψ : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hmZ : Work.Spaces.HkMem α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) :
    ∀ a b : ℝ, 0 < a → a < b →
      MeasureTheory.IntegrableOn (Function.uncurry (fun s θ : ℝ =>
        (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))))
        (Set.Icc a b ×ˢ Work.Spaces.Iθ) := by
  intro a b ha hab
  have hsub : Set.Icc a b ⊆ Work.Spaces.Iz :=
    fun x hx => Set.mem_Ici.mpr (le_trans (le_of_lt ha) hx.1)
  -- The integrand is continuous on the open quadrant: `∂_z²Ψ` is `C^∞` there and
  -- `sin(2θ) > 0` on the quadrant, so its negative power is continuous.
  have hsinpos : ∀ p ∈ Work.FTS.EllipticEst.Q0, 0 < Real.sin (2 * p.2) := by
    intro p hp
    obtain ⟨-, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hg : ContinuousOn (fun p : ℝ × ℝ =>
      (Work.Spaces.pzIter 2 Ψ p.1 p.2) ^ 2 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)))
      Work.FTS.EllipticEst.Q0 := by
    refine ContinuousOn.mul ?_ ?_
    · exact (((Work.FTS.EllipticEst.smoothOpen_of_forall hsm).pzIter 2).continuousOn).pow 2
    · exact ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
        (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))
  -- Nonnegativity on the box.
  have hnn : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Work.Spaces.Iθ,
      0 ≤ (Work.Spaces.pzIter 2 Ψ z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
    fun z _ θ hθ => mul_nonneg (sq_nonneg _)
      (Real.rpow_nonneg (Work.Spaces.sin_two_nonneg_of_Iθ hθ) _)
  -- Angular slices: dominate by the level-`0` integrand of `z² ∂_z²Ψ`.
  have hsl : ∀ s ∈ Set.Icc a b, Integrable (fun θ : ℝ =>
      (Work.Spaces.pzIter 2 Ψ s θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      (volume.restrict Work.Spaces.Iθ) := by
    intro s hs
    have hspos : 0 < s := lt_of_lt_of_le ha hs.1
    have hsz : s ∈ Work.Spaces.Iz := hsub hs
    refine Integrable.mono' (hmZ.1 s hsz) ?_ ?_
    · exact Work.Spaces.aesm_slice_of_continuousOn_Qd
        (fun p : ℝ × ℝ => (Work.Spaces.pzIter 2 Ψ p.1 p.2) ^ 2
          * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta))) hg hspos
    · filter_upwards [ae_restrict_mem
        (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)] with θ hθ
      rw [Real.norm_of_nonneg (hnn s hs θ hθ)]
      exact pzIter2_sq_mul_sEta_le_HkIntegrand hspos hθ
  -- The iterated `θ`-integral over `[a,b]`: the `θ`-integral of the summand is bounded
  -- pointwise by that of `HkIntegrand α 0 (z² ∂_z²Ψ)`, whose `z`-integral is finite by `hmZ`.
  have hint : Integrable (fun s : ℝ => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.pzIter 2 Ψ s θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      (volume.restrict (Set.Icc a b)) := by
    have hbase : Integrable (fun s : ℝ => ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) s θ)
        (volume.restrict (Set.Icc a b)) :=
      hmZ.2.mono_set hsub
    refine Integrable.mono' hbase ?_ ?_
    · -- Measurability of the iterated integral, by Fubini.
      have hle : (volume.restrict (Set.Icc a b)).prod (volume.restrict Work.Spaces.Iθ)
          ≤ (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ) :=
        Measure.prod_mono (Measure.restrict_mono hsub le_rfl) le_rfl
      have hAEj : AEStronglyMeasurable (fun p : ℝ × ℝ =>
          (Work.Spaces.pzIter 2 Ψ p.1 p.2) ^ 2
            * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)))
          ((volume.restrict (Set.Icc a b)).prod (volume.restrict Work.Spaces.Iθ)) :=
        (Work.Spaces.aesm_of_continuousOn_Qd _ hg).mono_measure hle
      have h2 := hAEj.integral_prod_right' (μ := volume.restrict (Set.Icc a b))
        (ν := volume.restrict Work.Spaces.Iθ)
      simpa only using h2
    · filter_upwards [ae_restrict_mem
        (show MeasurableSet (Set.Icc a b) from measurableSet_Icc)] with s hs
      have hspos : 0 < s := lt_of_lt_of_le ha hs.1
      have hsz : s ∈ Work.Spaces.Iz := hsub hs
      have hnonneg : 0 ≤ ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.pzIter 2 Ψ s θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
        refine MeasureTheory.integral_nonneg_of_ae ?_
        filter_upwards [ae_restrict_mem
          (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)] with θ hθ
        exact hnn s hs θ hθ
      rw [Real.norm_of_nonneg hnonneg]
      refine MeasureTheory.integral_mono_of_nonneg ?_ (hmZ.1 s hsz) ?_
      · filter_upwards [ae_restrict_mem
          (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)] with θ hθ
        exact hnn s hs θ hθ
      · filter_upwards [ae_restrict_mem
          (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)] with θ hθ
        exact pzIter2_sq_mul_sEta_le_HkIntegrand hspos hθ
  exact integrableOn_box_of_slice_of_nonneg ha hab hg hnn hsl hint

end Work.FTS.EllipticEst.Endpt
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Endpt.boxIntegrable_pzPsi =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.EllipticEst.Endpt

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-- **Pointwise domination of the `∂_zΨ`-term by the `ℋ⁰`-integrand of `D_zΨ = z ∂_zΨ`.**

For `z > 0` and `θ ∈ Iθ`,

  `(∂_zΨ)² · sin(2θ)^{-η}  ≤  HkIntegrand α 0 (z ∂_zΨ)`,

because `pz_DzIter_sq_mul_sin_le_term` absorbs the angular weight into
`(z·∂_zΨ · w(z)/sin(2θ)^{η/2})² = (D_zΨ · w/sin(2θ)^{η/2})²` (using `z·w(z) ≥ 1`), which is
the `i = 0` summand of the level-`0` integrand of `D_zΨ`. -/
theorem pz_sq_mul_sEta_le_HkIntegrand_Dz (α : ℝ) {Ψ : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.pz Ψ z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      ≤ Work.Spaces.HkIntegrand α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ) z θ := by
  have h1 := Work.FTS.EllipticEst.pz_DzIter_sq_mul_sin_le_term (F := Ψ) 0 hz hθ
  have h2 := Work.Spaces.sq_le_HkIntegrand_z α 0
    (fun z θ => z * Work.Spaces.pz Ψ z θ) z θ 0 (le_refl 0)
  refine le_trans h1 ?_
  simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.Dz] using h2

theorem boxIntegrable_pzPsi {α : ℝ} {Ψ : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hmU : Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ)) :
    ∀ a b : ℝ, 0 < a → a < b →
      MeasureTheory.IntegrableOn (Function.uncurry (fun s θ : ℝ =>
        (Work.Spaces.pz Ψ s θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))))
        (Set.Icc a b ×ˢ Work.Spaces.Iθ) := by
  intro a b ha hab
  have hsub : Set.Icc a b ⊆ Work.Spaces.Iz :=
    fun x hx => Set.mem_Ici.mpr (le_trans (le_of_lt ha) hx.1)
  -- The integrand is continuous on the open quadrant: `∂_zΨ` is `C^∞` there and
  -- `sin(2θ) > 0` on the quadrant, so its negative power is continuous.
  have hsinpos : ∀ p ∈ Work.FTS.EllipticEst.Q0, 0 < Real.sin (2 * p.2) := by
    intro p hp
    obtain ⟨-, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hg : ContinuousOn (fun p : ℝ × ℝ =>
      (Work.Spaces.pz Ψ p.1 p.2) ^ 2 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)))
      Work.FTS.EllipticEst.Q0 := by
    refine ContinuousOn.mul ?_ ?_
    · exact ((((Work.FTS.EllipticEst.smoothOpen_of_forall hsm).pz).forall 0).continuousOn).pow 2
    · exact ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
        (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))
  -- Nonnegativity on the box.
  have hnn : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Work.Spaces.Iθ,
      0 ≤ (Work.Spaces.pz Ψ z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
    fun z _ θ hθ => mul_nonneg (sq_nonneg _)
      (Real.rpow_nonneg (Work.Spaces.sin_two_nonneg_of_Iθ hθ) _)
  -- Angular slices: dominate by the level-`0` integrand of `D_zΨ`.
  have hsl : ∀ s ∈ Set.Icc a b, Integrable (fun θ : ℝ =>
      (Work.Spaces.pz Ψ s θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      (volume.restrict Work.Spaces.Iθ) := by
    intro s hs
    have hspos : 0 < s := lt_of_lt_of_le ha hs.1
    have hsz : s ∈ Work.Spaces.Iz := hsub hs
    refine Integrable.mono' (hmU.1 s hsz) ?_ ?_
    · exact Work.Spaces.aesm_slice_of_continuousOn_Qd
        (fun p : ℝ × ℝ => (Work.Spaces.pz Ψ p.1 p.2) ^ 2
          * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta))) hg hspos
    · filter_upwards [ae_restrict_mem
        (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)] with θ hθ
      rw [Real.norm_of_nonneg (hnn s hs θ hθ)]
      exact pz_sq_mul_sEta_le_HkIntegrand_Dz α hspos hθ
  -- The iterated `θ`-integral over `[a,b]`: the `θ`-integral of the summand is bounded
  -- pointwise by that of `HkIntegrand α 0 (z ∂_zΨ)`, whose `z`-integral is finite by `hmU`.
  have hint : Integrable (fun s : ℝ => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.pz Ψ s θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      (volume.restrict (Set.Icc a b)) := by
    have hbase : Integrable (fun s : ℝ => ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ) s θ)
        (volume.restrict (Set.Icc a b)) :=
      hmU.2.mono_set hsub
    refine Integrable.mono' hbase ?_ ?_
    · -- Measurability of the iterated integral, by Fubini.
      have hle : (volume.restrict (Set.Icc a b)).prod (volume.restrict Work.Spaces.Iθ)
          ≤ (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ) :=
        Measure.prod_mono (Measure.restrict_mono hsub le_rfl) le_rfl
      have hAEj : AEStronglyMeasurable (fun p : ℝ × ℝ =>
          (Work.Spaces.pz Ψ p.1 p.2) ^ 2
            * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)))
          ((volume.restrict (Set.Icc a b)).prod (volume.restrict Work.Spaces.Iθ)) :=
        (Work.Spaces.aesm_of_continuousOn_Qd _ hg).mono_measure hle
      have h2 := hAEj.integral_prod_right' (μ := volume.restrict (Set.Icc a b))
        (ν := volume.restrict Work.Spaces.Iθ)
      simpa only using h2
    · filter_upwards [ae_restrict_mem
        (show MeasurableSet (Set.Icc a b) from measurableSet_Icc)] with s hs
      have hspos : 0 < s := lt_of_lt_of_le ha hs.1
      have hsz : s ∈ Work.Spaces.Iz := hsub hs
      have hnonneg : 0 ≤ ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.pz Ψ s θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
        refine MeasureTheory.integral_nonneg_of_ae ?_
        filter_upwards [ae_restrict_mem
          (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)] with θ hθ
        exact hnn s hs θ hθ
      rw [Real.norm_of_nonneg hnonneg]
      refine MeasureTheory.integral_mono_of_nonneg ?_ (hmU.1 s hsz) ?_
      · filter_upwards [ae_restrict_mem
          (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)] with θ hθ
        exact hnn s hs θ hθ
      · filter_upwards [ae_restrict_mem
          (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)] with θ hθ
        exact pz_sq_mul_sEta_le_HkIntegrand_Dz α hspos hθ
  exact integrableOn_box_of_slice_of_nonneg ha hab hg hnn hsl hint

end Work.FTS.EllipticEst.Endpt
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.SliceB.pzSecGrowthLoc =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `H2W/SliceB/pzSecGrowthLoc` — the locally uniform pole bound from the *honest second-derivative
slots*

Target of the node `Work.FTS.EllipticEst.H2W.pzIterSliceGrowth3Loc`: for a datum
`WeakPos2 α F Ψ` (`0 < α ≤ 1/4`) and for almost every `z₀ > 0` there are `ε ∈ (0, z₀)` and a
*single* `C ≥ 0` with

  `|D_z^j Ψ(z,θ)| ≤ C·(θ⁻¹ + (π/2-θ)⁻¹)`   for all `j ≤ 3`, `z ∈ (z₀-ε, z₀+ε)`,
  `θ ∈ (0,π/2)`.

This file proves a **second, independent reduction** of that target, resting on the *honest slot*
of the paper's class rather than on the source-mass bound
(`H2W/pzIterSliceGrowth3LocReduction.lean`):

> if the *second angular derivative* of each of the four slices `D_z^mΨ` (`m ≤ 3`) is bounded in
> the `sin(2θ)^{-η}`-weighted `L²`-sense, **locally uniformly in `z`** (`LocSecBound Ψ` below),
> then the target holds.

Two remarks on the shape of the hypothesis.

* The class `WeakPos2` supplies `HkMem α 2 F` for the *source* only; the *left-hand side* slots
  (`∂_θθΦ`, `z²∂_zzΦ`) are not required to be honest.  Adding their honesty is exactly the
  strengthening recommended in `H2W/WeakPureAux/NOTES_weakPzPoleBound.md` §5.
* The **local uniformity** is the essential part of the shape of the hypothesis, and it is *not
  automatic*: Fatou only gives that `z ↦ ∫_θ (∂_θθ(u)(z,·))² σ` is *lower* semicontinuous, and a
  lower semicontinuous function that is finite a.e. need not be locally bounded a.e.
  (The joint — `HkMem`-style — honesty of a slot gives exactly the a.e. finiteness of this
  function, so the *naive* route from a joint honesty hypothesis to the uniform conclusion fails.
  Whether the extra smoothness of the present situation forces local boundedness anyway is
  **not known**; see §2 of `NOTES_pzSecGrowthLoc.md` beside this file, where the natural
  "concentrating spike" constructions are examined and blocked by smoothness.  The locally
  uniform form below is the hypothesis the proof here actually consumes.)

## The mathematics (elementary, and *quantitative*)

For a single slice `u = D_z^mΨ(z,·)` the second-derivative control gives boundedness with an
**explicit constant**.  Writing `B := |u'(π/4)| + ∫_{Iθ}|u''|`, the fundamental theorem of
calculus on `(π/4, θ)` gives `|u'(θ)| ≤ B` and `|u(θ)| ≤ |u(π/4)| + B·(π/2)`; and since
`σ = sin(2θ)^{-η} ≥ 1` on `(0,π/2)`, Cauchy–Schwarz (`H2W.integralAbsLeSqrtMulSqrt`) gives

  `∫_{Iθ}|u''| ≤ √(∫_{Iθ}(u'')²σ)·√(π/2) ≤ K + π/2`  whenever `∫_{Iθ}(u'')²σ ≤ K`.

Hence `|u(θ)| ≤ U + (π/2)·(U + K + π/2)`, where `U` bounds the data
`|u(π/4)| + |u'(π/4)|`.  The data term is *continuous in `z`* (hence locally bounded —
`H2W.exists_sliceData_bound_single`) and `K` is bounded on the `z`-neighbourhood by hypothesis,
so a *single* constant works on `(z₀-ε, z₀+ε)`, which is the target.  This is the same pattern as
the source-mass reduction: the qualitative sibling `Honest.slice_bdd_of_sq_mul_sEta` (an `∃ C`)
is replaced here by a *quantitative* form, which is what makes the constant uniform in `z`. -/

namespace Work.FTS.EllipticEst.H2W.SliceB

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

noncomputable section

/-! ## Facts about `sEta` on the open interval -/


/-- `1 ≤ sEta θ` on the open interval: `sin(2θ) ∈ (0,1]` and `sEta = sin(2θ)^{-η}`. -/
theorem one_le_sEta {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    1 ≤ Work.FTS.EllipticEst.sEta θ := by
  have hpos : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hle : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hη : 0 ≤ Work.Spaces.eta := by rw [Work.Spaces.eta]; norm_num
  have hpow : (Real.sin (2 * θ)) ^ Work.Spaces.eta ≤ 1 := Real.rpow_le_one hpos.le hle hη
  have hpowpos : 0 < (Real.sin (2 * θ)) ^ Work.Spaces.eta := Real.rpow_pos_of_pos hpos _
  rw [Work.FTS.EllipticEst.sEta, Real.rpow_neg hpos.le]
  exact (one_le_inv₀ hpowpos).mpr hpow

/-- The restriction of `volume` to `Iθ` agrees with the restriction to the open interval. -/
theorem restrict_Ioo_eq_restrict_Iθ :
    MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))
      = MeasureTheory.volume.restrict Work.Spaces.Iθ := by
  rw [Work.Spaces.Iθ]
  exact MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc

/-- Almost every point of `Iθ` lies in the open interval: the two endpoints are null. -/
theorem ae_mem_Ioo_Iθ :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
  rw [← restrict_Ioo_eq_restrict_Iθ]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioo

/-- The set integral over `Iθ` is the interval integral over `[0, π/2]`. -/
theorem integral_Iθ_eq_intervalIntegral (h : ℝ → ℝ) :
    (∫ x in Work.Spaces.Iθ, h x) = ∫ x in (0 : ℝ)..(Real.pi / 2), h x := by
  rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : (0 : ℝ) ≤ Real.pi / 2)]

/-! ## The quantitative slice bound from the honest second-derivative slot -/


/-! ## The hypothesis, and the reduction of the target -/



/-! ## The same conclusion from the *first*-derivative slot (a strictly weaker hypothesis)

The second-derivative slot above is the paper's honest slot.  It can be weakened: the fundamental
theorem of calculus anchored at the interior point `π/4` gives `|u θ| ≤ |u(π/4)| + ∫_{Iθ}|u'|`,
and Cauchy–Schwarz bounds `∫_{Iθ}|u'|` by `√(∫_{Iθ}(u')²σ)·√(π/2)`.  So the *first* angular
derivative, in the same `σ`-weighted `L²`-sense, already suffices — and `|u(π/4)|` is part of the
locally bounded data term. -/




end

end Work.FTS.EllipticEst.H2W.SliceB
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.Slot11Src.mixed11_Wt_sq_eq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W.Slot11Src

/-- The first mixed derivative `D_z¹D_θ¹f = D_z(D_θf)` equals `sin(2θ)·∂_θ(D_z f)` on the open
quadrant.  This is the `j = 1` case of the Clairaut identity
`∂_θ(D_z^j f) = D_z^j(∂_θ f)` (`Work.EllipticEst.H2W.pth_DzIter_eqOn_Q0`), transported through
the definition of `D_z`: `D_z(D_θ f) = D_z(sin(2θ)·∂_θf) = sin(2θ)·D_z(∂_θf)` because the
factor `sin(2θ)` does not depend on `z`. -/
lemma mixed_one_one_eq_sin_mul_pth {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    Work.Spaces.mixed 1 1 f z θ
      = Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.DzIter 1 f) z θ := by
  have hQ : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ0, hθ1⟩
  have heq : Work.Spaces.pth (Work.Spaces.DzIter 1 f) z θ
      = Work.Spaces.Dz (Work.Spaces.pth f) z θ := by
    have h := Work.EllipticEst.H2W.pth_DzIter_eqOn_Q0 hf 1 hQ
    simpa [Function.uncurry] using h
  rw [heq]
  show Work.Spaces.Dz (Work.Spaces.Dth f) z θ
      = Real.sin (2 * θ) * Work.Spaces.Dz (Work.Spaces.pth f) z θ
  show z * deriv (fun z' => Work.Spaces.Dth f z' θ) z
      = Real.sin (2 * θ) * (z * deriv (fun z' => Work.Spaces.pth f z' θ) z)
  rw [show (fun z' : ℝ => Work.Spaces.Dth f z' θ)
        = (fun z' : ℝ => Real.sin (2 * θ) * Work.Spaces.pth f z' θ) from rfl,
      deriv_const_mul_field]
  ring

/-- Pure monomial algebra of the `γ`-weight: for `s > 0` and real `γ`,
`(s·A·(w·s^{-γ/2}))² = w²·A²·s^{2-γ}`.  This is the pointwise content of the identity
`(D_zD_θf · W)² = w²·(∂_θD_zf)²·sin(2θ)^{2-γ}`, the two `rpow` exponents `-γ/2` (from the
angular weight `w_θ = sin(2θ)^{-γ/2}`) combining to `-γ`, and the two powers of `sin(2θ)`
combining to `2 - γ`. -/
lemma mul_Wt_sq_key {s A w γ : ℝ} (hs : 0 < s) :
    (s * A * (w * s ^ (-(γ / 2)))) ^ 2 = w ^ 2 * A ^ 2 * s ^ (2 - γ) := by
  have harith1 : -(γ / 2) + -(γ / 2) = -γ := by ring
  have h1 : (s ^ (-(γ / 2))) ^ 2 = s ^ (-γ) := by
    have h : s ^ (-(γ / 2)) * s ^ (-(γ / 2)) = s ^ (-(γ / 2) + -(γ / 2)) :=
      (Real.rpow_add hs _ _).symm
    rw [pow_two, h, harith1]
  have harith2 : (2 : ℝ) - γ = 1 + (1 + -γ) := by ring
  have h2 : s ^ (2 - γ) = s * s * s ^ (-γ) := by
    rw [harith2, Real.rpow_add hs 1 (1 + -γ), Real.rpow_add hs 1 (-γ), Real.rpow_one]
    ring
  have hL : (s * A * (w * s ^ (-(γ / 2)))) ^ 2 = s ^ 2 * A ^ 2 * w ^ 2 * (s ^ (-(γ / 2))) ^ 2 :=
    by ring
  rw [hL, h1, h2]
  ring

theorem mixed11_Wt_sq_eq {α : ℝ} {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (Work.Spaces.mixed 1 1 f z θ * Work.Spaces.Wt α z θ) ^ 2
        = (Work.Spaces.w z) ^ 2 * (Work.Spaces.pth (Work.Spaces.DzIter 1 f) z θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α) := by
  intro z θ hz hθ0 hθ1
  have hs : 0 < Real.sin (2 * θ) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · linarith
    · linarith [Real.pi_pos]
  have hmix := mixed_one_one_eq_sin_mul_pth hf hz hθ0 hθ1
  rw [hmix, Work.Spaces.Wt, Work.Spaces.wTheta]
  exact mul_Wt_sq_key (s := Real.sin (2 * θ))
    (A := Work.Spaces.pth (Work.Spaces.DzIter 1 f) z θ) (w := Work.Spaces.w z)
    (γ := Work.Spaces.gam α) hs

end Work.FTS.EllipticEst.H2W.Slot11Src
end
-- ===== merged: Submission.Work.FTS.EllipticEst.thth.Pre =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Open-quadrant closure lemmas for the `RemovingL12` assembly

Self-contained `SmoothOpen`/`HkMem` closure lemmas (proved from `OpenQDefs`, `LocData` and
`SmoothOpenAdd`) used by the assembly of
`Work.FTS.EllipticEst.theta_theta_removing_fts`.  They are collected in their own module so
that the assembly file stays within the project's per-file limits and shares no module with the
`Fstar_Hk_le` development (whose `integrableOn_zSummand` clashes with `OpenQDefs`).
-/
noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
variable {α : ℝ} {k : ℕ} {f g : ℝ → ℝ → ℝ}

set_option maxHeartbeats 4000000



/-! ## Self-contained open-quadrant closure lemmas

The assembly uses only a handful of `SmoothOpen`/`HkMem` closure facts.  They are proved here
from `OpenQDefs`, `LocData` and `SmoothOpenAdd` so that this file shares no module with the
`Fstar_Hk_le` development, whose declaration `integrabletesOn_zSummand` clashes with the one of
`OpenQDefs`. -/











/-! ## Glue lemmas -/


/-- Congruence of `HkNorm` on the open quadrant. -/
theorem HkNorm_congr_open {f g : ℝ → ℝ → ℝ}
    (h : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → f z θ = g z θ) (α : ℝ) (k : ℕ) :
    Work.Spaces.HkNorm α k f = Work.Spaces.HkNorm α k g := by
  rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm,
    Work.FTS.EllipticEst.HkSq_congr_open α k h]




end Work.FTS.EllipticEst
end
end
-- ===== merged: Submission.Work.FTS.H2.QangAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2

set_option autoImplicit false

/-! ## `Qang` as an interval integral -/

/-- The angular moment `Qang g j z = ∫_θ K(θ)·(D_z^j g)(z,θ) dθ` written as the *interval*
integral over `0..π/2` (the form in which `Fubini`'s theorem for interval integrals is
stated). -/
def QangI (g : ℝ → ℝ → ℝ) (j : ℕ) (z : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..(π / 2), Work.Elliptic.Ktheta θ * Work.Spaces.DzIter j g z θ

/-- `Qang` is the interval integral `QangI`: `Iθ = Icc 0 (π/2)` differs from `Ioc 0 (π/2)`
by the null singleton `{0}`. -/
theorem Qang_eq_intervalIntegral (g : ℝ → ℝ → ℝ) (j : ℕ) (z : ℝ) :
    Work.Elliptic.Qang g j z = QangI g j z := by
  rw [Work.Elliptic.Qang, QangI, Work.Spaces.Iθ,
    MeasureTheory.integral_Icc_eq_integral_Ioc]
  exact (intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ π / 2)).symm

/-! ## The radial weight -/

theorem w_pos {z : ℝ} (hz : 0 < z) : 0 < Work.Spaces.w z := by
  rw [Work.Spaces.w]
  exact div_pos (by positivity) (by positivity)


/-! ## The pointwise domination of a pure `D_z`-iterate by the `H^k`-integrand -/

/-- **A single pure `D_z` slot of the `H^k`-integrand dominates the square of the iterate,
on the open quadrant.**  From `Spaces.sq_le_HkIntegrand_z`

  `(D_z^j g · w/sin(2θ)^{η/2})² ≤ HkIntegrand α k g`

and `sin(2θ)^{η/2} ≤ 1` on `(0,π/2)`, so that the angular weight can be dropped: for
`z > 0` and `0 < θ < π/2`,

  `(D_z^j g z θ)² ≤ HkIntegrand α k g z θ / w(z)²`.

(The statement is *pointwise* on the open quadrant — the endpoints `θ = 0, π/2` are the
null set on which Lean's `sin(2θ)^{η/2} = 0` makes the weighted inequality degenerate.) -/
theorem sq_DzIter_le_HkIntegrand_div_w_sq (α : ℝ) (k : ℕ) (g : ℝ → ℝ → ℝ) (j : ℕ)
    (hj : j ≤ k) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    (Work.Spaces.DzIter j g z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α k g z θ / (Work.Spaces.w z) ^ 2 := by
  have hs : 0 < Real.sin (2 * θ) := sin_two_pos_of_Ioo hθ
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hw : 0 < Work.Spaces.w z := w_pos hz
  have he : 0 < Work.Spaces.eta := Work.Spaces.eta_pos
  set s : ℝ := Real.sin (2 * θ) with hsdef
  have hsnn : 0 ≤ s := le_of_lt hs
  have hpowle : s ^ (Work.Spaces.eta / 2) ≤ 1 := by
    have h1 : s ^ (Work.Spaces.eta / 2) ≤ (1 : ℝ) ^ (Work.Spaces.eta / 2) :=
      Real.rpow_le_rpow hsnn hs1 (by positivity)
    simpa using h1
  have hpowpos : 0 < s ^ (Work.Spaces.eta / 2) := Real.rpow_pos_of_pos hs _
  -- the weighted factor is at least `w z`
  have hfac : (Work.Spaces.w z) ^ 2
      ≤ (Work.Spaces.w z / s ^ (Work.Spaces.eta / 2)) ^ 2 := by
    rw [div_pow, le_div_iff₀ (by positivity)]
    have hsq : (s ^ (Work.Spaces.eta / 2)) ^ 2 ≤ 1 := pow_le_one₀ hpowpos.le hpowle
    nlinarith [hw]
  have hkey := Work.Spaces.sq_le_HkIntegrand_z α k g z θ j hj
  have hkey' : (Work.Spaces.DzIter j g z θ) ^ 2 * (Work.Spaces.w z) ^ 2
      ≤ Work.Spaces.HkIntegrand α k g z θ := by
    have h2 : (Work.Spaces.DzIter j g z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        ≤ (Work.Spaces.DzIter j g z θ
            * (Work.Spaces.w z / s ^ (Work.Spaces.eta / 2))) ^ 2 := by
      nlinarith [hfac, sq_nonneg (Work.Spaces.DzIter j g z θ)]
    exact le_trans h2 hkey
  rw [le_div_iff₀ (by positivity)]
  linarith [hkey']


/-! ## The interior class of `SmoothQuad` data is a `SmoothOpen` datum -/

/-- `SmoothQuad` (smoothness on `z > -1`, `0 < θ < π/2`) restricts to `SmoothOpen`
(smoothness on the open quadrant `z > 0`, `0 < θ < π/2`), which is the class of the
open-quadrant API of `Submission/Work/FTS/EllipticEst/`. -/
theorem SmoothQuad.toSmoothOpen {f : ℝ → ℝ → ℝ} (h : Work.FTS.LocData.SmoothQuad f) :
    Work.FTS.EllipticEst.SmoothOpen f :=
  ContDiffOn.mono h (by
    rintro ⟨z, θ⟩ hp
    obtain ⟨hz, hθ1, hθ2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    have hz' : (-1 : ℝ) < z := by linarith
    exact ⟨hz', ⟨hθ1, hθ2⟩⟩)

/-! ## The primitive formula along a `z`-slice -/

/-- The angular weight is bounded by `3`. -/
theorem abs_Ktheta_le_three (θ : ℝ) : |Work.Elliptic.Ktheta θ| ≤ 3 := by
  have hsin : |Real.sin θ| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_sin θ, Real.sin_le_one θ⟩
  have hcos : |Real.cos θ| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩
  have hcos2 : |Real.cos θ ^ 2| ≤ 1 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [hcos, abs_nonneg (Real.cos θ), sq_abs (Real.cos θ)]
  rw [Work.Elliptic.Ktheta, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
  have hsin' : 0 ≤ |Real.sin θ| := abs_nonneg _
  have hcos2' : 0 ≤ |Real.cos θ ^ 2| := abs_nonneg _
  nlinarith [hsin, hcos2, hsin', hcos2']

/-- **The primitive formula along a `z`-slice.**  For `g` of class `SmoothQuad`, every
`j : ℕ`, every `z, z₀ > 0` and every `θ ∈ (0,π/2)`,

  `D_z^j g z θ - D_z^j g z₀ θ = ∫_{z₀}^{z} D_z^{j+1} g x θ / x dx`. -/
theorem QangSliceFTC {g : ℝ → ℝ → ℝ} (hsm : Work.FTS.LocData.SmoothQuad g) (j : ℕ)
    {z z₀ θ : ℝ} (hz : 0 < z) (hz₀ : 0 < z₀) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Spaces.DzIter j g z θ - Work.Spaces.DzIter j g z₀ θ
      = ∫ x in z₀..z, Work.Spaces.DzIter (j + 1) g x θ / x := by
  have hO : Work.FTS.EllipticEst.SmoothOpen g := SmoothQuad.toSmoothOpen hsm
  -- the derivative of the `θ`-slice of `D_z^j g`, in divided form
  have hderiv : ∀ r : ℝ, r ∈ Set.uIcc z₀ z →
      Work.Spaces.pz (Work.Spaces.DzIter j g) r θ
        = Work.Spaces.DzIter (j + 1) g r θ / r := by
    intro r hr
    have hrpos : 0 < r := lt_of_lt_of_le (lt_min hz₀ hz) hr.1
    have h1 : Work.Spaces.DzIter (j + 1) g r θ
        = r * Work.Spaces.pz (Work.Spaces.DzIter j g) r θ := rfl
    rw [h1, mul_comm r, mul_div_cancel_right₀ _ (ne_of_gt hrpos)]
  rcases le_total z₀ z with hle | hle
  · have hF := Work.FTS.EllipticEst.DzIter_slice_FTC_open hO j hz₀ hle hθ
    rw [hF]
    refine intervalIntegral.integral_congr (a := z₀) (b := z)
      (f := fun r => Work.Spaces.pz (Work.Spaces.DzIter j g) r θ)
      (g := fun r => Work.Spaces.DzIter (j + 1) g r θ / r) (fun r hr => hderiv r hr)
  · have hF := Work.FTS.EllipticEst.DzIter_slice_FTC_open hO j hz hle hθ
    have hF' : Work.Spaces.DzIter j g z θ - Work.Spaces.DzIter j g z₀ θ
        = -∫ r in z..z₀, Work.Spaces.pz (Work.Spaces.DzIter j g) r θ := by
      linarith [hF]
    rw [hF']
    rw [intervalIntegral.integral_congr (a := z) (b := z₀)
      (f := fun r => Work.Spaces.pz (Work.Spaces.DzIter j g) r θ)
      (g := fun r => Work.Spaces.DzIter (j + 1) g r θ / r)
      (fun r hr => hderiv r (by rwa [Set.uIcc_comm]))]
    rw [intervalIntegral.integral_symm, neg_neg]

/-! ## Integrability of the angular slice of `Ktheta · D_z^j g` -/

/-- The pair `(z,θ) ↦ Ktheta θ · D_z^j g z θ` is continuous on the open quadrant. -/
theorem continuousOn_Ktheta_DzIter {g : ℝ → ℝ → ℝ} (hsm : Work.FTS.LocData.SmoothQuad g)
    (j : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2
      * Work.Spaces.DzIter j g p.1 p.2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  have hO : Work.FTS.EllipticEst.SmoothOpen g := SmoothQuad.toSmoothOpen hsm
  have hK : ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    have hfun : (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2)
        = fun p : ℝ × ℝ => 3 * Real.sin p.2 * Real.cos p.2 ^ 2 := by
      funext p; rfl
    rw [hfun]
    exact ((continuous_const.mul (Real.continuous_sin.comp continuous_snd)).mul
      ((Real.continuous_cos.comp continuous_snd).pow 2)).continuousOn
  have hD : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter j g p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := (hO.DzIter j).continuousOn
  refine (hD.mul hK).congr (fun p hp => ?_)
  exact mul_comm _ _

/-- **The angular slice `θ ↦ Ktheta θ · D_z^j g z θ` is integrable on `Iθ`** for `z > 0` and
`j ≤ 4`, in the interior class `SmoothQuad g + HkMem α 4 g`. -/
theorem QangSliceIntegrable {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 4 g)
    {j : ℕ} (hj : j ≤ 4) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => Work.Elliptic.Ktheta θ * Work.Spaces.DzIter j g z θ)
      Work.Spaces.Iθ := by
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => Work.Elliptic.Ktheta θ * Work.Spaces.DzIter j g z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    Work.Spaces.aesm_slice_of_continuousOn_Qd _ (continuousOn_Ktheta_DzIter hsm j) hz
  have hmaj : MeasureTheory.Integrable (fun θ : ℝ =>
      3 * (Work.Spaces.HkIntegrand α 4 g z θ / (Work.Spaces.w z) ^ 2 + 1))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    have h1 : MeasureTheory.Integrable (fun θ : ℝ =>
        Work.Spaces.HkIntegrand α 4 g z θ / (Work.Spaces.w z) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      (hmem.1 z (Set.mem_Ici.mpr hz.le)).div_const _
    have h2 : MeasureTheory.Integrable (fun _ : ℝ => (1 : ℝ))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      MeasureTheory.integrableOn_const (s := Work.Spaces.Iθ) (C := (1 : ℝ)) (by
        rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
    exact (h1.add h2).const_mul 3
  refine MeasureTheory.Integrable.mono' hmaj haesm ?_
  rw [show (MeasureTheory.volume.restrict Work.Spaces.Iθ)
      = MeasureTheory.volume.restrict (Set.Ioo 0 (π / 2)) from by
    rw [Work.Spaces.Iθ]
    exact MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc.symm]
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  have hKh := abs_Ktheta_le_three θ
  have hDh := sq_DzIter_le_HkIntegrand_div_w_sq α 4 g j hj hz hθ
  have hsq : |Work.Spaces.DzIter j g z θ| ≤ (Work.Spaces.DzIter j g z θ) ^ 2 + 1 := by
    nlinarith [sq_nonneg (|Work.Spaces.DzIter j g z θ| - 1),
      sq_abs (Work.Spaces.DzIter j g z θ), abs_nonneg (Work.Spaces.DzIter j g z θ)]
  have hDnn : 0 ≤ |Work.Spaces.DzIter j g z θ| := abs_nonneg _
  have hDh' : |Work.Spaces.DzIter j g z θ|
      ≤ Work.Spaces.HkIntegrand α 4 g z θ / (Work.Spaces.w z) ^ 2 + 1 :=
    le_trans hsq (by linarith)
  calc |Work.Elliptic.Ktheta θ| * |Work.Spaces.DzIter j g z θ|
      ≤ 3 * |Work.Spaces.DzIter j g z θ| := mul_le_mul_of_nonneg_right hKh hDnn
    _ ≤ 3 * (Work.Spaces.HkIntegrand α 4 g z θ / (Work.Spaces.w z) ^ 2 + 1) :=
        mul_le_mul_of_nonneg_left hDh' (by norm_num)

/-! ## An almost-everywhere statement on the interval integral over `0..π/2` -/

/-- A property which holds on the open interval `(0,π/2)` holds almost everywhere on
`uIoc 0 (π/2)` (the two endpoints form a null set). -/
theorem ae_imp_uIoc {p : ℝ → Prop} (h : ∀ θ : ℝ, 0 < θ → θ < π / 2 → p θ) :
    ∀ᵐ θ ∂(MeasureTheory.volume), θ ∈ Set.uIoc 0 (π / 2) → p θ := by
  rw [MeasureTheory.ae_iff]
  refine MeasureTheory.measure_mono_null (t := ({π / 2} : Set ℝ)) ?_
    (MeasureTheory.measure_singleton (π / 2))
  intro θ hθ
  simp only [Set.mem_setOf_eq, not_imp] at hθ
  obtain ⟨hin, hp⟩ := hθ
  rw [Set.uIoc_of_le (by positivity : (0 : ℝ) ≤ π / 2)] at hin
  simp only [Set.mem_Ioc] at hin
  by_contra hc
  simp only [Set.mem_singleton_iff] at hc
  exact hp (h θ hin.1 (lt_of_le_of_ne hin.2 hc))

end Work.FTS.H2
end
end
-- ===== merged: Submission.Work.FTS.LocDataExt.FMJet5 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocDataExt

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The fifth iterate of `D_z` on `FM.Fstar` -/

/-- One more step of the recursion of `Work.FTS.LocData.Phi_div_deriv` (`n = 4`, where the
fifth normalised iterate is not provided by the delivered `PhiR`). -/
theorem Phi_div_deriv_four {z : ℝ} (hz : z ≠ -1) :
    z * deriv (fun w : ℝ => Work.FTS.LocData.PhiR 4 w / (1 + w) ^ 6) z
      = 2 * z * (1 - 57 * z + 302 * z ^ 2 - 302 * z ^ 3 + 57 * z ^ 4 - z ^ 5)
          / (1 + z) ^ 7 := by
  have h1 : (1 : ℝ) + z ≠ 0 := by
    intro h
    exact hz (by linarith)
  have hsub2 : (2 : ℕ) - 1 = 1 := by norm_num
  have hsub3 : (3 : ℕ) - 1 = 2 := by norm_num
  have hsub4 : (4 : ℕ) - 1 = 3 := by norm_num
  have hsub6 : (6 : ℕ) - 1 = 5 := by norm_num
  have hp6 : (1 + z) ^ 6 ≠ 0 := pow_ne_zero 6 h1
  have hp62 : ((1 + z) ^ 6) ^ 2 ≠ 0 := pow_ne_zero 2 hp6
  have hsq : HasDerivAt (fun w : ℝ => w ^ 2) (2 * z) z := by
    have h0 : HasDerivAt ((fun x : ℝ => x) ^ 2) (2 * z) z := by
      refine (((hasDerivAt_id' (x := z)).pow 2).congr_deriv ?_)
      simp [hsub2]
    refine (h0.congr_of_eventuallyEq ?_).congr_deriv ?_
    · filter_upwards with w
      simp
    · ring
  have hcu : HasDerivAt (fun w : ℝ => w ^ 3) (3 * z ^ 2) z := by
    have h0 : HasDerivAt ((fun x : ℝ => x) ^ 3) (3 * z ^ 2) z := by
      refine (((hasDerivAt_id' (x := z)).pow 3).congr_deriv ?_)
      simp [hsub3]
    refine (h0.congr_of_eventuallyEq ?_).congr_deriv ?_
    · filter_upwards with w
      simp
    · ring
  have hqu : HasDerivAt (fun w : ℝ => w ^ 4) (4 * z ^ 3) z := by
    have h0 : HasDerivAt ((fun x : ℝ => x) ^ 4) (4 * z ^ 3) z := by
      refine (((hasDerivAt_id' (x := z)).pow 4).congr_deriv ?_)
      simp [hsub4]
    refine (h0.congr_of_eventuallyEq ?_).congr_deriv ?_
    · filter_upwards with w
      simp
    · ring
  have hquartic : HasDerivAt (fun w : ℝ => 1 - 26 * w + 66 * w ^ 2 - 26 * w ^ 3 + w ^ 4)
      (-26 + 132 * z - 78 * z ^ 2 + 4 * z ^ 3) z := by
    have h26 : HasDerivAt (fun w : ℝ => 26 * w) 26 z :=
      hasDerivAt_const_mul (c := (26 : ℝ)) (x := z)
    have h66 : HasDerivAt (fun w : ℝ => 66 * w ^ 2) (66 * (2 * z)) z :=
      hsq.const_mul (66 : ℝ)
    have h26c : HasDerivAt (fun w : ℝ => 26 * w ^ 3) (26 * (3 * z ^ 2)) z :=
      hcu.const_mul (26 : ℝ)
    have hlin : HasDerivAt (fun w : ℝ => 1 - 26 * w) (0 - 26) z :=
      (hasDerivAt_const (c := (1 : ℝ)) (x := z)).sub h26
    exact ((((hlin.add h66).sub h26c).add hqu)).congr_deriv (by ring)
  have ha : HasDerivAt (fun w : ℝ => 2 * w) 2 z :=
    hasDerivAt_const_mul (c := (2 : ℝ)) (x := z)
  have hnum : HasDerivAt (fun w : ℝ => Work.FTS.LocData.PhiR 4 w)
      (2 * (1 - 26 * z + 66 * z ^ 2 - 26 * z ^ 3 + z ^ 4)
        + 2 * z * (-26 + 132 * z - 78 * z ^ 2 + 4 * z ^ 3)) z := by
    have h0 : HasDerivAt
        ((fun w : ℝ => 2 * w) * (fun w : ℝ => 1 - 26 * w + 66 * w ^ 2 - 26 * w ^ 3 + w ^ 4))
        (2 * (1 - 26 * z + 66 * z ^ 2 - 26 * z ^ 3 + z ^ 4)
          + 2 * z * (-26 + 132 * z - 78 * z ^ 2 + 4 * z ^ 3)) z :=
      ha.mul hquartic
    refine (h0.congr_of_eventuallyEq ?_).congr_deriv ?_
    · filter_upwards with w
      simp only [Pi.mul_apply, Work.FTS.LocData.PhiR_four]
    · ring
  have hden : HasDerivAt (fun w : ℝ => (1 + w) ^ 6) (6 * (1 + z) ^ 5) z := by
    have h0 : HasDerivAt ((fun w : ℝ => 1 + w) ^ 6) (6 * (1 + z) ^ 5) z := by
      refine ((((hasDerivAt_id' (x := z)).const_add (1 : ℝ)).pow 6).congr_deriv ?_)
      simp [hsub6]
    refine (h0.congr_of_eventuallyEq ?_).congr_deriv ?_
    · filter_upwards with w
      simp
    · ring
  have hq : HasDerivAt (fun w : ℝ => Work.FTS.LocData.PhiR 4 w / (1 + w) ^ 6)
      (2 * (1 - 57 * z + 302 * z ^ 2 - 302 * z ^ 3 + 57 * z ^ 4 - z ^ 5)
        / (1 + z) ^ 7) z := by
    refine (hnum.fun_div hden (pow_ne_zero 6 h1)).congr_deriv ?_
    simp only [Work.FTS.LocData.PhiR_four]
    field_simp [h1, hp6, hp62]
    ring
  have hgoal : deriv (fun w : ℝ => Work.FTS.LocData.PhiR 4 w / (1 + w) ^ 6) z
      = 2 * (1 - 57 * z + 302 * z ^ 2 - 302 * z ^ 3 + 57 * z ^ 4 - z ^ 5)
          / (1 + z) ^ 7 := by
    simpa using hq.deriv
  rw [hgoal]
  ring

/-- **The fifth `D_z`-iterate of the plain profile decays like `1/z`.** -/
theorem DzIter_FM_Fstar_five_le {z : ℝ} (hz : 1 ≤ z) (θ : ℝ) :
    |Work.Spaces.DzIter 5 (fun z _ => Work.FM.Fstar z) z θ| ≤ 1440 / z := by
  have hz1 : z ≠ -1 := by linarith
  have hz0 : 0 < z := lt_of_lt_of_le zero_lt_one hz
  have hstep : Work.Spaces.DzIter 5 (fun z _ => Work.FM.Fstar z) z θ
      = z * deriv (fun w : ℝ => Work.FTS.LocData.PhiR 4 w / (1 + w) ^ 6) z := by
    show Work.Spaces.Dz (Work.Spaces.DzIter 4 (fun z _ => Work.FM.Fstar z)) z θ = _
    rw [Work.Spaces.Dz, Work.Spaces.pz]
    congr 1
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards with w
    rw [Work.FTS.LocData.PhiZ_eq 4 (by norm_num) w θ]
    rfl
  rw [hstep, Phi_div_deriv_four hz1]
  have hR5 : |1 - 57 * z + 302 * z ^ 2 - 302 * z ^ 3 + 57 * z ^ 4 - z ^ 5| ≤ 720 * (1 + z) ^ 5 := by
    have hz0' : (0 : ℝ) ≤ z := le_of_lt hz0
    refine abs_le.mpr ⟨?_, ?_⟩
    · nlinarith [hz0', sq_nonneg z, pow_nonneg hz0' 3, pow_nonneg hz0' 4, pow_nonneg hz0' 5]
    · nlinarith [hz0', sq_nonneg z, pow_nonneg hz0' 3, pow_nonneg hz0' 4, pow_nonneg hz0' 5]
  have hnum : |2 * z * (1 - 57 * z + 302 * z ^ 2 - 302 * z ^ 3 + 57 * z ^ 4 - z ^ 5)|
      ≤ 2 * z * (720 * (1 + z) ^ 5) := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos hz0]
    exact mul_le_mul_of_nonneg_left hR5 (by positivity)
  calc |2 * z * (1 - 57 * z + 302 * z ^ 2 - 302 * z ^ 3 + 57 * z ^ 4 - z ^ 5) / (1 + z) ^ 7|
      = |2 * z * (1 - 57 * z + 302 * z ^ 2 - 302 * z ^ 3 + 57 * z ^ 4 - z ^ 5)|
          / (1 + z) ^ 7 := by
        rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (1 + z) ^ 7)]
    _ ≤ (2 * z * (720 * (1 + z) ^ 5)) / (1 + z) ^ 7 :=
        div_le_div_of_nonneg_right hnum (by positivity)
    _ = 1440 * z / (1 + z) ^ 2 := by
        field_simp
        ring
    _ ≤ 1440 / z := by
        rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < (1 + z) ^ 2) hz0]
        nlinarith [hz, sq_nonneg z]

/-! ## The order-`5` jet bound of `FM.Fstar` -/

/-- On `z > 0` the radial weight is at least `1`. -/
theorem one_le_w5 {z : ℝ} (hz : 0 < z) : 1 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w, le_div_iff₀ (by positivity : (0 : ℝ) < z ^ 2)]
  nlinarith

/-- The order-`4` decay of the `D_z`-jets of `FM.Fstar`, from the delivered `Phi_w_le`. -/
theorem DzIter_FM_Fstar_le_four5 {b : ℕ} (hb : b ≤ 4) {z : ℝ} (hz : 1 ≤ z) (θ : ℝ) :
    |Work.Spaces.DzIter b (fun z _ => Work.FM.Fstar z) z θ| ≤ 2 / z := by
  rw [Work.FTS.LocData.PhiZ_eq b hb z θ]
  have hz0 : 0 < z := lt_of_lt_of_le zero_lt_one hz
  have h1 := Work.FTS.LocData.Phi_w_le b hb hz θ
  calc |Work.FTS.LocData.Phi b z θ| = |Work.FTS.LocData.Phi b z θ| * 1 := by ring
    _ ≤ |Work.FTS.LocData.Phi b z θ| * Work.Spaces.w z :=
        mul_le_mul_of_nonneg_left (one_le_w5 hz0) (abs_nonneg _)
    _ = |Work.Spaces.w z * Work.FTS.LocData.Phi b z θ| := by
        rw [abs_mul, abs_of_pos (lt_of_lt_of_le zero_lt_one (one_le_w5 hz0))]
        ring
    _ ≤ 2 / z := h1


end Work.FTS.LocDataExt
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.mixed_sub_eqOn =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty.SlotsLimit

open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false

local notation "Q0" => Work.FTS.EllipticEst.Q0

/-! ## Pointwise linearity of `D_z` and `D_θ` on the open quadrant -/

/-- **`D_z` commutes with subtraction on `Q0`.**  The only content is `deriv_sub` on the
`z`-slice, whose differentiability is `SmoothOpen.hasDerivAt_slice`. -/
lemma Dz_sub_point {A B : ℝ → ℝ → ℝ}
    (hA : Work.FTS.EllipticEst.SmoothOpen A) (hB : Work.FTS.EllipticEst.SmoothOpen B)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Spaces.Dz (fun z θ => A z θ - B z θ) z θ
      = Work.Spaces.Dz A z θ - Work.Spaces.Dz B z θ := by
  have hda := hA.hasDerivAt_slice hθ hz
  have hdb := hB.hasDerivAt_slice hθ hz
  have hfun : (fun z' : ℝ => A z' θ - B z' θ)
      = (fun z' : ℝ => A z' θ) - (fun z' => B z' θ) := rfl
  simp only [Work.Spaces.Dz, Work.Spaces.pz]
  rw [hfun, deriv_sub hda.differentiableAt hdb.differentiableAt]
  ring

/-- **`D_θ` commutes with subtraction on `Q0`.**  Here the differentiability of the two
`θ`-slices comes from `SmoothOpen.curry_θ` (a `C^∞` function has differentiable slices). -/
lemma Dth_sub_point {A B : ℝ → ℝ → ℝ}
    (hA : Work.FTS.EllipticEst.SmoothOpen A) (hB : Work.FTS.EllipticEst.SmoothOpen B)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Spaces.Dth (fun z θ => A z θ - B z θ) z θ
      = Work.Spaces.Dth A z θ - Work.Spaces.Dth B z θ := by
  have hdA : DifferentiableAt ℝ (fun θ' : ℝ => A z θ') θ :=
    ((hA.curry_θ hz).differentiableOn Work.FTS.LocData.smoothOrder_ne_zero).differentiableAt
      (isOpen_Ioo.mem_nhds hθ)
  have hdB : DifferentiableAt ℝ (fun θ' : ℝ => B z θ') θ :=
    ((hB.curry_θ hz).differentiableOn Work.FTS.LocData.smoothOrder_ne_zero).differentiableAt
      (isOpen_Ioo.mem_nhds hθ)
  have hfun : (fun θ' : ℝ => A z θ' - B z θ')
      = (fun θ' : ℝ => A z θ') - (fun θ' => B z θ') := rfl
  simp only [Work.Spaces.Dth, Work.Spaces.pth]
  rw [hfun, deriv_sub hdA hdB]
  ring

/-! ## Congruence on `Q0`: only the values inside the open quadrant matter -/

/-- **`D_z` is local on `Q0`.**  If `A` and `B` agree on the open quadrant then so do `D_z A`
and `D_z B`: at an interior point the `z`-derivative is a germ limit, and a neighbourhood of
the point inside `Q0` is again contained in `Q0`. -/
lemma Dz_congr_Q0 {A B : ℝ → ℝ → ℝ}
    (h : Set.EqOn (Function.uncurry A) (Function.uncurry B) Q0) :
    Set.EqOn (Function.uncurry (Work.Spaces.Dz A))
      (Function.uncurry (Work.Spaces.Dz B)) Q0 := by
  intro p hp
  obtain ⟨hz, hθ0, hθ1⟩ :=
    Work.FTS.EllipticEst.mem_Q0.mp (show (p.1, p.2) ∈ Q0 from hp)
  have hev : (fun z' : ℝ => A z' p.2) =ᶠ[𝓝 p.1] (fun z' : ℝ => B z' p.2) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    exact h (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz', hθ0, hθ1⟩)
  simp only [Function.uncurry, Work.Spaces.Dz, Work.Spaces.pz]
  rw [Filter.EventuallyEq.deriv_eq hev]

/-- **`D_θ` is local on `Q0`.** -/
lemma Dth_congr_Q0 {A B : ℝ → ℝ → ℝ}
    (h : Set.EqOn (Function.uncurry A) (Function.uncurry B) Q0) :
    Set.EqOn (Function.uncurry (Work.Spaces.Dth A))
      (Function.uncurry (Work.Spaces.Dth B)) Q0 := by
  intro p hp
  obtain ⟨hz, hθ0, hθ1⟩ :=
    Work.FTS.EllipticEst.mem_Q0.mp (show (p.1, p.2) ∈ Q0 from hp)
  have hev : (fun θ' : ℝ => A p.1 θ') =ᶠ[𝓝 p.2] (fun θ' : ℝ => B p.1 θ') := by
    filter_upwards [isOpen_Ioo.mem_nhds
      (show p.2 ∈ Set.Ioo 0 (π / 2) from ⟨hθ0, hθ1⟩)] with θ' hθ'
    exact h (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ'.1, hθ'.2⟩)
  simp only [Function.uncurry, Work.Spaces.Dth, Work.Spaces.pth]
  rw [Filter.EventuallyEq.deriv_eq hev]

/-- **The iterates `D_z^n` are local on `Q0`.** -/
lemma DzIter_congr_Q0 {A B : ℝ → ℝ → ℝ}
    (h : Set.EqOn (Function.uncurry A) (Function.uncurry B) Q0) (n : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DzIter n A))
      (Function.uncurry (Work.Spaces.DzIter n B)) Q0 := by
  induction n with
  | zero => simpa using h
  | succ n ih => simpa only [Work.Spaces.DzIter_succ] using Dz_congr_Q0 ih

/-- **The iterates `D_θ^n` are local on `Q0`.** -/
lemma DthIter_congr_Q0 {A B : ℝ → ℝ → ℝ}
    (h : Set.EqOn (Function.uncurry A) (Function.uncurry B) Q0) (n : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DthIter n A))
      (Function.uncurry (Work.Spaces.DthIter n B)) Q0 := by
  induction n with
  | zero => simpa using h
  | succ n ih => simpa only [Work.Spaces.DthIter_succ] using Dth_congr_Q0 ih

/-! ## The `EqOn`-form of the pointwise identities -/

/-- `D_z (A - B) = D_z A - D_z B` on the open quadrant. -/
lemma Dz_sub_eqOn {A B : ℝ → ℝ → ℝ}
    (hA : Work.FTS.EllipticEst.SmoothOpen A) (hB : Work.FTS.EllipticEst.SmoothOpen B) :
    Set.EqOn (Function.uncurry (Work.Spaces.Dz (fun z θ => A z θ - B z θ)))
      (Function.uncurry (fun z θ => Work.Spaces.Dz A z θ - Work.Spaces.Dz B z θ)) Q0 := by
  intro p hp
  obtain ⟨hz, hθ0, hθ1⟩ :=
    Work.FTS.EllipticEst.mem_Q0.mp (show (p.1, p.2) ∈ Q0 from hp)
  exact Dz_sub_point hA hB hz ⟨hθ0, hθ1⟩

/-- `D_θ (A - B) = D_θ A - D_θ B` on the open quadrant. -/
lemma Dth_sub_eqOn {A B : ℝ → ℝ → ℝ}
    (hA : Work.FTS.EllipticEst.SmoothOpen A) (hB : Work.FTS.EllipticEst.SmoothOpen B) :
    Set.EqOn (Function.uncurry (Work.Spaces.Dth (fun z θ => A z θ - B z θ)))
      (Function.uncurry (fun z θ => Work.Spaces.Dth A z θ - Work.Spaces.Dth B z θ)) Q0 := by
  intro p hp
  obtain ⟨hz, hθ0, hθ1⟩ :=
    Work.FTS.EllipticEst.mem_Q0.mp (show (p.1, p.2) ∈ Q0 from hp)
  exact Dth_sub_point hA hB hz ⟨hθ0, hθ1⟩

/-- **`D_z^n` commutes with subtraction on `Q0`.**  Induction on `n`, using that a `D_z`-iterate
of a `SmoothOpen` function is again `SmoothOpen` (so `Dz_sub_point` applies) together with the
localisation `Dz_congr_Q0`, which transfers the induction hypothesis into the argument of `D_z`. -/
lemma DzIter_sub_eqOn {A B : ℝ → ℝ → ℝ}
    (hA : Work.FTS.EllipticEst.SmoothOpen A) (hB : Work.FTS.EllipticEst.SmoothOpen B)
    (n : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DzIter n (fun z θ => A z θ - B z θ)))
      (Function.uncurry (fun z θ => Work.Spaces.DzIter n A z θ
        - Work.Spaces.DzIter n B z θ)) Q0 := by
  induction n with
  | zero => intro p hp; rfl
  | succ n ih =>
    have hcongr := Dz_congr_Q0 ih
    have hsub := Dz_sub_eqOn (hA.DzIter n) (hB.DzIter n)
    intro p hp
    calc Function.uncurry (Work.Spaces.DzIter (n + 1) (fun z θ => A z θ - B z θ)) p
        = Function.uncurry (Work.Spaces.Dz
            (Work.Spaces.DzIter n (fun z θ => A z θ - B z θ))) p := rfl
      _ = Function.uncurry (Work.Spaces.Dz (fun z θ => Work.Spaces.DzIter n A z θ
              - Work.Spaces.DzIter n B z θ)) p := hcongr hp
      _ = Function.uncurry (fun z θ => Work.Spaces.Dz (Work.Spaces.DzIter n A) z θ
              - Work.Spaces.Dz (Work.Spaces.DzIter n B) z θ) p := hsub hp
      _ = Function.uncurry (fun z θ => Work.Spaces.DzIter (n + 1) A z θ
              - Work.Spaces.DzIter (n + 1) B z θ) p := rfl

/-- **`D_θ^n` commutes with subtraction on `Q0`.** -/
lemma DthIter_sub_eqOn {A B : ℝ → ℝ → ℝ}
    (hA : Work.FTS.EllipticEst.SmoothOpen A) (hB : Work.FTS.EllipticEst.SmoothOpen B)
    (n : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DthIter n (fun z θ => A z θ - B z θ)))
      (Function.uncurry (fun z θ => Work.Spaces.DthIter n A z θ
        - Work.Spaces.DthIter n B z θ)) Q0 := by
  induction n with
  | zero => intro p hp; rfl
  | succ n ih =>
    have hcongr := Dth_congr_Q0 ih
    have hsub := Dth_sub_eqOn (hA.DthIter n) (hB.DthIter n)
    intro p hp
    calc Function.uncurry (Work.Spaces.DthIter (n + 1) (fun z θ => A z θ - B z θ)) p
        = Function.uncurry (Work.Spaces.Dth
            (Work.Spaces.DthIter n (fun z θ => A z θ - B z θ))) p := rfl
      _ = Function.uncurry (Work.Spaces.Dth (fun z θ => Work.Spaces.DthIter n A z θ
              - Work.Spaces.DthIter n B z θ)) p := hcongr hp
      _ = Function.uncurry (fun z θ => Work.Spaces.Dth (Work.Spaces.DthIter n A) z θ
              - Work.Spaces.Dth (Work.Spaces.DthIter n B) z θ) p := hsub hp
      _ = Function.uncurry (fun z θ => Work.Spaces.DthIter (n + 1) A z θ
              - Work.Spaces.DthIter (n + 1) B z θ) p := rfl

/-! ## The mixed operator -/

/-- **`mixed j i = D_z^j D_θ^i` commutes with subtraction on `Q0`** (general `SmoothOpen` data;
the requested theorem is the instance `A = f`, `B = g`). -/
lemma mixed_sub_eqOn_of_smoothOpen {A B : ℝ → ℝ → ℝ}
    (hA : Work.FTS.EllipticEst.SmoothOpen A) (hB : Work.FTS.EllipticEst.SmoothOpen B)
    (j i : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.mixed j i (fun z θ => A z θ - B z θ)))
      (Function.uncurry (fun z θ => Work.Spaces.mixed j i A z θ
        - Work.Spaces.mixed j i B z θ)) Q0 := by
  have h2 := DzIter_congr_Q0 (DthIter_sub_eqOn hA hB i) j
  have h3 := DzIter_sub_eqOn (hA.DthIter i) (hB.DthIter i) j
  intro p hp
  calc Function.uncurry (Work.Spaces.mixed j i (fun z θ => A z θ - B z θ)) p
      = Function.uncurry (Work.Spaces.DzIter j
          (Work.Spaces.DthIter i (fun z θ => A z θ - B z θ))) p := rfl
    _ = Function.uncurry (Work.Spaces.DzIter j (fun z θ => Work.Spaces.DthIter i A z θ
            - Work.Spaces.DthIter i B z θ)) p := h2 hp
    _ = Function.uncurry (fun z θ => Work.Spaces.DzIter j (Work.Spaces.DthIter i A) z θ
            - Work.Spaces.DzIter j (Work.Spaces.DthIter i B) z θ) p := h3 hp
    _ = Function.uncurry (fun z θ => Work.Spaces.mixed j i A z θ
            - Work.Spaces.mixed j i B z θ) p := rfl

/-- **The mixed operators are linear on the open quadrant.**  For `f`, `g` smooth on `Q0` and all
`j`, `i`, the operator `mixed j i = D_z^j D_θ^i` commutes with subtraction on `Q0`.  This is the
pointwise identity needed to move between the slot *of the difference* and the *difference of the
slots* (both occur in the limit passage). -/
theorem mixed_sub_eqOn {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (j i : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.mixed j i (fun z θ => f z θ - g z θ)))
      (Function.uncurry (fun z θ => Work.Spaces.mixed j i f z θ
        - Work.Spaces.mixed j i g z θ))
      Work.FTS.EllipticEst.Q0 :=
  mixed_sub_eqOn_of_smoothOpen hf hg j i

end Work.FTS.PhiStar.Honesty.SlotsLimit
end
-- ===== merged: Submission.Work.SolutionDelivery.BKM =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

namespace Work.SolutionDelivery

variable {α : NNReal}

namespace ConstructedSolution

variable (C : ConstructedSolution α)

/-- The vorticity sup-norm function of the constructed solution is continuous on the window. -/
theorem continuousOn_vortLInf :
    ContinuousOn (Work.LWP.vortLInf C.u) (Set.Icc (-1) (C.T + 1)) := by
  have hcont : ContinuousOn (fun p : R3 × ℝ => ‖vorticity (fun y => C.u y p.2) p.1‖)
      (Metric.closedBall 0 C.R ×ˢ Set.Icc (-1) (C.T + 1)) :=
    (Measurable.continuousOn_vorticity_of_contDiffOn (T := C.T) (R := C.R) C.smooth).norm
  have hsup := Sup.continuousOn_ciSup_closedBall
    (F := fun x t => ‖vorticity (fun y => C.u y t) x‖)
    (R := C.R) (a := -1) (b := C.T + 1) C.hR.le hcont
  refine hsup.congr fun t ht => ?_
  exact Sup.ciSup_norm_vorticity_eq_ciSup_closedBall (u := C.u) (R := C.R) (t := t) (M := C.M)
    C.hR.le (fun x => C.vorticity_bounded t ht x) (fun x => C.vorticity_supported t ht x)

/-- **`bkmIntegrable` of `AssemblyInputs`.** -/
theorem bkmIntegrable :
    ∀ t ∈ Set.Ico 0 C.T, IntervalIntegrable (Work.LWP.vortLInf C.u) volume 0 t := by
  intro t ht
  refine (C.continuousOn_vortLInf.mono ?_).intervalIntegrable
  rw [Set.uIcc_of_le ht.1]
  intro s hs
  exact ⟨by linarith [hs.1], by linarith [hs.2, ht.2.le]⟩

/-- **`VortLinfLower` of `AssemblyInputs` (`St5`'s input).** -/
theorem linfLower (hα : 0 < (α : ℝ)) :
    Work.StabilityFar.VortLinfLower C.u C.T (C.c₀ * (α : ℝ) / 2) :=
  Work.StabilityFar.vortLinfLower_of_ansatz (u := C.u) (T := C.T) (c₀ := C.c₀) (α := (α : ℝ))
    (lam := C.lam) C.hlam_pos C.hlam_le C.hc₀ hα (fun t ht => C.bddAbove_vorticity ht)
    (fun t ht => by
      obtain ⟨x, hx⟩ := C.hansatz t ht
      refine ⟨x, ?_⟩
      rw [C.vorticity_eq t (Work.StabilityFar.Ico_subset_window C.hT.le ht) x]
      exact hx)

end ConstructedSolution

end Work.SolutionDelivery
end
end
-- ===== merged: Submission.Work.SolutionDelivery.DatumEuler =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

namespace Work.SolutionDelivery

namespace ConstructedSolution

variable {α : NNReal} (C : ConstructedSolution α)







end ConstructedSolution


end Work.SolutionDelivery
end
end
