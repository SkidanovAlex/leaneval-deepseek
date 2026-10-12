import Mathlib.Tactic.Have
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.BracketCount
import Submission.CentredGap
import Submission.Commons.Analysis.Calculus.contDiff_setIntegral_isCompact
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Steps of the kinetic bridge (SESSION-284 cont.)

FS's `lm:LocKinEn` replaces the full kinetic energy by the sliding sum of localized
operators `𝒯_u` whose main part `𝒯'_u = Q_uχ_u{...}χ_uQ_u` is a pseudo-differential operator
with symbol `[|p|−c]₊²`.  The corpus's D1 word `kinPWord` is the p-space transcription of
`𝒯'_0`; bridging `kinPWord` to the corpus's honest kinetic word
`kinWord N s Φ = Σ_iΣ_k ∫_{abox N s}(∂_{ik}Φ)²` needs, among other things, the two structural
facts proved here:

* **the `Q_i`-projection is free for the `i`-th derivative**: `aQ ℓ i Φ = Φ − aP ℓ i Φ` and
  `aP ℓ i Φ` does not depend on the `i`-th coordinate, hence
  `fderiv ℝ (aQ ℓ i Φ) x (kcDir N i k) = fderiv ℝ Φ x (kcDir N i k)` (`fderiv_aQ_kcDir`);
* consequently the window/`Q`-sandwich `χ_iQ_i F(√−Δ_i) Q_iχ_i ≤ χ_i²·(-Δ_i)` step loses nothing
  at the level of the `i`-th derivative.

The companion facts (the `j ≠ i` case, where the mean-subtraction acts in another slot and the
variance inequality `‖f − P_jf‖² ≤ ‖f‖²` applies, and the windowing
`∫|∇(χu)|² ≤ (1+η)∫χ²|∇u|² + (1+η)η⁻¹∫|∇χ|²u²`) are the next steps of the bridge.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators

namespace Submission
open _root_.BoseGases
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

namespace BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- **Smoothness of the mean**: `aP ℓ i Φ` is smooth when `Φ` is (the integral
`x ↦ ∫_{acube}Φ(x_{i←y})dy` of a smooth integrand over a compact set). -/
lemma contDiff_aP {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin N) {Φ : X N → ℝ}
    (hΦ : ContDiff ℝ ∞ Φ) : ContDiff ℝ ∞ (aP ℓ i Φ) := by
  have hupd : ContDiff ℝ ∞ (fun q : X N × ℝ³ => Function.update q.1 i q.2) := by
    have hEq : (fun q : X N × ℝ³ => Function.update q.1 i q.2)
        = fun q : X N × ℝ³ => q.1 + Function.update (0 : X N) i (q.2 - q.1 i) := by
      funext q
      funext j
      by_cases hj : j = i
      · subst hj
        simp
      · simp [Function.update_of_ne hj]
    rw [hEq]
    have hz : ContDiff ℝ ∞ (fun q : X N × ℝ³ => q.2 - q.1 i) := by fun_prop
    exact contDiff_fst.add ((contDiff_update ∞ (0 : X N) i).comp hz)
  have hF : ContDiff ℝ ∞
      (Function.uncurry (fun (p : X N) (y : ℝ³) =>
        (1 / ℓ ^ 3) * Φ (Function.update p i y))) := by
    have hEq : (Function.uncurry (fun (p : X N) (y : ℝ³) =>
          (1 / ℓ ^ 3) * Φ (Function.update p i y)))
        = fun q : X N × ℝ³ => (1 / ℓ ^ 3) * Φ (Function.update q.1 i q.2) := rfl
    rw [hEq]
    exact (contDiff_const : ContDiff ℝ ∞ (fun _ : X N × ℝ³ => (1 / ℓ ^ 3))).mul
      (hΦ.comp hupd)
  have h := Commons.Analysis.Calculus.contDiff_setIntegral_isCompact (n := (⊤ : ℕ∞))
    (k := acube ℓ) (acube_compact hℓ) hF
  have hEq2 : aP ℓ i Φ
      = fun p : X N => ∫ y in acube ℓ, (1 / ℓ ^ 3) * Φ (Function.update p i y) := by
    funext p
    rw [aP]
    exact (MeasureTheory.integral_const_mul (1 / ℓ ^ 3)
      (fun y : ℝ³ => Φ (Function.update p i y))).symm
  rw [hEq2]
  exact h

/-- **The `i`-directional derivative of `P_i Φ` vanishes**: `P_i Φ` does not depend on the
`i`-th coordinate. -/
lemma fderiv_aP_kcDir {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin N) {Φ : X N → ℝ}
    (hΦ : ContDiff ℝ ∞ Φ) (x : X N) (k : Fin 3) :
    fderiv ℝ (aP ℓ i Φ) x (kcDir N i k) = 0 := by
  -- the curve `t ↦ x + t • kcDir N i k` differs from `x` only in the `i`-th slot
  have hpt : ∀ t : ℝ, (x + t • kcDir N i k)
      = Function.update x i (x i + t • kcStdBasis k) := by
    intro t
    ext j
    by_cases hj : j = i
    · subst hj
      rw [Function.update_self]
      simp [kcDir_apply_eq]
    · rw [Function.update_of_ne hj]
      simp [kcDir_apply_ne i k hj]
  have hconst : (aP ℓ i Φ) ∘ (fun t : ℝ => x + t • kcDir N i k)
      = fun _ : ℝ => aP ℓ i Φ x := by
    funext t
    simp only [Function.comp_apply]
    rw [hpt t]
    exact aP_const_in_coord hℓ i hΦ.continuous x _
  have hg : DifferentiableAt ℝ (aP ℓ i Φ) (x + (0 : ℝ) • kcDir N i k) :=
    (contDiff_aP hℓ i hΦ).differentiable (by norm_num) _
  have hf : DifferentiableAt ℝ (fun t : ℝ => x + t • kcDir N i k) (0 : ℝ) := by fun_prop
  have hcomp := fderiv_comp (x := (0 : ℝ)) (f := fun t : ℝ => x + t • kcDir N i k)
    (g := aP ℓ i Φ) hg hf
  have h0 : fderiv ℝ ((aP ℓ i Φ) ∘ (fun t : ℝ => x + t • kcDir N i k)) (0 : ℝ) = 0 := by
    rw [hconst]
    exact fderiv_const_apply _
  have hzero : (fderiv ℝ (aP ℓ i Φ) (x + (0 : ℝ) • kcDir N i k)).comp
      (fderiv ℝ (fun t : ℝ => x + t • kcDir N i k) (0 : ℝ)) = 0 := by
    rw [← hcomp, h0]
  have h1 := congrArg (fun L : ℝ →L[ℝ] ℝ => L 1) hzero
  simp only [ContinuousLinearMap.comp_apply, zero_apply] at h1
  have hcurve : (fderiv ℝ (fun t : ℝ => x + t • kcDir N i k) (0 : ℝ)) 1 = kcDir N i k := by
    rw [fderiv_apply_one_eq_deriv]
    have hd : HasDerivAt (fun t : ℝ => x + t • kcDir N i k) (kcDir N i k) (0 : ℝ) := by
      have h2 := (hasDerivAt_const (0 : ℝ) x).add
        ((hasDerivAt_id (0 : ℝ)).smul_const (kcDir N i k))
      have hfun : ((fun _ : ℝ => x) + fun y : ℝ => id y • kcDir N i k)
          = (fun t : ℝ => x + t • kcDir N i k) := by
        funext t
        rfl
      have hval : (0 + (1 : ℝ) • kcDir N i k) = kcDir N i k := by simp
      rw [hfun, hval] at h2
      exact h2
    exact hd.deriv
  rw [hcurve] at h1
  have hx0 : x + (0 : ℝ) • kcDir N i k = x := by simp
  rwa [hx0] at h1

/-- **The `i`-directional derivative of `Q_i Φ` is that of `Φ`** (the mean-subtraction is
free for the `i`-th derivative). -/
lemma fderiv_aQ_kcDir {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin N) {Φ : X N → ℝ}
    (hΦ : ContDiff ℝ ∞ Φ) (x : X N) (k : Fin 3) :
    fderiv ℝ (aQ ℓ i Φ) x (kcDir N i k) = fderiv ℝ Φ x (kcDir N i k) := by
  have hdiff : DifferentiableAt ℝ Φ x := hΦ.differentiable (by norm_num) x
  have hdiffP : DifferentiableAt ℝ (aP ℓ i Φ) x :=
    (contDiff_aP hℓ i hΦ).differentiable (by norm_num) x
  have hsub : aQ ℓ i Φ = Φ - aP ℓ i Φ := by
    funext y
    simp [aQ, Pi.sub_apply]
  rw [hsub, fderiv_sub hdiff hdiffP, sub_apply,
    fderiv_aP_kcDir hℓ i hΦ x k, sub_zero]


/-! ## The `j ≠ i` direction: the mean is differentiated under the integral -/

/-- The linear map `v ↦ Function.update v i 0` (the linear part of the `i`-slot update). -/
noncomputable def piUpd (N : ℕ) (i : Fin N) : X N →L[ℝ] X N :=
  ContinuousLinearMap.pi (fun j =>
    if h : j = i then 0 else ContinuousLinearMap.proj (φ := fun _ : Fin N => ℝ³) j)

lemma piUpd_apply (N : ℕ) (i : Fin N) (v : X N) :
    piUpd N i v = Function.update v i 0 := by
  funext j
  rw [piUpd, ContinuousLinearMap.pi_apply]
  by_cases hj : j = i
  · subst hj
    simp
  · simp [hj]

lemma piUpd_kcDir_of_ne {N : ℕ} {i j : Fin N} (hji : j ≠ i) (k : Fin 3) :
    piUpd N i (kcDir N j k) = kcDir N j k := by
  rw [piUpd_apply]
  funext l
  by_cases hl : l = i
  · subst hl
    rw [Function.update_self]
    exact (kcDir_apply_ne j k (Ne.symm hji)).symm
  · rw [Function.update_of_ne hl]

/-- `p ↦ Function.update p i y` is affine with linear part `piUpd N i`. -/
lemma hasFDerivAt_update {N : ℕ} (i : Fin N) (y : ℝ³) (x : X N) :
    HasFDerivAt (fun p : X N => Function.update p i y) (piUpd N i) x := by
  have hpt : ∀ p : X N,
      Function.update p i y = Function.update x i y + piUpd N i (p - x) := by
    intro p
    rw [piUpd_apply]
    funext l
    by_cases hl : l = i
    · subst hl
      simp
    · simp only [Pi.add_apply, Pi.sub_apply, Function.update_of_ne hl]
      abel
  have hfun : (fun p : X N => Function.update p i y)
      = fun p : X N => Function.update x i y + piUpd N i (p - x) := funext hpt
  rw [hfun]
  have h1 : HasFDerivAt (fun p : X N => piUpd N i (p - x)) (piUpd N i) x := by
    have hE : (fun p : X N => piUpd N i (p - x))
        = fun p : X N => piUpd N i p - piUpd N i x := by
      funext p
      rw [map_sub]
    rw [hE]
    exact (piUpd N i).hasFDerivAt.sub_const (piUpd N i x)
  exact h1.const_add (Function.update x i y)

/-- the chain rule through the `i`-slot update -/
lemma fderiv_comp_update {N : ℕ} (i : Fin N) {Φ : X N → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    (x : X N) (y : ℝ³) (v : X N) :
    fderiv ℝ (fun p : X N => Φ (Function.update p i y)) x v
      = fderiv ℝ Φ (Function.update x i y) (piUpd N i v) := by
  have h1 : HasFDerivAt (fun p : X N => Function.update p i y) (piUpd N i) x :=
    hasFDerivAt_update i y x
  have h2 : HasFDerivAt Φ (fderiv ℝ Φ (Function.update x i y)) (Function.update x i y) :=
    (hΦ.differentiable (by norm_num) _).hasFDerivAt
  have hc := (h2.comp x h1).fderiv
  rw [show (fun p : X N => Φ (Function.update p i y))
      = ((Φ : X N → ℝ) ∘ fun p : X N => Function.update p i y) from rfl, hc,
    ContinuousLinearMap.comp_apply]

/-- the `y`-dependence of the differentiation under the integral is continuous -/
lemma continuousOn_fderiv_update {N : ℕ} {ℓ : ℝ} (i : Fin N) {Φ : X N → ℝ}
    (hΦ : ContDiff ℝ ∞ Φ) (x : X N) :
    ContinuousOn (fun y : ℝ³ => fderiv ℝ (fun p : X N => Φ (Function.update p i y)) x)
      (acube ℓ) := by
  have hfder : Continuous (fderiv ℝ Φ) :=
    hΦ.continuous_fderiv (by decide)
  have hy : Continuous (fun y : ℝ³ => Function.update x i y) := by fun_prop
  have h1 : Continuous (fun y : ℝ³ => fderiv ℝ Φ (Function.update x i y)) := hfder.comp hy
  have h2 : Continuous (fun y : ℝ³ =>
      (fderiv ℝ Φ (Function.update x i y)).comp (piUpd N i)) :=
    h1.clm_comp (continuous_const : Continuous (fun _ : ℝ³ => piUpd N i))
  have hEq : (fun y : ℝ³ => fderiv ℝ (fun p : X N => Φ (Function.update p i y)) x)
      = fun y : ℝ³ => (fderiv ℝ Φ (Function.update x i y)).comp (piUpd N i) := by
    funext y
    exact ContinuousLinearMap.ext (fun v => fderiv_comp_update i hΦ x y v)
  rw [hEq]
  exact h2.continuousOn

/-- **The `j ≠ i` directional derivative of `P_i`** (differentiation under the integral of the
fibre mean): `∂_{jk}(P_iΦ)(x) = P_i(∂_{jk}Φ)(x)`. -/
lemma fderiv_aP_kcDir_of_ne {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {i j : Fin N} (hji : j ≠ i)
    {Φ : X N → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (x : X N) (k : Fin 3) :
    fderiv ℝ (aP ℓ i Φ) x (kcDir N j k)
      = aP ℓ i (fun y => fderiv ℝ Φ y (kcDir N j k)) x := by
  have hupd : ContDiff ℝ ∞ (fun q : X N × ℝ³ => Function.update q.1 i q.2) := by
    have hEq : (fun q : X N × ℝ³ => Function.update q.1 i q.2)
        = fun q : X N × ℝ³ => q.1 + Function.update (0 : X N) i (q.2 - q.1 i) := by
      funext q
      funext jj
      by_cases hj : jj = i
      · subst hj
        simp
      · simp [Function.update_of_ne hj]
    rw [hEq]
    have hz : ContDiff ℝ ∞ (fun q : X N × ℝ³ => q.2 - q.1 i) := by fun_prop
    exact contDiff_fst.add ((contDiff_update ∞ (0 : X N) i).comp hz)
  have hF2 : ContDiff ℝ ∞
      (Function.uncurry (fun (p : X N) (y : ℝ³) => Φ (Function.update p i y))) := by
    rw [show (Function.uncurry (fun (p : X N) (y : ℝ³) => Φ (Function.update p i y)))
        = fun q : X N × ℝ³ => Φ (Function.update q.1 i q.2) from rfl]
    exact hΦ.comp hupd
  have hF : ContDiff ℝ ((1 + 1 : ℕ) : ℕ∞)
      (Function.uncurry (fun (p : X N) (y : ℝ³) => Φ (Function.update p i y))) :=
    hF2.of_le (WithTop.coe_le_coe.mpr le_top)
  have hd := Commons.Analysis.Calculus.hasFDerivAt_setIntegral_isCompact (m := 1)
    (k := acube ℓ) (acube_compact hℓ) hF x
  -- integrability of the derivative integrand
  have hInt : MeasureTheory.Integrable
      (fun y : ℝ³ => fderiv ℝ (fun p : X N => Φ (Function.update p i y)) x)
      ((volume : Measure ℝ³).restrict (acube ℓ)) :=
    (continuousOn_fderiv_update i hΦ x).integrableOn_compact (acube_compact hℓ)
  -- `aP` as a constant multiple of the parametric integral
  have heqA : aP ℓ i Φ
      = fun p : X N => (1 / ℓ ^ 3) * ∫ y in acube ℓ, Φ (Function.update p i y) := by
    funext p
    rw [aP]
  have hdiffInt : DifferentiableAt ℝ
      (fun p : X N => ∫ y in acube ℓ, Φ (Function.update p i y)) x :=
    hd.differentiableAt
  have hderiv : fderiv ℝ (aP ℓ i Φ) x
      = (1 / ℓ ^ 3) • (∫ y in acube ℓ,
          fderiv ℝ (fun p : X N => Φ (Function.update p i y)) x) := by
    rw [heqA, fderiv_const_mul hdiffInt]
    rw [hd.fderiv]
  rw [hderiv, smul_apply, ContinuousLinearMap.integral_apply hInt]
  have hcongr : (∫ y in acube ℓ,
        (fderiv ℝ (fun p : X N => Φ (Function.update p i y)) x) (kcDir N j k))
      = ∫ y in acube ℓ, fderiv ℝ Φ (Function.update x i y) (kcDir N j k) := by
    refine integral_congr_ae ?_
    filter_upwards with y
    rw [fderiv_comp_update i hΦ x y (kcDir N j k), piUpd_kcDir_of_ne hji k]
  rw [hcongr, aP, smul_eq_mul]

/-- **The `i`-th kinetic integrand is invariant under `Q_i`**: taking the mean-subtraction
`Q_i` costs NOTHING at the level of the `i`-th derivative (hence of the `i`-th contribution to
`kinWord`). -/
theorem integral_fderiv_aQ_kcDir {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin N) {Φ : X N → ℝ}
    (hΦ : ContDiff ℝ ∞ Φ) (k : Fin 3) :
    (∫ x in abox N ℓ, (fderiv ℝ (aQ ℓ i Φ) x (kcDir N i k)) ^ 2)
      = ∫ x in abox N ℓ, (fderiv ℝ Φ x (kcDir N i k)) ^ 2 := by
  refine integral_congr_ae ?_
  filter_upwards with x
  rw [fderiv_aQ_kcDir hℓ i hΦ x k]

/-! ## The variance inequality and `kinWord (Q_iΦ) ≤ kinWord Φ` -/

/-- the `j ≠ i` directional derivative of `Q_i` is the mean-subtraction of the derivative -/
lemma fderiv_aQ_kcDir_of_ne {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {i j : Fin N} (hji : j ≠ i)
    {Φ : X N → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (x : X N) (k : Fin 3) :
    fderiv ℝ (aQ ℓ i Φ) x (kcDir N j k)
      = aQ ℓ i (fun y => fderiv ℝ Φ y (kcDir N j k)) x := by
  have hsub : aQ ℓ i Φ = Φ - aP ℓ i Φ := by
    funext y
    simp [aQ, Pi.sub_apply]
  have hdiff : DifferentiableAt ℝ Φ x := hΦ.differentiable (by norm_num) x
  have hdiffP : DifferentiableAt ℝ (aP ℓ i Φ) x :=
    (contDiff_aP hℓ i hΦ).differentiable (by norm_num) x
  rw [hsub, fderiv_sub hdiff hdiffP, sub_apply, fderiv_aP_kcDir_of_ne hℓ hji hΦ x k]
  simp only [aQ]


/-! ## The orthogonality of the mean and the fluctuation -/

/-- the `i`-slot update is continuous in the slot variable -/
lemma continuous_update_slot {N : ℕ} (i : Fin N) (x : X N) :
    Continuous (fun y : ℝ³ => Function.update x i y) := by
  refine continuous_pi (fun j => ?_)
  by_cases hj : j = i
  · subst hj
    simp only [Function.update_self]
    exact continuous_id
  · simp only [Function.update_of_ne hj]
    exact continuous_const

/-- **`P_i (Q_i Ψ) = 0`** (pointwise): the fluctuation is mean-free. -/
lemma aP_aQ_eq_zero {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin N) {Ψ : X N → ℝ}
    (hΨc : Continuous Ψ) (x : X N) : aP ℓ i (aQ ℓ i Ψ) x = 0 := by
  have hcont1 : Continuous (fun y : ℝ³ => Ψ (Function.update x i y)) :=
    hΨc.comp (continuous_update_slot i x)
  have hpt : (fun y : ℝ³ => aQ ℓ i Ψ (Function.update x i y))
      = fun y : ℝ³ => Ψ (Function.update x i y) - aP ℓ i Ψ x := by
    funext y
    rw [show aQ ℓ i Ψ (Function.update x i y)
        = Ψ (Function.update x i y) - aP ℓ i Ψ (Function.update x i y) from rfl]
    rw [aP_const_in_coord hℓ i hΨc x y]
  have hcont2 : Continuous (fun y : ℝ³ => Ψ (Function.update x i y) - aP ℓ i Ψ x) :=
    hcont1.sub continuous_const
  have hI1 : MeasureTheory.IntegrableOn (fun y : ℝ³ => Ψ (Function.update x i y))
      (acube ℓ) volume :=
    ContinuousOn.integrableOn_compact (acube_compact hℓ) hcont1.continuousOn
  have hI2 : MeasureTheory.IntegrableOn (fun _ : ℝ³ => aP ℓ i Ψ x) (acube ℓ) volume :=
    ContinuousOn.integrableOn_compact (acube_compact hℓ) continuous_const.continuousOn
  have hval : (∫ y : ℝ³ in acube ℓ, Ψ (Function.update x i y)) = ℓ ^ 3 * aP ℓ i Ψ x := by
    rw [aP, one_div, ← mul_assoc, mul_inv_cancel₀ (by positivity : ℓ ^ 3 ≠ 0), one_mul]
  rw [aP, hpt,
    MeasureTheory.integral_sub hI1 hI2, integral_const_acube ℓ hℓ, hval, one_div]
  ring

/-- **Orthogonality of the mean and the fluctuation**: `∫ (P_iΨ)·(Q_iΨ) = 0`. -/
lemma integral_aP_mul_aQ_eq_zero {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin N) {Ψ : X N → ℝ}
    (hΨc : Continuous Ψ) :
    (∫ x in abox N ℓ, aP ℓ i Ψ x * aQ ℓ i Ψ x) = 0 := by
  have hPc : Continuous (aP ℓ i Ψ) := aP_continuous hℓ i hΨc
  have hQc : Continuous (aQ ℓ i Ψ) := hΨc.sub hPc
  rw [aP_sym_box hℓ i hΨc hQc]
  have hzero : (fun x : X N => Ψ x * aP ℓ i (aQ ℓ i Ψ) x) = fun _ : X N => 0 := by
    funext x
    rw [aP_aQ_eq_zero hℓ i hΨc x, mul_zero]
  rw [hzero, MeasureTheory.integral_zero]

/-- **The mean-subtraction is a contraction**: `∫(Q_iΨ)² ≤ ∫Ψ²` on the centred box (the
`P_i`-orthogonal-projection algebra `∫(Q_iΨ)² = ∫Ψ² − ∫(P_iΨ)²`). -/
lemma integral_aQ_sq_le {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin N) {Ψ : X N → ℝ}
    (hΨc : Continuous Ψ) :
    (∫ x in abox N ℓ, (aQ ℓ i Ψ x) ^ 2) ≤ ∫ x in abox N ℓ, (Ψ x) ^ 2 := by
  have hPc : Continuous (aP ℓ i Ψ) := aP_continuous hℓ i hΨc
  have hQc : Continuous (aQ ℓ i Ψ) := hΨc.sub hPc
  have hInt : ∀ (f : X N → ℝ), Continuous f →
      MeasureTheory.IntegrableOn f (abox N ℓ) volume :=
    fun f hf => ContinuousOn.integrableOn_compact (abox_compact N hℓ) hf.continuousOn
  have hI1 : MeasureTheory.IntegrableOn (fun x : X N => (Ψ x) ^ 2) (abox N ℓ) volume :=
    hInt _ (hΨc.pow 2)
  have hI2 : MeasureTheory.IntegrableOn (fun x : X N => 2 * (aP ℓ i Ψ x * aQ ℓ i Ψ x))
      (abox N ℓ) volume := hInt _ (continuous_const.mul (hPc.mul hQc))
  have hI3 : MeasureTheory.IntegrableOn (fun x : X N => (aP ℓ i Ψ x) ^ 2) (abox N ℓ) volume :=
    hInt _ (hPc.pow 2)
  have hI12 : MeasureTheory.IntegrableOn
      (fun x : X N => (Ψ x) ^ 2 - 2 * (aP ℓ i Ψ x * aQ ℓ i Ψ x)) (abox N ℓ) volume :=
    hI1.sub hI2
  have e1 : (∫ x in abox N ℓ,
        ((Ψ x) ^ 2 - 2 * (aP ℓ i Ψ x * aQ ℓ i Ψ x)) - (aP ℓ i Ψ x) ^ 2)
      = (∫ x in abox N ℓ, ((Ψ x) ^ 2 - 2 * (aP ℓ i Ψ x * aQ ℓ i Ψ x)))
        - (∫ x in abox N ℓ, (aP ℓ i Ψ x) ^ 2) :=
    MeasureTheory.integral_sub hI12 hI3
  have e2 : (∫ x in abox N ℓ, ((Ψ x) ^ 2 - 2 * (aP ℓ i Ψ x * aQ ℓ i Ψ x)))
      = (∫ x in abox N ℓ, (Ψ x) ^ 2)
        - (∫ x in abox N ℓ, 2 * (aP ℓ i Ψ x * aQ ℓ i Ψ x)) :=
    MeasureTheory.integral_sub hI1 hI2
  have e3 : (∫ x in abox N ℓ, 2 * (aP ℓ i Ψ x * aQ ℓ i Ψ x))
      = 2 * (∫ x in abox N ℓ, aP ℓ i Ψ x * aQ ℓ i Ψ x) :=
    MeasureTheory.integral_const_mul 2 _
  have hexp : (∫ x in abox N ℓ, (aQ ℓ i Ψ x) ^ 2)
      = (∫ x in abox N ℓ, (Ψ x) ^ 2)
        - 2 * (∫ x in abox N ℓ, aP ℓ i Ψ x * aQ ℓ i Ψ x)
        - (∫ x in abox N ℓ, (aP ℓ i Ψ x) ^ 2) := by
    rw [show (∫ x in abox N ℓ, (aQ ℓ i Ψ x) ^ 2)
        = ∫ x in abox N ℓ,
            ((Ψ x) ^ 2 - 2 * (aP ℓ i Ψ x * aQ ℓ i Ψ x)) - (aP ℓ i Ψ x) ^ 2 from
      integral_congr_ae (Eventually.of_forall (fun x : X N => by
        simp only []
        rw [show aQ ℓ i Ψ x = Ψ x - aP ℓ i Ψ x from rfl]
        ring))]
    rw [e1, e2, e3]
  have horth := integral_aP_mul_aQ_eq_zero hℓ i hΨc
  have hnn : (0 : ℝ) ≤ ∫ x in abox N ℓ, (aP ℓ i Ψ x) ^ 2 :=
    integral_nonneg (fun x => sq_nonneg _)
  rw [hexp, horth]
  linarith [hnn]

/-- **The `Q_i`-projection does not increase the kinetic word** `kinWord N ℓ Ψ = Σ_{i,k}
∫_{abox N ℓ}(∂_{ik}Ψ)²`: the `i`-th derivatives are UNTOUCHED (`fderiv_aQ_kcDir`) and in every
other slot the mean-subtraction contracts (`integral_aQ_sq_le`). -/
theorem kinWord_aQ_le {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin N) {Φ : X N → ℝ}
    (hΦ : ContDiff ℝ ∞ Φ) :
    kinWord N ℓ (aQ ℓ i Φ) ≤ kinWord N ℓ Φ := by
  unfold kinWord
  refine Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun k _ => ?_))
  by_cases hji : j = i
  · subst j
    exact le_of_eq (integral_fderiv_aQ_kcDir hℓ i hΦ k)
  · have hcont : Continuous (fun y : X N => fderiv ℝ Φ y (kcDir N j k)) :=
      (hΦ.continuous_fderiv (by decide)).clm_apply continuous_const
    have hvar := integral_aQ_sq_le hℓ i (Ψ := fun y : X N => fderiv ℝ Φ y (kcDir N j k)) hcont
    have hcongr : (∫ x in abox N ℓ, (fderiv ℝ (aQ ℓ i Φ) x (kcDir N j k)) ^ 2)
        = ∫ x in abox N ℓ, (aQ ℓ i (fun y => fderiv ℝ Φ y (kcDir N j k)) x) ^ 2 := by
      refine integral_congr_ae (Eventually.of_forall (fun x : X N => ?_))
      simp only []
      rw [fderiv_aQ_kcDir_of_ne hℓ hji hΦ x k]
    rw [hcongr]
    exact hvar

/-! ## Windowing: the Leibniz + Cauchy–Schwarz step of the kinetic bridge -/

/-- **The pointwise windowing bound**: for a product `χ·u` the `k`-th coordinate derivative
satisfies `(∂_k(χu))² ≤ 2χ²(∂_ku)² + 2(∂_kχ)²u²` (Leibniz + `(a+b)² ≤ 2a²+2b²`). -/
lemma fderiv_mul_coord_sq_le {χ u : ℝ³ → ℝ} {x : ℝ³}
    (hχ : DifferentiableAt ℝ χ x) (hu : DifferentiableAt ℝ u x) (k : Fin 3) :
    (fderiv ℝ (fun y => χ y * u y) x (kcStdBasis k)) ^ 2
      ≤ 2 * (χ x) ^ 2 * (fderiv ℝ u x (kcStdBasis k)) ^ 2
        + 2 * (fderiv ℝ χ x (kcStdBasis k)) ^ 2 * (u x) ^ 2 := by
  have hd : fderiv ℝ (fun y => χ y * u y) x (kcStdBasis k)
      = χ x * fderiv ℝ u x (kcStdBasis k) + u x * fderiv ℝ χ x (kcStdBasis k) := by
    have h1 : fderiv ℝ (fun y => χ y * u y) x = fderiv ℝ (χ * u) x := rfl
    rw [h1, fderiv_mul hχ hu, add_apply, smul_apply, smul_apply, smul_eq_mul, smul_eq_mul]
  rw [hd]
  nlinarith [sq_nonneg (χ x * fderiv ℝ u x (kcStdBasis k)
      - u x * fderiv ℝ χ x (kcStdBasis k))]

end BoseGases
end Submission
