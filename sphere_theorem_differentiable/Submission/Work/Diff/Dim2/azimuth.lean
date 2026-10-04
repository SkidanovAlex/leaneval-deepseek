import Mathlib
import Submission.Work.Diff.Dim2.Lib
import Submission.Work.Diff.Dim2.Azim
import Submission.Work.Diff.Dim2.Ambient
import Submission.Work.Diff.Dim2.twist_smooth
import Submission.Work.Diff.Dim2.PhaseAux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace Work.Diff.Dim2

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter Submission.Geodesic

/-! ## Elementary facts about `circPt`, `rotE`, `argE`

These are the circle/argument facts used by the azimuth construction. -/

section CircleFacts

/-- `toC (circPt t) = exp (t * I)`. -/
lemma toC_circPt_exp (t : ℝ) :
    toC (circPt t) = Complex.exp ((t : ℂ) * Complex.I) := by
  rw [← ofC_exp_I t, toC_ofC]

/-- **Injectivity of `toC`** (the canonical identification `ℝ² ≃ ℂ`). -/
lemma toC_injective : Function.Injective (toC : EuclideanSpace ℝ (Fin 2) → ℂ) := by
  intro x y h
  rw [← ofC_toC x, ← ofC_toC y, h]

/-- `circPt` is smooth. -/
lemma contDiff_circPt : ContDiff ℝ (⊤ : ℕ∞) circPt := by
  have h : ContDiff ℝ (⊤ : ℕ∞)
      (fun t : ℝ => (![Real.cos t, Real.sin t] : Fin 2 → ℝ)) := by
    rw [contDiff_pi]
    intro i
    fin_cases i <;> simp [Real.contDiff_cos, Real.contDiff_sin]
  exact (EuclideanSpace.equiv (Fin 2) ℝ).symm.contDiff.comp h

/-- `toC` is smooth. -/
lemma contDiff_toC : ContDiff ℝ (⊤ : ℕ∞) toC := by
  have h : toC = fun z : EuclideanSpace ℝ (Fin 2) =>
      (((EuclideanSpace.equiv (Fin 2) ℝ) z) 0 : ℂ)
        + (((EuclideanSpace.equiv (Fin 2) ℝ) z) 1 : ℂ) * Complex.I := by
    funext z
    apply Complex.ext <;> simp [toC]
  rw [h]
  have h0 : ContDiff ℝ (⊤ : ℕ∞) (fun z : EuclideanSpace ℝ (Fin 2) =>
      (((EuclideanSpace.equiv (Fin 2) ℝ) z) 0 : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (((ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : Fin 2 => ℝ) (0 : Fin 2))).comp
      ((EuclideanSpace.equiv (Fin 2) ℝ) : EuclideanSpace ℝ (Fin 2) →L[ℝ] (Fin 2 → ℝ))).contDiff
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun z : EuclideanSpace ℝ (Fin 2) =>
      (((EuclideanSpace.equiv (Fin 2) ℝ) z) 1 : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (((ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : Fin 2 => ℝ) (1 : Fin 2))).comp
      ((EuclideanSpace.equiv (Fin 2) ℝ) : EuclideanSpace ℝ (Fin 2) →L[ℝ] (Fin 2 → ℝ))).contDiff
  exact h0.add (h1.mul contDiff_const)

/-- **`circPt` has derivative the quarter turn of its value.** -/
lemma hasDerivAt_circPt (t : ℝ) : HasDerivAt circPt (rot90 (circPt t)) t := by
  have h1 : HasDerivAt (fun s : ℝ => (![Real.cos s, Real.sin s] : Fin 2 → ℝ))
      (![-Real.sin t, Real.cos t]) t := by
    rw [hasDerivAt_pi]
    intro i
    fin_cases i
    · simpa using Real.hasDerivAt_cos t
    · simpa using Real.hasDerivAt_sin t
  have h2 : HasDerivAt
      (fun s : ℝ =>
        (EuclideanSpace.equiv (Fin 2) ℝ).symm (![Real.cos s, Real.sin s] : Fin 2 → ℝ))
      ((EuclideanSpace.equiv (Fin 2) ℝ).symm (![-Real.sin t, Real.cos t] : Fin 2 → ℝ)) t :=
    ((EuclideanSpace.equiv (Fin 2) ℝ).symm :
        (Fin 2 → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 2)).hasFDerivAt.comp_hasDerivAt t h1
  have hval : (EuclideanSpace.equiv (Fin 2) ℝ).symm (![-Real.sin t, Real.cos t] : Fin 2 → ℝ)
      = rot90 (circPt t) := by
    rw [rot90]
    congr 1
  rw [hval] at h2
  exact h2

/-- `toC` commutes with negation. -/
lemma toC_neg (z : EuclideanSpace ℝ (Fin 2)) : toC (-z) = -toC z := by
  apply Complex.ext <;> simp [toC]

/-- `circPt (a + b) = rotE b (circPt a)` (the angle shifts by `b`). -/
lemma circPt_add (a b : ℝ) : circPt (a + b) = rotE b (circPt a) := by
  rw [← ofC_exp_I (a + b), ← ofC_exp_I a, rotE,
    show ((a + b : ℝ) : ℂ) * Complex.I = (b : ℂ) * Complex.I + (a : ℂ) * Complex.I by
      push_cast; ring,
    Complex.exp_add]
  simp

/-- `circPt (a + π) = - circPt a`. -/
lemma circPt_add_pi (a : ℝ) : circPt (a + Real.pi) = -circPt a := by
  apply toC_injective
  rw [toC_circPt_exp, toC_neg, toC_circPt_exp,
    show ((a + Real.pi : ℝ) : ℂ) * Complex.I
      = (a : ℂ) * Complex.I + ((Real.pi : ℂ) * Complex.I) by push_cast; ring,
    Complex.exp_add, Complex.exp_pi_mul_I]
  ring

/-- `rotE ((k : ℝ) * 2π) = id`. -/
lemma rotE_int_mul_two_pi (k : ℤ) (z : EuclideanSpace ℝ (Fin 2)) :
    rotE ((k : ℝ) * (2 * Real.pi)) z = z := by
  rw [rotE,
    show (((k : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I
      = (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by push_cast; ring,
    Complex.exp_int_mul_two_pi_mul_I k, one_mul, ofC_toC]

/-- `rotE t (circPt a) = circPt (a + t)`. -/
lemma rotE_circPt (t a : ℝ) : rotE t (circPt a) = circPt (a + t) :=
  (circPt_add a t).symm

/-- `circPt` is `2π`-periodic (integer multiples). -/
lemma circPt_periodic (a : ℝ) (k : ℤ) :
    circPt (a + (k : ℝ) * (2 * Real.pi)) = circPt a := by
  rw [circPt_add a _, rotE_int_mul_two_pi]

/-- **`circPt ∘ argE` is the identity on the unit circle.** -/
lemma circPt_argE {z : EuclideanSpace ℝ (Fin 2)} (hz : ‖z‖ = 1) : circPt (argE z) = z := by
  have hnorm : ‖toC z‖ = 1 := by rw [norm_toC, hz]
  have hexp : Complex.exp ((argE z : ℂ) * Complex.I) = toC z := by
    change Complex.exp (((toC z).arg : ℂ) * Complex.I) = toC z
    have h := Complex.norm_mul_exp_arg_mul_I (toC z)
    rw [hnorm] at h
    simpa only [Complex.ofReal_one, one_mul] using h
  rw [← ofC_exp_I (argE z), hexp, ofC_toC]

/-- A unit vector of `ℝ²` whose `toC`-image is not `-1` lies in the slit plane. -/
lemma slitPlane_toC {z : EuclideanSpace ℝ (Fin 2)} (hz : ‖z‖ = 1) (h : toC z ≠ -1) :
    toC z ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_contra hcon
  push Not at hcon
  obtain ⟨hre, him⟩ := hcon
  have hnorm : ‖toC z‖ = 1 := by rw [norm_toC, hz]
  have hsq : (toC z).re ^ 2 + (toC z).im ^ 2 = 1 := by
    have h2 := Complex.sq_norm (toC z)
    rw [hnorm] at h2
    norm_num at h2
    rw [Complex.normSq_apply] at h2
    linarith
  rw [him] at hsq
  have hre' : (toC z).re = -1 := by nlinarith [sq_nonneg ((toC z).re + 1)]
  apply h
  apply Complex.ext
  · simpa using hre'
  · simpa using him

/-- `argE` is smooth off the branch cut. -/
lemma contDiffAt_argE {z : EuclideanSpace ℝ (Fin 2)}
    (hz : toC z ∈ Complex.slitPlane) : ContDiffAt ℝ (⊤ : ℕ∞) argE z := by
  change ContDiffAt ℝ (⊤ : ℕ∞) (fun v => Complex.arg (toC v)) z
  have hlog : ContDiffAt ℝ (⊤ : ℕ∞) Complex.log (toC z) :=
    (Complex.contDiffAt_log hz).restrict_scalars ℝ
  have h3 : ContDiffAt ℝ (⊤ : ℕ∞) (Complex.imCLM ∘ Complex.log) (toC z) :=
    ContDiffAt.comp (toC z) Complex.imCLM.contDiff.contDiffAt hlog
  have h4 : ContDiffAt ℝ (⊤ : ℕ∞) (fun w : ℂ => (Complex.log w).im) (toC z) := by
    simpa only [Function.comp_def, Complex.imCLM_apply] using h3
  rw [show (fun w : ℂ => (Complex.log w).im) = Complex.arg from
    funext fun w => Complex.log_im w] at h4
  exact ContDiffAt.comp z h4 contDiff_toC.contDiffAt

/-- The derivative of `Real.smoothTransition` vanishes on `(-∞,0] ∪ [1,∞)`. -/
lemma deriv_smoothTransition_eq_zero (t : ℝ) (h : t ≤ 0 ∨ 1 ≤ t) :
    deriv Real.smoothTransition t = 0 := by
  have hcont : Continuous (deriv Real.smoothTransition) :=
    ContDiff.continuous_deriv_one (Real.smoothTransition.contDiff (n := (1 : ℕ∞)))
  have hnone : ∀ s : ℝ, s < 0 → deriv Real.smoothTransition s = 0 := by
    intro s hs
    have hc : Real.smoothTransition =ᶠ[𝓝 s] fun _ : ℝ => (0 : ℝ) := by
      filter_upwards [isOpen_Iio.mem_nhds hs] with y hy
      exact Real.smoothTransition.zero_of_nonpos (le_of_lt hy)
    rw [hc.deriv_eq, deriv_const]
  have hone : ∀ s : ℝ, 1 < s → deriv Real.smoothTransition s = 0 := by
    intro s hs
    have hc : Real.smoothTransition =ᶠ[𝓝 s] fun _ : ℝ => (1 : ℝ) := by
      filter_upwards [isOpen_Ioi.mem_nhds hs] with y hy
      exact Real.smoothTransition.one_of_one_le (le_of_lt hy)
    rw [hc.deriv_eq, deriv_const]
  rcases h with h | h
  · rcases lt_or_eq_of_le h with h' | h'
    · exact hnone t h'
    · subst h'
      have h1 : Filter.Tendsto (deriv Real.smoothTransition) (𝓝[<] (0 : ℝ))
          (𝓝 (deriv Real.smoothTransition 0)) :=
        hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      have h2 : Filter.Tendsto (deriv Real.smoothTransition) (𝓝[<] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
        apply Filter.Tendsto.congr' _ tendsto_const_nhds
        filter_upwards [self_mem_nhdsWithin] with s hs
        exact (hnone s hs).symm
      exact tendsto_nhds_unique h1 h2
  · rcases lt_or_eq_of_le h with h' | h'
    · exact hone t h'
    · subst h'
      have h1 : Filter.Tendsto (deriv Real.smoothTransition) (𝓝[>] (1 : ℝ))
          (𝓝 (deriv Real.smoothTransition 1)) :=
        hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      have h2 : Filter.Tendsto (deriv Real.smoothTransition) (𝓝[>] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
        apply Filter.Tendsto.congr' _ tendsto_const_nhds
        filter_upwards [self_mem_nhdsWithin] with s hs
        exact (hone s hs).symm
      exact tendsto_nhds_unique h1 h2

end CircleFacts

/-! ## The angular form of a `circPt`-lifted map -/

section ManifoldFacts

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/- **The derivative of `circPt` at `t`**, applied to a tangent vector. -/
set_option backward.isDefEq.respectTransparency.types false in
lemma mfderiv_circPt_apply (t : ℝ) (w : TangentSpace 𝓘(ℝ,ℝ) t) :
    (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) circPt t) w
      = (NormedSpace.fromTangentSpace t w : ℝ) • rot90 (circPt t) := by
  have h := (hasDerivAt_circPt t).hasFDerivAt.hasMFDerivAt
  rw [h.mfderiv]
  change (ContinuousLinearMap.toSpanSingleton ℝ (rot90 (circPt t)))
      (NormedSpace.fromTangentSpace t w : ℝ) = _
  rw [ContinuousLinearMap.toSpanSingleton_apply]

/- **Chain rule for `x ↦ circPt (f x)`** (pointwise form, model-space flavour). -/
set_option backward.isDefEq.respectTransparency.types false in
lemma mvfderiv_circPt_comp_apply {f : M → ℝ} {x : M} (hf : MDifferentiableAt I 𝓘(ℝ,ℝ) f x)
    (v : TangentSpace I x) :
    mvfderiv I (fun y => circPt (f y)) x v
      = (NormedSpace.fromTangentSpace (f x) (mfderiv I 𝓘(ℝ,ℝ) f x v)) •
          rot90 (circPt (f x)) := by
  have hg : MDifferentiableAt 𝓘(ℝ,ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) circPt (f x) :=
    mdifferentiableAt_iff_differentiableAt.mpr
      (hasDerivAt_circPt (f x)).hasFDerivAt.differentiableAt
  have h2 : (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) (fun y => circPt (f y)) x) v
      = (NormedSpace.fromTangentSpace (f x) ((mfderiv I 𝓘(ℝ,ℝ) f x) v)) •
          rot90 (circPt (f x)) := by
    erw [show (fun y => circPt (f y)) = circPt ∘ f from rfl, mfderiv_comp_apply x hg hf v,
      mfderiv_circPt_apply (f x) ((mfderiv I 𝓘(ℝ,ℝ) f x) v)]
  rw [show mvfderiv I (fun y => circPt (f y)) x v
      = NormedSpace.fromTangentSpace (circPt (f x))
          ((mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) (fun y => circPt (f y)) x) v) from rfl,
    h2]
  rfl

/- **The angular form of a `circPt`-lifted map is the derivative of the angle** (pointwise).
If `w = circPt ∘ ψ` near `x` (with `ψ` smooth at `x`) and `‖w x‖ = 1`, then the angular form of `w`
at `x` is the differential of `ψ`. -/
set_option backward.isDefEq.respectTransparency.types false in
lemma angForm_apply_eq_mvfderiv_of_circPt {ψ : M → ℝ} {x : M}
    (hψ : ContMDiffAt I 𝓘(ℝ,ℝ) (⊤ : ℕ∞) ψ x)
    {w : M → EuclideanSpace ℝ (Fin 2)}
    (hw : w =ᶠ[𝓝 x] fun y => circPt (ψ y)) (hw1 : ‖w x‖ = 1) (v : TangentSpace I x) :
    angForm (Az := w) x v = mvfderiv I ψ x v := by
  have hψd : MDifferentiableAt I 𝓘(ℝ,ℝ) ψ x := hψ.mdifferentiableAt (by simp)
  have hg : MDifferentiableAt 𝓘(ℝ,ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) circPt (ψ x) :=
    mdifferentiableAt_iff_differentiableAt.mpr
      (hasDerivAt_circPt (ψ x)).hasFDerivAt.differentiableAt
  have hcd : MDifferentiableAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))
      (fun y => circPt (ψ y)) x := hg.comp x hψd
  have hwx : w x = circPt (ψ x) := hw.eq_of_nhds
  have hw' : HasMFDerivAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) w x
      (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) (fun y => circPt (ψ y)) x) :=
    hcd.hasMFDerivAt.congr_of_eventuallyEq_abuse hw
  have h2 : (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) (fun y => circPt (ψ y)) x) v
      = (NormedSpace.fromTangentSpace (ψ x) ((mfderiv I 𝓘(ℝ,ℝ) ψ x) v)) •
          rot90 (circPt (ψ x)) := by
    erw [show (fun y => circPt (ψ y)) = circPt ∘ ψ from rfl, mfderiv_comp_apply x hg hψd v,
      mfderiv_circPt_apply (ψ x) ((mfderiv I 𝓘(ℝ,ℝ) ψ x) v)]
  have step1 : angForm (Az := w) x v
      = Inner.inner ℝ (rot90 (circPt (ψ x)))
          ((mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) (fun y => circPt (ψ y)) x) v) := by
    rw [show angForm (Az := w) x v
        = Inner.inner ℝ (rot90 (w x))
            ((mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) w x) v) from rfl,
      congrArg (fun L => L v) hw'.mfderiv, hwx]
  rw [step1, h2, real_inner_smul_right, real_inner_self_eq_norm_sq, norm_rot90, norm_circPt,
    show mvfderiv I ψ x v = NormedSpace.fromTangentSpace (ψ x) ((mfderiv% ψ x) v) from rfl,
    one_pow, mul_one]



/- **The angular form vanishes on the kernel of the derivative.** -/
set_option backward.isDefEq.respectTransparency.types false in
lemma angForm_eq_zero_of_mvfderiv_eq_zero {Az : M → EuclideanSpace ℝ (Fin 2)} {x : M}
    {v : TangentSpace I x} (h : mvfderiv I Az x v = 0) :
    angForm (Az := Az) x v = 0 := by
  have h1 : angForm (Az := Az) x v
      = Inner.inner ℝ (rot90 (Az x)) (mvfderiv I Az x v) := rfl
  rw [h1, h, inner_zero_right]

/-! ## The local computation of the angular form of the azimuth field -/

/- **The angular form of the azimuth field**, locally.

Given a local smooth lift `ϑ` of the argument of `u` (`circPt ∘ ϑ = u` near `x`) for which the
twisted field `rotE (β(τ) · (ρ(arg u) - arg u)) u` agrees near `x` with `circPt ∘ A`, where
`A = (1 - β(τ))·ϑ + β(τ)·ρ(ϑ)`, the angular form of the twisted field is computed in terms of
`ϑ` and of the derivative of `τ` and `β`. -/
set_option backward.isDefEq.respectTransparency.types false in
lemma angForm_twist_core
    {β : ℝ → ℝ} {τ : M → ℝ} {u : M → EuclideanSpace ℝ (Fin 2)} {ρ : ℝ → ℝ} {ϑ : M → ℝ}
    {x : M}
    (hϑ : ContMDiffAt I 𝓘(ℝ,ℝ) ∞ ϑ x)
    (hτa : ContMDiffAt I 𝓘(ℝ,ℝ) ∞ τ x)
    (hβ : ContDiff ℝ ∞ β) (hρ : ContDiff ℝ ∞ ρ)
    (hucirc : ∀ᶠ y in 𝓝 x, circPt (ϑ y) = u y)
    (hu1x : ‖u x‖ = 1)
    (hAzcirc : (fun y => rotE (Real.smoothTransition (β (τ y)) *
          (ρ (argE (u y)) - argE (u y))) (u y))
        =ᶠ[𝓝 x] fun y => circPt ((1 - Real.smoothTransition (β (τ y))) * ϑ y
            + Real.smoothTransition (β (τ y)) * ρ (ϑ y))) :
    ContMDiffAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞
        (fun y => rotE (Real.smoothTransition (β (τ y)) * (ρ (argE (u y)) - argE (u y))) (u y)) x ∧
      (∀ w : TangentSpace I x,
        angForm (Az := fun y => rotE (Real.smoothTransition (β (τ y)) *
            (ρ (argE (u y)) - argE (u y))) (u y)) x w
          = (1 - Real.smoothTransition (β (τ x))
                + Real.smoothTransition (β (τ x)) * deriv ρ (ϑ x)) * mvfderiv I ϑ x w
            + (ρ (ϑ x) - ϑ x) *
                (deriv (Real.smoothTransition ∘ β) (τ x) * mvfderiv I τ x w)) ∧
      (∀ w : TangentSpace I x, mvfderiv I ϑ x w = angForm (Az := u) x w) := by
  set A : M → ℝ := fun y => (1 - Real.smoothTransition (β (τ y))) * ϑ y
      + Real.smoothTransition (β (τ y)) * ρ (ϑ y) with hA
  have hηa : ContMDiffAt I 𝓘(ℝ,ℝ) ∞ (fun y => Real.smoothTransition (β (τ y))) x :=
    Real.smoothTransition.contDiff.contDiffAt.comp_contMDiffAt (hβ.contDiffAt.comp_contMDiffAt hτa)
  have hηd : MDifferentiableAt I 𝓘(ℝ,ℝ) (fun y => Real.smoothTransition (β (τ y))) x :=
    hηa.mdifferentiableAt (by simp)
  have hϑd : MDifferentiableAt I 𝓘(ℝ,ℝ) ϑ x := hϑ.mdifferentiableAt (by simp)
  have hτd : MDifferentiableAt I 𝓘(ℝ,ℝ) τ x := hτa.mdifferentiableAt (by simp)
  have hρϑ : ContMDiffAt I 𝓘(ℝ,ℝ) ∞ (fun y => ρ (ϑ y)) x :=
    hρ.contDiffAt.comp_contMDiffAt hϑ
  have hρϑd : MDifferentiableAt I 𝓘(ℝ,ℝ) (fun y => ρ (ϑ y)) x := hρϑ.mdifferentiableAt (by simp)
  have h1mη : MDifferentiableAt I 𝓘(ℝ,ℝ) (fun y => (1 : ℝ) - Real.smoothTransition (β (τ y))) x :=
    (mdifferentiableAt_const (I := I) (c := (1 : ℝ))).sub hηd
  have hAsm : ContMDiffAt I 𝓘(ℝ,ℝ) ∞ A x := by
    rw [hA]
    exact (((contMDiffAt_const (I := I) (c := (1 : ℝ))).sub hηa).mul hϑ).add (hηa.mul hρϑ)
  have hAzsm : ContMDiffAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞
      (fun y => rotE (Real.smoothTransition (β (τ y)) * (ρ (argE (u y)) - argE (u y))) (u y)) x := by
    have h1 : ContMDiffAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞ (fun y => circPt (A y)) x :=
      (contDiff_circPt.contDiffAt).comp_contMDiffAt hAsm
    exact h1.congr_of_eventuallyEq (by
      filter_upwards [hAzcirc] with y hy
      simpa only [hA] using hy)
  refine ⟨hAzsm, ?_, ?_⟩
  · intro w
    have hrot1 : ‖(fun y => rotE (Real.smoothTransition (β (τ y)) *
        (ρ (argE (u y)) - argE (u y))) (u y)) x‖ = 1 := by
      rw [norm_rotE, hu1x]
    have h1 : angForm (Az := fun y => rotE (Real.smoothTransition (β (τ y)) *
        (ρ (argE (u y)) - argE (u y))) (u y)) x w = mvfderiv I A x w :=
      angForm_apply_eq_mvfderiv_of_circPt (ψ := A) hAsm hAzcirc hrot1 w
    have hF : MDifferentiableAt I 𝓘(ℝ,ℝ)
        (fun y : M => (1 - Real.smoothTransition (β (τ y))) * ϑ y) x := h1mη.mul hϑd
    have hG : MDifferentiableAt I 𝓘(ℝ,ℝ)
        (fun y : M => Real.smoothTransition (β (τ y)) * ρ (ϑ y)) x := hηd.mul hρϑd
    have h2 : mvfderiv I A x w
        = mvfderiv I (fun y : M => (1 - Real.smoothTransition (β (τ y))) * ϑ y) x w
          + mvfderiv I (fun y : M => Real.smoothTransition (β (τ y)) * ρ (ϑ y)) x w :=
      mvfderiv_add_apply (I := I)
        (F := fun y : M => (1 - Real.smoothTransition (β (τ y))) * ϑ y)
        (G := fun y : M => Real.smoothTransition (β (τ y)) * ρ (ϑ y)) (x := x) (v := w) hF hG
    have h3 : mvfderiv I (fun y : M => (1 - Real.smoothTransition (β (τ y))) * ϑ y) x w
        = (1 - Real.smoothTransition (β (τ x))) * mvfderiv I ϑ x w
          + ϑ x * (- mvfderiv I (fun y : M => Real.smoothTransition (β (τ y))) x w) := by
      rw [mvfderiv_mul_apply (F := fun y : M => (1 : ℝ) - Real.smoothTransition (β (τ y)))
            (G := ϑ) h1mη hϑd,
        mvfderiv_const_sub_apply (F := fun y : M => Real.smoothTransition (β (τ y))) hηd]
    have h4 : mvfderiv I (fun y : M => Real.smoothTransition (β (τ y)) * ρ (ϑ y)) x w
        = Real.smoothTransition (β (τ x)) * (deriv ρ (ϑ x) * mvfderiv I ϑ x w)
          + mvfderiv I (fun y : M => Real.smoothTransition (β (τ y))) x w * ρ (ϑ x) := by
      rw [mvfderiv_mul_apply (F := fun y : M => Real.smoothTransition (β (τ y)))
            (G := fun y : M => ρ (ϑ y)) hηd hρϑd,
        mvfderiv_comp_scalar (φ := ρ) (f := ϑ) (hρ.contDiffAt.differentiableAt (by simp)) hϑd]
      ring
    have h5 : mvfderiv I (fun y : M => Real.smoothTransition (β (τ y))) x w
        = deriv (Real.smoothTransition ∘ β) (τ x) * mvfderiv I τ x w := by
      rw [show (fun y : M => Real.smoothTransition (β (τ y)))
          = (Real.smoothTransition ∘ β) ∘ τ from rfl]
      exact mvfderiv_comp_scalar (φ := Real.smoothTransition ∘ β) (f := τ)
        ((Real.smoothTransition.contDiff.comp hβ).differentiable (by simp)).differentiableAt hτd
    rw [h1, h2, h3, h4, h5]
    ring
  · intro w
    exact (angForm_apply_eq_mvfderiv_of_circPt (ψ := ϑ) hϑ
      (hucirc.mono fun y hy => hy.symm) hu1x w).symm


/-! ## The azimuth field: local existence of the angle lift -/

set_option backward.isDefEq.respectTransparency.types false in
lemma azimuth_core
    {β : ℝ → ℝ} {τ : M → ℝ} {u : M → EuclideanSpace ℝ (Fin 2)} {ρ : ℝ → ℝ}
    {N : Set M} {x : M} (hN : IsOpen N) (hx : x ∈ N)
    (hτsm : ContMDiffOn I 𝓘(ℝ,ℝ) ∞ τ N)
    (hu : ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞ u N)
    (hu1 : ∀ y ∈ N, ‖u y‖ = 1)
    (hβ : ContDiff ℝ ∞ β) (hρ : ContDiff ℝ ∞ ρ)
    (hρp : ∀ θ : ℝ, ρ (θ + 2 * Real.pi) = ρ θ + 2 * Real.pi) :
    ∃ ϑ : M → ℝ,
      ContMDiffAt I 𝓘(ℝ,ℝ) ∞ ϑ x ∧
      (u =ᶠ[𝓝 x] fun y => circPt (ϑ y)) ∧
      ((fun y => rotE (Real.smoothTransition (β (τ y)) *
          (ρ (argE (u y)) - argE (u y))) (u y))
        =ᶠ[𝓝 x] fun y => circPt ((1 - Real.smoothTransition (β (τ y))) * ϑ y
            + Real.smoothTransition (β (τ y)) * ρ (ϑ y))) ∧
      ContMDiffAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞
        (fun y => rotE (Real.smoothTransition (β (τ y)) *
          (ρ (argE (u y)) - argE (u y))) (u y)) x ∧
      (∀ w : TangentSpace I x,
        angForm (Az := fun y => rotE (Real.smoothTransition (β (τ y)) *
            (ρ (argE (u y)) - argE (u y))) (u y)) x w
          = (1 - Real.smoothTransition (β (τ x))
                + Real.smoothTransition (β (τ x)) * deriv ρ (ϑ x)) * mvfderiv I ϑ x w
            + (ρ (ϑ x) - ϑ x) *
                (deriv (Real.smoothTransition ∘ β) (τ x) * mvfderiv I τ x w)) ∧
      (∀ w : TangentSpace I x, mvfderiv I ϑ x w = angForm (Az := u) x w) := by
  have hτa : ContMDiffAt I 𝓘(ℝ,ℝ) ∞ τ x := hτsm.contMDiffAt (hN.mem_nhds hx)
  have hua : ContMDiffAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞ u x := hu.contMDiffAt (hN.mem_nhds hx)
  have hu1x : ‖u x‖ = 1 := hu1 x hx
  have key : ∀ ϑ : M → ℝ, ContMDiffAt I 𝓘(ℝ,ℝ) ∞ ϑ x →
      (u =ᶠ[𝓝 x] fun y => circPt (ϑ y)) →
      ((fun y => rotE (Real.smoothTransition (β (τ y)) *
          (ρ (argE (u y)) - argE (u y))) (u y))
        =ᶠ[𝓝 x] fun y => circPt ((1 - Real.smoothTransition (β (τ y))) * ϑ y
            + Real.smoothTransition (β (τ y)) * ρ (ϑ y))) →
      ContMDiffAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞
        (fun y => rotE (Real.smoothTransition (β (τ y)) *
          (ρ (argE (u y)) - argE (u y))) (u y)) x ∧
      (∀ w : TangentSpace I x,
        angForm (Az := fun y => rotE (Real.smoothTransition (β (τ y)) *
            (ρ (argE (u y)) - argE (u y))) (u y)) x w
          = (1 - Real.smoothTransition (β (τ x))
                + Real.smoothTransition (β (τ x)) * deriv ρ (ϑ x)) * mvfderiv I ϑ x w
            + (ρ (ϑ x) - ϑ x) *
                (deriv (Real.smoothTransition ∘ β) (τ x) * mvfderiv I τ x w)) ∧
      (∀ w : TangentSpace I x, mvfderiv I ϑ x w = angForm (Az := u) x w) :=
    fun ϑ hϑ hucirc hAzcirc =>
      angForm_twist_core hϑ hτa hβ hρ (hucirc.mono fun y hy => hy.symm) hu1x hAzcirc
  by_cases hcase : toC (u x) = -1
  · -- `u x` is the branch point: lift the angle using `-u`
    have hne : toC (-(u x)) ≠ -1 := by
      rw [toC_neg, hcase]
      norm_num
    have hslit : toC (-(u x)) ∈ Complex.slitPlane :=
      slitPlane_toC (by rw [norm_neg, hu1x]) hne
    have hnu : ContMDiffAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞ (fun y => -(u y)) x := hua.neg
    have harg : ContMDiffAt I 𝓘(ℝ,ℝ) ∞ (fun y => argE (-(u y))) x :=
      ContDiffAt.comp_contMDiffAt (x := x) (g := argE) (f := fun y => -(u y))
        (contDiffAt_argE hslit) hnu
    have hϑ : ContMDiffAt I 𝓘(ℝ,ℝ) ∞ (fun y => argE (-(u y)) + Real.pi) x :=
      harg.add (contMDiffAt_const (I := I) (c := Real.pi))
    have hucirc : u =ᶠ[𝓝 x] fun y => circPt (argE (-(u y)) + Real.pi) := by
      filter_upwards [hN.mem_nhds hx] with y hy
      rw [circPt_add_pi, circPt_argE (by rw [norm_neg, hu1 y hy]), neg_neg]
    have hAzcirc : ((fun y => rotE (Real.smoothTransition (β (τ y)) *
          (ρ (argE (u y)) - argE (u y))) (u y))
        =ᶠ[𝓝 x] fun y => circPt ((1 - Real.smoothTransition (β (τ y))) *
            (argE (-(u y)) + Real.pi)
            + Real.smoothTransition (β (τ y)) * ρ (argE (-(u y)) + Real.pi))) := by
      filter_upwards [hN.mem_nhds hx] with y hy
      have hne0 : toC (u y) ≠ 0 := by
        intro h'
        have h2 : ‖toC (u y)‖ = 1 := by rw [norm_toC, hu1 y hy]
        rw [h'] at h2
        norm_num at h2
      obtain ⟨k, hk⟩ := arg_neg_add_pi (toC (u y)) hne0
      have hk' : argE (-(u y)) + Real.pi = argE (u y) + (k : ℝ) * (2 * Real.pi) := by
        simpa only [argE, toC_neg] using hk
      have hk'' : argE (u y) = argE (-(u y)) + Real.pi - (k : ℝ) * (2 * Real.pi) := by
        rw [hk']
        ring
      have hρk : ρ (argE (u y)) = ρ (argE (-(u y)) + Real.pi) - (k : ℝ) * (2 * Real.pi) := by
        have h1 := rho_add_int_mul hρp (-k) (argE (-(u y)) + Real.pi)
        have h2 : argE (u y) = (argE (-(u y)) + Real.pi) + ((-k : ℤ) : ℝ) * (2 * Real.pi) := by
          rw [hk'']
          push_cast
          ring
        rw [h2, h1]
        push_cast
        ring
      have hstep : rotE (Real.smoothTransition (β (τ y)) *
            (ρ (argE (u y)) - argE (u y))) (u y)
          = circPt ((1 - Real.smoothTransition (β (τ y))) * argE (u y)
              + Real.smoothTransition (β (τ y)) * ρ (argE (u y))) := by
        have h1 : rotE (Real.smoothTransition (β (τ y)) *
              (ρ (argE (u y)) - argE (u y))) (u y)
            = rotE (Real.smoothTransition (β (τ y)) *
              (ρ (argE (u y)) - argE (u y))) (circPt (argE (u y))) :=
          congrArg (rotE (Real.smoothTransition (β (τ y)) *
              (ρ (argE (u y)) - argE (u y)))) (circPt_argE (hu1 y hy)).symm
        rw [h1, rotE_circPt]
        congr 1
        ring
      rw [hstep]
      have hA : (1 - Real.smoothTransition (β (τ y))) * argE (u y)
            + Real.smoothTransition (β (τ y)) * ρ (argE (u y))
          = ((1 - Real.smoothTransition (β (τ y))) * (argE (-(u y)) + Real.pi)
              + Real.smoothTransition (β (τ y)) * ρ (argE (-(u y)) + Real.pi))
            + ((-k : ℤ) : ℝ) * (2 * Real.pi) := by
        rw [hρk, hk'']
        push_cast
        ring
      rw [hA, circPt_periodic]
    obtain ⟨h1, h2, h3⟩ := key (fun y => argE (-(u y)) + Real.pi) hϑ hucirc hAzcirc
    exact ⟨_, hϑ, hucirc, hAzcirc, h1, h2, h3⟩
  · -- `u x` avoids the branch cut
    have hslit : toC (u x) ∈ Complex.slitPlane := slitPlane_toC hu1x hcase
    have hϑ : ContMDiffAt I 𝓘(ℝ,ℝ) ∞ (fun y => argE (u y)) x :=
      (contDiffAt_argE hslit).comp_contMDiffAt hua
    have hucirc : u =ᶠ[𝓝 x] fun y => circPt (argE (u y)) := by
      filter_upwards [hN.mem_nhds hx] with y hy
      exact (circPt_argE (hu1 y hy)).symm
    have hAzcirc : ((fun y => rotE (Real.smoothTransition (β (τ y)) *
          (ρ (argE (u y)) - argE (u y))) (u y))
        =ᶠ[𝓝 x] fun y => circPt ((1 - Real.smoothTransition (β (τ y))) * argE (u y)
            + Real.smoothTransition (β (τ y)) * ρ (argE (u y)))) := by
      filter_upwards [hN.mem_nhds hx] with y hy
      have h1 : rotE (Real.smoothTransition (β (τ y)) *
            (ρ (argE (u y)) - argE (u y))) (u y)
          = rotE (Real.smoothTransition (β (τ y)) *
            (ρ (argE (u y)) - argE (u y))) (circPt (argE (u y))) :=
        congrArg (rotE (Real.smoothTransition (β (τ y)) *
            (ρ (argE (u y)) - argE (u y)))) (circPt_argE (hu1 y hy)).symm
      rw [h1, rotE_circPt]
      congr 1
      ring
    obtain ⟨h1, h2, h3⟩ := key (fun y => argE (u y)) hϑ hucirc hAzcirc
    exact ⟨_, hϑ, hucirc, hAzcirc, h1, h2, h3⟩

end ManifoldFacts

theorem azimuth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
    {N : Set M} (hN : IsOpen N)
    {V : (x : M) → TangentSpace I x}
    (hVsm : ContMDiff I (I.prod (modelWithCornersSelf ℝ E)) ∞
      (fun y : M => (⟨y, V y⟩ : Bundle.TotalSpace E (TangentSpace I))))
    {τ : M → ℝ} (hτsm : ContMDiffOn I 𝓘(ℝ,ℝ) ∞ τ N)
    (hτV : ∀ x ∈ N, mfderiv I 𝓘(ℝ,ℝ) τ x (V x) = 1)
    {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hβ0 : ∀ t : ℝ, t ≤ 0 → β t = 0) (hβ1 : ∀ t : ℝ, 1 ≤ t → β t = 1)
    (hβr : ∀ t : ℝ, 0 ≤ β t ∧ β t ≤ 1)
    {u v : M → EuclideanSpace ℝ (Fin 2)}
    (hu : ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞ u N)
    (hv : ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞ v N)
    (hu1 : ∀ x ∈ N, ‖u x‖ = 1) (hv1 : ∀ x ∈ N, ‖v x‖ = 1)
    (huV : ∀ x ∈ N, mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) u x (V x) = 0)
    (hvV : ∀ x ∈ N, mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) v x (V x) = 0)
    (huang : ∀ x ∈ N, 0 < β (τ x) → β (τ x) < 1 → ∀ w : TangentSpace I x, w ≠ 0 →
      mfderiv I 𝓘(ℝ,ℝ) τ x w = 0 →
      angForm (I := I) (M := M) (Az := u) x w ≠ 0)
    {s : ℝ} (hs : s = 1 ∨ s = -1) {ρ : ℝ → ℝ} (hρ : ContDiff ℝ ∞ ρ)
    (hρ' : ∀ θ : ℝ, 0 < deriv ρ θ)
    (hρp : ∀ θ : ℝ, ρ (θ + 2 * Real.pi) = ρ θ + 2 * Real.pi)
    (htrans : ∀ x ∈ N, reflE s (v x) = rotE (ρ (argE (u x)) - argE (u x)) (u x)) :
    ∃ Az : M → EuclideanSpace ℝ (Fin 2),
      Az = (fun x : M => rotE (Real.smoothTransition (β (τ x)) *
        (ρ (argE (u x)) - argE (u x))) (u x)) ∧
      ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞ Az N ∧
      (∀ x ∈ N, ‖Az x‖ = 1) ∧
      (∀ x ∈ N, β (τ x) = 0 → Az x = u x) ∧
      (∀ x ∈ N, 1 ≤ β (τ x) → Az x = reflE s (v x)) ∧
      (∀ x ∈ N, β (τ x) ≤ 0 →
        angForm (I := I) (M := M) (Az := Az) x (V x) = 0) ∧
      (∀ x ∈ N, 1 ≤ β (τ x) →
        angForm (I := I) (M := M) (Az := Az) x (V x) = 0) ∧
      (∀ x ∈ N, 0 < β (τ x) → β (τ x) < 1 → ∀ w : TangentSpace I x, w ≠ 0 →
        mfderiv I 𝓘(ℝ,ℝ) τ x w = 0 →
        angForm (I := I) (M := M) (Az := Az) x w ≠ 0) := by
  refine ⟨fun x => rotE (Real.smoothTransition (β (τ x)) * (ρ (argE (u x)) - argE (u x))) (u x),
    rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨ϑ, hϑ, hucirc, hAzcirc, hAzsm, hformula, hident⟩ :=
      azimuth_core (I := I) (M := M) hN hx hτsm hu hu1 hβ hρ hρp
    exact hAzsm.contMDiffWithinAt
  · intro x hx
    rw [norm_rotE, hu1 x hx]
  · intro x hx hx0
    change rotE (Real.smoothTransition (β (τ x)) * (ρ (argE (u x)) - argE (u x))) (u x) = u x
    rw [Real.smoothTransition.zero_of_nonpos (le_of_eq hx0), zero_mul, rotE_zero]
  · intro x hx hx1
    change rotE (Real.smoothTransition (β (τ x)) * (ρ (argE (u x)) - argE (u x))) (u x)
      = reflE s (v x)
    rw [Real.smoothTransition.one_of_one_le hx1, one_mul, htrans x hx]
  · intro x hx hx0
    obtain ⟨ϑ, hϑ, hucirc, hAzcirc, hAzsm, hformula, hident⟩ :=
      azimuth_core (I := I) (M := M) hN hx hτsm hu hu1 hβ hρ hρp
    have huVx : angForm (Az := u) x (V x) = 0 := by
      apply angForm_eq_zero_of_mvfderiv_eq_zero (Az := u) (x := x) (v := V x)
      rw [show mvfderiv I u x (V x) = NormedSpace.fromTangentSpace (u x)
          ((mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) u x) (V x)) from rfl,
        huV x hx, map_zero]
    have hτVx : mvfderiv I τ x (V x) = 1 := by
      rw [show mvfderiv I τ x (V x) = NormedSpace.fromTangentSpace (τ x)
          ((mfderiv I 𝓘(ℝ,ℝ) τ x) (V x)) from rfl, hτV x hx]
      rfl
    have hderiv : deriv (Real.smoothTransition ∘ β) (τ x) = 0 := by
      rw [deriv_comp (τ x)
        ((Real.smoothTransition.contDiff (n := (1 : ℕ∞))).differentiable
          (by norm_num)).differentiableAt
        ((hβ.differentiable (by simp)).differentiableAt)]
      rw [deriv_smoothTransition_eq_zero (β (τ x)) (Or.inl hx0), zero_mul]
    rw [hformula (V x), hderiv, hident (V x), huVx, hτVx]
    ring
  · intro x hx hx1
    obtain ⟨ϑ, hϑ, hucirc, hAzcirc, hAzsm, hformula, hident⟩ :=
      azimuth_core (I := I) (M := M) hN hx hτsm hu hu1 hβ hρ hρp
    have huVx : angForm (Az := u) x (V x) = 0 := by
      apply angForm_eq_zero_of_mvfderiv_eq_zero (Az := u) (x := x) (v := V x)
      rw [show mvfderiv I u x (V x) = NormedSpace.fromTangentSpace (u x)
          ((mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) u x) (V x)) from rfl,
        huV x hx, map_zero]
    have hτVx : mvfderiv I τ x (V x) = 1 := by
      rw [show mvfderiv I τ x (V x) = NormedSpace.fromTangentSpace (τ x)
          ((mfderiv I 𝓘(ℝ,ℝ) τ x) (V x)) from rfl, hτV x hx]
      rfl
    have hderiv : deriv (Real.smoothTransition ∘ β) (τ x) = 0 := by
      rw [deriv_comp (τ x)
        ((Real.smoothTransition.contDiff (n := (1 : ℕ∞))).differentiable
          (by norm_num)).differentiableAt
        ((hβ.differentiable (by simp)).differentiableAt)]
      rw [deriv_smoothTransition_eq_zero (β (τ x)) (Or.inr hx1), zero_mul]
    rw [hformula (V x), hderiv, hident (V x), huVx, hτVx]
    ring
  · intro x hx hx0 hxlt w hw hτw
    obtain ⟨ϑ, hϑ, hucirc, hAzcirc, hAzsm, hformula, hident⟩ :=
      azimuth_core (I := I) (M := M) hN hx hτsm hu hu1 hβ hρ hρp
    have hτw' : mvfderiv I τ x w = 0 := by
      rw [show mvfderiv I τ x w = NormedSpace.fromTangentSpace (τ x)
          ((mfderiv I 𝓘(ℝ,ℝ) τ x) w) from rfl, hτw, map_zero]
    have hcoef : 0 < 1 - Real.smoothTransition (β (τ x))
        + Real.smoothTransition (β (τ x)) * deriv ρ (ϑ x) := by
      have he0 : 0 ≤ Real.smoothTransition (β (τ x)) := Real.smoothTransition.nonneg _
      have he1 : Real.smoothTransition (β (τ x)) ≤ 1 := Real.smoothTransition.le_one _
      have hd : 0 < deriv ρ (ϑ x) := hρ' (ϑ x)
      by_cases hd1 : 1 ≤ deriv ρ (ϑ x)
      · nlinarith [he0, he1, hd1]
      · nlinarith [he0, he1, hd, not_le.mp hd1]
    have hrest : mvfderiv I ϑ x w ≠ 0 := by
      rw [hident w]
      exact huang x hx hx0 hxlt w hw hτw
    rw [hformula w, hτw', mul_zero, mul_zero, add_zero]
    exact mul_ne_zero (ne_of_gt hcoef) hrest
end Work.Diff.Dim2
