import Submission.EDist
import Submission.Commons.Analysis.ODE.sturm_eqOn_zero_of_second_deriv_add_nonneg
import Submission.Commons.Analysis.Calculus.cos_second_deriv_ge_of_cot

open Set Filter
open scoped Topology ContDiff Manifold
open Bundle

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.HingeCompare

noncomputable section


variable {ρ ρ' F : ℝ → ℝ} {a θ T : ℝ}

/-- The model distance function of the space form of curvature `1` (spherical law of cosines). -/
def modelFun (a θ : ℝ) : ℝ → ℝ :=
  (fun t => Real.cos a * Real.cos t) + (fun t => Real.sin a * Real.sin t * Real.cos θ)

/-- The derivative of the model function. -/
def modelFun' (a θ : ℝ) : ℝ → ℝ :=
  (-(fun t => Real.cos a * Real.sin t)) + (fun t => Real.sin a * Real.cos t * Real.cos θ)

lemma hasDerivAt_modelFun (a θ t : ℝ) : HasDerivAt (modelFun a θ) (modelFun' a θ t) t := by
  have hfun : modelFun a θ
      = ((fun y : ℝ => Real.cos a * Real.cos y)
          + (fun y : ℝ => Real.sin a * Real.sin y * Real.cos θ)) := rfl
  have hval : modelFun' a θ t
      = Real.cos a * -Real.sin t + Real.sin a * Real.cos t * Real.cos θ := by
    simp only [modelFun', Pi.add_apply, Pi.neg_apply]; ring
  rw [hfun, hval]
  exact ((Real.hasDerivAt_cos t).const_mul (Real.cos a)).add
    (((Real.hasDerivAt_sin t).const_mul (Real.sin a)).mul_const (Real.cos θ))

lemma hasDerivAt_modelFun' (a θ t : ℝ) : HasDerivAt (modelFun' a θ) (-(modelFun a θ t)) t := by
  have hfun : modelFun' a θ
      = ((-(fun y : ℝ => Real.cos a * Real.sin y))
          + (fun y : ℝ => Real.sin a * Real.cos y * Real.cos θ)) := rfl
  have hval : -(modelFun a θ t)
      = -(Real.cos a * Real.cos t) + Real.sin a * -Real.sin t * Real.cos θ := by
    simp only [modelFun, Pi.add_apply]; ring
  rw [hfun, hval]
  exact (((Real.hasDerivAt_sin t).const_mul (Real.cos a)).neg).add
    (((Real.hasDerivAt_cos t).const_mul (Real.sin a)).mul_const (Real.cos θ))



lemma continuous_modelFun (a θ : ℝ) : Continuous (modelFun a θ) := by
  rw [show modelFun a θ
      = ((fun t : ℝ => Real.cos a * Real.cos t)
          + (fun t : ℝ => Real.sin a * Real.sin t * Real.cos θ)) from rfl]
  exact (continuous_const.mul Real.continuous_cos).add
    ((continuous_const.mul Real.continuous_sin).mul continuous_const)

/-- **Toponogov's hinge comparison, reduced to the Hessian bound for the distance function.**

Let `ρ` be a continuous function with values in `[0, π]` on `[0, T]`, `T < π`, with `ρ 0 = a` and
`ρ'(0) = -cos θ` (the first variation formula for the distance function), and suppose that
`(cos ∘ ρ)'' ≥ -(cos ∘ ρ)` on `(0, T)` (the Hessian comparison for the distance function).  Then
`ρ t ≤ ⋎(θ; a, t)` for `t ∈ [0, T]`, where `⋎` is the distance in the model space form of
curvature `1` given by the spherical law of cosines
`cos ⋎ = cos a cos t + sin a sin t cos θ`. -/
theorem hinge_of_cos_second_deriv
    (_ha : 0 ≤ a) (_hθ : 0 ≤ θ) (_hθπ : θ ≤ Real.pi)
    (hT : 0 < T) (hTπ : T < Real.pi)
    (hρ0 : ρ 0 = a)
    (hρcont : ContinuousOn ρ (Set.Icc 0 T))
    (hρrange : ∀ t ∈ Set.Icc 0 T, ρ t ∈ Set.Icc 0 Real.pi)
    (hd0 : HasDerivAt ρ (-(Real.cos θ)) 0)
    (hρ : ∀ t ∈ Set.Ioo 0 T, HasDerivAt ρ (ρ' t) t)
    (hρ2 : ∀ t ∈ Set.Ioo 0 T, HasDerivAt (fun s => -(Real.sin (ρ s) * ρ' s)) (F t) t)
    (hF : ∀ t ∈ Set.Ioo 0 T, 0 ≤ F t + Real.cos (ρ t)) :
    ∀ t ∈ Set.Icc 0 T, ρ t ≤ Real.arccos (modelFun a θ t) := by
  set w : ℝ → ℝ := (fun s : ℝ => Real.cos (ρ s)) - modelFun a θ with hwdef
  set w' : ℝ → ℝ := (-(fun s : ℝ => Real.sin (ρ s) * ρ' s)) - modelFun' a θ with hw'def
  set Ff : ℝ → ℝ := F + modelFun a θ with hFfdef
  have hwderiv : ∀ t ∈ Set.Ioo 0 T, HasDerivAt w (w' t) t := by
    intro t ht
    rw [hwdef, hw'def]
    have h1 : HasDerivAt (fun s : ℝ => Real.cos (ρ s)) (-(Real.sin (ρ t) * ρ' t)) t := by
      have h := (hρ t ht).cos
      have hv : -(Real.sin (ρ t)) * ρ' t = -(Real.sin (ρ t) * ρ' t) := by ring
      rwa [hv] at h
    exact h1.sub (hasDerivAt_modelFun a θ t)
  have hw'deriv : ∀ t ∈ Set.Ioo 0 T, HasDerivAt w' (Ff t) t := by
    intro t ht
    rw [hw'def, hFfdef]
    have h3 := (hρ2 t ht).sub (hasDerivAt_modelFun' a θ t)
    have hv : F t - -modelFun a θ t = F t + modelFun a θ t := by ring
    rw [hv] at h3
    exact h3
  have hc0 : HasDerivAt w 0 0 := by
    rw [hwdef]
    have h1 : HasDerivAt (fun s : ℝ => Real.cos (ρ s)) (Real.sin a * Real.cos θ) 0 := by
      have h := hd0.cos
      have hv : -(Real.sin (ρ 0)) * (-(Real.cos θ)) = Real.sin a * Real.cos θ := by
        rw [hρ0]; ring
      rwa [hv] at h
    have h2 : HasDerivAt (modelFun a θ) (Real.sin a * Real.cos θ) 0 := by
      have h := hasDerivAt_modelFun a θ 0
      have hv : modelFun' a θ 0 = Real.sin a * Real.cos θ := by
        simp only [modelFun', Pi.add_apply, Pi.neg_apply, Real.sin_zero, Real.cos_zero, mul_zero,
          mul_one, neg_zero, zero_add]
      rwa [hv] at h
    have h3 := h1.sub h2
    have hv : Real.sin a * Real.cos θ - Real.sin a * Real.cos θ = (0 : ℝ) := sub_self _
    rwa [hv] at h3
  have hwc : w 0 = 0 := by
    rw [hwdef]
    simp only [Pi.sub_apply, hρ0, modelFun, Pi.add_apply, Real.cos_zero, Real.sin_zero, mul_zero,
      mul_one]
    ring
  have hwcont : ContinuousOn w (Set.Icc 0 T) := by
    rw [hwdef]
    exact (Real.continuous_cos.comp_continuousOn hρcont).sub
      (continuous_modelFun a θ).continuousOn
  have hFf : ∀ t ∈ Set.Ioo 0 T, 0 ≤ Ff t + (1 : ℝ) ^ 2 * w t := by
    intro t ht
    rw [hFfdef, hwdef]
    have hh := hF t ht
    simp only [Pi.add_apply, Pi.sub_apply, one_pow, one_mul]
    linarith
  have hmain := Commons.Analysis.ODE.sturm_max_principle_right (a := 1) (c := 0) (d := T)
    (w := w) (w' := w') (F := Ff) one_pos hT (by simpa using hTπ) hwcont hwderiv hw'deriv hc0 hwc
    hFf
  intro t ht
  have hnn : 0 ≤ w t := hmain t ht
  rw [hwdef] at hnn
  simp only [Pi.sub_apply] at hnn
  have hM : modelFun a θ t ≤ Real.cos (ρ t) := by linarith
  have hle : Real.arccos (Real.cos (ρ t)) ≤ Real.arccos (modelFun a θ t) :=
    Real.arccos_le_arccos hM
  rwa [Real.arccos_cos (hρrange t ht).1 (hρrange t ht).2] at hle



/-- **The Hessian bound for the distance function along a geodesic** (the single remaining
geometric input of Toponogov's hinge comparison).  It says that for the function
`ρ t = d(q, σ t)` one has `(cos ∘ ρ)'' ≥ -(cos ∘ ρ)` on `(0, T)`, with the second derivative named by
the function `G`. -/
def DistHessianBound (ρ ρ' G : ℝ → ℝ) (T : ℝ) : Prop :=
  (∀ t ∈ Set.Ioo (0 : ℝ) T, HasDerivAt ρ (ρ' t) t) ∧
  (∀ t ∈ Set.Ioo (0 : ℝ) T, HasDerivAt (fun s => -(Real.sin (ρ s) * ρ' s)) (G t) t) ∧
  (∀ t ∈ Set.Ioo (0 : ℝ) T, -(Real.cos (ρ t)) ≤ G t)

/-- **Toponogov's hinge comparison for the Riemannian distance function**, in the manifold
setting, assuming the Hessian bound `DistHessianBound`.  Let `σ` be a unit-speed geodesic starting
at `p = σ 0`, `q ∈ M`, `a = d(q, p)`, and `θ` the hinge angle at `p` (so that the right derivative of
`d(q, σ ·)` at `0` is `-cos θ`, by the first variation formula).  Then
`d(q, σ T) ≤ ⋎(θ; a, T)` for `T < π`, the model distance of the space form of curvature `1`. -/
theorem hinge_comparison_dist
    {q : M} {σ : ℝ → M} {a θ T : ℝ}
    (_ha : 0 ≤ a) (_hθ : 0 ≤ θ) (hθπ : θ ≤ Real.pi) (hT : 0 < T) (hTπ : T < Real.pi)
    {ρ ρ' G : ℝ → ℝ}
    (hρeq : ∀ t, ρ t = (Manifold.riemannianEDist I q (σ t)).toReal)
    (hρ0 : ρ 0 = a)
    (hcont : ContinuousOn ρ (Set.Icc 0 T))
    (hrange : ∀ t ∈ Set.Icc 0 T, ρ t ∈ Set.Icc 0 Real.pi)
    (hd0 : HasDerivAt ρ (-(Real.cos θ)) 0)
    (hb : DistHessianBound ρ ρ' G T) :
    (Manifold.riemannianEDist I q (σ T)).toReal ≤ Real.arccos (modelFun a θ T) := by
  obtain ⟨hd1, hd2, hd3⟩ := hb
  have hmain := hinge_of_cos_second_deriv (ρ := ρ) (ρ' := ρ') (F := G) (a := a) (θ := θ) (T := T)
    _ha _hθ hθπ hT hTπ hρ0 hcont hrange hd0 hd1 hd2 (fun t ht => by linarith [hd3 t ht])
  rw [← hρeq T]
  exact hmain T ⟨le_of_lt hT, le_refl T⟩

/-- **Toponogov's hinge comparison in the classical `cot` form.**  Same setting as
`hinge_of_cos_second_deriv`, but the Hessian bound is given as the classical inequality
`ρ'' ≤ cot ρ · (1 - ρ'²)` (which makes `ρ` concave where `ρ > π/2`). -/
theorem hinge_of_cot_bound
    {ρ ρ' ρ'' : ℝ → ℝ}
    (_ha : 0 ≤ a) (hθ : 0 ≤ θ) (hθπ : θ ≤ Real.pi)
    (hT : 0 < T) (hTπ : T < Real.pi)
    (hρ0 : ρ 0 = a)
    (hρcont : ContinuousOn ρ (Set.Icc 0 T))
    (hρint : ∀ t ∈ Set.Ioo 0 T, ρ t ∈ Set.Ioo 0 Real.pi)
    (hρrange : ∀ t ∈ Set.Icc 0 T, ρ t ∈ Set.Icc 0 Real.pi)
    (hd0 : HasDerivAt ρ (-(Real.cos θ)) 0)
    (hρ : ∀ t ∈ Set.Ioo 0 T, HasDerivAt ρ (ρ' t) t)
    (hρ' : ∀ t ∈ Set.Ioo 0 T, HasDerivAt ρ' (ρ'' t) t)
    (hcot : ∀ t ∈ Set.Ioo 0 T, ρ'' t ≤ Real.cot (ρ t) * (1 - ρ' t ^ 2)) :
    ∀ t ∈ Set.Icc 0 T, ρ t ≤ Real.arccos (modelFun a θ t) := by
  have h2 : ∀ t ∈ Set.Ioo 0 T, HasDerivAt (fun s : ℝ => -(Real.sin (ρ s) * ρ' s))
      (-(Real.sin (ρ t) * ρ'' t) - Real.cos (ρ t) * ρ' t ^ 2) t := by
    intro t ht
    have hsin : HasDerivAt (fun s : ℝ => Real.sin (ρ s)) (Real.cos (ρ t) * ρ' t) t :=
      (hρ t ht).sin
    have h1 : HasDerivAt (fun s : ℝ => -(Real.sin (ρ s) * ρ' s))
        (-(Real.cos (ρ t) * ρ' t * ρ' t + Real.sin (ρ t) * ρ'' t)) t :=
      (hsin.mul (hρ' t ht)).neg
    have hval : -(Real.cos (ρ t) * ρ' t * ρ' t + Real.sin (ρ t) * ρ'' t)
        = -(Real.sin (ρ t) * ρ'' t) - Real.cos (ρ t) * ρ' t ^ 2 := by ring
    rwa [hval] at h1
  have h3 : ∀ t ∈ Set.Ioo 0 T,
      0 ≤ -(Real.sin (ρ t) * ρ'' t) - Real.cos (ρ t) * ρ' t ^ 2 + Real.cos (ρ t) := by
    intro t ht
    have h := Commons.Analysis.Calculus.cos_second_deriv_ge_of_cot (ρ := ρ) (ρ' := ρ')
      (ρ'' := ρ'') (T := T) hρint hcot t ht
    linarith
  exact hinge_of_cos_second_deriv (ρ := ρ) (ρ' := ρ')
    (F := fun t => -(Real.sin (ρ t) * ρ'' t) - Real.cos (ρ t) * ρ' t ^ 2)
    _ha hθ hθπ hT hTπ hρ0 hρcont hρrange hd0 hρ h2 h3

end

end Submission.HingeCompare
