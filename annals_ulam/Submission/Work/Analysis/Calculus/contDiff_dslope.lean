import Mathlib
import Submission.Commons.Analysis.Calculus.iteratedFDeriv_intervalIntegral_comp_smul

/-!
# Smoothness of the divided difference

`dslope h u σ` is `(h σ - h u)/(σ - u)` for `σ ≠ u`, and `deriv h u` on the diagonal.  We
show that when `h` is `C^∞` the map `(u, σ) ↦ dslope h u σ` is `C^∞`.

The proof rests on two pieces:

* the integral representation `dslope h u σ = ∫ t in 0..1, deriv h (u + t * (σ - u))`
  (the `t ↦ u + t * (σ - u)` substitution in `∫_u^σ deriv h`), and
* the smoothness of parametric interval integrals: for a jointly `C^n` function
  `f : P → ℝ → G` on a proper parameter space `P`, the map `y ↦ ∫ s in a..b, f y s` is `C^n`.
-/

noncomputable section

open MeasureTheory Filter Function
open scoped Topology Interval

namespace Work.Analysis.Calculus

set_option maxHeartbeats 1600000

/-- **Parametric smoothness of a fixed-interval integral.**  If `f : P → ℝ → G` is jointly
`C^n` then so is `y ↦ ∫ s in a..b, f y s`. -/
theorem contDiff_intervalIntegral_parametric.{u}
    {P : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P] [ProperSpace P]
    {a b : ℝ} (n : ℕ) :
    ∀ {G : Type u} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
      (f : P → ℝ → G), ContDiff ℝ n (Function.uncurry f) →
      ContDiff ℝ n (fun y : P => ∫ s in a..b, f y s) := by
  induction n with
  | zero =>
      intro G _ _ _ f hf
      have hcont := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (μ := volume) (f := f) hf.continuous a b
      simpa only [Nat.cast_zero] using
        (contDiff_zero.mpr hcont : ContDiff ℝ (0 : ℕ∞) (fun y : P => ∫ s in a..b, f y s))
  | succ n ih =>
      intro G _ _ _ f hf
      rw [Nat.cast_succ, contDiff_succ_iff_hasFDerivAt]
      have key : ∀ (y : P) (s : ℝ), fderiv ℝ (fun y' : P => f y' s) y
          = (fderiv ℝ (Function.uncurry f) (y, s)).comp (ContinuousLinearMap.inl ℝ P ℝ) := by
        intro y s
        have hφ : HasFDerivAt (fun y' : P => (y', s)) (ContinuousLinearMap.inl ℝ P ℝ) y :=
          hasFDerivAt_prodMk_left y s
        have hF : HasFDerivAt (Function.uncurry f) (fderiv ℝ (Function.uncurry f) (y, s))
            (y, s) :=
          ((hf.differentiable (by simp) (y, s))).hasFDerivAt
        have hcomp : HasFDerivAt ((Function.uncurry f) ∘ (fun y' : P => (y', s)))
            ((fderiv ℝ (Function.uncurry f) (y, s)).comp (ContinuousLinearMap.inl ℝ P ℝ)) y :=
          hF.comp y hφ
        have hfun2 : (fun y' : P => f y' s)
            = (Function.uncurry f) ∘ (fun y' : P => (y', s)) := rfl
        rw [hfun2]
        exact hcomp.fderiv
      set f' : P → ℝ → P →L[ℝ] G := fun y s => fderiv ℝ (fun y' : P => f y' s) y with hf'def
      have hfun : Function.uncurry f'
          = fun q : P × ℝ => (fderiv ℝ (Function.uncurry f) q) ∘SL
              (ContinuousLinearMap.inl ℝ P ℝ) := by
        funext q
        obtain ⟨y, s⟩ := q
        simp only [Function.uncurry_apply_pair, hf'def]
        exact key y s
      have hf'_joint : ContDiff ℝ n (Function.uncurry f') := by
        rw [hfun]
        have h1 : ContDiff ℝ n (fderiv ℝ (Function.uncurry f)) :=
          hf.fderiv_right (m := (n : WithTop ℕ∞)) (by simp)
        exact h1.clm_comp contDiff_const
      refine ⟨fun y => ∫ s in a..b, f' y s, ih f' hf'_joint, fun y => ?_⟩
      refine Commons.Analysis.Calculus.hasFDerivAt_intervalIntegral_of_continuous
        hf.continuous hf'_joint.continuous ?_
      intro y s
      have hφ : HasFDerivAt (fun y' : P => (y', s)) (ContinuousLinearMap.inl ℝ P ℝ) y :=
        hasFDerivAt_prodMk_left y s
      have hF : HasFDerivAt (Function.uncurry f) (fderiv ℝ (Function.uncurry f) (y, s))
          (y, s) :=
        ((hf.differentiable (by simp) (y, s))).hasFDerivAt
      have hcomp : HasFDerivAt ((Function.uncurry f) ∘ (fun y' : P => (y', s)))
          ((fderiv ℝ (Function.uncurry f) (y, s)).comp (ContinuousLinearMap.inl ℝ P ℝ)) y :=
        hF.comp y hφ
      have hfun2 : (fun y' : P => f y' s)
          = (Function.uncurry f) ∘ (fun y' : P => (y', s)) := rfl
      rw [hf'def]
      simp only [key y s]
      rw [hfun2]
      exact hcomp

/-- The `C^∞` version of `contDiff_intervalIntegral_parametric`. -/
theorem contDiff_intervalIntegral_parametric_top.{u}
    {P : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P] [ProperSpace P]
    {a b : ℝ} :
    ∀ {G : Type u} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
      (f : P → ℝ → G), ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry f) →
      ContDiff ℝ (⊤ : ℕ∞) (fun y : P => ∫ s in a..b, f y s) := by
  intro G _ _ _ f hf
  rw [contDiff_iff_forall_nat_le]
  intro m _
  exact contDiff_intervalIntegral_parametric m f
    (hf.of_le (WithTop.coe_le_coe.mpr (le_top : (m : ℕ∞) ≤ ⊤)))

/-- The fixed-interval integral identity: the divided difference is the average of
`deriv h` along the segment `[u, σ]`.  (On the diagonal both sides are `deriv h u`.) -/
lemma dslope_eq_integral_deriv (h : ℝ → ℝ) (hh : ContDiff ℝ (⊤ : ℕ∞) h) (u σ : ℝ) :
    dslope h u σ = ∫ t in (0 : ℝ)..1, deriv h (u + t * (σ - u)) := by
  have hder : Continuous (deriv h) := by
    have hd : ContDiff ℝ (⊤ : ℕ∞) (deriv h) := by
      simpa only [Function.iterate_one] using hh.iterate_deriv 1
    exact hd.continuous
  rcases eq_or_ne σ u with hσu | hne
  · rw [hσu, dslope_same]
    have hfun : (fun t : ℝ => deriv h (u + t * (u - u))) = fun _ : ℝ => deriv h u := by
      funext t
      simp
    rw [hfun, intervalIntegral.integral_const]
    simp
  · rw [dslope_of_ne h hne, slope_def_field]
    have hc : σ - u ≠ 0 := sub_ne_zero.mpr hne
    have hkey : (∫ t in (0 : ℝ)..1, deriv h (u + t * (σ - u)))
        = (σ - u)⁻¹ * (h σ - h u) := by
      have hcongr : (∫ t in (0 : ℝ)..1, deriv h (u + t * (σ - u)))
          = ∫ t in (0 : ℝ)..1, deriv h ((σ - u) * t + u) := by
        apply intervalIntegral.integral_congr
        intro t _
        simp only [show u + t * (σ - u) = (σ - u) * t + u by ring]
      rw [hcongr,
        intervalIntegral.integral_comp_mul_add (f := fun x : ℝ => deriv h x) hc u,
        show (σ - u) * 0 + u = u by ring, show (σ - u) * 1 + u = σ by ring,
        intervalIntegral.integral_deriv_eq_sub
          (fun x _ => (hh.differentiable (by simp)) x)
          (hder.intervalIntegrable u σ),
        smul_eq_mul]
    rw [hkey, div_eq_mul_inv, mul_comm]

/-- **The divided difference of a smooth function is smooth.**

`dslope h u σ` is `(h σ - h u)/(σ - u)` for `σ ≠ u` and `deriv h u` for `σ = u`; as a
function of the pair `(u,σ)` it is `C^∞` whenever `h` is.

Proof plan: for `u ≠ σ`, `dslope h u σ = ∫_0^1 deriv h (u + τ * (σ - u)) dτ` (the substitution
`v = u + τ(σ-u)` in `∫_u^σ deriv h`), and both sides also agree on the diagonal with value
`deriv h u`.  A parametric integral `(u,σ) ↦ ∫_0^1 F (u,σ,τ) dτ` of a jointly smooth `F` is
itself smooth: differentiate under the integral sign with
`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`, all partial derivatives
of `F` being bounded on a compact neighbourhood of the parameter domain, and iterate. -/
theorem contDiff_dslope (h : ℝ → ℝ) (hh : ContDiff ℝ (⊤ : ℕ∞) h) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => dslope h q.1 q.2) := by
  have hd : ContDiff ℝ (⊤ : ℕ∞) (deriv h) := by
    simpa only [Function.iterate_one] using hh.iterate_deriv 1
  have hinner : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : (ℝ × ℝ) × ℝ => z.1.1 + z.2 * (z.1.2 - z.1.1)) := by fun_prop
  have hF : ContDiff ℝ (⊤ : ℕ∞)
      (Function.uncurry (fun (p : ℝ × ℝ) (t : ℝ) => deriv h (p.1 + t * (p.2 - p.1)))) := by
    have hEq : Function.uncurry (fun (p : ℝ × ℝ) (t : ℝ) => deriv h (p.1 + t * (p.2 - p.1)))
        = fun z : (ℝ × ℝ) × ℝ => deriv h (z.1.1 + z.2 * (z.1.2 - z.1.1)) := rfl
    rw [hEq]
    exact hd.comp hinner
  have hG : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : ℝ × ℝ => ∫ t in (0 : ℝ)..1, deriv h (q.1 + t * (q.2 - q.1))) :=
    contDiff_intervalIntegral_parametric_top
      (f := fun (p : ℝ × ℝ) (t : ℝ) => deriv h (p.1 + t * (p.2 - p.1))) hF
  have hfun : (fun q : ℝ × ℝ => dslope h q.1 q.2)
      = fun q : ℝ × ℝ => ∫ t in (0 : ℝ)..1, deriv h (q.1 + t * (q.2 - q.1)) := by
    funext q
    exact dslope_eq_integral_deriv h hh q.1 q.2
  rw [hfun]
  exact hG

end Work.Analysis.Calculus
