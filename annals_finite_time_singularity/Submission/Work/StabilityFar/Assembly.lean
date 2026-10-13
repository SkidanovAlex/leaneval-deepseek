/-
# `Work.StabilityFar.Assembly` — the `fts` assembly

This is the assembly of the main theorem from the *named inputs* of all the delivered areas: the
LWP/continuation chapter, the construction and the Stability bootstrap (`St0`–`St3`), and the
`St4`/`St5` far-field and BKM results of this chapter.

The hypotheses are collected in `Work.StabilityFar.AssemblyInputs`: a solution `u` on `[0,T*)`
with datum `u₀`, its vorticity `ω`, the compact-support/decay data (`St4`'s inputs), the
regularity of the solution in the *core* (where the self-similar profile lives — this is the
content of the construction, and it is what `St4` does *not* prove), and the BKM lower bound
(`St5`'s input).  The conclusions are

* `Work.StabilityFar.stability_strip_holder` — the joint `C^{1,α}` regularity on every strip
  `univ ×ˢ Icc 0 S`, `S < T*`, obtained by gluing the far-field bound `St4` to the core bound;
* `Work.StabilityFar.stability_bkm_divergence` — the divergence of the BKM integral at `T*`;
* `Work.StabilityFar.theorem1_shape_of_inputs` — the `(p,u)`-shape of `theorem_1` at `T*`;
* `Work.StabilityFar.theorem_1_of_inputs` — **the exact statement of `theorem_1`**, from the
  named inputs together with the scaling input `EulerScalingToUnit` that moves the blow-up time
  to `1` (the lead's wiring into `Submission.lean`).
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.StabilityFar.St4
import Submission.Work.StabilityFar.St4Refine
import Submission.Work.StabilityFar.St5
import Submission.Work.StabilityFar.FarDerivLipschitz
import Submission.Work.StabilityFar.St4.isContDiffHolderOn_glue

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

set_option autoImplicit false

namespace Work.StabilityFar

/-- The two-sided windows are monotone in the time horizon. -/
theorem window_mono {S T : ℝ} (h : S ≤ T) : window S ⊆ window T :=
  fun t ht => ⟨ht.1, by linarith [ht.2]⟩

/-- **The input package of the assembly.**  Every field is a precisely named statement about the
constructed solution; `NOTES.md` records, for each, which area delivers it. -/
structure AssemblyInputs (α : NNReal) where
  /-- the maximal time `T*` of the constructed solution -/
  T : ℝ
  /-- `T* > 0` -/
  hT : 0 < T
  /-- the support radius of the vorticity -/
  R : ℝ
  /-- `R > 0` -/
  hR : 0 < R
  /-- the `L^∞` bound for `ω` -/
  M : ℝ
  /-- `M ≥ 0` -/
  hM : 0 ≤ M
  /-- the `L^∞` bound for `∂ₜω` -/
  M₁ : ℝ
  /-- `M₁ ≥ 0` -/
  hM₁ : 0 ≤ M₁
  /-- the time-Hölder constant of `ω` on the support ball -/
  H : ℝ
  /-- `H ≥ 0` -/
  hH : 0 ≤ H
  /-- the time-Hölder constant of `∂ₜω` on the support ball -/
  H₁ : ℝ
  /-- `H₁ ≥ 0` -/
  hH₁ : 0 ≤ H₁
  /-- the constant of the `St5` lower bound for the vorticity sup-norm -/
  c : ℝ
  /-- `c > 0` -/
  hc : 0 < c
  /-- the initial datum -/
  u₀ : R3 → R3
  /-- the pressure -/
  p : R3 → ℝ → ℝ
  /-- the velocity -/
  u : R3 → ℝ → R3
  /-- the vorticity -/
  ω : R3 → ℝ → R3
  /-- the datum is divergence-free -/
  div_u₀ : div u₀ = 0
  /-- the datum is odd -/
  odd_u₀ : IsOdd u₀
  /-- the datum is `C^{1,α}` -/
  cdh_u₀ : IsContDiffHolder ℝ α u₀
  /-- the vorticity of the datum decays like `‖x‖^{-α}` -/
  vortDecay_u₀ : ∃ C : ℝ, 0 < C ∧ ∀ x : R3, ‖vorticity u₀ x‖ ≤ C / (‖x‖ ^ (α : ℝ) + 1)
  /-- `(p,u)` solves the Euler equation on `[0,T*)` -/
  sol : IsLocalEulerEquationSolution p u₀ T u
  /-- the solution is odd at every time -/
  odd : ∀ t ∈ Set.Ico 0 T, IsOdd (u · t)
  /-- the solution is `C¹` near the (two-sided) window — from the construction -/
  smooth : ContDiffOn ℝ 1 u.uncurry (Set.univ ×ˢ Set.Ioo (-1) (T + 1))
  /-- **the core regularity** of the construction (`St0`–`St3`): joint `C^{1,α}` on the ball of
  radius `2R+6` (the far-field argument supplies everything outside `2R+5`) -/
  core : ∀ S ∈ Set.Ioo 0 T,
    IsContDiffHolderOn ℝ α u.uncurry (coreRegion (st4Radius R + 1) ×ˢ Set.Icc 0 S)
  /-- `u(·,t) = BS(ω(·,t))` -/
  bsSlice : IsBiotSavartSlice u ω T
  /-- `∂ₜu(·,t) = BS(∂ₜω(·,t))` (differentiation under the Biot–Savart integral) -/
  bsTimeSlice : IsTimeBiotSavartSlice u ω T
  /-- the vorticity is supported in `B(0,R)` -/
  supp : SlicesSupported ω R T
  /-- the vorticity is bounded by `M` -/
  bdd : SlicesBounded ω M T
  /-- `∂ₜω` is bounded by `M₁` -/
  bddDt : SlicesBounded (timeDeriv ω) M₁ T
  /-- `ω` is measurable slicewise -/
  meas : SlicesMeasurable ω T
  /-- `∂ₜω` is measurable slicewise -/
  measDt : SlicesMeasurable (timeDeriv ω) T
  /-- `ω` is `α`-Hölder in time on the support ball -/
  th : TimeHolderOnBall (α : ℝ) ω R T H
  /-- `∂ₜω` is `α`-Hölder in time on the support ball -/
  thDt : TimeHolderOnBall (α : ℝ) (timeDeriv ω) R T H₁
  /-- **`St5`'s input**: `‖ω(·,t)‖_∞ ≥ c/(T*-t)` -/
  linfLower : VortLinfLower u T c
  /-- the interval-integrability needed by the BKM comparison -/
  bkmIntegrable : ∀ t ∈ Set.Ico 0 T, IntervalIntegrable (Work.LWP.vortLInf u) volume 0 t

variable {α : NNReal}

/-- **The joint `C^{1,α}` regularity of the constructed solution on every strip.**

`St4` bounds the far-field part of `fderiv u.uncurry` (`farRegion (2R+5)`), the construction
bounds the core part (`coreRegion (2R+6)`), and the two cover `ℝ³`; the gluing
(`Work.StabilityFar.St4.isContDiffHolderOn_glue`) gives the whole strip. -/
theorem stability_strip_holder (D : AssemblyInputs α) (hα : 0 < (α : ℝ)) (hα1 : (α : ℝ) ≤ 1) :
    ∀ S ∈ Set.Ioo 0 D.T,
      IsContDiffHolderOn ℝ α D.u.uncurry (Set.univ ×ˢ Set.Icc 0 S) := by
  intro S hS
  have hST : S ≤ D.T := le_of_lt hS.2
  have hwin : window S ⊆ window D.T := window_mono hST
  have hfar : IsContDiffHolderOn ℝ α D.u.uncurry (farRegion (st4Radius D.R) ×ˢ Set.Icc 0 S) :=
    st4_farField_holder_of_vorticity (α := α) (ω := D.ω) (u := D.u) (T := S) (R := D.R)
      (M := D.M) (M₁ := D.M₁) (H := D.H) (H₁ := D.H₁)
      hS.1 hα hα1 D.hR D.hM D.hM₁ D.hH D.hH₁
      (D.smooth.mono (fun p hp => ⟨trivial, ⟨by linarith [hp.2.1], by linarith [hp.2.2]⟩⟩))
      (fun t ht => D.bsSlice t (hwin ht)) (fun t ht => D.bsTimeSlice t (hwin ht))
      (fun t ht => D.supp t (hwin ht)) (fun t ht => D.bdd t (hwin ht))
      (fun t ht => D.meas t (hwin ht))
      (fun t ht => D.bddDt t (hwin ht)) (fun t ht => D.measDt t (hwin ht))
      (fun z hz t ht τ hτ => D.th z hz t (hwin ht) τ (hwin hτ))
      (fun z hz t ht τ hτ => D.thDt z hz t (hwin ht) τ (hwin hτ))
  exact St4.isContDiffHolderOn_glue (ρ := st4Radius D.R) (ρ' := st4Radius D.R + 1) (T := S)
    (by simp only [st4Radius]; linarith [D.hR]) (by simp only [st4Radius]; linarith)
    (D.core S hS) hfar

/-- **The divergence of the BKM integral at the maximal time** (`St5`). -/
theorem stability_bkm_divergence (D : AssemblyInputs α) :
    Filter.Tendsto (Work.LWP.bkm D.u) (𝓝[<] D.T) Filter.atTop :=
  bkm_divergence_of_vortLinfLower D.hT D.hc D.linfLower D.bkmIntegrable

/-- **The `(p,u)`-shape of `theorem_1` at the constructed maximal time `T*`.** -/
theorem theorem1_shape_of_inputs (D : AssemblyInputs α) (hα : 0 < (α : ℝ)) (hα1 : (α : ℝ) ≤ 1) :
    ∃ p : R3 → ℝ → ℝ, ∃ u : R3 → ℝ → R3,
      (∀ t ∈ Set.Ico 0 D.T, IsOdd (u · t)) ∧
      IsLocalEulerEquationSolution p D.u₀ D.T u ∧
      (∀ S ∈ Set.Ioo 0 D.T, IsContDiffHolderOn ℝ α u.uncurry (Set.univ ×ˢ Set.Icc 0 S)) ∧
      Filter.Tendsto (Work.LWP.bkm u) (𝓝[<] D.T) Filter.atTop :=
  ⟨D.p, D.u, D.odd, D.sol, stability_strip_holder D hα hα1, stability_bkm_divergence D⟩

/-- **The `(p,u)`-shape of `theorem_1` at the blow-up time `1`**, from the scaling input. -/
theorem theorem1_shape_of_inputs_scaled (D : AssemblyInputs α) (hα : 0 < (α : ℝ))
    (hα1 : (α : ℝ) ≤ 1) (hscl : EulerScalingToUnit) :
    ∃ u₀' : R3 → R3, ∃ p' : R3 → ℝ → ℝ, ∃ u' : R3 → ℝ → R3,
      div u₀' = 0 ∧ IsOdd u₀' ∧ IsContDiffHolder ℝ α u₀' ∧
      (∃ C : ℝ, 0 < C ∧ ∀ x : R3, ‖vorticity u₀' x‖ ≤ C / (‖x‖ ^ (α : ℝ) + 1)) ∧
      (∀ t ∈ Set.Ico 0 1, IsOdd (u' · t)) ∧
      IsLocalEulerEquationSolution p' u₀' 1 u' ∧
      (∀ S ∈ Set.Ioo 0 1, IsContDiffHolderOn ℝ α u'.uncurry (Set.univ ×ˢ Set.Icc 0 S)) ∧
      Filter.Tendsto (fun t => ∫ s in 0..t, ⨆ x, ‖vorticity (fun y => u' y s) x‖) (𝓝[<] 1)
        Filter.atTop := by
  obtain ⟨u₀', p', u', h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
    hscl α D.u₀ D.T D.p D.u D.sol D.odd (stability_strip_holder D hα hα1)
      (stability_bkm_divergence D)
  exact ⟨u₀', p', u', h1, h2, h3, h4, h5, h6, h7, h8⟩

/-- **THE ASSEMBLY: `theorem_1`, exactly as stated in the challenge, from the named inputs.** -/
theorem theorem_1_of_inputs {α : NNReal} (hα : 0 < (α : ℝ)) (hα1 : (α : ℝ) ≤ 1)
    (D : AssemblyInputs α) (hscl : EulerScalingToUnit) :
    ∃ β > 0, ∃ u₀, div u₀ = 0 ∧ IsOdd u₀ ∧ IsContDiffHolder ℝ β u₀ ∧
      (∃ C > 0, ∀ x, ‖vorticity u₀ x‖ ≤ C / (‖x‖ ^ (β : ℝ) + 1)) ∧
        ∃ p, ∃ u, (∀ t ∈ Set.Ico 0 1, IsOdd (u · t)) ∧
            IsLocalEulerEquationSolution p u₀ 1 u ∧
              (∀ T ∈ Set.Ioo 0 1, IsContDiffHolderOn ℝ β u.uncurry (Set.univ ×ˢ Set.Icc 0 T)) ∧
                Filter.Tendsto (fun t => ∫ s in 0..t, ⨆ x, ‖vorticity (fun y => u y s) x‖)
                  (𝓝[<] 1) Filter.atTop := by
  obtain ⟨u₀', p', u', h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
    theorem1_shape_of_inputs_scaled D hα hα1 hscl
  exact ⟨α, hα, u₀', h1, h2, h3, h4, p', u', h5, h6, h7, h8⟩

end Work.StabilityFar
