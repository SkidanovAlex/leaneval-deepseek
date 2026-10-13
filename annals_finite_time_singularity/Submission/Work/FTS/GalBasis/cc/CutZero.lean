/-
# `Work.FTS.GalBasis.cc.CutZero` — iterates of locally constant functions

The `D_z`- and `D_θ`-iterates of a function which is *locally constant* at a point (in the
relevant variable) vanish there.  This is the mechanism by which the *plateau* value `ψ = 1` of
a cutoff and the layer-constancy of its angular step propagate to the derivatives.

The module is deliberately free of any dependency on the `CutSpec` structure (*), so that
`cc.psiCut_layer_zero` — which sits on the import path of the proof `cc.psiCut_spec` of the
cutoff's specification — can use it without importing `cc.CutSpec`.  Before the split the two
lemmas lived in `cc.CutSpec`, which forced `cc.CutSpec` to obtain `psiCut_spec` from a scratch
`axiom`, and thus made the axiom part of the dependency closure of the main theorem.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.GalBasis.cc.CutDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalBasis.cc

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The `D_z`-iterates of a function which is *locally constant in `z`* vanish. -/
theorem DzIter_eq_zero_of_isOpen_const (f : ℝ → ℝ → ℝ) (U : Set ℝ) (hU : IsOpen U) (θ : ℝ)
    (hconst : ∀ z' z'' : ℝ, z' ∈ U → z'' ∈ U → f z' θ = f z'' θ) :
    ∀ (k : ℕ) (z : ℝ), z ∈ U → 1 ≤ k → Work.Spaces.DzIter k f z θ = 0 := by
  intro k
  induction k with
  | zero => intro z _ hk; exact absurd hk (by norm_num)
  | succ k ih =>
      intro z hz hk
      rw [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
      have h0 : deriv (fun z' => Work.Spaces.DzIter k f z' θ) z = 0 := by
        rcases Nat.eq_zero_or_pos k with hk0 | hkpos
        · subst hk0
          rw [Work.Spaces.DzIter_zero]
          have hev : (fun z' => f z' θ) =ᶠ[𝓝 z] (fun _ => f z θ) := by
            filter_upwards [hU.mem_nhds hz] with z' hz'
            exact hconst z' z hz' hz
          rw [hev.deriv_eq, deriv_const]
        · have hev : (fun z' => Work.Spaces.DzIter k f z' θ) =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
            filter_upwards [hU.mem_nhds hz] with z' hz'
            exact ih z' hz' hkpos
          rw [hev.deriv_eq, deriv_const]
      rw [h0, mul_zero]

/-- The `D_θ`-iterates of a function which is *locally constant in `θ`* vanish. -/
theorem DthIter_eq_zero_of_isOpen_const (f : ℝ → ℝ → ℝ) (U : Set ℝ) (hU : IsOpen U) (z : ℝ)
    (hconst : ∀ θ' θ'' : ℝ, θ' ∈ U → θ'' ∈ U → f z θ' = f z θ'') :
    ∀ (k : ℕ) (θ : ℝ), θ ∈ U → 1 ≤ k → Work.Spaces.DthIter k f z θ = 0 := by
  intro k
  induction k with
  | zero => intro θ _ hk; exact absurd hk (by norm_num)
  | succ k ih =>
      intro θ hθ hk
      rw [Work.Spaces.DthIter_succ, Work.Spaces.Dth, Work.Spaces.pth]
      have h0 : deriv (fun θ' => Work.Spaces.DthIter k f z θ') θ = 0 := by
        rcases Nat.eq_zero_or_pos k with hk0 | hkpos
        · subst hk0
          rw [Work.Spaces.DthIter_zero]
          have hev : (fun θ' => f z θ') =ᶠ[𝓝 θ] (fun _ => f z θ) := by
            filter_upwards [hU.mem_nhds hθ] with θ' hθ'
            exact hconst θ' θ hθ' hθ
          rw [hev.deriv_eq, deriv_const]
        · have hev : (fun θ' => Work.Spaces.DthIter k f z θ') =ᶠ[𝓝 θ] (fun _ => (0 : ℝ)) := by
            filter_upwards [hU.mem_nhds hθ] with θ' hθ'
            exact ih θ' hθ' hkpos
          rw [hev.deriv_eq, deriv_const]
      rw [h0, mul_zero]

/-- The `D_z`-iterates (of positive order) of a function which is locally constant in `z` at a
point vanish there. -/
theorem DzIter_eq_zero_of_eventually_const (f : ℝ → ℝ → ℝ) {z θ : ℝ}
    (h : ∀ᶠ z' in 𝓝 z, f z' θ = f z θ) (k : ℕ) (hk : 1 ≤ k) :
    Work.Spaces.DzIter k f z θ = 0 := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp h
  refine DzIter_eq_zero_of_isOpen_const f (Metric.ball z ε) Metric.isOpen_ball θ ?_ k z
    (Metric.mem_ball_self hε) hk
  intro z' z'' hz' hz''
  rw [hball hz', hball hz'']

/-- The `D_θ`-iterates (of positive order) of a function which is locally constant in `θ` at a
point vanish there. -/
theorem DthIter_eq_zero_of_eventually_const (f : ℝ → ℝ → ℝ) {z θ : ℝ}
    (h : ∀ᶠ θ' in 𝓝 θ, f z θ' = f z θ) (k : ℕ) (hk : 1 ≤ k) :
    Work.Spaces.DthIter k f z θ = 0 := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp h
  refine DthIter_eq_zero_of_isOpen_const f (Metric.ball θ ε) Metric.isOpen_ball z ?_ k θ
    (Metric.mem_ball_self hε) hk
  intro θ' θ'' hθ' hθ''
  rw [hball hθ', hball hθ'']

end Work.FTS.GalBasis.cc
