import Mathlib
import Submission.Work.TMContract.Components

/-!
# C11: extracting the data of component C9 (`P_mAnalytic`)

Component C9 provides, on a spectral interval `(a,b)`, a *jointly* real-analytic family
`(E,x) ↦ (C E x, φ E x)` conjugating the almost Mathieu cocycle to rotations.  Two things are
needed downstream:

* at a *single* energy `E ∈ (a,b)`: a 1-variable analytic conjugacy `x ↦ C E x`, `x ↦ φ E x`
  (used to build reducible gauges and to solve the cohomological equation);
* the joint analyticity of `φ` itself, to complexify it (component C11's Fourier argument).
-/

open LeanEval.Analysis.TenMartini

set_option autoImplicit false

noncomputable section

namespace Work.TMComp.RedProj

open Work.TMContract

/-- The single-energy form of component C9's conclusion. -/
theorem data_of_mAnalytic (h9 : P_mAnalytic) (α lam a b E : ℝ)
    (hα : Irrational α) (h0 : 0 < lam) (h1 : lam ≤ 1) (hab : a < b)
    (hspec : Set.Ioo a b ⊆ amoSpec α lam) (hE : E ∈ Set.Ioo a b) :
    ∃ (C : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (φ : ℝ → ℝ),
      (∀ i j, AnalyticOnNhd ℝ (fun x => C x i j) Set.univ) ∧
      (∀ x, C (x + 1) = C x) ∧ (∀ x, (C x).det = 1) ∧ HasDegree C 0 ∧
      (∀ x, C (x + α) * tmR lam E x = rot (φ x) * C x) ∧
      AnalyticOnNhd ℝ φ Set.univ ∧ (∀ x, φ (x + 1) = φ x) := by
  obtain ⟨C, φ, hCan, hφan, hCp, hφp, hCdet, hCdeg, hconj⟩ :=
    h9 α lam a b hα h0 h1 hab hspec
  have hf : AnalyticOnNhd ℝ (fun x : ℝ => (E, x)) Set.univ :=
    analyticOnNhd_const.prod analyticOnNhd_id
  refine ⟨fun x => C E x, fun x => φ E x, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    exact (hCan i j).comp hf (fun x _ => ⟨hE, trivial⟩)
  · intro x; exact hCp E x
  · intro x; exact hCdet E hE x
  · exact hCdeg E hE
  · intro x; exact hconj E hE x
  · exact hφan.comp hf (fun x _ => ⟨hE, trivial⟩)
  · intro x; exact hφp E x

/-- The joint analyticity of C9's angle function `φ`, in the form needed to complexify it. -/
theorem joint_analytic_of_mAnalytic (h9 : P_mAnalytic) (α lam a b : ℝ)
    (hα : Irrational α) (h0 : 0 < lam) (h1 : lam ≤ 1) (hab : a < b)
    (hspec : Set.Ioo a b ⊆ amoSpec α lam) :
    ∃ (C : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ) (φ : ℝ → ℝ → ℝ),
      (∀ i j, AnalyticOnNhd ℝ (fun p : ℝ × ℝ => C p.1 p.2 i j) (Set.Ioo a b ×ˢ Set.univ)) ∧
      AnalyticOnNhd ℝ (fun p : ℝ × ℝ => φ p.1 p.2) (Set.Ioo a b ×ˢ Set.univ) ∧
      (∀ E x, C E (x + 1) = C E x) ∧ (∀ E x, φ E (x + 1) = φ E x) ∧
      (∀ E ∈ Set.Ioo a b, ∀ x, (C E x).det = 1) ∧
      (∀ E ∈ Set.Ioo a b, HasDegree (C E) 0) ∧
      (∀ E ∈ Set.Ioo a b, ∀ x, C E (x + α) * tmR lam E x = rot (φ E x) * C E x) :=
  h9 α lam a b hα h0 h1 hab hspec

end Work.TMComp.RedProj
