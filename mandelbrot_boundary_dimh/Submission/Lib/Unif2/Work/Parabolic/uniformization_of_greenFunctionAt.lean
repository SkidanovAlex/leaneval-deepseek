import Mathlib
import Submission.Lib.Unif2.Work.Parabolic.Deps

namespace Work.Parabolic

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

open Filter Set
open Classical

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

variable {z₀ : X} {E : X → ℝ} {Φ : X → ℂ}

/-- **Properness into the disc, from a Green function in the relative-compactness sense.**

If `E` is positive off `z₀`, `‖Φ x‖ = exp (-E x)` there, `Φ z₀ = 0`, and the *closures* of the
superlevel sets `{x | ε ≤ E x}` (`ε > 0`) are compact, then the preimage of every compact subset of
the open unit disc is compact.

This is `Submission.isCompact_preimage_of_green` with the strong hypothesis
`IsCompact {x | ε ≤ E x}` replaced by the satisfiable hypothesis
`IsCompact (closure {x | ε ≤ E x})`: the superlevel set `{x | ε ≤ E x}` is a *punctured*
neighbourhood of the pole, hence not closed, and one must adjoin `{z₀}` (contained in the closure
of every superlevel set of a genuine Green function) before taking the compact hull. -/
theorem isCompact_preimage_of_greenFunctionAt (hE : IsGreenFunctionAt (X := X) z₀ E)
    (hmod : ∀ x : X, x ≠ z₀ → ‖Φ x‖ = Real.exp (-(E x))) (hzero : Φ z₀ = 0)
    (hcont : Continuous Φ) {K : Set ℂ} (hK : IsCompact K)
    (hKsub : K ⊆ Metric.ball (0 : ℂ) 1) : IsCompact (Φ ⁻¹' K) := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · simp
  obtain ⟨w₀, hw₀K, hw₀max⟩ := hK.exists_isMaxOn hne continuous_norm.continuousOn
  set r : ℝ := ‖w₀‖ with hr
  have hw₀lt : r < 1 := by
    have h := hKsub hw₀K
    rw [Metric.mem_ball, dist_eq_norm, sub_zero] at h
    exact h
  have hrle : 0 ≤ r := norm_nonneg w₀
  have hclosed : IsClosed (Φ ⁻¹' K) := hK.isClosed.preimage hcont
  have hpre0 : Φ ⁻¹' {0} = {z₀} :=
    Submission.phi_preimage_zero (fun x hx => hE.pos hx) hmod hzero
  rcases eq_or_ne r 0 with hr0 | hrne
  · have hKsub' : K ⊆ {0} := by
      intro z hz
      have h1 : ‖z‖ ≤ r := hw₀max hz
      rw [hr0] at h1
      simp only [Set.mem_singleton_iff]
      exact norm_eq_zero.mp (le_antisymm h1 (norm_nonneg z))
    have hpre : Φ ⁻¹' K ⊆ {z₀} := by
      intro x hx
      have h2 : Φ x = 0 := hKsub' hx
      have hx0 : x ∈ Φ ⁻¹' {0} := by simpa using h2
      rwa [hpre0] at hx0
    exact IsCompact.of_isClosed_subset isCompact_singleton hclosed hpre
  · have hrpos : 0 < r := lt_of_le_of_ne hrle (Ne.symm hrne)
    have hlog : Real.log r < 0 := Real.log_neg hrpos hw₀lt
    have hcomp : IsCompact (closure {x : X | -Real.log r ≤ E x} ∪ {z₀} : Set X) :=
      (hE.isCompact_closure_level (by rw [neg_pos]; exact hlog)).union isCompact_singleton
    have hsub : Φ ⁻¹' K ⊆ (closure {x : X | -Real.log r ≤ E x} ∪ {z₀} : Set X) := by
      intro x hx
      rcases eq_or_ne x z₀ with rfl | hxne
      · exact Or.inr rfl
      · refine Or.inl (subset_closure ?_)
        have h1 : ‖Φ x‖ ≤ r := hw₀max hx
        rw [hmod x hxne, ← Real.exp_log hrpos] at h1
        have h2 : -(E x) ≤ Real.log r := Real.exp_le_exp.mp h1
        show -Real.log r ≤ E x
        linarith
    exact IsCompact.of_isClosed_subset hcomp hclosed hsub

/-- **The hyperbolic endgame, with the corrected (relative compactness) notion of Green function.**
The two `Diffeomorph` types below are Mathlib's plain `X ≃ₘ⟮mℂ, mℂ⟯ ℂ` and `X ≃ₘ⟮mℂ, mℂ⟯ ℍ`
(the level `((⊤ : ℕ∞) : WithTop ℕ∞)` is the `∞` of that notation).

This is `Submission.uniformization_of_green_modulus` with its hypothesis
`hinf : ∀ ε > 0, IsCompact {x | ε ≤ E x}` replaced by the correct one
(`IsGreenFunctionAt z₀ E`, i.e. compact *closures* of the superlevel sets), which is satisfiable —
the classical Green functions of the disc and the half plane satisfy it, while the strong
compactness condition (without closure) is unsatisfiable when `X` is non-compact and connected
(`Work.Parabolic.not_exists_hasGreenFunctionWeak_of_not_compact`).

Proof: exactly the proof of `Submission.uniformization_of_green_modulus`
(`Submission/GreenModulus.lean`), which only uses `hinf` to show that `Φ` is proper into the disc:
for a compact `K ⊆ 𝔻` the set `Φ ⁻¹' K` is contained in `{x | ε ≤ E x}` for `ε := -log (max ‖·‖ K)`
(when positive) and hence in the compact closure `closure {x | ε ≤ E x}`; being closed as well it is
compact, which is the properness needed by `Submission.uniformization_of_properInto_disc`.  The
helper `Submission.isCompact_preimage_of_green` needs the same one-line adaptation. -/
theorem uniformization_of_greenFunctionAt {X : Type*} [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] (hX : ¬ CompactSpace X) {z₀ : X} {E : X → ℝ}
    {Φ : X → ℂ} (hE : Work.Parabolic.IsGreenFunctionAt (X := X) z₀ E)
    (hΦ : Submission.HolomorphicOnX Φ Set.univ)
    (hmod : ∀ x : X, x ≠ z₀ → ‖Φ x‖ = Real.exp (-(E x)))
    (hpole : Submission.HasLogPoleAt z₀ Φ) :
    Nonempty (Diffeomorph (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) X ℂ
        ((⊤ : ℕ∞) : WithTop ℕ∞)) ∨
      Nonempty (Diffeomorph (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) X UpperHalfPlane
        ((⊤ : ℕ∞) : WithTop ℕ∞)) := by
  have hzero : Φ z₀ = 0 := Submission.phi_zero_of_logPole hΦ hpole
  have hpos : ∀ x : X, x ≠ z₀ → 0 < E x := fun x hx => hE.pos hx
  exact Submission.uniformization_of_properInto_disc hX
    (Submission.phi_mem_ball hpos hmod hzero)
    (fun K hK hKsub =>
      isCompact_preimage_of_greenFunctionAt hE hmod hzero hΦ.continuous hK hKsub)
    hΦ (Submission.phi_preimage_zero hpos hmod hzero)
    (Submission.phi_deriv_ne_zero_of_logPole hpole)

end Work.Parabolic
