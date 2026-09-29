import Mathlib
import Submission.Work.A14D.LC_setup

/-!
# A14D — holomorphic extension of `Φ` from the upper half-disc to the full disc

If `Ψ` is holomorphic on the disc `ball (1/9) δ` and `Φ` is holomorphic on the upper half
`halfU δ = ball (1/9) δ ∩ {Im > 0}` of that disc with `Φ' = Ψ` there, then `Φ` is the
restriction of a function holomorphic on the whole disc.

The proof is the elementary one: `Ψ` has a primitive `F` on the disc (a disc is simply
connected, `DifferentiableOn.isExactOn_ball`), so `F - Φ` is holomorphic on the open
half-disc with derivative `0` everywhere; an open preconnected set on which the derivative
of a holomorphic function vanishes is a constant (`halfU δ` is convex, hence preconnected),
and subtracting that constant from `F` gives the extension.
-/

open Complex Metric
open scoped Topology

namespace Work.A14D

noncomputable section

/-- The upper half-disc `halfU δ = ball ninth δ ∩ {Im > 0}` is convex. -/
lemma convex_halfU_ext (δ : ℝ) : Convex ℝ (halfU δ) :=
  (convex_ball ninth δ).inter (convex_halfSpace_im_gt 0)

/-- The upper half-disc `halfU δ = ball ninth δ ∩ {Im > 0}` is open. -/
lemma isOpen_halfU_ext (δ : ℝ) : IsOpen (halfU δ) :=
  Metric.isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_im)

theorem exists_holo_ext_halfU {δ : ℝ} (hδ : 0 < δ) {Φ Ψ : ℂ → ℂ}
    (hΨ : DifferentiableOn ℂ Ψ (Metric.ball ninth δ))
    (hΦ : DifferentiableOn ℂ Φ (halfU δ))
    (hderiv : ∀ z ∈ halfU δ, HasDerivAt Φ (Ψ z) z) :
    ∃ B : ℂ → ℂ, DifferentiableOn ℂ B (Metric.ball ninth δ) ∧ ∀ z ∈ halfU δ, B z = Φ z := by
  -- `Ψ` has a primitive `F` on the disc.
  obtain ⟨F, hF⟩ := hΨ.isExactOn_ball
  have hFd : DifferentiableOn ℂ F (Metric.ball ninth δ) :=
    fun z hz => (hF z hz).differentiableAt.differentiableWithinAt
  have hsub : halfU δ ⊆ Metric.ball ninth δ := Set.inter_subset_left
  -- `F - Φ` is holomorphic on the half-disc with derivative `0`.
  have hGd : DifferentiableOn ℂ (fun z => F z - Φ z) (halfU δ) :=
    (hFd.mono hsub).sub hΦ
  have hG' : (halfU δ).EqOn (deriv fun z => F z - Φ z) 0 := by
    intro z hz
    have h1 : HasDerivAt (fun z => F z - Φ z) (Ψ z - Ψ z) z :=
      (hF z (hsub hz)).sub (hderiv z hz)
    rw [sub_self] at h1
    exact h1.deriv
  -- hence `F - Φ` is constant on the (preconnected) half-disc.
  obtain ⟨a, ha⟩ := (isOpen_halfU_ext δ).exists_is_const_of_deriv_eq_zero
    (convex_halfU_ext δ).isPreconnected hGd hG'
  refine ⟨fun z => F z - a, hFd.sub_const a, ?_⟩
  intro z hz
  have h := ha z hz
  rw [← h]; abel

end

end Work.A14D
