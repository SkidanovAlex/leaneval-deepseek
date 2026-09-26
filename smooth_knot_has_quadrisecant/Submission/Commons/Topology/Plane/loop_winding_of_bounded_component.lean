import Mathlib
import Submission.Commons.Topology.Plane.essential_loop_of_bounded_component

set_option autoImplicit false

namespace Commons.Topology.Plane

noncomputable section

open Set

/-- **A loop of non-zero winding number in the complement of a closed set with a bounded
component.**

If `K ⊆ ℂ` is closed, `0 ∈ K`, and the connected component of `0` in `K` is bounded, then there
is a loop `γ : Circle → ℂ` lying in `Kᶜ` which is **not** null-homotopic inside `ℂ \ {0}`: there
is `t₀ : Circle` such that there is no homotopy from `γ` to the constant loop at `γ t₀` whose
values never vanish.  In other words `γ` winds around `0` with non-zero winding number.

This is an instance of the classical planar duality: a bounded component of a closed set is
"surrounded" by an essential loop of the complement. -/
theorem loop_winding_of_bounded_component {K : Set ℂ} (hK : IsClosed K) (h0 : (0 : ℂ) ∈ K)
    (hbdd : Bornology.IsBounded (connectedComponentIn K 0)) :
    ∃ γ : C(Circle, ℂ), (∀ t, γ t ∈ Kᶜ) ∧ ∃ t₀ : Circle,
      ¬ ∃ H : C(Circle × Set.Icc (0 : ℝ) 1, ℂ),
        (∀ t, H (t, (0 : Set.Icc (0 : ℝ) 1)) = γ t) ∧
        (∀ t, H (t, (1 : Set.Icc (0 : ℝ) 1)) = γ t₀) ∧
        ∀ p : Circle × Set.Icc (0 : ℝ) 1, H p ≠ (0 : ℂ) := by
  -- The essential loop in `ℂ \ {0}` supplied by the shared commons.
  obtain ⟨γ₀, hγ₀mem, hγ₀ne⟩ :=
    Commons.Topology.Plane.essential_loop_of_bounded_component hK h0 hbdd
  refine ⟨⟨fun t => (γ₀ t : ℂ), continuous_subtype_val.comp γ₀.continuous⟩,
    fun t => hγ₀mem t, 1, ?_⟩
  rintro ⟨H, h0H, h1H, hneH⟩
  -- A null-homotopy of `γ` avoiding `0` is a null-homotopy of `γ₀` in `ℂ \ {0}`.
  apply hγ₀ne
  have hcont : Continuous fun p : Set.Icc (0 : ℝ) 1 × Circle =>
      (⟨H (p.2, p.1), hneH (p.2, p.1)⟩ : {z : ℂ // z ≠ 0}) :=
    Continuous.subtype_mk (H.continuous.comp (continuous_snd.prodMk continuous_fst))
      (fun p => hneH (p.2, p.1))
  refine ⟨γ₀ 1, ⟨⟨⟨fun p => ⟨H (p.2, p.1), hneH (p.2, p.1)⟩, hcont⟩,
    fun t => Subtype.ext (h0H t), fun t => Subtype.ext (h1H t)⟩⟩⟩

end

end Commons.Topology.Plane
