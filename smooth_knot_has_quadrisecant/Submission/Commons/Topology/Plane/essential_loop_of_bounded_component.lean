import Mathlib
import Submission.Commons.Topology.Jordan.annulus_no_spanning
import Submission.Commons.Topology.Plane.annulus_essential_loop_of_no_spanning

set_option autoImplicit false

open Set Metric
open scoped Topology

namespace Commons.Topology.Plane

/-- **An essential loop outside a closed set with a bounded component.**

Let `K ⊆ ℂ` be closed with `0 ∈ K` and with the connected component of `0` in `K` bounded.  Then
there is a loop `γ : Circle → ℂ \ {0}` lying in the complement of `K` which is not null-homotopic,
i.e. which winds around `0` with non-zero winding number.

Proof: `Commons.Topology.Jordan.annulus_no_spanning` supplies radii `0 < a < b` around `0` such
that no preconnected subset of `K` meets both circles `{|z| = a}` and `{|z| = b}`.  Applying the
annulus duality `Commons.Topology.Plane.annulus_essential_loop_of_no_spanning` to the closed set
`K ∩ {a ≤ ‖z‖ ≤ b}` (whose preconnected subsets are preconnected subsets of `K`) produces an
essential loop inside the annulus `{a ≤ ‖z‖ ≤ b}` avoiding `K ∩ {a ≤ ‖z‖ ≤ b}`; as the loop stays
in the annulus it also avoids all of `K`. -/
theorem essential_loop_of_bounded_component {K : Set ℂ} (hK : IsClosed K) (h0 : (0 : ℂ) ∈ K)
    (hbdd : Bornology.IsBounded (connectedComponentIn K 0)) :
    ∃ γ : C(Circle, {z : ℂ // z ≠ 0}),
      (∀ t, (γ t : ℂ) ∈ Kᶜ) ∧ ¬ γ.Nullhomotopic := by
  obtain ⟨a, b, ha, hab, hns⟩ := Commons.Topology.Jordan.annulus_no_spanning hK h0 hbdd
  set A : Set ℂ := {z : ℂ | a ≤ ‖z‖} ∩ {z : ℂ | ‖z‖ ≤ b} with hA
  set L : Set ℂ := K ∩ A with hL
  have hAclosed : IsClosed A :=
    (isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)
  have hLclosed : IsClosed L := hK.inter hAclosed
  have hLsub : L ⊆ {z : ℂ | a ≤ ‖z‖ ∧ ‖z‖ ≤ b} := by
    rintro z ⟨-, hzA⟩
    exact hzA
  have hjoin : ∀ C : Set ℂ, C ⊆ L → IsPreconnected C →
      (C ∩ {z : ℂ | ‖z‖ = a}).Nonempty → (C ∩ {z : ℂ | ‖z‖ = b}).Nonempty → False := by
    intro C hC hCpre h1 h2
    exact hns C (fun z hz => (hC hz).1) hCpre h1 h2
  obtain ⟨γ, hγ, hγne⟩ :=
    Commons.Topology.Plane.annulus_essential_loop_of_no_spanning hLclosed ha hab hLsub hjoin
  refine ⟨γ, ?_, hγne⟩
  intro t hmem
  obtain ⟨h1, h2, h3⟩ := hγ t
  exact h3 ⟨hmem, h1, h2⟩

end Commons.Topology.Plane
