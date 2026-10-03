import Mathlib
import Submission.Work.ORHughesFree.Section6.TreeG
import Submission.Work.ORHughesFree.Rat.OfGroup
import Submission.Work.ORHughesFree.RatU.exists_decomp

namespace Work.ORHughesFree.Section6

open Work.ORHughesFree

variable {K : Type} [Field K] {G : Type} [Group G] {U : Type} [Ring U]

/-- The image under `Φ` of the group element `u` is a unit of `D = divisionClosure (Set.range φ)`
with inverse the image of `u⁻¹`: `Φ (ofGroup u) * Φ (ofGroup u⁻¹) = Φ (ofGroup (u * u⁻¹)) = 1`. -/
theorem Phi_ofGroup_mul_Phi_ofGroup_inv (φ : MonoidAlgebra K G →+* U) (u : Kˣ × G) :
    Phi φ (RatU.ofGroup u) * Phi φ (RatU.ofGroup u⁻¹) = 1 := by
  rw [← map_mul, ← RatU.ofGroup_mul, mul_inv_cancel, RatU.ofGroup_one, map_one]

/-- Multiplying a `G`-realiser by a group element does not change the `G`-complexity of its
image: `Rat.treeOfRat` of `α * ofGroup u` is `Rat.treeOfRat α` (`RatU.treeOfRat_mul_ofGroup`), so
the two sets of complexities of the realisers of `Φ α` and of `Φ α * φ(unitOf u)` are the same
(multiplication by `Φ (ofGroup u) = φ (unitOf u)` is a bijection of the realiser sets, with
inverse multiplication by `Φ (ofGroup u⁻¹)`). -/
theorem treeG_Phi_mul_ofGroup {K : Type} [Field K] {G : Type} [Group G] {U : Type} [Ring U]
    (φ : MonoidAlgebra K G →+* U) (α : RatU (Kˣ × G)) (u : Kˣ × G) :
    treeG φ (Phi φ (α * RatU.ofGroup u)) = treeG φ (Phi φ α) := by
  refine Tree.le_antisymm ?_ ?_
  · -- take a realiser `β` of `Φ α` of minimal complexity and multiply it by `u`
    obtain ⟨⟨β, hβ, hβt⟩, -⟩ := treeG_spec φ (Phi φ α)
    have hmem : Phi φ (β * RatU.ofGroup u) = Phi φ (α * RatU.ofGroup u) := by
      rw [map_mul, hβ, map_mul]
    have h := (treeG_spec φ (Phi φ (α * RatU.ofGroup u))).2 (β * RatU.ofGroup u) hmem
    rwa [RatU.treeOfRat_mul_ofGroup, hβt] at h
  · -- take a realiser `γ` of `Φ (α * ofGroup u)` and multiply it by `u⁻¹`
    obtain ⟨⟨γ, hγ, hγt⟩, -⟩ := treeG_spec φ (Phi φ (α * RatU.ofGroup u))
    have hmem : Phi φ (γ * RatU.ofGroup u⁻¹) = Phi φ α := by
      rw [map_mul, hγ, map_mul]
      rw [mul_assoc, Phi_ofGroup_mul_Phi_ofGroup_inv, mul_one]
    have h := (treeG_spec φ (Phi φ α)).2 (γ * RatU.ofGroup u⁻¹) hmem
    rwa [RatU.treeOfRat_mul_ofGroup, hγt] at h

end Work.ORHughesFree.Section6
