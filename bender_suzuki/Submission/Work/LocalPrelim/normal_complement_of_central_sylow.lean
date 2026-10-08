import Mathlib
import Submission.Work.NPC.Engine
import Submission.Work.NPC.Complement

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.LocalPrelim

/-- A central normal `p`-subgroup of index coprime to `p` (equivalently, a central Sylow
`p`-subgroup) has a normal complement.  Since `N` is central, Burnside's normal `p`-complement
theorem applies: `N` is a Sylow `p`-subgroup whose normalizer (`= G`) is contained in its
centralizer, so `G` has a normal `p`-complement `K`, and a normal `p`-complement is exactly a
complement of a Sylow `p`-subgroup. -/
theorem normal_complement_of_central_sylow {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (N : Subgroup G) [N.Normal] (hNp : IsPGroup p N) (hNd : ¬ p ∣ N.index)
    (hcen : N ≤ Subgroup.center G) : ∃ K : Subgroup G, K.Normal ∧ N.IsComplement' K := by
  -- `N` is a Sylow `p`-subgroup of `G`.
  let P : Sylow p G := hNp.toSylow hNd
  -- `G` centralizes `N` because `N` is contained in the centre of `G`.
  have hcent : (⊤ : Subgroup G) ≤ Subgroup.centralizer (N : Set G) := by
    rw [Subgroup.le_centralizer_iff]
    simpa [Subgroup.centralizer_univ] using hcen
  -- Burnside's normal `p`-complement theorem applies, since `N_G(P) ≤ G ≤ C_G(N) = C_G(P)`.
  have hburn : Work.NPC.HasNormalPComplement p G := by
    refine Work.NPC.burnside_npc P ?_
    exact le_top.trans hcent
  obtain ⟨K, hK⟩ := hburn
  -- A normal `p`-complement is a complement of any Sylow `p`-subgroup, in particular of `N`.
  refine ⟨K, hK.normal, ?_⟩
  exact (Work.NPC.Basic.isNormalPComplement_complement_sylow hK P).symm

end Work.LocalPrelim
