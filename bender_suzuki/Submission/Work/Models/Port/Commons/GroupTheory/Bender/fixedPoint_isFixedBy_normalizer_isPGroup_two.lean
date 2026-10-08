import Mathlib
import Submission.Work.Models.Port.Commons.GroupTheory.Bender.existsUnique_fixedPoint_isPGroup_two

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.GroupTheory.Bender

/-- If a finite group `G` of even order acts on a finite set `Ω` so that every involution
has a unique fixed point, then any nontrivial `2`-subgroup `P ≤ G` has a unique fixed point,
and this fixed point is fixed by the whole normalizer `N_G(P)`.

Indeed, `z` is the unique fixed point of `P`. For `n ∈ N_G(P)` and `g ∈ P` we have
`n⁻¹ * g * n ∈ P`, so `g` fixes `n • z`; hence `n • z` is a fixed point of `P`, and by
uniqueness `n • z = z`. -/
theorem fixedPoint_isFixedBy_normalizer_isPGroup_two {G Ω : Type*} [Group G] [Finite G]
    [MulAction G Ω] [Finite Ω] (heven : Even (Nat.card G))
    (hinv : ∀ t : G, orderOf t = 2 → ∃! x : Ω, t • x = x)
    {P : Subgroup G} (hP : IsPGroup 2 P) (hPne : P ≠ ⊥) {z : Ω}
    (hz : ∀ g : P, (g : G) • z = z) {n : G} (hn : n ∈ Subgroup.normalizer (P : Set G)) :
    n • z = z := by
  -- `P` has a unique fixed point `a`; since `z` is fixed by `P`, we have `z = a`.
  obtain ⟨a, _ha, huniq⟩ := existsUnique_fixedPoint_isPGroup_two heven hinv P hP hPne
  have hza : z = a := huniq z hz
  -- `n • z` is also a fixed point of `P`, because `n` normalizes `P`.
  have hfix : ∀ g : P, (g : G) • (n • z) = n • z := by
    intro g
    have hg' : n⁻¹ * (g : G) * n ∈ P :=
      ((Subgroup.mem_set_normalizer_iff'').mp hn (g : G)).mp g.2
    rw [← mul_smul]
    have hconj : (g : G) * n = n * (n⁻¹ * (g : G) * n) := by group
    rw [hconj, mul_smul]
    congr 1
    exact hz ⟨_, hg'⟩
  -- Uniqueness forces `n • z = a = z`.
  exact (huniq (n • z) hfix).trans hza.symm

end Commons.GroupTheory.Bender
