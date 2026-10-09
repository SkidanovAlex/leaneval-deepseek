import Submission.Commons.RepresentationTheory.TateCohomology.tateCohomology_neg_one_iso
import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open CategoryTheory

set_option linter.style.haveILetI false

namespace NK.GlobalCFTdeep

/-- **Periodicity in degree `-1` for a cyclic group.** For a finite cyclic group `G` and a
`ℤ[G]`-module `M`, the vanishing of `H¹(G, M)` implies the vanishing of `Ĥ⁻¹(G, M)`.

Indeed for cyclic `G = ⟨σ⟩` both groups compute `ker(N) / (σ - 1)M`:
`Commons.RepresentationTheory.TateCohomology.tateCohomology_neg_one_iso` identifies `Ĥ⁻¹(G,M)`
with `ker(N)/IM`, and `H¹(G,M) ≅ ker(N)/IM` is Mathlib's
`Rep.FiniteCyclicGroup.groupCohomologyIsoOdd` for `n = 1`, i.e. the homology of
`M --(ρ(g)-1)--> M --N--> M`.  Since `IsCyclic G` supplies a generator `g` with
`Subgroup.zpowers g = ⊤`, the image of the augmentation ideal is `(ρ(g)-1)M`.  So vanishing of
`H¹` gives `ker N ⊆ (ρ(g)-1)M`, hence `Ĥ⁻¹(G,M) = 0`. -/
theorem subsingleton_tateCohomology_neg_one_of_subsingleton_groupCohomology_one_cyclic
    {G : Type} [Group G] [Fintype G] [IsCyclic G] (M : Rep ℤ G)
    (h : Subsingleton (groupCohomology M 1)) :
    Subsingleton (tateCohomology M (-1)) := by
  classical
  -- `ℤ`-module structures, made available to typeclass search in the canonical form.
  letI : Module ℤ M.V := M.hV2
  letI : Module ℤ ↥(LinearMap.ker (Representation.norm M.ρ)) :=
    (LinearMap.ker (Representation.norm M.ρ)).module
  -- A finite cyclic group is commutative.
  letI : CommGroup G := IsCyclic.commGroup
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  -- **Step 1.** Every element of `ker N` lies in the image of `ρ(g) - 1`: the quotient map
  -- `ker N ⟶ H¹(G,M)` is zero because `H¹(G,M)` is a subsingleton.
  have hker : ∀ x : ↥(LinearMap.ker (Representation.norm M.ρ)),
      (x : ↑M) ∈ (Rep.Hom.hom (M.applyAsHom g - 𝟙 M)).range := by
    intro x
    have hx0 : (ConcreteCategory.hom
        (Rep.FiniteCyclicGroup.groupCohomologyπOdd M g hg 1 (by norm_num))) x = 0 :=
      Subsingleton.elim _ _
    exact (Rep.FiniteCyclicGroup.groupCohomologyπOdd_eq_zero_iff M g hg 1 (by norm_num) x).mp hx0
  -- **Step 2.** The image of `ρ(g) - 1` lies in the augmentation ideal `I = ⟨ρ(g')v - v⟩`.
  have hrange : ∀ y ∈ (Rep.Hom.hom (M.applyAsHom g - 𝟙 M)).range,
      y ∈ Submodule.span ℤ (Set.range fun p : G × ↑M => M.ρ p.1 p.2 - p.2) := by
    intro y hy
    rw [Representation.IntertwiningMap.mem_range] at hy
    obtain ⟨v, rfl⟩ := hy
    have hv : (Rep.Hom.hom (M.applyAsHom g - 𝟙 M)) v = M.ρ g v - v := by
      simp [Rep.sub_hom, Rep.applyAsHom_apply]
    rw [hv]
    exact Submodule.subset_span ⟨(g, v), rfl⟩
  -- **Step 3.** Hence `ker N / I` is a subsingleton.
  have hquot : Subsingleton (↥(LinearMap.ker (Representation.norm M.ρ)) ⧸
      Submodule.comap (LinearMap.ker (Representation.norm M.ρ)).subtype
        (Submodule.span ℤ (Set.range fun p : G × ↑M => M.ρ p.1 p.2 - p.2))) := by
    rw [Submodule.Quotient.subsingleton_iff, Submodule.eq_top_iff']
    intro x
    exact hrange (x : ↑M) (hker x)
  -- **Step 4.** `Ĥ⁻¹(G,M) ≅ ker N / I`, so it is a subsingleton too.
  obtain ⟨e⟩ := Commons.RepresentationTheory.TateCohomology.tateCohomology_neg_one_iso M.ρ
  have hsrc : Subsingleton (tateCohomology (Rep.of M.ρ) (-1)) := by
    refine ⟨fun a b => e.injective ?_⟩
    exact hquot.elim (e a) (e b)
  have hobj : (Rep.of M.ρ : Rep ℤ G) = M := rfl
  exact hobj ▸ hsrc

end NK.GlobalCFTdeep
