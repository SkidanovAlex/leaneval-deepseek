import Mathlib
import Submission.Commons.RepresentationTheory.TateCohomology.tateCohomology_neg_one_iso
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false
set_option autoImplicit false

open CategoryTheory

namespace NK.CFTLib

/-! ## The kernel description of `Ĥ⁻¹` in degree `-1` -/

variable {G : Type} [Group G] [Fintype G]

/-- The norm map of a representation commutes with intertwining maps. -/
theorem intertwiningMap_norm_apply {V W : Type} [AddCommGroup V] [Module ℤ V] [AddCommGroup W] [Module ℤ W]
    (ρ : Representation ℤ G V) (σ : Representation ℤ G W) (f : ρ.IntertwiningMap σ) (x : V) :
    f (Representation.norm ρ x) = Representation.norm σ (f x) := by
  have h1 : Representation.norm ρ x = ∑ g : G, ρ g x := by
    rw [Representation.norm, LinearMap.sum_apply]
  have h2 : Representation.norm σ (f x) = ∑ g : G, σ g (f x) := by
    rw [Representation.norm, LinearMap.sum_apply]
  rw [h1, h2, map_sum]
  exact Finset.sum_congr rfl fun g _ =>
    Representation.IntertwiningMap.isIntertwining ρ σ f g x

omit [Fintype G] in
/-- An intertwining map sends the augmentation submodule of its source into that of its target. -/
theorem map_coinvariantsKer_le {V W : Type} [AddCommGroup V] [Module ℤ V] [AddCommGroup W]
    [Module ℤ W] (ρ : Representation ℤ G V) (σ : Representation ℤ G W)
    (f : ρ.IntertwiningMap σ) :
    Submodule.map f.toLinearMap (Representation.Coinvariants.ker ρ) ≤
      Representation.Coinvariants.ker σ := by
  rw [Representation.Coinvariants.ker, Representation.Coinvariants.ker, Submodule.map_span]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨x, ⟨⟨g, v⟩, rfl⟩, rfl⟩
  change f (ρ g v - v) ∈ Representation.Coinvariants.ker σ
  rw [map_sub, Representation.IntertwiningMap.isIntertwining ρ σ f g v]
  exact Representation.Coinvariants.sub_mem_ker g (f v)

/-- `Ĥ⁻¹(G,V) = 0` implies `ker(N) ⊆ I_G V`. -/
theorem ker_norm_le_coinvariantsKer_of_subsingleton {V : Type} [AddCommGroup V] [Module ℤ V]
    (ρ : Representation ℤ G V) (h : Subsingleton (tateCohomology (Rep.of ρ) (-1))) :
    LinearMap.ker (Representation.norm ρ) ≤ Representation.Coinvariants.ker ρ := by
  letI : Module ℤ ↥(LinearMap.ker (Representation.norm ρ)) :=
    (LinearMap.ker (Representation.norm ρ)).module
  obtain ⟨e⟩ := Commons.RepresentationTheory.TateCohomology.tateCohomology_neg_one_iso ρ
  haveI hsub : Subsingleton ((LinearMap.ker (Representation.norm ρ)) ⧸
      (Submodule.comap (LinearMap.ker (Representation.norm ρ)).subtype
        (Submodule.span ℤ (Set.range fun p : G × V => ρ p.1 p.2 - p.2)))) :=
    e.symm.injective.subsingleton
  have htop : (Submodule.comap (LinearMap.ker (Representation.norm ρ)).subtype
      (Submodule.span ℤ (Set.range fun p : G × V => ρ p.1 p.2 - p.2))) = ⊤ :=
    Submodule.Quotient.subsingleton_iff.mp hsub
  have htop' : (Submodule.comap (LinearMap.ker (Representation.norm ρ)).subtype
      (Representation.Coinvariants.ker ρ)) = ⊤ := by
    rw [Representation.Coinvariants.ker]
    exact htop
  exact Submodule.comap_subtype_eq_top.mp htop'

/-- Conversely, `ker(N) ⊆ I_G V` forces `Ĥ⁻¹(G,V) = 0`. -/
theorem subsingleton_tateCohomology_neg_one_of_ker_le {V : Type} [AddCommGroup V] [Module ℤ V]
    (ρ : Representation ℤ G V)
    (h : LinearMap.ker (Representation.norm ρ) ≤ Representation.Coinvariants.ker ρ) :
    Subsingleton (tateCohomology (Rep.of ρ) (-1)) := by
  letI : Module ℤ ↥(LinearMap.ker (Representation.norm ρ)) :=
    (LinearMap.ker (Representation.norm ρ)).module
  obtain ⟨e⟩ := Commons.RepresentationTheory.TateCohomology.tateCohomology_neg_one_iso ρ
  have htop : (Submodule.comap (LinearMap.ker (Representation.norm ρ)).subtype
      (Representation.Coinvariants.ker ρ)) = ⊤ :=
    Submodule.comap_subtype_eq_top.mpr h
  have htop' : (Submodule.comap (LinearMap.ker (Representation.norm ρ)).subtype
      (Submodule.span ℤ (Set.range fun p : G × V => ρ p.1 p.2 - p.2))) = ⊤ := by
    rw [Representation.Coinvariants.ker] at htop
    exact htop
  haveI : Subsingleton ((LinearMap.ker (Representation.norm ρ)) ⧸
      (Submodule.comap (LinearMap.ker (Representation.norm ρ)).subtype
        (Submodule.span ℤ (Set.range fun p : G × V => ρ p.1 p.2 - p.2)))) :=
    Submodule.Quotient.subsingleton_iff.mpr htop'
  exact e.injective.subsingleton

/-! ## The covering lemma -/

theorem subsingleton_tateCohomology_neg_one_of_cover {G : Type} [Group G] [Fintype G] {ι : Type}
    (M : Rep ℤ G) (M' : ι → Rep ℤ G) (φ : ∀ i, M' i ⟶ M)
    (hφ : ∀ i, Function.Injective (⇑(φ i).hom : (M' i).V → M.V))
    (hcov : ∀ x : M.V, ∃ i, ∃ y : (M' i).V, (φ i).hom y = x)
    (h : ∀ i, Subsingleton (tateCohomology (M' i) (-1))) :
    Subsingleton (tateCohomology M (-1)) := by
  classical
  letI : Module ℤ M.V := M.hV2
  have hker : LinearMap.ker (Representation.norm M.ρ) ≤ Representation.Coinvariants.ker M.ρ := by
    intro x hx
    obtain ⟨i, y, hy⟩ := hcov x
    letI : Module ℤ (M' i).V := (M' i).hV2
    have hNy : Representation.norm (M' i).ρ y = 0 := by
      apply hφ i
      rw [intertwiningMap_norm_apply (M' i).ρ M.ρ (φ i).hom y, hy, LinearMap.mem_ker.mp hx, map_zero]
    have hyI : y ∈ Representation.Coinvariants.ker (M' i).ρ :=
      ker_norm_le_coinvariantsKer_of_subsingleton (M' i).ρ (h i) hNy
    exact map_coinvariantsKer_le (M' i).ρ M.ρ (φ i).hom ⟨y, hyI, hy⟩
  exact subsingleton_tateCohomology_neg_one_of_ker_le M.ρ hker

end NK.CFTLib
