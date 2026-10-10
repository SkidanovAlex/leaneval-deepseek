import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
import Submission.NK.GlobalCFTdeep.Herbrand.natCard_tateCohomology_mul_of_shortExact
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option autoImplicit false

open CategoryTheory

noncomputable section

namespace NK.GlobalCFTdeep.Herbrand

/-- The "no finiteness" Tate hexagon cardinality relation: the same identity as
`natCard_tateCohomology_mul_of_shortExact`, but with no `Finite` hypotheses on the Tate
cohomology groups.  This is possible because the underlying counting identity
`cyclicExact_card_relation` is valid with the convention `Nat.card X = 0` for infinite `X`. -/
theorem tateCohomology_mul_eq_of_shortExact_noFin {G : Type} [CommGroup G] [Fintype G]
    [IsCyclic G] (S : CategoryTheory.ShortComplex (Rep ℤ G)) (hS : S.ShortExact) :
    Nat.card ↥(tateCohomology S.X₂ 0) * Nat.card ↥(tateCohomology S.X₁ 1) *
        Nat.card ↥(tateCohomology S.X₃ 1)
      = Nat.card ↥(tateCohomology S.X₁ 0) * Nat.card ↥(tateCohomology S.X₃ 0) *
        Nat.card ↥(tateCohomology S.X₂ 1) := by
  classical
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  have hper := perF_shortExact (k := ℤ) (G := G) g S hS
  have h23 : (ComplexShape.up ℕ).Rel 2 3 := by simp
  have h34 : (ComplexShape.up ℕ).Rel 3 4 := by simp
  have hαβ : LinearMap.range
        (HomologicalComplex.homologyMap ((perF (k:=ℤ) (G:=G) g).map S.f) 2).hom
      = LinearMap.ker
        (HomologicalComplex.homologyMap ((perF (k:=ℤ) (G:=G) g).map S.g) 2).hom :=
    (hper.homology_exact₂ 2).moduleCat_range_eq_ker
  have hβγ : LinearMap.range
        (HomologicalComplex.homologyMap ((perF (k:=ℤ) (G:=G) g).map S.g) 2).hom
      = LinearMap.ker (hper.δ 2 3 h23).hom :=
    (hper.homology_exact₃ 2 3 h23).moduleCat_range_eq_ker
  have hγδ : LinearMap.range (hper.δ 2 3 h23).hom
      = LinearMap.ker
        (HomologicalComplex.homologyMap ((perF (k:=ℤ) (G:=G) g).map S.f) 3).hom :=
    (hper.homology_exact₁ 2 3 h23).moduleCat_range_eq_ker
  have hδε : LinearMap.range
        (HomologicalComplex.homologyMap ((perF (k:=ℤ) (G:=G) g).map S.f) 3).hom
      = LinearMap.ker
        (HomologicalComplex.homologyMap ((perF (k:=ℤ) (G:=G) g).map S.g) 3).hom :=
    (hper.homology_exact₂ 3).moduleCat_range_eq_ker
  have hδ4 : LinearMap.range (hper.δ 3 4 h34).hom
      = LinearMap.ker
        (HomologicalComplex.homologyMap ((perF (k:=ℤ) (G:=G) g).map S.f) 4).hom :=
    (hper.homology_exact₁ 3 4 h34).moduleCat_range_eq_ker
  have hεδ : LinearMap.range
        (HomologicalComplex.homologyMap ((perF (k:=ℤ) (G:=G) g).map S.g) 3).hom
      = LinearMap.ker (hper.δ 3 4 h34).hom :=
    (hper.homology_exact₃ 3 4 h34).moduleCat_range_eq_ker
  -- pointwise naturality of the periodicity isomorphism
  have hnat : ∀ w : ↥(((perF (k:=ℤ) (G:=G) g).obj S.X₁).homology 2),
      (HomologicalComplex.homologyMap ((perF (k:=ℤ) (G:=G) g).map S.f) 4).hom
          ((perIso g S.X₁).hom w)
      = (perIso g S.X₂).hom
          ((HomologicalComplex.homologyMap ((perF (k:=ℤ) (G:=G) g).map S.f) 2).hom w) := by
    intro w
    have h := perIso_natural (G := G) g S.f
    have h' := congrArg (fun (t : ((perF (k:=ℤ) (G:=G) g).obj S.X₁).homology 2 ⟶
        ((perF (k:=ℤ) (G:=G) g).obj S.X₂).homology 4) => t.hom w) h
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h'
  have hεζ : LinearMap.range
        (HomologicalComplex.homologyMap ((perF (k:=ℤ) (G:=G) g).map S.g) 3).hom
      = LinearMap.ker (perZeta (G := G) g S hS h34) := by
    rw [hεδ]
    ext x
    change ((hper.δ 3 4 h34).hom x = 0) ↔
      ((perIso g S.X₁).inv ((hper.δ 3 4 h34).hom x) = 0)
    constructor
    · intro hx; rw [hx]; exact map_zero (ModuleCat.Hom.hom (perIso g S.X₁).inv)
    · intro hx
      have h1 : (perIso g S.X₁).hom ((perIso g S.X₁).inv ((hper.δ 3 4 h34).hom x))
          = (hper.δ 3 4 h34).hom x :=
        Iso.inv_hom_id_apply (perIso g S.X₁) ((hper.δ 3 4 h34).hom x)
      rw [← h1, hx]; exact map_zero (ModuleCat.Hom.hom (perIso g S.X₁).hom)
  have hζα : LinearMap.range (perZeta (G := G) g S hS h34)
      = LinearMap.ker
        (HomologicalComplex.homologyMap ((perF (k:=ℤ) (G:=G) g).map S.f) 2).hom := by
    ext y
    change (∃ x, perZeta (G := G) g S hS h34 x = y) ↔
      ((HomologicalComplex.homologyMap ((perF (k:=ℤ) (G:=G) g).map S.f) 2).hom y = 0)
    constructor
    · rintro ⟨x, hx⟩
      have hx' : (perIso g S.X₁).inv ((hper.δ 3 4 h34).hom x) = y := hx
      have hEy : (hper.δ 3 4 h34).hom x = (perIso g S.X₁).hom y := by
        rw [← hx']
        exact (Iso.inv_hom_id_apply (perIso g S.X₁) ((hper.δ 3 4 h34).hom x)).symm
      have h4z : (HomologicalComplex.homologyMap ((perF (k:=ℤ) (G:=G) g).map S.f) 4).hom
          ((hper.δ 3 4 h34).hom x) = 0 := by
        have hmem : ((hper.δ 3 4 h34).hom x) ∈
            LinearMap.ker (HomologicalComplex.homologyMap
              ((perF (k:=ℤ) (G:=G) g).map S.f) 4).hom := by
          rw [← hδ4]; exact LinearMap.mem_range_self _ x
        exact hmem
      have hkey := hnat y
      rw [← hEy] at hkey
      rw [h4z] at hkey
      have hfin : (perIso g S.X₂).hom
            ((HomologicalComplex.homologyMap ((perF (k:=ℤ) (G:=G) g).map S.f) 2).hom y)
          = (perIso g S.X₂).hom 0 := by
        rw [hkey.symm]; exact (map_zero (ModuleCat.Hom.hom (perIso g S.X₂).hom)).symm
      exact perIso_hom_injective g S.X₂ hfin
    · intro hy
      have h4y : (HomologicalComplex.homologyMap ((perF (k:=ℤ) (G:=G) g).map S.f) 4).hom
          ((perIso g S.X₁).hom y) = 0 := by
        rw [hnat y, hy]; exact map_zero (ModuleCat.Hom.hom (perIso g S.X₂).hom)
      have hmem : (perIso g S.X₁).hom y ∈ LinearMap.range (hper.δ 3 4 h34).hom := by
        rw [hδ4]; exact h4y
      obtain ⟨x, hx⟩ := hmem
      refine ⟨x, ?_⟩
      change (perIso g S.X₁).inv ((hper.δ 3 4 h34).hom x) = y
      rw [hx]
      exact Iso.hom_inv_id_apply (perIso g S.X₁) y
  have key := cyclicExact_card_relation
    (HomologicalComplex.homologyMap ((perF (k:=ℤ) (G:=G) g).map S.f) 2).hom
    (HomologicalComplex.homologyMap ((perF (k:=ℤ) (G:=G) g).map S.g) 2).hom
    (hper.δ 2 3 h23).hom
    (HomologicalComplex.homologyMap ((perF (k:=ℤ) (G:=G) g).map S.f) 3).hom
    (HomologicalComplex.homologyMap ((perF (k:=ℤ) (G:=G) g).map S.g) 3).hom
    (perZeta (G := G) g S hS h34)
    hαβ hβγ hγδ hδε hεζ hζα
  rw [← natCard_perF_homology_two_eq (G := G) g S.X₂ hg,
      ← natCard_perF_homology_three_eq (G := G) g S.X₁ hg,
      ← natCard_perF_homology_three_eq (G := G) g S.X₃ hg,
      ← natCard_perF_homology_two_eq (G := G) g S.X₁ hg,
      ← natCard_perF_homology_two_eq (G := G) g S.X₃ hg,
      ← natCard_perF_homology_three_eq (G := G) g S.X₂ hg]
  exact key

end NK.GlobalCFTdeep.Herbrand
