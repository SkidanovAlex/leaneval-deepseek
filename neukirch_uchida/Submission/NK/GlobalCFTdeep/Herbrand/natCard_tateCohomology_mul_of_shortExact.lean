import Mathlib
import Submission.NK.GlobalCFTdeep.Basic
import Submission.NK.GlobalCFTdeep.Herbrand.PeriodicComplex

set_option autoImplicit false
open CategoryTheory

noncomputable section
namespace NK.GlobalCFTdeep.Herbrand

/-- **The arithmetic of the Tate hexagon.** -/
theorem cyclicExact_card_relation
    {A B C A' B' C' : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [AddCommGroup A'] [AddCommGroup B'] [AddCommGroup C']
    [Module ℤ A] [Module ℤ B] [Module ℤ C] [Module ℤ A'] [Module ℤ B'] [Module ℤ C']
    (α : A →ₗ[ℤ] B) (β : B →ₗ[ℤ] C) (γ : C →ₗ[ℤ] A')
    (δ : A' →ₗ[ℤ] B') (ε : B' →ₗ[ℤ] C') (ζ : C' →ₗ[ℤ] A)
    (hαβ : LinearMap.range α = LinearMap.ker β) (hβγ : LinearMap.range β = LinearMap.ker γ)
    (hγδ : LinearMap.range γ = LinearMap.ker δ) (hδε : LinearMap.range δ = LinearMap.ker ε)
    (hεζ : LinearMap.range ε = LinearMap.ker ζ) (hζα : LinearMap.range ζ = LinearMap.ker α) :
    Nat.card B * Nat.card A' * Nat.card C' = Nat.card A * Nat.card C * Nat.card B' := by
  have hB : Nat.card B = Nat.card ↥(LinearMap.range α) * Nat.card ↥(LinearMap.range β) := by
    have hcard : Nat.card B = Nat.card ↥(LinearMap.ker β) * Nat.card (B ⧸ LinearMap.ker β) :=
      Submodule.card_eq_card_quotient_mul_card _
    rw [Nat.card_congr (LinearMap.quotKerEquivRange β).toEquiv] at hcard
    rw [hcard, ← hαβ]
  have hA' : Nat.card A' = Nat.card ↥(LinearMap.range γ) * Nat.card ↥(LinearMap.range δ) := by
    have hcard : Nat.card A' = Nat.card ↥(LinearMap.ker δ) * Nat.card (A' ⧸ LinearMap.ker δ) :=
      Submodule.card_eq_card_quotient_mul_card _
    rw [Nat.card_congr (LinearMap.quotKerEquivRange δ).toEquiv] at hcard
    rw [hcard, ← hγδ]
  have hC' : Nat.card C' = Nat.card ↥(LinearMap.range ε) * Nat.card ↥(LinearMap.range ζ) := by
    have hcard : Nat.card C' = Nat.card ↥(LinearMap.ker ζ) * Nat.card (C' ⧸ LinearMap.ker ζ) :=
      Submodule.card_eq_card_quotient_mul_card _
    rw [Nat.card_congr (LinearMap.quotKerEquivRange ζ).toEquiv] at hcard
    rw [hcard, ← hεζ]
  have hA : Nat.card A = Nat.card ↥(LinearMap.range ζ) * Nat.card ↥(LinearMap.range α) := by
    have hcard : Nat.card A = Nat.card ↥(LinearMap.ker α) * Nat.card (A ⧸ LinearMap.ker α) :=
      Submodule.card_eq_card_quotient_mul_card _
    rw [Nat.card_congr (LinearMap.quotKerEquivRange α).toEquiv] at hcard
    rw [hcard, ← hζα]
  have hC : Nat.card C = Nat.card ↥(LinearMap.range γ) * Nat.card ↥(LinearMap.range β) := by
    have hcard : Nat.card C = Nat.card ↥(LinearMap.ker γ) * Nat.card (C ⧸ LinearMap.ker γ) :=
      Submodule.card_eq_card_quotient_mul_card _
    rw [Nat.card_congr (LinearMap.quotKerEquivRange γ).toEquiv] at hcard
    rw [hcard, ← hβγ]; ring
  have hB' : Nat.card B' = Nat.card ↥(LinearMap.range δ) * Nat.card ↥(LinearMap.range ε) := by
    have hcard : Nat.card B' = Nat.card ↥(LinearMap.ker ε) * Nat.card (B' ⧸ LinearMap.ker ε) :=
      Submodule.card_eq_card_quotient_mul_card _
    rw [Nat.card_congr (LinearMap.quotKerEquivRange ε).toEquiv] at hcard
    rw [hcard, ← hδε]
  rw [hB, hA', hC', hA, hC, hB']
  ring

section Bridge
variable {k G : Type} [CommRing k] [CommGroup G] [Fintype G] (g : G)

noncomputable def perF_homology_two_iso (M : Rep k G) :
    ((perF (k:=k) (G:=G) g).obj M).homology 2 ≅
      (Rep.FiniteCyclicGroup.normHomCompSub M g).homology :=
  HomologicalComplex.alternatingConstHomologyIsoEven (ModuleCat.of k M.V)
    (φ := ModuleCat.ofHom (Rep.applyAsHom M g - 𝟙 M).hom.toLinearMap)
    (ψ := ModuleCat.ofHom M.norm.hom.toLinearMap)
    (by ext; simp [Rep.sub_hom, Rep.applyAsHom, Rep.norm])
    (by ext; simp [Rep.sub_hom, Rep.applyAsHom, Rep.norm])
    (fun i j hij => ComplexShape.up_nat_odd_add hij)
    (by simp) (by simp) (by norm_num : Even 2)

noncomputable def perF_homology_one_iso (M : Rep k G) :
    ((perF (k:=k) (G:=G) g).obj M).homology 1 ≅
      (Rep.FiniteCyclicGroup.subCompNormHom M g).homology :=
  HomologicalComplex.alternatingConstHomologyIsoOdd (ModuleCat.of k M.V)
    (φ := ModuleCat.ofHom (Rep.applyAsHom M g - 𝟙 M).hom.toLinearMap)
    (ψ := ModuleCat.ofHom M.norm.hom.toLinearMap)
    (by ext; simp [Rep.sub_hom, Rep.applyAsHom, Rep.norm])
    (by ext; simp [Rep.sub_hom, Rep.applyAsHom, Rep.norm])
    (fun i j hij => ComplexShape.up_nat_odd_add hij)
    (by simp) (by simp) (by norm_num : Odd 1)

noncomputable def perF_homology_three_iso (M : Rep k G) :
    ((perF (k:=k) (G:=G) g).obj M).homology 3 ≅
      (Rep.FiniteCyclicGroup.subCompNormHom M g).homology :=
  HomologicalComplex.alternatingConstHomologyIsoOdd (ModuleCat.of k M.V)
    (φ := ModuleCat.ofHom (Rep.applyAsHom M g - 𝟙 M).hom.toLinearMap)
    (ψ := ModuleCat.ofHom M.norm.hom.toLinearMap)
    (by ext; simp [Rep.sub_hom, Rep.applyAsHom, Rep.norm])
    (by ext; simp [Rep.sub_hom, Rep.applyAsHom, Rep.norm])
    (fun i j hij => ComplexShape.up_nat_odd_add hij)
    (by simp) (by simp) (by norm_num : Odd 3)

end Bridge

section PeriodicIso
variable {G : Type} [CommGroup G] [Fintype G]

/-- The identity-component isomorphism `K.sc 2 ≅ K.sc 4` of the periodic complex. -/
noncomputable def scIso (g : G) (M : Rep ℤ G) :
    ((perF (k:=ℤ) (G:=G) g).obj M).sc 2 ≅ ((perF (k:=ℤ) (G:=G) g).obj M).sc 4 := by
  refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ <;>
    simp only [perF, HomologicalComplex.sc, HomologicalComplex.shortComplexFunctor,
      HomologicalComplex.shortComplexFunctor', CochainComplex.prev_nat_succ, CochainComplex.next,
      Nat.reduceAdd, Rep.FiniteCyclicGroup.moduleCatCochainComplex,
      HomologicalComplex.alternatingConst, Iso.refl_hom, Category.id_comp, Category.comp_id] <;>
    norm_num

lemma scIso_natural (g : G) {M M' : Rep ℤ G} (ψ : M ⟶ M') :
    (scIso g M).hom ≫
        (HomologicalComplex.shortComplexFunctor (ModuleCat ℤ) (ComplexShape.up ℕ) 4).map
          ((perF (k:=ℤ) (G:=G) g).map ψ)
      = (HomologicalComplex.shortComplexFunctor (ModuleCat ℤ) (ComplexShape.up ℕ) 2).map
          ((perF (k:=ℤ) (G:=G) g).map ψ) ≫ (scIso g M').hom := by
  apply ShortComplex.hom_ext <;> rfl

/-- The periodicity isomorphism between the homology in degrees `2` and `4`. -/
noncomputable def perIso (g : G) (M : Rep ℤ G) :
    ((perF (k:=ℤ) (G:=G) g).obj M).homology 2 ≅
      ((perF (k:=ℤ) (G:=G) g).obj M).homology 4 :=
  ShortComplex.homologyMapIso (scIso g M)

lemma perIso_natural (g : G) {M M' : Rep ℤ G} (ψ : M ⟶ M') :
    (perIso g M).hom ≫ HomologicalComplex.homologyMap ((perF (k:=ℤ) (G:=G) g).map ψ) 4
      = HomologicalComplex.homologyMap ((perF (k:=ℤ) (G:=G) g).map ψ) 2 ≫ (perIso g M').hom := by
  have h := scIso_natural g ψ
  simp only [perIso, ShortComplex.homologyMapIso_hom, HomologicalComplex.homologyMap] at h ⊢
  erw [← ShortComplex.homologyMap_comp, ← ShortComplex.homologyMap_comp]
  exact congrArg (fun t => ShortComplex.homologyMap t) h

end PeriodicIso

section ZBridge
variable {G : Type} [CommGroup G] [Fintype G] (g : G)

theorem natCard_perF_homology_two_eq (M : Rep ℤ G) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    Nat.card ↥(((perF (k:=ℤ) (G:=G) g).obj M).homology 2) = Nat.card ↥(tateCohomology M 0) := by
  calc Nat.card ↥(((perF (k:=ℤ) (G:=G) g).obj M).homology 2)
      = Nat.card ↥((Rep.FiniteCyclicGroup.normHomCompSub M g).homology) :=
        Nat.card_congr (perF_homology_two_iso (k := ℤ) g M).toLinearEquiv.toEquiv
    _ = Nat.card ↥(groupCohomology M 2) :=
        (Nat.card_congr (Rep.FiniteCyclicGroup.groupCohomologyIsoEven M g hg 2
          (by norm_num : Even 2)).toLinearEquiv.toEquiv).symm
    _ = Nat.card ↥(tateCohomology M 0) :=
        Commons.RepresentationTheory.GroupCohomology.natCard_groupCohomology_two_eq_natCard_tateCohomology_zero_of_cyclic_general M g hg

theorem natCard_perF_homology_one_eq (M : Rep ℤ G) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    Nat.card ↥(((perF (k:=ℤ) (G:=G) g).obj M).homology 1) = Nat.card ↥(tateCohomology M 1) := by
  calc Nat.card ↥(((perF (k:=ℤ) (G:=G) g).obj M).homology 1)
      = Nat.card ↥((Rep.FiniteCyclicGroup.subCompNormHom M g).homology) :=
        Nat.card_congr (perF_homology_one_iso (k := ℤ) g M).toLinearEquiv.toEquiv
    _ = Nat.card ↥(groupCohomology M 1) :=
        (Nat.card_congr (Rep.FiniteCyclicGroup.groupCohomologyIsoOdd M g hg 1
          (by norm_num : Odd 1)).toLinearEquiv.toEquiv).symm
    _ = Nat.card ↥(tateCohomology M 1) :=
        (Nat.card_congr ((TateCohomology.isoGroupCohomology (R := ℤ) (G := G) 1).app M).toLinearEquiv.toEquiv).symm

theorem natCard_perF_homology_three_eq (M : Rep ℤ G) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    Nat.card ↥(((perF (k:=ℤ) (G:=G) g).obj M).homology 3) = Nat.card ↥(tateCohomology M 1) := by
  calc Nat.card ↥(((perF (k:=ℤ) (G:=G) g).obj M).homology 3)
      = Nat.card ↥((Rep.FiniteCyclicGroup.subCompNormHom M g).homology) :=
        Nat.card_congr (perF_homology_three_iso (k := ℤ) g M).toLinearEquiv.toEquiv
    _ = Nat.card ↥(groupCohomology M 1) :=
        (Nat.card_congr (Rep.FiniteCyclicGroup.groupCohomologyIsoOdd M g hg 1
          (by norm_num : Odd 1)).toLinearEquiv.toEquiv).symm
    _ = Nat.card ↥(tateCohomology M 1) :=
        (Nat.card_congr ((TateCohomology.isoGroupCohomology (R := ℤ) (G := G) 1).app M).toLinearEquiv.toEquiv).symm

end ZBridge


section Zeta
variable {G : Type} [CommGroup G] [Fintype G]

/-- The wrapped connecting map `Ĥ¹(X₃) → Ĥ⁰(X₁)` obtained by composing the connecting map
`Ĥ¹(X₃) → Ĥ²(X₁)` with the (inverse) periodicity isomorphism `Ĥ²(X₁) ≅ Ĥ⁰(X₁)`. -/
noncomputable def perZeta (g : G) (S : ShortComplex (Rep ℤ G)) (hS : S.ShortExact)
    (h34 : (ComplexShape.up ℕ).Rel 3 4) :
    ↥(((perF (k:=ℤ) (G:=G) g).obj S.X₃).homology 3) →ₗ[ℤ]
      ↥(((perF (k:=ℤ) (G:=G) g).obj S.X₁).homology 2) :=
  (perIso g S.X₁).inv.hom.comp ((perF_shortExact (k:=ℤ) (G:=G) g S hS).δ 3 4 h34).hom

lemma perZeta_apply (g : G) (S : ShortComplex (Rep ℤ G)) (hS : S.ShortExact)
    (h34 : (ComplexShape.up ℕ).Rel 3 4)
    (x : ↥(((perF (k:=ℤ) (G:=G) g).obj S.X₃).homology 3)) :
    perZeta (G := G) g S hS h34 x
      = (perIso g S.X₁).inv (((perF_shortExact (k:=ℤ) (G:=G) g S hS).δ 3 4 h34).hom x) :=
  rfl

lemma perIso_hom_injective (g : G) (M : Rep ℤ G) :
    Function.Injective (perIso g M).hom := by
  intro a b h
  have := congrArg (fun z => (perIso g M).inv z) h
  simpa only [Iso.hom_inv_id_apply] using this

end Zeta

theorem natCard_tateCohomology_mul_of_shortExact {G : Type} [CommGroup G] [Fintype G] [IsCyclic G]
    (S : CategoryTheory.ShortComplex (Rep ℤ G)) (hS : S.ShortExact)
    [Finite ↥(tateCohomology S.X₁ 0)] [Finite ↥(tateCohomology S.X₁ 1)]
    [Finite ↥(tateCohomology S.X₂ 0)] [Finite ↥(tateCohomology S.X₂ 1)]
    [Finite ↥(tateCohomology S.X₃ 0)] [Finite ↥(tateCohomology S.X₃ 1)] :
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
