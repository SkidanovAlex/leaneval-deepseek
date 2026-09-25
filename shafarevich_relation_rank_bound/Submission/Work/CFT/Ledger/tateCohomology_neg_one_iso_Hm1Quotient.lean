import Mathlib
import Submission.Work.CFT.Ledger.Coind

/-!
# `Ĥ⁻¹(G, A)` is the kernel of the norm modulo the augmentation subgroup

For a finite group `G` and a `ℤ`-linear representation `A`, the `(-1)`-st Tate cohomology
`Ĥ⁻¹(G, A)` is the homology in degree `-1` of the Tate complex.  The Tate complex is obtained by
connecting the inhomogeneous chain complex with the inhomogeneous cochain complex along the norm
map, so its degree `-1` homology is the homology of the short complex
`C₁(G, A) --d₁₀--> A --N--> A`, where `C₁(G, A)` is the group of inhomogeneous `1`-chains and
`d₁₀` the `0`-th chain differential.  Its homology is `ker(N) / im(d₁₀)`, and `im(d₁₀)` is
precisely the augmentation subgroup `I_G A = ⟨ρ g a - a⟩`.

## Main results

* `Work.CFT.Ledger.tateCohomology_neg_one_iso_Hm1Quotient` :
  `Ĥ⁻¹(G, A) ≃+ ker N_A ⧸ I_G A = Hm1Quotient A`.
-/

namespace Work.CFT.Ledger

open CategoryTheory groupHomology groupCohomology

noncomputable section

variable {G : Type} [Group G] [Fintype G]

/-- The short complex `C₁(G, A) --d₁₀--> A --N--> A` whose homology in degree `-1` computes
`Ĥ⁻¹(G, A)`. -/
noncomputable def tateNegOneComplex (A : Rep ℤ G) : ShortComplex (ModuleCat ℤ) :=
  ShortComplex.mk (groupHomology.d₁₀ A) A.norm.toModuleCatHom (Rep.comp_eq_zero A)

@[simp] lemma tateNegOneComplex_f (A : Rep ℤ G) :
    (tateNegOneComplex A).f = groupHomology.d₁₀ A := rfl

@[simp] lemma tateNegOneComplex_g (A : Rep ℤ G) :
    (tateNegOneComplex A).g = A.norm.toModuleCatHom := rfl

/-- The comparison isomorphism between the Tate complex in degrees `-2, -1, 0` and the short
complex `C₁(G, A) --d₁₀--> A --N--> A`. -/
noncomputable def tateNegOneIso (A : Rep ℤ G) :
    (tateComplex A).sc' (-2) (-1) 0 ≅ tateNegOneComplex A :=
  ShortComplex.isoMk (groupHomology.chainsIso₁ A) (groupHomology.chainsIso₀ A)
    (groupCohomology.cochainsIso₀ A)
    (by
      change (groupHomology.chainsIso₁ A).hom ≫ groupHomology.d₁₀ A =
        (inhomogeneousChains A).d 1 0 ≫ (groupHomology.chainsIso₀ A).hom
      exact groupHomology.comp_d₁₀_eq A)
    (by
      change (groupHomology.chainsIso₀ A).hom ≫ A.norm.toModuleCatHom =
        A.tateNorm ≫ (groupCohomology.cochainsIso₀ A).hom
      exact Work.CFT.IdeleClassGroup.tateNorm_sq A)

/-- `Ĥ⁻¹(G, A)` is computed as the homology of the short complex
`C₁(G, A) --d₁₀--> A --N--> A`. -/
noncomputable def tateCohomology_neg_one_iso_shortComplex (A : Rep ℤ G) :
    tateCohomology A (-1) ≅ (tateNegOneComplex A).homology :=
  (tateComplex A).homologyIsoSc' (-2) (-1) 0 (by simp) (by simp) ≪≫
    ShortComplex.homologyMapIso (tateNegOneIso A)

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
/-- **The `(-1)`-st Tate cohomology as the kernel of the norm modulo the augmentation
subgroup.**  For a `ℤ`-representation `A` of a finite group `G`, the `(-1)`-st Tate cohomology
group `Ĥ⁻¹(G, A)` (Mathlib's `tateCohomology A (-1)`, the homology of the Tate complex in
degree `-1`) is the quotient of the kernel of the norm endomorphism `N = ∑_{g : G} g` by the
augmentation subgroup `I_G A = ⟨ρ g a - a⟩`. -/
theorem tateCohomology_neg_one_iso_Hm1Quotient {G : Type} [Group G] [Fintype G]
    (A : Rep ℤ G) :
    Nonempty (↥(tateCohomology A (-1)) ≃+ Work.CFT.Ledger.Hm1Quotient A) := by
  letI : Module ℤ A.V := A.hV2
  let T := tateNegOneComplex A
  letI : Module ℤ ↥(T.g.hom.ker) := (T.g.hom.ker).module
  letI : Module ℤ (↥(T.g.hom.ker) ⧸ T.moduleCatToCycles.range) :=
    (T.moduleCatLeftHomologyData.H).isModule
  -- The norm of the representation is the `(-1)`-st differential of the short complex.
  have hnorm : ∀ x : A.V, T.g.hom x = Work.CFT.IdeleClassGroup.normMap A x := by
    intro x
    show A.norm.toModuleCatHom.hom x = _
    rw [show A.norm.toModuleCatHom.hom x = A.norm.hom x from rfl, Rep.norm_apply]
    simp only [Work.CFT.IdeleClassGroup.normMap_apply, Representation.norm]
    rw [LinearMap.sum_apply]
  have hnorm2 : ∀ x : A.V, x ∈ T.g.hom.ker ↔ Work.CFT.IdeleClassGroup.normMap A x = 0 := by
    intro x
    have h : x ∈ T.g.hom.ker ↔ T.g.hom x = 0 := Iff.rfl
    rw [h, hnorm x]
  -- The range of the `0`-th chain differential is the augmentation subgroup.
  have hrange : (LinearMap.range T.f.hom).toAddSubgroup = augIdeal A := by
    apply le_antisymm
    · intro x hx
      rw [Submodule.mem_toAddSubgroup, LinearMap.mem_range] at hx
      obtain ⟨y, rfl⟩ := hx
      change (groupHomology.d₁₀ A) y ∈ augIdeal A
      induction y using Finsupp.induction with
      | zero => exact (augIdeal A).zero_mem
      | single_add g a f hg hf ih =>
          rw [map_add, groupHomology.d₁₀_single]
          exact (augIdeal A).add_mem (smul_sub_self_mem_augIdeal A g⁻¹ a) ih
    · change AddSubgroup.closure (Set.range fun (gv : G × A.V) => A.ρ gv.1 gv.2 - gv.2) ≤
        (LinearMap.range T.f.hom).toAddSubgroup
      rw [AddSubgroup.closure_le]
      rintro _ ⟨⟨g, a⟩, rfl⟩
      exact (Submodule.mem_toAddSubgroup _).mpr
        ⟨Finsupp.single g⁻¹ a, by
          change (groupHomology.d₁₀ A) (Finsupp.single g⁻¹ a) = A.ρ g a - a
          rw [groupHomology.d₁₀_single]; simp⟩
  -- `Ĥ⁻¹(G, A)` as the kernel of the norm modulo the range of the chain differential.
  have e1 := ((tateCohomology_neg_one_iso_shortComplex A ≪≫ T.moduleCatHomologyIso ≪≫
      eqToIso (ShortComplex.moduleCatLeftHomologyData_H T)).toLinearEquiv.toAddEquiv)
  -- The comparison map `ker N_A → Hm1Quotient A`.
  let inc : ↥(T.g.hom.ker) →+ ↥((Work.CFT.IdeleClassGroup.normMap A).ker) :=
    { toFun := fun x =>
        let y : A.V := x.1
        have h : Work.CFT.IdeleClassGroup.normMap A y = 0 := by
          rw [← hnorm y]
          exact (LinearMap.mem_ker).mp x.2
        Subtype.mk y h
      map_zero' := Subtype.ext rfl
      map_add' := fun x y => Subtype.ext rfl }
  let Φ : ↥(T.g.hom.ker) →+ Work.CFT.Ledger.Hm1Quotient A :=
    (QuotientAddGroup.mk' (Work.CFT.Ledger.Hm1Sub A)).comp inc
  have hinc_surj : Function.Surjective inc := by
    intro y
    refine ⟨⟨(y.1 : A.V), (hnorm2 (y.1 : A.V)).mpr ((AddMonoidHom.mem_ker).mp y.2)⟩, ?_⟩
    apply Subtype.ext
    rfl
  have hsurj : Function.Surjective Φ :=
    (QuotientAddGroup.mk'_surjective (Work.CFT.Ledger.Hm1Sub A)).comp hinc_surj
  -- The kernel of `Φ` is exactly the range of the chain differential.
  have hker : Φ.ker = (T.moduleCatToCycles.range).toAddSubgroup := by
    ext x
    rw [AddMonoidHom.mem_ker, Submodule.mem_toAddSubgroup]
    rw [show Φ x = QuotientAddGroup.mk' (Work.CFT.Ledger.Hm1Sub A) (inc x) from rfl,
      QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff, Work.CFT.Ledger.mem_Hm1Sub]
    have hinc1 : (inc x).1 = x.1 := rfl
    have hmem : x ∈ T.moduleCatToCycles.range ↔ x.1 ∈ LinearMap.range T.f.hom := by
      rw [LinearMap.mem_range]
      constructor
      · rintro ⟨y, hy⟩; exact ⟨y, congrArg Subtype.val hy⟩
      · rintro ⟨y, hy⟩; exact ⟨y, Subtype.ext hy⟩
    rw [hinc1, hmem]
    have hkey : x.1 ∈ LinearMap.range T.f.hom ↔ x.1 ∈ augIdeal A := by
      rw [← Submodule.mem_toAddSubgroup, hrange]
    exact hkey.symm
  have e2 : (↥(T.g.hom.ker) ⧸ (T.moduleCatToCycles.range).toAddSubgroup) ≃+
      Work.CFT.Ledger.Hm1Quotient A :=
    hker ▸ QuotientAddGroup.quotientKerEquivOfSurjective Φ hsurj
  exact ⟨e1.trans e2⟩

end

end Work.CFT.Ledger
