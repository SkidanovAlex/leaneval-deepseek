import Mathlib
import Submission.Work.Clifford.Classes
import Submission.Work.Clifford.card_Irr_eq_card_conjClasses
import Submission.Work.CharCore.finrank_classFun_eq_card_Irr
import Submission.Work.CharCore.finrank_classFun_eq_card_conjClasses
import Submission.Work.CharCore.star_Irr
import Submission.Work.Clifford.principalChar_mem_Irr
import Submission.Work.Clifford.brauer_permutation_lemma
import Submission.Work.Clifford.galoisChar_mem_Irr
import Submission.Work.Clifford.cfInner_eq_ite_of_mem_Irr
import Submission.Work.CharCore.mem_Irr_iff_fdrep

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The number of real irreducible characters equals the number of real conjugacy classes

For a finite group `G`, the complex conjugation involution `χ ↦ χ̄` (`χ̄ g = conj (χ g)`)
permutes the irreducible complex characters `Work.Clifford.Irr G`, and the inversion
involution `C ↦ C⁻¹` permutes the conjugacy classes `ConjClasses G`.  The fixed points are
the *real* characters (`Work.Clifford.IsRealChar`) and the *real* classes
(`Work.Clifford.IsRealClass`); the two fixed-point sets have the same cardinality.

This is the `k = -1` (complex conjugation) case of Brauer's permutation lemma, proved by
applying `Work.Clifford.brauer_permutation_lemma` to the character table
`M χ C = χ (rep C)`: as `conj (χ (rep C)) = χ ((rep C)⁻¹) = χ (rep (C⁻¹))`, the two
permutations are intertwined by the table, so they have the same number of fixed points.

The only non-formal inputs are the independence of the rows of the character table (from
`Work.Clifford.cfInner_eq_ite_of_mem_Irr`, the orthonormality of `Irr G`) and the fact that
the conjugate of an irreducible character is irreducible (`Work.Clifford.galoisChar_mem_Irr`
for the complex conjugation automorphism of `ℂ`).
-/

noncomputable section
set_option linter.unusedSectionVars false
open Classical

namespace Work.Clifford

section Helpers

variable {G : Type*} [Group G] [Fintype G]

/-! ### Complex conjugation as a ring automorphism -/

/-- Complex conjugation, as a ring automorphism of `ℂ`. -/
noncomputable def conjRingEquiv : ℂ ≃+* ℂ :=
  RingEquiv.ofBijective (starRingEnd ℂ)
    (Function.Involutive.bijective fun z => starRingEnd_self_apply z)

@[simp] theorem conjRingEquiv_apply (z : ℂ) : conjRingEquiv z = starRingEnd ℂ z := rfl

/-! ### The conjugate character -/

/-- The complex-conjugate function `χ̄ g = conj (χ g)`. -/
def conjChar (χ : G → ℂ) : G → ℂ := fun g => starRingEnd ℂ (χ g)

@[simp] theorem conjChar_apply (χ : G → ℂ) (g : G) : conjChar χ g = starRingEnd ℂ (χ g) := rfl

theorem conjChar_conjChar (χ : G → ℂ) : conjChar (conjChar χ) = χ := by
  ext g; simp [conjChar]

/-- The conjugate of an irreducible character is irreducible. -/
theorem conjChar_mem_Irr {χ : G → ℂ} (hχ : χ ∈ Irr G) : conjChar χ ∈ Irr G := by
  have h : (fun g => starRingEnd ℂ (χ g)) ∈ Irr G := galoisChar_mem_Irr conjRingEquiv hχ
  have h2 : conjChar χ = fun g => starRingEnd ℂ (χ g) := rfl
  rwa [h2]

theorem conjChar_eq_self_iff (χ : G → ℂ) : conjChar χ = χ ↔ IsRealChar χ := by
  constructor
  · intro h g; exact congrFun h g
  · intro h; exact funext h

/-- For an irreducible character, `conj (χ g) = χ g⁻¹`. -/
theorem star_Irr_clifford {χ : G → ℂ} (hχ : χ ∈ Irr G) (g : G) :
    starRingEnd ℂ (χ g) = χ g⁻¹ := by
  obtain ⟨V, -, hVχ⟩ := hχ
  rw [← congrFun hVχ g, ← congrFun hVχ g⁻¹]
  exact star_char_eq_char_inv V g

/-- A class function is constant on conjugacy classes. -/
theorem IsClassFun.eq_of_isConj {f : G → ℂ} (hf : IsClassFun f) {a b : G} (h : IsConj a b) :
    f a = f b := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  rw [← hc]
  exact (hf a c).symm

/-! ### The conjugation permutation of `Irr G` and the inversion permutation of classes -/

/-- Complex conjugation as an involutive map on `Irr G`. -/
def conjIrrFun (χ : {χ : G → ℂ // χ ∈ Irr G}) : {χ : G → ℂ // χ ∈ Irr G} :=
  ⟨conjChar χ.1, conjChar_mem_Irr χ.2⟩

theorem conjIrrFun_involutive : Function.Involutive (conjIrrFun (G := G)) :=
  fun χ => Subtype.ext (conjChar_conjChar χ.1)

/-- Complex conjugation, as a permutation of the irreducible characters. -/
noncomputable def conjIrrEquiv : {χ : G → ℂ // χ ∈ Irr G} ≃ {χ : G → ℂ // χ ∈ Irr G} where
  toFun := conjIrrFun
  invFun := conjIrrFun
  left_inv := conjIrrFun_involutive
  right_inv := conjIrrFun_involutive

/-- Inversion of conjugacy classes, as a permutation. -/
noncomputable def conjClassesInvEquiv : ConjClasses G ≃ ConjClasses G where
  toFun := conjClassesInv
  invFun := conjClassesInv
  left_inv := conjClassesInv_involutive
  right_inv := conjClassesInv_involutive

/-- The fixed points of `conjIrrEquiv` are exactly the real characters. -/
theorem conjIrrEquiv_eq_iff (χ : {χ : G → ℂ // χ ∈ Irr G}) :
    conjIrrEquiv χ = χ ↔ IsRealChar χ.1 := by
  rw [Subtype.ext_iff]
  change conjChar χ.1 = χ.1 ↔ IsRealChar χ.1
  exact conjChar_eq_self_iff χ.1

/-- The fixed points of `conjClassesInvEquiv` are exactly the real classes. -/
theorem conjClassesInvEquiv_eq_iff (C : ConjClasses G) :
    conjClassesInvEquiv C = C ↔ IsRealClass C := by
  unfold conjClassesInvEquiv IsRealClass
  exact Iff.rfl

/-! ### The character table and the independence of its rows -/

/-- A chosen representative of a conjugacy class. -/
noncomputable def charRep (C : ConjClasses G) : G :=
  Classical.choose (ConjClasses.exists_rep C)

theorem charRep_spec (C : ConjClasses G) : ConjClasses.mk (charRep C) = C :=
  Classical.choose_spec (ConjClasses.exists_rep C)

/-- The character table, as a function `Irr G → (ConjClasses G → ℂ)`. -/
noncomputable def charTableMap (χ : {χ : G → ℂ // χ ∈ Irr G}) : ConjClasses G → ℂ :=
  fun C => χ.1 (charRep C)

/-- `Irr G` is finite, being (definitionally as a set) the finset `Work.CharCore.Irr G`. -/
noncomputable instance instFintypeIrrSubtype : Fintype {χ : G → ℂ // χ ∈ Irr G} :=
  Fintype.ofEquiv {χ : G → ℂ // χ ∈ Work.CharCore.Irr G}
    (Equiv.subtypeEquivRight fun χ =>
      (Work.CharCore.mem_Irr_iff_fdrep χ).trans
        (Work.Clifford.mem_Irr (G := G) (χ := χ)).symm)

/-- The rows of the character table are linearly independent: the character table is the
(injective) evaluation-at-representatives map applied to the linearly independent family
`Irr G` of class functions. -/
theorem charTableMap_linearIndependent :
    LinearIndependent ℂ (charTableMap (G := G)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hF : (∑ χ : {χ : G → ℂ // χ ∈ Irr G}, c χ • (χ.1 : G → ℂ)) = 0 := by
    funext g
    have hg0 : (∑ χ : {χ : G → ℂ // χ ∈ Irr G},
        c χ * χ.1 (charRep (ConjClasses.mk g))) = 0 := by
      have h := congrFun hc (ConjClasses.mk g)
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, charTableMap, Pi.zero_apply]
        using h
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [← hg0]
    refine Finset.sum_congr rfl (fun χ _ => ?_)
    have hconj : χ.1 g = χ.1 (charRep (ConjClasses.mk g)) :=
      IsClassFun.eq_of_isConj (IsClassFun.of_mem_Irr χ.2)
        (ConjClasses.mk_eq_mk_iff_isConj.mp (charRep_spec (ConjClasses.mk g))).symm
    rw [hconj]
  intro ψ
  have h0 : cfInner (∑ χ : {χ : G → ℂ // χ ∈ Irr G}, c χ • (χ.1 : G → ℂ)) ψ.1 = 0 := by
    rw [hF, cfInner_zero_left]
  rw [cfInner_sum_smul_left] at h0
  have hsingle : (∑ χ : {χ : G → ℂ // χ ∈ Irr G}, c χ * cfInner χ.1 ψ.1) = c ψ := by
    rw [Finset.sum_eq_single ψ]
    · rw [cfInner_eq_ite_of_mem_Irr ψ.2 ψ.2, if_pos rfl, mul_one]
    · intro χ _ hne
      rw [cfInner_eq_ite_of_mem_Irr χ.2 ψ.2, if_neg (fun h => hne (Subtype.ext h)), mul_zero]
    · intro h; exact absurd (Finset.mem_univ ψ) h
  rw [hsingle] at h0
  exact h0

/-- The two index sets of the character table have the same cardinality. -/
theorem charTableCard :
    Fintype.card {χ : G → ℂ // χ ∈ Irr G} = Fintype.card (ConjClasses G) := by
  rw [show Fintype.card {χ : G → ℂ // χ ∈ Irr G}
        = Nat.card {χ : G → ℂ // χ ∈ Irr G} from Nat.card_eq_fintype_card.symm,
    card_Irr_eq_card_conjClasses, Nat.card_eq_fintype_card]

/-- The canonical representative of `C⁻¹` is conjugate to the inverse of the canonical
representative of `C`. -/
theorem mk_charRep_conjClassesInv (C : ConjClasses G) :
    ConjClasses.mk (charRep (conjClassesInv C)) = ConjClasses.mk ((charRep C)⁻¹) := by
  have h1 : conjClassesInv C = ConjClasses.mk ((charRep C)⁻¹) := by
    conv_lhs => rw [← charRep_spec C]
    rw [conjClassesInv_mk]
  rw [charRep_spec (conjClassesInv C), h1]

/-- The conjugation permutation of `Irr G` and the inversion permutation of the conjugacy
classes are intertwined by the character table. -/
theorem charTableMap_conjIrrEquiv (χ : {χ : G → ℂ // χ ∈ Irr G}) (C : ConjClasses G) :
    charTableMap (conjIrrEquiv χ) C = charTableMap χ (conjClassesInvEquiv C) := by
  show (conjIrrEquiv χ).1 (charRep C) = χ.1 (charRep (conjClassesInvEquiv C))
  rw [show (conjIrrEquiv χ).1 = conjChar χ.1 from rfl,
    show conjClassesInvEquiv C = conjClassesInv C from rfl]
  show starRingEnd ℂ (χ.1 (charRep C)) = χ.1 (charRep (conjClassesInv C))
  rw [star_Irr_clifford χ.2 (charRep C)]
  exact IsClassFun.eq_of_isConj (IsClassFun.of_mem_Irr χ.2)
    (ConjClasses.mk_eq_mk_iff_isConj.mp (mk_charRep_conjClassesInv C)).symm

end Helpers

/-- **The number of real irreducible characters equals the number of real conjugacy
classes.**  Both are the fixed-point sets of the complex-conjugation involution on `Irr G`
and the inversion involution on `ConjClasses G`; these two permutations are intertwined by
the character table, so Brauer's permutation lemma applies. -/
theorem card_realIrr_eq_card_realClasses {G : Type*} [Group G] [Fintype G] :
    Nat.card {χ : G → ℂ // χ ∈ Work.Clifford.Irr G ∧ Work.Clifford.IsRealChar χ} =
    Nat.card {C : ConjClasses G // Work.Clifford.IsRealClass C} := by
  classical
  have hbrauer := brauer_permutation_lemma (charTableMap (G := G)) (conjIrrEquiv (G := G))
    (conjClassesInvEquiv (G := G)) (charTableMap_linearIndependent (G := G))
    (charTableCard (G := G)) (charTableMap_conjIrrEquiv (G := G))
  have eBoth : {i : {χ : G → ℂ // χ ∈ Work.Clifford.Irr G} //
        conjIrrEquiv (G := G) i = i} ≃
      {χ : G → ℂ // χ ∈ Work.Clifford.Irr G ∧ Work.Clifford.IsRealChar χ} :=
    { toFun := fun x => ⟨x.1.1, x.1.2, (conjIrrEquiv_eq_iff (G := G) x.1).mp x.2⟩
      invFun := fun x =>
        ⟨⟨x.1, x.2.1⟩, (conjIrrEquiv_eq_iff (G := G) ⟨x.1, x.2.1⟩).mpr x.2.2⟩
      left_inv := fun x => Subtype.ext (Subtype.ext rfl)
      right_inv := fun x => Subtype.ext rfl }
  have eClass : {j : ConjClasses G // conjClassesInvEquiv (G := G) j = j} ≃
      {C : ConjClasses G // Work.Clifford.IsRealClass C} :=
    Equiv.subtypeEquivRight fun C => conjClassesInvEquiv_eq_iff (G := G) C
  calc Nat.card {χ : G → ℂ // χ ∈ Work.Clifford.Irr G ∧ Work.Clifford.IsRealChar χ}
      = Nat.card {i : {χ : G → ℂ // χ ∈ Work.Clifford.Irr G} //
          conjIrrEquiv (G := G) i = i} := (Nat.card_congr eBoth).symm
    _ = Nat.card {j : ConjClasses G // conjClassesInvEquiv (G := G) j = j} := hbrauer
    _ = Nat.card {C : ConjClasses G // Work.Clifford.IsRealClass C} := Nat.card_congr eClass

end Work.Clifford
