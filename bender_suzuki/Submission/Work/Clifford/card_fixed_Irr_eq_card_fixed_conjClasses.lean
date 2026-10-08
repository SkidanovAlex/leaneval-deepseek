import Mathlib
import Submission.Work.Clifford.Classes
import Submission.Work.Clifford.FunAPI
import Submission.Work.Clifford.autChar_mem_Irr
import Submission.Work.Clifford.brauer_permutation_lemma
import Submission.Work.Clifford.cfInner_eq_ite_of_mem_Irr
import Submission.Work.Clifford.card_Irr_eq_card_conjClasses

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Clifford.card_fixed_Irr_eq_card_fixed_conjClasses`

Brauer's permutation lemma applied to the character table of a finite group `G`: the number of
irreducible complex characters fixed by an automorphism `α` of `G` equals the number of
conjugacy classes fixed by `α`.

## The argument

The character table is the matrix `M χ C = χ (rep C)`, with rows indexed by the irreducible
characters and columns by the conjugacy classes.  Its rows are linearly independent by the
orthonormality of the irreducible characters for `Work.Clifford.charPair`
(`Work.Clifford.charPair_eq_ite_of_mem_Irr`): a linear combination of the rows vanishing at every
`rep C` defines a class function vanishing everywhere, hence has all coefficients zero.

The automorphism `α` permutes the irreducible characters by `χ ↦ χ ∘ α⁻¹`
(`Work.Clifford.autChar α χ`) and the conjugacy classes by `C ↦ ConjClasses.map α⁻¹ C`, and these
two permutations are related by `M (σ χ) C = M χ (τ C)`.  Since `#Irr G = #ConjClasses G`
(`Work.Clifford.card_Irr_eq_card_conjClasses`), Brauer's permutation lemma
(`Work.Clifford.brauer_permutation_lemma`) gives that `σ` and `τ` have the same number of fixed
points; conjugating by `α` identifies these fixed points with the `α`-fixed irreducible
characters and the `α`-fixed classes.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Classical

namespace Work.Clifford

theorem card_fixed_Irr_eq_card_fixed_conjClasses {G : Type*} [Group G] [Fintype G] (α : G ≃* G) :
    Nat.card {χ : G → ℂ // χ ∈ Work.Clifford.Irr G ∧ Work.Clifford.IsFixedIrr α χ} =
    Nat.card {C : ConjClasses G // Work.Clifford.IsFixedClass α C} := by
  classical
  haveI : Fintype (ConjClasses G) := inferInstance
  haveI hιf : Fintype {χ : G → ℂ // χ ∈ Work.Clifford.Irr G} := by
    have h := Work.Clifford.card_Irr_eq_card_conjClasses (G := G)
    have hpos : 0 < Nat.card (ConjClasses G) := Nat.card_pos
    have hfin : Finite {χ : G → ℂ // χ ∈ Work.Clifford.Irr G} :=
      Nat.finite_of_card_ne_zero (by rw [h]; exact hpos.ne')
    exact Fintype.ofFinite _
  -- a representative of each conjugacy class
  let rep : ConjClasses G → G := fun C => Classical.choose (ConjClasses.exists_rep C)
  have rep_spec : ∀ C, ConjClasses.mk (rep C) = C := fun C => by
    dsimp only [rep]
    exact Classical.choose_spec (ConjClasses.exists_rep C)
  -- the character table
  let M : {χ : G → ℂ // χ ∈ Work.Clifford.Irr G} → ConjClasses G → ℂ := fun χ C => χ.1 (rep C)
  -- membership in `CharCore.Irr`, to apply orthonormality
  have hcl : ∀ χ : {χ : G → ℂ // χ ∈ Work.Clifford.Irr G}, χ.1 ∈ Work.CharCore.Irr G :=
    fun χ => (Work.Clifford.mem_Irr_iff_fdrep_aux χ.1).mpr χ.2
  -- the rows of the character table are linearly independent
  have hli : LinearIndependent ℂ M := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    let f : G → ℂ := ∑ χ : {χ : G → ℂ // χ ∈ Work.Clifford.Irr G}, g χ • (χ.1 : G → ℂ)
    have hf_eq : f = ∑ χ : {χ : G → ℂ // χ ∈ Work.Clifford.Irr G}, g χ • (χ.1 : G → ℂ) := rfl
    have hfclass : Work.Clifford.IsClassFun f := by
      rw [hf_eq]
      refine Work.Clifford.IsClassFun.sum _ _ (fun χ _ => ?_)
      exact (Work.Clifford.IsClassFun.of_mem_Irr χ.2).smul (g χ)
    have hfrep : ∀ C : ConjClasses G, f (rep C) = 0 := by
      intro C
      have h := congrFun hg C
      have h2 : f (rep C) = (∑ χ : {χ : G → ℂ // χ ∈ Work.Clifford.Irr G}, g χ • M χ) C := by
        simp only [f, M, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [h2, h]
      rfl
    have hfzero : f = 0 := by
      funext x
      have hconj : IsConj x (rep (ConjClasses.mk x)) := by
        rw [← ConjClasses.mk_eq_mk_iff_isConj]
        exact (rep_spec (ConjClasses.mk x)).symm
      obtain ⟨c, hc⟩ := isConj_iff.mp hconj
      rw [← hfclass x c, hc, hfrep (ConjClasses.mk x)]
      rfl
    intro χ₀
    have hchar0 : Work.Clifford.charPair f χ₀.1 = 0 := by
      rw [hfzero]; simp [Work.Clifford.charPair]
    have hsum : Work.Clifford.charPair f χ₀.1 =
        ∑ χ : {χ : G → ℂ // χ ∈ Work.Clifford.Irr G},
          g χ * Work.Clifford.charPair χ.1 χ₀.1 := by
      rw [hf_eq]
      exact Work.Clifford.charPair_sum_left Finset.univ g (fun χ => (χ.1 : G → ℂ)) χ₀.1
    have key : (∑ χ : {χ : G → ℂ // χ ∈ Work.Clifford.Irr G},
          g χ * Work.Clifford.charPair χ.1 χ₀.1) = g χ₀ := by
      rw [Finset.sum_eq_single χ₀]
      · rw [Work.Clifford.charPair_eq_ite_of_mem_Irr (hcl χ₀) (hcl χ₀), ite_eq_left rfl, mul_one]
      · intro χ _ hχ
        have hne : χ.1 ≠ χ₀.1 := fun hh => hχ (Subtype.ext hh)
        rw [Work.Clifford.charPair_eq_ite_of_mem_Irr (hcl χ) (hcl χ₀), ite_eq_right hne, mul_zero]
      · intro h; exact absurd (Finset.mem_univ χ₀) h
    rw [hsum, key] at hchar0
    exact hchar0
  -- the permutation `σ` of the irreducible characters, `χ ↦ χ ∘ α⁻¹`
  let σ : {χ : G → ℂ // χ ∈ Work.Clifford.Irr G} ≃ {χ : G → ℂ // χ ∈ Work.Clifford.Irr G} :=
    { toFun := fun χ => ⟨Work.Clifford.autChar α χ.1, Work.Clifford.autChar_mem_Irr α χ.2⟩
      invFun := fun χ => ⟨Work.Clifford.autChar α⁻¹ χ.1, Work.Clifford.autChar_mem_Irr α⁻¹ χ.2⟩
      left_inv := fun χ => Subtype.ext (by
        show Work.Clifford.autChar α⁻¹ (Work.Clifford.autChar α χ.1) = χ.1
        rw [← Work.Clifford.autChar_mul_apply, inv_mul_cancel]
        rfl)
      right_inv := fun χ => Subtype.ext (by
        show Work.Clifford.autChar α (Work.Clifford.autChar α⁻¹ χ.1) = χ.1
        rw [← Work.Clifford.autChar_mul_apply, mul_inv_cancel]
        rfl) }
  -- the inverse permutations on conjugacy classes
  have hcancel₁ : ∀ C, ConjClasses.map (α : G →* G)
      (ConjClasses.map ((α.symm : G ≃* G) : G →* G) C) = C := by
    intro C
    obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective C
    rw [Work.Clifford.conjClasses_map_mk, Work.Clifford.conjClasses_map_mk]
    congr 1
    exact MulEquiv.apply_symm_apply α g
  have hcancel₂ : ∀ C, ConjClasses.map ((α.symm : G ≃* G) : G →* G)
      (ConjClasses.map (α : G →* G) C) = C := by
    intro C
    obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective C
    rw [Work.Clifford.conjClasses_map_mk, Work.Clifford.conjClasses_map_mk]
    congr 1
    exact MulEquiv.symm_apply_apply α g
  -- the permutation `τ` of the conjugacy classes, `C ↦ ConjClasses.map α⁻¹ C`
  let τ : ConjClasses G ≃ ConjClasses G :=
    { toFun := ConjClasses.map ((α.symm : G ≃* G) : G →* G)
      invFun := ConjClasses.map (α : G →* G)
      left_inv := fun C => hcancel₁ C
      right_inv := fun C => hcancel₂ C }
  have hcard : Fintype.card {χ : G → ℂ // χ ∈ Work.Clifford.Irr G} =
      Fintype.card (ConjClasses G) := by
    rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card]
    exact Work.Clifford.card_Irr_eq_card_conjClasses
  -- the two permutations are compatible with the character table
  have hrel : ∀ (χ : {χ : G → ℂ // χ ∈ Work.Clifford.Irr G}) (C : ConjClasses G),
      M (σ χ) C = M χ (τ C) := by
    intro χ C
    have hclχ : Work.Clifford.IsClassFun χ.1 := Work.Clifford.IsClassFun.of_mem_Irr χ.2
    have hkey : ConjClasses.mk (rep (ConjClasses.map ((α.symm : G ≃* G) : G →* G) C)) =
        ConjClasses.mk (((α.symm : G ≃* G) : G →* G) (rep C)) := by
      calc ConjClasses.mk (rep (ConjClasses.map ((α.symm : G ≃* G) : G →* G) C))
          = ConjClasses.map ((α.symm : G ≃* G) : G →* G) C := rep_spec _
        _ = ConjClasses.map ((α.symm : G ≃* G) : G →* G) (ConjClasses.mk (rep C)) := by
              rw [rep_spec C]
        _ = ConjClasses.mk (((α.symm : G ≃* G) : G →* G) (rep C)) :=
              Work.Clifford.conjClasses_map_mk _ _
    obtain ⟨c, hc⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp hkey)
    show Work.Clifford.autChar α χ.1 (rep C) =
        χ.1 (rep (ConjClasses.map ((α.symm : G ≃* G) : G →* G) C))
    have haux : Work.Clifford.autChar α χ.1 (rep C) =
        χ.1 (((α.symm : G ≃* G) : G →* G) (rep C)) := rfl
    rw [haux, ← hc]
    exact hclχ _ c
  -- fixed points of `σ` are the `α`-fixed irreducible characters
  have hσfix : Nat.card {x : {χ : G → ℂ // χ ∈ Work.Clifford.Irr G} // σ x = x} =
      Nat.card {χ : G → ℂ // χ ∈ Work.Clifford.Irr G ∧ Work.Clifford.IsFixedIrr α χ} := by
    apply Nat.card_congr
    refine
      { toFun := fun x => ⟨x.1.1, x.1.2, ?_⟩
        invFun := fun χ => ⟨⟨χ.1, χ.2.1⟩, ?_⟩
        left_inv := fun x => Subtype.ext rfl
        right_inv := fun χ => Subtype.ext rfl }
    · exact congrArg Subtype.val x.2
    · exact Subtype.ext χ.2.2
  -- fixed points of `τ` are the `α`-fixed conjugacy classes
  have hτfix : Nat.card {C : ConjClasses G // τ C = C} =
      Nat.card {C : ConjClasses G // Work.Clifford.IsFixedClass α C} := by
    apply Nat.card_congr
    refine
      { toFun := fun C => ⟨C.1, ?_⟩
        invFun := fun C => ⟨C.1, ?_⟩
        left_inv := fun C => Subtype.ext rfl
        right_inv := fun C => Subtype.ext rfl }
    · have hC : ConjClasses.map ((α.symm : G ≃* G) : G →* G) C.1 = C.1 := C.2
      have h := hcancel₁ C.1
      rw [hC] at h
      exact h
    · have hC : ConjClasses.map (α : G →* G) C.1 = C.1 := C.2
      have h := hcancel₂ C.1
      rw [hC] at h
      exact h
  rw [← hσfix, ← hτfix]
  exact Work.Clifford.brauer_permutation_lemma M σ τ hli hcard hrel

end Work.Clifford
