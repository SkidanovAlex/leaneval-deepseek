import Mathlib
import Submission.Work.DSG4a.FreeResDefs

namespace Work.DSG4a

open CategoryTheory Limits

universe u

/-! ## Elementary facts about finitely generated and free modules

The resolution `F` is built by extending the syzygy complex `Kcc` along the embedding
`down ℕ → up ℤ`, `n ↦ -n`.  Its terms are therefore either one of the terms
`Kcc.X n = (Fin (stateSeq M n).m → A)` (of which there are, in particular, finitely many
generators) or zero (in the positive degrees, which lie outside the image of the embedding).
The two lemmas below handle the second alternative. -/

/-- A module with a single element is finitely generated (it is the span of the empty set). -/
private lemma module_finite_of_subsingleton {R M : Type*} [Semiring R] [AddCommMonoid M]
    [Module R M] [Subsingleton M] : Module.Finite R M := by
  rw [Module.finite_def]
  refine ⟨∅, ?_⟩
  rw [Finset.coe_empty, Submodule.span_empty]
  refine le_antisymm bot_le fun x _ => ?_
  rw [Submodule.mem_bot]
  exact Subsingleton.elim x 0

/-- A zero object of `ModuleCat R` is finitely generated. -/
private lemma moduleCat_finite_of_isZero {R : Type*} [Ring R] {P : ModuleCat R} (h : IsZero P) :
    Module.Finite R P :=
  haveI := ModuleCat.isZero_iff_subsingleton.mp h
  module_finite_of_subsingleton

/-- A zero object of `ModuleCat R` is free. -/
private lemma moduleCat_free_of_isZero {R : Type*} [Ring R] {P : ModuleCat R} (h : IsZero P) :
    Module.Free R P :=
  haveI := ModuleCat.isZero_iff_subsingleton.mp h
  Module.Free.of_subsingleton R _

/-- The embedding `emb` sends `n` to `-n`. -/
private lemma emb_f_apply (n : ℕ) : (emb).f n = -(n : ℤ) := by
  simp [emb, ComplexShape.embeddingUpIntLE_f]

/-- Every `i ≤ 0` lies in the image of `emb`, namely `i = emb.f ((-i).toNat)`. -/
private lemma emb_f_toNat (i : ℤ) (hi : i ≤ 0) : (emb).f ((-i).toNat) = i := by
  rw [emb_f_apply]
  have h3 : ((-i).toNat : ℤ) = -i := Int.toNat_of_nonneg (by omega)
  omega

/-- For `i ≤ 0` the index `i` is in the image of `emb`. -/
private lemma emb_r_of_nonpos (i : ℤ) (hi : i ≤ 0) :
    (emb).r i = some ((-i).toNat) :=
  ComplexShape.Embedding.r_eq_some emb (emb_f_toNat i hi)

/-- For `i > 0` the index `i` is not in the image of `emb`. -/
private lemma emb_r_of_pos (i : ℤ) (hi : 0 < i) : (emb).r i = none :=
  ComplexShape.Embedding.r_eq_none emb i (by
    intro n hn
    rw [emb_f_apply] at hn
    omega)

/-- The terms of the syzygy complex `Kcc` are finitely generated free modules. -/
private lemma Kcc_finite_free {A : Type u} [CommRing A] [IsNoetherianRing A]
    (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M] (n : ℕ) :
    Module.Finite A ((Kcc (A:=A) M).X n) ∧ Module.Free A ((Kcc (A:=A) M).X n) :=
  ⟨by
    show Module.Finite A (Fin ((stateSeq (A:=A) M n).m) → A)
    infer_instance,
  by
    show Module.Free A (Fin ((stateSeq (A:=A) M n).m) → A)
    infer_instance⟩

/-- In non-positive degrees the resolution `F` agrees with `Kcc` (up to the reindexing
`i ↦ -i`); in particular its `i`-th term is the free module `Fin (stateSeq M (-i).toNat) → A`. -/
private lemma F_X_of_nonpos {A : Type u} [CommRing A] [IsNoetherianRing A]
    (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M] (i : ℤ) (hi : i ≤ 0) :
    (F (A:=A) M).X i = (Kcc (A:=A) M).X ((-i).toNat) := by
  rw [show (F (A:=A) M).X i
      = HomologicalComplex.extend.X (Kcc (A:=A) M) (emb.r i) from rfl,
    emb_r_of_nonpos i hi]
  rfl

/-- In positive degrees the resolution `F` vanishes. -/
private lemma isZero_F_X_of_pos {A : Type u} [CommRing A] [IsNoetherianRing A]
    (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M] (i : ℤ) (hi : 0 < i) :
    IsZero ((F (A:=A) M).X i) := by
  apply HomologicalComplex.isZero_extend_X
  intro n hn
  rw [emb_f_apply] at hn
  omega

/-- The terms of the free resolution `F` of a finitely generated module over a Noetherian
ring are finitely generated free modules. -/
theorem F_finite_free {A : Type u} [CommRing A] [IsNoetherianRing A]
    (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M] :
    (∀ i : ℤ, Module.Finite A ((F (A:=A) M).X i)) ∧
      (∀ i : ℤ, Module.Free A ((F (A:=A) M).X i)) := by
  constructor
  · intro i
    rcases le_or_gt i 0 with hi | hi
    · rw [F_X_of_nonpos M i hi]
      exact (Kcc_finite_free M _).1
    · exact moduleCat_finite_of_isZero (isZero_F_X_of_pos M i hi)
  · intro i
    rcases le_or_gt i 0 with hi | hi
    · rw [F_X_of_nonpos M i hi]
      exact (Kcc_finite_free M _).2
    · exact moduleCat_free_of_isZero (isZero_F_X_of_pos M i hi)

end Work.DSG4a
