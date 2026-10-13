/-
  WilE4 / CAD — the set identity of the iterated projection (`projSeq`), proved directly.

  This is the `projSeq` version of `exists_projSeq`'s induction: `projSeq k j` removes the last `j`
  coordinates, and if the top family is closed under `pderiv` in the last variable (and the atoms of
  `Z` lie in it), its set is the set of points of `ℝ^{k+1}` that extend by `j` more coordinates into
  `Z`.
-/
import Mathlib
import Submission.Work.WilE4.CAD.FiberClosureDefs
import Submission.Work.WilE4.CAD.Level
import Submission.Work.WilE4.CAD.CellsUnion
import Submission.Work.WilE4.CAD.CadCells_isUnionOf
import Submission.Work.WilE4.CAD.CadCells_covers
import Submission.Work.WilE4.CAD.exists_projSeq

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Classical
namespace Work.WilE4.CAD

open MvPolynomial Polynomial
open Work.WilE4 (rot spec tower)

/-! ## Two elementary facts about `extend` -/

/-- Adding no coordinate: `extend k 0` is the identity. -/
theorem extend_zero_apply (k : ℕ) (x : Fin (k+1) → ℝ) (v : Fin 0 → ℝ) : extend k 0 x v = x := by
  have hv : v = (Fin.elim0 : Fin 0 → ℝ) := Subsingleton.elim _ _
  rw [hv]
  simp only [extend]
  rw [← Fin.snoc_eq_append, Fin.snoc_init_self]

/-- Splitting off the last of the `j+1` extra coordinates. -/
theorem extend_succ_apply (k j : ℕ) (x : Fin (k+1) → ℝ) (w : Fin (j+1) → ℝ) :
    extend k (j+1) x w = Fin.snoc (extend k j x (Fin.init w)) (w (Fin.last j)) := by
  have h := snoc_extend (k := k) (j := j) x (Fin.init w) (w (Fin.last j))
  rw [Fin.snoc_init_self] at h
  exact h.symm

/-- The extension by `j+1` coordinates, split off at the last one. -/
theorem exists_extend_succ_iff (k j : ℕ) (x : Fin (k+1) → ℝ) (Z : SAd (k+(j+2))) :
    (∃ w : Fin (j+1) → ℝ, extend k (j+1) x w ∈ Z.set) ↔
      ∃ v : Fin j → ℝ, extend k j x v ∈ WilkiesDesign.projLast Z.set := by
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨Fin.init w, w (Fin.last j), ?_⟩
    rw [← extend_succ_apply]
    exact hw
  · rintro ⟨v, t, ht⟩
    refine ⟨Fin.snoc v t, ?_⟩
    rw [extend_succ_apply, Fin.init_snoc, Fin.snoc_last]
    exact ht

/-! ## The iterated projection -/

/-- The set of the iterated projection, with the union-of-cells hypothesis at each level (which is
what the induction needs). -/
theorem projSeq_set_aux (k : ℕ) (j : ℕ) :
    ∀ (Z : SAd (k+(j+1))) (H : List (MvPolynomial (Fin (k+(j+1))) ℝ)),
      (∀ i : Fin H.length, ∃ i' : Fin H.length,
        H.get i' = MvPolynomial.pderiv (Fin.last (k+j)) (H.get i)) →
      (∀ C ∈ CadCells (k+(j+1)) H, C.set ⊆ Z.set ∨ Disjoint C.set Z.set) →
      (projSeq k j (Z,H)).1.set =
        {x : Fin (k+1) → ℝ | ∃ v : Fin j → ℝ, extend k j x v ∈ Z.set} := by
  induction j with
  | zero =>
    intro Z H hclosed hUn
    rw [projSeq_zero]
    ext x
    constructor
    · intro hx
      exact ⟨Fin.elim0, by simpa only [extend_zero_apply] using hx⟩
    · rintro ⟨v, hv⟩
      rwa [extend_zero_apply] at hv
  | succ j ih =>
    intro Z H hclosed hUn
    have hUn₁ : ∀ C ∈ CadCells (k+(j+1)) (projDataT (k+j+1) H),
        C.set ⊆ (projSAd (k := k+j+1) H Z).set ∨
          Disjoint C.set (projSAd (k := k+j+1) H Z).set :=
      fun C hC => cell_subset_unionCells_or_disjoint (projDataT (k+j+1) H) (projCells H Z)
        (fun D hD => (projCells_mem H Z D hD).1) C hC
    have hih := ih (projSAd (k := k+j+1) H Z) (projDataT (k+j+1) H)
      (projDataT_deriv_closed (m := k+j) H) hUn₁
    have hproj : (projSAd (k := k+j+1) H Z).set = WilkiesDesign.projLast Z.set :=
      projSAd_set (k := k+j+1) (H := H) (Z := Z)
        (CadCells_covers (projDataT (k+j+1) H)) hUn
        (realizedOn_all_projDataT (k+j+1) H hclosed)
    rw [projSeq_succ]
    change (projSeq k j (projSAd (k := k+j+1) H Z, projDataT (k+j+1) H)).1.set = _
    rw [hih, hproj]
    ext x
    exact (exists_extend_succ_iff k j x Z).symm

/-- Set identity of the iterated last-coordinate projection. -/
theorem projSeq_set_apply (k j : ℕ) (Z : SAd (k+(j+1)))
    (H : List (MvPolynomial (Fin (k+(j+1))) ℝ))
    (hclosed : ∀ i : Fin H.length, ∃ i' : Fin H.length,
      H.get i' = MvPolynomial.pderiv (Fin.last (k+j)) (H.get i))
    (hatoms : ∀ B ∈ Z.basics, ∀ P ∈ B.eqs ++ B.pos, P ∈ H) :
    (projSeq k j (Z,H)).1.set = {x : Fin (k+1) → ℝ | ∃ v : Fin j → ℝ, extend k j x v ∈ Z.set} :=
  projSeq_set_aux k j Z H hclosed (CadCells_isUnionOf H Z hatoms)

end Work.WilE4.CAD
