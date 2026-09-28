import Mathlib
import Submission.Work.Q44Geom.planeBound

noncomputable section
open MvPolynomial

namespace Work.Q44Geom

/-- The set of `ℚ`-lines in `ℚ³` (one-dimensional `ℚ`-subspaces) on which all the forms
`G i` vanish. -/
def lineSet {ι : Type*} (G : ι → MvPolynomial (Fin 3) ℚ) :
    Set (Submodule ℚ (Fin 3 → ℚ)) :=
  {L | Module.finrank ℚ L = 1 ∧ ∀ x ∈ L, ∀ i, MvPolynomial.eval x (G i) = 0}

/-- Reindexing the family of forms along an equivalence does not change the line set. -/
theorem lineSet_comp_equiv {ι ι' : Type*} (e : ι ≃ ι')
    (G : ι' → MvPolynomial (Fin 3) ℚ) :
    lineSet (G ∘ e) = lineSet G := by
  ext L
  simp only [lineSet, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hf, h⟩
    refine ⟨hf, fun x hx j => ?_⟩
    have h' := h x hx (e.symm j)
    simpa using h'
  · rintro ⟨hf, h⟩
    exact ⟨hf, fun x hx i => h x hx (e i)⟩

/-- The line set only depends on the indices at which `G` is non-zero: the indices carrying the
zero polynomial impose no condition, so they may be dropped. This is the reduction from an
arbitrary family to a family whose members are all non-zero. -/
theorem lineSet_eq_subtype_ne_zero {ι : Type*} (G : ι → MvPolynomial (Fin 3) ℚ) :
    lineSet G = lineSet (fun s : {i // G i ≠ 0} => G s.val) := by
  ext L
  simp only [lineSet, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hf, h⟩
    exact ⟨hf, fun x hx s => h x hx s.val⟩
  · rintro ⟨hf, h⟩
    refine ⟨hf, fun x hx i => ?_⟩
    by_cases hi : G i = 0
    · rw [hi, map_zero]
    · exact h x hx ⟨i, hi⟩

/-- **Reduction to a finite index type.** The plane bound `B` proved for families of forms
indexed by `Fin n` (all members non-zero) propagates to families indexed by an arbitrary finite
type `ι`. The argument drops the zero members (they impose no condition and, by the coprimality
hypothesis, cannot be all of them) and reindexes the survivors by `Fin (card)`. -/
theorem planeBoundFin (B : ℕ)
    (hB : ∀ (n : ℕ) (G : Fin n → MvPolynomial (Fin 3) ℚ),
      (∀ i, G i ≠ 0) →
      (∀ i, ∃ d : ℕ, d ≤ 4 ∧ (G i).IsHomogeneous d) →
      (∀ h : MvPolynomial (Fin 3) ℚ, (∀ i, h ∣ G i) → IsUnit h) →
      {L : Submodule ℚ (Fin 3 → ℚ) | Module.finrank ℚ L = 1 ∧
        ∀ x ∈ L, ∀ i, MvPolynomial.eval x (G i) = 0}.Finite ∧
      {L : Submodule ℚ (Fin 3 → ℚ) | Module.finrank ℚ L = 1 ∧
        ∀ x ∈ L, ∀ i, MvPolynomial.eval x (G i) = 0}.ncard ≤ B)
    (ι : Type) [Fintype ι] (G : ι → MvPolynomial (Fin 3) ℚ)
    (hdeg : ∀ i, ∃ d : ℕ, d ≤ 4 ∧ (G i).IsHomogeneous d)
    (hgcd : ∀ h, (∀ i, h ∣ G i) → IsUnit h) :
    {L : Submodule ℚ (Fin 3 → ℚ) | Module.finrank ℚ L = 1 ∧
      ∀ x ∈ L, ∀ i, MvPolynomial.eval x (G i) = 0}.Finite ∧
    {L : Submodule ℚ (Fin 3 → ℚ) | Module.finrank ℚ L = 1 ∧
      ∀ x ∈ L, ∀ i, MvPolynomial.eval x (G i) = 0}.ncard ≤ B := by
  show (lineSet G).Finite ∧ (lineSet G).ncard ≤ B
  classical
  let eS : {i : ι // G i ≠ 0} ≃ Fin (Fintype.card {i : ι // G i ≠ 0}) :=
    Fintype.equivFin _
  let G' : Fin (Fintype.card {i : ι // G i ≠ 0}) → MvPolynomial (Fin 3) ℚ :=
    fun j => G (eS.symm j).val
  have hEq : lineSet G = lineSet G' := by
    rw [show lineSet G = lineSet (fun s : {i : ι // G i ≠ 0} => G s.val) from
      lineSet_eq_subtype_ne_zero G]
    exact (lineSet_comp_equiv eS.symm (fun s : {i : ι // G i ≠ 0} => G s.val)).symm
  have hne : ∀ j : Fin (Fintype.card {i : ι // G i ≠ 0}), G' j ≠ 0 :=
    fun j => (eS.symm j).2
  have hhom : ∀ j : Fin (Fintype.card {i : ι // G i ≠ 0}),
      ∃ d : ℕ, d ≤ 4 ∧ (G' j).IsHomogeneous d :=
    fun j => hdeg (eS.symm j).val
  have hcop : ∀ h : MvPolynomial (Fin 3) ℚ, (∀ j, h ∣ G' j) → IsUnit h := by
    intro h hj
    apply hgcd h
    intro i
    by_cases hi : G i = 0
    · rw [hi]; exact dvd_zero h
    · have hji : h ∣ G' (eS ⟨i, hi⟩) := hj (eS ⟨i, hi⟩)
      have hval : G' (eS ⟨i, hi⟩) = G i := by
        show G (eS.symm (eS ⟨i, hi⟩)).val = G i
        rw [Equiv.symm_apply_apply]
      rwa [hval] at hji
  have hres : (lineSet G').Finite ∧ (lineSet G').ncard ≤ B :=
    hB (Fintype.card {i : ι // G i ≠ 0}) G' hne hhom hcop
  rwa [← hEq] at hres

end Work.Q44Geom
