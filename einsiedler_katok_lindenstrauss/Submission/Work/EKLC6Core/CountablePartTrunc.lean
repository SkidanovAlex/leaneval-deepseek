import Mathlib
import Submission.Work.EKLC6Core.Basic

/-!
# Truncations of a countable partition

Given a countable partition `P : ℕ → Set X` (measurable, pairwise disjoint, covering), the
truncation `truncPart P l` is the finite partition whose parts are `P 0, …, P (l-1)` together
with the "tail" `(⋃_{k<l} P k)ᶜ`.

The lemmas here are the bookkeeping used by the countable-generator form of Pisa 7.6(ii):
the truncations refine, they generate `σ(range P)`, and the σ-algebra of the `l`-th truncation
is contained in `σ(range P)`.
-/

open MeasureTheory

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

variable {X : Type*} [MeasurableSpace X]

/-- The `l`-th truncation of the countable partition `P`: the pieces `P 0, …, P (l-1)` together
with the tail `(⋃_{k<l} P k)ᶜ`. -/
def truncPart (P : ℕ → Set X) (hPmeas : ∀ n, MeasurableSet (P n))
    (hPdisj : ∀ m n : ℕ, m ≠ n → Disjoint (P m) (P n)) (l : ℕ) : FinPart X where
  n := l + 1
  parts := fun i => if (i : ℕ) < l then P (i : ℕ) else (⋃ j : Fin l, P (j : ℕ))ᶜ
  measurable := by
    intro i
    by_cases hi : (i : ℕ) < l
    · simp only [hi, if_true]
      exact hPmeas _
    · simp only [hi, if_false]
      exact (MeasurableSet.iUnion fun j : Fin l => hPmeas _).compl
  disjoint := by
    intro i j hij
    by_cases hi : (i : ℕ) < l
    · by_cases hj : (j : ℕ) < l
      · simp only [hi, hj, if_true]
        exact hPdisj _ _ (fun h => hij (Fin.ext h))
      · simp only [hi, hj, if_false]
        rw [Set.disjoint_compl_right_iff_subset]
        exact fun x hx => Set.mem_iUnion.mpr ⟨⟨(i : ℕ), hi⟩, hx⟩
    · simp only [hi, if_false]
      by_cases hj : (j : ℕ) < l
      · simp only [hj, if_true]
        rw [Set.disjoint_compl_left_iff_subset]
        exact fun x hx => Set.mem_iUnion.mpr ⟨⟨(j : ℕ), hj⟩, hx⟩
      · exfalso
        apply hij
        apply Fin.ext
        have h1 : (i : ℕ) = l := by have := i.isLt; omega
        have h2 : (j : ℕ) = l := by have := j.isLt; omega
        omega
  cover := by
    refine Set.eq_univ_of_forall fun x => ?_
    by_cases hx : x ∈ ⋃ j : Fin l, P (j : ℕ)
    · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
      refine Set.mem_iUnion.mpr ⟨⟨(j : ℕ), by have := j.isLt; omega⟩, ?_⟩
      simp only [j.isLt, if_true]
      exact hj
    · refine Set.mem_iUnion.mpr ⟨⟨l, Nat.lt_succ_self l⟩, ?_⟩
      simp only [Fin.val_mk, lt_self_iff_false, if_false]
      exact hx

section

variable {P : ℕ → Set X} {hPmeas : ∀ n, MeasurableSet (P n)}
  {hPdisj : ∀ m n : ℕ, m ≠ n → Disjoint (P m) (P n)}

theorem truncPart_apply_lt {l k : ℕ} (hk : k < l) :
    (truncPart P hPmeas hPdisj l).parts ⟨k, by show k < l + 1; omega⟩ = P k := by
  simp only [truncPart, Fin.val_mk, hk, if_true]

theorem truncPart_apply_last {l : ℕ} (i : Fin (l+1)) (hi : ¬ (i : ℕ) < l) :
    (truncPart P hPmeas hPdisj l).parts i = (⋃ j : Fin l, P (j : ℕ))ᶜ := by
  simp only [truncPart, hi, if_false]

/-- The σ-algebra of a truncation is contained in `σ(range P)`. -/
theorem partSigma_truncPart_le (l : ℕ) :
    partSigma (truncPart P hPmeas hPdisj l) ≤ MeasurableSpace.generateFrom (Set.range P) := by
  rw [partSigma]
  refine MeasurableSpace.generateFrom_le ?_
  rintro s ⟨i, rfl⟩
  by_cases hi : (i : ℕ) < l
  · rw [truncPart_apply_lt (P := P) (hPmeas := hPmeas) (hPdisj := hPdisj) hi]
    exact MeasurableSpace.measurableSet_generateFrom ⟨_, rfl⟩
  · rw [truncPart_apply_last (P := P) (hPmeas := hPmeas) (hPdisj := hPdisj) i hi]
    refine MeasurableSet.compl ?_
    refine MeasurableSet.iUnion fun j : Fin l => ?_
    exact MeasurableSpace.measurableSet_generateFrom ⟨_, rfl⟩

/-- The truncations form a refining sequence. -/
theorem partSigma_truncPart_mono (l : ℕ) :
    partSigma (truncPart P hPmeas hPdisj l)
      ≤ partSigma (truncPart P hPmeas hPdisj (l+1)) := by
  rw [partSigma, partSigma]
  refine MeasurableSpace.generateFrom_le ?_
  rintro s ⟨i, rfl⟩
  by_cases hi : (i : ℕ) < l
  · rw [truncPart_apply_lt (P := P) (hPmeas := hPmeas) (hPdisj := hPdisj) hi]
    rw [show P (i : ℕ) = (truncPart P hPmeas hPdisj (l+1)).parts
        ⟨(i : ℕ), by show (i : ℕ) < l + 1 + 1; omega⟩ from
      (truncPart_apply_lt (P := P) (hPmeas := hPmeas) (hPdisj := hPdisj) (l := l+1)
        (k := (i : ℕ)) (by omega)).symm]
    exact MeasurableSpace.measurableSet_generateFrom ⟨_, rfl⟩
  · rw [truncPart_apply_last (P := P) (hPmeas := hPmeas) (hPdisj := hPdisj) i hi]
    refine MeasurableSet.compl ?_
    have hsplit : (⋃ j : Fin l, P (j : ℕ))
        = (⋃ j : Fin l, (truncPart P hPmeas hPdisj (l+1)).parts
            ⟨(j : ℕ), by show (j : ℕ) < l + 1 + 1; omega⟩) := by
      refine Set.iUnion_congr fun j => ?_
      exact (truncPart_apply_lt (P := P) (hPmeas := hPmeas) (hPdisj := hPdisj) (l := l+1)
        (k := (j : ℕ)) (by have := j.isLt; omega)).symm
    rw [hsplit]
    exact MeasurableSet.iUnion fun j : Fin l =>
      MeasurableSpace.measurableSet_generateFrom ⟨_, rfl⟩

/-- The truncations generate `σ(range P)`. -/
theorem iSup_partSigma_truncPart :
    (⨆ l, partSigma (truncPart P hPmeas hPdisj l))
      = MeasurableSpace.generateFrom (Set.range P) := by
  refine le_antisymm (iSup_le fun l => partSigma_truncPart_le l) ?_
  refine MeasurableSpace.generateFrom_le ?_
  rintro s ⟨n, rfl⟩
  have hmem : MeasurableSet[partSigma (truncPart P hPmeas hPdisj (n+1))] (P n) := by
    rw [show P n = (truncPart P hPmeas hPdisj (n+1)).parts
        ⟨n, by show n < n + 1 + 1; omega⟩ from
      (truncPart_apply_lt (P := P) (hPmeas := hPmeas) (hPdisj := hPdisj) (l := n+1)
        (k := n) (Nat.lt_succ_self n)).symm]
    exact MeasurableSpace.measurableSet_generateFrom ⟨_, rfl⟩
  have hle : partSigma (truncPart P hPmeas hPdisj (n+1))
      ≤ (⨆ l, partSigma (truncPart P hPmeas hPdisj l)) :=
    le_iSup (fun l : ℕ => partSigma (truncPart P hPmeas hPdisj l)) (n+1)
  exact hle (P n) hmem

end

end Work.EKLC6Core
