import Submission.WeylRoots
import Submission.WeylWeights

/-!
# The Weyl group of `E₈`: the root reflection, the length function and the dominant chamber

This file develops the elementary Weyl-group combinatorics of `E₈` on top of
`Submission.WeylRoots` (the 240 roots of `E₈` in `d`-coordinates).  A weight is a vector
`v : Fin 8 → ℤ` in the `ω`-basis (`v j = ⟨v, α_j∨⟩`), so that the simple reflection at the node `i`
acts by `(sᵢ v) j = v j - v i * A i j` (`Submission.WeylWeights.sref`).
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

noncomputable section
open scoped BigOperators

namespace Submission.WeylReflect

open Submission.WeylRoots Submission.WeylWeights

variable {i : Fin 8} {v d : Fin 8 → ℤ}

/-! ## Elementary properties of the pairing -/

lemma pair_sub_right (v d₁ d₂ : Fin 8 → ℤ) : pair v (d₁ - d₂) = pair v d₁ - pair v d₂ := by
  simp only [pair, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

/-- `⟨v, c·αᵢ∨⟩ = c·v i`. -/
lemma pair_smul_e (v : Fin 8 → ℤ) (i : Fin 8) (c : ℤ) : pair v (c • e i) = c * v i := by
  simp only [pair, e, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  rw [show (∑ j, v j * (c * if j = i then (1 : ℤ) else 0)) =
      ∑ j, (if j = i then v j * c else 0) by
    apply Finset.sum_congr rfl; intro j _
    by_cases h : j = i <;> simp [h]]
  simp [mul_comm]

lemma pair_neg (v d : Fin 8 → ℤ) : pair v (-d) = -pair v d := by
  simp only [pair, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]

lemma pair_e (v : Fin 8 → ℤ) (i : Fin 8) : pair v (e i) = v i := by
  have h := pair_smul_e v i 1
  rw [one_smul, one_mul] at h
  exact h

/-- The value `⟨α, αᵢ∨⟩ = (A · d) i` of a root at the node `i`. -/
def cval (i : Fin 8) (d : Fin 8 → ℤ) : ℤ := ∑ k, A i k * d k

lemma rref_eq (i : Fin 8) (d : Fin 8 → ℤ) : rref i d = d - cval i d • e i := rfl

lemma rref_apply (i : Fin 8) (d : Fin 8 → ℤ) (j : Fin 8) :
    rref i d j = d j - cval i d * (if j = i then (1 : ℤ) else 0) := by
  simp only [rref, cval, Pi.sub_apply, Pi.smul_apply, e, Pi.single_apply, smul_eq_mul]

lemma pair_rref (i : Fin 8) (v d : Fin 8 → ℤ) : pair v (rref i d) = pair v d - cval i d * v i := by
  rw [rref_eq, pair_sub_right, pair_smul_e]

/-- **The Cartan pairing is invariant under the simple reflections**:
`⟨sᵢ v, α∨⟩ = ⟨v, (sᵢ α)∨⟩`. -/
lemma pair_sref (i : Fin 8) (v d : Fin 8 → ℤ) : pair (sref i v) d = pair v (rref i d) := by
  rw [pair_rref]
  have h : pair (sref i v) d = pair v d - v i * cval i d := by
    simp only [pair, sref_apply, cval, A, Int.cast_id]
    rw [show (∑ j, (v j - v i * CartanMatrix.E₈ i j) * d j)
        = ∑ j, (v j * d j - v i * (CartanMatrix.E₈ i j * d j)) by
      apply Finset.sum_congr rfl; intro j _; ring]
    rw [Finset.sum_sub_distrib, Finset.mul_sum]
  rw [h]; ring

lemma cval_rref (i : Fin 8) (d : Fin 8 → ℤ) : cval i (rref i d) = -cval i d := by
  have expand : cval i (rref i d)
      = ∑ k, (A i k * d k - cval i d * (A i k * (if k = i then (1 : ℤ) else 0))) := by
    apply Finset.sum_congr rfl; intro k _
    simp only [cval, rref, Pi.sub_apply, Pi.smul_apply, e, Pi.single_apply, smul_eq_mul]
    ring
  rw [expand, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [show (∑ k, A i k * (if k = i then (1 : ℤ) else 0)) = A i i by
    rw [show (∑ k, A i k * (if k = i then (1 : ℤ) else 0)) = ∑ k, (if k = i then A i k else 0) by
      apply Finset.sum_congr rfl; intro k _
      by_cases h : k = i <;> simp [h]]
    simp]
  rw [show A i i = 2 from E8_diag i]
  simp only [cval]
  ring

/-- The reflected `d`-coordinates form an involution of the root lattice. -/
lemma rref_involutive (i : Fin 8) : Function.Involutive (rref i) := by
  intro d
  funext j
  rw [rref_apply, cval_rref, rref_apply]
  by_cases hj : j = i <;> simp [hj]


/-! ## The positive roots and the length function -/

/-- The simple root `αᵢ` (in `d`-coordinates, i.e. `eᵢ`) is a positive root. -/
theorem e_mem_PD (i : Fin 8) : e i ∈ PD := by
  fin_cases i <;> decide

/-- `-αᵢ` is not a positive root. -/
theorem neg_e_notMem_PD (i : Fin 8) : -(e i) ∉ PD := by
  fin_cases i <;> decide

private theorem rref_mem_rootsD_0 : rootsD.all (fun d => decide (rref 0 d ∈ rootsD)) = true := by decide
private theorem rref_mem_rootsD_1 : rootsD.all (fun d => decide (rref 1 d ∈ rootsD)) = true := by decide
private theorem rref_mem_rootsD_2 : rootsD.all (fun d => decide (rref 2 d ∈ rootsD)) = true := by decide
private theorem rref_mem_rootsD_3 : rootsD.all (fun d => decide (rref 3 d ∈ rootsD)) = true := by decide
private theorem rref_mem_rootsD_4 : rootsD.all (fun d => decide (rref 4 d ∈ rootsD)) = true := by decide
private theorem rref_mem_rootsD_5 : rootsD.all (fun d => decide (rref 5 d ∈ rootsD)) = true := by decide
private theorem rref_mem_rootsD_6 : rootsD.all (fun d => decide (rref 6 d ∈ rootsD)) = true := by decide
private theorem rref_mem_rootsD_7 : rootsD.all (fun d => decide (rref 7 d ∈ rootsD)) = true := by decide

theorem rref_mem_rootsD (i : Fin 8) :
    rootsD.all (fun d => decide (rref i d ∈ rootsD)) = true := by
  fin_cases i
  · exact rref_mem_rootsD_0
  · exact rref_mem_rootsD_1
  · exact rref_mem_rootsD_2
  · exact rref_mem_rootsD_3
  · exact rref_mem_rootsD_4
  · exact rref_mem_rootsD_5
  · exact rref_mem_rootsD_6
  · exact rref_mem_rootsD_7
private theorem PD_image_rref_0 : PD.image (rref 0) = insert (-(e 0)) (PD.erase (e 0)) := by decide
private theorem PD_image_rref_1 : PD.image (rref 1) = insert (-(e 1)) (PD.erase (e 1)) := by decide
private theorem PD_image_rref_2 : PD.image (rref 2) = insert (-(e 2)) (PD.erase (e 2)) := by decide
private theorem PD_image_rref_3 : PD.image (rref 3) = insert (-(e 3)) (PD.erase (e 3)) := by decide
private theorem PD_image_rref_4 : PD.image (rref 4) = insert (-(e 4)) (PD.erase (e 4)) := by decide
private theorem PD_image_rref_5 : PD.image (rref 5) = insert (-(e 5)) (PD.erase (e 5)) := by decide
private theorem PD_image_rref_6 : PD.image (rref 6) = insert (-(e 6)) (PD.erase (e 6)) := by decide
private theorem PD_image_rref_7 : PD.image (rref 7) = insert (-(e 7)) (PD.erase (e 7)) := by decide

theorem PD_image_rref (i : Fin 8) : PD.image (rref i) = insert (-(e i)) (PD.erase (e i)) := by
  fin_cases i
  · exact PD_image_rref_0
  · exact PD_image_rref_1
  · exact PD_image_rref_2
  · exact PD_image_rref_3
  · exact PD_image_rref_4
  · exact PD_image_rref_5
  · exact PD_image_rref_6
  · exact PD_image_rref_7

/-- The number of positive roots paired negatively with a weight.  This is the length of the
element of the Weyl group that takes the weight into the dominant chamber. -/
def negCount (v : Fin 8 → ℤ) : ℕ := (PD.filter (fun d => pair v d < 0)).card

/-- **Reflecting a weight with a negative `i`-th coordinate decreases `negCount` by one.**  This is
the termination measure of the reflection algorithm below. -/
theorem negCount_sref (i : Fin 8) (v : Fin 8 → ℤ) (hv : v i < 0) :
    negCount (sref i v) = negCount v - 1 := by
  classical
  have hQneg : ¬ (pair v (-(e i)) < 0) := by
    rw [pair_neg, pair_e]; omega
  have hQpos : pair v (e i) < 0 := by rw [pair_e]; exact hv
  have hinj : Function.Injective (rref i) := (rref_involutive i).injective
  have hstep : PD.filter (fun d => pair (sref i v) d < 0)
      = PD.filter (fun d => pair v (rref i d) < 0) :=
    Finset.filter_congr (fun d _ => by rw [pair_sref])
  have hcard1 : (PD.filter (fun d => pair v (rref i d) < 0)).card
      = ((PD.image (rref i)).filter (fun d => pair v d < 0)).card := by
    rw [Finset.filter_image]
    exact (Finset.card_image_of_injOn (fun a _ b _ h => hinj h)).symm
  have hcard2 : ((insert (-(e i)) (PD.erase (e i))).filter (fun d => pair v d < 0)).card
      = ((PD.erase (e i)).filter (fun d => pair v d < 0)).card := by
    rw [Finset.filter_insert, if_neg hQneg]
  have hcard3 : ((PD.erase (e i)).filter (fun d => pair v d < 0)).card = negCount v - 1 := by
    have hins : PD = insert (e i) (PD.erase (e i)) := (Finset.insert_erase (e_mem_PD i)).symm
    have hmain : negCount v = ((PD.erase (e i)).filter (fun d => pair v d < 0)).card + 1 := by
      have h1 : negCount v = (PD.filter (fun d => pair v d < 0)).card := rfl
      rw [h1]
      conv_lhs => rw [hins]
      rw [Finset.filter_insert, if_pos hQpos]
      rw [Finset.card_insert_of_notMem]
      intro h
      rw [Finset.mem_filter] at h
      exact Finset.notMem_erase _ _ h.1
    omega
  change (PD.filter (fun d => pair (sref i v) d < 0)).card = negCount v - 1
  rw [hstep, hcard1, PD_image_rref, hcard2]
  exact hcard3

/-- A weight is dominant when all its `ω`-coordinates are nonnegative. -/
def Dominant (v : Fin 8 → ℤ) : Prop := ∀ i, 0 ≤ v i

/-- A weight with no negatively paired positive root is dominant. -/
theorem dominant_of_negCount_zero {v : Fin 8 → ℤ} (h : negCount v = 0) : Dominant v := by
  intro i
  by_contra hi
  have hmem : e i ∈ PD.filter (fun d => pair v d < 0) := by
    rw [Finset.mem_filter]
    exact ⟨e_mem_PD i, by rw [pair_e]; omega⟩
  have : 0 < negCount v := by
    rw [negCount]
    exact Finset.card_pos.mpr ⟨e i, hmem⟩
  omega

/-- `v'` is obtained from `v` by a sequence of simple reflections. -/
def WConj (v v' : Fin 8 → ℤ) : Prop := ∃ L : List (Fin 8), L.foldl (fun w i => sref i w) v = v'

theorem WConj_refl (v : Fin 8 → ℤ) : WConj v v := ⟨[], rfl⟩

theorem WConj.step {v v' : Fin 8 → ℤ} (i : Fin 8) (h : WConj (sref i v) v') : WConj v v' := by
  obtain ⟨L, hL⟩ := h
  exact ⟨i :: L, by simpa using hL⟩

/-- **Every weight of the weight lattice can be reflected into the dominant chamber** by a sequence
of simple reflections.  (The Weyl group has 696 729 600 elements, so this is proved by the length
function `negCount` and never by generating the group.) -/
theorem exists_dominant_WConj (v : Fin 8 → ℤ) : ∃ v', WConj v v' ∧ Dominant v' := by
  suffices H : ∀ n, ∀ v : Fin 8 → ℤ, negCount v = n → ∃ v', WConj v v' ∧ Dominant v' by
    exact H (negCount v) v rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro v hv
    by_cases hd : Dominant v
    · exact ⟨v, WConj_refl v, hd⟩
    · obtain ⟨i, hi⟩ : ∃ i, v i < 0 := by
        by_contra hcon
        exact hd (fun i => le_of_not_gt (fun hvi => hcon ⟨i, hvi⟩))
      have hpos : 0 < negCount v := by
        rw [negCount]
        exact Finset.card_pos.mpr ⟨e i, by
          rw [Finset.mem_filter]
          exact ⟨e_mem_PD i, by rw [pair_e]; exact hi⟩⟩
      have hlt : negCount (sref i v) < n := by
        rw [negCount_sref i v hi, ← hv]; omega
      obtain ⟨v', hv', hd'⟩ := ih (negCount (sref i v)) hlt (sref i v) rfl
      exact ⟨v', WConj.step i hv', hd'⟩

end Submission.WeylReflect

