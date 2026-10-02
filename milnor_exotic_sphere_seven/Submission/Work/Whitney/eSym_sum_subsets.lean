import Mathlib
import Submission.Work.Whitney.cruxDefs
import Submission.Work.Gen.eSymClass
import Submission.Work.Gen.lineSumCore_top_chern

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-!
# The sum of the complementary top elementary symmetric classes

`Work.Whitney.eSym_sum_subsets`: for a family `M : Fin N → (complex line bundles over B)`,

  `∑_{k : Fin N} eSym (N-1) (M ∘ skipIdx k) (N-1) = eSym N M (N-1)`,

i.e. the sum, over the `N` ways of dropping one summand, of the top elementary symmetric class of
the remaining `N-1` summands is the second-highest elementary symmetric class of the full family.
Both sides are `∑_{k} ∏_{i ≠ k} c₁(M i)`.

The proof reduces to the combinatorial identity `Work.Gen.eSymC_sum_skipIdx_succ` for the
elementary symmetric classes `eSymC` of a family of arbitrary degree-`2` classes, which is proved
by induction on the number of variables using the top-degree recursion of `eSymC` and the relation
between the maps `skipIdx` at successive levels.
-/

namespace Work.Whitney

open Work.TangentClasses Work.Thom

noncomputable section

variable {B : Type} [TopologicalSpace B]

/-! ## The map `skipIdx` in coordinates -/

/-- **The value of `skipIdx`**: `skipIdx hN k i` is `i` if `i < k` and `i + 1` otherwise, i.e. the
increasing enumeration of `Fin N ∖ {k}`. -/
theorem skipIdx_val {N : ℕ} (hN : 1 ≤ N) (k : Fin N) (i : Fin (N - 1)) :
    ((Work.Whitney.skipIdx hN k i : Fin N) : ℕ)
      = if (i : ℕ) < (k : ℕ) then (i : ℕ) else (i : ℕ) + 1 := by
  have key : Work.Whitney.skipIdx hN k i
      = Fin.cast (show (N - 1) + 1 = N by omega)
          (Fin.succAbove (Fin.cast (show N = (N - 1) + 1 by omega) k) i) := rfl
  rw [key]
  simp only [Fin.val_cast]
  by_cases hik : (i : ℕ) < (k : ℕ)
  · have hlt : i.castSucc < Fin.cast (show N = (N-1)+1 by omega) k := by
      rw [Fin.lt_def, Fin.val_castSucc, Fin.val_cast]; exact hik
    rw [Fin.succAbove_of_castSucc_lt _ _ hlt, Fin.val_castSucc]
    exact (if_pos hik).symm
  · have hle : Fin.cast (show N = (N-1)+1 by omega) k ≤ i.castSucc := by
      rw [Fin.le_def, Fin.val_castSucc, Fin.val_cast]; omega
    rw [Fin.succAbove_of_le_castSucc _ _ hle, Fin.val_succ]
    exact (if_neg hik).symm

/-- **Skipping the last index is the inclusion `Fin n ↪ Fin (n+1)`.** -/
theorem skipIdx_last (n : ℕ) (hk : 1 ≤ n + 1) :
    Work.Whitney.skipIdx hk (Fin.last n) = Fin.castSucc := by
  funext i
  apply Fin.ext
  rw [skipIdx_val, Fin.val_castSucc, Fin.val_last]
  exact if_pos (by simpa using i.isLt)

/-- **`skipIdx` is compatible with `Fin.castSucc`**: skipping `j` at level `n+1` and restricting to
the first `n` indices is the same as skipping `j` at level `n`. -/
theorem skipIdx_castSucc_castSucc (n : ℕ) (hk : 1 ≤ n + 2) (hj : 1 ≤ n + 1)
    (j : Fin (n + 1)) (i : Fin n) :
    Work.Whitney.skipIdx hk (Fin.castSucc j) (Fin.castSucc i)
      = (Work.Whitney.skipIdx hj j i).castSucc := by
  apply Fin.ext
  rw [skipIdx_val]
  simp only [Fin.val_castSucc]
  rw [skipIdx_val]

/-- **Skipping `j` at level `n+1` and taking the last index gives the last index of `Fin (n+2)`.**
-/
theorem skipIdx_castSucc_last (n : ℕ) (hk : 1 ≤ n + 2) (j : Fin (n + 1)) :
    Work.Whitney.skipIdx hk (Fin.castSucc j) (Fin.last n) = Fin.last (n + 1) := by
  apply Fin.ext
  rw [skipIdx_val, Fin.val_last, Fin.val_castSucc, Fin.val_last]
  rw [if_neg]
  omega

/-! ## Algebraic preliminaries -/

/-- **The graded product is additive in a finite sum of its second arguments.** -/
theorem cupChern_sum_right' {α : Type} (a b : ℕ)
    (x : Work.Thom.Coh ℤ (2 * a) B) (s : Finset α) (f : α → Work.Thom.Coh ℤ (2 * b) B) :
    Work.Whitney.cupChern a b x (∑ i ∈ s, f i)
      = ∑ i ∈ s, Work.Whitney.cupChern a b x (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.sum_empty, Finset.sum_empty, Work.Whitney.cupChern_def,
        Work.Cohomology.cupH'_zero_right]
      exact map_zero (Work.Thom.cohTransportLM _)
  | insert i s his ih =>
      rw [Finset.sum_insert his, Finset.sum_insert his,
        Work.Whitney.ChernRel.cupChern_add_right, ih]

/-- From `a = a'` get `a + b = b + a'`. -/
theorem add_comm_eq {α : Type} [AddCommMonoid α] {a a' b : α} (h : a = a') :
    a + b = b + a' := (congrArg (· + b) h).trans (add_comm a' b)

/-! ## The elementary symmetric classes -/

/-- **The top elementary symmetric class is the product of the variables**: in degree `n` in `n+1`
variables the first term of the recursion of `eSymC` vanishes, so only the second survives. -/
theorem eSymC_top {P : Type} [TopologicalSpace P] (n : ℕ)
    (s : Fin (n + 1) → Work.Thom.Coh ℤ 2 P) :
    Work.Gen.eSymC (P := P) (n + 1) s (n + 1)
      = Work.Thom.cohTransport (by omega : 2 * (1 + n) = 2 * (n + 1))
          (Work.Whitney.cupChern 1 n (s (Fin.last n))
            (Work.Gen.eSymC (P := P) n (fun i => s (Fin.castSucc i)) n)) := by
  rw [Work.Gen.eSymC_succ, dif_pos (show 1 ≤ n + 1 by omega)]
  have hz : Work.Gen.eSymC (P := P) n (fun i => s (Fin.castSucc i)) (n + 1) = 0 :=
    Work.Gen.eSymC_above (fun i => s (Fin.castSucc i)) (by omega)
  rw [hz, zero_add]
  exact Work.LerayHirsch.cohTransport_congr_proof _ _

/-- **The recursion of `eSymC` at the top degree.** -/
theorem eSymC_succ_top {P : Type} [TopologicalSpace P] (n : ℕ)
    (t : Fin (n + 2) → Work.Thom.Coh ℤ 2 P) :
    Work.Gen.eSymC (P := P) (n + 2) t (n + 1)
      = Work.Gen.eSymC (P := P) (n + 1) (fun i => t (Fin.castSucc i)) (n + 1)
        + Work.Thom.cohTransport (by omega : 2 * (1 + n) = 2 * (n + 1))
            (Work.Whitney.cupChern 1 n (t (Fin.last (n + 1)))
              (Work.Gen.eSymC (P := P) (n + 1) (fun i => t (Fin.castSucc i)) n)) := by
  conv_lhs => rw [Work.Gen.eSymC_succ, dif_pos (show 1 ≤ n + 1 by omega)]
  congr 1

/-! ## The main combinatorial identity -/

/-- **The sum of the top elementary symmetric classes of the skipping subfamilies.**  For a family
`t : Fin (n+1) → H²(·;ℤ)`, the sum over `k` of the product of all the variables except the `k`-th
is the second-highest elementary symmetric class of the whole family. -/
theorem eSymC_sum_skipIdx_succ {P : Type} [TopologicalSpace P] (n : ℕ) :
    ∀ (t : Fin (n + 1) → Work.Thom.Coh ℤ 2 P) (h : 1 ≤ n + 1),
      (∑ k : Fin (n + 1), Work.Gen.eSymC (P := P) n (t ∘ Work.Whitney.skipIdx h k) n)
        = Work.Gen.eSymC (P := P) (n + 1) t n := by
  induction n with
  | zero =>
    intro t h
    rw [Fin.sum_univ_one]
    rw [Work.Gen.eSymC_succ, dif_neg (by norm_num : ¬ (1 ≤ 0)), add_zero]
    rw [Work.Gen.eSymC_zero, Work.Gen.eSymC_zero]
  | succ n ih =>
    intro t h
    have hj : 1 ≤ n + 1 := by omega
    rw [Fin.sum_univ_castSucc]
    have hlast : Work.Gen.eSymC (P := P) (n + 1)
          (t ∘ Work.Whitney.skipIdx h (Fin.last (n + 1))) (n + 1)
        = Work.Gen.eSymC (P := P) (n + 1) (fun i => t (Fin.castSucc i)) (n + 1) :=
      Work.Gen.eSymC_congr (fun i => by
        simp only [Function.comp_apply]
        rw [Work.Whitney.skipIdx_last (n + 1) h]) (n + 1)
    rw [hlast]
    have hterm : ∀ j : Fin (n + 1),
        Work.Gen.eSymC (P := P) (n + 1)
            (t ∘ Work.Whitney.skipIdx h (Fin.castSucc j)) (n + 1)
          = Work.Thom.cohTransportLM (by omega : 2 * (1 + n) = 2 * (n + 1))
              (Work.Whitney.cupChern 1 n (t (Fin.last (n + 1)))
                (Work.Gen.eSymC (P := P) n
                  ((fun i => t (Fin.castSucc i)) ∘ Work.Whitney.skipIdx hj j) n)) := by
      intro j
      have h1 : (t ∘ Work.Whitney.skipIdx h (Fin.castSucc j)) (Fin.last n)
          = t (Fin.last (n + 1)) := by
        simp only [Function.comp_apply]
        rw [Work.Whitney.skipIdx_castSucc_last n h j]
      have h2 : (fun i : Fin n =>
            (t ∘ Work.Whitney.skipIdx h (Fin.castSucc j)) (Fin.castSucc i))
          = ((fun i => t (Fin.castSucc i)) ∘ Work.Whitney.skipIdx hj j) := by
        funext i
        simp only [Function.comp_apply]
        rw [Work.Whitney.skipIdx_castSucc_castSucc n h hj j i]
      rw [eSymC_top (P := P) n (t ∘ Work.Whitney.skipIdx h (Fin.castSucc j)), h1, h2]
      exact Work.LerayHirsch.cohTransport_congr_proof _ _
    simp only [hterm]
    rw [← map_sum (Work.Thom.cohTransportLM (by omega : 2 * (1 + n) = 2 * (n + 1)))
      (fun j : Fin (n + 1) => Work.Whitney.cupChern 1 n (t (Fin.last (n + 1)))
        (Work.Gen.eSymC (P := P) n
          ((fun i => t (Fin.castSucc i)) ∘ Work.Whitney.skipIdx hj j) n)) Finset.univ]
    rw [← cupChern_sum_right' (a := 1) (b := n) (x := t (Fin.last (n + 1))) Finset.univ
      (fun j : Fin (n + 1) => Work.Gen.eSymC (P := P) n
        ((fun i => t (Fin.castSucc i)) ∘ Work.Whitney.skipIdx hj j) n)]
    rw [ih (fun i => t (Fin.castSucc i)) hj]
    rw [eSymC_succ_top (P := P) n t]
    exact add_comm_eq (Work.LerayHirsch.cohTransport_congr_proof _ _)

/-! ## The target -/

theorem eSym_sum_subsets {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι] {N : ℕ}
    (hN : 1 ≤ N)
    (M : Fin N → VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι) :
    (∑ k : Fin N, Work.Gen.eSym (N - 1) (M ∘ Work.Whitney.skipIdx hN k) (N - 1))
      = Work.Gen.eSym N M (N - 1) := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have h := eSymC_sum_skipIdx_succ (P := B) n
    (fun i => Work.Thom.chernClass 1 1 (M i)) hN
  simp only [Work.Gen.eSym_eq_eSymC]
  exact h

end

end Work.Whitney
