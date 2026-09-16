import Mathlib
import Submission.SlabBridge

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option linter.unusedVariables false

open scoped BigOperators
open Finset

namespace Commons.NumberTheory.MaynardSieve

/-- A multiplicity vector: the `i`-th entry counts the occurrences of the part `2(i+1)`. -/
abbrev MV := Fin 12 → ℕ

/-!
# The degree-graded index of the certificate's x-side polynomial

(see the roadmap, SESSION 45).  For each even-part signature `β` of weighted degree `≤ 24` the
certificate computation evaluates the x-side polynomial

  `A^(50-|β|) · ∏_w h_w^(σ_w)`,   `A = 1 + Σ_v v! x_v`,   `h_w = w! + Σ_v (v+w)! x_v`

and reads its coefficients at the 272 signatures of weighted degree `≤ 24`.  The polynomial is
stored as a packed `Nat`: the coefficient of `x^m` at block `pos m` of `B` bits.  Here we build
`pos`: states are grouped by weighted degree `deg m = Σ_i 2(i+1)m_i` (classes of sizes
`1,1,2,3,5,7,11,15,22,30,42,56,77`), `muVal m = Σ_i mu_i m_i` is a linear functional injective
inside every class, and `pos m = classOff (deg m / 2) + muVal m` lays the classes out
consecutively.

The point (`pos_shift`): multiplying by a monomial `x_v` translates the packed word by a constant
depending only on the source class and `v` — so a multiplication is a handful of block-aligned
shifts and adds, with no masks and no separate truncation (a class beyond degree 24 simply does
not exist).
-/

/-- All even-part signatures of weighted degree `≤ rem` using parts `2,4,…,2k`. -/
def sigAux : ℕ → ℕ → List (List ℕ)
  | 0, _ => [[]]
  | (k + 1), rem =>
      (List.range (rem / (2 * (k + 1)) + 1)).flatMap (fun m =>
        (sigAux k (rem - 2 * (k + 1) * m)).map
          (fun t => List.replicate m (2 * (k + 1)) ++ t))

/-- The 272 even-part signatures of weighted degree `≤ 24`. -/
def certSigs : List (List ℕ) := sigAux 12 24

/-- The unit multiplicity vector `e_v` (one occurrence of the part `2(v+1)`). -/
def evec (v : Fin 12) : Fin 12 → ℕ := Pi.single v 1

/-- The multiplicity vector of a signature. -/
def mvec (σ : List ℕ) : Fin 12 → ℕ := fun i => σ.count (2 * ((i : ℕ) + 1))

/-- Weighted degree of a multiplicity vector. -/
def degV (m : Fin 12 → ℕ) : ℕ := ∑ i : Fin 12, 2 * ((i : ℕ) + 1) * m i

/-- The linear functional used for the within-class index. -/
def mu : Fin 12 → ℕ := ![17, 32, 31, 18, 16, 25, 16, 8, 10, 28, 22, 33]

/-- Value of the linear functional. -/
def muVal (m : Fin 12 → ℕ) : ℕ := ∑ i : Fin 12, mu i * m i

/-- The 272 states, as multiplicity vectors. -/
def certStates : List (Fin 12 → ℕ) := certSigs.map mvec

/-- The states of half-class `j` (weighted degree `2 j`). -/
def classJ (j : ℕ) : List (Fin 12 → ℕ) := certStates.filter (fun m => degV m = 2 * j)

/-- Offset of class `j` in the packed word: the total width of the earlier classes. -/
def classOff (j : ℕ) : ℕ :=
  ∑ j' ∈ Finset.range 13, if j' < j then ((classJ j').map muVal).max?.getD 0 + 1 else 0

/-- The packed index of a state. -/
def pos (m : Fin 12 → ℕ) : ℕ := classOff (degV m / 2) + muVal m

/-- The width of class `j` (used to bound the packed word). -/
def classWin (j : ℕ) : ℕ :=
  ((classJ j).map muVal).max?.getD 0 - ((classJ j).map muVal).min?.getD 0 + 1

/-! ## The verified facts about the index -/

theorem certSigs_length : certSigs.length = 272 := by decide

theorem certStates_length : certStates.length = 272 := by decide

/-- `mu` is injective inside every class (`Nodup` of the values). -/
theorem mu_inj_class (j : ℕ) (hj : j < 13) : ((classJ j).map muVal).Nodup := by
  interval_cases j <;> decide

/-- The packed index is injective on the 272 states. -/
theorem pos_inj : (certStates.map pos).Nodup := by decide

/-- The class width table (the packed word has `Σ classWin + 1` blocks). -/
theorem classWin_table :
    (List.range 13).map classWin = [1, 1, 3, 21, 51, 70, 78, 104, 129, 144, 144, 166, 179] := by
  decide

/-! ## The two elementary linearity lemmas -/

theorem degV_add_single (m : Fin 12 → ℕ) (v : Fin 12) :
    degV (m + evec v) = degV m + 2 * ((v : ℕ) + 1) := by
  have hB : (∑ i : Fin 12, 2 * ((i : ℕ) + 1) * (evec v) i)
      = 2 * ((v : ℕ) + 1) := by
    rw [Finset.sum_eq_single v]
    · simp only [evec, Pi.single_eq_same, mul_one]
    · intro b _ hb
      rw [show evec v b = 0 from Pi.single_eq_of_ne hb 1, mul_zero]
    · intro hv
      exact absurd (Finset.mem_univ v) hv
  have hcongr : (∑ i : Fin 12, 2 * ((i : ℕ) + 1) * (m + evec v) i)
      = ∑ i : Fin 12, (2 * ((i : ℕ) + 1) * m i
          + 2 * ((i : ℕ) + 1) * (evec v) i) :=
    Finset.sum_congr rfl (fun i _ => by rw [Pi.add_apply, mul_add])
  unfold degV
  rw [hcongr, Finset.sum_add_distrib, hB]

theorem muVal_add_single (m : Fin 12 → ℕ) (v : Fin 12) :
    muVal (m + evec v) = muVal m + mu v := by
  have hB : (∑ i : Fin 12, mu i * (evec v) i) = mu v := by
    rw [Finset.sum_eq_single v]
    · simp only [evec, Pi.single_eq_same, mul_one]
    · intro b _ hb
      rw [show evec v b = 0 from Pi.single_eq_of_ne hb 1, mul_zero]
    · intro hv
      exact absurd (Finset.mem_univ v) hv
  have hcongr : (∑ i : Fin 12, mu i * (m + evec v) i)
      = ∑ i : Fin 12, (mu i * m i + mu i * (evec v) i) :=
    Finset.sum_congr rfl (fun i _ => by rw [Pi.add_apply, mul_add])
  unfold muVal
  rw [hcongr, Finset.sum_add_distrib, hB]

/-- **The shift structure.**  For a state `m` of class `j`, multiplying by the monomial `x_{2(v+1)}`
moves the packed index into class `j + v + 1`, and
`pos (m + e_v) = classOff (j+v+1) + (muVal m + mu v)`; since `pos m = classOff j + muVal m`, the
increment is the constant `classOff (j+v+1) - classOff j + mu v`, independent of `m`. -/
theorem pos_shift (j : ℕ) (v : Fin 12) (m : Fin 12 → ℕ)
    (hm : m ∈ classJ j) (hlt : j + (v : ℕ) + 1 < 13) :
    pos (m + evec v) = classOff (j + (v : ℕ) + 1) + (muVal m + mu v) := by
  have hdeg : degV m = 2 * j := of_decide_eq_true (List.mem_filter.mp hm).2
  have h1 : degV (m + evec v) = 2 * (j + (v : ℕ) + 1) := by
    rw [degV_add_single, hdeg]; omega
  have h2 : (2 * (j + (v : ℕ) + 1)) / 2 = j + (v : ℕ) + 1 := by omega
  unfold pos
  rw [h1, h2, muVal_add_single]

/-- The same statement in the "constant increment" form used by the DP. -/
theorem pos_shift_const (j : ℕ) (v : Fin 12) (m : Fin 12 → ℕ)
    (hm : m ∈ classJ j) (hlt : j + (v : ℕ) + 1 < 13) :
    pos (m + evec v) =
      pos m + (classOff (j + (v : ℕ) + 1) - classOff j + mu v) := by
  have hdeg : degV m = 2 * j := of_decide_eq_true (List.mem_filter.mp hm).2
  have hpos : pos m = classOff j + muVal m := by
    unfold pos
    rw [hdeg, show 2 * j / 2 = j from by omega]
  have h1 := pos_shift j v m hm hlt
  have hmono : classOff j ≤ classOff (j + (v : ℕ) + 1) := by
    unfold classOff
    apply Finset.sum_le_sum
    intro j' hj'
    by_cases h : j' < j
    · rw [if_pos h, if_pos (by omega)]
    · rw [if_neg h]
      exact Nat.zero_le _
  rw [hpos, h1]; omega

end Commons.NumberTheory.MaynardSieve
