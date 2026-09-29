import Mathlib
import Submission.Work.TMC7Core.Cocycle
import Submission.Work.TMC7Core.Cocycle.frob_mul_le
import Submission.Work.TMC7Core.Cocycle.frob_sqrt_two_le_of_det_one
import Submission.Work.TMC7Core.Cocycle.log_frob_iterC_nonneg
import Submission.Work.TMC7Core.Lyap.subadditive_integral_log_frob

/-!
# `LEAlg` — the algebraic subadditivity of the transfer cocycle

Writing `n = (n / k) * k + n % k`, the cocycle identity gives

`A_n(x) = A_{n % k}(x + (n/k) k α) · (A_k(x + (m-1)kα) ⋯ A_k(x))`,

and submultiplicativity of the Frobenius norm turns this into the subadditive estimate

`log ‖A_n(x)‖ ≤ log ‖A_{n % k}(x + (n/k)kα)‖ + Σ_{j<n/k} log ‖A_k(x + jkα)‖`

used in the amortisation of `LEFurman`.
-/

noncomputable section

namespace Work.TMComp

open MeasureTheory

theorem iterC_block_prod (α lam : ℝ) (E : ℂ) (k : ℕ) (x : ℝ) (m : ℕ) :
    Work.TMC7Core.iterC α lam E (m * k) x
      = Work.TMC7Core.matProd (fun j => Work.TMC7Core.iterC α lam E k
          (x + (j : ℝ) * (k : ℝ) * α)) m := by
  induction m with
  | zero => rw [Nat.zero_mul, Work.TMC7Core.matProd_zero, Work.TMC7Core.iterC_zero]
  | succ m ih =>
    have h1 : (m + 1) * k = k + m * k := by ring
    rw [h1, Work.TMC7Core.iterC_add, ih, Work.TMC7Core.matProd_succ]
    congr 2
    have : x + ((m * k : ℕ) : ℝ) * α = x + (m : ℝ) * (k : ℝ) * α := by
      push_cast
      ring
    exact this

/-- The ordered product of determinant-one matrices has determinant one, hence Frobenius
norm at least `√2`. -/
theorem frob_matProd_pos_of_det_one (A : ℕ → Matrix (Fin 2) (Fin 2) ℂ)
    (hdet : ∀ j, (A j).det = 1) (m : ℕ) :
    0 < Work.TMC7Core.frob (Work.TMC7Core.matProd A m) :=
  lt_of_lt_of_le (Real.sqrt_pos.mpr (by norm_num))
    (Work.TMC7Core.Cocycle.frob_sqrt_two_le_of_det_one
      (Work.TMC7Core.det_matProd A hdet m))

/-- Positivity of the Frobenius norm of a product of two determinant-one matrices. -/
theorem frob_mul_pos_of_det_one (A B : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.det = 1)
    (hB : B.det = 1) : 0 < Work.TMC7Core.frob (A * B) :=
  lt_of_lt_of_le (Real.sqrt_pos.mpr (by norm_num))
    (Work.TMC7Core.Cocycle.frob_sqrt_two_le_of_det_one (by rw [Matrix.det_mul, hA, hB, one_mul]))

/-- `log` of the Frobenius norm of an ordered product is subadditive, for determinant-one
matrices. -/
theorem log_frob_matProd_le_of_det_one (A : ℕ → Matrix (Fin 2) (Fin 2) ℂ)
    (hdet : ∀ j, (A j).det = 1) :
    ∀ m : ℕ, 1 ≤ m →
      Real.log (Work.TMC7Core.frob (Work.TMC7Core.matProd A m))
        ≤ ∑ j ∈ Finset.range m, Real.log (Work.TMC7Core.frob (A j)) := by
  intro m
  induction m with
  | zero => intro hm; omega
  | succ m ih =>
    intro hm
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · subst hm0
      rw [Work.TMC7Core.matProd_succ, Work.TMC7Core.matProd_zero, mul_one,
        Finset.sum_range_one]
    · have h1 : Work.TMC7Core.matProd A (m + 1) = A m * Work.TMC7Core.matProd A m :=
        Work.TMC7Core.matProd_succ A m
      rw [h1]
      have hp1 : 0 < Work.TMC7Core.frob (A m) :=
        lt_of_lt_of_le (Real.sqrt_pos.mpr (by norm_num))
          (Work.TMC7Core.Cocycle.frob_sqrt_two_le_of_det_one (hdet m))
      have hp2 : 0 < Work.TMC7Core.frob (Work.TMC7Core.matProd A m) :=
        frob_matProd_pos_of_det_one A hdet m
      have hp3 : 0 < Work.TMC7Core.frob (A m * Work.TMC7Core.matProd A m) :=
        frob_mul_pos_of_det_one _ _ (hdet m)
          (Work.TMC7Core.det_matProd A hdet m)
      have hmul := Work.TMC7Core.Cocycle.frob_mul_le (A m) (Work.TMC7Core.matProd A m)
      have step1 : Real.log (Work.TMC7Core.frob (A m * Work.TMC7Core.matProd A m))
          ≤ Real.log (Work.TMC7Core.frob (A m))
            + Real.log (Work.TMC7Core.frob (Work.TMC7Core.matProd A m)) := by
        have h := Real.log_le_log hp3 hmul
        rwa [Real.log_mul (ne_of_gt hp1) (ne_of_gt hp2)] at h
      have step2 := ih hmpos
      rw [Finset.sum_range_succ]
      linarith [step1, step2]

theorem log_frob_matProd_iterC_le (α lam : ℝ) (E : ℂ) (k : ℕ) (x : ℝ) (m : ℕ) (hm : 1 ≤ m) :
    Real.log (Work.TMC7Core.frob (Work.TMC7Core.matProd
        (fun j => Work.TMC7Core.iterC α lam E k (x + (j : ℝ) * (k : ℝ) * α)) m))
      ≤ ∑ j ∈ Finset.range m,
          Real.log (Work.TMC7Core.frob (Work.TMC7Core.iterC α lam E k
            (x + (j : ℝ) * (k : ℝ) * α))) :=
  log_frob_matProd_le_of_det_one _
    (fun j => Work.TMC7Core.det_iterC α lam E k _) m hm

theorem iterC_subadditive_decomp' (α lam : ℝ) (E : ℂ) (k n : ℕ) (x : ℝ) (hk : 1 ≤ k) :
    Real.log (Work.TMC7Core.frob (Work.TMC7Core.iterC α lam E n x)) ≤
      Real.log (Work.TMC7Core.frob (Work.TMC7Core.iterC α lam E (n % k)
        (x + ((n / k : ℕ) : ℝ) * (k : ℝ) * α))) +
      ∑ j ∈ Finset.range (n / k),
        Real.log (Work.TMC7Core.frob (Work.TMC7Core.iterC α lam E k
          (x + (j : ℝ) * (k : ℝ) * α))) := by
  have hkpos : 0 < k := hk
  by_cases hm : n / k = 0
  · have hlt : n < k := by
      by_contra h
      have h2 : k ≤ n := not_lt.mp h
      have h3 : 1 ≤ n / k := by
        rw [Nat.le_div_iff_mul_le hkpos]
        simpa using h2
      omega
    have hmod : n % k = n := Nat.mod_eq_of_lt hlt
    rw [hm, hmod]
    simp
  · have hmpos : 0 < n / k := Nat.pos_of_ne_zero hm
    have hn : n % k + (n / k) * k = n := by
      rw [Nat.mul_comm (n / k) k, Nat.mod_add_div]
    have hsplit : Work.TMC7Core.iterC α lam E n x
        = Work.TMC7Core.iterC α lam E (n % k) (x + (((n / k) * k : ℕ) : ℝ) * α)
          * Work.TMC7Core.iterC α lam E ((n / k) * k) x := by
      conv_lhs => rw [← hn]
      rw [Work.TMC7Core.iterC_add]
    have hlog : Real.log (Work.TMC7Core.frob (Work.TMC7Core.iterC α lam E n x)) ≤
        Real.log (Work.TMC7Core.frob (Work.TMC7Core.iterC α lam E (n % k)
          (x + (((n / k) * k : ℕ) : ℝ) * α)))
        + Real.log (Work.TMC7Core.frob (Work.TMC7Core.iterC α lam E ((n / k) * k) x)) := by
      rw [hsplit]
      have h1 := Work.TMC7Core.Cocycle.frob_mul_le
        (Work.TMC7Core.iterC α lam E (n % k) (x + (((n / k) * k : ℕ) : ℝ) * α))
        (Work.TMC7Core.iterC α lam E ((n / k) * k) x)
      have hp4 := frob_mul_pos_of_det_one
        (Work.TMC7Core.iterC α lam E (n % k) (x + (((n / k) * k : ℕ) : ℝ) * α))
        (Work.TMC7Core.iterC α lam E ((n / k) * k) x)
        (Work.TMC7Core.det_iterC α lam E (n % k) _)
        (Work.TMC7Core.det_iterC α lam E ((n / k) * k) x)
      have h2 := Work.TMC7Core.Lyap.frob_iterC_pos α lam E (n % k)
        (x + (((n / k) * k : ℕ) : ℝ) * α)
      have h3 := Work.TMC7Core.Lyap.frob_iterC_pos α lam E ((n / k) * k) x
      have h := Real.log_le_log hp4 h1
      rwa [Real.log_mul (ne_of_gt h2) (ne_of_gt h3)] at h
    have hblock : Real.log (Work.TMC7Core.frob
          (Work.TMC7Core.iterC α lam E ((n / k) * k) x)) ≤
        ∑ j ∈ Finset.range (n / k), Real.log (Work.TMC7Core.frob
          (Work.TMC7Core.iterC α lam E k (x + (j : ℝ) * (k : ℝ) * α))) := by
      rw [iterC_block_prod α lam E k x (n / k)]
      exact log_frob_matProd_iterC_le α lam E k x (n / k) hmpos
    have harg : x + (((n / k) * k : ℕ) : ℝ) * α = x + ((n / k : ℕ) : ℝ) * (k : ℝ) * α := by
      push_cast
      ring
    rw [harg] at hlog
    linarith [hlog, hblock]

end Work.TMComp
