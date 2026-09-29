import Mathlib
import Submission.Work.TMC14Core.Assembly

/-!
# TMC14Core: auxiliaries for `discZeroEven`

The value of the discriminant `disc p q lam` at `0` is the constant Fourier mode of
`θ ↦ trAq(0,θ)`, and by Chambers' formula (`Chambers.chambers`) it equals
`trAq p q lam 0 0 + 2λ^q` for even `q` and `p` coprime to `q`.

(`trAq p q lam 0 0` is the trace of the `q`-step transfer matrix of the rational
(`θ = 0`) cocycle, i.e. the trace of the product of the `q` transfer matrices
`!![-2λ cos (2π j p/q), -1; 1, 0]`.)
-/

open LeanEval.Analysis.TenMartini
open Polynomial

noncomputable section

namespace Work.TMC14Core

/-- The oscillatory coefficient of Chambers' formula is `-2λ^q` for even `q` and odd `p`. -/
theorem chamCoef_even (p : ℤ) (q : ℕ) (lam : ℝ) (hq2 : Even q) (hp : Odd p) :
    chamCoef p q lam = ((-2 * lam ^ q : ℝ) : ℂ) := by
  have h1 : (-(lam : ℂ)) ^ q = (lam : ℂ) ^ q := by
    rw [neg_pow, hq2.neg_one_pow, one_mul]
  have hq1 : Odd ((q : ℤ) - 1) := by
    obtain ⟨k, hk⟩ := hq2
    exact ⟨(k : ℤ) - 1, by omega⟩
  have h2 : ((-1 : ℂ) ^ (p * ((q : ℤ) - 1))) = -1 := by
    apply Odd.neg_one_zpow
    exact hp.mul hq1
  rw [chamCoef, h1, h2]
  push_cast
  ring

/-- `p` coprime to an even `q` is odd. -/
theorem odd_of_coprime_even {p : ℤ} {q : ℕ} (hpq : Nat.Coprime p.natAbs q) (hq2 : Even q) :
    Odd p := by
  obtain ⟨k, hk⟩ := hq2
  have h2q : 2 ∣ q := ⟨k, by omega⟩
  have h2 : ¬ 2 ∣ p.natAbs := by
    intro h
    have h3 : 2 ∣ p.natAbs.gcd q := Nat.dvd_gcd h h2q
    rw [hpq.gcd_eq_one] at h3
    omega
  have hp2 : Odd p.natAbs := by
    rw [← Nat.not_even_iff_odd]
    intro he
    exact h2 (even_iff_two_dvd.mp he)
  obtain ⟨k', hk'⟩ := hp2
  by_cases h : 0 ≤ p
  · refine ⟨(k' : ℤ), ?_⟩
    have h1 : (p.natAbs : ℤ) = p := Int.natAbs_of_nonneg h
    omega
  · refine ⟨-((k' : ℤ)) - 1, ?_⟩
    have h1 : (p.natAbs : ℤ) = -p := by
      have h2 : ((-p).natAbs : ℤ) = -p := Int.natAbs_of_nonneg (by omega)
      rwa [Int.natAbs_neg] at h2
    omega

/-- **Reduction.**  For even `q` and `p` coprime to `q`, the discriminant at `0` equals the
trace of the `q`-step transfer matrix of the rational cocycle, plus `2λ^q`. -/
theorem disc_eval_zero_reduction (p : ℤ) (q m : ℕ) (hm : q = 2 * m + 2)
    (hpq : Nat.Coprime p.natAbs q) (lam : ℝ) :
    (disc p q lam).eval 0 = trAq p q lam 0 0 + ((2 * lam ^ q : ℝ) : ℂ) := by
  have hq : 1 ≤ q := by omega
  have hq2 : Even q := ⟨m + 1, by omega⟩
  have hp : Odd p := odd_of_coprime_even hpq hq2
  have hch := chambers p q lam 0 hpq hq 0
  rw [chamCoef_even p q lam hq2 hp] at hch
  have hcos : (Real.cos (2 * Real.pi * (q : ℝ) * 0) : ℂ) = 1 := by simp
  rw [hcos, mul_one] at hch
  have h2 : ((2 * lam ^ q : ℝ) : ℂ) = -((-2 * lam ^ q : ℝ) : ℂ) := by push_cast; ring
  rw [h2, hch]
  ring

/-- The `90°`-rotation `!![0,-1;1,0]`. -/
def Rmat : Matrix (Fin 2) (Fin 2) ℂ := !![0, -1; 1, 0]

/-- The projection `!![1,0;0,0]`. -/
def Emat : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 0]

/-- `matProd q M = M 0 * M 1 * ⋯ * M (q-1)`, the product in increasing order of the index. -/
def matProd (q : ℕ) (M : ℕ → Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (List.range q).foldl (fun acc j => acc * M j) 1

/-- Strictly increasing `k`-tuples in `{0,…,q-1}` all of whose cyclic gaps are odd.
For `k = 0` the set is empty; for `k = 1` it is empty when `q` is even. -/
noncomputable def gapOddTuples (q k : ℕ) : Finset (Fin k → ℕ) := by
  classical
  exact (Fintype.piFinset fun _ : Fin k => Finset.range q).filter fun i =>
    0 < k ∧
      (∀ (j : ℕ) (hj : j + 1 < k), i ⟨j, by omega⟩ < i ⟨j + 1, by omega⟩) ∧
      (∀ (j : ℕ) (hj : j + 1 < k), Odd (i ⟨j + 1, by omega⟩ - i ⟨j, by omega⟩)) ∧
      (∀ (h : 0 < k), Odd (q + i ⟨0, h⟩ - i ⟨k - 1, by omega⟩))

/-- `tmC lam 0 x` written with the `R,E` letters: the potential is `-w - w⁻¹` with
`w = ee x = e^{2πix}`. -/
theorem tmC_zero_eq_R_E (lam : ℝ) (x : ℝ) :
    tmC lam 0 x = Rmat + (((lam : ℂ) * (-(ee x + (ee x)⁻¹))) • Emat) := by
  have h00 : ((2 * lam * Real.cos (2 * Real.pi * x) : ℝ) : ℂ)
      = (lam : ℂ) * (ee x + (ee x)⁻¹) := by
    rw [← two_cos_eq x]; push_cast; ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tmC, Rmat, Emat, Matrix.add_apply, Matrix.smul_apply, h00] <;>
    ring


/-! ## Assembly helpers -/

theorem matProd_succ (n : ℕ) (M : ℕ → Matrix (Fin 2) (Fin 2) ℂ) :
    matProd (n + 1) M = matProd n M * M n := by
  have hrange : List.range (n + 1) = List.range n ++ [n] := List.range_succ
  simp only [matProd, hrange, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem matProd_shift (n : ℕ) (M : ℕ → Matrix (Fin 2) (Fin 2) ℂ) :
    matProd (n + 1) M = M 0 * matProd n (fun j => M (j + 1)) := by
  induction n with
  | zero => simp [matProd]
  | succ k ih => rw [matProd_succ, ih, matProd_succ, mul_assoc]

/-- `iterC` at `E = 0` is the product of the transfer matrices in increasing order of the
reversed index. -/
theorem iterC_zero_eq_matProd (α lam : ℝ) (n : ℕ) :
    iterC α lam 0 n 0 = matProd n (fun j => tmC lam 0 (((n - 1 - j : ℕ) : ℝ) * α)) := by
  induction n with
  | zero => simp [iterC, matProd]
  | succ k ih =>
    have hcast : ∀ j : ℕ, (((k + 1 - 1 - j : ℕ)) : ℝ) = ((k - j : ℕ) : ℝ) := by
      intro j; congr 1; try omega
    have hkey : ∀ j : ℕ, ((k - (j + 1) : ℕ) : ℝ) = ((k - 1 - j : ℕ) : ℝ) := by
      intro j; congr 1; try omega
    rw [iterC_succ, ih, matProd_shift, show (0 : ℝ) + (k : ℝ) * α = (k : ℝ) * α from by ring,
      hcast 0]
    congr 1
    congr 1
    funext j
    rw [hcast (j + 1), hkey j]

end Work.TMC14Core
