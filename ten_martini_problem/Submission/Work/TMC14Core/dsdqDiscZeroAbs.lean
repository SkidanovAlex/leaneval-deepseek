import Mathlib
import Submission.Work.TMC14Core.Assembly
import Submission.Work.TMC14Core.zero_aux
import Submission.Work.TMC14Core.dzAux

/-!
# `disc p q lam` at energy `0` for even `q`

For `q = 2N` even and `p` coprime to `q` (hence odd) we prove

  `‖(disc p q lam).eval 0‖ = 2 + 2 * lam ^ q`.

The proof evaluates the discriminant at `0` through Chambers' formula

  `trAq p q lam z θ = (disc p q lam).eval z + chamCoef p q lam * cos (2π q θ)`

at the phase `θ = 1/4`, where the `q`-step monodromy at energy `0` has trace `2(-1)^N`.

The two ingredients for the trace computation are:

* `sin (2π (N + k) p / q) = - sin (2π k p / q)`  (anti-periodicity), which makes the transfer
  matrix of step `k + N` equal to `-sz * (step k) * sz`, so that the monodromy over the full
  period is `(-1)^N (A sz)^2` with `A` the monodromy of the first half;
* `sin (2π (N - k) p / q) = sin (2π k p / q)` (palindromy of the first half), which makes the
  half product `A` invariant under `M ↦ sz * Mᵀ * sz`, whence `A * sz` is traceless.

This is the "two central bands touch at `0`" computation.
-/

open Matrix
open LeanEval.Analysis.TenMartini

noncomputable section

namespace Work.TMC14Core

/-! ## 1. Trigonometry at the phase `1/4` -/

/-- Palindrome: for `q = 2N`, `p` odd, `sin (2π (N-k) p / q) = sin (2π k p / q)`. -/
theorem sin_two_pi_pal_aux (N : ℕ) (hN : 1 ≤ N) (p : ℤ) (hp : Odd p) (k : ℕ) (hk : k ≤ N) :
    Real.sin (2 * Real.pi * ((N - k : ℕ) : ℝ) * (p : ℝ) / ((2 * N : ℕ) : ℝ))
      = Real.sin (2 * Real.pi * (k : ℝ) * (p : ℝ) / ((2 * N : ℕ) : ℝ)) := by
  have h2N : ((2 * N : ℕ) : ℝ) = 2 * (N : ℝ) := by push_cast; ring
  have hNk : ((N - k : ℕ) : ℝ) = (N : ℝ) - (k : ℝ) := by rw [Nat.cast_sub hk]
  have hkey : 2 * Real.pi * ((N - k : ℕ) : ℝ) * (p : ℝ) / ((2 * N : ℕ) : ℝ)
      = (p : ℝ) * Real.pi - 2 * Real.pi * (k : ℝ) * (p : ℝ) / ((2 * N : ℕ) : ℝ) := by
    rw [h2N, hNk]
    field_simp
  rw [hkey, Real.sin_sub, Real.sin_int_mul_pi, Real.cos_int_mul_pi, Odd.neg_one_zpow hp]
  ring

/-- Anti-periodicity: for `q = 2N`, `p` odd, `sin (2π (N+k) p / q) = - sin (2π k p / q)`. -/
theorem sin_two_pi_anti_aux (N : ℕ) (hN : 1 ≤ N) (p : ℤ) (hp : Odd p) (k : ℕ) :
    Real.sin (2 * Real.pi * ((N + k : ℕ) : ℝ) * (p : ℝ) / ((2 * N : ℕ) : ℝ))
      = -Real.sin (2 * Real.pi * (k : ℝ) * (p : ℝ) / ((2 * N : ℕ) : ℝ)) := by
  have h2N : ((2 * N : ℕ) : ℝ) = 2 * (N : ℝ) := by push_cast; ring
  have hkey : 2 * Real.pi * ((N + k : ℕ) : ℝ) * (p : ℝ) / ((2 * N : ℕ) : ℝ)
      = (p : ℝ) * Real.pi + 2 * Real.pi * (k : ℝ) * (p : ℝ) / ((2 * N : ℕ) : ℝ) := by
    rw [h2N]
    push_cast
    field_simp
  rw [hkey, Real.sin_add, Real.sin_int_mul_pi, Real.cos_int_mul_pi, Odd.neg_one_zpow hp]
  ring

/-! ## 2. Products of `2 × 2` matrices -/

/-- `mprod` only depends on the first `n` terms. -/
theorem mprod_congr_aux (f g : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (n : ℕ)
    (h : ∀ j, j < n → f j = g j) : mprod f n = mprod g n := by
  induction n with
  | zero => rfl
  | succ k ih => rw [mprod_succ, mprod_succ, ih (fun j hj => h j (by omega)), h k (by omega)]

/-- Shifting a product. -/
theorem mprod_shift_aux (h : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (n : ℕ) :
    mprod h (n + 1) = h 0 * mprod (fun j => h (j + 1)) n := by
  induction n with
  | zero => rw [mprod_succ h 0, mprod_zero h, Matrix.one_mul, mprod_zero, Matrix.mul_one]
  | succ k ih => rw [mprod_succ, ih, mprod_succ, Matrix.mul_assoc]

/-- Transposing a product reverses the order of the factors. -/
theorem mprod_transpose_aux (g : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (n : ℕ) :
    (mprod g n).transpose = mprod (fun j => (g (n - 1 - j)).transpose) n := by
  induction n with
  | zero => simp [mprod]
  | succ k ih =>
    have hL : (mprod g (k + 1)).transpose
        = (g k).transpose * mprod (fun j => (g (k - 1 - j)).transpose) k := by
      rw [mprod_succ, Matrix.transpose_mul, ih]
    have hR : mprod (fun j => (g (k + 1 - 1 - j)).transpose) (k + 1)
        = (g k).transpose * mprod (fun j => (g (k - 1 - j)).transpose) k := by
      have harg : (fun j => (g (k + 1 - 1 - j)).transpose)
          = (fun j => (g (k - j)).transpose) := by
        funext j
        rw [show k + 1 - 1 - j = k - j by omega]
      rw [harg, mprod_shift_aux]
      congr 1
      apply mprod_congr_aux
      intro j hj
      rw [show k - (j + 1) = k - 1 - j by omega]
    rw [hL, hR]

/-- A palindromic sequence of `sz`-symmetric transfer matrices has an `sz`-symmetric product. -/
theorem mprod_pal_transpose_aux (f : ℕ → Matrix (Fin 2) (Fin 2) ℂ)
    (hT : ∀ j, (f j).transpose = sz * f j * sz) (n : ℕ)
    (hpal : ∀ j, j < n → f j = f (n - 1 - j)) :
    (mprod f n).transpose = sz * mprod f n * sz := by
  calc (mprod f n).transpose
      = (mprod (fun j => f (n - 1 - j)) n).transpose := by
        rw [mprod_congr_aux _ _ n (fun j hj => (hpal j hj).symm)]
    _ = mprod (fun j => (f j).transpose) n := by
        rw [mprod_transpose_aux]
        apply mprod_congr_aux
        intro j hj
        exact congrArg (fun m : ℕ => (f m).transpose) (by omega)
    _ = mprod (fun j => sz * f j * sz) n := by
        apply mprod_congr_aux
        intro j _
        rw [hT]
    _ = sz * mprod f n * sz := mprod_conj sz sz_mul_sz f n

/-! ## 3. Two small matrix facts -/

/-- `S2 x = !![x,-1;1,0]` is `sz`-symmetric. -/
theorem transpose_S2_aux (x : ℂ) : (S2 x).transpose = sz * S2 x * sz := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [S2, sz, Matrix.mul_apply, Fin.sum_univ_two]

/-- `S2 (-x) = -(sz * S2 x * sz)`. -/
theorem S2_neg_aux (x : ℂ) : S2 (-x) = -(sz * S2 x * sz) := by
  rw [sz_mul_S2]; simp

/-- The energy-zero transfer matrix `tmC lam 0 x`. -/
theorem tmC_zero_eq_aux (lam x : ℝ) :
    tmC lam 0 x = S2 (-(((2 * lam * Real.cos (2 * Real.pi * x) : ℝ)) : ℂ)) := by
  rw [S2, tmC]; congr 1; ring_nf

/-- `tmC lam z x` is `sz`-symmetric. -/
theorem tmC_transpose_aux (lam : ℝ) (z : ℂ) (x : ℝ) :
    (tmC lam z x).transpose = sz * tmC lam z x * sz := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tmC, sz, Matrix.mul_apply, Fin.sum_univ_two]

/-- A matrix whose `(0,1)` entry is minus its `(1,0)` entry has `sz`-traceless product. -/
theorem trace_mul_diag_aux (B : Matrix (Fin 2) (Fin 2) ℂ) (h : B 0 1 = -B 1 0) :
    (B * !![(0:ℂ), -1; -1, 0]).trace = 0 := by
  obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d : ℂ, B = !![a, b; c, d] :=
    ⟨B 0 0, B 0 1, B 1 0, B 1 1, by ext i j; fin_cases i <;> fin_cases j <;> rfl⟩
  simp [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two] at h ⊢
  rw [h]; ring

/-- The transpose identity for a palindromic product read on the off-diagonal. -/
theorem pal_entry_aux (B : Matrix (Fin 2) (Fin 2) ℂ) (hB : B.transpose = sz * B * sz) :
    B 0 1 = -B 1 0 := by
  obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d : ℂ, B = !![a, b; c, d] :=
    ⟨B 0 0, B 0 1, B 1 0, B 1 1, by ext i j; fin_cases i <;> fin_cases j <;> rfl⟩
  have h := congrFun (congrFun hB 0) 1
  simp [sz, Matrix.mul_apply, Fin.sum_univ_two] at h ⊢
  rw [h]; ring

/-! ## 4. The sequence of weights and the bridge from `iterC` to `mprod` -/

/-- The weight `-2λ cos (2π (1/4 + j p/q))` is `2λ sin (2π j p/q)`. -/
def dseq (p : ℤ) (q : ℕ) (lam : ℝ) (j : ℕ) : ℂ :=
  ((2 * lam * Real.sin (2 * Real.pi * (j : ℝ) * ((p : ℝ) / (q : ℝ))) : ℝ) : ℂ)

theorem dseq_zero (p : ℤ) (q : ℕ) (lam : ℝ) : dseq p q lam 0 = 0 := by simp [dseq]

theorem tmC_quarter_eq_S2_aux (p : ℤ) (q : ℕ) (lam : ℝ) (j : ℕ) :
    tmC lam 0 (1 / 4 + (j : ℝ) * ((p : ℝ) / (q : ℝ))) = S2 (dseq p q lam j) := by
  rw [tmC_zero_eq_aux, dseq]
  congr 1
  rw [← Complex.ofReal_neg, Complex.ofReal_inj]
  have hc : 2 * Real.pi * (1 / 4 + (j : ℝ) * ((p : ℝ) / (q : ℝ)))
      = 2 * Real.pi * (j : ℝ) * ((p : ℝ) / (q : ℝ)) + Real.pi / 2 := by ring
  rw [hc, Real.cos_add_pi_div_two]
  ring_nf

/-- `iterC` is the product in decreasing order of the phases. -/
theorem iterC_eq_mprod_rev_aux (α lam : ℝ) (z : ℂ) (n : ℕ) (x : ℝ) :
    iterC α lam z n x = mprod (fun k => tmC lam z (x + ((n - 1 - k : ℕ) : ℝ) * α)) n := by
  induction n with
  | zero => rw [iterC, mprod_zero]
  | succ k ih =>
    rw [iterC_succ, ih]
    have h1 : mprod (fun j => tmC lam z (x + ((k + 1 - 1 - j : ℕ) : ℝ) * α)) (k + 1)
        = mprod (fun j => tmC lam z (x + ((k - j : ℕ) : ℝ) * α)) (k + 1) := by
      apply mprod_congr_aux
      intro j _
      exact congrArg (fun m : ℕ => tmC lam z (x + (m : ℝ) * α)) (by rw [Nat.add_sub_cancel])
    rw [h1, mprod_shift_aux]
    simp only [Nat.sub_zero]
    rw [show mprod (fun j => tmC lam z (x + ((k - (j + 1) : ℕ) : ℝ) * α)) k
        = mprod (fun j => tmC lam z (x + ((k - 1 - j : ℕ) : ℝ) * α)) k from by
      apply mprod_congr_aux
      intro j hj
      exact congrArg (fun m : ℕ => tmC lam z (x + (m : ℝ) * α)) (by omega)]

/-- `iterC` and the increasing `mprod` have the same trace (reversal + transposition by `sz`). -/
theorem trace_iterC_eq_trace_mprod_aux (α lam : ℝ) (z : ℂ) (n : ℕ) (x : ℝ) :
    (iterC α lam z n x).trace
      = (mprod (fun k => tmC lam z (x + (k : ℝ) * α)) n).trace := by
  let g : ℕ → Matrix (Fin 2) (Fin 2) ℂ := fun k => tmC lam z (x + (k : ℝ) * α)
  have hrev : iterC α lam z n x = mprod (fun k => g (n - 1 - k)) n := by
    rw [iterC_eq_mprod_rev_aux]
  have hT : ∀ k : ℕ, (g k).transpose = sz * g k * sz := by
    intro k
    exact tmC_transpose_aux lam z (x + (k : ℝ) * α)
  have h1 : (mprod (fun k => g (n - 1 - k)) n).transpose = sz * mprod g n * sz := by
    rw [mprod_transpose_aux]
    trans mprod (fun j => (g j).transpose) n
    · apply mprod_congr_aux
      intro j hj
      congr 1
      congr 1
      omega
    · trans mprod (fun j => sz * g j * sz) n
      · apply mprod_congr_aux
        intro j _
        rw [hT j]
      · exact mprod_conj sz sz_mul_sz g n
  rw [hrev, ← Matrix.trace_transpose, h1]
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, sz_mul_sz, Matrix.one_mul]

/-! ## 5. The monodromy at energy `0` and phase `1/4` -/

theorem trAq_quarter (p : ℤ) (q N : ℕ) (hN : 1 ≤ N) (hq : q = 2 * N) (hp : Odd p) (lam : ℝ) :
    trAq p q lam 0 (1 / 4) = 2 * ((-1 : ℂ) ^ N) := by
  have hqR : (q : ℝ) = ((2 * N : ℕ) : ℝ) := by rw [hq]
  have hform : ∀ k : ℕ, 2 * Real.pi * (k : ℝ) * ((p : ℝ) / (q : ℝ))
      = 2 * Real.pi * (k : ℝ) * (p : ℝ) / ((2 * N : ℕ) : ℝ) := by
    intro k; rw [hqR]; ring
  have hwpal : ∀ k : ℕ, k ≤ N → dseq p q lam k = dseq p q lam (N - k) := by
    intro k hk
    simp only [dseq]
    rw [hform k, hform (N - k), sin_two_pi_pal_aux N hN p hp k hk]
  have hwanti : ∀ k : ℕ, dseq p q lam (N + k) = -dseq p q lam k := by
    intro k
    simp only [dseq]
    rw [hform (N + k), hform k, sin_two_pi_anti_aux N hN p hp k]
    push_cast; ring
  set F : ℕ → Matrix (Fin 2) (Fin 2) ℂ := fun j => S2 (dseq p q lam j) with hF
  have hF0 : F 0 = S2 0 := by rw [hF]; simp [dseq]
  -- the trace is the trace of the increasing product
  have hstep1 : trAq p q lam 0 (1 / 4) = (mprod F q).trace := by
    have h0 : trAq p q lam 0 (1 / 4) = (iterC ((p : ℝ) / (q : ℝ)) lam 0 q (1 / 4)).trace := by
      rw [trAq, Matrix.trace_fin_two]
    have hAgree : (fun k : ℕ => tmC lam 0 (1 / 4 + (k : ℝ) * ((p : ℝ) / (q : ℝ)))) = F := by
      funext k
      rw [tmC_quarter_eq_S2_aux]
    rw [h0, trace_iterC_eq_trace_mprod_aux, hAgree]
  -- the second half is minus the conjugate of the first
  have hsecond : mprod (fun k => F (N + k)) N = ((-1 : ℂ) ^ N) • (sz * mprod F N * sz) := by
    have hpt : (fun k => F (N + k)) = fun k => (-1 : ℂ) • (sz * F k * sz) := by
      funext k
      show S2 (dseq p q lam (N + k)) = (-1 : ℂ) • (sz * S2 (dseq p q lam k) * sz)
      rw [hwanti k, S2_neg_aux, neg_one_smul]
    have hconst : (Finset.range N).prod (fun _ => (-1 : ℂ)) = (-1 : ℂ) ^ N := by simp
    rw [hpt, mprod_smul, mprod_conj sz sz_mul_sz, hconst]
  -- the half product `mprod F N` has `sz`-traceless `sz`-twist
  have hAtrace : ((mprod F N) * sz).trace = 0 := by
    have hAeq : mprod F N = F 0 * mprod (fun k => F (1 + k)) (N - 1) := by
      have h1 : mprod F N = mprod F 1 * mprod (fun k => F (1 + k)) (N - 1) := by
        rw [← mprod_add, show (1:ℕ) + (N - 1) = N by omega]
      rw [h1, mprod_succ F 0, mprod_zero F, Matrix.one_mul]
    have hB : (mprod (fun k => F (1 + k)) (N - 1)).transpose
        = sz * (mprod (fun k => F (1 + k)) (N - 1)) * sz := by
      refine mprod_pal_transpose_aux (fun k => F (1 + k)) ?_ (N - 1) ?_
      · intro j
        show (S2 (dseq p q lam (1 + j))).transpose
            = sz * S2 (dseq p q lam (1 + j)) * sz
        exact transpose_S2_aux _
      · intro j hj
        show F (1 + j) = F (1 + (N - 1 - 1 - j))
        show S2 (dseq p q lam (1 + j)) = S2 (dseq p q lam (1 + (N - 1 - 1 - j)))
        congr 1
        have hk : 1 + j ≤ N := by omega
        have h2 : N - (1 + j) = 1 + (N - 1 - 1 - j) := by omega
        rw [← h2]
        exact hwpal (1 + j) hk
    have hkey : ((mprod F N) * sz).trace
        = ((mprod (fun k => F (1 + k)) (N - 1)) * (sz * S2 (0:ℂ))).trace := by
      rw [hAeq, hF0, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
    have hX : sz * S2 (0 : ℂ) = !![(0:ℂ), -1; -1, 0] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [sz, S2]
    rw [hkey, hX]
    exact trace_mul_diag_aux _ (pal_entry_aux (mprod (fun k => F (1 + k)) (N - 1)) hB)
  -- assembling
  have hsplit : mprod F q = mprod F N * mprod (fun k => F (N + k)) N := by
    rw [hq, show 2 * N = N + N from by ring, mprod_add]
  have hdetA : (mprod F N).det = 1 := mprod_det_eq_one F (fun k => S2_det _) N
  have hfull : (mprod F q).trace = ((-1 : ℂ) ^ N) * (((mprod F N) * sz).trace ^ 2 + 2) := by
    calc (mprod F q).trace
        = ((mprod F N) * (((-1 : ℂ) ^ N) • (sz * mprod F N * sz))).trace := by
            rw [hsplit, hsecond]
      _ = ((-1 : ℂ) ^ N) * ((mprod F N * (sz * mprod F N * sz)).trace) := by
            rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
      _ = ((-1 : ℂ) ^ N) * (((mprod F N) * sz).trace ^ 2 + 2) := by
            rw [show mprod F N * (sz * mprod F N * sz) = mprod F N * sz * mprod F N * sz from
              by simp only [Matrix.mul_assoc], trace_conj_sz _ hdetA]
  rw [hstep1, hfull, hAtrace]
  ring

/-! ## 6. The discriminant at `0` -/

theorem dsdqDiscZeroAbs (p : ℤ) (q m : ℕ) (hm : q = 2*m+2) (hpq : Nat.Coprime p.natAbs q)
    (lam : ℝ) (hlam : 0 < lam) :
    ‖(Work.TMC14Core.disc p q lam).eval (0 : ℂ)‖ = 2 + 2 * lam ^ q := by
  have hq1 : 1 ≤ q := by omega
  have hq2 : Even q := ⟨m + 1, by omega⟩
  have hp : Odd p := odd_of_coprime_even hpq hq2
  have hN : 1 ≤ m + 1 := by omega
  have hqN : q = 2 * (m + 1) := by omega
  have hcham := chambers p q lam 0 hpq hq1 (1 / 4)
  have htr := trAq_quarter p q (m + 1) hN hqN hp lam
  have hcos : Real.cos (2 * Real.pi * (q : ℝ) * (1 / 4)) = (-1 : ℝ) ^ (m + 1) := by
    have h1 : 2 * Real.pi * (q : ℝ) * (1 / 4) = ((m + 1 : ℕ) : ℝ) * Real.pi := by
      rw [show (q : ℝ) = ((2 * (m + 1) : ℕ) : ℝ) by rw [hqN]]
      push_cast
      ring
    rw [h1, Real.cos_nat_mul_pi]
  have hcoef := chamCoef_even p q lam hq2 hp
  have hval : (disc p q lam).eval 0 = (((-1 : ℝ) ^ (m + 1) * (2 + 2 * lam ^ q) : ℝ) : ℂ) := by
    have h1 : (disc p q lam).eval 0
        = trAq p q lam 0 (1 / 4)
          - chamCoef p q lam * ((Real.cos (2 * Real.pi * (q : ℝ) * (1 / 4)) : ℝ) : ℂ) := by
      rw [hcham]; ring
    rw [h1, htr, hcos, hcoef]
    push_cast
    ring
  rw [hval, show ‖((((-1 : ℝ) ^ (m + 1)) * (2 + 2 * lam ^ q) : ℝ) : ℂ)‖
      = |((-1 : ℝ) ^ (m + 1)) * (2 + 2 * lam ^ q)| from RCLike.norm_ofReal _]
  have habs1 : |((-1 : ℝ) ^ (m + 1))| = 1 := by simp
  rw [abs_mul, habs1, one_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 + 2 * lam ^ q)]

end Work.TMC14Core
