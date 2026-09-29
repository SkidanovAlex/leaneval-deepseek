import Mathlib
import Submission.Work.TMC14Core.dzgen
import Submission.Work.TMC14Core.Chambers
import Submission.Work.TMC14Core.Adjunct.cos_prod_sq

/-!
# `disc_zero_abs`: the discriminant of the rational approximant at `0`

`Δ(0) = ±(2 + 2λ^q)` for `q = 2m+2` and `p` coprime to `q`, whence
`‖Δ(0)‖ = 2 + 2λ^q`.

The value `Δ(0)` is the trace of the `q`-step transfer matrix at the phase `θ = p/(4q)`
(Chambers' formula at `θ = p/(4q)`, where `cos 2πqθ = cos(πp/2) = 0`).  The `q = 2N` step
product splits into two antiperiodic halves; the half-product supertrace is computed by the
graded identity `DZ.half_trace_gen`, and the remaining ingredient is the Gauss-type product
identity `cos_prod_sq`.
-/

open Matrix Polynomial
open scoped BigOperators
open LeanEval.Analysis.TenMartini

noncomputable section

namespace Work.TMC14Core

namespace DZ

/-! ## 1. The chain at the phase `p/(4q)` -/

/-- The `j`-th phase of the rational approximant `p/q` at the reference phase `p/(4q)`. -/
def dphz (p : ℤ) (q : ℕ) (j : ℤ) : ℝ := (p : ℝ) / (4 * (q : ℝ)) + (j : ℝ) * ((p : ℝ) / (q : ℝ))

/-- The energy-zero diagonal entry `-2λ cos 2π x_j` of the transfer matrix. -/
def ddz (p : ℤ) (q : ℕ) (lam : ℝ) (j : ℤ) : ℂ :=
  -(((2 * lam * Real.cos (2 * Real.pi * dphz p q j)) : ℝ) : ℂ)

/-- The transfer matrix at the `j`-th phase. -/
def dS (p : ℤ) (q : ℕ) (lam : ℝ) (j : ℤ) : Matrix (Fin 2) (Fin 2) ℂ := S2 (ddz p q lam j)

/-! ## 2. The decreasing product `bprod` (the order in which `iterC` accumulates) -/

/-- `bprod f a n = f (a+n-1) * ⋯ * f a`. -/
def bprod (f : ℤ → Matrix (Fin 2) (Fin 2) ℂ) (a : ℤ) : ℕ → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => 1
  | n + 1 => f (a + n) * bprod f a n

@[simp] theorem bprod_zero (f : ℤ → Matrix (Fin 2) (Fin 2) ℂ) (a : ℤ) :
    bprod f a 0 = 1 := rfl

@[simp] theorem bprod_succ (f : ℤ → Matrix (Fin 2) (Fin 2) ℂ) (a : ℤ) (n : ℕ) :
    bprod f a (n + 1) = f (a + n) * bprod f a n := rfl

theorem bprod_split (f : ℤ → Matrix (Fin 2) (Fin 2) ℂ) (a : ℤ) (m n : ℕ) :
    bprod f a (m + n) = bprod f (a + m) n * bprod f a m := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.add_succ, bprod_succ, bprod_succ, ih, mul_assoc]
    congr 2
    push_cast
    ring

theorem bprod_shift (f : ℤ → Matrix (Fin 2) (Fin 2) ℂ) (a : ℤ) (n : ℕ) :
    bprod f a n = bprod (fun k : ℤ => f (a + k)) 0 n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [bprod_succ, bprod_succ, ih]
    congr 2
    ring

theorem bprod_conj (X : Matrix (Fin 2) (Fin 2) ℂ) (hX : X * X = 1)
    (f : ℤ → Matrix (Fin 2) (Fin 2) ℂ) (a : ℤ) (n : ℕ) :
    bprod (fun j : ℤ => X * f j * X) a n = X * bprod f a n * X := by
  induction n with
  | zero => rw [bprod_zero, bprod_zero, mul_one, hX]
  | succ n ih =>
    rw [bprod_succ, bprod_succ, ih]
    calc X * f (a + ↑n) * X * (X * bprod f a n * X)
        = X * f (a + ↑n) * (X * X) * (bprod f a n * X) := by simp only [mul_assoc]
      _ = X * f (a + ↑n) * 1 * (bprod f a n * X) := by rw [hX]
      _ = X * (f (a + ↑n) * bprod f a n) * X := by simp only [mul_one, mul_assoc]

theorem bprod_smul (c : ℤ → ℂ) (f : ℤ → Matrix (Fin 2) (Fin 2) ℂ) (a : ℤ) (n : ℕ) :
    bprod (fun j : ℤ => c j • f j) a n
      = (∏ k ∈ Finset.range n, c (a + k)) • bprod f a n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [bprod_succ, ih, bprod_succ, Finset.prod_range_succ, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, mul_comm (∏ k ∈ Finset.range n, c (a + k)) (c (a + ↑n))]

theorem bprod_det (f : ℤ → Matrix (Fin 2) (Fin 2) ℂ) (hf : ∀ j, (f j).det = 1) (a : ℤ)
    (n : ℕ) : (bprod f a n).det = 1 := by
  induction n with
  | zero => simp
  | succ n ih => rw [bprod_succ, Matrix.det_mul, hf, ih, one_mul]

/-! ## 3. The reversal identity -/

theorem transpose_S2 (x : ℂ) : (S2 x)ᵀ = sz * S2 x * sz := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [S2, sz, Matrix.mul_apply, Fin.sum_univ_two]

theorem transpose_sz : (sz : Matrix (Fin 2) (Fin 2) ℂ)ᵀ = sz := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sz]

theorem mprod_transpose (d : ℤ → ℂ) (N : ℕ) :
    (mprod (fun t => S2 (d (t : ℤ))) N)ᵀ = sz * bprod (fun j => S2 (d j)) 0 N * sz := by
  induction N with
  | zero => rw [mprod_zero, bprod_zero]; simp [sz_mul_sz]
  | succ n ih =>
    rw [mprod_succ, Matrix.transpose_mul, ih, transpose_S2, bprod_succ]
    simp only [Nat.cast_add, Nat.cast_one, zero_add, mul_assoc]
    rw [← mul_assoc sz sz, sz_mul_sz, Matrix.one_mul]

/-- The `sz`-twisted trace of the increasing product equals that of the decreasing product. -/
theorem trace_mprod_eq_trace_bprod (d : ℤ → ℂ) (N : ℕ) :
    ((mprod (fun t => S2 (d (t : ℤ))) N) * sz).trace
      = ((bprod (fun j => S2 (d j)) 0 N) * sz).trace := by
  have h := mprod_transpose d N
  rw [← Matrix.trace_transpose ((mprod (fun t => S2 (d (t : ℤ))) N) * sz), Matrix.transpose_mul,
    transpose_sz, h, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc sz sz, sz_mul_sz, Matrix.one_mul]

/-! ## 4. The `iterC` bridge -/

theorem tmC_zero_eq_S2 (lam : ℝ) (x : ℝ) :
    tmC lam 0 x = S2 (((-(2 * lam * Real.cos (2 * Real.pi * x))) : ℝ) : ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tmC, S2]

theorem iterC_zero_eq_bprod (p : ℤ) (q : ℕ) (lam : ℝ) (n : ℕ) :
    iterC ((p : ℝ) / (q : ℝ)) lam 0 n (dphz p q 0) = bprod (dS p q lam) 0 n := by
  induction n with
  | zero => simp [iterC, bprod]
  | succ n ih =>
    rw [iterC_succ, ih, bprod_succ]
    congr 1
    rw [tmC_zero_eq_S2]
    congr 2
    simp only [dS, ddz, dphz]
    push_cast
    ring_nf

/-! ## 5. The half trace -/

theorem bprod_half_trace (f : ℤ → Matrix (Fin 2) (Fin 2) ℂ) (N : ℕ)
    (hanti : ∀ j : ℤ, f (j + (N : ℤ)) = -sz * f j * sz) (hdet : ∀ j, (f j).det = 1) :
    (bprod f 0 (2 * N)).trace = (-1 : ℂ) ^ N * (((bprod f 0 N * sz).trace) ^ 2 + 2) := by
  have h2 : (2 : ℕ) * N = N + N := by ring
  have hsplit : bprod f 0 (2 * N) = bprod f N N * bprod f 0 N := by
    rw [h2, bprod_split]
    norm_num
  have hhalf : bprod f N N = (-1 : ℂ) ^ N • (sz * bprod f 0 N * sz) := by
    rw [bprod_shift f N N]
    have hfun : (fun k : ℤ => f (↑N + k)) = (fun k : ℤ => (-1 : ℂ) • (sz * f k * sz)) := by
      funext k
      rw [show (↑N : ℤ) + k = k + (↑N : ℤ) from add_comm _ _, hanti k]
      simp
    rw [hfun, bprod_smul, bprod_conj _ sz_mul_sz, Finset.prod_const, Finset.card_range]
  rw [hsplit, hhalf, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  have htr : (sz * bprod f 0 N * sz * bprod f 0 N).trace
      = (bprod f 0 N * sz * bprod f 0 N * sz).trace := by
    rw [show sz * bprod f 0 N * sz * bprod f 0 N
          = sz * (bprod f 0 N * sz * bprod f 0 N) from by simp only [mul_assoc],
      Matrix.trace_mul_comm]
  rw [htr, trace_conj_sz _ (bprod_det f hdet 0 N)]

/-! ## 6. The phase shift and the parametrisation -/

theorem ddz_add (p : ℤ) (q : ℕ) (lam : ℝ) (N : ℕ) (hN : 1 ≤ N) (hq : q = 2 * N) (hp : Odd p)
    (j : ℤ) : ddz p q lam (j + N) = -ddz p q lam j := by
  have hq0 : (q : ℝ) ≠ 0 := by rw [hq]; positivity
  have hangle : 2 * Real.pi * dphz p q (j + N) = 2 * Real.pi * dphz p q j + (p : ℝ) * Real.pi := by
    simp only [dphz]
    field_simp
    push_cast [hq]
    ring
  rw [ddz, ddz, hangle, Real.cos_add_int_mul_pi, Odd.neg_one_zpow hp]
  push_cast
  ring

theorem dS_add (p : ℤ) (q : ℕ) (lam : ℝ) (N : ℕ) (hN : 1 ≤ N) (hq : q = 2 * N) (hp : Odd p)
    (j : ℤ) : dS p q lam (j + N) = -sz * dS p q lam j * sz := by
  rw [dS, dS, ddz_add p q lam N hN hq hp j, S2_neg, Matrix.neg_mul, Matrix.neg_mul]

/-- `u = e^{iπp/(4N)}`. -/
def ut (p : ℤ) (N : ℕ) : ℂ := Complex.exp (Complex.I * ((p : ℝ) * Real.pi / (4 * (N : ℝ))))

/-- `ζ = e^{iπp/N}`. -/
def zt (p : ℤ) (N : ℕ) : ℂ := Complex.exp (Complex.I * ((p : ℝ) * Real.pi / (N : ℝ)))

theorem ut_ne_zero (p : ℤ) (N : ℕ) : ut p N ≠ 0 := Complex.exp_ne_zero _

theorem zt_primitive (p : ℤ) (N : ℕ) (hN : 1 ≤ N) (hpq : Nat.Coprime p.natAbs (2 * N)) :
    IsPrimitiveRoot (zt p N) (2 * N) := by
  have h0 : 2 * N ≠ 0 := by omega
  have hcop : IsCoprime p ((2 * N : ℕ) : ℤ) := by
    rw [Int.isCoprime_iff_nat_coprime, Int.natAbs_natCast]
    exact hpq
  have h := Complex.isPrimitiveRoot_exp_of_isCoprime p (2 * N) h0 hcop
  have heq : Complex.exp (2 * Real.pi * Complex.I * ((p : ℂ) / ((2 * N : ℕ) : ℂ))) = zt p N := by
    rw [zt]
    congr 1
    push_cast
    field_simp
  rwa [heq] at h

theorem ee_eq_ut_zt (p : ℤ) (q : ℕ) (N : ℕ) (hN : 1 ≤ N) (hq : q = 2 * N) (t : ℕ) :
    ee (dphz p q (t : ℤ)) = ut p N * (zt p N) ^ t := by
  have hq0 : (q : ℝ) ≠ 0 := by rw [hq]; positivity
  have harg : 2 * Real.pi * Complex.I * (dphz p q (t : ℤ) : ℂ)
      = Complex.I * ((p : ℝ) * Real.pi / (4 * (N : ℝ)))
        + (t : ℂ) * (Complex.I * ((p : ℝ) * Real.pi / (N : ℝ))) := by
    simp only [dphz]
    push_cast [hq]
    field_simp
  rw [ee, ut, zt, ← Complex.exp_nat_mul, ← Complex.exp_add, harg]

theorem ddz_eq_gen (p : ℤ) (q : ℕ) (lam : ℝ) (N : ℕ) (hN : 1 ≤ N) (hq : q = 2 * N)
    (t : ℕ) :
    ddz p q lam (t : ℤ)
      = ((-(2 * lam) / 2) * (ut p N * (zt p N) ^ t + (ut p N * (zt p N) ^ t)⁻¹)) := by
  have h1 : (((2 * lam * Real.cos (2 * Real.pi * dphz p q (t : ℤ))) : ℝ) : ℂ)
      = (lam : ℂ) * (ee (dphz p q (t : ℤ)) + (ee (dphz p q (t : ℤ)))⁻¹) := by
    have h := two_cos_eq (dphz p q (t : ℤ))
    rw [show (((2 * lam * Real.cos (2 * Real.pi * dphz p q (t : ℤ))) : ℝ) : ℂ)
        = (lam : ℂ) * (((2 : ℝ) : ℂ)
            * ((Real.cos (2 * Real.pi * dphz p q (t : ℤ))) : ℂ)) by push_cast; ring, h]
  rw [ddz, h1, ee_eq_ut_zt p q N hN hq t]
  ring

/-! ## 7. Oddness and the phase `p/(4q)` -/

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

/-- Chambers' formula at `θ = p/(4q)` gives `Δ(0)`, since `cos(2πqθ) = cos(πp/2) = 0`. -/
theorem trAq_dphz_zero (p : ℤ) (q : ℕ) (lam : ℝ) (hq : 1 ≤ q) (hpq : Nat.Coprime p.natAbs q)
    (hp : Odd p) : trAq p q lam 0 (dphz p q 0) = (disc p q lam).eval 0 := by
  have hch := chambers p q lam 0 hpq hq (dphz p q 0)
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  have hcos : (Real.cos (2 * Real.pi * (q : ℝ) * dphz p q 0) : ℂ) = 0 := by
    have harg : 2 * Real.pi * (q : ℝ) * dphz p q 0 = (p : ℝ) * Real.pi / 2 := by
      simp only [dphz]
      field_simp
      ring
    obtain ⟨k, hk⟩ := hp
    have h2 : (p : ℝ) * Real.pi / 2 = Real.pi / 2 + (k : ℝ) * Real.pi := by
      rw [hk]; push_cast; ring
    rw [harg, h2, Real.cos_add_int_mul_pi, Real.cos_pi_div_two, mul_zero]
    exact Complex.ofReal_zero
  rw [hch, hcos, mul_zero, add_zero]

/-- `Δ(0)` as the trace of the `q`-step product of the `dS`. -/
theorem disc_eval_zero_eq (p : ℤ) (q : ℕ) (lam : ℝ) (N : ℕ) (hN : 1 ≤ N) (hq : q = 2 * N)
    (hpq : Nat.Coprime p.natAbs q) (hp : Odd p) :
    (disc p q lam).eval 0 = (bprod (dS p q lam) 0 q).trace := by
  have hq1 : 1 ≤ q := by omega
  rw [← trAq_dphz_zero p q lam hq1 hpq hp, trAq, ← Matrix.trace_fin_two]
  congr 1
  exact iterC_zero_eq_bprod p q lam q

/-! ## 8. The `ddz` in cosine form and their product -/

theorem ddz_eq_cos (p : ℤ) (q : ℕ) (lam : ℝ) (N : ℕ) (hN : 1 ≤ N) (hq : q = 2 * N)
    (j : ℕ) :
    ddz p q lam (j : ℤ)
      = -(((2 * lam * Real.cos (Real.pi * (4 * (j : ℝ) + 1) * (p : ℝ) / (4 * (N : ℝ)))) : ℝ)
          : ℂ) := by
  have hq0 : (q : ℝ) ≠ 0 := by rw [hq]; positivity
  rw [ddz, dphz]
  congr 2
  push_cast [hq]
  field_simp
  ring

theorem sq_prod_ddz (p : ℤ) (q : ℕ) (lam : ℝ) (N : ℕ) (hN : 1 ≤ N) (hq : q = 2 * N)
    (hpq : Nat.Coprime p.natAbs q) :
    (∏ j ∈ Finset.range N, ddz p q lam (j : ℤ)) ^ 2 = ((2 * lam ^ (2 * N) : ℝ) : ℂ) := by
  have hcp : Nat.Coprime p.natAbs (2 * N) := by rw [← hq]; exact hpq
  set P : ℝ := ∏ j ∈ Finset.range N,
    Real.cos (Real.pi * (4 * (j : ℝ) + 1) * (p : ℝ) / (4 * (N : ℝ))) with hP
  have hcos : ∀ j : ℕ, Real.cos (Real.pi * (4 * (j : ℝ) + 1) * (p : ℝ) / (4 * (N : ℝ)))
      = Real.cos (Real.pi * (4 * (j : ℝ) + 1) * (p.natAbs : ℝ) / (4 * (N : ℝ))) := by
    intro j
    by_cases hpos : 0 ≤ p
    · have h1 : (p.natAbs : ℝ) = (p : ℝ) := by
        rw [← Int.cast_natCast (R := ℝ), Int.natAbs_of_nonneg hpos]
      rw [h1]
    · have hz : (p.natAbs : ℤ) = -p := by
        have hz0 : ((-p).natAbs : ℤ) = -p := Int.natAbs_of_nonneg (by omega)
        rwa [Int.natAbs_neg] at hz0
      have h1 : (p.natAbs : ℝ) = -(p : ℝ) := by
        rw [← Int.cast_natCast (R := ℝ), hz, Int.cast_neg]
      rw [h1,
        show Real.pi * (4 * (j : ℝ) + 1) * (-(p : ℝ)) / (4 * (N : ℝ))
            = -(Real.pi * (4 * (j : ℝ) + 1) * (p : ℝ) / (4 * (N : ℝ))) by ring,
        Real.cos_neg]
  have hQ : (∏ j ∈ Finset.range N,
      (2 * Real.cos (Real.pi * (4 * (j : ℝ) + 1) * (p : ℝ) / (4 * (N : ℝ))))) ^ 2 = 2 := by
    rw [Finset.prod_congr rfl (fun j _ => by rw [hcos j])]
    exact Adjunct.cos_prod_sq N p.natAbs hN hcp
  have hP2 : P ^ 2 = 2 / (4 : ℝ) ^ N := by
    have h2N : (∏ j ∈ Finset.range N,
        (2 * Real.cos (Real.pi * (4 * (j : ℝ) + 1) * (p : ℝ) / (4 * (N : ℝ)))))
        = (2 : ℝ) ^ N * P := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← hP]
    rw [h2N] at hQ
    have h4 : (((2 : ℝ) ^ N)) ^ 2 = (4 : ℝ) ^ N := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow, pow_two]
    have h2p : ((2 : ℝ) ^ N) ≠ 0 := pow_ne_zero _ (by norm_num)
    calc P ^ 2 = (((2 : ℝ) ^ N * P) ^ 2) / (((2 : ℝ) ^ N)) ^ 2 := by
          field_simp
      _ = 2 / (4 : ℝ) ^ N := by rw [hQ, h4]
  have hprod : (∏ j ∈ Finset.range N, ddz p q lam (j : ℤ))
      = ((-1 : ℂ) ^ N) * ((((2 * lam : ℝ) ^ N) * P : ℝ) : ℂ) := by
    have h1 : (∏ j ∈ Finset.range N, ddz p q lam (j : ℤ))
        = (∏ j ∈ Finset.range N,
            -(((2 * lam * Real.cos (Real.pi * (4 * (j : ℝ) + 1) * (p : ℝ) / (4 * (N : ℝ)))) : ℝ)
              : ℂ)) :=
      Finset.prod_congr rfl (fun j _ => ddz_eq_cos p q lam N hN hq j)
    rw [h1, Finset.prod_neg, Finset.card_range]
    congr 1
    change (∏ x ∈ Finset.range N,
        Complex.ofRealHom (2 * lam * Real.cos (Real.pi * (4 * (x : ℝ) + 1) * (p : ℝ)
          / (4 * (N : ℝ))))) = Complex.ofRealHom (((2 * lam : ℝ) ^ N) * P)
    rw [← map_prod Complex.ofRealHom, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_range, ← hP]
  have hsq : ((((2 * lam : ℝ) ^ N) * P) ^ 2) = 2 * lam ^ (2 * N) := by
    rw [mul_pow, ← pow_mul, hP2]
    have h4 : (4 : ℝ) ^ N = (2 : ℝ) ^ (2 * N) := by rw [pow_mul]; norm_num
    rw [h4, show N * 2 = 2 * N by ring, mul_pow]
    have hne : ((2 : ℝ) ^ (2 * N)) ≠ 0 := pow_ne_zero _ (by norm_num)
    field_simp
  calc (∏ j ∈ Finset.range N, ddz p q lam (j : ℤ)) ^ 2
      = (((-1 : ℂ) ^ N) ^ 2) * (((((2 * lam : ℝ) ^ N) * P : ℝ) : ℂ) ^ 2) := by
        rw [hprod, mul_pow]
    _ = (((((2 * lam : ℝ) ^ N) * P) ^ 2 : ℝ) : ℂ) := by
        rw [show ((-1 : ℂ) ^ N) ^ 2 = 1 by
          rw [← pow_mul]
          exact Even.neg_one_pow (⟨N, by ring⟩ : Even (N * 2)), one_mul]
        exact (map_pow Complex.ofRealHom (((2 * lam : ℝ) ^ N) * P) 2).symm
    _ = ((2 * lam ^ (2 * N) : ℝ) : ℂ) := by rw [hsq]

/-! ## 9. The theorem -/

theorem disc_zero_abs_aux (p : ℤ) (q m : ℕ) (lam : ℝ) (hm : q = 2 * m + 2)
    (hpq : Nat.Coprime p.natAbs q) (hlam : 0 < lam) :
    ‖(disc p q lam).eval (0 : ℂ)‖ = 2 + 2 * lam ^ q := by
  have hq2 : Even q := ⟨m + 1, by omega⟩
  have hp : Odd p := odd_of_coprime_even hpq hq2
  have hN : 1 ≤ m + 1 := by omega
  have hqN : q = 2 * (m + 1) := by omega
  have hhalf := bprod_half_trace (dS p q lam) (m + 1)
    (fun j => dS_add p q lam (m + 1) hN hqN hp j) (fun j => S2_det _)
  have hident := half_trace_gen (m + 1) hN (-(2 * lam)) (zt p (m + 1)) (ut p (m + 1))
    (zt_primitive p (m + 1) hN (by rw [← hqN]; exact hpq)) (ut_ne_zero p (m + 1))
  have hhalf' : ((mprod (fun t : ℕ => S2 (ddz p q lam (t : ℤ))) (m + 1)) * sz).trace
      = ∏ t ∈ Finset.range (m + 1), ddz p q lam (t : ℤ) := by
    have hfun : (fun t : ℕ => S2 (ddz p q lam (t : ℤ)))
        = (fun t : ℕ => S2 ((-(2 * lam) / 2)
            * (ut p (m + 1) * (zt p (m + 1)) ^ t + (ut p (m + 1) * (zt p (m + 1)) ^ t)⁻¹))) := by
      funext t
      rw [ddz_eq_gen p q lam (m + 1) hN hqN t]
    rw [hfun, hident]
    exact Finset.prod_congr rfl (fun t _ => (ddz_eq_gen p q lam (m + 1) hN hqN t).symm)
  have htrace : (bprod (dS p q lam) 0 (m + 1) * sz).trace
      = ∏ t ∈ Finset.range (m + 1), ddz p q lam (t : ℤ) := by
    change ((bprod (fun j : ℤ => S2 (ddz p q lam j)) 0 (m + 1)) * sz).trace
      = ∏ t ∈ Finset.range (m + 1), ddz p q lam (t : ℤ)
    rw [← trace_mprod_eq_trace_bprod (fun j : ℤ => ddz p q lam j) (m + 1), hhalf']
  have hsq := sq_prod_ddz p q lam (m + 1) hN hqN hpq
  have hval : (disc p q lam).eval 0
      = (((-1 : ℝ) ^ (m + 1) * (2 + 2 * lam ^ q) : ℝ) : ℂ) := by
    rw [disc_eval_zero_eq p q lam (m + 1) hN hqN hpq hp,
      congrArg (fun n : ℕ => (bprod (dS p q lam) 0 n).trace) hqN]
    rw [hhalf, htrace, hsq, show (2 * lam ^ (2 * (m + 1)) : ℝ) = 2 * lam ^ q by rw [hqN]]
    push_cast
    ring
  rw [hval, show ‖((((-1 : ℝ) ^ (m + 1)) * (2 + 2 * lam ^ q) : ℝ) : ℂ)‖
      = |((-1 : ℝ) ^ (m + 1)) * (2 + 2 * lam ^ q)| from RCLike.norm_ofReal _,
    abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 + 2 * lam ^ q)]
  simp


end DZ

/-- The discriminant `Δ(0)` of the rational approximant `p/q` with `q = 2m+2` and `p` coprime
to `q` has modulus `2 + 2λ^q`. -/
theorem disc_zero_abs (p : ℤ) (q m : ℕ) (lam : ℝ) (hm : q = 2 * m + 2)
    (hpq : Nat.Coprime p.natAbs q) (hlam : 0 < lam) :
    ‖(Work.TMC14Core.disc p q lam).eval (0 : ℂ)‖ = 2 + 2 * lam ^ q :=
  DZ.disc_zero_abs_aux p q m lam hm hpq hlam

end Work.TMC14Core
