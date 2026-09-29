import Mathlib
import Submission.Work.TMC14Core.Assembly
import Submission.Work.TMC14Core.zero_aux
import Submission.Work.TMC14Core.dzAux
import Submission.Work.TMC14Core.halfProductTraceGenAux
import Submission.Work.TMC14Core.cosProdQuarterSq

open Matrix

noncomputable section

namespace Work.TMC14Core

/-- The `j`-th phase of the rational approximant `p/q` at the reference phase `1/(4q)`. -/
def phz (p : ℤ) (q : ℕ) (j : ℤ) : ℝ :=
  1 / (4 * (q : ℝ)) + (j : ℝ) * ((p : ℝ) / (q : ℝ))

/-- The energy-zero diagonal entry at the `j`-th phase: `-2λ cos 2π x_j`. -/
def dz (p : ℤ) (q : ℕ) (lam : ℝ) (j : ℤ) : ℂ :=
  -(((2 * lam * Real.cos (2 * Real.pi * phz p q j)) : ℝ) : ℂ)

/-- The energy-zero transfer matrix at the `j`-th phase. -/
def Sz (p : ℤ) (q : ℕ) (lam : ℝ) (j : ℤ) : Matrix (Fin 2) (Fin 2) ℂ :=
  S2 (dz p q lam j)

/-! ## 2. Products of transfer matrices in the order used by `iterC` -/

/-- `bprod f a n = f (a+n-1) * f (a+n-2) * ⋯ * f a`, the order in which `iterC` accumulates
(with the index increasing). -/
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

/-! ## 3. `iterC` at zero energy -/

theorem trace_mul_sz (M : Matrix (Fin 2) (Fin 2) ℂ) : (M * sz).trace = (sz * M).trace :=
  Matrix.trace_mul_comm M sz

/-- The increasing product `f 0 * f 1 * ⋯ * f (n-1)` as a `List.prod`. -/
def iprod {α : Type*} [Monoid α] (f : ℕ → α) (n : ℕ) : α := ((List.range n).map f).prod

theorem iprod_succ {α : Type*} [Monoid α] (f : ℕ → α) (n : ℕ) :
    iprod f (n + 1) = iprod f n * f n := by
  simp only [iprod, List.range_succ, List.map_append, List.prod_append, List.map_cons,
    List.map_nil, List.prod_cons, List.prod_nil, mul_one]

theorem transpose_S2 (x : ℂ) : (S2 x)ᵀ = sz * S2 x * sz := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [S2, sz, Matrix.mul_apply, Fin.sum_univ_two]

theorem transpose_sz_eq : szᵀ = sz := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sz]

/-- Transposing the increasing product reverses the order, and `S2 xᵀ = sz * S2 x * sz`. -/
theorem iprod_transpose (d : ℤ → ℂ) (n : ℕ) :
    (iprod (fun t : ℕ => S2 (d (t : ℤ))) n)ᵀ
      = sz * bprod (fun j : ℤ => S2 (d j)) 0 n * sz := by
  induction n with
  | zero => simp [iprod, bprod, sz_mul_sz]
  | succ n ih =>
    rw [iprod_succ, Matrix.transpose_mul, ih, transpose_S2, bprod_succ]
    simp only [zero_add, mul_assoc]
    rw [← mul_assoc sz sz, sz_mul_sz, one_mul]

/-- **Reversal identity**: the trace of the increasing product twisted by `sz` equals the trace
of the decreasing (backward) product twisted by `sz`. -/
theorem trace_iprod_eq_trace_bprod (d : ℤ → ℂ) (n : ℕ) :
    (iprod (fun t : ℕ => S2 (d (t : ℤ))) n * sz).trace
      = ((bprod (fun j : ℤ => S2 (d j)) 0 n) * sz).trace := by
  have h := iprod_transpose d n
  rw [← Matrix.trace_transpose (iprod (fun t : ℕ => S2 (d (t : ℤ))) n * sz), Matrix.transpose_mul,
    transpose_sz_eq, h, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc sz sz, sz_mul_sz, Matrix.one_mul]

theorem tmC_zero_eq_S2 (lam : ℝ) (x : ℝ) :
    tmC lam 0 x = S2 (((-(2 * lam * Real.cos (2 * Real.pi * x))) : ℝ) : ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tmC, S2]

theorem iterC_zero_eq_bprod (p : ℤ) (q : ℕ) (lam : ℝ) (n : ℕ) :
    iterC ((p : ℝ) / (q : ℝ)) lam 0 n (1 / (4 * (q : ℝ))) = bprod (Sz p q lam) 0 n := by
  induction n with
  | zero => simp [iterC, bprod]
  | succ n ih =>
    rw [iterC_succ, ih, bprod_succ]
    congr 1
    rw [tmC_zero_eq_S2, Sz, dz]
    congr 2
    simp only [phz]
    push_cast
    ring_nf

/-! ## 4. The half-trace identity -/

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

/-! ## 5. The phase shift -/

theorem dz_add (p : ℤ) (q : ℕ) (lam : ℝ) (N : ℕ) (hN : 1 ≤ N) (hq : q = 2 * N) (hp : Odd p)
    (j : ℤ) :
    dz p q lam (j + N) = -dz p q lam j := by
  have hq0 : (q : ℝ) ≠ 0 := by
    rw [hq]
    have h : (2 * N : ℕ) ≠ 0 := by omega
    exact_mod_cast h
  have hangle : 2 * Real.pi * phz p q (j + N) = 2 * Real.pi * phz p q j + (p : ℝ) * Real.pi := by
    simp only [phz]
    field_simp
    push_cast [hq]
    ring
  rw [dz, dz, hangle, Real.cos_add_int_mul_pi, Odd.neg_one_zpow hp]
  push_cast
  ring




/-! ## 5. The generic parameters `u = e^{iπ/(4N)}`, `ζ = e^{iπp/N}` -/

/-- `u = e^{iπ/(4N)}`, the phase of the `0`-th transfer matrix. -/
def ut (N : ℕ) : ℂ := Complex.exp (Complex.I * (Real.pi / (4 * (N : ℝ))))

/-- `ζ = e^{iπp/N}`, the phase step. -/
def zt (p : ℤ) (N : ℕ) : ℂ := Complex.exp (Complex.I * ((p : ℝ) * Real.pi / (N : ℝ)))

theorem ut_ne_zero (N : ℕ) : ut N ≠ 0 := Complex.exp_ne_zero _

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
    ee (phz p q (t : ℤ)) = ut N * (zt p N) ^ t := by
  have hq0 : (q : ℝ) ≠ 0 := by rw [hq]; positivity
  have harg : 2 * Real.pi * Complex.I * (phz p q (t : ℤ) : ℂ)
      = Complex.I * (Real.pi / (4 * (N : ℝ)))
        + (t : ℂ) * (Complex.I * ((p : ℝ) * Real.pi / (N : ℝ))) := by
    simp only [phz]
    push_cast [hq]
    field_simp
  rw [ee, ut, zt, ← Complex.exp_nat_mul, ← Complex.exp_add, harg]

theorem dz_eq_gen (p : ℤ) (q : ℕ) (lam : ℝ) (N : ℕ) (hN : 1 ≤ N) (hq : q = 2 * N) (t : ℕ) :
    dz p q lam (t : ℤ)
      = ((-(2 * lam) / 2) * (ut N * (zt p N) ^ t + (ut N * (zt p N) ^ t)⁻¹)) := by
  have h1 : (((2 * lam * Real.cos (2 * Real.pi * phz p q (t : ℤ))) : ℝ) : ℂ)
      = (lam : ℂ) * (ee (phz p q (t : ℤ)) + (ee (phz p q (t : ℤ)))⁻¹) := by
    have h := two_cos_eq (phz p q (t : ℤ))
    rw [show (((2 * lam * Real.cos (2 * Real.pi * phz p q (t : ℤ))) : ℝ) : ℂ)
        = (lam : ℂ) * (((2 : ℝ) : ℂ)
            * ((Real.cos (2 * Real.pi * phz p q (t : ℤ))) : ℂ)) by push_cast; ring, h]
  rw [dz, h1, ee_eq_ut_zt p q N hN hq t]
  ring

/-! ## 6. The reduction `Δ(0) = tr (bprod Sz 0 q)` -/

theorem disc_eval_zero_eq (p : ℤ) (q : ℕ) (lam : ℝ) (hq : 1 ≤ q) :
    (disc p q lam).eval 0 = (bprod (Sz p q lam) 0 q).trace := by
  rw [disc_eval p q lam 0 hq, trAq_eq_trace, iterC_zero_eq_bprod]

/-! ## 7. The half-product trace identity (from the generic lemma) -/

theorem half_ident
    (hGen : ∀ (N : ℕ), 1 ≤ N → ∀ (a u ζ : ℂ), u ≠ 0 → IsPrimitiveRoot ζ (2 * N) →
      (((List.range N).map (fun t : ℕ => S2 ((a / 2) * (u * ζ ^ t + (u * ζ ^ t)⁻¹)))).prod * sz).trace
        = ∏ t ∈ Finset.range N, ((a / 2) * (u * ζ ^ t + (u * ζ ^ t)⁻¹)))
    (p : ℤ) (q : ℕ) (lam : ℝ) (N : ℕ) (hN : 1 ≤ N) (hq : q = 2 * N)
    (hpq : Nat.Coprime p.natAbs q) :
    (bprod (fun j : ℤ => S2 (dz p q lam j)) 0 N * sz).trace
      = ∏ j ∈ Finset.range N, dz p q lam j := by
  have hqp : Nat.Coprime p.natAbs (2 * N) := by rw [← hq]; exact hpq
  have hfun : (fun t : ℕ => S2 (dz p q lam (t : ℤ)))
      = (fun t : ℕ => S2 ((-(2 * lam) / 2) * (ut N * (zt p N) ^ t + (ut N * (zt p N) ^ t)⁻¹))) := by
    funext t
    rw [dz_eq_gen p q lam N hN hq t]
  rw [← trace_iprod_eq_trace_bprod (dz p q lam) N, iprod, hfun,
    hGen N hN (-(2 * lam)) (ut N) (zt p N) (ut_ne_zero N) (zt_primitive p N hN hqp)]
  refine Finset.prod_congr rfl (fun t _ => ?_)
  rw [dz_eq_gen p q lam N hN hq t]

/-! ## 8. The square of the product of the `dz j` -/

theorem dz_eq_cos (p : ℤ) (q : ℕ) (lam : ℝ) (N : ℕ) (hN : 1 ≤ N) (hq : q = 2 * N) (j : ℕ) :
    dz p q lam (j : ℤ)
      = -(((2 * lam * Real.cos (Real.pi * (4 * (j : ℝ) * (p : ℝ) + 1) / (4 * (N : ℝ)))) : ℝ) : ℂ) := by
  have hq0 : (q : ℝ) ≠ 0 := by rw [hq]; positivity
  rw [dz, phz]
  congr 2
  push_cast [hq]
  field_simp
  ring

/-! ## 8a. The general (frequency-dependent) cosine product -/

theorem cosProdGen (N : ℕ) (hN : 1 ≤ N) (P : ℤ) (hP : Nat.Coprime P.natAbs N) :
    (∏ j ∈ Finset.range N, Real.cos (Real.pi * (4 * (j : ℝ) * (P : ℝ) + 1) / (4 * N))) ^ 2
      = 2 / (4 : ℝ) ^ N := by
  have hNpos : (0 : ℤ) < (N : ℤ) := by omega
  have hNr : (N : ℝ) ≠ 0 := by positivity
  have hcop : IsCoprime (N : ℤ) P := by
    rw [Int.isCoprime_iff_nat_coprime, Int.natAbs_natCast]
    exact hP.symm
  set φ : ℕ → ℕ := fun j => (((j : ℤ) * P) % (N : ℤ)).toNat with hφdef
  have hφval : ∀ j : ℕ, ((φ j : ℕ) : ℤ) = ((j : ℤ) * P) % (N : ℤ) := by
    intro j
    rw [hφdef]
    exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))
  have hrep : ∀ j : ℕ, (j : ℤ) * P = (N : ℤ) * (((j : ℤ) * P) / (N : ℤ)) + (φ j : ℤ) := by
    intro j
    rw [hφval j]
    exact (Int.mul_ediv_add_emod _ _).symm
  have hφlt : ∀ j, φ j < N := by
    intro j
    have h := Int.emod_lt_of_pos ((j : ℤ) * P) hNpos
    have h2 : ((φ j : ℕ) : ℤ) = ((j : ℤ) * P) % (N : ℤ) := hφval j
    have h3 : ((φ j : ℕ) : ℤ) < (N : ℤ) := by rw [h2]; exact h
    exact_mod_cast h3
  have hterm : ∀ j : ℕ, Real.cos (Real.pi * (4 * (j : ℝ) * (P : ℝ) + 1) / (4 * N))
      = (-1 : ℝ) ^ (((j : ℤ) * P) / (N : ℤ))
        * Real.cos (Real.pi * (4 * (φ j : ℝ) + 1) / (4 * N)) := by
    intro j
    have harg : Real.pi * (4 * (j : ℝ) * (P : ℝ) + 1) / (4 * N)
        = Real.pi * (4 * (φ j : ℝ) + 1) / (4 * N)
          + ((((j : ℤ) * P) / (N : ℤ) : ℤ) : ℝ) * Real.pi := by
      have h3 : ((j : ℤ) * P : ℝ)
          = (N : ℝ) * ((((j : ℤ) * P) / (N : ℤ) : ℤ) : ℝ) + (φ j : ℝ) := by
        exact_mod_cast (hrep j)
      have h4 : (j : ℝ) * (P : ℝ) = ((j : ℤ) * P : ℝ) := by push_cast; ring
      rw [show (4 * (j : ℝ) * (P : ℝ) + 1) = 4 * ((j : ℝ) * (P : ℝ)) + 1 by ring, h4, h3]
      field_simp
      ring
    rw [harg, Real.cos_add_int_mul_pi]
  have hinj : Set.InjOn φ (↑(Finset.range N) : Set ℕ) := by
    intro j₁ h₁ j₂ h₂ heq
    have h₁' : j₁ < N := Finset.mem_range.mp h₁
    have h₂' : j₂ < N := Finset.mem_range.mp h₂
    have h3 : ((j₁ : ℤ) * P) % (N : ℤ) = ((j₂ : ℤ) * P) % (N : ℤ) := by
      rw [← hφval j₁, ← hφval j₂, heq]
    have h5 : ((N : ℤ)) ∣ ((j₁ : ℤ) - (j₂ : ℤ)) * P := by
      have h6 : (((j₁ : ℤ) * P) - ((j₂ : ℤ) * P)) % (N : ℤ) = 0 := by
        rw [← Int.emod_eq_emod_iff_emod_sub_eq_zero]
        exact h3
      have h7 : ((j₁ : ℤ) - (j₂ : ℤ)) * P = ((j₁ : ℤ) * P) - ((j₂ : ℤ) * P) := by ring
      rw [h7]
      exact Int.dvd_of_emod_eq_zero h6
    have h8 : (N : ℤ) ∣ ((j₁ : ℤ) - (j₂ : ℤ)) := hcop.dvd_of_dvd_mul_right h5
    have h9 : |((j₁ : ℤ) - (j₂ : ℤ))| < (N : ℤ) := by
      have h10 : (j₁ : ℤ) < (N : ℤ) := by exact_mod_cast h₁'
      have h11 : (j₂ : ℤ) < (N : ℤ) := by exact_mod_cast h₂'
      rw [abs_lt]; constructor <;> omega
    have h12 : ((j₁ : ℤ) - (j₂ : ℤ)) = 0 := by
      rcases h8 with ⟨k, hk⟩
      have h13 : |k| * (N : ℤ) = |((j₁ : ℤ) - (j₂ : ℤ))| := by
        have h16 : |((j₁ : ℤ) - (j₂ : ℤ))| = |k| * (N : ℤ) := by
          rw [hk, abs_mul, abs_of_nonneg (show (0 : ℤ) ≤ (N : ℤ) by omega)]
          ring
        exact h16.symm
      have h14 : |k| = 0 := by
        have h15 : |k| * (N : ℤ) < (N : ℤ) := by rw [h13]; exact h9
        nlinarith [h15, hNpos, abs_nonneg k]
      have hk0 : k = 0 := abs_eq_zero.mp h14
      rw [hk0, mul_zero] at hk
      exact hk
    exact_mod_cast (sub_eq_zero.mp h12)
  have hbi : (Finset.range N).image φ = Finset.range N := by
    refine Finset.eq_of_subset_of_card_le (fun y hy => ?_) ?_
    · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hy
      exact Finset.mem_range.mpr (hφlt j)
    · rw [Finset.card_image_of_injOn hinj, Finset.card_range]
  have hstep : (∏ j ∈ Finset.range N, Real.cos (Real.pi * (4 * (j : ℝ) * (P : ℝ) + 1) / (4 * N)))
      = (∏ j ∈ Finset.range N, (-1 : ℝ) ^ (((j : ℤ) * P) / (N : ℤ)))
        * (∏ j ∈ Finset.range N, Real.cos (Real.pi * (4 * (φ j : ℝ) + 1) / (4 * N))) := by
    rw [Finset.prod_congr rfl (fun j _ => hterm j), Finset.prod_mul_distrib]
  have hreindex : (∏ j ∈ Finset.range N, Real.cos (Real.pi * (4 * (φ j : ℝ) + 1) / (4 * N)))
      = (∏ j ∈ Finset.range N, Real.cos (Real.pi * (4 * (j : ℝ) + 1) / (4 * N))) := by
    conv_rhs => rw [← hbi]
    rw [Finset.prod_image hinj]
  rw [hstep, hreindex]
  have hsign : (∏ j ∈ Finset.range N, (-1 : ℝ) ^ (((j : ℤ) * P) / (N : ℤ))) ^ 2 = 1 := by
    rw [← Finset.prod_pow]
    refine Finset.prod_eq_one (fun j _ => ?_)
    rw [sq, ← _root_.zpow_add₀ (by norm_num : (-1 : ℝ) ≠ 0),
      show (((j : ℤ) * P) / (N : ℤ)) + (((j : ℤ) * P) / (N : ℤ))
        = (2 : ℤ) * (((j : ℤ) * P) / (N : ℤ)) from by ring,
      _root_.zpow_mul]
    norm_num
  rw [mul_pow, hsign, one_mul, cosProdQuarterSq N hN]

theorem sq_prod_dz
    (hCos : ∀ (N : ℕ), 1 ≤ N → ∀ (P : ℤ), Nat.Coprime P.natAbs N →
      (∏ j ∈ Finset.range N, Real.cos (Real.pi * (4 * (j : ℝ) * (P : ℝ) + 1) / (4 * (N : ℝ)))) ^ 2
        = 2 / (4 : ℝ) ^ N)
    (p : ℤ) (q : ℕ) (lam : ℝ) (N : ℕ) (hN : 1 ≤ N) (hq : q = 2 * N)
    (hpq : Nat.Coprime p.natAbs q) :
    (∏ j ∈ Finset.range N, dz p q lam j) ^ 2 = ((2 * lam ^ (2 * N) : ℝ) : ℂ) := by
  have hpn : Nat.Coprime p.natAbs N := hpq.coprime_dvd_right ⟨2, by omega⟩
  set P : ℝ := ∏ j ∈ Finset.range N,
    Real.cos (Real.pi * (4 * (j : ℝ) * (p : ℝ) + 1) / (4 * (N : ℝ))) with hP
  have hP2 : P ^ 2 = 2 / (4 : ℝ) ^ N := hCos N hN p hpn
  have hprod : (∏ j ∈ Finset.range N, dz p q lam j)
      = ((-1 : ℂ) ^ N) * ((((2 * lam : ℝ) ^ N) * P : ℝ) : ℂ) := by
    have h1 : (∏ j ∈ Finset.range N, dz p q lam j)
        = (∏ j ∈ Finset.range N,
            -(((2 * lam * Real.cos (Real.pi * (4 * (j : ℝ) * (p : ℝ) + 1) / (4 * (N : ℝ)))) : ℝ) : ℂ)) :=
      Finset.prod_congr rfl (fun j _ => dz_eq_cos p q lam N hN hq j)
    rw [h1, Finset.prod_neg, Finset.card_range]
    congr 1
    change (∏ x ∈ Finset.range N,
        Complex.ofRealHom (2 * lam * Real.cos (Real.pi * (4 * (x : ℝ) * (p : ℝ) + 1) / (4 * (N : ℝ)))))
      = Complex.ofRealHom (((2 * lam : ℝ) ^ N) * P)
    rw [← map_prod Complex.ofRealHom, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_range, ← hP]
  have hsq : ((((2 * lam : ℝ) ^ N) * P) ^ 2) = 2 * lam ^ (2 * N) := by
    rw [mul_pow, ← pow_mul, hP2]
    have h4 : (4 : ℝ) ^ N = (2 : ℝ) ^ (2 * N) := by rw [pow_mul]; norm_num
    rw [h4, show N * 2 = 2 * N by ring, mul_pow]
    have hne : ((2 : ℝ) ^ (2 * N)) ≠ 0 := pow_ne_zero _ (by norm_num)
    field_simp
  calc (∏ j ∈ Finset.range N, dz p q lam j) ^ 2
      = (((-1 : ℂ) ^ N) ^ 2) * (((((2 * lam : ℝ) ^ N) * P : ℝ) : ℂ) ^ 2) := by
        rw [hprod, mul_pow]
    _ = (((((2 * lam : ℝ) ^ N) * P) ^ 2 : ℝ) : ℂ) := by
        rw [show ((-1 : ℂ) ^ N) ^ 2 = 1 by
          rw [← pow_mul]
          exact Even.neg_one_pow (⟨N, by ring⟩ : Even (N * 2)), one_mul]
        exact (map_pow Complex.ofRealHom (((2 * lam : ℝ) ^ N) * P) 2).symm
    _ = ((2 * lam ^ (2 * N) : ℝ) : ℂ) := by rw [hsq]

/-! ## 9. The discriminant at `0` and the main statement -/

theorem discZeroAbsEven (p : ℤ) (q m : ℕ) (hm : q = 2*m+2) (hpq : Nat.Coprime p.natAbs q)
    (lam : ℝ) (hlam : 0 < lam) :
    ‖(disc p q lam).eval (0 : ℂ)‖ = 2 + 2 * lam^q := by
  have hq1 : 1 ≤ q := by omega
  have hq2 : Even q := ⟨m + 1, by omega⟩
  have hpodd : Odd p := odd_of_coprime_even hpq hq2
  have hN : 1 ≤ m + 1 := by omega
  have hqN : q = 2 * (m + 1) := by omega
  have hident := half_ident
    (fun N hN a u ζ hu hζ => halfProductTraceGenAux N hN a u ζ hu hζ) p q lam (m+1) hN hqN hpq
  have hsq := sq_prod_dz
    (fun N hN P hP => cosProdGen N hN P hP) p q lam (m+1) hN hqN hpq
  have hanti : ∀ j : ℤ, S2 (dz p q lam (j + ((m+1 : ℕ) : ℤ)))
      = -sz * S2 (dz p q lam j) * sz := by
    intro j
    have h := sz_mul_S2 (dz p q lam j)
    rw [dz_add p q lam (m+1) hN hqN hpodd j]
    have hb : S2 (-(dz p q lam j)) = -(sz * S2 (dz p q lam j) * sz) := by
      rw [h]; simp
    rw [hb, neg_mul, neg_mul]
  have hhalf := bprod_half_trace (fun j : ℤ => S2 (dz p q lam j)) (m+1) hanti
    (fun j => S2_det _)
  have hident' : (bprod (Sz p q lam) 0 (m + 1) * sz).trace
      = ∏ j ∈ Finset.range (m+1), dz p q lam j := hident
  have hhalf' : (bprod (Sz p q lam) 0 (2 * (m + 1))).trace
      = (-1 : ℂ) ^ (m + 1)
        * (((bprod (Sz p q lam) 0 (m + 1) * sz).trace) ^ 2 + 2) := hhalf
  have hidx : (bprod (Sz p q lam) 0 q).trace
      = (bprod (Sz p q lam) 0 (2 * (m + 1))).trace :=
    congrArg (fun n : ℕ => (bprod (Sz p q lam) 0 n).trace) hqN
  have hval : (disc p q lam).eval 0
      = (((-1 : ℝ) ^ (m + 1) * (2 + 2 * lam ^ q) : ℝ) : ℂ) := by
    rw [disc_eval_zero_eq p q lam hq1, hidx, hhalf', hident', hsq]
    rw [show (2 * lam ^ (2 * (m + 1)) : ℝ) = 2 * lam ^ q by rw [hqN]]
    push_cast
    ring
  rw [hval, show ‖(((((-1 : ℝ) ^ (m + 1)) * (2 + 2 * lam ^ q) : ℝ)) : ℂ)‖
      = |((-1 : ℝ) ^ (m + 1)) * (2 + 2 * lam ^ q)| from RCLike.norm_ofReal _,
    abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 + 2 * lam ^ q)]
  simp

end Work.TMC14Core
