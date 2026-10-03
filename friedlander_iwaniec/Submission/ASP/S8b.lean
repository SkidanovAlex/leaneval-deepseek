/-
  Companion paper ("Asymptotic sieve for primes"), §8 (`S₃`), part (8.1).

  This file proves the estimate `(8.1)` for the `λ⁻`-contribution to `S₃`, i.e.

      `|S₃⁻(x;y,z)| ≤ J·E·log C`   (for `sz = 2^J z`),

  from the `(B′)`-type hypothesis `RhoWindow`, which is the `ρ(n;t)`-weighted form of the
  bilinear axiom (B′): for every truncation level `s ∈ [1,C]` and every dyadic window `(t,2t]`,

      `∑_{ℓ ≤ N} w(ℓ)·|∑_{t < n ≤ 2t, ℓn ≤ N} ρ(n;s)·μ(ℓn)·a(ℓn)| ≤ E`.

  The estimate is the companion's (8.1); it is obtained by
  * merging the `(b,e)`-pair of `S₃⁻` into `ℓ = be` (an exact reindexing),
  * replacing `λ⁻(c)` by its integral representation `∫_1^C ρ(c;t)/t dt` (proved in `S8`),
  * inserting the squarefree-support identity `μ(c)·a(ℓc) = μ(ℓ)·μ(ℓc)·a(ℓc)`,
  * splitting the `c`-range `(z, sz]` into `J` dyadic windows and applying `RhoWindow` to each,
  * integrating `∫_1^C dt/t = log C`.
-/
import Mathlib
import Submission.ASP.S8
import Submission.ASP.S7c

namespace Submission.ASP

open Finset MeasureTheory
open scoped Interval

noncomputable section

/-! ### The `ρ`-weighted bilinear sum and its window hypothesis -/

/-- The §8 bilinear sum: for a modulus `ℓ` and a truncation level `s`,
`Xrho a N ℓ s t u = ∑_{t < n ≤ u, ℓn ≤ N} μ(n)·ρ(n;s)·μ(ℓn)·a(ℓn)` — the companion's (B2)
coefficient `ρ(n;C)` with `C = s`, multiplied by the Möbius function as in the main paper's
(5.13) (`γ(n) = μ(n)∑_{d|n,d≤C}μ(d)`). -/
def Xrho (a : ℕ → ℝ) (N m : ℕ) (s t u : ℝ) : ℝ :=
  ∑ n ∈ (Finset.Icc 1 N).filter (fun n => m * n ≤ N),
    (if t < ((n : ℕ) : ℝ) ∧ ((n : ℕ) : ℝ) ≤ u
      then (ArithmeticFunction.moebius n : ℝ) * rhoTrunc n s
        * (ArithmeticFunction.moebius (m * n) : ℝ) * a (m * n) else 0)

/-- The `(B′)`-type hypothesis of §8: the `ρ`-weighted bilinear form is bounded by `E` on every
dyadic window `(t,2t]` with `t ∈ [lo,hi]`, uniformly in the truncation level `s ∈ [1,C]`. -/
def RhoWindow (a : ℕ → ℝ) (N : ℕ) (w : ℕ → ℝ) (E C lo hi : ℝ) : Prop :=
  ∀ s t : ℝ, 1 ≤ s → s ≤ C → lo ≤ t → t ≤ hi →
    (∑ m ∈ Finset.Icc 1 N, w m * |Xrho a N m s t (2 * t)|) ≤ E

/-- `Xrho` in "filtered" form (the `range`-condition pushed into the index set). -/
lemma Xrho_eq_sum_filter (a : ℕ → ℝ) (N m : ℕ) (s t u : ℝ) :
    Xrho a N m s t u
      = ∑ n ∈ (Finset.Icc 1 N).filter
          (fun n => t < ((n : ℕ) : ℝ) ∧ ((n : ℕ) : ℝ) ≤ u ∧ m * n ≤ N),
          (ArithmeticFunction.moebius n : ℝ) * rhoTrunc n s
            * (ArithmeticFunction.moebius (m * n) : ℝ) * a (m * n) := by
  rw [Xrho, Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  by_cases hN : m * n ≤ N <;> by_cases h1 : t < ((n : ℕ) : ℝ) ∧ ((n : ℕ) : ℝ) ≤ u <;>
    simp [hN, h1, and_comm]

/-- `Xrho` is additive over adjacent windows. -/
lemma Xrho_add_adjacent (a : ℕ → ℝ) (N m : ℕ) (s : ℝ) {t v w : ℝ} (htv : t ≤ v) (hvw : v ≤ w) :
    Xrho a N m s t w = Xrho a N m s t v + Xrho a N m s v w := by
  rw [Xrho, Xrho, Xrho, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rcases le_or_gt (((n : ℕ) : ℝ)) t with h1 | h1
  · have h2 : ¬ (t < ((n : ℕ) : ℝ)) := not_lt.mpr h1
    have h3 : ¬ (v < ((n : ℕ) : ℝ)) := not_lt.mpr (le_trans h1 htv)
    simp [h2, h3]
  · rcases le_or_gt (((n : ℕ) : ℝ)) v with h2 | h2
    · have h3 : ¬ (v < ((n : ℕ) : ℝ)) := not_lt.mpr h2
      have h4 : ((n : ℕ) : ℝ) ≤ w := le_trans h2 hvw
      simp [h1, h2, h3, h4]
    · have h3 : ¬ (((n : ℕ) : ℝ) ≤ v) := not_le.mpr h2
      by_cases h4 : ((n : ℕ) : ℝ) ≤ w
      · simp [h1, h2, h3, h4]
      · have h5 : ¬ (((n : ℕ) : ℝ) ≤ w) := h4
        simp [h1, h2, h3, h5]

/-- The dyadic splitting of the `Xrho` window (the intervals `(2^j u, 2^{j+1} u]`, `j < J`,
partition `(u, 2^J u]`). -/
lemma Xrho_dyadic (a : ℕ → ℝ) (N m : ℕ) (s : ℝ) {u : ℝ} (hu : 0 < u) (J : ℕ) :
    Xrho a N m s u ((2 : ℝ) ^ J * u)
      = ∑ j ∈ Finset.range J, Xrho a N m s ((2 : ℝ) ^ j * u) ((2 : ℝ) ^ (j + 1) * u) := by
  induction J with
  | zero =>
      rw [Xrho, pow_zero, one_mul]
      refine Finset.sum_eq_zero (fun n _ => ?_)
      have hne : ¬ (u < ((n : ℕ) : ℝ) ∧ ((n : ℕ) : ℝ) ≤ u) :=
        fun h => absurd h.2 (not_le.mpr h.1)
      simp only [hne, if_false]
  | succ J ih =>
      have hle : u ≤ (2 : ℝ) ^ J * u := by
        have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ J := one_le_pow₀ (by norm_num)
        nlinarith
      have hle2 : (2 : ℝ) ^ J * u ≤ (2 : ℝ) ^ (J + 1) * u := by
        have h2 : (2 : ℝ) ^ J ≤ (2 : ℝ) ^ (J + 1) := by
          calc (2 : ℝ) ^ J = (2 : ℝ) ^ J * 1 := (mul_one _).symm
            _ ≤ (2 : ℝ) ^ J * 2 := by nlinarith [(show (1:ℝ) ≤ 2 by norm_num)]
            _ = (2 : ℝ) ^ (J + 1) := by ring
        nlinarith
      rw [Finset.sum_range_succ, ← ih, Xrho_add_adjacent (a := a) (N := N) (m := m) (s := s)
        (t := u) (v := (2 : ℝ) ^ J * u) (w := (2 : ℝ) ^ (J + 1) * u) hle hle2]

/-! ### The merge of `(b,e)` into `ℓ = b·e` in `S₃⁻` -/

/-- **§8, the merge**: for fixed `c ≥ 1` the `(b,e)`-sum of `S₃⁻` is an exact reindexing along
`ℓ = b·e`. -/
lemma sum_merge_be (a lam : ℕ → ℝ) (N : ℕ) (sy : ℝ) {c : ℕ} (hc : 1 ≤ c) :
    (∑ b ∈ (Finset.Icc 1 N).filter (fun b => sy < ((b : ℕ) : ℝ)),
        (ArithmeticFunction.moebius b : ℝ) *
          ∑ e ∈ (Finset.Icc 1 N).filter (fun e => b * (c * e) ≤ N),
            a (b * (c * e)) * rhoOf lam (b * e))
      = ∑ ℓ ∈ Finset.Icc 1 N,
          (∑ b ∈ ℓ.divisors.filter (fun b => sy < ((b : ℕ) : ℝ)),
              (ArithmeticFunction.moebius b : ℝ))
            * rhoOf lam ℓ * (if ℓ * c ≤ N then a (ℓ * c) else 0) := by
  classical
  set B : Finset ℕ := (Finset.Icc 1 N).filter (fun b => sy < ((b : ℕ) : ℝ)) with hB
  set G : ℕ → ℕ → ℝ := fun b e =>
    (ArithmeticFunction.moebius b : ℝ) * (a (b * (c * e)) * rhoOf lam (b * e)) with hG
  set s : Finset (ℕ × ℕ) := (B ×ˢ Finset.Icc 1 N).filter (fun p => p.1 * (c * p.2) ≤ N) with hs
  -- **Step 1**: the double sum is a sum over `s`.
  have step1 : (∑ b ∈ B, (ArithmeticFunction.moebius b : ℝ) *
        ∑ e ∈ (Finset.Icc 1 N).filter (fun e => b * (c * e) ≤ N),
          a (b * (c * e)) * rhoOf lam (b * e))
      = ∑ p ∈ s, G p.1 p.2 := by
    have hA : (∑ p ∈ s, G p.1 p.2)
        = ∑ b ∈ B, ∑ e ∈ Finset.Icc 1 N,
            (if b * (c * e) ≤ N then G b e else 0) := by
      rw [hs, Finset.sum_filter, Finset.sum_product]
    rw [hA]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    simp only [Finset.mul_sum, Finset.sum_filter, G]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    by_cases h : b * (c * e) ≤ N <;> simp [h]
  -- **Step 2**: fiberwise over `ℓ = p.1 * p.2`.
  have hmaps : ∀ p ∈ s, p.1 * p.2 ∈ Finset.Icc 1 N := by
    intro p hp
    rw [hs] at hp
    obtain ⟨hpm, hcond⟩ := Finset.mem_filter.mp hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hpm
    have hb1 : 1 ≤ p.1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp1).1).1
    have hb2 : 1 ≤ p.2 := (Finset.mem_Icc.mp hp2).1
    refine Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)), ?_⟩
    calc p.1 * p.2 ≤ p.1 * (c * p.2) := by
          refine Nat.mul_le_mul_left _ ?_
          calc p.2 = 1 * p.2 := (one_mul _).symm
            _ ≤ c * p.2 := Nat.mul_le_mul_right _ hc
      _ ≤ N := hcond
  have step2 : (∑ p ∈ s, G p.1 p.2)
      = ∑ ℓ ∈ Finset.Icc 1 N,
          ∑ p ∈ s.filter (fun p => p.1 * p.2 = ℓ), G p.1 p.2 :=
    (Finset.sum_fiberwise_of_maps_to hmaps (fun p => G p.1 p.2)).symm
  -- **Step 3**: each fibre is the divisor sum of the claim.
  have step3 : ∀ ℓ ∈ Finset.Icc 1 N,
      (∑ p ∈ s.filter (fun p => p.1 * p.2 = ℓ), G p.1 p.2)
        = (∑ b ∈ ℓ.divisors.filter (fun b => sy < ((b : ℕ) : ℝ)),
              (ArithmeticFunction.moebius b : ℝ))
            * rhoOf lam ℓ * (if ℓ * c ≤ N then a (ℓ * c) else 0) := by
    intro ℓ hℓ
    have hℓ1 : 1 ≤ ℓ := (Finset.mem_Icc.mp hℓ).1
    have hℓN : ℓ ≤ N := (Finset.mem_Icc.mp hℓ).2
    have hℓ0 : ℓ ≠ 0 := by omega
    by_cases hcN : ℓ * c ≤ N
    · -- the bijection `p ↦ p.1` onto `ℓ.divisors.filter (sy < ·)`
      rw [if_pos hcN]
      rw [Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_bij (s := s.filter (fun p : ℕ × ℕ => p.1 * p.2 = ℓ))
        (t := ℓ.divisors.filter (fun b => sy < ((b : ℕ) : ℝ)))
        (f := fun p : ℕ × ℕ => G p.1 p.2)
        (g := fun b : ℕ => (ArithmeticFunction.moebius b : ℝ) * rhoOf lam ℓ * a (ℓ * c))
        (fun (p : ℕ × ℕ) _ => p.1) ?_ ?_ ?_ ?_
      · intro p hp
        obtain ⟨hps, heq⟩ := Finset.mem_filter.mp hp
        rw [hs] at hps
        obtain ⟨hpm, -⟩ := Finset.mem_filter.mp hps
        obtain ⟨hp1, -⟩ := Finset.mem_product.mp hpm
        exact Finset.mem_filter.mpr
          ⟨Nat.mem_divisors.mpr ⟨⟨p.2, heq.symm⟩, hℓ0⟩, (Finset.mem_filter.mp hp1).2⟩
      · intro p hp q hq hpq
        obtain ⟨hps, heq⟩ := Finset.mem_filter.mp hp
        obtain ⟨hqs, heq'⟩ := Finset.mem_filter.mp hq
        rw [hs] at hqs
        obtain ⟨hqm, -⟩ := Finset.mem_filter.mp hqs
        have hq1 : q.1 ≠ 0 := by
          have hh := (Finset.mem_Icc.mp (Finset.mem_filter.mp
            (Finset.mem_product.mp hqm).1).1).1
          omega
        have h2 : p.2 = q.2 := by
          refine Nat.mul_left_cancel (Nat.pos_of_ne_zero hq1) ?_
          calc q.1 * p.2 = p.1 * p.2 := by rw [hpq]
            _ = q.1 * q.2 := by rw [heq, ← heq']
        exact Prod.ext hpq h2
      · intro b hb
        obtain ⟨hbdvd, hsy⟩ := Finset.mem_filter.mp hb
        obtain ⟨hdvdvd, hℓne⟩ := Nat.mem_divisors.mp hbdvd
        have hbpos : 1 ≤ b := Nat.pos_of_dvd_of_pos hdvdvd (Nat.pos_of_ne_zero hℓne)
        have hble : b ≤ ℓ := Nat.le_of_dvd (Nat.pos_of_ne_zero hℓne) hdvdvd
        have hdivpos : 1 ≤ ℓ / b := (Nat.one_le_div_iff (by omega)).mpr hble
        have hdivle : ℓ / b ≤ N := le_trans (Nat.div_le_self _ _) hℓN
        refine ⟨(b, ℓ / b), ?_, ?_⟩
        · refine Finset.mem_filter.mpr ⟨?_, ?_⟩
          · rw [hs]
            refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
            · exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hbpos, le_trans hble hℓN⟩, hsy⟩
            · exact Finset.mem_Icc.mpr ⟨hdivpos, hdivle⟩
            · have hmul : b * (c * (ℓ / b)) = c * ℓ := by
                rw [show b * (c * (ℓ / b)) = c * (b * (ℓ / b)) by ring,
                  Nat.mul_div_cancel' hdvdvd]
              rw [hmul, mul_comm]; exact hcN
          · exact Nat.mul_div_cancel' hdvdvd
        · rfl
      · intro p hp
        obtain ⟨hps, heq⟩ := Finset.mem_filter.mp hp
        simp only [hG]
        rw [show p.1 * p.2 = ℓ from heq,
          show p.1 * (c * p.2) = ℓ * c by rw [← heq]; ring]
        ring
    · -- the fibre is empty
      rw [if_neg hcN]
      have hempty : s.filter (fun p : ℕ × ℕ => p.1 * p.2 = ℓ) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro p hp
        obtain ⟨hps, heq⟩ := Finset.mem_filter.mp hp
        rw [hs] at hps
        obtain ⟨-, hcond⟩ := Finset.mem_filter.mp hps
        have hle : c * ℓ ≤ N := by
          have hc1 : p.1 * (c * p.2) = c * (p.1 * p.2) := by ring
          rw [hc1, heq] at hcond
          exact hcond
        exact hcN (by rwa [mul_comm] at hle)
      rw [hempty, Finset.sum_empty, mul_zero]
  rw [step1, step2]
  exact Finset.sum_congr rfl (fun ℓ hℓ => step3 ℓ hℓ)

/-- **§8, the reindexed form of `S₃⁻`**: the `(b,e)`-pair is merged into `ℓ = b·e`. -/
theorem S3minus_eq_reindex (a lam : ℕ → ℝ) (N : ℕ) (z sy sz C : ℝ) :
    S3minus a lam N z sy sz C
      = ∑ ℓ ∈ Finset.Icc 1 N,
          (∑ b ∈ ℓ.divisors.filter (fun b => sy < ((b : ℕ) : ℝ)),
              (ArithmeticFunction.moebius b : ℝ))
            * rhoOf lam ℓ
            * ∑ c ∈ (Finset.Icc 1 N).filter
                (fun c => z < ((c : ℕ) : ℝ) ∧ ((c : ℕ) : ℝ) ≤ sz ∧ ℓ * c ≤ N),
                lamMinus c C * a (ℓ * c) := by
  classical
  set Cf : Finset ℕ := (Finset.Icc 1 N).filter
    (fun c => z < ((c : ℕ) : ℝ) ∧ ((c : ℕ) : ℝ) ≤ sz) with hCf
  -- **Step A**: swap the `b`- and `c`-sums.
  have hA : S3minus a lam N z sy sz C
      = ∑ c ∈ Cf, lamMinus c C *
          ∑ b ∈ (Finset.Icc 1 N).filter (fun b => sy < ((b : ℕ) : ℝ)),
            (ArithmeticFunction.moebius b : ℝ) *
              ∑ e ∈ (Finset.Icc 1 N).filter (fun e => b * (c * e) ≤ N),
                a (b * (c * e)) * rhoOf lam (b * e) := by
    unfold S3minus
    rw [hCf]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    refine Finset.sum_congr rfl (fun b _ => ?_)
    refine Finset.sum_congr rfl (fun e _ => ?_)
    ring
  rw [hA]
  -- **Step B**: merge `(b,e)` into `ℓ = b·e` (for each `c ∈ Cf`, so `c ≥ 1`).
  rw [Finset.sum_congr rfl (fun c hc => by
    rw [sum_merge_be a lam N sy (Finset.mem_Icc.mp (Finset.mem_filter.mp hc).1).1])]
  -- **Step C**: swap the `c`- and `ℓ`-sums and clean up.
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun ℓ _ => ?_)
  set A : ℝ := (∑ b ∈ ℓ.divisors.filter (fun b => sy < ((b : ℕ) : ℝ)),
      (ArithmeticFunction.moebius b : ℝ)) * rhoOf lam ℓ with hAdef
  have hset : Cf.filter (fun c => ℓ * c ≤ N)
      = (Finset.Icc 1 N).filter
          (fun c => z < ((c : ℕ) : ℝ) ∧ ((c : ℕ) : ℝ) ≤ sz ∧ ℓ * c ≤ N) := by
    rw [hCf, Finset.filter_filter]
    refine Finset.filter_congr (fun c _ => ?_)
    tauto
  have hsum : (∑ c ∈ Cf, lamMinus c C * (A * (if ℓ * c ≤ N then a (ℓ * c) else 0)))
      = ∑ c ∈ Cf.filter (fun c => ℓ * c ≤ N), lamMinus c C * (A * a (ℓ * c)) := by
    simp only [mul_ite, mul_zero]
    rw [← Finset.sum_filter]
  rw [hsum, hset]
  refine Finset.sum_congr rfl (fun c _ => by ring)

/-! ### The squarefree-support identities for `a` -/

/-- `μ(n)^2 = 1` for squarefree `n` (as a real number). -/
lemma moebius_cast_sq_eq_one {n : ℕ} (hn : Squarefree n) :
    ((ArithmeticFunction.moebius n : ℝ)) ^ 2 = 1 := by
  have h := ArithmeticFunction.moebius_sq (n := n)
  have h' : ((ArithmeticFunction.moebius n ^ 2 : ℤ) : ℝ) = 1 := by
    rw [h, if_pos hn]; norm_num
  simpa using h'


/-- The triple Möbius product is `1` exactly on squarefree products. -/
lemma moebius_triple_mul_eq_ite (m n : ℕ) :
    ((ArithmeticFunction.moebius m : ℝ) * (ArithmeticFunction.moebius n : ℝ)
      * (ArithmeticFunction.moebius (m * n) : ℝ)) = if Squarefree (m * n) then 1 else 0 := by
  by_cases hs : Squarefree (m * n)
  · rw [if_pos hs]
    obtain ⟨hcop, hm, hn⟩ := Nat.squarefree_mul_iff.mp hs
    have hmul : (ArithmeticFunction.moebius (m * n) : ℝ)
        = (ArithmeticFunction.moebius m : ℝ) * (ArithmeticFunction.moebius n : ℝ) := by
      have h := ArithmeticFunction.IsMultiplicative.map_mul_of_coprime
        (f := ArithmeticFunction.moebius) ArithmeticFunction.isMultiplicative_moebius
        (show Nat.gcd m n = 1 from hcop)
      exact_mod_cast h
    have h1 := moebius_cast_sq_eq_one hm
    have h2 := moebius_cast_sq_eq_one hn
    rw [hmul]
    calc (ArithmeticFunction.moebius m : ℝ) * (ArithmeticFunction.moebius n : ℝ)
          * ((ArithmeticFunction.moebius m : ℝ) * (ArithmeticFunction.moebius n : ℝ))
        = ((ArithmeticFunction.moebius m : ℝ)) ^ 2
            * ((ArithmeticFunction.moebius n : ℝ)) ^ 2 := by ring
      _ = 1 := by rw [h1, h2, one_mul]
  · rw [if_neg hs]
    have hz : (ArithmeticFunction.moebius (m * n) : ℝ) = 0 := by
      rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs]; norm_num
    rw [hz, mul_zero]

/-- On the squarefree support of `a`, `a(ℓc) = μ(ℓ)μ(c)μ(ℓc)a(ℓc)`. -/
lemma a_eq_moebius_triple_mul_a {a : ℕ → ℝ} (ha : ∀ n, ¬ Squarefree n → a n = 0)
    (m n : ℕ) :
    a (m * n) = (ArithmeticFunction.moebius m : ℝ) * (ArithmeticFunction.moebius n : ℝ)
      * (ArithmeticFunction.moebius (m * n) : ℝ) * a (m * n) := by
  rw [moebius_triple_mul_eq_ite]
  by_cases hs : Squarefree (m * n)
  · rw [if_pos hs, one_mul]
  · rw [if_neg hs, zero_mul, ha _ hs]

/-- On the squarefree support of `a`, `μ(c)·a(ℓc) = μ(ℓ)·μ(ℓc)·a(ℓc)`. -/
lemma moebius_mul_a_mul_eq {a : ℕ → ℝ} (ha : ∀ n, ¬ Squarefree n → a n = 0)
    (ℓ c : ℕ) :
    (ArithmeticFunction.moebius c : ℝ) * a (ℓ * c)
      = (ArithmeticFunction.moebius ℓ : ℝ) * (ArithmeticFunction.moebius (ℓ * c) : ℝ)
        * a (ℓ * c) := by
  by_cases hs : Squarefree (ℓ * c)
  · obtain ⟨hcop, hℓ, hc⟩ := Nat.squarefree_mul_iff.mp hs
    have hsq : (ArithmeticFunction.moebius ℓ : ℝ) * (ArithmeticFunction.moebius ℓ : ℝ) = 1 := by
      rw [← sq]; exact moebius_cast_sq_eq_one hℓ
    have hmul : (ArithmeticFunction.moebius (ℓ * c) : ℝ)
        = (ArithmeticFunction.moebius ℓ : ℝ) * (ArithmeticFunction.moebius c : ℝ) := by
      have h := ArithmeticFunction.IsMultiplicative.map_mul_of_coprime
        (f := ArithmeticFunction.moebius) ArithmeticFunction.isMultiplicative_moebius
        (show Nat.gcd ℓ c = 1 from hcop)
      exact_mod_cast h
    have hkey : (ArithmeticFunction.moebius ℓ : ℝ) * ((ArithmeticFunction.moebius ℓ : ℝ)
          * (ArithmeticFunction.moebius c : ℝ)) * a (ℓ * c)
        = (ArithmeticFunction.moebius c : ℝ) * a (ℓ * c) := by
      rw [← mul_assoc, hsq, one_mul]
    rw [hmul, hkey]
  · simp [ha _ hs]

/-! ### Measurability and boundedness of the truncated Möbius sum -/

/-- `s ↦ ρ(n;s)` is measurable (a finite sum of step functions). -/
lemma measurable_rhoTrunc (n : ℕ) : Measurable (fun s : ℝ => rhoTrunc n s) := by
  have h : (fun s : ℝ => rhoTrunc n s)
      = fun s => ∑ d ∈ n.divisors,
          ((Set.Ici ((d : ℕ) : ℝ)).indicator (fun _ => (ArithmeticFunction.moebius d : ℝ))) s := by
    funext s
    rw [rhoTrunc, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [Set.indicator_apply]
    by_cases hd : ((d : ℕ) : ℝ) ≤ s
    · rw [if_pos hd, if_pos (Set.mem_Ici.mpr hd)]
    · rw [if_neg hd, if_neg (fun h => hd (Set.mem_Ici.mp h))]
  rw [h]
  exact Finset.measurable_sum _ (fun d _ => measurable_const.indicator measurableSet_Ici)

/-- `|ρ(n;s)| ≤ τ(n)`. -/
lemma abs_rhoTrunc_le (n : ℕ) (s : ℝ) : |rhoTrunc n s| ≤ (n.divisors.card : ℝ) := by
  rw [rhoTrunc]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ d ∈ n.divisors.filter (fun d => ((d : ℕ) : ℝ) ≤ s),
        |(ArithmeticFunction.moebius d : ℝ)|
      ≤ ∑ _d ∈ n.divisors.filter (fun d => ((d : ℕ) : ℝ) ≤ s), (1 : ℝ) :=
        Finset.sum_le_sum (fun d _ => by
          have := ArithmeticFunction.abs_moebius_le_one (n := d)
          exact_mod_cast this)
    _ = ((n.divisors.filter (fun d => ((d : ℕ) : ℝ) ≤ s)).card : ℝ) := by simp
    _ ≤ (n.divisors.card : ℝ) := by exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)

/-- `s ↦ ρ(n;s)/s` is interval-integrable on `[1,C]` for `C ≥ 1`. -/
lemma intervalIntegrable_rhoTrunc_div (n : ℕ) {C : ℝ} (hC : 1 ≤ C) :
    IntervalIntegrable (fun s : ℝ => rhoTrunc n s / s) volume (1 : ℝ) C := by
  refine intervalIntegrable_div_Ioc (measurable_rhoTrunc n) (by norm_num) hC
    (n.divisors.card : ℝ) (fun s _ => abs_rhoTrunc_le n s)

/-! ### The integral bound for the inner `c`-sum -/

/-- Measurability of `s ↦ Xrho a N ℓ s t u`. -/
lemma measurable_Xrho (a : ℕ → ℝ) (N ℓ : ℕ) (t u : ℝ) :
    Measurable (fun s : ℝ => Xrho a N ℓ s t u) := by
  have h : (fun s : ℝ => Xrho a N ℓ s t u)
      = fun s => ∑ n ∈ (Finset.Icc 1 N).filter (fun n => ℓ * n ≤ N),
          (if t < ((n : ℕ) : ℝ) ∧ ((n : ℕ) : ℝ) ≤ u
            then (ArithmeticFunction.moebius n : ℝ) * rhoTrunc n s
              * (ArithmeticFunction.moebius (ℓ * n) : ℝ) * a (ℓ * n) else 0) := by
    funext s; rw [Xrho]
  rw [h]
  refine Finset.measurable_sum _ (fun n _ => ?_)
  by_cases hc : t < ((n : ℕ) : ℝ) ∧ ((n : ℕ) : ℝ) ≤ u
  · simp only [if_pos hc]
    have heq : (fun s : ℝ => (ArithmeticFunction.moebius n : ℝ) * rhoTrunc n s
          * (ArithmeticFunction.moebius (ℓ * n) : ℝ) * a (ℓ * n))
        = fun s : ℝ => ((ArithmeticFunction.moebius n : ℝ)
            * (ArithmeticFunction.moebius (ℓ * n) : ℝ) * a (ℓ * n)) * rhoTrunc n s := by
      funext s; ring
    rw [heq]
    exact measurable_const.mul (measurable_rhoTrunc n)
  · simp only [if_neg hc]; exact measurable_const

/-- `|Xrho|` is bounded by the `τ`-weighted sum of `|a|`. -/
lemma abs_Xrho_le (a : ℕ → ℝ) (N ℓ : ℕ) (s t u : ℝ) :
    |Xrho a N ℓ s t u|
      ≤ ∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) * |a (ℓ * n)| := by
  rw [Xrho]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum (fun n _ => ?_)).trans
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun n _ _ => mul_nonneg (by positivity) (abs_nonneg _)))
  by_cases hc : t < ((n : ℕ) : ℝ) ∧ ((n : ℕ) : ℝ) ≤ u
  · rw [if_pos hc, abs_mul, abs_mul, abs_mul]
    calc |(ArithmeticFunction.moebius n : ℝ)| * |rhoTrunc n s|
          * |(ArithmeticFunction.moebius (ℓ * n) : ℝ)| * |a (ℓ * n)|
        ≤ 1 * (n.divisors.card : ℝ) * 1 * |a (ℓ * n)| := by
          gcongr
          · exact abs_moebius_cast_le_one n
          · exact abs_rhoTrunc_le n s
          · exact abs_moebius_cast_le_one (ℓ * n)
      _ = (n.divisors.card : ℝ) * |a (ℓ * n)| := by ring
  · rw [if_neg hc, abs_zero]; positivity

/-- Measurability of the `ρ`-weighted `c`-sum. -/
lemma measurable_rhoCsum (a : ℕ → ℝ) (Ch : Finset ℕ) (ℓ : ℕ) :
    Measurable (fun s : ℝ => ∑ c ∈ Ch, rhoTrunc c s * a (ℓ * c)) :=
  Finset.measurable_sum _ (fun c _ => (measurable_rhoTrunc c).mul_const _)

/-- **§8, the integral representation of the inner `c`-sum**: the absolute value of the
`λ⁻`-weighted `c`-sum is bounded by the integral of `|Xrho|`. -/
lemma abs_Csum_le_integral (a : ℕ → ℝ) (N ℓ : ℕ) (z sz C : ℝ) (hC : 1 ≤ C)
    (ha : ∀ n, ¬ Squarefree n → a n = 0) :
    |∑ c ∈ (Finset.Icc 1 N).filter
        (fun c => z < ((c : ℕ) : ℝ) ∧ ((c : ℕ) : ℝ) ≤ sz ∧ ℓ * c ≤ N),
        lamMinus c C * a (ℓ * c)|
      ≤ ∫ s in (1 : ℝ)..C, |Xrho a N ℓ s z sz| / s := by
  classical
  set Ch : Finset ℕ := (Finset.Icc 1 N).filter
    (fun c => z < ((c : ℕ) : ℝ) ∧ ((c : ℕ) : ℝ) ≤ sz ∧ ℓ * c ≤ N) with hCh
  -- the sum is the integral of the `ρ`-weighted sum, divided by `s`
  have hInt : (∑ c ∈ Ch, lamMinus c C * a (ℓ * c))
      = ∫ s in (1 : ℝ)..C, (∑ c ∈ Ch, rhoTrunc c s * a (ℓ * c)) / s := by
    have hstep : (∑ c ∈ Ch, lamMinus c C * a (ℓ * c))
        = ∑ c ∈ Ch, ∫ s in (1 : ℝ)..C, rhoTrunc c s / s * a (ℓ * c) := by
      refine Finset.sum_congr rfl (fun c _ => ?_)
      rw [lamMinus_eq_integral c hC, ← intervalIntegral.integral_mul_const]
    rw [hstep, ← intervalIntegral.integral_finsetSum (fun c _ =>
      (intervalIntegrable_rhoTrunc_div c hC).mul_const _)]
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall (fun s _ => ?_))
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl (fun c _ => by ring)
  -- pointwise: the `ρ`-weighted sum is `μ(ℓ)·Xrho`
  have hsum_eq : ∀ s : ℝ, (∑ c ∈ Ch, rhoTrunc c s * a (ℓ * c))
      = (ArithmeticFunction.moebius ℓ : ℝ) * Xrho a N ℓ s z sz := by
    intro s
    have hterm : ∀ c : ℕ, rhoTrunc c s * a (ℓ * c)
        = (ArithmeticFunction.moebius ℓ : ℝ)
            * ((ArithmeticFunction.moebius c : ℝ) * rhoTrunc c s
                * (ArithmeticFunction.moebius (ℓ * c) : ℝ) * a (ℓ * c)) := by
      intro c
      conv_lhs => rw [a_eq_moebius_triple_mul_a ha ℓ c]
      ring
    have hsum : (∑ c ∈ Ch, (ArithmeticFunction.moebius c : ℝ) * rhoTrunc c s
        * (ArithmeticFunction.moebius (ℓ * c) : ℝ) * a (ℓ * c)) = Xrho a N ℓ s z sz := by
      rw [Xrho_eq_sum_filter, hCh]
    rw [Finset.sum_congr rfl (fun c _ => hterm c), ← Finset.mul_sum, hsum]
  rw [hInt]
  refine le_trans (intervalIntegral.abs_integral_le_integral_abs hC) ?_
  refine intervalIntegral.integral_mono_ae_restrict hC ?_ ?_ ?_
  · -- integrability of the left-hand side
    refine (intervalIntegrable_div_Ioc (measurable_rhoCsum a Ch ℓ) (by norm_num) hC
      (∑ c ∈ Ch, (c.divisors.card : ℝ) * |a (ℓ * c)|) (fun s _ => ?_)).abs
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun c _ => ?_))
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (abs_rhoTrunc_le c s) (abs_nonneg _)
  · -- integrability of the right-hand side
    refine intervalIntegrable_div_Ioc (measurable_Xrho a N ℓ z sz).abs (by norm_num) hC
      (∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) * |a (ℓ * n)|) (fun s _ => ?_)
    simpa using abs_Xrho_le a N ℓ s z sz
  · change ∀ᵐ x ∂(volume.restrict (Set.Icc (1 : ℝ) C)),
        |(∑ c ∈ Ch, rhoTrunc c x * a (ℓ * c)) / x| ≤ |Xrho a N ℓ x z sz| / x
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    refine Filter.Eventually.of_forall (fun s hs => ?_)
    have hs1 : 1 ≤ s := hs.1
    have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs1
    rw [hsum_eq s, abs_div, abs_of_pos hs0, abs_mul]
    calc |(ArithmeticFunction.moebius ℓ : ℝ)| * |Xrho a N ℓ s z sz| / s
        ≤ 1 * |Xrho a N ℓ s z sz| / s := by
          gcongr
          exact abs_moebius_cast_le_one ℓ
      _ = |Xrho a N ℓ s z sz| / s := by ring

/-! ### §8 (8.1): the `λ⁻`-contribution to `S₃` -/

/-- The dyadic-window estimate for `∑_ℓ w(ℓ)|Xrho|`, from the (B′)-hypothesis. -/
lemma sum_w_Xrho_le (a : ℕ → ℝ) (N : ℕ) (z sz C : ℝ) {w : ℕ → ℝ} {E : ℝ} {J : ℕ}
    (hz : 0 < z) (hsz : sz = (2 : ℝ) ^ J * z) (hw0 : ∀ ℓ, 0 ≤ w ℓ)
    (hwin : RhoWindow a N w E C z sz) (s : ℝ) (hs1 : 1 ≤ s) (hsC : s ≤ C) :
    (∑ ℓ ∈ Finset.Icc 1 N, w ℓ * abs (Xrho a N ℓ s z sz)) ≤ (J : ℝ) * E := by
  have hz1 : (1 : ℝ) ≤ 2 := by norm_num
  have hdyad : ∀ ℓ : ℕ, abs (Xrho a N ℓ s z sz)
      ≤ ∑ j ∈ Finset.range J, abs (Xrho a N ℓ s ((2 : ℝ) ^ j * z) ((2 : ℝ) ^ (j + 1) * z)) := by
    intro ℓ
    rw [hsz, Xrho_dyadic a N ℓ s hz J]
    exact Finset.abs_sum_le_sum_abs _ _
  calc (∑ ℓ ∈ Finset.Icc 1 N, w ℓ * abs (Xrho a N ℓ s z sz))
      ≤ ∑ ℓ ∈ Finset.Icc 1 N,
          w ℓ * ∑ j ∈ Finset.range J, abs (Xrho a N ℓ s ((2 : ℝ) ^ j * z) ((2 : ℝ) ^ (j + 1) * z)) :=
        Finset.sum_le_sum (fun ℓ _ => mul_le_mul_of_nonneg_left (hdyad ℓ) (hw0 ℓ))
    _ = ∑ j ∈ Finset.range J,
          ∑ ℓ ∈ Finset.Icc 1 N,
            w ℓ * abs (Xrho a N ℓ s ((2 : ℝ) ^ j * z) ((2 : ℝ) ^ (j + 1) * z)) := by
        rw [Finset.sum_congr rfl (fun ℓ _ => Finset.mul_sum _ _ _), Finset.sum_comm]
    _ ≤ ∑ _j ∈ Finset.range J, E := by
        refine Finset.sum_le_sum (fun j hj => ?_)
        have hlo : z ≤ (2 : ℝ) ^ j * z := by
          have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ hz1
          nlinarith
        have hhi : (2 : ℝ) ^ j * z ≤ sz := by
          have h2 : (2 : ℝ) ^ j ≤ (2 : ℝ) ^ J :=
            pow_le_pow_right₀ hz1 (Nat.le_of_lt (Finset.mem_range.mp hj))
          rw [hsz]
          nlinarith
        simpa [show (2 : ℝ) * ((2 : ℝ) ^ j * z) = (2 : ℝ) ^ (j + 1) * z by ring]
          using hwin s ((2 : ℝ) ^ j * z) hs1 hsC hlo hhi
    _ = (J : ℝ) * E := by simp [Finset.sum_const, nsmul_eq_mul]

/-- The inner `c`-sum of `S₃⁻` at a fixed `ℓ`: `∑_{z < c ≤ sz, ℓc ≤ N} λ⁻(c)·a(ℓc)`. -/
def S3minusInner (a : ℕ → ℝ) (N ℓ : ℕ) (z sz C : ℝ) : ℝ :=
  ∑ c ∈ (Finset.Icc 1 N).filter
      (fun c => z < ((c : ℕ) : ℝ) ∧ ((c : ℕ) : ℝ) ≤ sz ∧ ℓ * c ≤ N),
    lamMinus c C * a (ℓ * c)

/-- **§8 (8.1)**: the `λ⁻`-contribution to `S₃` is `≤ J·E·log C` under the (B′)-hypothesis
`RhoWindow` (with `sz = 2^J z`). -/
theorem abs_S3minus_le (a lam : ℕ → ℝ) (N : ℕ) (z sy sz C : ℝ) {w : ℕ → ℝ} {E : ℝ} {J : ℕ}
    (ha : ∀ n, ¬ Squarefree n → a n = 0)
    (hz : 0 < z) (hC : 1 ≤ C) (hsz : sz = (2 : ℝ) ^ J * z) (hw0 : ∀ ℓ, 0 ≤ w ℓ)
    (hw : ∀ ℓ : ℕ, 1 ≤ ℓ →
      abs (∑ b ∈ ℓ.divisors.filter (fun b => sy < ((b : ℕ) : ℝ)),
          (ArithmeticFunction.moebius b : ℝ)) * abs (rhoOf lam ℓ) ≤ w ℓ)
    (hwin : RhoWindow a N w E C z sz) :
    abs (S3minus a lam N z sy sz C) ≤ (J : ℝ) * E * Real.log C := by
  classical
  rw [S3minus_eq_reindex]
  -- Step 1: replace `(∑_{b|ℓ} μ b)·ρ_ℓ` by its bound `w ℓ`
  have h1 : abs (∑ ℓ ∈ Finset.Icc 1 N,
        (∑ b ∈ ℓ.divisors.filter (fun b => sy < ((b : ℕ) : ℝ)),
            (ArithmeticFunction.moebius b : ℝ)) * rhoOf lam ℓ * S3minusInner a N ℓ z sz C)
      ≤ ∑ ℓ ∈ Finset.Icc 1 N, w ℓ * abs (S3minusInner a N ℓ z sz C) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun ℓ hℓ => ?_))
    rw [abs_mul, abs_mul]
    exact mul_le_mul_of_nonneg_right (hw ℓ (Finset.mem_Icc.mp hℓ).1) (abs_nonneg _)
  have h2 : (∑ ℓ ∈ Finset.Icc 1 N, w ℓ * abs (S3minusInner a N ℓ z sz C)) ≤ ∑ ℓ ∈ Finset.Icc 1 N, w ℓ * (∫ s in (1 : ℝ)..C, abs (Xrho a N ℓ s z sz) / s) := by
    refine Finset.sum_le_sum (fun ℓ _ => mul_le_mul_of_nonneg_left ?_ (hw0 ℓ))
    exact abs_Csum_le_integral a N ℓ z sz C hC ha
  -- Step 3: swap the `ℓ`-sum and the integral
  have hInt : ∀ ℓ : ℕ, IntervalIntegrable (fun s : ℝ => abs (Xrho a N ℓ s z sz) / s)
      volume (1 : ℝ) C := fun ℓ =>
    intervalIntegrable_div_Ioc (measurable_Xrho a N ℓ z sz).abs (by norm_num) hC
      (∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) * abs (a (ℓ * n)))
      (fun s _ => by simpa using abs_Xrho_le a N ℓ s z sz)
  have h3 : (∑ ℓ ∈ Finset.Icc 1 N, w ℓ * (∫ s in (1 : ℝ)..C, abs (Xrho a N ℓ s z sz) / s)) = (∫ s in (1 : ℝ)..C, ∑ ℓ ∈ Finset.Icc 1 N, w ℓ * (abs (Xrho a N ℓ s z sz) / s)) := by
    rw [Finset.sum_congr rfl (fun ℓ _ =>
      (intervalIntegral.integral_const_mul (w ℓ) (fun s => abs (Xrho a N ℓ s z sz) / s)).symm)]
    rw [intervalIntegral.integral_finsetSum (fun ℓ _ => (hInt ℓ).const_mul (w ℓ))]
  -- Step 4: the pointwise bound (dyadic windows)
  have hpt : ∀ s : ℝ, 1 ≤ s → s ≤ C → (∑ ℓ ∈ Finset.Icc 1 N, w ℓ * (abs (Xrho a N ℓ s z sz) / s)) ≤ ((J : ℝ) * E) / s := by
    intro s hs1 hsC
    have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs1
    calc (∑ ℓ ∈ Finset.Icc 1 N, w ℓ * (abs (Xrho a N ℓ s z sz) / s))
        = (∑ ℓ ∈ Finset.Icc 1 N, w ℓ * abs (Xrho a N ℓ s z sz)) / s := by
          rw [Finset.sum_div]
          exact Finset.sum_congr rfl (fun ℓ _ => by ring)
      _ ≤ ((J : ℝ) * E) / s :=
          div_le_div_of_nonneg_right (sum_w_Xrho_le a N z sz C hz hsz hw0 hwin s hs1 hsC) hs0.le
  -- Step 5: integrate
  have hIntSum : IntervalIntegrable (fun s : ℝ => ∑ ℓ ∈ Finset.Icc 1 N, w ℓ * (abs (Xrho a N ℓ s z sz) / s)) volume (1 : ℝ) C := by
    have hfun : (∑ ℓ ∈ Finset.Icc 1 N, fun x : ℝ => w ℓ * (abs (Xrho a N ℓ x z sz) / x))
        = fun s : ℝ => ∑ ℓ ∈ Finset.Icc 1 N, w ℓ * (abs (Xrho a N ℓ s z sz) / s) := by
      funext s
      rw [Finset.sum_apply]
    rw [← hfun]
    exact IntervalIntegrable.sum (Finset.Icc 1 N) (fun ℓ _ => (hInt ℓ).const_mul (w ℓ))
  have hIntR : IntervalIntegrable (fun s : ℝ => ((J : ℝ) * E) / s) volume (1 : ℝ) C :=
    intervalIntegrable_div_Ioc measurable_const (by norm_num) hC (abs ((J : ℝ) * E))
      (fun s _ => by simp)
  have h4 : (∫ s in (1 : ℝ)..C, ∑ ℓ ∈ Finset.Icc 1 N, w ℓ * (abs (Xrho a N ℓ s z sz) / s)) ≤ (J : ℝ) * E * Real.log C := by
    have hmono : (∫ s in (1 : ℝ)..C, ∑ ℓ ∈ Finset.Icc 1 N, w ℓ * (abs (Xrho a N ℓ s z sz) / s))
        ≤ ∫ s in (1 : ℝ)..C, ((J : ℝ) * E) / s := by
      refine intervalIntegral.integral_mono_ae_restrict hC hIntSum hIntR ?_
      change ∀ᵐ x ∂(volume.restrict (Set.Icc (1 : ℝ) C)),
          (∑ ℓ ∈ Finset.Icc 1 N, w ℓ * (abs (Xrho a N ℓ x z sz) / x)) ≤ ((J : ℝ) * E) / x
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
      exact Filter.Eventually.of_forall (fun s hs => hpt s hs.1 hs.2)
    have hval : (∫ s in (1 : ℝ)..C, ((J : ℝ) * E) / s) = (J : ℝ) * E * Real.log C := by
      have hfun : (fun s : ℝ => ((J : ℝ) * E) / s) = fun s => ((J : ℝ) * E) * (1 / s) := by
        funext s; ring
      rw [hfun, intervalIntegral.integral_const_mul,
        integral_one_div_of_pos zero_lt_one (by linarith), div_one]
    rw [hval] at hmono
    exact hmono
  exact le_trans h1 (le_trans h2 (le_trans (le_of_eq h3) h4))

end

end Submission.ASP
