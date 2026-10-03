/-
# `Submission.Work.FIChain.RhoWin2Box` — the `Π`-restricted `ρ`-window box bound

From the `Π`-restricted Proposition 4.1 (`Work.FITop4.Prop41StatementPiBig`) this file derives the
box bound

  `∑_{c ≤ x} |Xpg x Pz c σ u| ≤ K₀·Ã(x)·(log x)^{-2^26}`

for every real window position `u ∈ (x^{1/4+η'}, x^{1/2}(log x)^{-B₀}]` and every truncation level
`σ ∈ [1, (u/2)^{1-η'}]`, uniformly in `Pz` in the range (4.4).

The argument is the one of the companion paper's §10:

* `RhoWin2Bridge` (already proved) identifies the Proposition-4.1 form `BformPi x N C Pz` at an
  *integral* window `N` with the aggregate `∑_{c ≤ x}|Xpg x Pz c C N|` (the coprimality condition
  `(n,c) = 1` of `BformPi` is redundant: `ã(mn) = 0` when `(m,n) > 1`);
* `rwb_split` splits the real window `(u,2u]` at the aligned integral window `(⌊u⌋, 2⌊u⌋]`; the only
  leftover term is the single integer `2⌊u⌋+1`;
* `rwb_corr` bounds that single-modulus congruence sum by `C·(τ(2⌊u⌋+1)³/(2⌊u⌋+1))·Ã(x)`, using
  the aggregate (2.1)-type input `Work.FITop.AtilCongruenceSum` (which rests on the elementary
  bound `A_d(x) ≤ Cτ(d)²A(x)/d` of the main paper);
* `rwb_arith` converts the divisor factor `τ(d)³/d` into the logarithmic saving
  `(log x)^{-2^26}`, using `τ(d) ≤ Cτ·d^{1/8}` and `d ≥ x^{1/4+η'}`.

Everything is proved here; the only imported results about the sequence are
`Work.FIChain.RhoWin2Bridge` and `Work.FITop.AtilCongruenceSum`.
-/
import Mathlib
import Submission.Work.FIChain.RhoWin2Defs
import Submission.Work.FIChain.RhoWin2Bridge
import Submission.Work.FITop.AtilCongruenceSum
import Submission.Commons.Analysis.ExpLog.const_mul_log_pow_le_rpow_threshold_nat
import Submission.Commons.NumberTheory.DivisorBound.card_divisors_le_rpow

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIChain

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. Splitting the real window `(u,2u]` at the aligned integral window -/

/-- The real window `(u,2u]` and the aligned integral window `(⌊u⌋, 2⌊u⌋]` have the same integer
content except for the single integer `2⌊u⌋+1`, which appears exactly when `2⌊u⌋+1 ≤ 2u`. -/
private lemma rwb_split (x Pz c : ℕ) (σ u : ℝ) (hc : 1 ≤ c) (hu : 2 ≤ u) :
    Xpg x Pz c σ u = Xpg x Pz c σ ((⌊u⌋₊ : ℕ) : ℝ)
      + (if ((((2 * ⌊u⌋₊ + 1 : ℕ) : ℝ) ≤ 2 * u) ∧ ((2 * ⌊u⌋₊ + 1) * c ≤ x)
            ∧ Work.FITop4.PiCond Pz (2 * ⌊u⌋₊ + 1))
         then (ArithmeticFunction.moebius (2 * ⌊u⌋₊ + 1) : ℝ)
              * Work.FIPlan.gammaTrunc σ (2 * ⌊u⌋₊ + 1)
              * atilc ((2 * ⌊u⌋₊ + 1) * c) else 0) := by
  set S : Finset ℕ := (Finset.Icc 1 x).filter (fun n => c * n ≤ x ∧ Work.FITop4.PiCond Pz n) with hS
  set A : ℕ → ℝ := fun n => (ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc σ n * atilc (c * n) with hA
  have hu0 : 0 ≤ u := by linarith
  have h2u0 : (0:ℝ) ≤ 2 * u := by linarith
  have hQ1 : 2 * ⌊u⌋₊ ≤ ⌊2 * u⌋₊ := by
    apply Nat.le_floor
    push_cast
    linarith [Nat.floor_le hu0]
  have hQ2 : ⌊2 * u⌋₊ ≤ 2 * ⌊u⌋₊ + 1 := by
    have hfl : ((⌊2 * u⌋₊ : ℕ) : ℝ) ≤ 2 * u := Nat.floor_le h2u0
    have hlt : 2 * u < 2 * ((⌊u⌋₊ : ℕ) : ℝ) + 2 := by
      have := Nat.lt_floor_add_one u; linarith
    have h3 : ⌊2 * u⌋₊ < 2 * ⌊u⌋₊ + 2 := by
      have : ((⌊2 * u⌋₊ : ℕ) : ℝ) < ((2 * ⌊u⌋₊ + 2 : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    omega
  have hwin1 : Xpg x Pz c σ u
      = ∑ n ∈ S, (if (⌊u⌋₊ < n ∧ n ≤ ⌊2 * u⌋₊) then A n else 0) := by
    rw [Xpg_eq_ite, hS, hA]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    exact if_congr (by
      constructor
      · intro h
        exact ⟨(Nat.floor_lt hu0).mpr h.1, Nat.le_floor h.2⟩
      · intro h
        exact ⟨(Nat.floor_lt hu0).mp h.1, le_trans (Nat.cast_le.mpr h.2) (Nat.floor_le h2u0)⟩) rfl rfl
  have hwin2 : Xpg x Pz c σ ((⌊u⌋₊ : ℕ) : ℝ)
      = ∑ n ∈ S, (if (⌊u⌋₊ < n ∧ n ≤ 2 * ⌊u⌋₊) then A n else 0) := by
    rw [Xpg_natCast, hS, hA]
    have hfil : (Finset.Icc 1 x).filter
        (fun n => c * n ≤ x ∧ Work.FITop4.PiCond Pz n ∧ (⌊u⌋₊ < n ∧ n ≤ 2 * ⌊u⌋₊))
        = ((Finset.Icc 1 x).filter (fun n => c * n ≤ x ∧ Work.FITop4.PiCond Pz n)).filter
            (fun n => ⌊u⌋₊ < n ∧ n ≤ 2 * ⌊u⌋₊) := by
      rw [Finset.filter_filter]
      exact Finset.filter_congr (fun n _ => by tauto)
    rw [hfil, Finset.sum_filter]
  have hpt : ∀ n ∈ S, (if (⌊u⌋₊ < n ∧ n ≤ ⌊2 * u⌋₊) then A n else 0)
      = (if (⌊u⌋₊ < n ∧ n ≤ 2 * ⌊u⌋₊) then A n else 0)
        + (if (n = 2 * ⌊u⌋₊ + 1 ∧ 2 * ⌊u⌋₊ + 1 ≤ ⌊2 * u⌋₊) then A n else 0) := by
    intro n _
    by_cases hnN : n ≤ 2 * ⌊u⌋₊
    · have hiff : (⌊u⌋₊ < n ∧ n ≤ ⌊2 * u⌋₊) ↔ (⌊u⌋₊ < n ∧ n ≤ 2 * ⌊u⌋₊) :=
        ⟨fun h => ⟨h.1, hnN⟩, fun h => ⟨h.1, le_trans h.2 hQ1⟩⟩
      rw [if_congr hiff rfl rfl, if_neg (by omega : ¬ (n = 2 * ⌊u⌋₊ + 1 ∧ 2 * ⌊u⌋₊ + 1 ≤ ⌊2 * u⌋₊))]
      ring
    · have hiff : (⌊u⌋₊ < n ∧ n ≤ ⌊2 * u⌋₊) ↔ (n = 2 * ⌊u⌋₊ + 1 ∧ 2 * ⌊u⌋₊ + 1 ≤ ⌊2 * u⌋₊) := by
        constructor
        · intro h
          have hn1 : 2 * ⌊u⌋₊ + 1 ≤ n := by omega
          have h2 : n ≤ 2 * ⌊u⌋₊ + 1 := by omega
          exact ⟨by omega, by omega⟩
        · rintro ⟨rfl, h⟩
          exact ⟨by omega, h⟩
      rw [if_congr hiff rfl rfl, if_neg (by omega : ¬ (⌊u⌋₊ < n ∧ n ≤ 2 * ⌊u⌋₊)), zero_add]
  have hsumsplit : ∑ n ∈ S, (if (n = 2 * ⌊u⌋₊ + 1 ∧ 2 * ⌊u⌋₊ + 1 ≤ ⌊2 * u⌋₊) then A n else 0)
      = (if ((2 * ⌊u⌋₊ + 1 ∈ S) ∧ (2 * ⌊u⌋₊ + 1 ≤ ⌊2 * u⌋₊)) then A (2 * ⌊u⌋₊ + 1) else 0) := by
    rw [show (∑ n ∈ S, (if (n = 2 * ⌊u⌋₊ + 1 ∧ 2 * ⌊u⌋₊ + 1 ≤ ⌊2 * u⌋₊) then A n else 0))
        = ∑ n ∈ S, (if n = 2 * ⌊u⌋₊ + 1 then (if 2 * ⌊u⌋₊ + 1 ≤ ⌊2 * u⌋₊ then A n else 0) else 0) from
      Finset.sum_congr rfl (fun n _ => ite_and _ _ _ _)]
    rw [Finset.sum_ite_eq', ite_and]
  have hmem : (2 * ⌊u⌋₊ + 1 ∈ S) ↔ ((2 * ⌊u⌋₊ + 1) * c ≤ x ∧ Work.FITop4.PiCond Pz (2 * ⌊u⌋₊ + 1)) := by
    rw [hS, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨-, -⟩, h2, h3⟩
      exact ⟨by rwa [mul_comm] at h2, h3⟩
    · rintro ⟨h2, h3⟩
      refine ⟨⟨by omega, ?_⟩, by rwa [mul_comm], h3⟩
      calc 2 * ⌊u⌋₊ + 1 = (2 * ⌊u⌋₊ + 1) * 1 := by ring
        _ ≤ (2 * ⌊u⌋₊ + 1) * c := Nat.mul_le_mul_left _ hc
        _ ≤ x := h2
  have hP : (2 * ⌊u⌋₊ + 1 ≤ ⌊2 * u⌋₊) ↔ (((2 * ⌊u⌋₊ + 1 : ℕ) : ℝ) ≤ 2 * u) :=
    ⟨fun h => le_trans (Nat.cast_le.mpr h) (Nat.floor_le h2u0), fun h => Nat.le_floor h⟩
  rw [hwin1, hwin2, Finset.sum_congr rfl hpt, Finset.sum_add_distrib, hsumsplit]
  congr 1
  refine if_congr ?_ ?_ rfl
  · rw [hmem, hP]; tauto
  · rw [hA]; simp only [Nat.mul_comm c (2 * ⌊u⌋₊ + 1)]

/-! ## 2. The single leftover term -/

/-- The single-modulus congruence sum of `ã`, with the `τ(b)` from `|γ_σ(b)|`: this is
`AtilCongruenceSum` together with `|γ_σ(b)| ≤ τ(b)`. -/
private lemma rwb_corr :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℕ, ∀ x b : ℕ, X₀ ≤ x → 1 ≤ b → b * b ≤ x → ∀ σ : ℝ,
      (∑ c ∈ Finset.Icc 1 x,
          |(if b * c ≤ x then Work.FIPlan.gammaTrunc σ b * atilc (b * c) else 0)|)
        ≤ C * (((b.divisors.card : ℝ) ^ 3) / (b : ℝ)) * AcountAtilC x := by
  obtain ⟨C₀, XA, hC₀pos, hCong⟩ := Work.FITop.AtilCongruenceSum
  refine ⟨(C₀ : ℝ), by exact_mod_cast hC₀pos, XA, fun x b hx hb hbsq σ => ?_⟩
  have hγ : |Work.FIPlan.gammaTrunc σ b| ≤ ((b.divisors.card : ℝ)) := by
    rw [Work.FIPlan.gammaTrunc]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have h1 : (∑ d ∈ b.divisors.filter (fun d => ((d : ℕ) : ℝ) ≤ σ),
          |(ArithmeticFunction.moebius d : ℝ)|)
        ≤ ∑ d ∈ b.divisors.filter (fun d => ((d : ℕ) : ℝ) ≤ σ), (1 : ℝ) :=
      Finset.sum_le_sum (fun d _ => by
        have h := ArithmeticFunction.abs_moebius_le_one (n := d)
        exact_mod_cast h)
    have h2 : (∑ _d ∈ b.divisors.filter (fun d => ((d : ℕ) : ℝ) ≤ σ), (1 : ℝ))
        ≤ ∑ _d ∈ b.divisors, (1 : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => by norm_num)
    have h3 : (∑ _d ∈ b.divisors, (1 : ℝ)) = ((b.divisors.card : ℝ)) := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    linarith [h1, h2, h3]
  have hterm : ∀ c ∈ Finset.Icc 1 x,
      |(if b * c ≤ x then Work.FIPlan.gammaTrunc σ b * atilc (b * c) else 0)|
        ≤ ((b.divisors.card : ℝ)) * (if b * c ≤ x then atilc (b * c) else 0) := by
    intro c _
    by_cases h : b * c ≤ x
    · rw [if_pos h, if_pos h, abs_mul, abs_of_nonneg (Work.FITop.atilFIa_nonneg (b * c))]
      exact mul_le_mul_of_nonneg_right hγ (Work.FITop.atilFIa_nonneg (b * c))
    · rw [if_neg h, if_neg h, abs_zero, mul_zero]
  calc (∑ c ∈ Finset.Icc 1 x,
        |(if b * c ≤ x then Work.FIPlan.gammaTrunc σ b * atilc (b * c) else 0)|)
      ≤ ∑ c ∈ Finset.Icc 1 x,
          ((b.divisors.card : ℝ)) * (if b * c ≤ x then atilc (b * c) else 0) :=
        Finset.sum_le_sum hterm
    _ = ((b.divisors.card : ℝ)) * ∑ c ∈ Finset.Icc 1 x,
          (if b * c ≤ x then atilc (b * c) else 0) := by
        rw [Finset.mul_sum]
    _ ≤ ((b.divisors.card : ℝ)) * ((C₀ : ℝ) * (((b.divisors.card : ℝ) ^ 2) / (b : ℝ)) * AcountAtilC x) :=
        mul_le_mul_of_nonneg_left (hCong b x hx hb hbsq) (by positivity)
    _ = (C₀ : ℝ) * (((b.divisors.card : ℝ) ^ 3) / (b : ℝ)) * AcountAtilC x := by ring

/-! ## 3. The divisor factor `τ(d)³/d` against `(log x)^{-2^26}` -/

/-- `C·τ(d)³/d ≤ (log x)^{-2^26}` for `d ≥ x^{1/4+η'}`: with `τ(d) ≤ Cτ·d^{1/8}` the left side is
`≤ C·Cτ³·d^{-5/8} ≤ C·Cτ³·x^{-(5/8)(1/4+η')}`, and the constant times `(log x)^{2^26}` is
eventually below `x^{(5/8)(1/4+η')}`. -/
private lemma rwb_arith (dd : ℕ) (C Cτ D X L η' : ℝ) (hC : 0 < C) (_hCτ : 0 < Cτ) (hD : 0 < D)
    (hτ : ((dd.divisors.card : ℝ)) ≤ Cτ * D ^ ((1:ℝ)/8))
    (hXD : X ^ ((1:ℝ)/4 + η') ≤ D)
    (hx1 : 1 ≤ X) (hL : 0 < L)
    (hXr : (C * Cτ^3) * L ^ ((2:ℝ)^(26:ℕ)) ≤ X ^ ((5:ℝ)/8 * ((1:ℝ)/4 + η'))) :
    C * (((dd.divisors.card : ℝ))^3 / D) ≤ L ^ (-((2:ℝ)^(26:ℕ))) := by
  have hτnn : (0:ℝ) ≤ ((dd.divisors.card : ℝ)) := by positivity
  have hτ3 : ((dd.divisors.card : ℝ))^3 ≤ Cτ^3 * D ^ ((3:ℝ)/8) := by
    have h := pow_le_pow_left₀ hτnn hτ 3
    have h2 : (Cτ * D ^ ((1:ℝ)/8))^3 = Cτ^3 * D ^ ((3:ℝ)/8) := by
      rw [mul_pow, ← Real.rpow_natCast (D ^ ((1:ℝ)/8)) 3, ← Real.rpow_mul (le_of_lt hD)]
      norm_num
    rwa [h2] at h
  have hD38 : (0:ℝ) < D ^ ((3:ℝ)/8) := Real.rpow_pos_of_pos hD _
  have hXDpow : X ^ ((5:ℝ)/8 * ((1:ℝ)/4 + η')) ≤ D ^ ((5:ℝ)/8) := by
    have h1 : (X ^ ((1:ℝ)/4 + η')) ^ ((5:ℝ)/8) ≤ D ^ ((5:ℝ)/8) :=
      Real.rpow_le_rpow (Real.rpow_nonneg (by linarith) _) hXD (by norm_num)
    have h2 : (X ^ ((1:ℝ)/4 + η')) ^ ((5:ℝ)/8) = X ^ ((5:ℝ)/8 * ((1:ℝ)/4 + η')) := by
      rw [← Real.rpow_mul (by linarith : (0:ℝ) ≤ X)]
      congr 1; ring
    linarith [h1, h2.le]
  have hmain : C * (((dd.divisors.card : ℝ))^3) * L ^ ((2:ℝ)^(26:ℕ)) ≤ D := by
    calc C * (((dd.divisors.card : ℝ))^3) * L ^ ((2:ℝ)^(26:ℕ))
        ≤ C * (Cτ^3 * D ^ ((3:ℝ)/8)) * L ^ ((2:ℝ)^(26:ℕ)) := by
          gcongr
      _ = (C * Cτ^3 * L ^ ((2:ℝ)^(26:ℕ))) * D ^ ((3:ℝ)/8) := by ring
      _ ≤ X ^ ((5:ℝ)/8 * ((1:ℝ)/4 + η')) * D ^ ((3:ℝ)/8) := by
          apply mul_le_mul_of_nonneg_right hXr (le_of_lt hD38)
      _ ≤ D ^ ((5:ℝ)/8) * D ^ ((3:ℝ)/8) := by
          apply mul_le_mul_of_nonneg_right hXDpow (le_of_lt hD38)
      _ = D := by
          rw [← Real.rpow_add hD]
          norm_num
  rw [show C * (((dd.divisors.card : ℝ))^3 / D) = C * (((dd.divisors.card : ℝ))^3) / D by ring]
  rw [div_le_iff₀ hD, Real.rpow_neg (le_of_lt hL)]
  rw [inv_mul_eq_div, le_div_iff₀ (Real.rpow_pos_of_pos hL _)]
  exact hmain

/-! ## 4. Eventual facts in `x` -/

private lemma rwb_ll1 : ∀ᶠ x : ℕ in Filter.atTop, (1:ℝ) ≤ Real.log (Real.log (x:ℝ)) :=
  (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
    (Filter.eventually_ge_atTop 1)

private lemma rwb_log4 : ∀ᶠ x : ℕ in Filter.atTop, (4:ℝ) ≤ Real.log (x:ℝ) :=
  (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (Filter.eventually_ge_atTop 4)

private lemma rwb_x4 : ∀ᶠ x : ℕ in Filter.atTop, (4:ℝ) ≤ (x:ℝ) :=
  (Filter.eventually_ge_atTop 4).mono (fun x hx => by exact_mod_cast hx)

/-- `(log x)^{-B} ≤ 1/4` for `log x ≥ 4`, `B ≥ 1`. -/
private lemma rwb_LB_le (y : ℝ) (hlog : 4 ≤ Real.log y) (B : ℝ) (hB : 1 ≤ B) :
    (Real.log y) ^ (-B) ≤ (1:ℝ)/4 := by
  have h1 : (Real.log y) ^ (-B) ≤ (4:ℝ)^(-B) :=
    Real.rpow_le_rpow_of_nonpos (show (0:ℝ) < 4 by norm_num) hlog (by linarith)
  have h2 : (4:ℝ)^(-B) ≤ (4:ℝ)^(-1:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have h3 : (4:ℝ)^(-1:ℝ) = 1/4 := by rw [Real.rpow_neg (by norm_num), Real.rpow_one]; norm_num
  exact le_trans (le_trans h1 h2) h3.le

/-- `2·x^{1/2}(log x)^{-B} ≤ x` for large `x` (so that `2⌊u⌋ ≤ x`). -/
private lemma rwb_evhalf (B : ℝ) (hB : 1 ≤ B) :
    ∀ᶠ x : ℕ in Filter.atTop, 2 * ((x:ℝ) ^ ((1:ℝ)/2) * (Real.log (x:ℝ)) ^ (-B)) ≤ (x:ℝ) := by
  filter_upwards [rwb_log4, rwb_x4] with x hlog hx4
  have hx1 : (1:ℝ) ≤ (x:ℝ) := by linarith
  have hxpos : (0:ℝ) < (x:ℝ) := by linarith
  have hLB := rwb_LB_le (x:ℝ) hlog B hB
  have hhalf : 2 * ((x:ℝ) ^ ((1:ℝ)/2) * (Real.log (x:ℝ)) ^ (-B)) ≤ (x:ℝ) ^ ((1:ℝ)/2) / 2 := by
    have h2 : 2 * ((x:ℝ) ^ ((1:ℝ)/2) * (Real.log (x:ℝ)) ^ (-B))
        ≤ 2 * ((x:ℝ) ^ ((1:ℝ)/2) * (1/4)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hLB (Real.rpow_nonneg (le_of_lt hxpos) _)) (by norm_num)
    have h3 : 2 * ((x:ℝ) ^ ((1:ℝ)/2) * (1/4)) = (x:ℝ) ^ ((1:ℝ)/2) / 2 := by ring
    exact le_trans h2 h3.le
  have hxhalf : (x:ℝ) ^ ((1:ℝ)/2) ≤ (x:ℝ) := by
    calc (x:ℝ) ^ ((1:ℝ)/2) ≤ (x:ℝ) ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
      _ = (x:ℝ) := Real.rpow_one _
  have hnn : (0:ℝ) ≤ (x:ℝ) ^ ((1:ℝ)/2) := Real.rpow_nonneg (le_of_lt hxpos) _
  linarith

/-- `2·x^{1/2}(log x)^{-B} + 1 ≤ x^{1/2}` for large `x` (so that `(2⌊u⌋+1)² ≤ x`). -/
private lemma rwb_evfull (B : ℝ) (hB : 1 ≤ B) :
    ∀ᶠ x : ℕ in Filter.atTop,
      2 * ((x:ℝ) ^ ((1:ℝ)/2) * (Real.log (x:ℝ)) ^ (-B)) + 1 ≤ (x:ℝ) ^ ((1:ℝ)/2) := by
  filter_upwards [rwb_log4, rwb_x4] with x hlog hx4
  have hx1 : (1:ℝ) ≤ (x:ℝ) := by linarith
  have hxpos : (0:ℝ) < (x:ℝ) := by linarith
  have hLB := rwb_LB_le (x:ℝ) hlog B hB
  have hxhalf : (2:ℝ) ≤ (x:ℝ) ^ ((1:ℝ)/2) := by
    have h1 : (4:ℝ) ^ ((1:ℝ)/2) ≤ (x:ℝ) ^ ((1:ℝ)/2) :=
      Real.rpow_le_rpow (by norm_num) hx4 (by norm_num)
    have h2 : (4:ℝ) ^ ((1:ℝ)/2) = 2 := by norm_num
    linarith [h1, h2.le]
  have hhalf : 2 * ((x:ℝ) ^ ((1:ℝ)/2) * (Real.log (x:ℝ)) ^ (-B)) ≤ (x:ℝ) ^ ((1:ℝ)/2) / 2 := by
    have h2 : 2 * ((x:ℝ) ^ ((1:ℝ)/2) * (Real.log (x:ℝ)) ^ (-B))
        ≤ 2 * ((x:ℝ) ^ ((1:ℝ)/2) * (1/4)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hLB (Real.rpow_nonneg (le_of_lt hxpos) _)) (by norm_num)
    have h3 : 2 * ((x:ℝ) ^ ((1:ℝ)/2) * (1/4)) = (x:ℝ) ^ ((1:ℝ)/2) / 2 := by ring
    exact le_trans h2 h3.le
  linarith

/-! ## 5. The box bound -/

theorem RhoWin2Box (h : Work.FITop4.Prop41StatementPiBig) (η' : ℝ) (hη' : 0 < η')
    (hη'32 : η' < 3 / 32) :
    ∃ K₀ : ℝ, 0 < K₀ ∧ ∃ B₀ : ℝ, 0 < B₀ ∧ ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x → ∀ Pz : ℕ, 2 ≤ Pz →
      (Real.log (Real.log (x : ℝ))) ^ 2 ≤ Real.log (Pz : ℝ) →
      Real.log (Pz : ℝ) ≤ Real.log (x : ℝ) * (Real.log (Real.log (x : ℝ))) ^ (-2 : ℤ) →
      ∀ u σ : ℝ, (x : ℝ) ^ ((1 : ℝ) / 4 + η') + 1 < u →
        u ≤ (x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log (x : ℝ)) ^ (-B₀) →
        1 ≤ σ → σ ≤ (u / 2) ^ (1 - η') →
        (∑ c ∈ Finset.Icc 1 x, |Xpg x Pz c σ u|)
          ≤ K₀ * AcountAtilC x * (Real.log (x : ℝ)) ^ (-((2 : ℝ) ^ (26 : ℕ))) := by
  obtain ⟨B, K, xP, hBpos, hBleBmax, hKpos, hP41⟩ := h η' hη' hη'32
  obtain ⟨C, hCpos, XC, hCorr⟩ := rwb_corr
  obtain ⟨Cτ, hCτpos, hCτbd⟩ :=
    Commons.NumberTheory.DivisorBound.card_divisors_le_rpow (1 / 8) (by norm_num)
  have hRpos : 0 < (5 : ℝ) / 8 * ((1 : ℝ) / 4 + η') := by nlinarith
  obtain ⟨Xr, hXr1, hXr⟩ := Commons.Analysis.ExpLog.const_mul_log_pow_le_rpow_threshold_nat
      (K := C * Cτ ^ 3) (n := 2 ^ 26) (r := (5 : ℝ) / 8 * ((1 : ℝ) / 4 + η')) (by positivity) hRpos
  have hB1 : (1:ℝ) ≤ B + 1 := by linarith
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.mp (show ∀ᶠ x : ℕ in Filter.atTop,
      xP ≤ x ∧ XC ≤ x ∧ Xr ≤ x ∧ (4:ℝ) ≤ Real.log (x:ℝ) ∧ (1:ℝ) ≤ Real.log (Real.log (x:ℝ))
        ∧ (4:ℝ) ≤ (x:ℝ)
        ∧ 2 * ((x:ℝ) ^ ((1:ℝ)/2) * (Real.log (x:ℝ)) ^ (-(B+1))) ≤ (x:ℝ)
        ∧ 2 * ((x:ℝ) ^ ((1:ℝ)/2) * (Real.log (x:ℝ)) ^ (-(B+1))) + 1 ≤ (x:ℝ) ^ ((1:ℝ)/2) from by
    filter_upwards [Filter.eventually_ge_atTop xP, Filter.eventually_ge_atTop XC,
      Filter.eventually_ge_atTop Xr, rwb_log4, rwb_ll1, rwb_x4,
      rwb_evhalf (B + 1) hB1, rwb_evfull (B + 1) hB1] with x h1 h2 h3 h4 h5 h6 h7 h8
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩)
  refine ⟨K + 1, by linarith, B + 1, by linarith, x₀,
    fun x hx Pz hPz2 hPlo hPhi u σ hulo huup hσ1 hσ2 => ?_⟩
  obtain ⟨hxP, hxC, hxr, hlog4, hll1, hx4, hevhalf, hevfull⟩ := hx₀ x hx
  have hx1 : (1:ℝ) ≤ (x:ℝ) := by linarith
  have hxpos : (0:ℝ) < (x:ℝ) := by linarith
  have hL1 : (1:ℝ) ≤ Real.log (x:ℝ) := by linarith
  have hLpos : (0:ℝ) < Real.log (x:ℝ) := by linarith
  have hxpow1 : (1:ℝ) ≤ (x:ℝ)^((1:ℝ)/4+η') := Real.one_le_rpow hx1 (by nlinarith)
  have hu2 : 2 ≤ u := by linarith
  have hu0 : (0:ℝ) ≤ u := by linarith
  have hNle_u : ((⌊u⌋₊:ℕ):ℝ) ≤ u := Nat.floor_le hu0
  have hNlt : u < ((⌊u⌋₊:ℕ):ℝ) + 1 := Nat.lt_floor_add_one u
  have hNgt : (x:ℝ)^((1:ℝ)/4+η') < ((⌊u⌋₊:ℕ):ℝ) := by linarith
  have hN1 : 1 ≤ ⌊u⌋₊ := by
    have hh : (1:ℝ) ≤ ((⌊u⌋₊:ℕ):ℝ) := by linarith
    exact_mod_cast hh
  have h2N : 2 * ⌊u⌋₊ ≤ x := by
    have h1 : (((2 * ⌊u⌋₊ : ℕ)):ℝ) ≤ (x:ℝ) := by
      have h2 : (((2 * ⌊u⌋₊ : ℕ)):ℝ) ≤ 2*u := by push_cast; linarith
      linarith [h2, huup, hevhalf]
    exact_mod_cast h1
  have ha1 : 1 ≤ 2 * ⌊u⌋₊ + 1 := by omega
  have haD : (x:ℝ)^((1:ℝ)/4+η') ≤ (((2 * ⌊u⌋₊ + 1 : ℕ)):ℝ) := by
    have h2 : ((⌊u⌋₊:ℕ):ℝ) ≤ (((2 * ⌊u⌋₊ + 1 : ℕ)):ℝ) := by push_cast; linarith
    linarith [hNgt, h2]
  have haasq : (2 * ⌊u⌋₊ + 1) * (2 * ⌊u⌋₊ + 1) ≤ x := by
    have h1 : (((2 * ⌊u⌋₊ + 1 : ℕ)):ℝ) ≤ (x:ℝ)^((1:ℝ)/2) := by
      have h2 : (((2 * ⌊u⌋₊ + 1 : ℕ)):ℝ) ≤ 2*u+1 := by push_cast; linarith
      linarith [h2, huup, hevfull]
    have h4 : ((x:ℝ)^((1:ℝ)/2))^2 = (x:ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hxpos)]
      norm_num
    have h3 : ((((2 * ⌊u⌋₊ + 1 : ℕ)):ℝ))^2 ≤ (x:ℝ) := by
      calc ((((2 * ⌊u⌋₊ + 1 : ℕ)):ℝ))^2 ≤ ((x:ℝ)^((1:ℝ)/2))^2 :=
            pow_le_pow_left₀ (by positivity) h1 2
        _ = (x:ℝ) := h4
    have h5 : ((((2 * ⌊u⌋₊ + 1 : ℕ)):ℝ))^2
        = (((2 * ⌊u⌋₊ + 1)*(2 * ⌊u⌋₊ + 1):ℕ):ℝ) := by push_cast; ring
    rw [h5] at h3
    exact_mod_cast h3
  have hNhi : ((⌊u⌋₊:ℕ):ℝ) < (x:ℝ)^((1:ℝ)/2) * (Real.log (x:ℝ))^(-B) := by
    have h2 : (Real.log (x:ℝ))^(-(B+1)) < (Real.log (x:ℝ))^(-B) :=
      Real.rpow_lt_rpow_of_exponent_lt (by linarith : (1:ℝ) < Real.log (x:ℝ)) (by linarith)
    have h3 : (x:ℝ)^((1:ℝ)/2) * (Real.log (x:ℝ))^(-(B+1))
        < (x:ℝ)^((1:ℝ)/2) * (Real.log (x:ℝ))^(-B) :=
      mul_lt_mul_of_pos_left h2 (Real.rpow_pos_of_pos hxpos _)
    linarith
  have hσ2' : σ ≤ ((⌊u⌋₊:ℕ):ℝ)^(1-η') := by
    have huN : u/2 ≤ ((⌊u⌋₊:ℕ):ℝ) := by linarith
    have h1 : (u/2)^(1-η') ≤ ((⌊u⌋₊:ℕ):ℝ)^(1-η') :=
      Real.rpow_le_rpow (by linarith) huN (by linarith)
    linarith
  have hExp : (4:ℝ) - Work.FITop4.Astar = -((2:ℝ)^(26:ℕ)) := by rw [Work.FITop4.Astar]; ring
  have hP41app : (∑ m ∈ Finset.Icc 1 x, |Xpg x Pz m σ ((⌊u⌋₊:ℕ):ℝ)|)
      ≤ K * AcountAtilC x * (Real.log (x:ℝ)) ^ (-((2:ℝ)^(26:ℕ))) := by
    have h0 := hP41 x hxP ⌊u⌋₊ hNgt hNhi hll1 σ hσ1 hσ2' Pz hPz2 hPlo hPhi
    rw [hExp, RhoWin2Bridge x Pz ⌊u⌋₊ σ h2N] at h0
    exact h0
  have hsplit : ∀ c ∈ Finset.Icc 1 x,
      |Xpg x Pz c σ u| ≤ |Xpg x Pz c σ ((⌊u⌋₊:ℕ):ℝ)|
        + |(if ((((2 * ⌊u⌋₊ + 1 : ℕ) : ℝ) ≤ 2 * u) ∧ ((2 * ⌊u⌋₊ + 1) * c ≤ x)
              ∧ Work.FITop4.PiCond Pz (2 * ⌊u⌋₊ + 1))
           then (ArithmeticFunction.moebius (2 * ⌊u⌋₊ + 1) : ℝ)
                * Work.FIPlan.gammaTrunc σ (2 * ⌊u⌋₊ + 1)
                * atilc ((2 * ⌊u⌋₊ + 1) * c) else 0)| := by
    intro c hc
    have hc1 : 1 ≤ c := (Finset.mem_Icc.mp hc).1
    rw [rwb_split x Pz c σ u hc1 hu2]
    exact abs_add_le _ _
  have hsum : (∑ c ∈ Finset.Icc 1 x, |Xpg x Pz c σ u|)
      ≤ (∑ c ∈ Finset.Icc 1 x, |Xpg x Pz c σ ((⌊u⌋₊:ℕ):ℝ)|)
        + ∑ c ∈ Finset.Icc 1 x,
            |(if ((((2 * ⌊u⌋₊ + 1 : ℕ) : ℝ) ≤ 2 * u) ∧ ((2 * ⌊u⌋₊ + 1) * c ≤ x)
              ∧ Work.FITop4.PiCond Pz (2 * ⌊u⌋₊ + 1))
             then (ArithmeticFunction.moebius (2 * ⌊u⌋₊ + 1) : ℝ)
                  * Work.FIPlan.gammaTrunc σ (2 * ⌊u⌋₊ + 1)
                  * atilc ((2 * ⌊u⌋₊ + 1) * c) else 0)| := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum hsplit
  have hcorrpt : ∀ c ∈ Finset.Icc 1 x,
      |(if ((((2 * ⌊u⌋₊ + 1 : ℕ) : ℝ) ≤ 2 * u) ∧ ((2 * ⌊u⌋₊ + 1) * c ≤ x)
            ∧ Work.FITop4.PiCond Pz (2 * ⌊u⌋₊ + 1))
         then (ArithmeticFunction.moebius (2 * ⌊u⌋₊ + 1) : ℝ)
              * Work.FIPlan.gammaTrunc σ (2 * ⌊u⌋₊ + 1)
              * atilc ((2 * ⌊u⌋₊ + 1) * c) else 0)|
        ≤ |(if (2 * ⌊u⌋₊ + 1) * c ≤ x then Work.FIPlan.gammaTrunc σ (2 * ⌊u⌋₊ + 1)
            * atilc ((2 * ⌊u⌋₊ + 1) * c) else 0)| := by
    intro c _
    by_cases h : (2 * ⌊u⌋₊ + 1) * c ≤ x
    · rw [if_pos h]
      by_cases hQ : (((2 * ⌊u⌋₊ + 1 : ℕ) : ℝ) ≤ 2 * u) ∧ (2 * ⌊u⌋₊ + 1) * c ≤ x
          ∧ Work.FITop4.PiCond Pz (2 * ⌊u⌋₊ + 1)
      · rw [if_pos hQ]
        have hμ : |(ArithmeticFunction.moebius (2 * ⌊u⌋₊ + 1) : ℝ)| ≤ 1 := by
          have hh := ArithmeticFunction.abs_moebius_le_one (n := 2 * ⌊u⌋₊ + 1)
          exact_mod_cast hh
        have hγnn : (0:ℝ) ≤ |Work.FIPlan.gammaTrunc σ (2 * ⌊u⌋₊ + 1)| := abs_nonneg _
        have hann : (0:ℝ) ≤ atilc ((2 * ⌊u⌋₊ + 1) * c) := Work.FITop.atilFIa_nonneg _
        calc |(ArithmeticFunction.moebius (2 * ⌊u⌋₊ + 1) : ℝ)
                * Work.FIPlan.gammaTrunc σ (2 * ⌊u⌋₊ + 1)
                * atilc ((2 * ⌊u⌋₊ + 1) * c)|
            = |(ArithmeticFunction.moebius (2 * ⌊u⌋₊ + 1) : ℝ)|
                * |Work.FIPlan.gammaTrunc σ (2 * ⌊u⌋₊ + 1)| * atilc ((2 * ⌊u⌋₊ + 1) * c) := by
              rw [abs_mul, abs_mul, abs_of_nonneg hann]
          _ ≤ 1 * |Work.FIPlan.gammaTrunc σ (2 * ⌊u⌋₊ + 1)| * atilc ((2 * ⌊u⌋₊ + 1) * c) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hμ hγnn) hann
          _ = |Work.FIPlan.gammaTrunc σ (2 * ⌊u⌋₊ + 1) * atilc ((2 * ⌊u⌋₊ + 1) * c)| := by
              rw [one_mul, abs_mul, abs_of_nonneg hann]
      · rw [if_neg hQ, abs_zero]
        exact abs_nonneg _
    · rw [if_neg h, if_neg (fun hh => h hh.2.1), abs_zero]
  have hcorrsum : (∑ c ∈ Finset.Icc 1 x,
        |(if ((((2 * ⌊u⌋₊ + 1 : ℕ) : ℝ) ≤ 2 * u) ∧ ((2 * ⌊u⌋₊ + 1) * c ≤ x)
              ∧ Work.FITop4.PiCond Pz (2 * ⌊u⌋₊ + 1))
           then (ArithmeticFunction.moebius (2 * ⌊u⌋₊ + 1) : ℝ)
                * Work.FIPlan.gammaTrunc σ (2 * ⌊u⌋₊ + 1)
                * atilc ((2 * ⌊u⌋₊ + 1) * c) else 0)|)
      ≤ C * ((((2 * ⌊u⌋₊ + 1).divisors.card : ℝ) ^ 3) / ((2 * ⌊u⌋₊ + 1 : ℕ) : ℝ))
          * AcountAtilC x := by
    refine le_trans (Finset.sum_le_sum hcorrpt) ?_
    exact hCorr x (2 * ⌊u⌋₊ + 1) hxC ha1 haasq σ
  have hXrx : (C * Cτ ^ 3) * (Real.log (x:ℝ)) ^ ((2:ℝ)^(26:ℕ))
      ≤ (x:ℝ) ^ ((5:ℝ)/8 * ((1:ℝ)/4 + η')) := by
    have h := hXr x hxr
    have hcast : ((2^26 : ℕ) : ℝ) = (2:ℝ)^(26:ℕ) := by push_cast; ring
    rwa [← Real.rpow_natCast (Real.log (x:ℝ)) (2^26), hcast] at h
  have harith : C * ((((2 * ⌊u⌋₊ + 1).divisors.card : ℝ) ^ 3) / ((2 * ⌊u⌋₊ + 1 : ℕ) : ℝ))
      ≤ (Real.log (x:ℝ)) ^ (-((2:ℝ)^(26:ℕ))) :=
    rwb_arith (2 * ⌊u⌋₊ + 1) C Cτ (((2 * ⌊u⌋₊ + 1 : ℕ) : ℝ)) (x:ℝ) (Real.log (x:ℝ)) η'
      hCpos hCτpos (by positivity) (hCτbd (2 * ⌊u⌋₊ + 1)) haD hx1 hLpos hXrx
  have hÃnn : (0:ℝ) ≤ AcountAtilC x := by
    rw [AcountAtilC, Work.FITop.AcountAtil, Submission.ASP.Acount]
    exact Finset.sum_nonneg (fun n _ => Work.FITop.atilFIa_nonneg n)
  have hstep2 : C * ((((2 * ⌊u⌋₊ + 1).divisors.card : ℝ) ^ 3) / ((2 * ⌊u⌋₊ + 1 : ℕ) : ℝ))
        * AcountAtilC x
      ≤ AcountAtilC x * (Real.log (x:ℝ)) ^ (-((2:ℝ)^(26:ℕ))) := by
    rw [mul_comm (C * ((((2 * ⌊u⌋₊ + 1).divisors.card : ℝ) ^ 3) / ((2 * ⌊u⌋₊ + 1 : ℕ) : ℝ)))]
    exact mul_le_mul_of_nonneg_left harith hÃnn
  have hgoal : (∑ c ∈ Finset.Icc 1 x, |Xpg x Pz c σ u|)
      ≤ (K + 1) * AcountAtilC x * (Real.log (x:ℝ)) ^ (-((2:ℝ)^(26:ℕ))) := by
    have h3 : K * AcountAtilC x * (Real.log (x:ℝ)) ^ (-((2:ℝ)^(26:ℕ)))
        + AcountAtilC x * (Real.log (x:ℝ)) ^ (-((2:ℝ)^(26:ℕ)))
        = (K + 1) * AcountAtilC x * (Real.log (x:ℝ)) ^ (-((2:ℝ)^(26:ℕ))) := by ring
    calc (∑ c ∈ Finset.Icc 1 x, |Xpg x Pz c σ u|)
        ≤ (∑ c ∈ Finset.Icc 1 x, |Xpg x Pz c σ ((⌊u⌋₊:ℕ):ℝ)|)
          + (∑ c ∈ Finset.Icc 1 x,
            |(if ((((2 * ⌊u⌋₊ + 1 : ℕ) : ℝ) ≤ 2 * u) ∧ ((2 * ⌊u⌋₊ + 1) * c ≤ x)
              ∧ Work.FITop4.PiCond Pz (2 * ⌊u⌋₊ + 1))
             then (ArithmeticFunction.moebius (2 * ⌊u⌋₊ + 1) : ℝ)
                  * Work.FIPlan.gammaTrunc σ (2 * ⌊u⌋₊ + 1)
                  * atilc ((2 * ⌊u⌋₊ + 1) * c) else 0)|) := hsum
      _ ≤ K * AcountAtilC x * (Real.log (x:ℝ)) ^ (-((2:ℝ)^(26:ℕ)))
          + (C * ((((2 * ⌊u⌋₊ + 1).divisors.card : ℝ) ^ 3) / ((2 * ⌊u⌋₊ + 1 : ℕ) : ℝ))
              * AcountAtilC x) := add_le_add hP41app hcorrsum
      _ ≤ K * AcountAtilC x * (Real.log (x:ℝ)) ^ (-((2:ℝ)^(26:ℕ)))
          + AcountAtilC x * (Real.log (x:ℝ)) ^ (-((2:ℝ)^(26:ℕ))) :=
          add_le_add le_rfl hstep2
      _ = (K + 1) * AcountAtilC x * (Real.log (x:ℝ)) ^ (-((2:ℝ)^(26:ℕ))) := h3
  exact hgoal

end

end Work.FIChain
