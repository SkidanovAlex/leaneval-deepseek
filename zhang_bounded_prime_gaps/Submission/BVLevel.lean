import Mathlib
import Submission.BVBasic
import Submission.LevelOfDistribution
import Submission.Commons.NumberTheory.PrimeNumberTheorem.theta_window_shift_powLog_largeN
import Submission.Commons.NumberTheory.Chebyshev.charSum_lamPrime_diff_bound
import Submission.Commons.Data.Finset.sum_Icc_comp_add
import Submission.Commons.Analysis.Asymptotics.eventually_log_rpow_le_mul
import Submission.Commons.NumberTheory.Totient.sum_inv_totient_Icc_le_powLog

open scoped BigOperators Topology
open Finset Filter

/-!
# From Bombieri--Vinogradov to the level of distribution

This module closes step (6) of the roadmap for the Bombieri--Vinogradov theorem
(`Submission/BOUNDED_GAPS_ROADMAP.md`, SESSION 35 §0): it converts the classical
Bombieri--Vinogradov theorem *for `Λ`* into the shifted-window level of
distribution for `θ` required by the sieve
(`Commons.NumberTheory.MaynardSieve.levelOfDistribution`).

The Bombieri--Vinogradov input is packaged as `CleanBV`, the character-sup form
of the theorem (which is what the Basic Mean Value Theorem supplies, after the
primitive-character reduction of Vaughan §1).  The two error terms produced when
passing from `Λ` to `θ` are handled as in Polymath8a §4.2:

* `Δ(θ·1_W) − Δ(Λ·1_W) = Δ((θ−Λ)·1_W)`, and `θ − Λ` is supported on prime
  powers `p^k`, `k ≥ 2`, so its total mass in the window is
  `(ψ − θ)(2x+h) ≪ √x`; summed over the `Q ≤ x^ϑ` moduli this is
  `Q√x ≤ x^{1/2+ϑ} ≪ x log^{-A}x` since `ϑ < 1/2`;
* the shift in the normalization (from `x/φ(q)` to `(1/φ(q))Σ_{(m,q)=1}θ(m)`)
  costs `≪ x log^{-A}x/φ(q)`, which is absorbed by `Σ_q 1/φ(q) ≪ log²x`
  (Polymath8a: `Σ_{(m,q)=1}θ(m) = (1+o(1))x`).
-/

namespace Commons.NumberTheory.MaynardSieve

noncomputable section

set_option maxHeartbeats 4000000

open Submission.BV

/-! ## §1. The Bombieri--Vinogradov input. -/

/-- **The clean Bombieri--Vinogradov theorem**, in the character-sup form:
for every `A ≥ 1` there are `B, C` such that for all large `X`,
for every `Q ≤ √X/(log X)^B`,

    Σ_{q ≤ Q} (1/φ(q)) Σ_{χ mod q} sup_{y ≤ X} ‖ψ(y,χ) − δ(χ)y‖ ≤ C·X·(log X)^{-A}.

This is the output of the Basic Mean Value Theorem plus the primitive-character
reduction and Siegel--Walfisz (Vaughan, *The Bombieri--Vinogradov theorem*, §1). -/
def CleanBV : Prop :=
  ∀ A : ℝ, 1 ≤ A → ∃ B C : ℝ, 0 < C ∧ ∀ᶠ X : ℕ in atTop, ∀ Q : ℕ,
    (Q : ℝ) ≤ Real.sqrt (X : ℝ) / (Real.log (X : ℝ)) ^ B →
    (∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℕ) : ℝ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ q, charSup X χ) ≤
      C * (X : ℝ) * (Real.log (X : ℝ)) ^ (-A)

/-! ## §2. `Λ` versus `θ`. -/

lemma vonMangoldt_sub_thetaNat (n : ℕ) :
    ArithmeticFunction.vonMangoldt n - thetaNat n =
      if n.Prime then 0 else ArithmeticFunction.vonMangoldt n := by
  by_cases h : n.Prime
  · rw [if_pos h, thetaNat, if_pos h, ArithmeticFunction.vonMangoldt_apply_prime h, sub_self]
  · rw [if_neg h, thetaNat, if_neg h, sub_zero]

lemma thetaNat_le_vonMangoldt (n : ℕ) : thetaNat n ≤ ArithmeticFunction.vonMangoldt n := by
  rw [← sub_nonneg, vonMangoldt_sub_thetaNat]
  by_cases h : n.Prime
  · rw [if_pos h]
  · rw [if_neg h]
    exact ArithmeticFunction.vonMangoldt_nonneg

/-- The mass of `Λ - θ` over an interval is at most `ψ - θ` at the right endpoint
(everything beyond the primes is a non-negative contribution to `ψ - θ`). -/
lemma sum_Ioc_lam_sub_theta_le (u v : ℕ) :
    (∑ n ∈ Finset.Ioc u v, (ArithmeticFunction.vonMangoldt n - thetaNat n)) ≤
      Chebyshev.psi (v : ℝ) - Chebyshev.theta (v : ℝ) := by
  have hsplit := Finset.sum_filter_add_sum_filter_not (s := Finset.Ioc u v)
    (p := fun n : ℕ => n.Prime)
    (f := fun n => ArithmeticFunction.vonMangoldt n - thetaNat n)
  have hprime : (∑ n ∈ Finset.Ioc u v with n.Prime,
      (ArithmeticFunction.vonMangoldt n - thetaNat n)) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    rw [Finset.mem_filter] at hn
    rw [vonMangoldt_sub_thetaNat, if_pos hn.2]
  have hnon : (∑ n ∈ Finset.Ioc u v with ¬ n.Prime,
      (ArithmeticFunction.vonMangoldt n - thetaNat n))
      = ∑ n ∈ Finset.Ioc u v with ¬ n.Prime, ArithmeticFunction.vonMangoldt n := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.mem_filter] at hn
    rw [vonMangoldt_sub_thetaNat, if_neg hn.2]
  rw [← hsplit, hprime, hnon, zero_add]
  rw [Commons.NumberTheory.Chebyshev.CharSumLamPrime.psi_sub_theta_eq_sum_nonprime,
    Nat.floor_natCast]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    rw [Finset.mem_filter] at hn ⊢
    exact ⟨Finset.mem_Ioc.mpr ⟨by have := (Finset.mem_Ioc.mp hn.1).1; omega,
      (Finset.mem_Ioc.mp hn.1).2⟩, hn.2⟩
  · intro n _ _
    exact ArithmeticFunction.vonMangoldt_nonneg


/-! ## §3. Window forms of the discrepancy, and of `ψ(y;q,a)`. -/

/-- `Δ(Λ·1_{(u,v]}; a(q))` as the difference of two `psiAP` values. -/
lemma psiAP_sub_eq_sum_Ioc (u v q a : ℕ) (huv : u ≤ v) :
    psiAP v q a - psiAP u q a =
      ∑ n ∈ Finset.Ioc u v,
        (if n % q = a % q then ArithmeticFunction.vonMangoldt n else 0) := by
  unfold psiAP
  rw [Finset.sum_filter, Finset.sum_filter]
  have hsub : Finset.range (u + 1) ⊆ Finset.range (v + 1) := by
    intro n hn
    rw [Finset.mem_range] at hn ⊢
    omega
  have hset : Finset.range (v + 1) \ Finset.range (u + 1) = Finset.Ioc u v := by
    ext n
    simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_Ioc]
    omega
  rw [← Finset.sum_sdiff hsub, hset]
  ring

/-- Reindexing the shifted window sum over `n ∈ [x,2x]` to `m = n + h` in `[x+h,2x+h]`,
as an `Ioc` sum. -/
lemma discShift_eq_window (f : ℕ → ℝ) (x q a h : ℕ) (hx : 1 ≤ x) :
    discShift f x q a h =
      (∑ m ∈ Finset.Ioc (x + h - 1) (2 * x + h),
          (if m % q = a % q then f m else 0)) -
        (1 / ((q.totient : ℕ) : ℝ)) *
          (∑ m ∈ Finset.Ioc (x + h - 1) (2 * x + h),
            (if m.Coprime q then f m else 0)) := by
  unfold discShift
  rw [Finset.sum_filter, Finset.sum_filter]
  have h1 : (∑ n ∈ Finset.Icc x (2 * x), (if (n + h) % q = a % q then f (n + h) else 0)) =
      ∑ m ∈ Finset.Icc (x + h) (2 * x + h), (if m % q = a % q then f m else 0) := by
    exact Commons.Data.Finset.sum_Icc_comp_add x (2 * x) h
      (fun m => (if m % q = a % q then f m else 0))
  have h2 : (∑ n ∈ Finset.Icc x (2 * x), (if (n + h).Coprime q then f (n + h) else 0)) =
      ∑ m ∈ Finset.Icc (x + h) (2 * x + h), (if m.Coprime q then f m else 0) := by
    exact Commons.Data.Finset.sum_Icc_comp_add x (2 * x) h
      (fun m => (if m.Coprime q then f m else 0))
  have hIcc : Finset.Icc (x + h) (2 * x + h) = Finset.Ioc (x + h - 1) (2 * x + h) := by
    ext m
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [h1, h2, hIcc]


/-! ## §4. The pointwise comparison `Δ(θ) ↔ Δ(Λ)`. -/

/-- `psiAP` is a sum of non-negative terms. -/
lemma psiAP_nonneg (y q a : ℕ) : 0 ≤ psiAP y q a := by
  unfold psiAP
  exact Finset.sum_nonneg (fun n _ => ArithmeticFunction.vonMangoldt_nonneg)

/-- An explicit upper bound for the values occurring in `discSupPsi`. -/
lemma discSupPsi_bddAbove (X q : ℕ) :
    BddAbove ((fun pa : ℕ × ℕ =>
      |psiAP pa.1 q pa.2 - (pa.1 : ℝ) / ((q.totient : ℕ) : ℝ)|) ''
      (Set.Icc 1 X ×ˢ {a : ℕ | a.Coprime q})) := by
  refine ⟨(∑ n ∈ Finset.range (X + 1), ArithmeticFunction.vonMangoldt n) +
      (X : ℝ) / ((q.totient : ℕ) : ℝ), ?_⟩
  rintro v ⟨⟨y, a⟩, ⟨hy, _ha⟩, rfl⟩
  have hyX : y ≤ X := hy.2
  have hpsi : psiAP y q a ≤ ∑ n ∈ Finset.range (X + 1), ArithmeticFunction.vonMangoldt n := by
    have h1 : psiAP y q a ≤ ∑ n ∈ Finset.range (y + 1), ArithmeticFunction.vonMangoldt n := by
      unfold psiAP
      rw [Finset.sum_filter]
      exact Finset.sum_le_sum (fun n _ => by split_ifs <;> simp [ArithmeticFunction.vonMangoldt_nonneg])
    have h2 : (∑ n ∈ Finset.range (y + 1), ArithmeticFunction.vonMangoldt n)
        ≤ ∑ n ∈ Finset.range (X + 1), ArithmeticFunction.vonMangoldt n := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n hn; rw [Finset.mem_range] at hn ⊢; omega
      · intro n _ _; exact ArithmeticFunction.vonMangoldt_nonneg
    exact le_trans h1 h2
  have hycast : (y : ℝ) ≤ (X : ℝ) := by exact_mod_cast hyX
  have hφnn : (0 : ℝ) ≤ ((q.totient : ℕ) : ℝ) := Nat.cast_nonneg _
  have hydiv : 0 ≤ (y : ℝ) / ((q.totient : ℕ) : ℝ) := by positivity
  calc |psiAP y q a - (y : ℝ) / ((q.totient : ℕ) : ℝ)|
      ≤ psiAP y q a + (y : ℝ) / ((q.totient : ℕ) : ℝ) := by
        rw [abs_le]
        exact ⟨by linarith [psiAP_nonneg y q a, hydiv], by linarith [psiAP_nonneg y q a]⟩
    _ ≤ (∑ n ∈ Finset.range (X + 1), ArithmeticFunction.vonMangoldt n) +
          (X : ℝ) / ((q.totient : ℕ) : ℝ) := by
        refine add_le_add hpsi ?_
        exact div_le_div_of_nonneg_right hycast hφnn

/-- `discSupPsi` is non-negative, for `x ≥ 1` (the residue class `1` is primitive). -/
lemma discSupPsi_nonneg (X q : ℕ) (hX : 1 ≤ X) : 0 ≤ discSupPsi X q := by
  refine Real.sSup_nonneg (s := ((fun pa : ℕ × ℕ =>
      |psiAP pa.1 q pa.2 - (pa.1 : ℝ) / ((q.totient : ℕ) : ℝ)|) ''
      (Set.Icc 1 X ×ˢ {a : ℕ | a.Coprime q}))) ?_
  rintro v ⟨⟨y, a⟩, ⟨hy, _ha⟩, rfl⟩
  exact abs_nonneg _

/-- The defining property of `discSupPsi`. -/
lemma abs_psiAP_sub_le_discSupPsi {X q a y : ℕ} (hy : y ∈ Finset.Icc 1 X)
    (ha : a.Coprime q) :
    |psiAP y q a - (y : ℝ) / ((q.totient : ℕ) : ℝ)| ≤ discSupPsi X q := by
  refine le_csSup (discSupPsi_bddAbove X q) ?_
  exact ⟨(y, a), ⟨by simpa using hy, ha⟩, rfl⟩

/-- `discSupPsi` is monotone in the truncation point. -/
lemma discSupPsi_mono (q : ℕ) {X Y : ℕ} (hX : 1 ≤ X) (hXY : X ≤ Y) :
    discSupPsi X q ≤ discSupPsi Y q := by
  refine Real.sSup_le (fun v hv => ?_) (discSupPsi_nonneg Y q (le_trans hX hXY))
  rcases hv with ⟨⟨y, a⟩, ⟨hy, ha⟩, rfl⟩
  exact abs_psiAP_sub_le_discSupPsi
    (X := Y) (q := q) (a := a) (y := y)
    (Finset.mem_Icc.mpr ⟨hy.1, le_trans hy.2 hXY⟩) ha

/-- **The pointwise comparison.**  The shifted-window discrepancy of `θ` in a
primitive residue class is bounded by twice the `Λ`-discrepancy (in the
`y/φ(q)` normalization), plus the total mass of `Λ - θ` in the window, plus the
deviation of the normalizing main term from `x`. -/
lemma discShift_thetaNat_le (x q a h : ℕ) (hx : 1 ≤ x) (hq : 1 ≤ q) (ha : a.Coprime q) :
    |discShift (fun n => thetaNat n) x q a h|
      ≤ 2 * discSupPsi (3 * x + h) q
        + (Chebyshev.psi ((2 * x + h : ℕ) : ℝ) -
            Chebyshev.theta ((2 * x + h : ℕ) : ℝ))
        + (|(x : ℝ) - (∑ m ∈ Finset.Ioc (x + h - 1) (2 * x + h),
              (if m.Coprime q then thetaNat m else 0))| + 1) /
            ((q.totient : ℕ) : ℝ) := by
  have hφpos : 0 < ((q.totient : ℕ) : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (by omega)
  set S : ℝ := ∑ m ∈ Finset.Ioc (x + h - 1) (2 * x + h),
    (if m % q = a % q then thetaNat m else 0) with hS
  set SL : ℝ := ∑ m ∈ Finset.Ioc (x + h - 1) (2 * x + h),
    (if m % q = a % q then ArithmeticFunction.vonMangoldt m else 0) with hSL
  set T : ℝ := ∑ m ∈ Finset.Ioc (x + h - 1) (2 * x + h),
    (if m.Coprime q then thetaNat m else 0) with hT
  -- (1) the mass of `Λ - θ`
  have hdiff : |S - SL| ≤ Chebyshev.psi ((2 * x + h : ℕ) : ℝ) -
      Chebyshev.theta ((2 * x + h : ℕ) : ℝ) := by
    have hsub : S - SL = -(∑ m ∈ Finset.Ioc (x + h - 1) (2 * x + h),
        (if m % q = a % q then ArithmeticFunction.vonMangoldt m - thetaNat m else 0)) := by
      rw [hS, hSL, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro m _
      by_cases h : m % q = a % q <;> simp [h]
    rw [hsub, abs_neg]
    have hnn : 0 ≤ ∑ m ∈ Finset.Ioc (x + h - 1) (2 * x + h),
        (if m % q = a % q then ArithmeticFunction.vonMangoldt m - thetaNat m else 0) :=
      Finset.sum_nonneg (fun m _ => by
        by_cases h : m % q = a % q <;> simp [h, sub_nonneg.mpr (thetaNat_le_vonMangoldt m)])
    rw [abs_of_nonneg hnn]
    exact (Finset.sum_le_sum (fun m _ => by
        by_cases h : m % q = a % q <;> simp [h, sub_nonneg.mpr (thetaNat_le_vonMangoldt m)])).trans
        (sum_Ioc_lam_sub_theta_le _ _)
  -- (2) the `Λ`-window against `x/φ(q)`
  have hSLid : SL = psiAP (2 * x + h) q a - psiAP (x + h - 1) q a := by
    rw [hSL, psiAP_sub_eq_sum_Ioc (x + h - 1) (2 * x + h) q a (by omega)]
  have hA2 : |psiAP (2 * x + h) q a - ((2 * x + h : ℕ) : ℝ) / ((q.totient : ℕ) : ℝ)|
      ≤ discSupPsi (3 * x + h) q :=
    abs_psiAP_sub_le_discSupPsi
      (X := 3 * x + h) (q := q) (a := a) (y := 2 * x + h)
      (Finset.mem_Icc.mpr ⟨by omega, by omega⟩) ha
  have hA1 : |psiAP (x + h - 1) q a - ((x + h - 1 : ℕ) : ℝ) / ((q.totient : ℕ) : ℝ)|
      ≤ discSupPsi (3 * x + h) q := by
    rcases Nat.eq_zero_or_pos (x + h - 1) with hzero | hpos
    · have hz : ArithmeticFunction.vonMangoldt 0 = 0 := by
        rw [ArithmeticFunction.vonMangoldt_eq_zero_iff, isPrimePow_nat_iff]
        rintro ⟨p, k, hp, _hk, hpk⟩
        have : 0 < p ^ k := pow_pos hp.pos k
        omega
      have h0 : psiAP 0 q a = 0 := by
        unfold psiAP
        refine Finset.sum_eq_zero (fun n hn => ?_)
        rw [Finset.mem_filter, Finset.mem_range] at hn
        have hn0 : n = 0 := by omega
        rw [hn0, hz]
      rw [hzero, h0]
      simp only [Nat.cast_zero, zero_div, sub_zero, abs_zero]
      exact discSupPsi_nonneg _ _ (by omega)
    · exact abs_psiAP_sub_le_discSupPsi
        (X := 3 * x + h) (q := q) (a := a) (y := x + h - 1)
        (Finset.mem_Icc.mpr ⟨hpos, by omega⟩) ha
  have hcast : ((2 * x + h : ℕ) : ℝ) - ((x + h - 1 : ℕ) : ℝ) = (x : ℝ) + 1 := by
    have h1 : (x + h - 1 : ℕ) + 1 = x + h := by omega
    have h2 := congrArg (fun t : ℕ => (t : ℝ)) h1
    push_cast at h2
    have h3 : ((2 * x + h : ℕ) : ℝ) = 2 * (x : ℝ) + (h : ℝ) := by push_cast; ring
    have h4 : ((x + h - 1 : ℕ) : ℝ) = (x : ℝ) + (h : ℝ) - 1 := by linarith
    linarith
  have hSLbound : |SL - (x : ℝ) / ((q.totient : ℕ) : ℝ)|
      ≤ 2 * discSupPsi (3 * x + h) q + 1 / ((q.totient : ℕ) : ℝ) := by
    have hkey : SL - (x : ℝ) / ((q.totient : ℕ) : ℝ) =
        (psiAP (2 * x + h) q a - ((2 * x + h : ℕ) : ℝ) / ((q.totient : ℕ) : ℝ)) -
          (psiAP (x + h - 1) q a - ((x + h - 1 : ℕ) : ℝ) / ((q.totient : ℕ) : ℝ)) +
          (1 / ((q.totient : ℕ) : ℝ)) := by
      have ha_eq : ((2 * x + h : ℕ) : ℝ) = (x : ℝ) + 1 + ((x + h - 1 : ℕ) : ℝ) := by
        linarith [hcast]
      rw [hSLid, ha_eq]
      ring
    rw [hkey]
    calc |(psiAP (2 * x + h) q a - ((2 * x + h : ℕ) : ℝ) / ((q.totient : ℕ) : ℝ)) -
          (psiAP (x + h - 1) q a - ((x + h - 1 : ℕ) : ℝ) / ((q.totient : ℕ) : ℝ)) +
          (1 / ((q.totient : ℕ) : ℝ))|
        ≤ |(psiAP (2 * x + h) q a - ((2 * x + h : ℕ) : ℝ) / ((q.totient : ℕ) : ℝ)) -
            (psiAP (x + h - 1) q a - ((x + h - 1 : ℕ) : ℝ) / ((q.totient : ℕ) : ℝ))| +
          |(1 / ((q.totient : ℕ) : ℝ))| := abs_add_le _ _
      _ ≤ (|psiAP (2 * x + h) q a - ((2 * x + h : ℕ) : ℝ) / ((q.totient : ℕ) : ℝ)| +
            |psiAP (x + h - 1) q a - ((x + h - 1 : ℕ) : ℝ) / ((q.totient : ℕ) : ℝ)|) +
          |(1 / ((q.totient : ℕ) : ℝ))| := by
          refine add_le_add ?_ le_rfl
          simpa [abs_sub_comm] using abs_sub_le
            (psiAP (2 * x + h) q a - ((2 * x + h : ℕ) : ℝ) / ((q.totient : ℕ) : ℝ))
            0 (psiAP (x + h - 1) q a - ((x + h - 1 : ℕ) : ℝ) / ((q.totient : ℕ) : ℝ))
      _ ≤ discSupPsi (3 * x + h) q + discSupPsi (3 * x + h) q + 1 / ((q.totient : ℕ) : ℝ) := by
          refine add_le_add (add_le_add hA2 hA1) ?_
          rw [abs_of_pos (by positivity)]
      _ = 2 * discSupPsi (3 * x + h) q + 1 / ((q.totient : ℕ) : ℝ) := by ring
  -- (3) assemble
  rw [discShift_eq_window (fun n => thetaNat n) x q a h hx, ← hS, ← hT]
  have hmain : |S - T / ((q.totient : ℕ) : ℝ)|
      ≤ |S - SL| + |SL - (x : ℝ) / ((q.totient : ℕ) : ℝ)|
        + |(x : ℝ) - T| / ((q.totient : ℕ) : ℝ) := by
    have h1 : S - T / ((q.totient : ℕ) : ℝ) =
        (S - SL) + (SL - (x : ℝ) / ((q.totient : ℕ) : ℝ)) +
          ((x : ℝ) - T) / ((q.totient : ℕ) : ℝ) := by ring
    rw [h1]
    calc |(S - SL) + (SL - (x : ℝ) / ((q.totient : ℕ) : ℝ)) +
            ((x : ℝ) - T) / ((q.totient : ℕ) : ℝ)|
        ≤ |(S - SL) + (SL - (x : ℝ) / ((q.totient : ℕ) : ℝ))| +
            |((x : ℝ) - T) / ((q.totient : ℕ) : ℝ)| := abs_add_le _ _
      _ ≤ (|S - SL| + |SL - (x : ℝ) / ((q.totient : ℕ) : ℝ)|) +
            |((x : ℝ) - T) / ((q.totient : ℕ) : ℝ)| := by
          refine add_le_add ?_ le_rfl
          exact abs_add_le _ _
      _ = (|S - SL| + |SL - (x : ℝ) / ((q.totient : ℕ) : ℝ)|) +
            |(x : ℝ) - T| / ((q.totient : ℕ) : ℝ) := by
          rw [abs_div, abs_of_pos hφpos]
  have hform : (1 : ℝ) / ((q.totient : ℕ) : ℝ) * T = T / ((q.totient : ℕ) : ℝ) := by ring
  rw [hform]
  refine hmain.trans ?_
  rw [add_div]
  linarith [hdiff, hSLbound, hφpos]

/-! ## §5. From clean Bombieri--Vinogradov to the level of distribution. -/

/-- Domination of any fixed power of the logarithm by `x^δ`, eventually. -/
private lemma eventually_log_pow_le_rpow {B δ c : ℝ} (hδ : 0 < δ) (hc : 0 < c) :
    ∀ᶠ x : ℕ in atTop, (Real.log (x : ℝ)) ^ B ≤ c * (x : ℝ) ^ δ := by
  have h : (fun x : ℝ => Real.log x ^ B) =o[atTop] (fun x : ℝ => x ^ δ) :=
    isLittleO_log_rpow_rpow_atTop B hδ
  have h2 := h.comp_tendsto tendsto_natCast_atTop_atTop
  filter_upwards [h2.def hc, Filter.eventually_ge_atTop (1 : ℕ)] with N hN hN1
  simp only [Function.comp_apply] at hN
  rwa [Real.norm_of_nonneg (Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast hN1)) B),
      Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) δ)] at hN

/-- The shifted window sum defining the third term of `discShift_thetaNat_le`,
rewritten as the sum appearing in `theta_window_shift_powLog_largeN`. -/
private lemma window_coprime_theta_eq (x q h : ℕ) (hx : 1 ≤ x) :
    (∑ m ∈ Finset.Ioc (x + h - 1) (2 * x + h),
        (if m.Coprime q then thetaNat m else 0)) =
      ∑ m ∈ (Finset.Icc (x + h) (2 * x + h)).filter (fun m => m.Coprime q),
        (if m.Prime then Real.log (m : ℝ) else 0) := by
  have hset : Finset.Ioc (x + h - 1) (2 * x + h) = Finset.Icc (x + h) (2 * x + h) := by
    ext m
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  rw [hset, Finset.sum_filter]
  rfl

theorem levelOfDistribution_of_cleanBV (h : CleanBV) {ϑ : ℝ} (hϑ : ϑ < 1 / 2) :
    levelOfDistribution ϑ := by
  intro A hA C
  obtain ⟨B, Cbv, hCbvpos, hbv⟩ := h (A + 3) (by linarith)
  obtain ⟨C₀₀, hC₀₀⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  set C₀ : ℝ := max C₀₀ 1 with hC₀def
  have hC₀pos : 0 < C₀ := by rw [hC₀def]; exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hC₀ : ∀ x : ℝ, Chebyshev.psi x - Chebyshev.theta x ≤ C₀ * Real.sqrt x := by
    intro x
    refine le_trans (hC₀₀ x) ?_
    have : C₀₀ ≤ C₀ := by rw [hC₀def]; exact le_max_left C₀₀ 1
    exact mul_le_mul_of_nonneg_right this (Real.sqrt_nonneg x)
  obtain ⟨Cθ, hCθpos, hCθ⟩ :=
    Commons.NumberTheory.PrimeNumberTheorem.theta_window_shift_powLog_largeN (A + 3) (by linarith)
  obtain ⟨Cφ, hCφpos, hCφ⟩ := Commons.NumberTheory.Totient.sum_inv_totient_Icc_le_powLog
  have hδ : 0 < 1 / 2 - ϑ := by linarith
  -- ### eventual statements
  have hmap : Tendsto (fun x : ℕ => 3 * x + C) atTop atTop := by
    rw [Filter.tendsto_atTop]
    intro b
    filter_upwards [Filter.eventually_ge_atTop b] with x hx
    omega
  have hlognat : ∀ K : ℝ, ∀ᶠ x : ℕ in atTop, K ≤ Real.log (x : ℝ) := fun K =>
    tendsto_natCast_atTop_atTop.eventually
      (Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop K))
  have hbig : ∀ᶠ x : ℕ in atTop, 2 ≤ x ∧ C ≤ x ∧ (2 : ℝ) ≤ Real.log (x : ℝ) := by
    filter_upwards [Filter.eventually_ge_atTop (max 2 C), hlognat 2] with x hx hx2
    exact ⟨le_trans (le_max_left 2 C) hx, le_trans (le_max_right 2 C) hx, hx2⟩
  have hbv' : ∀ᶠ x : ℕ in atTop, ∀ Q : ℕ,
      (Q : ℝ) ≤ Real.sqrt (((3 * x + C) : ℕ) : ℝ) /
          (Real.log (((3 * x + C) : ℕ) : ℝ)) ^ B →
      (∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℕ) : ℝ)⁻¹ *
          ∑ χ : DirichletCharacter ℂ q, charSup (3 * x + C) χ) ≤
        Cbv * (((3 * x + C) : ℕ) : ℝ) *
          (Real.log (((3 * x + C) : ℕ) : ℝ)) ^ (-(A + 3)) :=
    hmap.eventually hbv
  have hQle : ∀ᶠ x : ℕ in atTop,
      (x : ℝ) ^ ϑ ≤ Real.sqrt (((3 * x + C) : ℕ) : ℝ) /
        (Real.log (((3 * x + C) : ℕ) : ℝ)) ^ B := by
    have h1 : ∀ᶠ X : ℕ in atTop, (Real.log (X : ℝ)) ^ B ≤
        (1 / (2 * (4 : ℝ) ^ (1 / 2 - ϑ))) * (X : ℝ) ^ (1 / 2 - ϑ) :=
      eventually_log_pow_le_rpow (B := B) (δ := 1 / 2 - ϑ) hδ (by positivity)
    have h2 : ∀ᶠ x : ℕ in atTop, (Real.log (((3 * x + C) : ℕ) : ℝ)) ^ B ≤
        (1 / (2 * (4 : ℝ) ^ (1 / 2 - ϑ))) * (((3 * x + C) : ℕ) : ℝ) ^ (1 / 2 - ϑ) :=
      hmap.eventually h1
    filter_upwards [h2, hbig, Filter.eventually_ge_atTop 1] with x hx hxbig hx1
    obtain ⟨hx2, hxC, hlog2⟩ := hxbig
    have hxpos : (0 : ℝ) < (x : ℝ) := by positivity
    have hx1' : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx1
    have hCx : (C : ℝ) ≤ (x : ℝ) := by exact_mod_cast hxC
    have hXeq : (((3 * x + C) : ℕ) : ℝ) = 3 * (x : ℝ) + (C : ℝ) := by push_cast; ring
    have hXle : 3 * (x : ℝ) + (C : ℝ) ≤ 4 * (x : ℝ) := by linarith
    have hXpos : 0 < 3 * (x : ℝ) + (C : ℝ) := by positivity
    have hXpow : (3 * (x : ℝ) + (C : ℝ)) ^ (1 / 2 - ϑ) ≤
        4 ^ (1 / 2 - ϑ) * (x : ℝ) ^ (1 / 2 - ϑ) := by
      calc (3 * (x : ℝ) + (C : ℝ)) ^ (1 / 2 - ϑ) ≤ (4 * (x : ℝ)) ^ (1 / 2 - ϑ) :=
            Real.rpow_le_rpow hXpos.le hXle (by linarith)
        _ = 4 ^ (1 / 2 - ϑ) * (x : ℝ) ^ (1 / 2 - ϑ) := Real.mul_rpow (by norm_num) hxpos.le
    have hlogle : (Real.log (((3 * x + C) : ℕ) : ℝ)) ^ B ≤ (x : ℝ) ^ (1 / 2 - ϑ) := by
      have hstep : (1 / (2 * (4 : ℝ) ^ (1 / 2 - ϑ))) *
          (4 ^ (1 / 2 - ϑ) * (x : ℝ) ^ (1 / 2 - ϑ)) = (x : ℝ) ^ (1 / 2 - ϑ) / 2 := by
        field_simp
      calc (Real.log (((3 * x + C) : ℕ) : ℝ)) ^ B
          ≤ (1 / (2 * (4 : ℝ) ^ (1 / 2 - ϑ))) * (3 * (x : ℝ) + (C : ℝ)) ^ (1 / 2 - ϑ) := by
            rw [← hXeq]; exact hx
        _ ≤ (1 / (2 * (4 : ℝ) ^ (1 / 2 - ϑ))) *
              (4 ^ (1 / 2 - ϑ) * (x : ℝ) ^ (1 / 2 - ϑ)) :=
            mul_le_mul_of_nonneg_left hXpow (by positivity)
        _ = (x : ℝ) ^ (1 / 2 - ϑ) / 2 := hstep
        _ ≤ (x : ℝ) ^ (1 / 2 - ϑ) := by
            linarith [Real.rpow_pos_of_pos hxpos (1 / 2 - ϑ)]
    have hlogXpos : 0 < (Real.log (((3 * x + C) : ℕ) : ℝ)) ^ B := by
      refine Real.rpow_pos_of_pos ?_ B
      rw [hXeq]
      exact Real.log_pos (by linarith)
    rw [le_div_iff₀ hlogXpos]
    have hprod : (x : ℝ) ^ ϑ * (Real.log (((3 * x + C) : ℕ) : ℝ)) ^ B ≤
        (x : ℝ) ^ ϑ * (x : ℝ) ^ (1 / 2 - ϑ) :=
      mul_le_mul_of_nonneg_left hlogle (Real.rpow_nonneg hxpos.le ϑ)
    have hprod2 : (x : ℝ) ^ ϑ * (x : ℝ) ^ (1 / 2 - ϑ) = Real.sqrt (x : ℝ) := by
      rw [← Real.rpow_add hxpos, Real.sqrt_eq_rpow]
      norm_num
    have hsqrtle : Real.sqrt (x : ℝ) ≤ Real.sqrt (((3 * x + C) : ℕ) : ℝ) := by
      apply Real.sqrt_le_sqrt
      rw [hXeq]; linarith
    rw [hprod2] at hprod
    linarith [hprod, hsqrtle]
  -- ### absorption facts
  have hlog3 : ∀ᶠ x : ℕ in atTop, (48 * Cbv) ≤ (Real.log (x : ℝ)) ^ 3 := by
    filter_upwards [hlognat (max 1 (48 * Cbv))] with x hx
    have h1 : (48 * Cbv) ≤ Real.log (x : ℝ) := le_trans (le_max_right 1 (48 * Cbv)) hx
    have h0 : (1 : ℝ) ≤ Real.log (x : ℝ) := le_trans (le_max_left 1 (48 * Cbv)) hx
    have hL2 : (1 : ℝ) ≤ (Real.log (x : ℝ)) ^ 2 := by nlinarith [h0]
    calc (48 * Cbv) ≤ Real.log (x : ℝ) := h1
      _ = Real.log (x : ℝ) * 1 := by ring
      _ ≤ Real.log (x : ℝ) * (Real.log (x : ℝ)) ^ 2 :=
          mul_le_mul_of_nonneg_left hL2 (by linarith)
      _ = (Real.log (x : ℝ)) ^ 3 := by ring
  have hlogφ : ∀ᶠ x : ℕ in atTop, (12 * (Cφ * Cθ)) ≤ Real.log (x : ℝ) := by
    filter_upwards [hlognat (max 1 (12 * (Cφ * Cθ)))] with x hx
    linarith [le_max_right (1 : ℝ) (12 * (Cφ * Cθ)), hx]
  have hpow : ∀ᶠ x : ℕ in atTop,
      (6 * C₀) * (Real.log (x : ℝ)) ^ A ≤ (x : ℝ) ^ (1 / 2 - ϑ) := by
    have h1 := eventually_log_pow_le_rpow (B := A) (δ := 1 / 2 - ϑ) hδ
      (by positivity : (0 : ℝ) < 1 / (6 * C₀))
    filter_upwards [h1] with x hx
    have h2 : (Real.log (x : ℝ)) ^ A * (6 * C₀) ≤
        ((1 / (6 * C₀)) * (x : ℝ) ^ (1 / 2 - ϑ)) * (6 * C₀) :=
      mul_le_mul_of_nonneg_right hx (by positivity)
    have h3 : ((1 / (6 * C₀)) * (x : ℝ) ^ (1 / 2 - ϑ)) * (6 * C₀) =
        (x : ℝ) ^ (1 / 2 - ϑ) := by field_simp
    rw [h3] at h2
    calc (6 * C₀) * (Real.log (x : ℝ)) ^ A = (Real.log (x : ℝ)) ^ A * (6 * C₀) := by ring
      _ ≤ (x : ℝ) ^ (1 / 2 - ϑ) := h2
  have hlogA2 : ∀ᶠ x : ℕ in atTop,
      (12 * Cφ) * (Real.log (x : ℝ)) ^ (A + 2) ≤ (x : ℝ) := by
    have h1 := eventually_log_pow_le_rpow (B := A + 2) (δ := 1) (by norm_num)
      (by positivity : (0 : ℝ) < 1 / (12 * Cφ))
    filter_upwards [h1] with x hx
    have h2 : (Real.log (x : ℝ)) ^ (A + 2) * (12 * Cφ) ≤
        ((1 / (12 * Cφ)) * (x : ℝ) ^ (1 : ℝ)) * (12 * Cφ) :=
      mul_le_mul_of_nonneg_right hx (by positivity)
    have h3 : ((1 / (12 * Cφ)) * (x : ℝ) ^ (1 : ℝ)) * (12 * Cφ) = (x : ℝ) := by
      rw [Real.rpow_one]; field_simp
    rw [h3] at h2
    calc (12 * Cφ) * (Real.log (x : ℝ)) ^ (A + 2) = (Real.log (x : ℝ)) ^ (A + 2) * (12 * Cφ) := by
          ring
      _ ≤ (x : ℝ) := h2
  -- ### main
  filter_upwards [hbig, hbv', hQle, hlog3, hlogφ, hpow, hlogA2] with x hbigx hbvx hQlex hlog3x
    hlogφx hpowx hlogA2x
  intro Q hQ
  obtain ⟨hx2, hxC, hlog2⟩ := hbigx
  have hx1 : 1 ≤ x := by omega
  have hxpos : (0 : ℝ) < (x : ℝ) := by positivity
  have hxnn : (0 : ℝ) ≤ (x : ℝ) := hxpos.le
  have hCx : (C : ℝ) ≤ (x : ℝ) := by exact_mod_cast hxC
  have hlogpos : 0 < Real.log (x : ℝ) := by linarith
  have hlogApos : 0 < (Real.log (x : ℝ)) ^ A := Real.rpow_pos_of_pos hlogpos A
  rw [show (x : ℝ) * (Real.log (x : ℝ)) ^ (-A) = (x : ℝ) / (Real.log (x : ℝ)) ^ A by
    rw [Real.rpow_neg hlogpos.le, div_eq_mul_inv]]
  have hQrootB : (Q : ℝ) ≤ Real.sqrt (((3 * x + C) : ℕ) : ℝ) /
      (Real.log (((3 * x + C) : ℕ) : ℝ)) ^ B := le_trans hQ hQlex
  -- ### per modulus
  have hperq : ∀ q ∈ Finset.Icc 1 Q,
      (Finset.range (C + 1)).sup' ⟨0, Finset.mem_range.mpr (Nat.succ_pos C)⟩
        (fun h => discSupShift x q h) ≤
      2 * discSupPsi (3 * x + C) q + C₀ * Real.sqrt (((2 * x + C) : ℕ) : ℝ) +
        (Cθ * (x : ℝ) / (Real.log (x : ℝ)) ^ (A + 3) + 1) / (((q.totient : ℕ)) : ℝ) := by
    intro q hq
    obtain ⟨hq1, hqQ⟩ := Finset.mem_Icc.mp hq
    haveI : NeZero q := ⟨by omega⟩
    have hqpos : (0 : ℝ) < ((q.totient : ℕ) : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr hq1
    have hqQx : (q : ℝ) ≤ (x : ℝ) ^ ϑ := le_trans (by exact_mod_cast hqQ) hQ
    have hx1' : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx1
    have hqroot : (q : ℝ) ≤ (x : ℝ) ^ (1 / 2 : ℝ) :=
      le_trans hqQx (Real.rpow_le_rpow_of_exponent_le hx1' (by linarith))
    refine Finset.sup'_le _ _ (fun h hh => ?_)
    have hhC : h ≤ C := by
      have := Finset.mem_range.mp hh
      omega
    have hhx : h ≤ x := by omega
    rw [discSupShift]
    refine Real.sSup_le (fun v hv => ?_) ?_
    · rcases hv with ⟨a, ha, rfl⟩
      have hb := discShift_thetaNat_le x q a h hx1 hq1 ha
      have hb' : |discShift (fun n => thetaNat n) x q a h| ≤
          2 * discSupPsi (3 * x + C) q +
            (Chebyshev.psi (((2 * x + h : ℕ)) : ℝ) - Chebyshev.theta (((2 * x + h : ℕ)) : ℝ)) +
            (|(x : ℝ) - (∑ m ∈ Finset.Ioc (x + h - 1) (2 * x + h),
              (if m.Coprime q then thetaNat m else 0))| + 1) /
                (((q.totient : ℕ)) : ℝ) := by
        refine le_trans hb (add_le_add (add_le_add ?_ le_rfl) le_rfl)
        exact mul_le_mul_of_nonneg_left (discSupPsi_mono q (by omega) (by omega)) (by norm_num)
      have hthird : |(x : ℝ) - (∑ m ∈ Finset.Ioc (x + h - 1) (2 * x + h),
            (if m.Coprime q then thetaNat m else 0))| ≤
          Cθ * (x : ℝ) / (Real.log (x : ℝ)) ^ (A + 3) := by
        rw [window_coprime_theta_eq x q h hx1, abs_sub_comm]
        exact hCθ x q h hx2 (NeZero.ne q) hqroot hhx
      have hsecond : Chebyshev.psi (((2 * x + h : ℕ)) : ℝ) -
          Chebyshev.theta (((2 * x + h : ℕ)) : ℝ) ≤ C₀ * Real.sqrt (((2 * x + C) : ℕ) : ℝ) := by
        refine le_trans (hC₀ _) ?_
        refine mul_le_mul_of_nonneg_left ?_ hC₀pos.le
        apply Real.sqrt_le_sqrt
        have : (2 * x + h : ℕ) ≤ (2 * x + C : ℕ) := by omega
        exact_mod_cast this
      have hthird2 : (|(x : ℝ) - (∑ m ∈ Finset.Ioc (x + h - 1) (2 * x + h),
            (if m.Coprime q then thetaNat m else 0))| + 1) / (((q.totient : ℕ)) : ℝ) ≤
          (Cθ * (x : ℝ) / (Real.log (x : ℝ)) ^ (A + 3) + 1) /
            (((q.totient : ℕ)) : ℝ) :=
        div_le_div_of_nonneg_right (by linarith [hthird]) hqpos.le
      exact le_trans hb' (by linarith [hsecond, hthird2])
    · have h1 : (0 : ℝ) ≤ 2 * discSupPsi (3 * x + C) q :=
        mul_nonneg (by norm_num) (discSupPsi_nonneg _ _ (by omega))
      have h2 : (0 : ℝ) ≤ C₀ * Real.sqrt (((2 * x + C) : ℕ) : ℝ) :=
        mul_nonneg hC₀pos.le (Real.sqrt_nonneg _)
      have h3 : (0 : ℝ) ≤ (Cθ * (x : ℝ) / (Real.log (x : ℝ)) ^ (A + 3) + 1) /
            (((q.totient : ℕ)) : ℝ) := by
        apply div_nonneg _ hqpos.le
        have : 0 ≤ Cθ * (x : ℝ) / (Real.log (x : ℝ)) ^ (A + 3) := by positivity
        linarith
      linarith
  refine le_trans (Finset.sum_le_sum hperq) ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  -- ### (1) Bombieri--Vinogradov
  have hsum1 : (∑ q ∈ Finset.Icc 1 Q, 2 * discSupPsi (3 * x + C) q) ≤
      (1 / 3) * ((x : ℝ) / (Real.log (x : ℝ)) ^ A) := by
    rw [← Finset.mul_sum]
    have hbv1 : (∑ q ∈ Finset.Icc 1 Q, discSupPsi (3 * x + C) q) ≤
        ∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℕ) : ℝ)⁻¹ *
          ∑ χ : DirichletCharacter ℂ q, charSup (3 * x + C) χ := by
      refine Finset.sum_le_sum (fun q hq => ?_)
      have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
      haveI : NeZero q := ⟨by omega⟩
      exact discSupPsi_le_sum_charSup (3 * x + C)
    have hbv2 := hbvx Q hQrootB
    have hXeq : (((3 * x + C) : ℕ) : ℝ) = 3 * (x : ℝ) + (C : ℝ) := by push_cast; ring
    have hXle : 3 * (x : ℝ) + (C : ℝ) ≤ 4 * (x : ℝ) := by linarith
    have hlogX : Real.log (x : ℝ) ≤ Real.log (3 * (x : ℝ) + (C : ℝ)) := by
      apply Real.log_le_log hxpos
      linarith
    have hlogXnn : 0 ≤ Real.log (3 * (x : ℝ) + (C : ℝ)) := le_trans hlogpos.le hlogX
    have hstep : (∑ q ∈ Finset.Icc 1 Q, discSupPsi (3 * x + C) q) ≤
        Cbv * (4 * (x : ℝ)) * (1 / (Real.log (x : ℝ)) ^ (A + 3)) := by
      refine le_trans hbv1 (le_trans hbv2 ?_)
      have hpowX : (Real.log (3 * (x : ℝ) + (C : ℝ))) ^ (-(A + 3)) ≤
          (Real.log (x : ℝ)) ^ (-(A + 3)) :=
        Real.rpow_le_rpow_of_nonpos hlogpos hlogX (by linarith)
      have hstep' : Cbv * (3 * (x : ℝ) + (C : ℝ)) *
            (Real.log (3 * (x : ℝ) + (C : ℝ))) ^ (-(A + 3)) ≤
          Cbv * (4 * (x : ℝ)) * (Real.log (x : ℝ)) ^ (-(A + 3)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hXle hCbvpos.le) hpowX
          (Real.rpow_nonneg hlogXnn _) (by positivity)
      rw [hXeq]
      exact le_trans hstep' (le_of_eq (by rw [Real.rpow_neg hlogpos.le, one_div]))
    have hLA3 : (Real.log (x : ℝ)) ^ (A + 3) =
        (Real.log (x : ℝ)) ^ A * (Real.log (x : ℝ)) ^ 3 := by
      rw [show (A + 3 : ℝ) = A + ((3 : ℕ) : ℝ) by norm_num, Real.rpow_add hlogpos,
        Real.rpow_natCast]
    have habs : 2 * (Cbv * (4 * (x : ℝ)) * (1 / (Real.log (x : ℝ)) ^ (A + 3))) ≤
        (1 / 3) * ((x : ℝ) / (Real.log (x : ℝ)) ^ A) := by
      rw [hLA3]
      have hL3pos : (0 : ℝ) < (Real.log (x : ℝ)) ^ 3 := pow_pos hlogpos 3
      have hid : 2 * (Cbv * (4 * (x : ℝ)) *
            (1 / ((Real.log (x : ℝ)) ^ A * (Real.log (x : ℝ)) ^ 3))) =
          (8 * Cbv / (Real.log (x : ℝ)) ^ 3) * ((x : ℝ) / (Real.log (x : ℝ)) ^ A) := by
        field_simp
        ring
      rw [hid]
      have hratio : 8 * Cbv / (Real.log (x : ℝ)) ^ 3 ≤ 1 / 3 := by
        rw [div_le_iff₀ hL3pos]
        linarith [hlog3x]
      exact mul_le_mul_of_nonneg_right hratio (by positivity)
    exact le_trans (mul_le_mul_of_nonneg_left hstep (by norm_num)) habs
  have hsum2 : (∑ q ∈ Finset.Icc 1 Q, C₀ * Real.sqrt (((2 * x + C) : ℕ) : ℝ)) ≤
      (1 / 3) * ((x : ℝ) / (Real.log (x : ℝ)) ^ A) := by
    rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]
    have hcard : ((Q + 1 - 1 : ℕ) : ℝ) = (Q : ℝ) := by
      have : (Q + 1 - 1 : ℕ) = Q := by omega
      rw [this]
    rw [hcard]
    have hsqrt : Real.sqrt (((2 * x + C) : ℕ) : ℝ) ≤ 2 * Real.sqrt (x : ℝ) := by
      have h1 : (((2 * x + C) : ℕ) : ℝ) ≤ 4 * (x : ℝ) := by
        push_cast; linarith
      calc Real.sqrt (((2 * x + C) : ℕ) : ℝ) ≤ Real.sqrt (4 * (x : ℝ)) := Real.sqrt_le_sqrt h1
        _ = Real.sqrt (4 : ℝ) * Real.sqrt (x : ℝ) := Real.sqrt_mul (by norm_num) x
        _ = 2 * Real.sqrt (x : ℝ) := by
            rw [show Real.sqrt (4 : ℝ) = 2 by
              rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    have hkey : (Q : ℝ) * (C₀ * Real.sqrt (((2 * x + C) : ℕ) : ℝ)) ≤
        2 * C₀ * (x : ℝ) ^ (ϑ + 1 / 2 : ℝ) := by
      have h1 : (Q : ℝ) * (C₀ * Real.sqrt (((2 * x + C) : ℕ) : ℝ)) ≤
          (x : ℝ) ^ ϑ * (C₀ * (2 * Real.sqrt (x : ℝ))) :=
        mul_le_mul hQ (mul_le_mul_of_nonneg_left hsqrt hC₀pos.le)
          (by positivity) (Real.rpow_nonneg hxnn ϑ)
      calc (Q : ℝ) * (C₀ * Real.sqrt (((2 * x + C) : ℕ) : ℝ))
          ≤ (x : ℝ) ^ ϑ * (C₀ * (2 * Real.sqrt (x : ℝ))) := h1
        _ = 2 * C₀ * ((x : ℝ) ^ ϑ * Real.sqrt (x : ℝ)) := by ring
        _ = 2 * C₀ * (x : ℝ) ^ (ϑ + 1 / 2 : ℝ) := by
            rw [Real.sqrt_eq_rpow, ← Real.rpow_add hxpos]
    have hexp : (x : ℝ) ^ (ϑ + 1 / 2 : ℝ) = (x : ℝ) / (x : ℝ) ^ (1 / 2 - ϑ) := by
      rw [show ϑ + 1 / 2 = 1 - (1 / 2 - ϑ) by ring, Real.rpow_sub hxpos, Real.rpow_one]
    rw [hexp] at hkey
    have hgoal2 : 2 * C₀ * ((x : ℝ) / (x : ℝ) ^ (1 / 2 - ϑ)) ≤
        (1 / 3) * ((x : ℝ) / (Real.log (x : ℝ)) ^ A) := by
      have hxδpos : 0 < (x : ℝ) ^ (1 / 2 - ϑ) := Real.rpow_pos_of_pos hxpos _
      rw [show 2 * C₀ * ((x : ℝ) / (x : ℝ) ^ (1 / 2 - ϑ)) =
          (2 * C₀ * (x : ℝ)) / (x : ℝ) ^ (1 / 2 - ϑ) by ring]
      rw [show (1 / 3) * ((x : ℝ) / (Real.log (x : ℝ)) ^ A) =
          (x : ℝ) / (3 * (Real.log (x : ℝ)) ^ A) by ring]
      rw [div_le_div_iff₀ hxδpos (by positivity)]
      have h2 : (2 * C₀ * (x : ℝ)) * (3 * (Real.log (x : ℝ)) ^ A) =
          (x : ℝ) * (6 * C₀ * (Real.log (x : ℝ)) ^ A) := by ring
      rw [h2]
      exact mul_le_mul_of_nonneg_left hpowx hxpos.le
    linarith [hkey, hgoal2]
  have hsum3 : (∑ q ∈ Finset.Icc 1 Q,
        (Cθ * (x : ℝ) / (Real.log (x : ℝ)) ^ (A + 3) + 1) / (((q.totient : ℕ)) : ℝ)) ≤
      (1 / 3) * ((x : ℝ) / (Real.log (x : ℝ)) ^ A) := by
    set K : ℝ := Cθ * (x : ℝ) / (Real.log (x : ℝ)) ^ (A + 3) + 1 with hKdef
    have hKpos : 0 < K := by
      rw [hKdef]
      have : 0 ≤ Cθ * (x : ℝ) / (Real.log (x : ℝ)) ^ (A + 3) := by positivity
      linarith
    have hfac : (∑ q ∈ Finset.Icc 1 Q, K / (((q.totient : ℕ)) : ℝ)) =
        K * ∑ q ∈ Finset.Icc 1 Q, (((q.totient : ℕ)) : ℝ)⁻¹ := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun q _ => by rw [div_eq_mul_inv])
    have hQmax : (max Q 2 : ℕ) ≤ x := by
      have hϑ1 : (x : ℝ) ^ ϑ ≤ (x : ℝ) := by
        calc (x : ℝ) ^ ϑ ≤ (x : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hx1) (by linarith)
          _ = (x : ℝ) := Real.rpow_one _
      have : (Q : ℝ) ≤ (x : ℝ) := le_trans hQ hϑ1
      have hQx : Q ≤ x := by exact_mod_cast this
      omega
    have hsuminv : (∑ q ∈ Finset.Icc 1 Q, (((q.totient : ℕ)) : ℝ)⁻¹) ≤
        Cφ * (Real.log (x : ℝ)) ^ 2 := by
      have h1 : (∑ q ∈ Finset.Icc 1 (max Q 2), (((q.totient : ℕ)) : ℝ)⁻¹) ≤
          Cφ * (Real.log ((max Q 2 : ℕ) : ℝ)) ^ 2 := hCφ (max Q 2) (le_max_right Q 2)
      have h2 : (∑ q ∈ Finset.Icc 1 Q, (((q.totient : ℕ)) : ℝ)⁻¹) ≤
          ∑ q ∈ Finset.Icc 1 (max Q 2), (((q.totient : ℕ)) : ℝ)⁻¹ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro q hq
          rw [Finset.mem_Icc] at hq ⊢
          exact ⟨hq.1, le_trans hq.2 (le_max_left Q 2)⟩
        · intro q _ _
          positivity
      have h3 : (Real.log ((max Q 2 : ℕ) : ℝ)) ^ 2 ≤ (Real.log (x : ℝ)) ^ 2 := by
        apply pow_le_pow_left₀ (by positivity)
        apply Real.log_le_log (by positivity)
        exact_mod_cast hQmax
      calc (∑ q ∈ Finset.Icc 1 Q, (((q.totient : ℕ)) : ℝ)⁻¹)
          ≤ ∑ q ∈ Finset.Icc 1 (max Q 2), (((q.totient : ℕ)) : ℝ)⁻¹ := h2
        _ ≤ Cφ * (Real.log ((max Q 2 : ℕ) : ℝ)) ^ 2 := h1
        _ ≤ Cφ * (Real.log (x : ℝ)) ^ 2 := mul_le_mul_of_nonneg_left h3 hCφpos.le
    have hlog2pos : 0 < (Real.log (x : ℝ)) ^ 2 := pow_pos hlogpos 2
    have hfinal : K * (Cφ * (Real.log (x : ℝ)) ^ 2) ≤
        (1 / 3) * ((x : ℝ) / (Real.log (x : ℝ)) ^ A) := by
      have hLA3 : (Real.log (x : ℝ)) ^ (A + 3) =
          (Real.log (x : ℝ)) ^ A * (Real.log (x : ℝ)) ^ 3 := by
        rw [show (A + 3 : ℝ) = A + ((3 : ℕ) : ℝ) by norm_num, Real.rpow_add hlogpos,
        Real.rpow_natCast]
      have hterm1 : Cθ * (x : ℝ) / (Real.log (x : ℝ)) ^ (A + 3) *
            (Cφ * (Real.log (x : ℝ)) ^ 2) ≤
          (1 / 6) * ((x : ℝ) / (Real.log (x : ℝ)) ^ A) := by
        rw [hLA3]
        have hL3pos : (0 : ℝ) < (Real.log (x : ℝ)) ^ 3 := pow_pos hlogpos 3
        have hid : Cθ * (x : ℝ) / ((Real.log (x : ℝ)) ^ A * (Real.log (x : ℝ)) ^ 3) *
            (Cφ * (Real.log (x : ℝ)) ^ 2) =
            (Cθ * Cφ / Real.log (x : ℝ)) * ((x : ℝ) / (Real.log (x : ℝ)) ^ A) := by
          field_simp
        rw [hid]
        have hratio : Cθ * Cφ / Real.log (x : ℝ) ≤ 1 / 6 := by
          rw [div_le_iff₀ hlogpos]
          linarith [hlogφx]
        exact mul_le_mul_of_nonneg_right hratio (by positivity)
      have hterm2 : (1 : ℝ) * (Cφ * (Real.log (x : ℝ)) ^ 2) ≤
          (1 / 6) * ((x : ℝ) / (Real.log (x : ℝ)) ^ A) := by
        have hp : (Real.log (x : ℝ)) ^ (A + 2) =
            (Real.log (x : ℝ)) ^ A * (Real.log (x : ℝ)) ^ (2 : ℕ) := by
          rw [show (A + 2 : ℝ) = A + ((2 : ℕ) : ℝ) by norm_num, Real.rpow_add hlogpos,
            Real.rpow_natCast]
        rw [show (1 : ℝ) * (Cφ * (Real.log (x : ℝ)) ^ 2) =
            Cφ * (Real.log (x : ℝ)) ^ 2 by ring]
        rw [show (1 / 6) * ((x : ℝ) / (Real.log (x : ℝ)) ^ A) =
            (x : ℝ) / (6 * (Real.log (x : ℝ)) ^ A) by ring]
        rw [le_div_iff₀ (by positivity : (0 : ℝ) < 6 * (Real.log (x : ℝ)) ^ A)]
        rw [show Cφ * (Real.log (x : ℝ)) ^ 2 * (6 * (Real.log (x : ℝ)) ^ A) =
            6 * Cφ * ((Real.log (x : ℝ)) ^ A * (Real.log (x : ℝ)) ^ 2) by ring]
        rw [← hp]
        linarith [hlogA2x]
      have hsplit : (Cθ * (x : ℝ) / (Real.log (x : ℝ)) ^ (A + 3) + 1) *
          (Cφ * (Real.log (x : ℝ)) ^ 2) =
          Cθ * (x : ℝ) / (Real.log (x : ℝ)) ^ (A + 3) * (Cφ * (Real.log (x : ℝ)) ^ 2) +
          (1 : ℝ) * (Cφ * (Real.log (x : ℝ)) ^ 2) := by ring
      rw [hKdef, hsplit]
      linarith [hterm1, hterm2]
    calc (∑ q ∈ Finset.Icc 1 Q, K / (((q.totient : ℕ)) : ℝ))
        = K * ∑ q ∈ Finset.Icc 1 Q, (((q.totient : ℕ)) : ℝ)⁻¹ := hfac
      _ ≤ K * (Cφ * (Real.log (x : ℝ)) ^ 2) :=
          mul_le_mul_of_nonneg_left hsuminv hKpos.le
      _ ≤ _ := hfinal
  linarith [hsum1, hsum2, hsum3]

end
end Commons.NumberTheory.MaynardSieve
