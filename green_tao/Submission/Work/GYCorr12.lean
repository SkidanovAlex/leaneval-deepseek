import Submission.Work.GYCorr11

/-!
# `GYCorr12`: the `p`-free (`CmB`-uniform) correlation bound for `ν = nuGT`

The correlation condition proved in `GYCorr11` (`corrCond_nuGT`) uses the *crude* diagonal value
`Dc m = (θ(W)·W·p²·log R)^m`, which makes the resulting constant `C m q` depend on `p`.  But the
`hP` interface of `GYFinal.green_tao_of_majorant` fixes the constant `CmB` *before* `p` (and before
`R`, `W`), so the correlation constant must be `p`-free.

This file supplies the ingredients of the fix (Green–Tao's own route, §9 of the paper):

* **the sharp diagonal bound** `‖ν‖_∞ ≤ log R · exp (C·ψ + C)` with
  `ψ = log (W p + 2) / log (log (W p + 2) + 2)`, coming from the *sub-polynomial divisor bound*
  `d(n) ≤ exp (C log n / log log n)`;
* **the `p`-free moment bound**: `p⁻¹ · Σ_x (τ x)^q` is bounded by an explicit function of `(m, q)`
  alone, via the arithmetic moment bound `CwMoment` and the elementary maximisation
  `p⁻¹ exp (A log p / log log p) ≤ exp (max (12 A) (exp A))`.
-/

open Finset
open scoped BigOperators

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

namespace GYMaj
namespace Corr

open GYMaj.BoxAvg
open Commons.NumberTheory.Sieve

variable {p : ℕ} [Fact p.Prime]

/-! ## 1. The arithmetic half-range moment bound for the pair weight -/

/-- The half-range moment bound for the pair weight `Vw`, with the `p`-free constant `CwMoment`. -/
lemma sum_ne_zero_Vw_pow_le {A : ℕ} (hA : 1 ≤ A) (hp : 3 ≤ p) :
    (p : ℝ)⁻¹ * ∑ x ∈ (Finset.univ.filter (fun x : ZMod p => x ≠ 0)), (Vw x) ^ A
      ≤ 2 * CwMoment A := by
  classical
  set G : ℕ → ℝ := fun d =>
    (∏ q ∈ d.primeFactors, (1 + (q : ℝ) ^ (-(1 / 2 : ℝ)))) ^ A with hG
  have hVw : ∀ x : ZMod p, (Vw x) ^ A = G (min x.val (p - x.val)) := by
    intro x
    rw [hG]
    rfl
  have hG0 : G 0 = 1 := by
    show (∏ q ∈ (0 : ℕ).primeFactors, (1 + (q : ℝ) ^ (-(1 / 2 : ℝ)))) ^ A = 1
    rw [Nat.primeFactors_zero, Finset.prod_empty, one_pow]
  have hVw0 : (Vw (0 : ZMod p)) ^ A = G 0 := by
    rw [hVw 0, ZMod.val_zero, Nat.sub_zero, Nat.zero_min]
  have hsplit : (∑ x ∈ Finset.univ.filter (fun x : ZMod p => x ≠ 0), (Vw x) ^ A)
      + (Vw (0 : ZMod p)) ^ A = ∑ x : ZMod p, (Vw x) ^ A := by
    have h1 : (Finset.univ.filter (fun x : ZMod p => ¬ x ≠ 0)) = {0} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨fun h => not_not.mp h, fun h => by simp [h]⟩
    have h2 := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (ZMod p))
      (fun x : ZMod p => x ≠ 0) (fun x : ZMod p => (Vw x) ^ A)
    rw [h1, Finset.sum_singleton] at h2
    exact h2
  have hne : (∑ x ∈ Finset.univ.filter (fun x : ZMod p => x ≠ 0), (Vw x) ^ A)
      = 2 * ∑ d ∈ Finset.Icc 1 (p / 2), G d := by
    have hdist := Commons.Data.ZMod.sum_dist_to_zero p hp G
    have hall : (∑ x : ZMod p, (Vw x) ^ A) = ∑ x : ZMod p, G (min x.val (p - x.val)) :=
      Finset.sum_congr rfl (fun x _ => hVw x)
    rw [hall, hdist, hVw0, hG0] at hsplit
    linarith
  rw [hne]
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hsub : Finset.Icc 1 (p / 2) ⊆ Finset.Icc 1 p := by
    intro d hd
    rw [Finset.mem_Icc] at hd ⊢
    exact ⟨hd.1, le_trans hd.2 (Nat.div_le_self p 2)⟩
  have hmono : ∑ d ∈ Finset.Icc 1 (p / 2), G d ≤ ∑ d ∈ Finset.Icc 1 p, G d :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => by
      show 0 ≤ (∏ q ∈ d.primeFactors, (1 + (q : ℝ) ^ (-(1 / 2 : ℝ)))) ^ A
      exact pow_nonneg (Finset.prod_nonneg (fun q _ => by
        have hq : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
        have := Real.rpow_nonneg hq (-(1 / 2 : ℝ))
        linarith)) _)
  have hspec := CwMoment_spec A p (by omega : 1 ≤ p)
  calc (p : ℝ)⁻¹ * (2 * ∑ d ∈ Finset.Icc 1 (p / 2), G d)
      = 2 * ((p : ℝ)⁻¹ * ∑ d ∈ Finset.Icc 1 (p / 2), G d) := by ring
    _ ≤ 2 * ((p : ℝ)⁻¹ * ∑ d ∈ Finset.Icc 1 p, G d) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        exact mul_le_mul_of_nonneg_left hmono (inv_nonneg.mpr (Nat.cast_nonneg p))
    _ ≤ 2 * CwMoment A := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        show (p : ℝ)⁻¹ * ∑ d ∈ Finset.Icc 1 p,
            (∏ q ∈ d.primeFactors, (1 + (q : ℝ) ^ (-(1 / 2 : ℝ)))) ^ A ≤ CwMoment A
        exact hspec

/-! ## 2. The `p`-free correlation condition -/

/-- **The correlation condition with a `p`-free constant.**  If the analytic correlation bound
`hgy` holds with a diagonal value `Dc` whose `q`-th moments are bounded by `S` (`p`-free) and with
pair constant `K ≤ Kmax`, then `ν` satisfies the correlation condition with the explicit `p`-free
constant `fun m q => max 1 (S m q + (Kmax m)^q * (2 * CwMoment (E m * q)))`. -/
theorem corrCond_of_gy_ub_pfree (hp : 3 ≤ p) (ν : ZMod p → ℝ) (m₀ : ℕ)
    {K Dc : ℕ → ℝ} (hK : ∀ m, 0 ≤ K m) (hDc : ∀ m, 0 ≤ Dc m) {E : ℕ → ℕ}
    (hE1 : ∀ m, 1 < m → 1 ≤ E m)
    (hgy : ∀ m, 1 < m → m ≤ m₀ → ∀ h : Fin m → ZMod p,
      (p : ℝ)⁻¹ * ∑ x : ZMod p, ∏ i, ν (x + h i)
        ≤ ∑ i : Fin m, ∑ j ∈ Finset.univ.filter (fun j => i < j),
            (if h i = h j then Dc m
             else K m * (∏ q ∈ (min (h i - h j).val (p - (h i - h j).val)).primeFactors,
                     (1 + (q : ℝ) ^ (-(1 / 2 : ℝ)))) ^ (E m)))
    {Kmax : ℕ → ℝ} (hKmax0 : ∀ m, 0 ≤ Kmax m) (hKle : ∀ m, K m ≤ Kmax m)
    {S : ℕ → ℕ → ℝ} (hS : ∀ m q, 1 ≤ q → (p : ℝ)⁻¹ * (Dc m) ^ q ≤ S m q) :
    Commons.NumberTheory.Sieve.CorrCond p ν m₀
      (fun m q => max 1 (S m q + (Kmax m) ^ q * (2 * CwMoment (E m * q)))) := by
  classical
  intro m hm1 hm2
  refine ⟨corrWeight p K Dc E m, ?_, ?_, ?_⟩
  · intro x
    exact corrWeight_nonneg hK hDc E m x
  · intro q hq
    rw [ZMod.card p]
    have hpoint : ∀ x : ZMod p, (corrWeight p K Dc E m x) ^ q
        = (if min x.val (p - x.val) = 0 then (Dc m) ^ q
            else (K m) ^ q * (Vw x) ^ (E m * q)) := by
      intro x
      rw [corrWeight]
      by_cases h : min x.val (p - x.val) = 0
      · rw [if_pos h, if_pos h]
      · rw [if_neg h, if_neg h, mul_pow, ← pow_mul, Vw]
    have hsum1 : ∑ x : ZMod p, (corrWeight p K Dc E m x) ^ q
        = (Dc m) ^ q
          + ∑ x ∈ (Finset.univ.filter (fun x : ZMod p => x ≠ 0)),
              (K m) ^ q * (Vw x) ^ (E m * q) := by
      rw [Finset.sum_congr rfl (fun x _ => hpoint x)]
      have h1 : (Finset.univ.filter (fun x : ZMod p => min x.val (p - x.val) = 0)) = {0} := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        exact min_val_eq_zero_iff x
      have h2 : (Finset.univ.filter (fun x : ZMod p => ¬ min x.val (p - x.val) = 0))
          = Finset.univ.filter (fun x : ZMod p => x ≠ 0) := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [min_val_eq_zero_iff]
      have h3 := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (ZMod p))
        (fun x : ZMod p => min x.val (p - x.val) = 0)
        (fun x : ZMod p => if min x.val (p - x.val) = 0 then (Dc m) ^ q
          else (K m) ^ q * (Vw x) ^ (E m * q))
      rw [h1, h2, Finset.sum_singleton] at h3
      have hmin0 : min (ZMod.val (0 : ZMod p)) (p - ZMod.val (0 : ZMod p)) = 0 :=
        (min_val_eq_zero_iff (0 : ZMod p)).mpr rfl
      have hf0 : (if min (ZMod.val (0 : ZMod p)) (p - ZMod.val (0 : ZMod p)) = 0 then (Dc m) ^ q
          else (K m) ^ q * (Vw (0 : ZMod p)) ^ (E m * q)) = (Dc m) ^ q := by
        rw [if_pos hmin0]
      have h4 : (∑ x ∈ Finset.univ.filter (fun x : ZMod p => x ≠ 0),
            (if min x.val (p - x.val) = 0 then (Dc m) ^ q
              else (K m) ^ q * (Vw x) ^ (E m * q)))
          = ∑ x ∈ (Finset.univ.filter (fun x : ZMod p => x ≠ 0)),
              (K m) ^ q * (Vw x) ^ (E m * q) := by
        refine Finset.sum_congr rfl (fun x hx => ?_)
        rw [Finset.mem_filter] at hx
        exact if_neg (fun hc => hx.2 ((min_val_eq_zero_iff x).mp hc))
      rw [hf0, h4] at h3
      linarith
    have hfac : ∑ x ∈ (Finset.univ.filter (fun x : ZMod p => x ≠ 0)),
          (K m) ^ q * (Vw x) ^ (E m * q)
        = (K m) ^ q * ∑ x ∈ (Finset.univ.filter (fun x : ZMod p => x ≠ 0)),
            (Vw x) ^ (E m * q) := by
      rw [Finset.mul_sum]
    rw [hsum1, hfac]
    have hEm : E m ≠ 0 := by have := hE1 m hm1; omega
    have hq0 : q ≠ 0 := by omega
    have hA1 : 1 ≤ E m * q := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hEm hq0)
    have hV := sum_ne_zero_Vw_pow_le (p := p) hA1 hp
    have hKq0 : (0 : ℝ) ≤ (K m) ^ q := pow_nonneg (hK m) q
    have hKqle : (K m) ^ q ≤ (Kmax m) ^ q := pow_le_pow_left₀ (hK m) (hKle m) q
    have hstep : (p : ℝ)⁻¹ * ((Dc m) ^ q
          + (K m) ^ q * ∑ x ∈ (Finset.univ.filter (fun x : ZMod p => x ≠ 0)),
              (Vw x) ^ (E m * q))
        ≤ S m q + (Kmax m) ^ q * (2 * CwMoment (E m * q)) := by
      have h1 := hS m q hq
      have h2 : (K m) ^ q * ((p : ℝ)⁻¹ * ∑ x ∈ (Finset.univ.filter (fun x : ZMod p => x ≠ 0)),
            (Vw x) ^ (E m * q)) ≤ (Kmax m) ^ q * (2 * CwMoment (E m * q)) := by
        have h2b : (K m) ^ q * ((p : ℝ)⁻¹ * ∑ x ∈ (Finset.univ.filter (fun x : ZMod p => x ≠ 0)),
              (Vw x) ^ (E m * q)) ≤ (K m) ^ q * (2 * CwMoment (E m * q)) :=
          mul_le_mul_of_nonneg_left hV hKq0
        have h2c : (K m) ^ q * (2 * CwMoment (E m * q))
            ≤ (Kmax m) ^ q * (2 * CwMoment (E m * q)) :=
          mul_le_mul_of_nonneg_right hKqle (by have := CwMoment_pos (E m * q); linarith)
        linarith
      have hsplit : (p : ℝ)⁻¹ * ((Dc m) ^ q
            + (K m) ^ q * ∑ x ∈ (Finset.univ.filter (fun x : ZMod p => x ≠ 0)),
                (Vw x) ^ (E m * q))
          = (p : ℝ)⁻¹ * (Dc m) ^ q
            + (K m) ^ q * ((p : ℝ)⁻¹ * ∑ x ∈ (Finset.univ.filter (fun x : ZMod p => x ≠ 0)),
                (Vw x) ^ (E m * q)) := by ring
      rw [hsplit]
      linarith
    exact le_trans hstep (le_max_right _ _)
  · intro h
    have hkey := hgy m hm1 hm2 h
    have hRHS : (∑ i : Fin m, ∑ j ∈ Finset.univ.filter (fun j => i < j),
          (if h i = h j then Dc m
           else K m * (∏ q ∈ (min (h i - h j).val (p - (h i - h j).val)).primeFactors,
                   (1 + (q : ℝ) ^ (-(1 / 2 : ℝ)))) ^ (E m)))
        = ∑ i : Fin m, ∑ j ∈ Finset.univ.filter (fun j => i < j),
            corrWeight p K Dc E m (h i - h j) := by
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      exact corrWeight_bracket E m h i j
    rw [ZMod.card p, ← hRHS]
    exact hkey

/-! ## 3. The uniform constants -/

/-- The `p`-free upper bound for the pair constant. -/
noncomputable def Kmax (m : ℕ) : ℝ := Kcorr 1 1 m

lemma Kcorr_le_Kmax {ε_box εcorr : ℝ} (hεb1 : ε_box ≤ 1)
    (hεc1 : εcorr ≤ 1) (m : ℕ) :
    Kcorr ε_box εcorr m ≤ Kmax m := by
  rw [Kmax, Kcorr, Kcorr]
  have h1 : (1 : ℝ) + ε_box ≤ 1 + 1 := by linarith
  have h2 : ∀ a ∈ Finset.range (m + 1), (1 + εcorr) * Kc a ≤ (1 + 1) * Kc a := by
    intro a _
    refine mul_le_mul_of_nonneg_right ?_ (Kc_nonneg' a)
    linarith
  have h3 : (1 + ε_box + ∑ a ∈ Finset.range (m + 1), (1 + εcorr) * Kc a)
      ≤ 1 + 1 + ∑ a ∈ Finset.range (m + 1), (1 + 1) * Kc a := by
    have := Finset.sum_le_sum h2
    linarith
  have h4 : (0 : ℝ) ≤ (2 : ℝ) ^ m := by positivity
  exact mul_le_mul_of_nonneg_left h3 h4

lemma Kmax_nonneg (m : ℕ) : 0 ≤ Kmax m := by
  rw [Kmax, Kcorr]
  have h : (0 : ℝ) ≤ Ktil 1 1 m := Ktil_nonneg 1 1 (by norm_num) (by norm_num) m
  positivity

end Corr
end GYMaj
