/-
# `Submission.Work.FIArea3.pairSumSharpCore`

The sharp pair-sum bound over the polar box (5.14) with the *parameter-free* right-hand side
`C·(θ²N + θ√N + 1)²·(log N)^{2^20-2}`.

With `u := θ√N`, `B := polarBoxFinset Pa φ` and `W z := τ(|z|²)`, `D z₁ z₂ := τ(|Δ(z₁,z₂)|)`:

* `IsBoxCoeff` forces `β` to vanish off `B`, and the summand is `≤ W z₁·W z₂·(1 + D z₁ z₂)`;
* splitting `1 + D` gives `(Σ_B W)² + Σ_{z₁ ∈ B} W z₁·(Σ_{z₂ ∈ B} W z₂ D z₁ z₂)`;
* `(Σ_B W)² ≤ #B·Σ_B W²` (Cauchy–Schwarz), `#B ≤ 200(u²+u+1)`
  (`FIArea4.polarBox_card_le`) and `Σ_B W² ≤ u²(log N)^{2^18}` (`secondMomentCore`);
* for `z₁ ∈ B`, writing `z₁ = c·z₁'` with `c = content(z₁)` and `z₁'` primitive,
  `τ(|Δ(z₁,·)|) ≤ τ(c)·τ(|Δ(z₁',·)|)` (`Nat.divisors_mul`), and the primitive bracket bound
  `Σ_{z₂ ∈ B} W z₂·D(z₁',z₂) ≤ u²(log N)^{2^19}` is `pairBracketPrim`;
* `τ(c) ≤ τ(|z₁|²) = W z₁`, so the extra factor is paid by the second moment;
* the hypothesis `u ≥ N^{3/8}` enters only through the two delegated estimates.
-/
import Mathlib
import Submission.Work.FIArea3.PairDefs6
import Submission.Work.FIArea3.BoxDefs
import Submission.Work.FIArea3.LargeUBase
import Submission.Work.FIArea3.JointCount.card_filter_le_class
import Submission.Work.FIArea3.JointCount.card_filter_le_le_arith
import Submission.Work.FIArea3.logFac_le

namespace Work.FIArea3

open Finset Work.FIPlan
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

/-- `τ(|z|²)` as a real number. -/
def pairTau (z : GaussianInt) : ℝ := ((Work.FIPlan.gnorm z).divisors.card : ℕ)

/-- `τ(|Δ(z₁,z₂)|)` as a real number. -/
def pairDel (z1 z2 : GaussianInt) : ℝ := ((Work.FIPlan.absDelta z1 z2).divisors.card : ℕ)

lemma pairTau_nonneg (z : GaussianInt) : 0 ≤ pairTau z := by rw [pairTau]; positivity

lemma pairDel_nonneg (z1 z2 : GaussianInt) : 0 ≤ pairDel z1 z2 := by rw [pairDel]; positivity

lemma one_add_pairDel_nonneg (z1 z2 : GaussianInt) : 0 ≤ 1 + pairDel z1 z2 := by
  linarith [pairDel_nonneg z1 z2]

/-! ## 0. The content and primitive part of a Gaussian integer -/

/-- Coprimality of the coordinates of the primitive part (from `LargeUBase.coprime_gPrimNe`). -/
lemma coprime_gPrimNe {z : GaussianInt} (hz : z ≠ 0) :
    Nat.Coprime (gPrim z).re.natAbs (gPrim z).im.natAbs :=
  coprime_gPrim (gContent_pos hz)

lemma Delta_natCast_mul (c : ℕ) (z w : GaussianInt) :
    Work.FIPlan.Delta ((c : GaussianInt) * z) w = (c : ℤ) * Work.FIPlan.Delta z w := by
  rw [Work.FIArea3.JointCount.Delta_class, Work.FIArea3.JointCount.Delta_class]
  have h1 : (((c : GaussianInt) * z).re) = (c : ℤ) * z.re := by simp
  have h2 : (((c : GaussianInt) * z).im) = (c : ℤ) * z.im := by simp
  rw [h1, h2]; ring

lemma Delta_gContent_mul_gPrim (z w : GaussianInt) :
    Work.FIPlan.Delta z w = (gContent z : ℤ) * Work.FIPlan.Delta (gPrim z) w := by
  conv_lhs => rw [eq_gContent_mul_gPrim z]
  rw [Delta_natCast_mul]

lemma absDelta_gContent_mul_gPrim (z w : GaussianInt) :
    Work.FIPlan.absDelta z w = gContent z * Work.FIPlan.absDelta (gPrim z) w := by
  rw [Work.FIPlan.absDelta, Work.FIPlan.absDelta, Delta_gContent_mul_gPrim, Int.natAbs_mul,
    Int.natAbs_natCast]

lemma tau_absDelta_le_mul (z w : GaussianInt) :
    pairDel z w ≤ ((gContent z).divisors.card : ℝ) * pairDel (gPrim z) w := by
  have h : (gContent z * Work.FIPlan.absDelta (gPrim z) w).divisors.card
      ≤ (gContent z).divisors.card * (Work.FIPlan.absDelta (gPrim z) w).divisors.card := by
    rw [Nat.divisors_mul]
    exact Finset.card_mul_le
  calc pairDel z w
      = (((gContent z * Work.FIPlan.absDelta (gPrim z) w).divisors.card : ℕ) : ℝ) := by
        rw [pairDel, absDelta_gContent_mul_gPrim z w]
    _ ≤ (((gContent z).divisors.card * (Work.FIPlan.absDelta (gPrim z) w).divisors.card : ℕ) : ℝ) := by
        exact_mod_cast h
    _ = ((gContent z).divisors.card : ℝ) * pairDel (gPrim z) w := by
        rw [pairDel]; push_cast; ring

lemma gContent_dvd_gnorm (z : GaussianInt) : gContent z ∣ Work.FIPlan.gnorm z := by
  rw [← Int.ofNat_dvd, Work.FIArea3.JointCount.gnorm_eq_re_im_class]
  have h1 : (gContent z : ℤ) ∣ z.re ^ 2 := by
    simpa [pow_two] using dvd_mul_of_dvd_left (gContent_dvd_re z) z.re
  have h2 : (gContent z : ℤ) ∣ z.im ^ 2 := by
    simpa [pow_two] using dvd_mul_of_dvd_left (gContent_dvd_im z) z.im
  exact dvd_add h1 h2

lemma gnorm_ne_zero {z : GaussianInt} (hz : z ≠ 0) : Work.FIPlan.gnorm z ≠ 0 := by
  intro h
  apply hz
  have hz0 : (Work.FIPlan.gnorm z : ℤ) = 0 := by exact_mod_cast h
  rw [Work.FIArea3.JointCount.gnorm_eq_re_im_class] at hz0
  have h1 : z.re = 0 := by nlinarith [sq_nonneg z.re, sq_nonneg z.im]
  have h2 : z.im = 0 := by nlinarith [sq_nonneg z.re, sq_nonneg z.im]
  exact Zsqrtd.ext h1 h2

lemma card_divisors_gContent_le (z : GaussianInt) (hz : z ≠ 0) :
    (gContent z).divisors.card ≤ (Work.FIPlan.gnorm z).divisors.card :=
  Finset.card_le_card (Nat.divisors_subset_of_dvd (gnorm_ne_zero hz) (gContent_dvd_gnorm z))

/-- `log N ≥ 1` under the sharpness hypothesis. -/
lemma one_le_log_N_of_sharp {Pa : Work.FITop.Params}
    (h : Pa.N ^ ((3 : ℝ) / 8) ≤ Pa.θ * Real.sqrt Pa.N) : 1 ≤ Real.log Pa.N := by
  by_contra hcon
  push_neg at hcon
  have hN0 : (0 : ℝ) < Pa.N := lt_of_lt_of_le zero_lt_one Pa.hN1
  have hNlt : Pa.N < Real.exp 1 := (Real.log_lt_iff_lt_exp hN0).mp hcon
  have hNlt4 : Pa.N < 4 := by
    have h4 : Real.exp 1 < 4 := by linarith [Real.exp_one_lt_d9]
    linarith
  have hsqrt : Real.sqrt Pa.N < 2 := by
    rw [show (2 : ℝ) = Real.sqrt 4 by norm_num]
    exact Real.sqrt_lt_sqrt hN0.le hNlt4
  have hθ : Pa.θ ≤ (1 : ℝ) / 10 := theta_le_tenth Pa
  have hu : Pa.θ * Real.sqrt Pa.N < 1 / 5 := by
    nlinarith [hθ, hsqrt, Pa.hθ0.le, Real.sqrt_nonneg Pa.N]
  have hpos : (1 : ℝ) ≤ Pa.N ^ ((3 : ℝ) / 8) := Real.one_le_rpow Pa.hN1 (by norm_num)
  linarith

/-- The polar-box block count: `#{z ∈ B : m ∣ |z|²} ≤ πu²τ(m)/m + 80uτ(m)/√m + τ(m)`. -/
lemma polarBox_filter_dvd_card_le (Pa : Work.FITop.Params) (φ : ℝ) (m : ℕ) (hm : 1 ≤ m) :
    (((Work.FIArea3.polarBoxFinset Pa φ).filter (fun z => m ∣ Work.FIPlan.gnorm z)).card : ℝ)
      ≤ Real.pi * (Pa.θ * Real.sqrt Pa.N) ^ 2 * ((m.divisors.card : ℝ) / (m : ℝ))
        + 80 * (Pa.θ * Real.sqrt Pa.N) * ((m.divisors.card : ℝ) / Real.sqrt (m : ℝ))
        + (m.divisors.card : ℝ) := by
  have hf : (Work.FIArea3.polarBoxFinset Pa φ).filter (fun z => m ∣ Work.FIPlan.gnorm z)
      = (Work.FIArea3.polarBoxFinset Pa φ).filter
          (fun z => m ∣ Work.FIPlan.gnorm z ∧ (1 : ℕ) ∣ Work.FIPlan.absDelta (0 : GaussianInt) z) := by
    apply Finset.filter_congr
    intro z _
    exact ⟨fun h => ⟨h, one_dvd _⟩, fun h => h.1⟩
  rw [hf]
  exact Work.FIArea3.JointCount.card_filter_le_le_arith Pa φ 0 m 1 hm le_rfl

/-- `Σ_{z ∈ B} (if p z then c else 0) = c · #{z ∈ B : p z}`. -/
lemma sum_ite_mul_card {α : Type*} [DecidableEq α] (B : Finset α) (p : α → Prop)
    [DecidablePred p] (c : ℝ) :
    (∑ z ∈ B, (if p z then c else 0)) = c * ((B.filter p).card : ℝ) := by
  rw [← Finset.sum_filter (s := B) (p := p) (f := fun _ => c), Finset.sum_const, nsmul_eq_mul]
  ring


end

end Work.FIArea3
