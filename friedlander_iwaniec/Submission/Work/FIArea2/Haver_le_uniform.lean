import Mathlib
import Submission.Work.FIArea2.sec9_error_Hweight
import Submission.Work.FIArea2.Hscale_bounds
import Submission.Work.FIArea2.secWeight_ge_uniform
import Submission.Work.FIArea2.summable_uniform_weight

namespace Work.FIArea2

open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

/-- **Comparing one frequency weight with the uniform one.**  If `c ≥ 2^{-3/2}·cu` and `cu > 0`,
then for every `x ≥ 0` the weight `(1 + x c)^{-1}` is at most `8 (1 + x cu)^{-1}`: indeed
`1 + x c ≥ 1 + x·2^{-3/2} cu ≥ 2^{-3/2}(1 + x cu)` because `2^{-3/2} ≥ 1/8` and `x cu ≥ 0`, and
`(2^{-3/2})^{-1} = 2^{3/2} ≤ 8`. -/
theorem inv_weight_compare (c cu x : ℝ) (hcu : 0 < cu) (hx : 0 ≤ x)
    (hc : (2 : ℝ) ^ (-(3 : ℝ) / 2) * cu ≤ c) :
    (1 + x * c)⁻¹ ≤ 8 * (1 + x * cu)⁻¹ := by
  have hcpos : 0 < c := by
    have h := Real.rpow_pos_of_pos (show (0 : ℝ) < 2 by norm_num) (-(3 : ℝ) / 2)
    nlinarith [mul_pos h hcu]
  have hk18 : (1 / 8 : ℝ) ≤ (2 : ℝ) ^ (-(3 : ℝ) / 2) := by
    have h1 : (1 / 8 : ℝ) = (2 : ℝ) ^ (-(3 : ℝ)) := by
      rw [Real.rpow_neg (show (0 : ℝ) ≤ 2 by norm_num) (3 : ℝ)]
      norm_num
    rw [h1]
    exact Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num)
      (show (-(3 : ℝ)) ≤ -(3 : ℝ) / 2 by norm_num)
  have hkey : (1 / 8 : ℝ) * (1 + x * cu) ≤ 1 + x * c := by
    have hxk : x * ((1 / 8) * cu) ≤ x * c :=
      le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hk18 hcu.le) hx)
        (mul_le_mul_of_nonneg_left hc hx)
    have hEq : x * ((1 / 8) * cu) = (1 / 8) * (x * cu) := by ring
    rw [hEq] at hxk
    nlinarith [hxk]
  have hpos1 : 0 < 1 + x * c := by nlinarith [mul_nonneg hx hcpos.le]
  have hpos2 : 0 < 1 + x * cu := by nlinarith [mul_nonneg hx hcu.le]
  have hpos3 : 0 < (1 / 8 : ℝ) * (1 + x * cu) := by linarith
  have step : (1 + x * c)⁻¹ ≤ ((1 / 8 : ℝ) * (1 + x * cu))⁻¹ :=
    (inv_le_inv₀ hpos1 hpos3).mpr hkey
  calc (1 + x * c)⁻¹ ≤ ((1 / 8 : ℝ) * (1 + x * cu))⁻¹ := step
    _ = 8 * (1 + x * cu)⁻¹ := by rw [mul_inv]; norm_num

/-- Non-negativity of `(1 + x c)^{-1}` for `c > 0`, `x ≥ 0`. -/
theorem inv_nonneg_of_pos_aux {c x : ℝ} (hc : 0 < c) (hx : 0 ≤ x) : 0 ≤ (1 + x * c)⁻¹ :=
  inv_nonneg.mpr (by nlinarith)

/-- Positivity of `c` from `2^{-3/2} cu ≤ c`, `cu > 0`. -/
theorem const_pos_of_rpow_le {c cu : ℝ} (hcu : 0 < cu)
    (hc : (2 : ℝ) ^ (-(3 : ℝ) / 2) * cu ≤ c) : 0 < c := by
  have h := Real.rpow_pos_of_pos (show (0 : ℝ) < 2 by norm_num) (-(3 : ℝ) / 2)
  nlinarith [mul_pos h hcu]

/-- **The `h`-sum of (9.2) with the weights `c₁,c₂` is at most `64` times the sum with the uniform
weight `cu`**, whenever `2^{-3/2} cu ≤ c₁, c₂` and the uniform sum is summable.  Everything is
termwise and non-negative: `gcdDelta ≥ 0` and each frequency weight obeys `inv_weight_compare`. -/
theorem tsum_Haver_le_uniform (z1 z2 : GaussianInt) (c1 c2 cu : ℝ) (hcu : 0 < cu)
    (hc1 : (2 : ℝ) ^ (-(3 : ℝ) / 2) * cu ≤ c1)
    (hc2 : (2 : ℝ) ^ (-(3 : ℝ) / 2) * cu ≤ c2)
    (hsum : Summable (fun p : ℤ × ℤ => (if p = (0, 0) then 0 else
      (Work.FIArea2.gcdDelta z1 z2 p.1 p.2 : ℝ)
        * (1 + (p.1 : ℝ) ^ 2 * cu)⁻¹ * (1 + (p.2 : ℝ) ^ 2 * cu)⁻¹))) :
    (∑' p : ℤ × ℤ, (if p = (0, 0) then 0 else
      (Work.FIArea2.gcdDelta z1 z2 p.1 p.2 : ℝ)
        * (1 + (p.1 : ℝ) ^ 2 * c1)⁻¹ * (1 + (p.2 : ℝ) ^ 2 * c2)⁻¹))
      ≤ 64 * ∑' p : ℤ × ℤ, (if p = (0, 0) then 0 else
      (Work.FIArea2.gcdDelta z1 z2 p.1 p.2 : ℝ)
        * (1 + (p.1 : ℝ) ^ 2 * cu)⁻¹ * (1 + (p.2 : ℝ) ^ 2 * cu)⁻¹) := by
  have hc1pos : 0 < c1 := const_pos_of_rpow_le hcu hc1
  have hc2pos : 0 < c2 := const_pos_of_rpow_le hcu hc2
  have key : ∀ p : ℤ × ℤ,
      (if p = (0, 0) then 0 else (Work.FIArea2.gcdDelta z1 z2 p.1 p.2 : ℝ)
        * (1 + (p.1 : ℝ) ^ 2 * c1)⁻¹ * (1 + (p.2 : ℝ) ^ 2 * c2)⁻¹)
      ≤ 64 * (if p = (0, 0) then 0 else (Work.FIArea2.gcdDelta z1 z2 p.1 p.2 : ℝ)
        * (1 + (p.1 : ℝ) ^ 2 * cu)⁻¹ * (1 + (p.2 : ℝ) ^ 2 * cu)⁻¹) := by
    intro p
    by_cases hp : p = (0, 0)
    · rw [if_pos hp, if_pos hp]; norm_num
    · rw [if_neg hp, if_neg hp]
      have h1 := inv_weight_compare c1 cu ((p.1 : ℝ) ^ 2) hcu (sq_nonneg _) hc1
      have h2 := inv_weight_compare c2 cu ((p.2 : ℝ) ^ 2) hcu (sq_nonneg _) hc2
      have hA2 : 0 ≤ (1 + (p.2 : ℝ) ^ 2 * c2)⁻¹ := inv_nonneg_of_pos_aux hc2pos (sq_nonneg _)
      have hB1 : 0 ≤ 8 * (1 + (p.1 : ℝ) ^ 2 * cu)⁻¹ := by
        have := inv_nonneg_of_pos_aux hcu (sq_nonneg (p.1 : ℝ)); linarith
      calc (Work.FIArea2.gcdDelta z1 z2 p.1 p.2 : ℝ)
            * (1 + (p.1 : ℝ) ^ 2 * c1)⁻¹ * (1 + (p.2 : ℝ) ^ 2 * c2)⁻¹
          = (Work.FIArea2.gcdDelta z1 z2 p.1 p.2 : ℝ)
            * ((1 + (p.1 : ℝ) ^ 2 * c1)⁻¹ * (1 + (p.2 : ℝ) ^ 2 * c2)⁻¹) := by ring
        _ ≤ (Work.FIArea2.gcdDelta z1 z2 p.1 p.2 : ℝ)
            * ((8 * (1 + (p.1 : ℝ) ^ 2 * cu)⁻¹) * (8 * (1 + (p.2 : ℝ) ^ 2 * cu)⁻¹)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 hA2 hB1) (Nat.cast_nonneg _)
        _ = 64 * ((Work.FIArea2.gcdDelta z1 z2 p.1 p.2 : ℝ)
            * (1 + (p.1 : ℝ) ^ 2 * cu)⁻¹ * (1 + (p.2 : ℝ) ^ 2 * cu)⁻¹) := by ring
  have hmaj : Summable (fun p : ℤ × ℤ => 64 * (if p = (0, 0) then 0 else
      (Work.FIArea2.gcdDelta z1 z2 p.1 p.2 : ℝ)
        * (1 + (p.1 : ℝ) ^ 2 * cu)⁻¹ * (1 + (p.2 : ℝ) ^ 2 * cu)⁻¹)) := hsum.mul_left 64
  have hL : Summable (fun p : ℤ × ℤ => (if p = (0, 0) then 0 else
      (Work.FIArea2.gcdDelta z1 z2 p.1 p.2 : ℝ)
        * (1 + (p.1 : ℝ) ^ 2 * c1)⁻¹ * (1 + (p.2 : ℝ) ^ 2 * c2)⁻¹)) := by
    refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => key p) hmaj
    by_cases hp : p = (0, 0)
    · simp [hp]
    · rw [if_neg hp]
      exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
        (inv_nonneg_of_pos_aux hc1pos (sq_nonneg _)))
        (inv_nonneg_of_pos_aux hc2pos (sq_nonneg _))
  calc (∑' p : ℤ × ℤ, (if p = (0, 0) then 0 else
        (Work.FIArea2.gcdDelta z1 z2 p.1 p.2 : ℝ)
          * (1 + (p.1 : ℝ) ^ 2 * c1)⁻¹ * (1 + (p.2 : ℝ) ^ 2 * c2)⁻¹))
      ≤ ∑' p : ℤ × ℤ, 64 * (if p = (0, 0) then 0 else
        (Work.FIArea2.gcdDelta z1 z2 p.1 p.2 : ℝ)
          * (1 + (p.1 : ℝ) ^ 2 * cu)⁻¹ * (1 + (p.2 : ℝ) ^ 2 * cu)⁻¹) :=
        Summable.tsum_le_tsum key hL hmaj
    _ = 64 * ∑' p : ℤ × ℤ, (if p = (0, 0) then 0 else
        (Work.FIArea2.gcdDelta z1 z2 p.1 p.2 : ℝ)
          * (1 + (p.1 : ℝ) ^ 2 * cu)⁻¹ * (1 + (p.2 : ℝ) ^ 2 * cu)⁻¹) := tsum_mul_left

/-- **The weight of (9.2) against the uniform weight `(1+h²H^{−2})^{−1}`.**  For a pair whose
norms lie in the polar box (`Pa.N < |z_j|² ≤ (1+Pa.θ)Pa.N`) and `Δ ≠ 0`, the frequency weights
`(1+h_j² secWeight_j)^{−1}` (which are what Lemma 7.1 produces, `secFreq_sq_mul`) are comparable
with the *uniform* weight `(1+h_j²H^{−2})^{−1}`, `H = M^{−1/4}N^{3/4}` of (9.2)/(9.3): indeed
`√(1−γ²) = |Δ|/√(|z₁|²|z₂|²)` gives `secWeight₁ = √M/(|z₁||z₂|²)` and `secWeight₂ = √M/(|z₁|²|z₂|)`,
so on the polar box `(1+θ)^{−3/2}H^{−2} ≤ secWeight_j ≤ H^{−2}`.  Hence
`(1+h²c)^{−1} ≤ 8(1+h²H^{−2})^{−1}` for `c ≥ (1+θ)^{−3/2}H^{−2}` (as `θ ≤ 1`), and the same for
`h₂`.  This is the step that makes the `h`-sum of §9 a *uniform* sum, so that it can be interchanged
with the summation over the pairs `(z₁,z₂)`. -/
theorem Haver_le_uniform (Pa : Work.FITop.Params) (z1 z2 : GaussianInt)
    (hΔ : Work.FIPlan.Delta z1 z2 ≠ 0) (hγ0 : 0 ≤ Work.FIArea2.gamOf z1 z2)
    (hγ1 : Work.FIArea2.gamOf z1 z2 < 1) (hM : 1 ≤ Pa.M) (hθ : Pa.θ ≤ 1)
    (hn1 : Pa.N < ((Work.FIPlan.gnorm z1 : ℕ) : ℝ))
    (hn1' : ((Work.FIPlan.gnorm z1 : ℕ) : ℝ) ≤ (1 + Pa.θ) * Pa.N)
    (hn2 : Pa.N < ((Work.FIPlan.gnorm z2 : ℕ) : ℝ))
    (hn2' : ((Work.FIPlan.gnorm z2 : ℕ) : ℝ) ≤ (1 + Pa.θ) * Pa.N) :
    Work.FIArea2.Haver Pa z1 z2
      ≤ 64 * ∑' h : ℤ × ℤ, (if h = (0, 0) then 0 else
          (Work.FIArea2.gcdDelta z1 z2 h.1 h.2 : ℝ)
            * (1 + (h.1 : ℝ) ^ 2 / (Work.FIPlan.Hscale Pa.M Pa.N) ^ 2)⁻¹
            * (1 + (h.2 : ℝ) ^ 2 / (Work.FIPlan.Hscale Pa.M Pa.N) ^ 2)⁻¹) := by
  have hMpos : (0 : ℝ) < Pa.M := by linarith
  have hNpos : (0 : ℝ) < Pa.N := by linarith [Pa.hN1]
  have hHpos : 0 < Work.FIPlan.Hscale Pa.M Pa.N := by
    rw [Work.FIPlan.Hscale]
    exact mul_pos (Real.rpow_pos_of_pos hMpos _) (Real.rpow_pos_of_pos hNpos _)
  have hcu_pos : 0 < ((Work.FIPlan.Hscale Pa.M Pa.N) ^ 2)⁻¹ :=
    inv_pos.mpr (pow_pos hHpos 2)
  -- the polar-box lower bounds for the two weight constants
  have hge := secWeight_ge_uniform Pa z1 z2 hΔ Pa.hθ0 hθ hM hn1 hn1' hn2 hn2'
  -- summability of the uniform `h`-sum
  have hsumW : Summable (fun p : ℤ × ℤ => (if p = (0, 0) then 0 else
      (Work.FIArea2.gcdDelta z1 z2 p.1 p.2 : ℝ)
        * (1 + (p.1 : ℝ) ^ 2 * ((Work.FIPlan.Hscale Pa.M Pa.N) ^ 2)⁻¹)⁻¹
        * (1 + (p.2 : ℝ) ^ 2 * ((Work.FIPlan.Hscale Pa.M Pa.N) ^ 2)⁻¹)⁻¹)) := by
    simpa only [div_eq_mul_inv] using
      summable_uniform_weight z1 z2 hΔ (Work.FIPlan.Hscale Pa.M Pa.N) hHpos
  -- the weights of (9.2) written as `(1 + h_j² secWeight_j)^{-1}`
  have hHaver : Work.FIArea2.Haver Pa z1 z2 = ∑' p : ℤ × ℤ, (if p = (0, 0) then 0 else
      (Work.FIArea2.gcdDelta z1 z2 p.1 p.2 : ℝ)
        * (1 + (p.1 : ℝ) ^ 2 * Work.FIArea2.secWeight₁ Pa z1 z2)⁻¹
        * (1 + (p.2 : ℝ) ^ 2 * Work.FIArea2.secWeight₂ Pa z1 z2)⁻¹) := by
    unfold Work.FIArea2.Haver
    refine tsum_congr (fun p => ?_)
    by_cases hp : p = (0, 0)
    · rw [if_pos hp, if_pos hp]
    · rw [if_neg hp, if_neg hp,
        Work.FIArea2.secFreq_sq_mul Pa z1 z2 hΔ hγ0 hγ1 hM p.1,
        Work.FIArea2.secFreq₂_sq_mul Pa z1 z2 hΔ hγ0 hγ1 hM p.2]
  -- rewriting `(1 + h²/H²)^{-1}` as `(1 + h²(H²)^{-1})^{-1}`
  have hfin : (∑' p : ℤ × ℤ, (if p = (0, 0) then 0 else
      (Work.FIArea2.gcdDelta z1 z2 p.1 p.2 : ℝ)
        * (1 + (p.1 : ℝ) ^ 2 * ((Work.FIPlan.Hscale Pa.M Pa.N) ^ 2)⁻¹)⁻¹
        * (1 + (p.2 : ℝ) ^ 2 * ((Work.FIPlan.Hscale Pa.M Pa.N) ^ 2)⁻¹)⁻¹))
      = ∑' p : ℤ × ℤ, (if p = (0, 0) then 0 else
      (Work.FIArea2.gcdDelta z1 z2 p.1 p.2 : ℝ)
        * (1 + (p.1 : ℝ) ^ 2 / (Work.FIPlan.Hscale Pa.M Pa.N) ^ 2)⁻¹
        * (1 + (p.2 : ℝ) ^ 2 / (Work.FIPlan.Hscale Pa.M Pa.N) ^ 2)⁻¹) := by
    refine tsum_congr (fun p => ?_)
    by_cases hp : p = (0, 0)
    · rw [if_pos hp, if_pos hp]
    · rw [if_neg hp, if_neg hp]
      simp only [div_eq_mul_inv]
  calc Work.FIArea2.Haver Pa z1 z2
      = ∑' p : ℤ × ℤ, (if p = (0, 0) then 0 else
          (Work.FIArea2.gcdDelta z1 z2 p.1 p.2 : ℝ)
            * (1 + (p.1 : ℝ) ^ 2 * Work.FIArea2.secWeight₁ Pa z1 z2)⁻¹
            * (1 + (p.2 : ℝ) ^ 2 * Work.FIArea2.secWeight₂ Pa z1 z2)⁻¹) := hHaver
    _ ≤ 64 * ∑' p : ℤ × ℤ, (if p = (0, 0) then 0 else
          (Work.FIArea2.gcdDelta z1 z2 p.1 p.2 : ℝ)
            * (1 + (p.1 : ℝ) ^ 2 * ((Work.FIPlan.Hscale Pa.M Pa.N) ^ 2)⁻¹)⁻¹
            * (1 + (p.2 : ℝ) ^ 2 * ((Work.FIPlan.Hscale Pa.M Pa.N) ^ 2)⁻¹)⁻¹) :=
        tsum_Haver_le_uniform z1 z2 _ _ _ hcu_pos hge.1 hge.2 hsumW
    _ = 64 * ∑' h : ℤ × ℤ, (if h = (0, 0) then 0 else
          (Work.FIArea2.gcdDelta z1 z2 h.1 h.2 : ℝ)
            * (1 + (h.1 : ℝ) ^ 2 / (Work.FIPlan.Hscale Pa.M Pa.N) ^ 2)⁻¹
            * (1 + (h.2 : ℝ) ^ 2 / (Work.FIPlan.Hscale Pa.M Pa.N) ^ 2)⁻¹) := by
        rw [hfin]

end

end Work.FIArea2
