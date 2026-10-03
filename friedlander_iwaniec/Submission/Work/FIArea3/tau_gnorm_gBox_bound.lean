/-
# `Submission.Work.FIArea3.tau_gnorm_gBox_bound` — the average of `τ(|z|²)` over a box

  `Σ_{z ∈ gBox R} τ(|z|²) ≤ C·(2R+3)²·(1 + log(2R+3))²`   for `R ≥ 1`,

i.e. the divisor function is `(log N)^{2}` on average over the lattice points of a box, in place of
the pointwise maximum `2^{ω(|z|²)} ≤ 2^{(log N+3)/(log log x)²}`, which degenerates for large
`log N`.

The proof is the hyperbola/`Σ_d` exchange, using the two elementary inputs proved in this directory,

* `card_gBox_filter_dvd_gnorm` — `#{z ∈ gBox R : d ∣ |z|²} ≤ ρ(d)·(2R/d+2)²`,
  `ρ(d) = #{(a,b) mod d : a² + b² ≡ 0}`;
* `rho_le_four_pow` — `ρ(d) ≤ d·τ(d)`;

and the two divisor sums from `Commons`,

* `sum_divisor_count_div_le` — `Σ_{d ≤ X} τ(d)/d ≤ (1 + log X)²`;
* `sum_card_divisors_le` — `Σ_{d ≤ X} τ(d) ≤ X(1 + log X)`.

With `D := ⌈2R+2⌉` (so `√|z|² ≤ D` on the box, since `|z|² ≤ 2R² ≤ D²`) and
`τ(n) ≤ 2·#{d ≤ D : d ∣ n}` (the divisors pair up as `d ↔ n/d`),

  `Σ_z τ(|z|²) ≤ 2 Σ_{d ≤ D} #{z ∈ gBox R : d ∣ |z|²}
              ≤ 2 Σ_{d ≤ D} d·τ(d)·(2R/d+2)²
              = 8R²Σ_{d≤D}τ(d)/d + 16RΣ_{d≤D}τ(d) + 8Σ_{d≤D}d·τ(d)
              ≤ 8R²(1+log D)² + 16R·D(1+log D) + 8D²(1+log D)  ≤  1024 R²(1+log(2R+3))².`
-/
import Mathlib
import Submission.Work.FIArea3.card_gBox_filter_dvd_gnorm
import Submission.Work.FIArea3.rho_le_four_pow
import Submission.Commons.NumberTheory.DivisorSum.sum_divisor_count_div_le
import Submission.Commons.NumberTheory.DivisorSum.sum_tau_mul_log_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 2000000

namespace Work.FIArea3

open Finset Work.FIPlan
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

/-- `gnorm z = z.re² + z.im²`, as real numbers. -/
lemma gnorm_eq_re_sq_add_im_sq (z : GaussianInt) :
    (((Work.FIPlan.gnorm z : ℕ)) : ℝ) = ((z.re : ℤ) : ℝ) ^ 2 + ((z.im : ℤ) : ℝ) ^ 2 := by
  have hnorm : Zsqrtd.norm z = z.re * z.re + z.im * z.im := by simp [Zsqrtd.norm]
  have hge : (0 : ℝ) ≤ (z.norm : ℝ) := by
    rw [hnorm]
    have : (0 : ℤ) ≤ z.re * z.re + z.im * z.im := by
      have h1 : (0 : ℤ) ≤ z.re * z.re := mul_self_nonneg _
      have h2 : (0 : ℤ) ≤ z.im * z.im := mul_self_nonneg _
      linarith
    exact_mod_cast this
  have hcast : (((z.norm.natAbs : ℕ)) : ℝ) = (z.norm : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs, abs_of_nonneg hge]
  rw [show Work.FIPlan.gnorm z = z.norm.natAbs from rfl, hcast, hnorm]
  push_cast
  ring

/-- `τ(n) ≤ 2·#{d ≤ D : d ∣ n}` as soon as `√n ≤ D`. -/
private lemma tau_le_two_mul_card_dvd (n D : ℕ) (hD : Real.sqrt (n : ℝ) ≤ (D : ℝ)) :
    ((n.divisors.card : ℕ) : ℝ)
      ≤ 2 * (((Finset.Icc 1 D).filter (fun d => d ∣ n)).card : ℝ) := by
  classical
  rcases eq_or_ne n 0 with hn | hn
  · subst hn; simp
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    set S : Finset ℕ := (Finset.Icc 1 D).filter (fun d => d ∣ n) with hS
    have hsub : n.divisors ⊆ S ∪ S.image (fun d => n / d) := by
      intro d hd
      rw [Nat.mem_divisors] at hd
      obtain ⟨hdvd, -⟩ := hd
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hnpos
      have hdn : d ≤ n := Nat.le_of_dvd hnpos hdvd
      by_cases hle : d ≤ D
      · exact Finset.mem_union_left _
          (by rw [hS, Finset.mem_filter]
              exact ⟨Finset.mem_Icc.mpr ⟨hdpos, hle⟩, hdvd⟩)
      · have hDlt : D < d := by omega
        have hsqrtpos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hnpos)
        have hDR : Real.sqrt (n : ℝ) < (d : ℝ) := lt_of_le_of_lt hD (by exact_mod_cast hDlt)
        have h2 : ((n / d : ℕ) : ℝ) ≤ (n : ℝ) / (d : ℝ) := Nat.cast_div_le
        have h3 : (n : ℝ) / (d : ℝ) < (n : ℝ) / Real.sqrt (n : ℝ) :=
          div_lt_div_of_pos_left (by exact_mod_cast hnpos) hsqrtpos hDR
        have h4 : (n : ℝ) / Real.sqrt (n : ℝ) = Real.sqrt (n : ℝ) := by
          rw [div_eq_iff (ne_of_gt hsqrtpos)]
          nlinarith [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (n : ℝ))]
        have h6 : ((n / d : ℕ) : ℝ) < Real.sqrt (n : ℝ) := lt_of_le_of_lt h2 (h4 ▸ h3)
        have h5 : ((n / d : ℕ) : ℝ) < (D : ℝ) := lt_of_lt_of_le h6 hD
        have hlt' : n / d < D := by exact_mod_cast h5
        exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨n / d, by
          rw [hS, Finset.mem_filter]
          exact ⟨Finset.mem_Icc.mpr ⟨Nat.div_pos hdn hdpos, hlt'.le⟩,
            Nat.div_dvd_of_dvd hdvd⟩, Nat.div_div_self hdvd hn⟩)
    have hcard : n.divisors.card ≤ 2 * S.card := by
      calc n.divisors.card ≤ (S ∪ S.image (fun d => n / d)).card := Finset.card_le_card hsub
        _ ≤ S.card + (S.image (fun d => n / d)).card := Finset.card_union_le _ _
        _ ≤ S.card + S.card := by
            have : (S.image (fun d => n / d)).card ≤ S.card := Finset.card_image_le
            omega
        _ = 2 * S.card := by ring
    have : ((n.divisors.card : ℕ) : ℝ) ≤ 2 * (S.card : ℝ) := by exact_mod_cast hcard
    rw [hS] at this
    exact this

/-- **The average of `τ(|z|²)` over the box.**  For `R ≥ 1`,

  `Σ_{z ∈ gBox R} τ(|z|²) ≤ C·(2R+3)²·(1 + log(2R+3))²`. -/
theorem tau_gnorm_gBox_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℤ, 1 ≤ R →
      (∑ z ∈ Work.FIPlan.gBox R, (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ))
        ≤ C * (2 * (R : ℝ) + 3) ^ 2 * (1 + Real.log (2 * (R : ℝ) + 3)) ^ (2 : ℕ) := by
  refine ⟨1024, by norm_num, ?_⟩
  intro R hR
  have hR0 : (0 : ℤ) ≤ R := by omega
  have hR1 : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  have hRpos : (0 : ℝ) < (R : ℝ) := by linarith
  set D : ℕ := Nat.ceil (2 * (R : ℝ) + 2) with hDdef
  have hDge : 2 * (R : ℝ) + 2 ≤ (D : ℝ) := Nat.le_ceil _
  have hDlt : (D : ℝ) < 2 * (R : ℝ) + 3 := by
    have h := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 2 * (R : ℝ) + 2 by linarith)
    linarith
  have hDle : (D : ℝ) ≤ 2 * (R : ℝ) + 3 := le_of_lt hDlt
  have hD0 : (0 : ℝ) < (D : ℝ) := by linarith
  have hD1 : 1 ≤ D := by
    rcases Nat.eq_zero_or_pos D with h0 | hpos
    · rw [h0] at hD0; norm_num at hD0
    · exact hpos
  -- Step 1: the pointwise hyperbola bound
  have hpt : ∀ z ∈ Work.FIPlan.gBox R,
      (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ)
        ≤ 2 * (((Finset.Icc 1 D).filter (fun d => d ∣ Work.FIPlan.gnorm z)).card : ℝ) := by
    intro z hz
    refine tau_le_two_mul_card_dvd _ _ ?_
    have hg : ((Work.FIPlan.gnorm z : ℕ) : ℝ) ≤ 2 * (R : ℝ) ^ 2 := by
      rw [gnorm_eq_re_sq_add_im_sq z]
      have h := (Work.FIArea7.mem_gBox_iff).mp hz
      have h1 : ((z.re : ℤ) : ℝ) ≤ (R : ℝ) := by exact_mod_cast h.2.1
      have h1' : -((R : ℝ)) ≤ ((z.re : ℤ) : ℝ) := by exact_mod_cast h.1
      have h3 : ((z.im : ℤ) : ℝ) ≤ (R : ℝ) := by exact_mod_cast h.2.2.2
      have h3' : -((R : ℝ)) ≤ ((z.im : ℤ) : ℝ) := by exact_mod_cast h.2.2.1
      nlinarith [sq_nonneg (((z.re : ℤ) : ℝ)), sq_nonneg (((z.im : ℤ) : ℝ))]
    have hsqrt2 : Real.sqrt (2 * (R : ℝ) ^ 2) = Real.sqrt 2 * (R : ℝ) := by
      have hsq : 2 * (R : ℝ) ^ 2 = (Real.sqrt 2 * (R : ℝ)) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      rw [hsq, Real.sqrt_sq (by positivity)]
    calc Real.sqrt ((Work.FIPlan.gnorm z : ℕ) : ℝ)
        ≤ Real.sqrt (2 * (R : ℝ) ^ 2) := Real.sqrt_le_sqrt hg
      _ = Real.sqrt 2 * (R : ℝ) := hsqrt2
      _ ≤ (D : ℝ) := by
          have h4 : Real.sqrt 2 ≤ 2 := by
            rw [Real.sqrt_le_iff]; exact ⟨by norm_num, by norm_num⟩
          nlinarith [Real.sqrt_nonneg 2, hR1, hDge]
  -- Step 2: exchange the order of summation
  have hswap : (∑ z ∈ Work.FIPlan.gBox R,
        (((Finset.Icc 1 D).filter (fun d => d ∣ Work.FIPlan.gnorm z)).card : ℝ))
      = ∑ d ∈ Finset.Icc 1 D,
          (((Work.FIPlan.gBox R).filter (fun z => d ∣ Work.FIPlan.gnorm z)).card : ℝ) := by
    have h1 : ∀ z : GaussianInt,
        (((Finset.Icc 1 D).filter (fun d => d ∣ Work.FIPlan.gnorm z)).card : ℝ)
          = ∑ d ∈ Finset.Icc 1 D, (if d ∣ Work.FIPlan.gnorm z then (1 : ℝ) else 0) := by
      intro z
      rw [Finset.card_filter]
      push_cast
      rfl
    have h2 : ∀ d : ℕ,
        (((Work.FIPlan.gBox R).filter (fun z => d ∣ Work.FIPlan.gnorm z)).card : ℝ)
          = ∑ z ∈ Work.FIPlan.gBox R, (if d ∣ Work.FIPlan.gnorm z then (1 : ℝ) else 0) := by
      intro d
      rw [Finset.card_filter]
      push_cast
      rfl
    simp only [h1, h2]
    exact Finset.sum_comm
  -- Step 3: bound each count
  have hcount : ∀ d ∈ Finset.Icc 1 D,
      (((Work.FIPlan.gBox R).filter (fun z => d ∣ Work.FIPlan.gnorm z)).card : ℝ)
        ≤ ((d : ℝ) * ((d.divisors.card : ℕ) : ℝ)) * (2 * (R : ℝ) / (d : ℝ) + 2) ^ 2 := by
    intro d hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have hsq : (0 : ℝ) ≤ (2 * (R : ℝ) / (d : ℝ) + 2) ^ 2 := by positivity
    have hcast : (({v : ZMod d × ZMod d | v.1 ^ 2 + v.2 ^ 2 = 0}).ncard : ℝ)
        ≤ (d : ℝ) * ((d.divisors.card : ℕ) : ℝ) := by
      have h := Work.FIArea3.rho_le_four_pow d hd1
      calc (({v : ZMod d × ZMod d | v.1 ^ 2 + v.2 ^ 2 = 0}).ncard : ℝ)
          ≤ ((d * d.divisors.card : ℕ) : ℝ) := by exact_mod_cast h
        _ = (d : ℝ) * ((d.divisors.card : ℕ) : ℝ) := by push_cast; ring
    calc (((Work.FIPlan.gBox R).filter (fun z => d ∣ Work.FIPlan.gnorm z)).card : ℝ)
        ≤ (({v : ZMod d × ZMod d | v.1 ^ 2 + v.2 ^ 2 = 0}).ncard : ℝ)
            * (2 * (R : ℝ) / (d : ℝ) + 2) ^ 2 :=
          Work.FIArea3.card_gBox_filter_dvd_gnorm R d hd1
      _ ≤ ((d : ℝ) * ((d.divisors.card : ℕ) : ℝ)) * (2 * (R : ℝ) / (d : ℝ) + 2) ^ 2 :=
          mul_le_mul_of_nonneg_right hcast hsq
  -- Step 4: the divisor sums
  have hS1 : (∑ d ∈ Finset.Icc 1 D, ((d.divisors.card : ℕ) : ℝ) / (d : ℝ))
      ≤ (1 + Real.log (D : ℝ)) ^ 2 :=
    Commons.NumberTheory.DivisorSum.sum_divisor_count_div_le D hD1
  have hS2 : (∑ d ∈ Finset.Icc 1 D, ((d.divisors.card : ℕ) : ℝ))
      ≤ (D : ℝ) * (1 + Real.log (D : ℝ)) :=
    Commons.NumberTheory.DivisorSum.sum_card_divisors_le D hD1
  have hS3 : (∑ d ∈ Finset.Icc 1 D, (d : ℝ) * ((d.divisors.card : ℕ) : ℝ))
      ≤ (D : ℝ) * ((D : ℝ) * (1 + Real.log (D : ℝ))) := by
    have h1 : (∑ d ∈ Finset.Icc 1 D, (d : ℝ) * ((d.divisors.card : ℕ) : ℝ))
        ≤ ∑ d ∈ Finset.Icc 1 D, (D : ℝ) * ((d.divisors.card : ℕ) : ℝ) := by
      refine Finset.sum_le_sum (fun d hd => ?_)
      have hdD : (d : ℝ) ≤ (D : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hd).2
      exact mul_le_mul_of_nonneg_right hdD (by positivity)
    calc (∑ d ∈ Finset.Icc 1 D, (d : ℝ) * ((d.divisors.card : ℕ) : ℝ))
        ≤ ∑ d ∈ Finset.Icc 1 D, (D : ℝ) * ((d.divisors.card : ℕ) : ℝ) := h1
      _ = (D : ℝ) * ∑ d ∈ Finset.Icc 1 D, ((d.divisors.card : ℕ) : ℝ) := (Finset.mul_sum _ _ _).symm
      _ ≤ (D : ℝ) * ((D : ℝ) * (1 + Real.log (D : ℝ))) :=
          mul_le_mul_of_nonneg_left hS2 hD0.le
  -- assemble
  have hstep : (∑ z ∈ Work.FIPlan.gBox R, (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ))
      ≤ 2 * ∑ d ∈ Finset.Icc 1 D,
          (4 * (R : ℝ) ^ 2 * (((d.divisors.card : ℕ) : ℝ) / (d : ℝ))
            + 8 * (R : ℝ) * ((d.divisors.card : ℕ) : ℝ)
            + 4 * ((d : ℝ) * ((d.divisors.card : ℕ) : ℝ))) := by
    calc (∑ z ∈ Work.FIPlan.gBox R, (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ))
        ≤ ∑ z ∈ Work.FIPlan.gBox R,
            2 * (((Finset.Icc 1 D).filter (fun d => d ∣ Work.FIPlan.gnorm z)).card : ℝ) :=
          Finset.sum_le_sum hpt
      _ = 2 * ∑ z ∈ Work.FIPlan.gBox R,
            (((Finset.Icc 1 D).filter (fun d => d ∣ Work.FIPlan.gnorm z)).card : ℝ) := by
          rw [Finset.mul_sum]
      _ = 2 * ∑ d ∈ Finset.Icc 1 D,
            (((Work.FIPlan.gBox R).filter (fun z => d ∣ Work.FIPlan.gnorm z)).card : ℝ) := by
          rw [hswap]
      _ ≤ 2 * ∑ d ∈ Finset.Icc 1 D,
            ((d : ℝ) * ((d.divisors.card : ℕ) : ℝ)) * (2 * (R : ℝ) / (d : ℝ) + 2) ^ 2 := by
          have h := Finset.sum_le_sum hcount
          linarith
      _ = 2 * ∑ d ∈ Finset.Icc 1 D,
          (4 * (R : ℝ) ^ 2 * (((d.divisors.card : ℕ) : ℝ) / (d : ℝ))
            + 8 * (R : ℝ) * ((d.divisors.card : ℕ) : ℝ)
            + 4 * ((d : ℝ) * ((d.divisors.card : ℕ) : ℝ))) := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro d hd
          have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hd).1
          have hd0 : (d : ℝ) ≠ 0 := by positivity
          field_simp
          ring
  -- the sum of the three pieces
  have hpieces : (∑ d ∈ Finset.Icc 1 D,
        (4 * (R : ℝ) ^ 2 * (((d.divisors.card : ℕ) : ℝ) / (d : ℝ))
          + 8 * (R : ℝ) * ((d.divisors.card : ℕ) : ℝ)
          + 4 * ((d : ℝ) * ((d.divisors.card : ℕ) : ℝ))))
      = 4 * (R : ℝ) ^ 2 * (∑ d ∈ Finset.Icc 1 D, ((d.divisors.card : ℕ) : ℝ) / (d : ℝ))
        + 8 * (R : ℝ) * (∑ d ∈ Finset.Icc 1 D, ((d.divisors.card : ℕ) : ℝ))
        + 4 * (∑ d ∈ Finset.Icc 1 D, (d : ℝ) * ((d.divisors.card : ℕ) : ℝ)) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum,
      Finset.mul_sum]
  rw [hpieces] at hstep
  -- final arithmetic
  set L : ℝ := 1 + Real.log (D : ℝ) with hLdef
  set Lp : ℝ := 1 + Real.log (2 * (R : ℝ) + 3) with hLpdef
  have hL0 : 1 ≤ L := by
    have : (0 : ℝ) ≤ Real.log (D : ℝ) := Real.log_nonneg (by linarith)
    rw [hLdef]; linarith
  have hLp0 : 1 ≤ Lp := by
    have : (0 : ℝ) ≤ Real.log (2 * (R : ℝ) + 3) := Real.log_nonneg (by linarith)
    rw [hLpdef]; linarith
  have hLL : L ≤ Lp := by
    have hDle' : (D : ℝ) ≤ 2 * (R : ℝ) + 3 := hDle
    have : Real.log (D : ℝ) ≤ Real.log (2 * (R : ℝ) + 3) := Real.log_le_log hD0 hDle'
    rw [hLdef, hLpdef]; linarith
  have hLL2 : L ^ 2 ≤ Lp ^ 2 := pow_le_pow_left₀ (by linarith) hLL 2
  have hRL : (R : ℝ) ≤ 2 * (R : ℝ) + 3 := by linarith
  have hRsq : (R : ℝ) ^ 2 ≤ (2 * (R : ℝ) + 3) ^ 2 := by nlinarith [hR1]
  have hRD : (R : ℝ) * (D : ℝ) ≤ (2 * (R : ℝ) + 3) ^ 2 := by
    nlinarith [hR1, hDle, hD0, hRpos]
  have hDsq : (D : ℝ) ^ 2 ≤ (2 * (R : ℝ) + 3) ^ 2 := by
    have h := mul_le_mul hDle hDle (le_of_lt hD0) (by linarith : (0:ℝ) ≤ 2 * (R:ℝ) + 3)
    nlinarith [h]
  have hLp_le : Lp ≤ Lp ^ 2 := by nlinarith [hLp0]
  have hL_le : L ≤ Lp ^ 2 := le_trans hLL hLp_le
  have hnonneg : (0 : ℝ) ≤ (2 * (R : ℝ) + 3) ^ 2 * Lp ^ 2 := by positivity
  have hB : 4 * (R : ℝ) ^ 2 * (∑ d ∈ Finset.Icc 1 D, ((d.divisors.card : ℕ) : ℝ) / (d : ℝ))
      + 8 * (R : ℝ) * (∑ d ∈ Finset.Icc 1 D, ((d.divisors.card : ℕ) : ℝ))
      + 4 * (∑ d ∈ Finset.Icc 1 D, (d : ℝ) * ((d.divisors.card : ℕ) : ℝ))
      ≤ 512 * (2 * (R : ℝ) + 3) ^ 2 * Lp ^ 2 := by
    have hb1 : 4 * (R : ℝ) ^ 2 * (∑ d ∈ Finset.Icc 1 D, ((d.divisors.card : ℕ) : ℝ) / (d : ℝ))
        ≤ 4 * (2 * (R : ℝ) + 3) ^ 2 * Lp ^ 2 := by
      have h1 : (R : ℝ) ^ 2 * L ^ 2 ≤ (2 * (R : ℝ) + 3) ^ 2 * Lp ^ 2 := by
        have := mul_le_mul hRsq hLL2 (sq_nonneg L) (by positivity : (0:ℝ) ≤ (2*(R:ℝ)+3)^2)
        linarith [this]
      have h2 := mul_le_mul_of_nonneg_left hS1 (by positivity : (0:ℝ) ≤ 4 * (R:ℝ)^2)
      nlinarith [h1, h2]
    have hb2 : 8 * (R : ℝ) * (∑ d ∈ Finset.Icc 1 D, ((d.divisors.card : ℕ) : ℝ))
        ≤ 8 * (2 * (R : ℝ) + 3) ^ 2 * Lp ^ 2 := by
      have h2 : (D : ℝ) * (1 + Real.log (D : ℝ)) ≤ (2 * (R : ℝ) + 3) * Lp := by
        rw [hLpdef]
        exact mul_le_mul hDle hLL (by linarith [hD0]) (by linarith)
      have h3 : (R : ℝ) * ((D : ℝ) * (1 + Real.log (D : ℝ)))
          ≤ (2 * (R : ℝ) + 3) * ((2 * (R : ℝ) + 3) * Lp) :=
        mul_le_mul hRL h2 (by positivity) (by linarith)
      have h4 := mul_le_mul_of_nonneg_left hS2 (by positivity : (0:ℝ) ≤ 8 * (R:ℝ))
      have h5 : (R : ℝ) * ((2 * (R : ℝ) + 3) * ((2 * (R : ℝ) + 3) * Lp))
          = ((2 * (R : ℝ) + 3) ^ 2 * Lp) * (R : ℝ) := by ring
      nlinarith [h3, h4, h5, hnonneg, hLp0, hRpos, hRL]
    have hb3 : 4 * (∑ d ∈ Finset.Icc 1 D, (d : ℝ) * ((d.divisors.card : ℕ) : ℝ))
        ≤ 4 * (2 * (R : ℝ) + 3) ^ 2 * Lp ^ 2 := by
      have h2 : (D : ℝ) * ((D : ℝ) * (1 + Real.log (D : ℝ)))
          ≤ (2 * (R : ℝ) + 3) ^ 2 * Lp := by
        rw [hLpdef]
        have h3 : (D : ℝ) * ((D : ℝ) * L) ≤ (2 * (R : ℝ) + 3) * ((2 * (R : ℝ) + 3) * L) :=
          mul_le_mul hDle (mul_le_mul hDle (le_refl L) (by linarith) (by linarith)) (by positivity)
            (by linarith)
        nlinarith [h3]
      have h4 := mul_le_mul_of_nonneg_left hS3 (by norm_num : (0:ℝ) ≤ 4)
      have h5 : (2 * (R : ℝ) + 3) ^ 2 * Lp ≤ (2 * (R : ℝ) + 3) ^ 2 * Lp ^ 2 :=
        mul_le_mul_of_nonneg_left hLp_le (by positivity)
      linarith [h2, h4, h5]
    linarith [hb1, hb2, hb3, hnonneg]
  linarith [hstep, hB]

end

end Work.FIArea3
