import Mathlib
import Submission.Work.BMF.mrlas.Psi2_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Bound for the `p`-component of the logarithmic derivative of the Euler product

For `f : ℕ → ℂ` with `f 1 = 1`, `‖f n‖ ≤ 1`, `p` prime and `Re s > 1`, the `p`-component
of the logarithmic derivative of the Euler product,
`deriv (gp f p) s / gp f p s + f p · log p · p^{-s}`,
is bounded by `16 · log p · p^{-2 Re s} · ‖(gp f p s)⁻¹‖`.

The key point is that the linear (`e = 1`) term in the local expansion cancels because
`f (p^1) = f p · f 1`, leaving an error of size `O(p^{-2 Re s})`.
-/

namespace Work.BMF.mrlas

set_option maxHeartbeats 2400000

open Finset Real Complex
open scoped BigOperators

noncomputable section

/-- Summability of `Σ_e e·f(p^e)·(u p s)^e` when `‖u p s‖ < 1`. -/
lemma summable_e_mul_u (f : ℕ → ℂ) (hb : ∀ n, ‖f n‖ ≤ 1) {p : ℕ} {s : ℂ}
    (h : ‖u p s‖ < 1) :
    Summable (fun e : ℕ => (e : ℂ) * f (p ^ e) * (u p s) ^ e) := by
  have hr0 : 0 ≤ ‖u p s‖ := norm_nonneg _
  have hg : Summable (fun e : ℕ => (e : ℝ) * ‖u p s‖ ^ e) := by
    have h1 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1
      (r := ‖u p s‖) (by rwa [Real.norm_eq_abs, abs_of_nonneg hr0])
    simpa using h1
  refine Summable.of_norm_bounded hg (fun e => ?_)
  simp only [norm_mul, Complex.norm_natCast, norm_pow]
  calc (e : ℝ) * ‖f (p ^ e)‖ * ‖u p s‖ ^ e
      = ‖u p s‖ ^ e * ((e : ℝ) * ‖f (p ^ e)‖) := by ring
    _ ≤ ‖u p s‖ ^ e * ((e : ℝ) * 1) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hb _) (Nat.cast_nonneg e)) (pow_nonneg hr0 e)
    _ = (e : ℝ) * ‖u p s‖ ^ e := by ring

/-- `(p : ℝ)^{-Re s} ≤ 1/2` for `p` prime and `Re s > 1`. -/
lemma rpow_neg_re_le_half {p : ℕ} (hp : p.Prime) {s : ℂ} (hs : 1 < s.re) :
    (p : ℝ) ^ (-s.re) ≤ 1 / 2 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  rw [Real.rpow_neg (le_of_lt (lt_trans zero_lt_one hp1))]
  have h2p : (2 : ℝ) ≤ (p : ℝ) ^ s.re :=
    calc (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := (Real.rpow_one 2).symm
      _ ≤ (2 : ℝ) ^ s.re := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ ≤ (p : ℝ) ^ s.re := Real.rpow_le_rpow (by norm_num) hp2 (by linarith)
  rw [show ((p : ℝ) ^ s.re)⁻¹ = 1 / ((p : ℝ) ^ s.re) from (one_div _).symm]
  exact one_div_le_one_div_of_le (by norm_num) h2p

/-- Tail bounds for geometric-like series with `0 ≤ r ≤ 1/2`. -/
lemma geom_tail_bounds {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2) :
    (∑' i : ℕ, r ^ (i + 2)) ≤ 2 * r ^ 2 ∧
      (∑' i : ℕ, ((i : ℝ) + 2) * r ^ (i + 2)) ≤ 6 * r ^ 2 := by
  have hnorm : ‖r‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hr0]; linarith
  have hgeo : Summable (fun i : ℕ => r ^ i) := summable_geometric_of_norm_lt_one hnorm
  have hgeoD : Summable (fun i : ℕ => (i : ℝ) * r ^ i) := by
    have h1 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 (r := r) hnorm
    simpa using h1
  have h1r : (0 : ℝ) < 1 - r := by linarith
  have hkey : (1 - r)⁻¹ ≤ 2 := by
    have hstep : (1 - r)⁻¹ ≤ ((2 : ℝ)⁻¹)⁻¹ :=
      (inv_le_inv₀ h1r (inv_pos.mpr (by norm_num : (0 : ℝ) < 2))).mpr
        (by rw [inv_eq_one_div]; linarith)
    rwa [inv_inv] at hstep
  constructor
  · have h1 : (∑' i : ℕ, r ^ (i + 2)) = r ^ 2 * (∑' i : ℕ, r ^ i) := by
      rw [show (fun i : ℕ => r ^ (i + 2)) = (fun i : ℕ => r ^ 2 * r ^ i) from
        funext (fun i => by rw [pow_add]; ring)]
      exact hgeo.tsum_mul_left (r ^ 2)
    rw [h1, tsum_geometric_of_norm_lt_one hnorm]
    calc r ^ 2 * (1 - r)⁻¹ ≤ r ^ 2 * 2 := mul_le_mul_of_nonneg_left hkey (sq_nonneg r)
      _ = 2 * r ^ 2 := by ring
  · have hsum : Summable (fun i : ℕ => (i : ℝ) * r ^ i + 2 * r ^ i) :=
      hgeoD.add (hgeo.mul_left 2)
    have h2 : (∑' i : ℕ, ((i : ℝ) + 2) * r ^ (i + 2))
        = r ^ 2 * ((∑' i : ℕ, (i : ℝ) * r ^ i) + 2 * (∑' i : ℕ, r ^ i)) := by
      rw [show (fun i : ℕ => ((i : ℝ) + 2) * r ^ (i + 2))
            = (fun i : ℕ => r ^ 2 * ((i : ℝ) * r ^ i + 2 * r ^ i)) from
            funext (fun i => by rw [pow_add]; ring)]
      rw [Summable.tsum_mul_left (r ^ 2) hsum, Summable.tsum_add hgeoD (hgeo.mul_left 2),
        Summable.tsum_mul_left 2 hgeo]
    rw [h2, tsum_coe_mul_geometric_of_norm_lt_one hnorm, tsum_geometric_of_norm_lt_one hnorm]
    have hA : r / (1 - r) ^ 2 ≤ 2 := by
      rw [div_le_iff₀ (pow_pos h1r 2)]
      have hh : 0 ≤ (1 - 2 * r) * (2 - r) := mul_nonneg (by linarith) (by linarith)
      nlinarith [hh]
    have hB : 2 * (1 - r)⁻¹ ≤ 4 := by linarith [hkey]
    calc r ^ 2 * (r / (1 - r) ^ 2 + 2 * (1 - r)⁻¹) ≤ r ^ 2 * (2 + 4) :=
          mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg r)
      _ = 6 * r ^ 2 := by ring

/-- `‖(gp f p s)⁻¹‖ ≥ 1/2`. -/
lemma gp_inv_norm_ge_half (f : ℕ → ℂ) (hf1 : f 1 = 1) (hb : ∀ n, ‖f n‖ ≤ 1) {p : ℕ}
    (hp : p.Prime) {s : ℂ} (hs : 1 < s.re) :
    (1 : ℝ) / 2 ≤ ‖(gp f p s)⁻¹‖ := by
  have hσ : 0 < s.re := by linarith
  have hnormu : ‖u p s‖ = (p : ℝ) ^ (-s.re) := norm_u hp.pos s
  have hr_half : (p : ℝ) ^ (-s.re) ≤ 1 / 2 := rpow_neg_re_le_half hp hs
  have hu_half : ‖u p s‖ ≤ 1 / 2 := by rw [hnormu]; exact hr_half
  have hle : ‖gp f p s‖ ≤ (1 - ‖u p s‖)⁻¹ := norm_gp_le f hb hp hσ
  have hgp2 : ‖gp f p s‖ ≤ 2 := by
    have h2 : (1 - ‖u p s‖)⁻¹ ≤ 2 := by
      have hpos : (0 : ℝ) < 1 - ‖u p s‖ := by linarith
      have hstep : (1 - ‖u p s‖)⁻¹ ≤ ((2 : ℝ)⁻¹)⁻¹ :=
        (inv_le_inv₀ hpos (inv_pos.mpr (by norm_num : (0 : ℝ) < 2))).mpr
          (by rw [inv_eq_one_div]; linarith)
      rwa [inv_inv] at hstep
    linarith
  have hne : gp f p s ≠ 0 :=
    gp_ne_zero f hf1 hb (σ := (1 + s.re) / 2) (by linarith) p hp (by linarith)
  have hpos : 0 < ‖gp f p s‖ := norm_pos_iff.mpr hne
  rw [show (1 : ℝ) / 2 = (2 : ℝ)⁻¹ by norm_num, norm_inv]
  exact (inv_le_inv₀ (by norm_num : (0 : ℝ) < 2) hpos).mpr hgp2

/-- Core bound: `‖g_p'(s) + f p · log p · p^{-s} · g_p(s)‖ ≤ 8 log p · p^{-2 Re s}`. -/
lemma norm_deriv_add_fp_mul_le (f : ℕ → ℂ) (hf1 : f 1 = 1) (hb : ∀ n, ‖f n‖ ≤ 1)
    {p : ℕ} (hp : p.Prime) {s : ℂ} (hs : 1 < s.re) :
    ‖deriv (gp f p) s + f p * (Real.log p : ℂ) * (p : ℂ) ^ (-s) * gp f p s‖
      ≤ 8 * Real.log p * (p : ℝ) ^ (-2 * s.re) := by
  have hσ : 0 < s.re := by linarith
  have hp0 : p ≠ 0 := hp.ne_zero
  have hlogp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hnormu : ‖u p s‖ = (p : ℝ) ^ (-s.re) := norm_u hp.pos s
  have hr_half : (p : ℝ) ^ (-s.re) ≤ 1 / 2 := rpow_neg_re_le_half hp hs
  have hu_half : ‖u p s‖ ≤ 1 / 2 := by rw [hnormu]; exact hr_half
  have hu_lt1 : ‖u p s‖ < 1 := lt_of_le_of_lt hu_half (by norm_num)
  have hr0 : 0 ≤ (p : ℝ) ^ (-s.re) := Real.rpow_nonneg (Nat.cast_nonneg p) _
  have hsq : (p : ℝ) ^ (-2 * s.re) = ((p : ℝ) ^ (-s.re)) ^ 2 := by
    rw [show -2 * s.re = -s.re + -s.re by ring, Real.rpow_add (by exact_mod_cast hp.pos)]
    ring
  -- summability
  have hS : Summable (fun e : ℕ => f (p ^ e) * (u p s) ^ e) := summable_gp_terms f hb hp hσ
  have hT : Summable (fun e : ℕ => (e : ℂ) * f (p ^ e) * (u p s) ^ e) :=
    summable_e_mul_u f hb hu_lt1
  have hS1 : Summable (fun j : ℕ => f (p ^ (j + 1)) * (u p s) ^ (j + 1)) :=
    hS.comp_injective Nat.succ_injective
  have hT1 : Summable (fun j : ℕ =>
    ((j + 1 : ℕ) : ℂ) * f (p ^ (j + 1)) * (u p s) ^ (j + 1)) :=
    hT.comp_injective Nat.succ_injective
  have hR : Summable (fun i : ℕ => f (p ^ (i + 2)) * (u p s) ^ (i + 2)) :=
    (summable_nat_add_iff 2).mpr hS
  have hR' : Summable (fun i : ℕ =>
    ((i + 2 : ℕ) : ℂ) * f (p ^ (i + 2)) * (u p s) ^ (i + 2)) :=
    (summable_nat_add_iff 2).mpr hT
  have hgeo : Summable (fun i : ℕ => ((p : ℝ) ^ (-s.re)) ^ i) :=
    summable_geometric_of_norm_lt_one (by rw [Real.norm_eq_abs, abs_of_nonneg hr0]; linarith)
  have hgeoD : Summable (fun i : ℕ => (i : ℝ) * ((p : ℝ) ^ (-s.re)) ^ i) := by
    have h1 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 (r := (p : ℝ) ^ (-s.re))
      (by rw [Real.norm_eq_abs, abs_of_nonneg hr0]; linarith)
    simpa using h1
  have hgeosum : Summable (fun i : ℕ => ((p : ℝ) ^ (-s.re)) ^ (i + 2)) :=
    (summable_nat_add_iff 2).mpr hgeo
  have hgeosum2 : Summable (fun i : ℕ => ((i : ℝ) + 2) * ((p : ℝ) ^ (-s.re)) ^ (i + 2)) := by
    have hb1 : Summable (fun i : ℕ =>
        (i : ℝ) * ((p : ℝ) ^ (-s.re)) ^ i + 2 * ((p : ℝ) ^ (-s.re)) ^ i) :=
      hgeoD.add (hgeo.mul_left 2)
    have hb2 := hb1.mul_right (((p : ℝ) ^ (-s.re)) ^ 2)
    refine hb2.congr (fun i => ?_)
    rw [pow_add]; ring
  -- splitting identities
  have hSsplit : (∑' e : ℕ, f (p ^ e) * (u p s) ^ e)
      = 1 + f p * (u p s) + (∑' i : ℕ, f (p ^ (i + 2)) * (u p s) ^ (i + 2)) := by
    rw [hS.tsum_eq_zero_add, hS1.tsum_eq_zero_add]
    simp only [pow_zero, mul_one, hf1, Nat.zero_add, pow_one]
    ring
  have hTsplit : (∑' e : ℕ, (e : ℂ) * f (p ^ e) * (u p s) ^ e)
      = f p * (u p s)
        + (∑' i : ℕ, ((i + 2 : ℕ) : ℂ) * f (p ^ (i + 2)) * (u p s) ^ (i + 2)) := by
    rw [hT.tsum_eq_zero_add, hT1.tsum_eq_zero_add]
    simp only [Nat.cast_zero, zero_mul, zero_add, Nat.cast_one, pow_one, one_mul]
  -- the bound on the two shifted tails
  have hRnorm : ‖∑' i : ℕ, f (p ^ (i + 2)) * (u p s) ^ (i + 2)‖
      ≤ 2 * ((p : ℝ) ^ (-s.re)) ^ 2 := by
    have hle : ‖∑' i : ℕ, f (p ^ (i + 2)) * (u p s) ^ (i + 2)‖
        ≤ ∑' i : ℕ, ((p : ℝ) ^ (-s.re)) ^ (i + 2) := by
      calc ‖∑' i : ℕ, f (p ^ (i + 2)) * (u p s) ^ (i + 2)‖
          ≤ ∑' i : ℕ, ‖f (p ^ (i + 2)) * (u p s) ^ (i + 2)‖ :=
            norm_tsum_le_tsum_norm hR.norm
        _ ≤ ∑' i : ℕ, ((p : ℝ) ^ (-s.re)) ^ (i + 2) := by
            refine Summable.tsum_le_tsum (fun i => ?_) hR.norm hgeosum
            rw [norm_mul, norm_pow, hnormu]
            exact mul_le_of_le_one_left (pow_nonneg hr0 _) (hb _)
    calc ‖∑' i : ℕ, f (p ^ (i + 2)) * (u p s) ^ (i + 2)‖
        ≤ ∑' i : ℕ, ((p : ℝ) ^ (-s.re)) ^ (i + 2) := hle
      _ ≤ 2 * ((p : ℝ) ^ (-s.re)) ^ 2 := (geom_tail_bounds hr0 hr_half).1
  have hR'norm : ‖∑' i : ℕ, ((i + 2 : ℕ) : ℂ) * f (p ^ (i + 2)) * (u p s) ^ (i + 2)‖
      ≤ 6 * ((p : ℝ) ^ (-s.re)) ^ 2 := by
    have hle : ‖∑' i : ℕ, ((i + 2 : ℕ) : ℂ) * f (p ^ (i + 2)) * (u p s) ^ (i + 2)‖
        ≤ ∑' i : ℕ, ((i : ℝ) + 2) * ((p : ℝ) ^ (-s.re)) ^ (i + 2) := by
      calc ‖∑' i : ℕ, ((i + 2 : ℕ) : ℂ) * f (p ^ (i + 2)) * (u p s) ^ (i + 2)‖
          ≤ ∑' i : ℕ, ‖((i + 2 : ℕ) : ℂ) * f (p ^ (i + 2)) * (u p s) ^ (i + 2)‖ :=
            norm_tsum_le_tsum_norm hR'.norm
        _ ≤ ∑' i : ℕ, ((i : ℝ) + 2) * ((p : ℝ) ^ (-s.re)) ^ (i + 2) := by
            refine Summable.tsum_le_tsum (fun i => ?_) hR'.norm hgeosum2
            rw [norm_mul, norm_mul, Complex.norm_natCast, norm_pow, hnormu]
            have hcast : ((i + 2 : ℕ) : ℝ) = (i : ℝ) + 2 := by push_cast; ring
            rw [hcast]
            have hgl : (0 : ℝ) ≤ (i : ℝ) + 2 := by positivity
            have := mul_le_mul_of_nonneg_left (hb (p ^ (i + 2))) hgl
            have hgl2 := mul_le_mul_of_nonneg_right this (pow_nonneg hr0 (i + 2))
            simpa using hgl2
    calc ‖∑' i : ℕ, ((i + 2 : ℕ) : ℂ) * f (p ^ (i + 2)) * (u p s) ^ (i + 2)‖
        ≤ ∑' i : ℕ, ((i : ℝ) + 2) * ((p : ℝ) ^ (-s.re)) ^ (i + 2) := hle
      _ ≤ 6 * ((p : ℝ) ^ (-s.re)) ^ 2 := (geom_tail_bounds hr0 hr_half).2
  -- algebra: the two `e = 1` terms cancel
  have hX : deriv (gp f p) s + f p * (Real.log p : ℂ) * (p : ℂ) ^ (-s) * gp f p s
      = (Real.log p : ℂ) * (f p * (u p s) * (∑' e : ℕ, f (p ^ e) * (u p s) ^ e)
          - (∑' e : ℕ, (e : ℂ) * f (p ^ e) * (u p s) ^ e)) := by
    rw [deriv_gp f hb hp (z := s) hs, ← u_eq_cpow hp0 s, gp_eq f hp s]
    ring
  rw [hX, norm_mul, Complex.norm_of_nonneg hlogp.le]
  have hinner : ‖f p * (u p s) * (∑' e : ℕ, f (p ^ e) * (u p s) ^ e)
      - (∑' e : ℕ, (e : ℂ) * f (p ^ e) * (u p s) ^ e)‖
      ≤ 8 * (p : ℝ) ^ (-2 * s.re) := by
    have hid : f p * (u p s) * (∑' e : ℕ, f (p ^ e) * (u p s) ^ e)
        - (∑' e : ℕ, (e : ℂ) * f (p ^ e) * (u p s) ^ e)
        = f p ^ 2 * (u p s) ^ 2
          + f p * (u p s) * (∑' i : ℕ, f (p ^ (i + 2)) * (u p s) ^ (i + 2))
          - (∑' i : ℕ, ((i + 2 : ℕ) : ℂ) * f (p ^ (i + 2)) * (u p s) ^ (i + 2)) := by
      rw [hSsplit, hTsplit]; ring
    rw [hid]
    have h1 : ‖f p ^ 2 * (u p s) ^ 2‖ ≤ ((p : ℝ) ^ (-s.re)) ^ 2 := by
      rw [norm_mul, norm_pow, norm_pow, hnormu]
      have hfp : ‖f p‖ ≤ 1 := hb p
      calc ‖f p‖ ^ 2 * ((p : ℝ) ^ (-s.re)) ^ 2 ≤ 1 ^ 2 * ((p : ℝ) ^ (-s.re)) ^ 2 :=
            mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hfp 2) (sq_nonneg _)
        _ = ((p : ℝ) ^ (-s.re)) ^ 2 := by ring
    have h2 : ‖f p * (u p s) * (∑' i : ℕ, f (p ^ (i + 2)) * (u p s) ^ (i + 2))‖
        ≤ (p : ℝ) ^ (-s.re) * (2 * ((p : ℝ) ^ (-s.re)) ^ 2) := by
      rw [norm_mul, norm_mul]
      have hfp : ‖f p‖ ≤ 1 := hb p
      calc ‖f p‖ * ‖u p s‖ * ‖∑' i : ℕ, f (p ^ (i + 2)) * (u p s) ^ (i + 2)‖
          ≤ (1 * (p : ℝ) ^ (-s.re)) * (2 * ((p : ℝ) ^ (-s.re)) ^ 2) :=
            mul_le_mul (mul_le_mul hfp (le_of_eq hnormu) (norm_nonneg _) (by norm_num))
              hRnorm (norm_nonneg _) (by rw [one_mul]; exact hr0)
        _ = (p : ℝ) ^ (-s.re) * (2 * ((p : ℝ) ^ (-s.re)) ^ 2) := by ring
    calc ‖f p ^ 2 * (u p s) ^ 2
            + f p * (u p s) * (∑' i : ℕ, f (p ^ (i + 2)) * (u p s) ^ (i + 2))
            - (∑' i : ℕ, ((i + 2 : ℕ) : ℂ) * f (p ^ (i + 2)) * (u p s) ^ (i + 2))‖
        ≤ ‖f p ^ 2 * (u p s) ^ 2‖
            + ‖f p * (u p s) * (∑' i : ℕ, f (p ^ (i + 2)) * (u p s) ^ (i + 2))‖
            + ‖∑' i : ℕ, ((i + 2 : ℕ) : ℂ) * f (p ^ (i + 2)) * (u p s) ^ (i + 2)‖ := by
          have ha := norm_add_le (f p ^ 2 * (u p s) ^ 2)
            (f p * (u p s) * (∑' i : ℕ, f (p ^ (i + 2)) * (u p s) ^ (i + 2)))
          have hb' := norm_sub_le
            (f p ^ 2 * (u p s) ^ 2
              + f p * (u p s) * (∑' i : ℕ, f (p ^ (i + 2)) * (u p s) ^ (i + 2)))
            (∑' i : ℕ, ((i + 2 : ℕ) : ℂ) * f (p ^ (i + 2)) * (u p s) ^ (i + 2))
          linarith
      _ ≤ ((p : ℝ) ^ (-s.re)) ^ 2
            + (p : ℝ) ^ (-s.re) * (2 * ((p : ℝ) ^ (-s.re)) ^ 2)
            + 6 * ((p : ℝ) ^ (-s.re)) ^ 2 := by linarith [h1, h2, hR'norm]
      _ ≤ 8 * ((p : ℝ) ^ (-s.re)) ^ 2 := by
          nlinarith [mul_nonneg (sq_nonneg ((p : ℝ) ^ (-s.re)))
            (by linarith : (0 : ℝ) ≤ 1 - 2 * (p : ℝ) ^ (-s.re))]
      _ = 8 * (p : ℝ) ^ (-2 * s.re) := by rw [hsq]
  calc Real.log p * ‖f p * (u p s) * (∑' e : ℕ, f (p ^ e) * (u p s) ^ e)
          - (∑' e : ℕ, (e : ℂ) * f (p ^ e) * (u p s) ^ e)‖
      ≤ Real.log p * (8 * (p : ℝ) ^ (-2 * s.re)) :=
        mul_le_mul_of_nonneg_left hinner hlogp.le
    _ = 8 * Real.log p * (p : ℝ) ^ (-2 * s.re) := by ring

theorem T_p_bound (f : ℕ → ℂ) (hf1 : f 1 = 1) (hb : ∀ n, ‖f n‖ ≤ 1) {p : ℕ} (hp : p.Prime)
    {s : ℂ} (hs : 1 < s.re) :
    ‖deriv (Work.BMF.gp f p) s / Work.BMF.gp f p s + f p * (Real.log p : ℂ) * (p : ℂ) ^ (-s)‖
      ≤ 16 * Real.log p * (p : ℝ) ^ (-2 * s.re) * ‖(Work.BMF.gp f p s)⁻¹‖ := by
  have hp0 : p ≠ 0 := hp.ne_zero
  have hlogp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hr2 : 0 ≤ (p : ℝ) ^ (-2 * s.re) := Real.rpow_nonneg (Nat.cast_nonneg p) _
  have hgpne : gp f p s ≠ 0 :=
    gp_ne_zero f hf1 hb (σ := (1 + s.re) / 2) (by linarith) p hp (by linarith)
  have hkey : deriv (gp f p) s / gp f p s + f p * (Real.log p : ℂ) * (p : ℂ) ^ (-s)
      = (deriv (gp f p) s + f p * (Real.log p : ℂ) * (p : ℂ) ^ (-s) * gp f p s)
          * (gp f p s)⁻¹ := by
    rw [div_eq_mul_inv]
    have h1 : gp f p s * (gp f p s)⁻¹ = 1 := mul_inv_cancel₀ hgpne
    calc deriv (gp f p) s * (gp f p s)⁻¹ + f p * (Real.log p : ℂ) * (p : ℂ) ^ (-s)
        = deriv (gp f p) s * (gp f p s)⁻¹
            + f p * (Real.log p : ℂ) * (p : ℂ) ^ (-s) * (gp f p s * (gp f p s)⁻¹) := by
          rw [h1, mul_one]
      _ = (deriv (gp f p) s + f p * (Real.log p : ℂ) * (p : ℂ) ^ (-s) * gp f p s)
            * (gp f p s)⁻¹ := by ring
  rw [hkey, norm_mul]
  have hcore := norm_deriv_add_fp_mul_le f hf1 hb hp hs
  have hinv := gp_inv_norm_ge_half f hf1 hb hp hs
  calc ‖deriv (gp f p) s + f p * (Real.log p : ℂ) * (p : ℂ) ^ (-s) * gp f p s‖
          * ‖(gp f p s)⁻¹‖
      ≤ (8 * Real.log p * (p : ℝ) ^ (-2 * s.re)) * ‖(gp f p s)⁻¹‖ :=
        mul_le_mul_of_nonneg_right hcore (norm_nonneg _)
    _ ≤ (16 * Real.log p * (p : ℝ) ^ (-2 * s.re)) * ‖(gp f p s)⁻¹‖ :=
        mul_le_mul_of_nonneg_right (by nlinarith [hlogp, hr2]) (norm_nonneg _)

end

end Work.BMF.mrlas
