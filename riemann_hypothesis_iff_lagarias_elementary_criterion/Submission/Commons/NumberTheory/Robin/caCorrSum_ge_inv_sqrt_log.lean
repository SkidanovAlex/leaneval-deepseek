import Mathlib
import Submission.Commons.NumberTheory.Robin.caMu_ge_iff_caF
import Submission.Commons.NumberTheory.Robin.caMu_pos
import Submission.Commons.NumberTheory.Robin.caExp_anti_p
import Submission.Commons.NumberTheory.Robin.caSupp_eq_primesLE_xi
import Submission.Commons.NumberTheory.Robin.caXi2_upper
import Submission.Commons.Analysis.Real.log_one_add_inv_div_log_strictAntiOn
import Submission.Commons.Analysis.Real.log_ratio_two_sandwich
import Submission.Commons.Analysis.Real.log_pow_le_sqrt_eventually
import Submission.Commons.NumberTheory.Chebyshev.sum_prime_inv_sq_lower_bound
import Submission.Commons.NumberTheory.Zeta.chebyshevTheta_sub_id_rh_bound
import Submission.Commons.NumberTheory.Robin.caXi_prime

set_option maxHeartbeats 4000000

open scoped BigOperators

namespace Commons.NumberTheory.Robin

noncomputable section

private def caMuR (p : ℕ) (ε : ℝ) : ℝ :=
  Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / ((((p : ℝ) ^ (1 + ε))) - (p : ℝ))) / Real.log (p : ℝ)

private def caExpR (p : ℕ) (ε : ℝ) : ℕ := ⌊caMuR p ε⌋₊

private def caFR (p : ℕ) (k : ℕ) : ℝ :=
  Real.log ((((p : ℝ) ^ (k + 1 : ℕ)) - 1) / ((((p : ℝ) ^ (k + 1 : ℕ))) - (p : ℝ))) / Real.log (p : ℝ)

private abbrev caBR (ε : ℝ) : ℕ := Nat.ceil (Real.exp (2 / ε)) + 2

private abbrev caSR (ε : ℝ) : Finset ℕ :=
  ((Finset.range (caBR ε)).filter Nat.Prime).filter (fun p : ℕ => 1 ≤ caExpR p ε)

private def gR (t : ℝ) : ℝ := Real.log (1 + 1/t)/Real.log t

private def g2R (t : ℝ) : ℝ := Real.log (1 + 1/(t + t^2))/Real.log t

private def caCorrLogR (p : ℕ) (k : ℕ) : ℝ :=
  Real.log ((((p:ℝ)^(k+1:ℕ)) - 1)/((p:ℝ)^(k+1:ℕ)))

private lemma mem_caSR {ε : ℝ} {p : ℕ} :
    p ∈ caSR ε ↔ Nat.Prime p ∧ p < caBR ε ∧ 1 ≤ caExpR p ε := by
  simp only [caSR, Finset.mem_filter, Finset.mem_range]
  tauto

private lemma caMuR_pos {p : ℕ} {ε : ℝ} (hp : 2 ≤ p) (hε : 0 < ε) : 0 < caMuR p ε := by
  simpa [caMuR] using caMu_pos (p := p) (ε := ε) hp hε

private lemma caExpR_ge_one_iff {p : ℕ} {ε : ℝ} (hp : 2 ≤ p) (hε : 0 < ε) :
    1 ≤ caExpR p ε ↔ ε ≤ caFR p 1 := by
  have hpos := caMuR_pos hp hε
  rw [caExpR, Nat.le_floor_iff (le_of_lt hpos)]
  simpa [caMuR, caFR] using (caMu_ge_iff_caF p ε 1 hp hε le_rfl)

private lemma caExpR_ge_two_iff {p : ℕ} {ε : ℝ} (hp : 2 ≤ p) (hε : 0 < ε) :
    2 ≤ caExpR p ε ↔ ε ≤ caFR p 2 := by
  have hpos := caMuR_pos hp hε
  rw [caExpR, Nat.le_floor_iff (le_of_lt hpos)]
  simpa [caMuR, caFR] using (caMu_ge_iff_caF p ε 2 hp hε (by norm_num))

private lemma caExpR_le_one_iff {p : ℕ} {ε : ℝ} (hp : 2 ≤ p) (hε : 0 < ε) :
    caExpR p ε ≤ 1 ↔ caFR p 2 < ε := by
  have h := caExpR_ge_two_iff (p:=p) (ε:=ε) hp hε
  have hnat : (caExpR p ε ≤ 1) ↔ ¬ (2 ≤ caExpR p ε) := by omega
  rw [hnat, h, not_le]

private lemma caExpR_eq_zero_iff {p : ℕ} {ε : ℝ} (hp : 2 ≤ p) (hε : 0 < ε) :
    caExpR p ε = 0 ↔ caFR p 1 < ε := by
  have h := caExpR_ge_one_iff (p:=p) (ε:=ε) hp hε
  have hnat : (caExpR p ε = 0) ↔ ¬ (1 ≤ caExpR p ε) := by omega
  rw [hnat, h, not_le]

private lemma caFR_one_eq (p : ℕ) (hp : 2 ≤ p) : caFR p 1 = gR p := by
  unfold caFR gR
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  have hpm1 : (p : ℝ) - 1 ≠ 0 := by
    have : (1:ℝ) < (p:ℝ) := by exact_mod_cast (by omega : 1 < p)
    linarith
  have hmain : (((p : ℝ) ^ (1 + 1 : ℕ)) - 1) / (((p : ℝ) ^ (1 + 1 : ℕ)) - (p : ℝ))
      = 1 + 1/(p : ℝ) := by
    have h2 : ((p : ℝ) ^ (1 + 1 : ℕ)) = (p:ℝ)^2 := by norm_num
    rw [h2]
    have hnum : (p:ℝ)^2 - 1 = ((p:ℝ)+1)*((p:ℝ)-1) := by ring
    have hden : (p:ℝ)^2 - (p:ℝ) = (p:ℝ)*((p:ℝ)-1) := by ring
    rw [hnum, hden]
    field_simp
  rw [hmain]

private lemma caFR_two_eq (p : ℕ) (hp : 2 ≤ p) : caFR p 2 = g2R p := by
  unfold caFR g2R
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  have hp1 : (1:ℝ) < (p:ℝ) := by exact_mod_cast (by omega : 1 < p)
  have h3 : ((p : ℝ) ^ (2 + 1 : ℕ)) = (p:ℝ)^3 := by norm_num
  have hden : (p:ℝ)^3 - (p:ℝ) ≠ 0 := by
    have heq : (p:ℝ)^3 - (p:ℝ) = (p:ℝ)*((p:ℝ)-1)*((p:ℝ)+1) := by ring
    rw [heq]
    exact ne_of_gt (mul_pos (mul_pos (by positivity) (by linarith)) (by linarith))
  have hfrac : ((p:ℝ)^3 - 1)/((p:ℝ)^3 - (p:ℝ)) = 1 + 1/((p:ℝ) + (p:ℝ)^2) := by
    rw [div_eq_iff hden]
    have hpp : (p:ℝ) + (p:ℝ)^2 ≠ 0 := by positivity
    field_simp
    ring
  rw [h3, hfrac]

private lemma gR_anti : StrictAntiOn gR (Set.Ioi 1) := by
  intro a ha b hb hab
  have h := Commons.Analysis.Real.log_one_add_inv_div_log_strictAntiOn ha hb hab
  simpa [gR, one_div] using h

private lemma gR_le_of_le {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) : gR b ≤ gR a := by
  rcases eq_or_lt_of_le hab with h | h
  · rw [← h]
  · exact le_of_lt (gR_anti ha (lt_trans ha h) h)

private lemma g2R_anti {a b : ℝ} (ha : 1 < a) (hab : a < b) : g2R b < g2R a := by
  have h := caXi2_upper_f2_strict ha hab
  simpa [g2R, one_div] using h

private lemma g2R_le_of_le {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) : g2R b ≤ g2R a := by
  rcases eq_or_lt_of_le hab with h | h
  · rw [← h]
  · exact le_of_lt (g2R_anti ha h)

private lemma g2R_sandwich_lo {x : ℝ} (hx : 2 ≤ x) : gR (x^2) ≤ g2R x := by
  have h := (Commons.Analysis.Real.log_ratio_two_sandwich hx).1
  simpa [gR, g2R, one_div] using h

private lemma g2R_sandwich_hi {x : ℝ} (hx : 2 ≤ x) : g2R x ≤ gR (x^2/2) := by
  have h := (Commons.Analysis.Real.log_ratio_two_sandwich hx).2
  simpa [gR, g2R, one_div] using h

/-- The support is exactly the set of primes `≤ ξ`. -/
private lemma supp_eq_primes_upto {ε : ℝ} (hε : 0 < ε) (hs : (caSR ε).Nonempty) {ξ : ℕ}
    (hξ : ξ = (caSR ε).sup id) :
    caSR ε = (Finset.range (ξ+1)).filter Nat.Prime := by
  have hmax : ξ = (caSR ε).max' hs := by
    rw [hξ, Finset.max'_eq_sup', Finset.sup'_eq_sup]
  have h := caSupp_eq_primesLE_xi (ε:=ε) hε hs
  change caSR ε = (Finset.range ((caSR ε).max' hs + 1)).filter Nat.Prime at h
  rw [h, hmax]

/-- `ξ = sup supp` belongs to the support. -/
private lemma xi_mem {ε : ℝ} (hs : (caSR ε).Nonempty) :
    (caSR ε).sup id ∈ caSR ε := by
  have h := Finset.sup_mem_of_nonempty (s := caSR ε) (f := id) hs
  simp only [id_eq, Set.mem_image, Finset.mem_coe] at h
  obtain ⟨x, hx, hfx⟩ := h
  rw [← hfx]; exact hx

private lemma eps_le_inv_xi_log {ε : ℝ} (hε : 0 < ε) (hs : (caSR ε).Nonempty) {ξ : ℕ}
    (hξ : ξ = (caSR ε).sup id) (hξ1 : 1 < ξ) :
    ε ≤ 1/((ξ:ℝ) * Real.log (ξ:ℝ)) := by
  have hmem : ξ ∈ caSR ε := by rw [hξ]; exact xi_mem hs
  have hp : Nat.Prime ξ := (mem_caSR.mp hmem).1
  have hone : 1 ≤ caExpR ξ ε := (mem_caSR.mp hmem).2.2
  have hiff := (caExpR_ge_one_iff (p:=ξ) (ε:=ε) hp.two_le hε).mp hone
  rw [caFR_one_eq ξ hp.two_le] at hiff
  have hξpos : (0:ℝ) < ξ := by positivity
  have hlogpos : 0 < Real.log (ξ:ℝ) := Real.log_pos (by exact_mod_cast hξ1)
  have hb := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 + 1/(ξ:ℝ) by positivity)
  have hb' : Real.log (1 + 1/(ξ:ℝ)) ≤ 1/(ξ:ℝ) := by
    have : (1:ℝ) + 1/(ξ:ℝ) - 1 = 1/(ξ:ℝ) := by ring
    linarith [hb, this.le, this.ge]
  have h1 : gR (ξ:ℝ) ≤ 1/((ξ:ℝ)*Real.log (ξ:ℝ)) := by
    unfold gR
    calc Real.log (1 + 1/(ξ:ℝ))/Real.log (ξ:ℝ)
        ≤ (1/(ξ:ℝ))/Real.log (ξ:ℝ) := div_le_div_of_nonneg_right hb' (le_of_lt hlogpos)
      _ = 1/((ξ:ℝ)*Real.log (ξ:ℝ)) := by field_simp
  exact le_trans hiff h1

private lemma exp_two_div_eps_ge {ε : ℝ} (hε : 0 < ε) (hs : (caSR ε).Nonempty) {ξ : ℕ}
    (hξ : ξ = (caSR ε).sup id) (hξ1 : 1 < ξ) :
    2*(ξ:ℝ) ≤ Real.exp (2/ε) := by
  have heps := eps_le_inv_xi_log hε hs hξ hξ1
  have hξpos : (0:ℝ) < ξ := by positivity
  have hlogpos : 0 < Real.log (ξ:ℝ) := Real.log_pos (by exact_mod_cast hξ1)
  have hden : 0 < (ξ:ℝ)*Real.log (ξ:ℝ) := mul_pos hξpos hlogpos
  have h1 : ε * ((ξ:ℝ)*Real.log (ξ:ℝ)) ≤ 1 := by
    have hm := mul_le_mul_of_nonneg_right heps (le_of_lt hden)
    rw [one_div, inv_mul_cancel₀ (ne_of_gt hden)] at hm
    exact hm
  have h2 : 2*(ξ:ℝ)*Real.log (ξ:ℝ) ≤ 2/ε := by
    rw [le_div_iff₀ hε]
    nlinarith [h1]
  have hrpow : Real.exp (2*((ξ:ℝ)*Real.log (ξ:ℝ))) = (ξ:ℝ)^(2*(ξ:ℝ)) := by
    rw [Real.rpow_def_of_pos hξpos]; ring_nf
  have h3 : 2*(ξ:ℝ) ≤ (ξ:ℝ)^(2*(ξ:ℝ)) := by
    have h1le : (1:ℝ) ≤ (ξ:ℝ) := by exact_mod_cast (le_of_lt hξ1)
    have h2le : (2:ℝ) ≤ (ξ:ℝ) := by exact_mod_cast (by omega : 2 ≤ ξ)
    have hsplit : (ξ:ℝ)^(2*(ξ:ℝ)) = (ξ:ℝ)^(((2:ℕ):ℝ)) * (ξ:ℝ)^(2*(ξ:ℝ)-2) := by
      rw [← Real.rpow_add hξpos]; congr 1; push_cast; ring
    rw [hsplit]
    have hge1 : (ξ:ℝ) ≤ (ξ:ℝ)^(2*(ξ:ℝ)-2) := by
      have h := Real.rpow_le_rpow_of_exponent_le h1le (by linarith : (1:ℝ) ≤ 2*(ξ:ℝ)-2)
      simpa using h
    have hA1 : (1:ℝ) ≤ (ξ:ℝ)^(2*(ξ:ℝ)-2) := le_trans h1le hge1
    have hstep : (ξ:ℝ)^2 ≤ (ξ:ℝ)^(((2:ℕ):ℝ)) * (ξ:ℝ)^(2*(ξ:ℝ)-2) := by
      rw [Real.rpow_natCast]
      calc (ξ:ℝ)^2 = (ξ:ℝ)^2 * 1 := by ring
        _ ≤ (ξ:ℝ)^2 * (ξ:ℝ)^(2*(ξ:ℝ)-2) :=
            mul_le_mul_of_nonneg_left hA1 (by positivity)
    nlinarith [hstep, h2le, hξpos]
  have h4 : Real.exp (2*((ξ:ℝ)*Real.log (ξ:ℝ))) ≤ Real.exp (2/ε) := by
    apply Real.exp_le_exp.mpr
    nlinarith [h2]
  linarith [hrpow ▸ h4, h3]

private lemma two_mul_xi_lt_caBR {ε : ℝ} (hε : 0 < ε) (hs : (caSR ε).Nonempty) {ξ : ℕ}
    (hξ : ξ = (caSR ε).sup id) (hξ1 : 1 < ξ) :
    2*ξ < caBR ε := by
  have hexp := exp_two_div_eps_ge hε hs hξ hξ1
  have hceil : Real.exp (2/ε) ≤ ((Nat.ceil (Real.exp (2/ε)) : ℕ) : ℝ) := Nat.le_ceil _
  have h1 : (2*(ξ:ℝ)) < (Nat.ceil (Real.exp (2/ε)) : ℝ) + 2 := by linarith
  have h2 : (2*ξ : ℕ) < Nat.ceil (Real.exp (2/ε)) + 2 := by
    rw [← Nat.cast_lt (α := ℝ)]
    push_cast
    linarith
  simpa [caBR] using h2

private lemma exists_prime_gt_xi {ε : ℝ} (hε : 0 < ε) (hs : (caSR ε).Nonempty) {ξ : ℕ}
    (hξ : ξ = (caSR ε).sup id) (hξ1 : 1 < ξ) :
    ∃ p : ℕ, Nat.Prime p ∧ ξ < p ∧ p ≤ 2*ξ ∧ p < caBR ε := by
  obtain ⟨p, hp, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul ξ (by omega)
  have h2 := two_mul_xi_lt_caBR hε hs hξ hξ1
  exact ⟨p, hp, hlt, hle, lt_of_le_of_lt hle h2⟩

private lemma eps_gt_gR_two_xi {ε : ℝ} (hε : 0 < ε) (hs : (caSR ε).Nonempty) {ξ : ℕ}
    (hξ : ξ = (caSR ε).sup id) (hξ1 : 1 < ξ) :
    gR (2*(ξ:ℝ)) < ε := by
  have hS := supp_eq_primes_upto hε hs hξ
  obtain ⟨p, hp, hlt, hle, hpB⟩ := exists_prime_gt_xi hε hs hξ hξ1
  have hpS : p ∉ caSR ε := by
    rw [hS]
    intro h
    have := Finset.mem_range.mp (Finset.mem_filter.mp h).1
    omega
  have hzero : caExpR p ε = 0 := by
    by_contra hne
    exact hpS (mem_caSR.mpr ⟨hp, hpB, Nat.one_le_iff_ne_zero.mpr hne⟩)
  have hgt := (caExpR_eq_zero_iff (p:=p) (ε:=ε) hp.two_le hε).mp hzero
  rw [caFR_one_eq p hp.two_le] at hgt
  have h2ξ : 1 < 2*(ξ:ℝ) := by
    have : (1:ℝ) < (ξ:ℝ) := by exact_mod_cast hξ1
    linarith
  have hple : (p:ℝ) ≤ 2*(ξ:ℝ) := by exact_mod_cast hle
  have hp1 : (1:ℝ) < (p:ℝ) := by exact_mod_cast hp.one_lt
  have hg := gR_le_of_le (a := (p:ℝ)) (b := 2*(ξ:ℝ)) hp1 hple
  linarith [hgt, hg]

private lemma eps_le_gR_xi {ε : ℝ} (hε : 0 < ε) (hs : (caSR ε).Nonempty) {ξ : ℕ}
    (hξ : ξ = (caSR ε).sup id) (hξ1 : 1 < ξ) : ε ≤ gR (ξ:ℝ) := by
  have hmem : ξ ∈ caSR ε := by rw [hξ]; exact xi_mem hs
  have hp : Nat.Prime ξ := (mem_caSR.mp hmem).1
  have hone : 1 ≤ caExpR ξ ε := (mem_caSR.mp hmem).2.2
  have hiff := (caExpR_ge_one_iff (p:=ξ) (ε:=ε) hp.two_le hε).mp hone
  rwa [caFR_one_eq ξ hp.two_le] at hiff

private lemma g2R_two_gt_one_tenth : (1:ℝ)/10 < g2R 2 := by
  unfold g2R
  have h2 : (2:ℝ) + 2^2 = 6 := by norm_num
  rw [h2]
  have hlog76 : (1:ℝ)/7 ≤ Real.log (1 + 1/6) := by
    have h := Real.one_sub_inv_le_log_of_pos (show (0:ℝ) < 1 + 1/6 by norm_num)
    have he : (1:ℝ) - (1 + 1/6)⁻¹ = 1/7 := by norm_num
    linarith [h, he.le, he.ge]
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2le : Real.log 2 ≤ 7/10 := by linarith [Real.log_two_lt_d9]
  rw [lt_div_iff₀ hlog2pos]
  nlinarith [hlog76, hlog2le]

private lemma two_le_caExpR_two {ε : ℝ} (hε : 0 < ε) (hs : (caSR ε).Nonempty) {ξ : ℕ}
    (hξ : ξ = (caSR ε).sup id) (hξ1 : 1 < ξ) (hξbig : (10:ℝ) ≤ (ξ:ℝ)) :
    2 ≤ caExpR 2 ε := by
  have heps := eps_le_inv_xi_log hε hs hξ hξ1
  have hξpos : (0:ℝ) < ξ := by positivity
  have hlog10 : (1:ℝ) ≤ Real.log 10 := by
    rw [Real.log_ten_eq]; linarith [Real.log_two_gt_d9, Real.log_five_gt_d9]
  have hlogξ : (1:ℝ) ≤ Real.log (ξ:ℝ) :=
    le_trans hlog10 (Real.log_le_log (by norm_num) hξbig)
  have heps10 : ε ≤ 1/10 := by
    have h1 : ε ≤ 1/((ξ:ℝ)) := by
      refine le_trans heps ?_
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith [hlogξ, hξpos]
    have h2 : 1/(ξ:ℝ) ≤ 1/10 := one_div_le_one_div_of_le (by norm_num) hξbig
    linarith
  have hle : ε ≤ g2R 2 := by
    have := g2R_two_gt_one_tenth
    linarith
  have := (caExpR_ge_two_iff (p:=2) (ε:=ε) (by norm_num) hε).mpr ?_
  · exact this
  · rw [caFR_two_eq 2 (by norm_num)]; exact hle

private lemma sqgt_of_gR_lt {a b : ℝ} (ha : 1 < a) (hb : 1 < b) (h : gR a < gR b) : b < a := by
  by_contra hcon
  push_neg at hcon
  have := gR_le_of_le ha hcon
  linarith

private lemma four_sqrt_lt_rpow {ξ : ℝ} (hξ : 10 ≤ ξ) : 4*Real.sqrt ξ < ξ^(2*ξ) := by
  have hξpos : 0 < ξ := by linarith
  have hsqrt_le : Real.sqrt ξ ≤ ξ := Real.sqrt_le_self_iff.mpr (Or.inr (by linarith))
  have hsplit : ξ^(2*ξ) = ξ^(((2:ℕ):ℝ)) * ξ^(2*ξ-2) := by
    rw [← Real.rpow_add hξpos]; congr 1; push_cast; ring
  rw [hsplit, Real.rpow_natCast]
  have hA1 : (1:ℝ) ≤ ξ^(2*ξ-2) :=
    Real.one_le_rpow (by linarith : (1:ℝ) ≤ ξ) (by linarith : (0:ℝ) ≤ 2*ξ-2)
  have hkey : 4*Real.sqrt ξ < ξ^2 := by
    have h1 : 4*Real.sqrt ξ ≤ 4*ξ := by nlinarith [hsqrt_le]
    have h2 : 4*ξ < ξ^2 := by nlinarith [hξ]
    linarith
  nlinarith [hkey, hA1, hξpos]

private lemma four_sqrt_lt_caBR {ε : ℝ} (hε : 0 < ε) (hs : (caSR ε).Nonempty) {ξ : ℕ}
    (hξ : ξ = (caSR ε).sup id) (hξ1 : 1 < ξ) (hξ10 : 10 ≤ ξ) :
    4*Real.sqrt (ξ:ℝ) < (caBR ε : ℝ) := by
  have heps := eps_le_inv_xi_log hε hs hξ hξ1
  have hξpos : (0:ℝ) < ξ := by positivity
  have hlogpos : 0 < Real.log (ξ:ℝ) := Real.log_pos (by exact_mod_cast hξ1)
  have hden : 0 < (ξ:ℝ)*Real.log (ξ:ℝ) := mul_pos hξpos hlogpos
  have h1 : ε * ((ξ:ℝ)*Real.log (ξ:ℝ)) ≤ 1 := by
    have hm := mul_le_mul_of_nonneg_right heps (le_of_lt hden)
    rw [one_div, inv_mul_cancel₀ (ne_of_gt hden)] at hm
    exact hm
  have h2 : 2*(ξ:ℝ)*Real.log (ξ:ℝ) ≤ 2/ε := by
    rw [le_div_iff₀ hε]; nlinarith [h1]
  have hexp : Real.exp (2*((ξ:ℝ)*Real.log (ξ:ℝ))) ≤ Real.exp (2/ε) :=
    Real.exp_le_exp.mpr (by nlinarith [h2])
  have hrpow : Real.exp (2*((ξ:ℝ)*Real.log (ξ:ℝ))) = (ξ:ℝ)^(2*(ξ:ℝ)) := by
    rw [Real.rpow_def_of_pos hξpos]; ring_nf
  have hlt := four_sqrt_lt_rpow (by exact_mod_cast hξ10 : (10:ℝ) ≤ ξ)
  have hceil : Real.exp (2/ε) ≤ ((Nat.ceil (Real.exp (2/ε)) : ℕ) : ℝ) := Nat.le_ceil _
  have : 4*Real.sqrt (ξ:ℝ) < ((Nat.ceil (Real.exp (2/ε)) + 2 : ℕ) : ℝ) := by
    push_cast
    linarith [hlt, hexp, hrpow ▸ hexp]
  simpa [caBR] using this

private lemma xi2_bounds {ε : ℝ} (hε : 0 < ε) (hs : (caSR ε).Nonempty) {ξ : ℕ}
    (hξ : ξ = (caSR ε).sup id) (hξ1 : 1 < ξ) (hξ10 : 10 ≤ ξ) :
    ∃ x2 : ℕ, 2 ≤ x2 ∧ x2 ∈ caSR ε ∧ 2 ≤ caExpR x2 ε ∧
      (∀ p ∈ caSR ε, 2 ≤ caExpR p ε → p ≤ x2) ∧
      Real.sqrt (ξ:ℝ)/2 ≤ (x2:ℝ) ∧ (x2:ℝ) ≤ 2*Real.sqrt (ξ:ℝ) := by
  have hξ10r : (10:ℝ) ≤ (ξ:ℝ) := by exact_mod_cast hξ10
  have h2exp : 2 ≤ caExpR 2 ε := two_le_caExpR_two hε hs hξ hξ1 hξ10r
  have h2mem : 2 ∈ caSR ε := by
    refine mem_caSR.mpr ⟨by norm_num, ?_, le_trans (by norm_num : 1 ≤ 2) h2exp⟩
    unfold caBR
    have hc : 1 ≤ Nat.ceil (Real.exp (2/ε)) := Nat.one_le_ceil_iff.mpr (Real.exp_pos _)
    omega
  let T : Finset ℕ := (caSR ε).filter (fun p => 2 ≤ caExpR p ε)
  have hTne : T.Nonempty := ⟨2, Finset.mem_filter.mpr ⟨h2mem, h2exp⟩⟩
  set x2 : ℕ := T.max' hTne with hx2def
  have hx2T : x2 ∈ T := by rw [hx2def]; exact Finset.max'_mem T hTne
  have hx2S : x2 ∈ caSR ε := (Finset.mem_filter.mp hx2T).1
  have hx2exp : 2 ≤ caExpR x2 ε := (Finset.mem_filter.mp hx2T).2
  have hx2max : ∀ p ∈ caSR ε, 2 ≤ caExpR p ε → p ≤ x2 := by
    intro p hpS hpe
    rw [hx2def]
    exact Finset.le_max' T p (Finset.mem_filter.mpr ⟨hpS, hpe⟩)
  have hx2prime : Nat.Prime x2 := (mem_caSR.mp hx2S).1
  have hx2ge2 : 2 ≤ x2 := hx2prime.two_le
  have h1x2 : (1:ℝ) < x2 := by exact_mod_cast hx2prime.one_lt
  have hepsxi : ε ≤ gR (ξ:ℝ) := eps_le_gR_xi hε hs hξ hξ1
  have hgt2xi : gR (2*(ξ:ℝ)) < ε := eps_gt_gR_two_xi hε hs hξ hξ1
  have hx2g2 : ε ≤ g2R (x2:ℝ) := by
    have := (caExpR_ge_two_iff (p:=x2) (ε:=ε) hx2prime.two_le hε).mp hx2exp
    rwa [caFR_two_eq x2 hx2prime.two_le] at this
  have hsqrtξ1 : (1:ℝ) ≤ Real.sqrt (ξ:ℝ) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]; exact_mod_cast (le_of_lt hξ1)
  have h2sqrt : (1:ℝ) < 2*Real.sqrt (ξ:ℝ) := by linarith
  have hx2lt : (x2:ℝ) < 2*Real.sqrt (ξ:ℝ) := by
    by_contra hcon
    push_neg at hcon
    have hanti := g2R_le_of_le (a := 2*Real.sqrt (ξ:ℝ)) h2sqrt hcon
    have hsh := g2R_sandwich_hi (x := 2*Real.sqrt (ξ:ℝ)) (by linarith)
    have h2sq : (2*Real.sqrt (ξ:ℝ))^2/2 = 2*(ξ:ℝ) := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]; ring
    rw [h2sq] at hsh
    linarith [hanti, hsh, hx2g2, hgt2xi]
  have hx2le2sqrt : (x2:ℝ) ≤ 2*Real.sqrt (ξ:ℝ) := le_of_lt hx2lt
  have hfour : 4*Real.sqrt (ξ:ℝ) < (caBR ε : ℝ) := four_sqrt_lt_caBR hε hs hξ hξ1 hξ10
  obtain ⟨p1, hp1prime, hp1lt, hp1le⟩ := Nat.exists_prime_lt_and_le_two_mul x2 (by omega)
  have hp1B : p1 < caBR ε := by
    have h1 : (p1:ℝ) ≤ 2*(x2:ℝ) := by exact_mod_cast hp1le
    have h2 : 2*(x2:ℝ) ≤ 4*Real.sqrt (ξ:ℝ) := by linarith [hx2le2sqrt]
    have h3 : (p1:ℝ) < (caBR ε : ℝ) := by linarith
    exact_mod_cast h3
  have hp1le1 : caExpR p1 ε ≤ 1 := by
    by_cases hp1S : p1 ∈ caSR ε
    · by_contra hcon
      push_neg at hcon
      have hmemT : p1 ∈ T := Finset.mem_filter.mpr ⟨hp1S, hcon⟩
      have := hx2max p1 hp1S hcon
      omega
    · have hzero : caExpR p1 ε = 0 := by
        by_contra hne
        exact hp1S (mem_caSR.mpr ⟨hp1prime, hp1B, Nat.one_le_iff_ne_zero.mpr hne⟩)
      omega
  have hgtp1 : g2R (p1:ℝ) < ε := by
    have := (caExpR_le_one_iff (p:=p1) (ε:=ε) hp1prime.two_le hε).mp hp1le1
    rwa [caFR_two_eq p1 hp1prime.two_le] at this
  have hp1r : (1:ℝ) < (p1:ℝ) := by exact_mod_cast hp1prime.one_lt
  have hp1ler : (p1:ℝ) ≤ 2*(x2:ℝ) := by exact_mod_cast hp1le
  have hx2r : (1:ℝ) < 2*(x2:ℝ) := by
    have : (1:ℝ) < (x2:ℝ) := by exact_mod_cast hx2prime.one_lt
    linarith
  have hg2mono : g2R (2*(x2:ℝ)) ≤ g2R (p1:ℝ) := g2R_le_of_le (a := (p1:ℝ)) hp1r hp1ler
  have hsand : gR ((2*(x2:ℝ))^2) ≤ g2R (2*(x2:ℝ)) := g2R_sandwich_lo (by linarith : (2:ℝ) ≤ 2*(x2:ℝ))
  have hchain : gR (4*(x2:ℝ)^2) < gR (ξ:ℝ) := by
    have h1 : gR ((2*(x2:ℝ))^2) = gR (4*(x2:ℝ)^2) := by ring_nf
    rw [← h1]
    linarith [hsand, hg2mono, hgtp1, hepsxi]
  have hA1 : (1:ℝ) < 4*(x2:ℝ)^2 := by
    have hx2ge2r : (2:ℝ) ≤ (x2:ℝ) := by exact_mod_cast hx2ge2
    nlinarith [hx2ge2r]
  have h4x2 : (ξ:ℝ) < 4*(x2:ℝ)^2 := sqgt_of_gR_lt (a := 4*(x2:ℝ)^2) (b := (ξ:ℝ)) hA1
      (by exact_mod_cast hξ1 : (1:ℝ) < (ξ:ℝ)) hchain
  have hsqrtlt : Real.sqrt (ξ:ℝ) < 2*(x2:ℝ) := by
    rw [Real.sqrt_lt' (by positivity)]
    nlinarith [h4x2]
  exact ⟨x2, hx2ge2, hx2S, hx2exp, hx2max, by linarith, hx2le2sqrt⟩

private lemma block_one_eq {ε : ℝ} (hε : 0 < ε) {ξ x2 : ℕ}
    (hS : caSR ε = (Finset.range (ξ+1)).filter Nat.Prime)
    (hx2S : x2 ∈ caSR ε) (hx2exp : 2 ≤ caExpR x2 ε)
    (hx2max : ∀ p ∈ caSR ε, 2 ≤ caExpR p ε → p ≤ x2) :
    (caSR ε).filter (fun p => caExpR p ε = 1) = (Finset.Ioc x2 ξ).filter Nat.Prime := by
  ext p
  constructor
  · intro hp
    rw [Finset.mem_filter] at hp
    obtain ⟨hpS, hp1⟩ := hp
    have hpprime : Nat.Prime p := (mem_caSR.mp hpS).1
    have hpξ : p ≤ ξ := by
      rw [hS] at hpS
      have := Finset.mem_range.mp (Finset.mem_filter.mp hpS).1
      omega
    have hpx2 : x2 < p := by
      by_contra hcon
      push_neg at hcon
      have h2 : 2 ≤ caExpR p ε := by
        rcases eq_or_lt_of_le hcon with h | h
        · rw [h]; exact hx2exp
        · exact le_trans hx2exp (caExp_anti_p (p:=p) (q:=x2)
            hpprime.two_le (mem_caSR.mp hx2S).1.two_le hε h)
      omega
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hpx2, hpξ⟩, hpprime⟩
  · intro hp
    rw [Finset.mem_filter, Finset.mem_Ioc] at hp
    obtain ⟨⟨hx2p, hpξ⟩, hpprime⟩ := hp
    have hpS : p ∈ caSR ε := by
      rw [hS]
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hpprime⟩
    have hle : caExpR p ε ≤ 1 := by
      by_contra hcon
      push_neg at hcon
      exact absurd (hx2max p hpS hcon) (by omega)
    have hpS1 : 1 ≤ caExpR p ε := (mem_caSR.mp hpS).2.2
    exact Finset.mem_filter.mpr ⟨hpS, by omega⟩

private lemma exists_xi0_large {C : ℝ} (hC : 0 < C) :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ ξ : ℝ, T ≤ ξ → 283*C*(Real.log ξ)^10 ≤ ξ^(1/4 : ℝ) := by
  obtain ⟨y0, hy0⟩ := Commons.Analysis.Real.log_pow_le_sqrt_eventually 10 (1024*283*C) (by positivity)
  refine ⟨max (y0^2) 1, le_max_right _ _, fun ξ hξ => ?_⟩
  have hξ1 : 1 ≤ ξ := le_trans (le_max_right _ _) hξ
  have hξ0 : 0 < ξ := lt_of_lt_of_le zero_lt_one hξ1
  have hy : y0 ≤ Real.sqrt ξ := by
    have h2 : y0^2 ≤ ξ := le_trans (le_max_left _ _) hξ
    calc y0 ≤ |y0| := le_abs_self y0
      _ = Real.sqrt (y0^2) := (Real.sqrt_sq_eq_abs y0).symm
      _ ≤ Real.sqrt ξ := Real.sqrt_le_sqrt h2
  have h := hy0 (Real.sqrt ξ) hy
  have hlog : Real.log (Real.sqrt ξ) = Real.log ξ / 2 := by
    rw [Real.log_sqrt (le_of_lt hξ0)]
  have hsqrtsqrt : Real.sqrt (Real.sqrt ξ) = ξ^(1/4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul (le_of_lt hξ0)]
    norm_num
  have hpow : ((Real.log ξ)/2)^10 = (Real.log ξ)^10/1024 := by
    rw [div_pow]; norm_num
  calc 283*C*(Real.log ξ)^10 = 1024*283*C*((Real.log ξ)/2)^10 := by rw [hpow]; ring
    _ = 1024*283*C*(Real.log (Real.sqrt ξ))^10 := by rw [hlog]
    _ ≤ Real.sqrt (Real.sqrt ξ) := h
    _ = ξ^(1/4 : ℝ) := hsqrtsqrt


theorem caCorrSum_ge_inv_sqrt_log (h : RiemannHypothesis) : ∃ ξ₀ : ℝ, ∀ (ε : ℝ), 0 < ε → ∀ ξ : ℕ, ξ = (((Finset.range (Nat.ceil (Real.exp (2 / ε)) + 2)).filter Nat.Prime).filter (fun p : ℕ => 1 ≤ ⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / ((((p : ℝ) ^ (1 + ε))) - (p : ℝ))) / Real.log (p : ℝ)⌋₊)).sup id → ξ₀ ≤ (ξ : ℝ) → 0.8 / (Real.sqrt (ξ : ℝ) * Real.log (ξ : ℝ)) ≤ - (Finset.sum (((Finset.range (Nat.ceil (Real.exp (2 / ε)) + 2)).filter Nat.Prime).filter (fun p : ℕ => 1 ≤ ⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / ((((p : ℝ) ^ (1 + ε))) - (p : ℝ))) / Real.log (p : ℝ)⌋₊)) (fun p : ℕ => Real.log ((((p : ℝ) ^ (⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / ((((p : ℝ) ^ (1 + ε))) - (p : ℝ))) / Real.log (p : ℝ)⌋₊ + 1)) - 1) / ((p : ℝ) ^ (⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / ((((p : ℝ) ^ (1 + ε))) - (p : ℝ))) / Real.log (p : ℝ)⌋₊ + 1))))) := by
  obtain ⟨C, hCpos, x0, hθb⟩ := Commons.NumberTheory.Zeta.chebyshevTheta_sub_id_rh_bound h
  have hC0 : (0:ℝ) ≤ C := le_of_lt hCpos
  obtain ⟨T, hT1, hT⟩ := exists_xi0_large hCpos
  refine ⟨max (max (4*x0^2 + 4) ((10:ℝ)^100)) T, ?_⟩
  intro ε hε ξ hξraw hξ0
  change 0.8 / (Real.sqrt (ξ : ℝ) * Real.log (ξ : ℝ))
      ≤ - (Finset.sum (caSR ε) (fun p => caCorrLogR p (caExpR p ε)))
  set s : ℝ := Real.sqrt (ξ:ℝ) with hsdef
  set L : ℝ := Real.log (ξ:ℝ) with hLdef
  have hA : max (4*x0^2+4) ((10:ℝ)^100) ≤ (ξ:ℝ) := le_trans (le_max_left _ _) hξ0
  have hTle : T ≤ (ξ:ℝ) := le_trans (le_max_right _ _) hξ0
  have h4x0 : 4*x0^2+4 ≤ (ξ:ℝ) := le_trans (le_max_left _ _) hA
  have h10 : (10:ℝ)^100 ≤ (ξ:ℝ) := le_trans (le_max_right _ _) hA
  have h10le : (10:ℝ) ≤ (ξ:ℝ) := le_trans (by norm_num : (10:ℝ) ≤ (10:ℝ)^100) h10
  have hξ10 : 10 ≤ ξ := by exact_mod_cast h10le
  have hξ1 : 1 < ξ := by omega
  have hξpos : (0:ℝ) < (ξ:ℝ) := by positivity
  have hξ : ξ = (caSR ε).sup id := by
    simpa [caSR, caBR, caExpR, caMuR] using hξraw
  have hs : (caSR ε).Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    have h0 : (caSR ε).sup id = 0 := by rw [hemp]; simp
    rw [hξ, h0] at h10le
    norm_num at h10le
  have hξmax : ξ = (caSR ε).max' hs := by rw [hξ, Finset.max'_eq_sup', Finset.sup'_eq_sup]
  have hS := supp_eq_primes_upto hε hs hξ
  obtain ⟨x2, hx2ge2, hx2S, hx2exp, hx2max, hx2lo, hx2hi⟩ := xi2_bounds hε hs hξ hξ1 hξ10
  have hblock := block_one_eq hε hS hx2S hx2exp hx2max
  have hspos : 0 < s := by rw [hsdef]; exact Real.sqrt_pos.mpr hξpos
  have hs2 : s^2 = (ξ:ℝ) := by rw [hsdef]; exact Real.sq_sqrt (le_of_lt hξpos)
  have hLpos : 0 < L := by rw [hLdef]; exact Real.log_pos (by linarith)
  have hsLpos : 0 < s*L := mul_pos hspos hLpos
  have hlog2le : Real.log 2 ≤ 7/10 := by linarith [Real.log_two_lt_d9]
  have hlog2nn : (0:ℝ) ≤ Real.log 2 := le_of_lt (Real.log_pos (by norm_num))
  have hlog10 : (23:ℝ)/10 ≤ Real.log 10 := by
    rw [Real.log_ten_eq]; linarith [Real.log_two_gt_d9, Real.log_five_gt_d9]
  have hL230 : 230 ≤ L := by
    rw [hLdef]
    have h1 : Real.log ((10:ℝ)^100) ≤ Real.log (ξ:ℝ) := Real.log_le_log (by norm_num) h10
    rw [Real.log_pow] at h1
    push_cast at h1
    have h2 : (230:ℝ) ≤ 100 * Real.log 10 := by linarith [hlog10]
    linarith [h1, h2]
  have hsbig : (200:ℝ) ≤ s := by
    rw [hsdef]
    have h1 : Real.sqrt ((200:ℝ)^2) ≤ Real.sqrt (ξ:ℝ) := Real.sqrt_le_sqrt (by nlinarith [h10])
    rwa [Real.sqrt_sq (by norm_num)] at h1
  have hx2rp : (0:ℝ) < (x2:ℝ) := by
    have : (0:ℕ) < x2 := by omega
    exact_mod_cast this
  -- sum bounds
  have hsum1 : -(Finset.sum (caSR ε) (fun p => caCorrLogR p (caExpR p ε)))
      = Finset.sum (caSR ε) (fun p => -(caCorrLogR p (caExpR p ε))) :=
    (Finset.sum_neg_distrib _).symm
  have hnonneg : ∀ p ∈ caSR ε, 0 ≤ -(caCorrLogR p (caExpR p ε)) := by
    intro p hpS
    have hp : Nat.Prime p := (mem_caSR.mp hpS).1
    have hk : 1 ≤ caExpR p ε := (mem_caSR.mp hpS).2.2
    have hppos : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp.pos
    have hpowpos : (0:ℝ) < (p:ℝ)^(caExpR p ε + 1) := pow_pos hppos _
    have hfrac : (((p:ℝ)^(caExpR p ε+1:ℕ)) - 1)/((p:ℝ)^(caExpR p ε+1:ℕ))
        = 1 - 1/(p:ℝ)^(caExpR p ε+1) := by
      field_simp
    rw [caCorrLogR, hfrac]
    have h1' : 1/(p:ℝ)^(caExpR p ε+1) < 1 := by
      rw [div_lt_one hpowpos]
      have hp1 : (1:ℝ) < (p:ℝ) := by exact_mod_cast hp.one_lt
      have hle : (1:ℕ) ≤ caExpR p ε + 1 := by omega
      have h1 : (1:ℝ) < (p:ℝ)^1 := by simpa using hp1
      exact lt_of_lt_of_le h1 (pow_le_pow_right₀ (le_of_lt hp1) hle)
    have hpos : (0:ℝ) < 1 - 1/(p:ℝ)^(caExpR p ε+1) := by linarith
    have hle1 : 1 - 1/(p:ℝ)^(caExpR p ε+1) ≤ 1 := by
      have : (0:ℝ) ≤ 1/(p:ℝ)^(caExpR p ε+1) := by positivity
      linarith
    have := Real.log_nonpos (le_of_lt hpos) hle1
    linarith
  have hstepA : Finset.sum ((caSR ε).filter (fun p => caExpR p ε = 1))
        (fun p => -(caCorrLogR p (caExpR p ε)))
      ≤ Finset.sum (caSR ε) (fun p => -(caCorrLogR p (caExpR p ε))) :=
    Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => (Finset.mem_filter.mp hp).1)
      (fun p hpS _ => hnonneg p hpS)
  have hstepB : Finset.sum ((caSR ε).filter (fun p => caExpR p ε = 1)) (fun p => (1:ℝ)/(p:ℝ)^2)
      ≤ Finset.sum ((caSR ε).filter (fun p => caExpR p ε = 1)) (fun p => -(caCorrLogR p (caExpR p ε))) := by
    refine Finset.sum_le_sum ?_
    intro p hp
    have hp1 : caExpR p ε = 1 := (Finset.mem_filter.mp hp).2
    have hpS : p ∈ caSR ε := (Finset.mem_filter.mp hp).1
    have hpprime : Nat.Prime p := (mem_caSR.mp hpS).1
    have hppos : (0:ℝ) < (p:ℝ) := by exact_mod_cast hpprime.pos
    have hp2pos : (0:ℝ) < (p:ℝ)^2 := pow_pos hppos 2
    rw [hp1, caCorrLogR]
    have h2 : ((p:ℝ)^(1+1:ℕ)) = (p:ℝ)^2 := by norm_num
    rw [h2]
    have hfrac : (((p:ℝ)^2) - 1)/((p:ℝ)^2) = 1 - 1/(p:ℝ)^2 := by
      field_simp
    rw [hfrac]
    have h1' : 1/(p:ℝ)^2 < 1 := by
      rw [div_lt_one hp2pos]
      have hp2 : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hpprime.two_le
      nlinarith
    have hpos : (0:ℝ) < 1 - 1/(p:ℝ)^2 := by linarith
    have hlog := Real.log_le_sub_one_of_pos hpos
    have he : (1:ℝ) - 1/(p:ℝ)^2 - 1 = -(1/(p:ℝ)^2) := by ring
    linarith [hlog, he.le, he.ge]
  have hQsum : Finset.sum ((Finset.Ioc x2 ξ).filter Nat.Prime) (fun p => (1:ℝ)/(p:ℝ)^2)
      ≤ Finset.sum (caSR ε) (fun p => -(caCorrLogR p (caExpR p ε))) := by
    rw [← hblock]
    exact le_trans hstepB hstepA
  -- master bound
  have hx0le : x0 ≤ s/2 := by
    have h4 : 4*x0^2 ≤ (ξ:ℝ) := by linarith [h4x0]
    have habs : |2*x0| ≤ s := by
      rw [hsdef]
      exact Real.abs_le_sqrt (by nlinarith [h4])
    have h1 : x0 ≤ |2*x0|/2 := by
      have := le_abs_self (2*x0); linarith
    linarith [habs]
  have hθx : ∀ t ∈ Set.Icc (x2:ℝ) (ξ:ℝ),
      |Chebyshev.theta t - t| ≤ C * Real.sqrt t * (Real.log t)^10 := by
    intro t ht
    exact hθb t (le_trans hx0le (le_trans hx2lo ht.1))
  have hx2ξ : x2 ≤ ξ := by
    have h2 : 2*s < (ξ:ℝ) := by nlinarith [hs2, hspos, hsbig]
    have : (x2:ℝ) < (ξ:ℝ) := lt_of_le_of_lt hx2hi h2
    exact_mod_cast le_of_lt this
  have hQm := Commons.NumberTheory.Chebyshev.sum_prime_inv_sq_lower_bound (n:=x2) (m:=ξ) hx2ge2 hx2ξ hC0 hθx
  have hQm' : (1/((x2:ℝ)*Real.log (x2:ℝ))) * (1 - (x2:ℝ)/min (ξ:ℝ) ((x2:ℝ)^2) - 1/(Real.log (x2:ℝ)))
        - 5*C*L^9/((x2:ℝ)^(3/2:ℝ))
      ≤ Finset.sum ((Finset.Ioc x2 ξ).filter Nat.Prime) (fun p => (1:ℝ)/(p:ℝ)^2) := by
    rw [Finset.sum_filter]
    simpa [hLdef] using hQm
  -- P bound
  have hlogx2pos : 0 < Real.log (x2:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < x2))
  have hlogx2le : Real.log (x2:ℝ) ≤ Real.log (2*s) :=
    Real.log_le_log hx2rp (by linarith [hx2hi])
  have hlog2s : Real.log (2*s) = Real.log 2 + L/2 := by
    rw [Real.log_mul (by norm_num) (ne_of_gt hspos), hLdef]
    congr 1
    rw [hsdef, Real.log_sqrt (le_of_lt hξpos)]
  have hlogx2le' : Real.log (x2:ℝ) ≤ Real.log 2 + L/2 := by rw [← hlog2s]; exact hlogx2le
  have hx2l2le : (x2:ℝ)*Real.log (x2:ℝ) ≤ s*(L + 2*Real.log 2) := by
    have h1 : (x2:ℝ)*Real.log (x2:ℝ) ≤ (2*s)*(Real.log 2 + L/2) :=
      mul_le_mul hx2hi hlogx2le' (le_of_lt hlogx2pos) (by positivity)
    have h2 : (2*s)*(Real.log 2 + L/2) = s*(L + 2*Real.log 2) := by ring
    linarith [h1, h2.le, h2.ge]
  have hP : 0.99/(s*L) ≤ 1/((x2:ℝ)*Real.log (x2:ℝ)) := by
    have h1 : 1/(s*(L + 2*Real.log 2)) ≤ 1/((x2:ℝ)*Real.log (x2:ℝ)) :=
      one_div_le_one_div_of_le (mul_pos hx2rp hlogx2pos) hx2l2le
    have h2 : 0.99/(s*L) ≤ 1/(s*(L + 2*Real.log 2)) := by
      rw [div_le_div_iff₀ hsLpos (mul_pos hspos (by linarith : (0:ℝ) < L + 2*Real.log 2))]
      nlinarith [hL230, hlog2le, hspos]
    linarith [h1, h2]
  -- F bound
  have hx2min : (x2:ℝ)/min (ξ:ℝ) ((x2:ℝ)^2) ≤ 0.01 := by
    by_cases hle : (ξ:ℝ) ≤ (x2:ℝ)^2
    · rw [min_eq_left hle]
      have h1 : (x2:ℝ)/(ξ:ℝ) ≤ 2*s/(ξ:ℝ) := div_le_div_of_nonneg_right hx2hi (le_of_lt hξpos)
      have h2 : 2*s/(ξ:ℝ) = 2/s := by rw [← hs2]; field_simp
      have h3 : 2/s ≤ 0.01 := by rw [div_le_iff₀ hspos]; nlinarith [hsbig]
      linarith [h1, h2.le, h2.ge, h3]
    · rw [min_eq_right (le_of_lt (not_le.mp hle))]
      have h2' : (x2:ℝ)/(x2:ℝ)^2 = 1/(x2:ℝ) := by field_simp
      have h3 : 1/(x2:ℝ) ≤ 0.01 := by
        rw [div_le_iff₀ hx2rp]; nlinarith [hsbig, hx2lo]
      linarith [h2'.le, h2'.ge, h3]
  have hlogx2ge : 100 ≤ Real.log (x2:ℝ) := by
    have h1 : Real.log (s/2) ≤ Real.log (x2:ℝ) := Real.log_le_log (by positivity) hx2lo
    have h2 : Real.log (s/2) = L/2 - Real.log 2 := by
      rw [Real.log_div (ne_of_gt hspos) (by norm_num), hLdef, hsdef, Real.log_sqrt (le_of_lt hξpos)]
    nlinarith [h1, h2.le, h2.ge, hL230, hlog2le]
  have hF : 0.98 ≤ 1 - (x2:ℝ)/min (ξ:ℝ) ((x2:ℝ)^2) - 1/(Real.log (x2:ℝ)) := by
    have h1 : 1/(Real.log (x2:ℝ)) ≤ 0.01 := by
      rw [div_le_iff₀ hlogx2pos]; linarith [hlogx2ge]
    linarith [hx2min, h1]
  -- C big
  have hs12 : s^(1/2:ℝ) = (ξ:ℝ)^(1/4:ℝ) := by
    rw [hsdef, Real.sqrt_eq_rpow, ← Real.rpow_mul (le_of_lt hξpos)]
    norm_num
  have hCbig : 283*C*L^10 ≤ (ξ:ℝ)^(1/4:ℝ) := by
    have h1 := hT (ξ:ℝ) hTle
    rw [hLdef]
    exact h1
  -- E bound
  have hs32 : s^(3/2:ℝ) = s * s^(1/2:ℝ) := by
    rw [show (3/2:ℝ) = 1 + 1/2 by norm_num, Real.rpow_add hspos, Real.rpow_one]
  have hx232 : (s/2)^(3/2:ℝ) ≤ (x2:ℝ)^(3/2:ℝ) :=
    Real.rpow_le_rpow (by positivity) hx2lo (by norm_num)
  have hdiv : (s/2)^(3/2:ℝ) = s^(3/2:ℝ)/2^(3/2:ℝ) := Real.div_rpow (le_of_lt hspos) (by norm_num) (3/2:ℝ)
  have hE : 5*C*L^9/((x2:ℝ)^(3/2:ℝ)) ≤ 0.05/(s*L) := by
    have hCL : C*L^9 ≤ (ξ:ℝ)^(1/4:ℝ)/(283*L) := by
      rw [le_div_iff₀ (by positivity : (0:ℝ) < 283*L)]
      nlinarith [hCbig, hLpos]
    have hstep : 5*C*L^9/((x2:ℝ)^(3/2:ℝ)) ≤ 5*C*L^9/((s/2)^(3/2:ℝ)) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hx232
    have hkey : 5*C*L^9/((s/2)^(3/2:ℝ)) = 5*C*L^9*2^(3/2:ℝ)/(s*(ξ:ℝ)^(1/4:ℝ)) := by
      rw [hdiv, hs32, hs12]; field_simp
    have hkey2 : 5*C*L^9*2^(3/2:ℝ)/(s*(ξ:ℝ)^(1/4:ℝ))
        ≤ 5*(2^(3/2:ℝ))/(283*s*L) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have e1 : 5*C*L^9*2^(3/2:ℝ) * (283*s*L) = 5*(2^(3/2:ℝ))*s*(283*C*L^10) := by ring
      have e2 : 5*(2^(3/2:ℝ)) * (s*(ξ:ℝ)^(1/4:ℝ)) = 5*(2^(3/2:ℝ))*s*((ξ:ℝ)^(1/4:ℝ)) := by ring
      rw [e1, e2]
      exact mul_le_mul_of_nonneg_left hCbig (by positivity : (0:ℝ) ≤ 5*(2:ℝ)^(3/2:ℝ)*s)
    have hkey3 : 5*(2^(3/2:ℝ))/(283*s*L) ≤ 0.05/(s*L) := by
      rw [div_le_div_iff₀ (by positivity) hsLpos]
      have h2 : (2:ℝ)^(3/2:ℝ) ≤ 2.83 := by
        rw [show (3/2:ℝ) = 1 + 1/2 by norm_num, Real.rpow_add (by norm_num) , Real.rpow_one]
        have hs2 : Real.sqrt 2 ≤ 1.4143 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
        have he : (2:ℝ)^(1/2:ℝ) = Real.sqrt 2 := (Real.sqrt_eq_rpow 2).symm
        rw [he]; nlinarith [hs2]
      nlinarith [h2, hsLpos]
    linarith [hstep, hkey.le, hkey.ge, hkey2, hkey3]
  -- combine
  have hPF : (0.99/(s*L))*0.98
      ≤ (1/((x2:ℝ)*Real.log (x2:ℝ))) * (1 - (x2:ℝ)/min (ξ:ℝ) ((x2:ℝ)^2) - 1/(Real.log (x2:ℝ))) :=
    mul_le_mul hP hF (by norm_num) (by positivity)
  have hfinal : 0.8/(s*L) ≤ Finset.sum ((Finset.Ioc x2 ξ).filter Nat.Prime) (fun p => (1:ℝ)/(p:ℝ)^2) := by
    have hring : (0.99/(s*L))*0.98 = 0.99*0.98/(s*L) := by ring
    have hcoef : (0.8:ℝ) ≤ (0.99*0.98 - 0.05) := by norm_num
    have h1 : 0.8/(s*L) ≤ (0.99*0.98 - 0.05)/(s*L) :=
      div_le_div_of_nonneg_right hcoef (le_of_lt hsLpos)
    have h2 : (0.99*0.98 - 0.05)/(s*L)
        ≤ (1/((x2:ℝ)*Real.log (x2:ℝ))) * (1 - (x2:ℝ)/min (ξ:ℝ) ((x2:ℝ)^2) - 1/(Real.log (x2:ℝ))) - 5*C*L^9/((x2:ℝ)^(3/2:ℝ)) := by
      have h3 : (0.99*0.98 - 0.05)/(s*L) = (0.99/(s*L))*0.98 - 0.05/(s*L) := by
        field_simp
      rw [h3]
      linarith [hPF, hE]
    exact le_trans h1 (le_trans h2 hQm')
  rw [hsum1]
  exact le_trans hfinal hQsum

end
end Commons.NumberTheory.Robin
