import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Submission.Commons.Analysis.SpecialFunctions.arctan_ge_taylor8
import Submission.Commons.Analysis.SpecialFunctions.log_one_add_le_quintic
import Submission.Commons.Analysis.Integral.integral_inv_sq_add
import Submission.Commons.Analysis.Real.log_one_add_upper

namespace Commons.Analysis.Integral

open MeasureTheory intervalIntegral
open scoped Real

noncomputable section

/-! ## Concrete arithmetic constants and bounding functions -/

/-- Upper bound for `Real.log 2`, a rational. -/
def cLog2UB : ℝ := 6931471808/10^10
/-- Lower bound for `Real.log 2`. -/
def cLog2LB : ℝ := 6931471803/10^10
/-- Upper bound for `Real.log 3`. -/
def cLog3UB : ℝ := 10986122888/10^10
/-- Lower bound for `Real.log 3`. -/
def cLog3LB : ℝ := 10986122885/10^10
/-- Lower bound for `∫_{1/4}^{3/4} log s ds`. -/
def cJlogLB : ℝ := (3/4)*cLog3LB - cLog2UB - 1/2
/-- Upper bound for `∫_{1/4}^{3/4} s^2 log s ds`. -/
def cJlog2UB : ℝ := (9/64)*cLog3UB - (13/48)*cLog2LB - 13/288

lemma log_two_le_cLog2UB : Real.log 2 ≤ cLog2UB := by
  have h := Real.log_two_lt_d9
  unfold cLog2UB; norm_num; linarith

lemma cLog2LB_le_log_two : cLog2LB ≤ Real.log 2 := by
  have h := Real.log_two_gt_d9
  unfold cLog2LB; norm_num; linarith

lemma log_three_le_cLog3UB : Real.log 3 ≤ cLog3UB := by
  have h := Real.log_three_lt_d9
  unfold cLog3UB; norm_num; linarith

lemma cLog3LB_le_log_three : cLog3LB ≤ Real.log 3 := by
  have h := Real.log_three_gt_d9
  unfold cLog3LB; norm_num; linarith

lemma cJlog2UB_nonpos : cJlog2UB ≤ 0 := by unfold cJlog2UB cLog2LB cLog3UB; norm_num

/-- The eight-term Taylor lower bound function for `arctan`. -/
def boxT8 (z : ℝ) : ℝ :=
  z - z^3/3 + z^5/5 - z^7/7 + z^9/9 - z^11/11 + z^13/13 - z^15/15

lemma arctan_ge_boxT8 {z : ℝ} (hz : 0 ≤ z) : boxT8 z ≤ Real.arctan z :=
  Commons.Analysis.SpecialFunctions.arctan_ge_taylor8 z hz

/-- Quintic upper bound for `log (1+u)` on `[0,1]`. -/
def bL1 (u : ℝ) : ℝ := u - u^2/2 + u^3/3 - u^4/4 + u^5/5

lemma log_one_add_le_bL1 {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) :
    Real.log (1+u) ≤ bL1 u :=
  Commons.Analysis.SpecialFunctions.log_one_add_le_quintic h0 h1

/-- Six-term upper bound for `log (1-u)`. -/
def bL2 (u : ℝ) : ℝ :=
  -(u + u^2/2 + u^3/3 + u^4/4 + u^5/5 + u^6/6)

lemma bL2_eq_neg_sum (u : ℝ) :
    bL2 u = -(∑ i ∈ Finset.range 6, u^(i+1)/((i:ℝ)+1)) := by
  simp [bL2, Finset.sum_range_succ]
  ring

lemma log_one_sub_le_bL2 {u : ℝ} (h0 : 0 ≤ u) (h1 : u < 1) :
    Real.log (1-u) ≤ bL2 u := by
  have habs : |u| < 1 := by rw [abs_of_nonneg h0]; exact h1
  have hs := Real.hasSum_pow_div_log_of_abs_lt_one habs
  have hle := hs.summable.sum_le_tsum (Finset.range 6)
    (fun i _ => by positivity)
  rw [hs.tsum_eq] at hle
  rw [bL2_eq_neg_sum]
  linarith

/-- Tail bound: for `0 ≤ u ≤ 3/4`, `log (1-u) ≥ -(Σ_{k=1}^{12} u^k/k) - 4 u^13/13`. -/
def blog1m (u : ℝ) : ℝ :=
  -(u + u^2/2 + u^3/3 + u^4/4 + u^5/5 + u^6/6 + u^7/7 + u^8/8 + u^9/9 + u^10/10
      + u^11/11 + u^12/12) - 4*u^13/13

lemma blog1m_eq (u : ℝ) :
    blog1m u = -(∑ i ∈ Finset.range 12, u^(i+1)/((i:ℝ)+1)) - 4*u^13/13 := by
  simp [blog1m, Finset.sum_range_succ]
  ring

lemma blog1m_le_log_one_sub {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 3/4) :
    blog1m u ≤ Real.log (1-u) := by
  have hu1 : u < 1 := by linarith
  have habs : |u| < 1 := by rw [abs_of_nonneg h0]; exact hu1
  have habs2 : ‖u‖ < 1 := by rwa [Real.norm_eq_abs]
  have hs := Real.hasSum_pow_div_log_of_abs_lt_one habs
  set f : ℕ → ℝ := fun n => u^(n+1)/((n:ℝ)+1) with hf
  have hsplit : (∑ i ∈ Finset.range 12, f i) + (∑' i, f (i+12)) = ∑' i, f i :=
    hs.summable.sum_add_tsum_nat_add 12
  have hsum : ∑' i : ℕ, f i = -Real.log (1-u) := hs.tsum_eq
  have hgsum : Summable (fun i : ℕ => u^13 * u^i / 13) :=
    ((hasSum_geometric_of_norm_lt_one habs2).summable.mul_left (u^13)).div_const 13
  have htail : ∑' i : ℕ, f (i+12) ≤ ∑' i : ℕ, u^13 * u^i / 13 := by
    have hs' : Summable (fun i : ℕ => f (i+12)) := (summable_nat_add_iff 12).mpr hs.summable
    refine Summable.tsum_le_tsum (f := fun i => f (i+12)) (g := fun i => u^13 * u^i / 13) ?_ hs' hgsum
    intro i
    have h1 : f (i+12) = u^(i+13)/((i:ℝ)+13) := by simp only [hf]; push_cast; ring
    have h2 : u^13 * u^i / 13 = u^(i+13)/13 := by rw [← pow_add]; ring
    rw [h1, h2]
    apply div_le_div_of_nonneg_left (by positivity) (by norm_num)
    have h3 : (0:ℝ) ≤ (i:ℝ) := Nat.cast_nonneg i
    push_cast
    linarith
  have hgeo : ∑' i : ℕ, u^13 * u^i / 13 = u^13 * (1-u)⁻¹ / 13 := by
    have hg := (hasSum_geometric_of_norm_lt_one habs2).mul_left (u^13)
    have h2 : HasSum (fun i : ℕ => u^13 * u^i / 13) (u^13 * (1-u)⁻¹ / 13) := by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hg.div_const 13
    exact h2.tsum_eq
  have hfin : u^13 * (1-u)⁻¹ / 13 ≤ 4*u^13/13 := by
    have hpos : (0:ℝ) < 1-u := by linarith
    have hle : (1-u)⁻¹ ≤ 4 := by
      rw [inv_le_comm₀ hpos (by norm_num)]; linarith
    have h13 : (0:ℝ) ≤ u^13 := by positivity
    calc u^13 * (1-u)⁻¹ / 13 ≤ u^13 * 4 / 13 := by
          apply div_le_div_of_nonneg_right _ (by norm_num)
          exact mul_le_mul_of_nonneg_left hle h13
      _ = 4*u^13/13 := by ring
  have htail4 : ∑' i : ℕ, f (i+12) ≤ 4*u^13/13 := le_trans (le_trans htail (le_of_eq hgeo)) hfin
  rw [blog1m_eq]
  have hS : (∑ i ∈ Finset.range 12, u ^ (i + 1) / ((↑i : ℝ) + 1)) = (∑ i ∈ Finset.range 12, f i) := by
    apply Finset.sum_congr rfl; intro i _; simp [hf]
  rw [hS]
  linarith [hsplit, hsum, htail4]

/-! ## The bounding functions -/

def bx1 (u : ℝ) : ℝ := (4+8*u)/(7+16*u+16*u^2)
def bx2 (u : ℝ) : ℝ := (16-8*u)/(67-64*u+16*u^2)
def bxq (u : ℝ) : ℝ := (8+8*u)/(19+32*u+16*u^2)

lemma bx1_antitone {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1) : bx1 y ≤ bx1 x := by
  unfold bx1
  have hx2 : 0 < 7+16*x+16*x^2 := by nlinarith [sq_nonneg x]
  have hy2 : 0 < 7+16*y+16*y^2 := by nlinarith [sq_nonneg y]
  rw [div_le_div_iff₀ hy2 hx2]
  have key : (4+8*x)*(7+16*y+16*y^2) - (4+8*y)*(7+16*x+16*x^2) = (y-x)*(128*x*y+64*x+64*y+8) := by ring
  nlinarith [key, mul_nonneg (sub_nonneg.mpr hxy) (by nlinarith : (0:ℝ) ≤ 128*x*y+64*x+64*y+8)]

lemma bx2_monotone {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1) : bx2 x ≤ bx2 y := by
  unfold bx2
  have hx2 : 0 < 67-64*x+16*x^2 := by nlinarith [sq_nonneg (4*x-8)]
  have hy2 : 0 < 67-64*y+16*y^2 := by nlinarith [sq_nonneg (4*y-8)]
  rw [div_le_div_iff₀ hx2 hy2]
  have key : (16-8*y)*(67-64*x+16*x^2) - (16-8*x)*(67-64*y+16*y^2) = (y-x)*(128*x*y-256*x-256*y+488) := by ring
  have h2 : x*(y-1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hx (by linarith)
  nlinarith [key, mul_nonneg (sub_nonneg.mpr hxy) (by nlinarith : (0:ℝ) ≤ 128*x*y-256*x-256*y+488),
    h2, hx, hxy, hy]

lemma bxq_antitone {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1) : bxq y ≤ bxq x := by
  unfold bxq
  have hx2 : 0 < 19+32*x+16*x^2 := by nlinarith [sq_nonneg x]
  have hy2 : 0 < 19+32*y+16*y^2 := by nlinarith [sq_nonneg y]
  rw [div_le_div_iff₀ hy2 hx2]
  have key : (8+8*x)*(19+32*y+16*y^2) - (8+8*y)*(19+32*x+16*x^2) = (y-x)*(128*x*y+128*x+128*y+104) := by ring
  nlinarith [key, mul_nonneg (sub_nonneg.mpr hxy) (by nlinarith : (0:ℝ) ≤ 128*x*y+128*x+128*y+104)]

def bqcoef (u : ℝ) : ℝ := 2*u/(1+u) + u^2/(1+u)^3

lemma bqcoef_monotone {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1) : bqcoef x ≤ bqcoef y := by
  unfold bqcoef
  have hx1 : (0:ℝ) < 1+x := by linarith
  have hy1 : (0:ℝ) < 1+y := by linarith
  have h1 : x/(1+x) ≤ y/(1+y) := by
    rw [div_le_div_iff₀ hx1 hy1]; nlinarith
  have k1 : x/(1+x)^2 ≤ y/(1+y)^2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have e : y*(1+x)^2 - x*(1+y)^2 = (y-x)*(1-x*y) := by ring
    nlinarith [e, mul_nonneg (sub_nonneg.mpr hxy) (by nlinarith : (0:ℝ) ≤ 1-x*y)]
  have e1 : x^2/(1+x)^3 = (x/(1+x))*(x/(1+x)^2) := by field_simp
  have e2 : y^2/(1+y)^3 = (y/(1+y))*(y/(1+y)^2) := by field_simp
  rw [e1, e2]
  have h2 : (x/(1+x))*(x/(1+x)^2) ≤ (y/(1+y))*(y/(1+y)^2) :=
    mul_le_mul h1 k1 (div_nonneg hx (by positivity : (0:ℝ) ≤ (1+x)^2)) (div_nonneg (le_trans hx hxy) hy1.le)
  have h3 : 2*x/(1+x) ≤ 2*y/(1+y) := by
    rw [show 2*x/(1+x) = 2*(x/(1+x)) by ring, show 2*y/(1+y) = 2*(y/(1+y)) by ring]
    linarith
  linarith [h3, h2]

def bR3s (u : ℝ) : ℝ :=
  (13/96)*(1/(4*(1+u)^2)) - (3/2)*(121/2560)*(1/(4*(1+u)^2))^2
    + (5/6)*(1093/57344)*(1/(4*(1+u)^2))^3

def bg (p : ℝ) : ℝ := (13/96)*p - (3/2)*(121/2560)*p^2 + (5/6)*(1093/57344)*p^3

lemma bg_monotone {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) (hq : q ≤ 1/4) : bg p ≤ bg q := by
  unfold bg
  have key : (13/96)*q - (3/2)*(121/2560)*q^2 + (5/6)*(1093/57344)*q^3
      - ((13/96)*p - (3/2)*(121/2560)*p^2 + (5/6)*(1093/57344)*p^3)
      = (q-p)*((13/96) - (3/2)*(121/2560)*(p+q) + (5/6)*(1093/57344)*(p^2+p*q+q^2)) := by ring
  have hb : 0 < (13/96) - (3/2)*(121/2560)*(p+q) + (5/6)*(1093/57344)*(p^2+p*q+q^2) := by
    nlinarith [hp, hpq, hq, sq_nonneg p, sq_nonneg q, mul_nonneg hp (le_trans hp hpq)]
  nlinarith [key, hb, hpq]

lemma bR3s_antitone {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1) : bR3s y ≤ bR3s x := by
  unfold bR3s
  have hx1 : (0:ℝ) < 1+x := by linarith
  have hy1 : (0:ℝ) < 1+y := by linarith
  have hcx : 0 < 4*(1+x)^2 := mul_pos (by norm_num) (pow_pos hx1 2)
  have hcy : 0 < 1/(4*(1+y)^2) := one_div_pos.mpr (mul_pos (by norm_num) (pow_pos hy1 2))
  have hcb : 4*(1+x)^2 ≤ 4*(1+y)^2 := by nlinarith
  have hcyx : 1/(4*(1+y)^2) ≤ 1/(4*(1+x)^2) :=
    one_div_le_one_div_of_le hcx hcb
  have hcxq : 1/(4*(1+x)^2) ≤ 1/4 := by
    rw [div_le_div_iff₀ hcx (by norm_num)]
    nlinarith
  have h := bg_monotone hcy.le hcyx hcxq
  simpa only [bg] using h

def bR4s (u : ℝ) : ℝ :=
  (1/(4*(1-u)^2))*((13/96) - (121/2560)*(1/(4*(1+u^2))))

lemma bR4s_monotone {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1/4) : bR4s x ≤ bR4s y := by
  unfold bR4s
  have hy1 : (0:ℝ) < 1-y := by linarith
  have hbx : 0 < 4*(1-y)^2 := mul_pos (by norm_num) (pow_pos hy1 2)
  have hbb : 4*(1-y)^2 ≤ 4*(1-x)^2 := by nlinarith
  have h1 : 1/(4*(1-x)^2) ≤ 1/(4*(1-y)^2) := one_div_le_one_div_of_le hbx hbb
  have h2 : (13/96) - (121/2560)*(1/(4*(1+x^2))) ≤ (13/96) - (121/2560)*(1/(4*(1+y^2))) := by
    have hax : 0 < 4*(1+x^2) := by positivity
    have hab : 4*(1+x^2) ≤ 4*(1+y^2) := by nlinarith
    have hh : (1/(4*(1+y^2))) ≤ (1/(4*(1+x^2))) := one_div_le_one_div_of_le hax hab
    linarith
  have h1p : 0 ≤ 1/(4*(1-y)^2) := by positivity
  have h2p : 0 ≤ (13/96) - (121/2560)*(1/(4*(1+x^2))) := by
    have hh : (1/(4*(1+x^2))) ≤ 1/4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    nlinarith
  exact mul_le_mul h1 h2 h2p h1p

def beJ2 (u : ℝ) : ℝ := ((1-u) - (1/64)/(1-u)^2)/12

lemma beJ2_antitone {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 3/4) : beJ2 y ≤ beJ2 x := by
  unfold beJ2
  have hy1 : (0:ℝ) < 1-y := by linarith
  have hx1 : (0:ℝ) < 1-x := by linarith
  have hy2 : (0:ℝ) < (1-y)^2 := pow_pos hy1 2
  have h : (1-y)^2 ≤ (1-x)^2 := by nlinarith
  have h4 : (1/(1-x)^2) ≤ (1/(1-y)^2) := by
    rw [one_div, one_div, inv_le_inv₀ (pow_pos hx1 2) hy2]
    nlinarith
  have key : ((1-x) - (1/64)/(1-x)^2) - ((1-y) - (1/64)/(1-y)^2)
      = ((1-x)-(1-y)) + (1/64)*((1/(1-y)^2) - (1/(1-x)^2)) := by ring
  have hpos : (0:ℝ) ≤ ((1-x) - (1/64)/(1-x)^2) - ((1-y) - (1/64)/(1-y)^2) := by
    rw [key]
    have : (0:ℝ) ≤ (1/64)*((1/(1-y)^2) - (1/(1-x)^2)) :=
      mul_nonneg (by norm_num) (by linarith)
    linarith
  linarith

def bCof (u : ℝ) : ℝ := u - 5/4 + 1/(768*(1+u^2))

lemma bCof_monotone {x y : ℝ} (hx : 1/4 ≤ x) (hxy : x ≤ y) (hy : y ≤ 3/4) : bCof x ≤ bCof y := by
  unfold bCof
  have hmain : (1:ℝ)/(768*(1+x^2)) - 1/(768*(1+y^2)) ≤ y - x := by
    have key : (1:ℝ)/(768*(1+x^2)) - 1/(768*(1+y^2)) = (y-x)*((x+y)/(768*(1+x^2)*(1+y^2))) := by
      field_simp
      ring
    rw [key]
    have hpos : (0:ℝ) ≤ y-x := sub_nonneg.mpr hxy
    have hle : (x+y)/(768*(1+x^2)*(1+y^2)) ≤ 1 := by
      rw [div_le_one (by positivity)]
      nlinarith [hx, hxy, hy, sq_nonneg x, sq_nonneg y]
    have := mul_le_mul_of_nonneg_left hle hpos
    linarith
  linarith

lemma bCof_nonpos {u : ℝ} (hx : 1/4 ≤ u) (hy : u ≤ 3/4) : bCof u ≤ 0 := by
  unfold bCof
  have h2 : (1/(768*(1+u^2))) ≤ 1/768 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  linarith



/-! ## Pointwise bounds and integral computations -/

lemma integral_log_range {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) :
    (∫ t in p..q, Real.log t) = q*Real.log q - q - (p*Real.log p - p) := by
  have hderiv : ∀ x ∈ Set.uIcc p q,
      HasDerivAt ((id * Real.log - id) : ℝ → ℝ) (Real.log x) x := by
    intro x hx
    simp only [Set.uIcc_of_le hpq, Set.mem_Icc] at hx
    have hx0 : x ≠ 0 := by linarith [hx.1]
    have h1 := (hasDerivAt_id x).mul (Real.hasDerivAt_log hx0)
    have h3 := h1.sub (hasDerivAt_id x)
    refine h3.congr_deriv ?_
    simp only [id_eq]
    rw [one_mul, mul_inv_cancel₀ hx0]; ring
  have hcont : ContinuousOn (fun t : ℝ => Real.log t) (Set.uIcc p q) := by
    have h2 : Set.uIcc p q = Set.Icc p q := Set.uIcc_of_le hpq
    rw [h2]
    apply ContinuousOn.log (by fun_prop)
    intro x hx
    exact ne_of_gt (by linarith [hx.1] : (0:ℝ) < x)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
  rw [h]
  have hg : ((id * Real.log - id : ℝ → ℝ) q) = q*Real.log q - q := by simp only [Pi.sub_apply, Pi.mul_apply, id_eq]
  have hg2 : ((id * Real.log - id : ℝ → ℝ) p) = p*Real.log p - p := by simp only [Pi.sub_apply, Pi.mul_apply, id_eq]
  rw [hg, hg2]

lemma integral_inv_range {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) :
    (∫ t in p..q, (t:ℝ)⁻¹) = Real.log q - Real.log p := by
  have hderiv : ∀ x ∈ Set.uIcc p q, HasDerivAt Real.log ((x:ℝ)⁻¹) x := by
    intro x hx
    simp only [Set.uIcc_of_le hpq, Set.mem_Icc] at hx
    have : (0:ℝ) < x := by linarith [hx.1]
    exact Real.hasDerivAt_log (ne_of_gt this)
  have hcont : ContinuousOn (fun t : ℝ => (t:ℝ)⁻¹) (Set.uIcc p q) := by
    rw [Set.uIcc_of_le hpq]
    apply ContinuousOn.inv₀ (by fun_prop)
    intro x hx
    exact ne_of_gt (by linarith [hx.1] : (0:ℝ) < x)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
  rw [h]

lemma log_one_add_le_cubic {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.log (1+x) ≤ x - x^2/2 + x^3/3 := by
  have h := Commons.Analysis.SpecialFunctions.log_one_add_le_quintic hx0 hx1
  have h2 : x^4/4 - x^5/5 ≥ 0 := by
    have : (0:ℝ) ≤ x^4 * (1/4 - x/5) := mul_nonneg (pow_nonneg hx0 4) (by linarith)
    nlinarith [this]
  linarith

def bhh (β s : ℝ) : ℝ := (3/2-β)/((3/2-β)^2+s^2) + (1+β)/((1+β)^2+s^2)

def bT3 (β s : ℝ) : ℝ := Real.log ((4*(2-β)^2+s^2)/(2*(2-β)*s))*(1-s^2/(4*(2-β)^2))
def bT4 (β s : ℝ) : ℝ :=
  if s ≤ β then Real.log ((4*β^2+s^2)/(2*β*s))*(1-s^2/(2*((2-β)^2+β^2)))
  else (2-β)*β/(s*Real.sqrt ((2-β)^2+s^2))

def bT3ub (β s : ℝ) : ℝ :=
  (1-s^2/(4*(2-β)^2))*((s^2/(4*(2-β)^2)) - (s^2/(4*(2-β)^2))^2/2 + (s^2/(4*(2-β)^2))^3/3)
  + (1-s^2/(4*(2-β)^2))*(Real.log (2*(2-β)) - Real.log s)

def bT4ub (β s : ℝ) : ℝ :=
  if s ≤ β then (1-s^2/(2*((2-β)^2+β^2)))*(s^2/(4*β^2))
      + (1-s^2/(2*((2-β)^2+β^2)))*(Real.log (2*β) - Real.log s)
  else β/s

/-- The integrand of the target inequality (verbatim from the requested statement). -/
def boxE (β s : ℝ) : ℝ :=
  ( (13/5)*((3/2-β)/((3/2-β)^2+s^2)+(1+β)/((1+β)^2+s^2))
    + ((2-β)^2-β^2)/(2*((2-β)^2+s^2))
    + ((2-β)^2-β^2)^2/(8*((2-β)^2+s^2)^2)
    + ((2-β)^2-β^2)^3/(16*((2-β)^2+s^2)^3)
    - Real.log ((4*(2-β)^2+s^2)/(2*(2-β)*s))*(1-s^2/(4*(2-β)^2))
    - (if s ≤ β then Real.log ((4*β^2+s^2)/(2*β*s))*(1-s^2/(2*((2-β)^2+β^2)))
               else (2-β)*β/(s*Real.sqrt ((2-β)^2+s^2))) )

lemma bhh_eq_boxE_part (β s : ℝ) :
    (13/5)*bhh β s = (13/5)*((3/2-β)/((3/2-β)^2+s^2)+(1+β)/((1+β)^2+s^2)) := by
  unfold bhh; ring

lemma bT3_le {β s : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hs1 : 1/4 ≤ s) (hs2 : s ≤ 3/4) :
    bT3 β s ≤ bT3ub β s := by
  unfold bT3 bT3ub
  have hb : (1:ℝ) ≤ 2-β := by linarith
  have hbpos : (0:ℝ) < 2-β := by linarith
  have hspos : (0:ℝ) < s := by linarith
  set v : ℝ := s^2/(4*(2-β)^2) with hv
  have hv0 : 0 ≤ v := by rw [hv]; positivity
  have hv1 : v ≤ 1 := by
    rw [hv]; rw [div_le_one (by positivity)]
    nlinarith [hs2, hb]
  have hlog : Real.log (1+v) ≤ v - v^2/2 + v^3/3 := log_one_add_le_cubic hv0 hv1
  have hkey : Real.log ((4*(2-β)^2+s^2)/(2*(2-β)*s)) = Real.log (2*(2-β)) - Real.log s + Real.log (1+v) := by
    have h1 : Real.log ((4*(2-β)^2+s^2)/(2*(2-β)*s)) - Real.log (2*(2-β)/s) = Real.log (1+v) := by
      rw [← Real.log_div (by positivity) (by positivity)]
      congr 1
      rw [hv]; field_simp; ring
    have h2 : Real.log (2*(2-β)/s) = Real.log (2*(2-β)) - Real.log s :=
      Real.log_div (by positivity) (by positivity)
    linarith
  have hfac : (0:ℝ) ≤ 1 - v := by linarith
  rw [hkey]
  have h1 : (1-v)*Real.log (1+v) ≤ (1-v)*(v - v^2/2 + v^3/3) :=
    mul_le_mul_of_nonneg_left hlog hfac
  nlinarith [h1, hfac]

lemma bT4_le {β s : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hs1 : 1/4 ≤ s) (hs2 : s ≤ 3/4) :
    bT4 β s ≤ bT4ub β s := by
  unfold bT4 bT4ub
  by_cases h : s ≤ β
  · rw [if_pos h, if_pos h]
    have hbpos : (0:ℝ) < 2-β := by linarith
    have hspos : (0:ℝ) < s := by linarith
    have hb2 : (0:ℝ) < (2-β)^2 := pow_pos hbpos 2
    set m : ℝ := s^2/(2*((2-β)^2+β^2)) with hm
    have hm0 : 0 ≤ m := by rw [hm]; positivity
    have hm1 : m ≤ 1 := by
      rw [hm, div_le_one (by positivity)]
      nlinarith [hs2, hβ0, hβ1, sq_nonneg β, sq_nonneg (2-β), sq_nonneg s]
    have hv0 : 0 ≤ s^2/(4*β^2) := by positivity
    have hv1 : s^2/(4*β^2) ≤ 1 := by
      rw [div_le_one (by positivity)]
      nlinarith [h, hβ0]
    have hlog : Real.log (1 + s^2/(4*β^2)) ≤ s^2/(4*β^2) :=
      Commons.Analysis.Real.log_one_add_upper hv0
    have hkey : Real.log ((4*β^2+s^2)/(2*β*s)) = Real.log (2*β) - Real.log s + Real.log (1+s^2/(4*β^2)) := by
      have h1 : Real.log ((4*β^2+s^2)/(2*β*s)) - Real.log (2*β/s) = Real.log (1+s^2/(4*β^2)) := by
        rw [← Real.log_div (by positivity) (by positivity)]
        congr 1
        field_simp; ring
      have h2 : Real.log (2*β/s) = Real.log (2*β) - Real.log s :=
        Real.log_div (by positivity) (by positivity)
      linarith
    have hfac : (0:ℝ) ≤ 1 - m := by linarith
    rw [hkey]
    have h1 : (1-m)*Real.log (1 + s^2/(4*β^2)) ≤ (1-m)*(s^2/(4*β^2)) :=
      mul_le_mul_of_nonneg_left hlog hfac
    nlinarith [h1]
  · rw [if_neg h, if_neg h]
    have hbpos : (0:ℝ) < 2-β := by linarith
    have hspos : (0:ℝ) < s := by linarith
    have hsqrt : (2-β) ≤ Real.sqrt ((2-β)^2+s^2) := by
      apply Real.le_sqrt_of_sq_le
      nlinarith [sq_nonneg s]
    rw [div_le_div_iff₀ (by positivity) hspos]
    have hbs : (0:ℝ) ≤ β*s := by positivity
    have hmm := mul_le_mul_of_nonneg_left hsqrt hbs
    nlinarith [hmm]

lemma arctan_sub_eq_arctan_div (a b : ℝ) (h : -1 < a * b) :
    Real.arctan a - Real.arctan b = Real.arctan ((a - b) / (1 + a * b)) := by
  have h' : a * (-b) < 1 := by nlinarith
  have hA := Real.arctan_add (x := a) (y := -b) h'
  rw [Real.arctan_neg] at hA
  rw [sub_eq_add_neg, hA]
  congr 1
  rw [show a + -b = a - b by ring, show 1 - a * (-b) = 1 + a * b by ring]

def bq1 (u : ℝ) : ℝ := 2*u/(1+u)

lemma integral_bhh {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    (∫ s in (1/4:ℝ)..(3/4), bhh β s)
      = Real.arctan (bx1 (1-β)) + Real.arctan (bx2 (1-β)) := by
  have hk1 : (0:ℝ) < 3/2-β := by linarith
  have hk2 : (0:ℝ) < 1+β := by linarith
  have h1 : (∫ s in (1/4:ℝ)..(3/4), (3/2-β)/((3/2-β)^2+s^2))
      = Real.arctan ((3/4)/(3/2-β)) - Real.arctan ((1/4)/(3/2-β)) :=
    Commons.Analysis.Integral.integral_inv_sq_add hk1
  have h2 : (∫ s in (1/4:ℝ)..(3/4), (1+β)/((1+β)^2+s^2))
      = Real.arctan ((3/4)/(1+β)) - Real.arctan ((1/4)/(1+β)) :=
    Commons.Analysis.Integral.integral_inv_sq_add hk2
  have hsplit : (∫ s in (1/4:ℝ)..(3/4), bhh β s)
      = (∫ s in (1/4:ℝ)..(3/4), (3/2-β)/((3/2-β)^2+s^2))
        + (∫ s in (1/4:ℝ)..(3/4), (1+β)/((1+β)^2+s^2)) := by
    unfold bhh
    rw [intervalIntegral.integral_add]
    · apply Continuous.intervalIntegrable
      apply Continuous.div continuous_const
      · fun_prop
      · intro s; have := hk1; positivity
    · apply Continuous.intervalIntegrable
      apply Continuous.div continuous_const
      · fun_prop
      · intro s; have := hk2; positivity
  rw [hsplit, h1, h2]
  have e1 : Real.arctan ((3/4)/(3/2-β)) - Real.arctan ((1/4)/(3/2-β)) = Real.arctan (bx1 (1-β)) := by
    have hlt : -1 < ((3:ℝ)/4)/(3/2-β) * (((1:ℝ)/4)/(3/2-β)) := by
      have hp : (0:ℝ) < ((3:ℝ)/4)/(3/2-β) * (((1:ℝ)/4)/(3/2-β)) := by positivity
      linarith
    rw [arctan_sub_eq_arctan_div _ _ hlt]
    congr 1
    have hD : (0:ℝ) < 3/2-β := by linarith
    have hR : (4 + 8*(1-β))/(7+16*(1-β)+16*(1-β)^2) = 8*(3/2-β)/(16*(3/2-β)^2+3) := by
      rw [show (4 + 8*(1-β)) = 8*(3/2-β) by ring,
          show (7+16*(1-β)+16*(1-β)^2) = 16*(3/2-β)^2+3 by ring]
    rw [bx1, hR]
    set D := (3:ℝ)/2 - β with hDdef
    have key : (((3:ℝ)/4)/D - ((1:ℝ)/4)/D) / (1 + ((3:ℝ)/4)/D * (((1:ℝ)/4)/D)) = 8*D/(16*D^2+3) := by
      rw [show ((3:ℝ)/4)/D - ((1:ℝ)/4)/D = ((1:ℝ)/2)/D by ring]
      rw [show ((3:ℝ)/4)/D * (((1:ℝ)/4)/D) = ((3:ℝ)/16)/(D^2) by rw [div_mul_div_comm]; ring]
      rw [show (((1:ℝ)/2)/D)/(1+((3:ℝ)/16)/(D^2)) = 8*D/(16*D^2+3) by field_simp; ring]
    exact key
  have e2 : Real.arctan ((3/4)/(1+β)) - Real.arctan ((1/4)/(1+β)) = Real.arctan (bx2 (1-β)) := by
    have hlt : -1 < ((3:ℝ)/4)/(1+β) * (((1:ℝ)/4)/(1+β)) := by
      have hp : (0:ℝ) < ((3:ℝ)/4)/(1+β) * (((1:ℝ)/4)/(1+β)) := by positivity
      linarith
    rw [arctan_sub_eq_arctan_div _ _ hlt]
    congr 1
    have hD : (0:ℝ) < 1+β := by linarith
    have hR : (16 - 8*(1-β))/(67-64*(1-β)+16*(1-β)^2) = 8*(1+β)/(16*(1+β)^2+3) := by
      rw [show (16 - 8*(1-β)) = 8*(1+β) by ring,
          show (67-64*(1-β)+16*(1-β)^2) = 16*(1+β)^2+3 by ring]
    rw [bx2, hR]
    set D := 1 + β with hDdef
    have key : (((3:ℝ)/4)/D - ((1:ℝ)/4)/D) / (1 + ((3:ℝ)/4)/D * (((1:ℝ)/4)/D)) = 8*D/(16*D^2+3) := by
      rw [show ((3:ℝ)/4)/D - ((1:ℝ)/4)/D = ((1:ℝ)/2)/D by ring]
      rw [show ((3:ℝ)/4)/D * (((1:ℝ)/4)/D) = ((3:ℝ)/16)/(D^2) by rw [div_mul_div_comm]; ring]
      rw [show (((1:ℝ)/2)/D)/(1+((3:ℝ)/16)/(D^2)) = 8*D/(16*D^2+3) by field_simp; ring]
    exact key
  rw [e1, e2]

lemma integral_q1 {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    (∫ s in (1/4:ℝ)..(3/4), ((2-β)^2-β^2)/(2*((2-β)^2+s^2)))
      = bq1 (1-β) * Real.arctan (bxq (1-β)) := by
  have hb : (0:ℝ) < 2-β := by linarith
  have hc : (2-β)^2-β^2 = 4*(1-β) := by ring
  have h1 : (∫ s in (1/4:ℝ)..(3/4), (2-β)/((2-β)^2+s^2))
      = Real.arctan ((3/4)/(2-β)) - Real.arctan ((1/4)/(2-β)) :=
    Commons.Analysis.Integral.integral_inv_sq_add hb
  have hmul : (∫ s in (1/4:ℝ)..(3/4), ((2-β)^2-β^2)/(2*((2-β)^2+s^2)))
      = ((2-β)^2-β^2)/(2*(2-β)) * (∫ s in (1/4:ℝ)..(3/4), (2-β)/((2-β)^2+s^2)) := by
    have hfun : (fun s : ℝ => ((2-β)^2-β^2)/(2*((2-β)^2+s^2)))
        = (fun s : ℝ => (((2-β)^2-β^2)/(2*(2-β))) * ((2-β)/((2-β)^2+s^2))) := by
      ext s; field_simp
    rw [hfun, intervalIntegral.integral_const_mul]
  rw [hmul, h1, hc]
  have e1 : Real.arctan ((3/4)/(2-β)) - Real.arctan ((1/4)/(2-β)) = Real.arctan (bxq (1-β)) := by
    have hlt : -1 < ((3:ℝ)/4)/(2-β) * (((1:ℝ)/4)/(2-β)) := by
      have hp : (0:ℝ) < ((3:ℝ)/4)/(2-β) * (((1:ℝ)/4)/(2-β)) := by positivity
      linarith
    rw [arctan_sub_eq_arctan_div _ _ hlt]
    congr 1
    have hD : (0:ℝ) < 2-β := by linarith
    have hR : (8 + 8*(1-β))/(19+32*(1-β)+16*(1-β)^2) = 8*(2-β)/(16*(2-β)^2+3) := by
      rw [show (8 + 8*(1-β)) = 8*(2-β) by ring,
          show (19+32*(1-β)+16*(1-β)^2) = 16*(2-β)^2+3 by ring]
    rw [bxq, hR]
    set D := 2 - β with hDdef
    have key : (((3:ℝ)/4)/D - ((1:ℝ)/4)/D) / (1 + ((3:ℝ)/4)/D * (((1:ℝ)/4)/D)) = 8*D/(16*D^2+3) := by
      rw [show ((3:ℝ)/4)/D - ((1:ℝ)/4)/D = ((1:ℝ)/2)/D by ring]
      rw [show ((3:ℝ)/4)/D * (((1:ℝ)/4)/D) = ((3:ℝ)/16)/(D^2) by rw [div_mul_div_comm]; ring]
      rw [show (((1:ℝ)/2)/D)/(1+((3:ℝ)/16)/(D^2)) = 8*D/(16*D^2+3) by field_simp; ring]
    exact key
  rw [e1]
  unfold bq1
  have h2b : (2:ℝ)-β ≠ 0 := by linarith
  have h1b : (1:ℝ)+(1-β) ≠ 0 := by linarith
  field_simp
  ring

/-! ## The remaining bounding functions and their monotonicity -/

/-- Rational lower bound for `∫ (c²/(8Δ²) + c³/(16Δ³))` where `c = 4u`, `Δ ≤ (1+u)²+9/16`. -/
def bRq (u : ℝ) : ℝ := u^2/((1+u)^2+9/16)^2 + 2*u^3/((1+u)^2+9/16)^3

lemma bRq_eq (u : ℝ) :
    bRq u = (u/((1+u)^2+9/16))^2 + 2*(u/((1+u)^2+9/16))^3 := by
  unfold bRq
  rw [div_pow, div_pow, mul_div_assoc]

lemma bRq1_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1) :
    x/((1+x)^2+9/16) ≤ y/((1+y)^2+9/16) := by
  have hx' : (0:ℝ) < (1+x)^2+9/16 := by positivity
  have hy' : (0:ℝ) < (1+y)^2+9/16 := by positivity
  rw [div_le_div_iff₀ hx' hy']
  have key : y*((1+x)^2+9/16) - x*((1+y)^2+9/16) = (y-x)*(25/16 - x*y) := by ring
  have h1 : 0 ≤ x*(1-y) := mul_nonneg hx (by linarith)
  have h2 : 0 ≤ x*(y-x) := mul_nonneg hx (by linarith)
  nlinarith [key, h1, h2, hx, hxy, hy, mul_nonneg (sub_nonneg.mpr hxy) (sub_nonneg.mpr h1)]

lemma bRq_monotone {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1) :
    bRq x ≤ bRq y := by
  have hp := bRq1_mono hx hxy hy
  have hp0 : 0 ≤ x/((1+x)^2+9/16) := div_nonneg hx (by positivity)
  have hq0 : 0 ≤ y/((1+y)^2+9/16) := div_nonneg (le_trans hx hxy) (by positivity)
  rw [bRq_eq, bRq_eq]
  have h2 : (x/((1+x)^2+9/16))^2 ≤ (y/((1+y)^2+9/16))^2 := by
    apply sq_le_sq' (by linarith) hp
  have h3 : (x/((1+x)^2+9/16))^3 ≤ (y/((1+y)^2+9/16))^3 :=
    pow_le_pow_left₀ (by linarith) hp 3
  linarith

/-- Coefficient of the logarithmic term in the `t₃`-integral. -/
def bA1 (u : ℝ) : ℝ := 1/2 - (13/96)/(4*(1+u)^2)
/-- Coefficient of the logarithmic term in the `t₄`-integral (region I). -/
def bA2 (u : ℝ) : ℝ := 1/2 - (13/96)/(4*(1+u^2))

/-- `∫_{1/4}^{3/4} log s ds`. -/
def dJlog : ℝ := (3/4)*Real.log 3 - Real.log 2 - 1/2
/-- `∫_{1/4}^{3/4} s^2 log s ds`. -/
def dJlog2 : ℝ := (9/64)*Real.log 3 - (13/48)*Real.log 2 - 13/288

lemma bA1_monotone {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : bA1 x ≤ bA1 y := by
  unfold bA1
  have hx1 : (0:ℝ) < 1+x := by linarith
  have hy1 : (0:ℝ) < 1+y := by linarith
  have h1 : ((13:ℝ)/96)/(4*(1+y)^2) ≤ (13/96)/(4*(1+x)^2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  linarith

lemma bA1_nonneg {u : ℝ} (hu : 0 ≤ u) : 0 ≤ bA1 u := by
  unfold bA1
  have hu1 : (0:ℝ) < 1+u := by linarith
  have h : ((13:ℝ)/96)/(4*(1+u)^2) ≤ 13/384 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  linarith

lemma bA2_monotone {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : bA2 x ≤ bA2 y := by
  unfold bA2
  have h1 : ((13:ℝ)/96)/(4*(1+y^2)) ≤ (13/96)/(4*(1+x^2)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  linarith

lemma bA2_nonneg (u : ℝ) : 0 ≤ bA2 u := by
  unfold bA2
  have h : ((13:ℝ)/96)/(4*(1+u^2)) ≤ 13/384 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  linarith

lemma bL1_hasDerivAt (t : ℝ) : HasDerivAt bL1 (1 - t + t^2 - t^3 + t^4) t := by
  change HasDerivAt (fun u : ℝ => u - u^2/2 + u^3/3 - u^4/4 + u^5/5)
    (1 - t + t^2 - t^3 + t^4) t
  have h1 : HasDerivAt (fun u : ℝ => u) 1 t := hasDerivAt_id' t
  have h2 : HasDerivAt (fun u : ℝ => u^2/2) t t := by
    convert! (hasDerivAt_pow 2 t).div_const (2:ℝ) using 1
    norm_num [pow_one]
  have h3 : HasDerivAt (fun u : ℝ => u^3/3) (t^2) t := by
    convert! (hasDerivAt_pow 3 t).div_const (3:ℝ) using 1; norm_num
  have h4 : HasDerivAt (fun u : ℝ => u^4/4) (t^3) t := by
    convert! (hasDerivAt_pow 4 t).div_const (4:ℝ) using 1; norm_num
  have h5 : HasDerivAt (fun u : ℝ => u^5/5) (t^4) t := by
    convert! (hasDerivAt_pow 5 t).div_const (5:ℝ) using 1; norm_num
  exact ((((h1.sub h2).add h3).sub h4).add h5)

lemma bL1_monotone_global : Monotone bL1 := by
  apply monotone_of_deriv_nonneg
  · unfold bL1; fun_prop
  · intro x
    rw [(bL1_hasDerivAt x).deriv]
    nlinarith [sq_nonneg (x^2 - x/2), sq_nonneg (x - 2/3)]

lemma bL1_monotone {x y : ℝ} (hxy : x ≤ y) : bL1 x ≤ bL1 y := bL1_monotone_global hxy

lemma bL2_antitone {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : bL2 y ≤ bL2 x := by
  unfold bL2
  have h2 := pow_le_pow_left₀ hx hxy 2
  have h3 := pow_le_pow_left₀ hx hxy 3
  have h4 := pow_le_pow_left₀ hx hxy 4
  have h5 := pow_le_pow_left₀ hx hxy 5
  have h6 := pow_le_pow_left₀ hx hxy 6
  linarith

lemma blog1m_antitone {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : blog1m y ≤ blog1m x := by
  unfold blog1m
  have h2 := pow_le_pow_left₀ hx hxy 2
  have h3 := pow_le_pow_left₀ hx hxy 3
  have h4 := pow_le_pow_left₀ hx hxy 4
  have h5 := pow_le_pow_left₀ hx hxy 5
  have h6 := pow_le_pow_left₀ hx hxy 6
  have h7 := pow_le_pow_left₀ hx hxy 7
  have h8 := pow_le_pow_left₀ hx hxy 8
  have h9 := pow_le_pow_left₀ hx hxy 9
  have h10 := pow_le_pow_left₀ hx hxy 10
  have h11 := pow_le_pow_left₀ hx hxy 11
  have h12 := pow_le_pow_left₀ hx hxy 12
  have h13 := pow_le_pow_left₀ hx hxy 13
  linarith

lemma bq1_monotone {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : bq1 x ≤ bq1 y := by
  unfold bq1
  have hx1 : (0:ℝ) < 1+x := by linarith
  have hy1 : (0:ℝ) < 1+y := by linarith
  rw [div_le_div_iff₀ hx1 hy1]; nlinarith

lemma bq1_nonneg {u : ℝ} (hu : 0 ≤ u) : 0 ≤ bq1 u := by
  unfold bq1; positivity

/-- `boxT8` is nonnegative on `[0,1]`. -/
lemma boxT8_nonneg {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) : 0 ≤ boxT8 z := by
  have hfac : boxT8 z = z*(1 - z^2/3 + z^4/5 - z^6/7 + z^8/9 - z^10/11 + z^12/13 - z^14/15) := by
    unfold boxT8; ring
  rw [hfac]
  have h2 : z^2 ≤ 1 := pow_le_one₀ hz0 hz1
  have h6 : z^6 ≤ 1 := pow_le_one₀ hz0 hz1
  have h10 : z^10 ≤ 1 := pow_le_one₀ hz0 hz1
  have h14 : z^14 ≤ 1 := pow_le_one₀ hz0 hz1
  have h4 : 0 ≤ z^4 := by positivity
  have h8 : 0 ≤ z^8 := by positivity
  have h12 : 0 ≤ z^12 := by positivity
  have hbr : 0 ≤ 1 - z^2/3 + z^4/5 - z^6/7 + z^8/9 - z^10/11 + z^12/13 - z^14/15 := by
    nlinarith
  exact mul_nonneg hz0 hbr



/-! ## Integrals of `log` and `s ↦ s² log s` over `[1/4,3/4]` -/

lemma integral_log_id : (∫ s in (1/4:ℝ)..(3/4), Real.log s) = dJlog := by
  rw [integral_log_range (by norm_num) (by norm_num)]
  have h3 : Real.log ((3:ℝ)/4) = Real.log 3 - 2*Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), show (4:ℝ) = 2^2 by norm_num,
      Real.log_pow]
    norm_num
  have h1 : Real.log ((1:ℝ)/4) = -2*Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one,
      show (4:ℝ) = 2^2 by norm_num, Real.log_pow]
    ring
  unfold dJlog
  rw [h3, h1]
  ring

lemma integral_sq_log_id : (∫ s in (1/4:ℝ)..(3/4), s^2 * Real.log s) = dJlog2 := by
  have h34 : (1/4:ℝ) ≤ 3/4 := by norm_num
  have hderiv : ∀ x ∈ Set.uIcc (1/4:ℝ) (3/4),
      HasDerivAt (fun s : ℝ => (s^3/3) * Real.log s - s^3/9) (x^2 * Real.log x) x := by
    intro x hx
    rw [Set.uIcc_of_le h34] at hx
    have hx0 : x ≠ 0 := by
      have : (0:ℝ) < x := by linarith [hx.1]
      positivity
    have h1 : HasDerivAt (fun s : ℝ => s^3/3) (x^2) x := by
      have h := (hasDerivAt_pow 3 x).div_const (3:ℝ)
      norm_num at h
      exact h
    have h2 : HasDerivAt (fun s : ℝ => Real.log s) (x⁻¹) x := Real.hasDerivAt_log hx0
    have h3 := h1.mul h2
    have h4 : HasDerivAt (fun s : ℝ => s^3/9) (x^2/3) x := by
      have h := (hasDerivAt_pow 3 x).div_const (9:ℝ)
      norm_num at h
      rw [show (3:ℝ)*x^2/9 = x^2/3 by ring] at h
      exact h
    have h5 := h3.sub h4
    have hval : (x^2) * Real.log x + x^3/3 * x⁻¹ - x^2/3 = x^2 * Real.log x := by
      field_simp
      ring
    rwa [hval] at h5
  have hint : IntervalIntegrable (fun s : ℝ => s^2 * Real.log s) volume (1/4:ℝ) (3/4) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le h34]
    apply ContinuousOn.mul
    · fun_prop
    · apply ContinuousOn.log (by fun_prop)
      intro x hx
      exact ne_of_gt (by linarith [hx.1] : (0:ℝ) < x)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [h]
  have h3 : Real.log ((3:ℝ)/4) = Real.log 3 - 2*Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), show (4:ℝ) = 2^2 by norm_num,
      Real.log_pow]
    norm_num
  have h1 : Real.log ((1:ℝ)/4) = -2*Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one,
      show (4:ℝ) = 2^2 by norm_num, Real.log_pow]
    ring
  unfold dJlog2
  rw [h3, h1]
  ring

/-! ## The `u`-dependent upper bounds for the two subtracted integrals -/

/-- Upper bound for `∫ bT3ub`, valid for all `β ∈ (0,1)`. -/
def U3u (β : ℝ) : ℝ :=
  bR3s (1 - β) + (Real.log 2 + Real.log (2 - β)) * bA1 (1 - β) - dJlog
    + dJlog2/(4*(2 - β)^2)

/-- Value of `∫ bT4ub` in region I (`3/4 ≤ β`). -/
def U4Iu (β : ℝ) : ℝ :=
  bR4s (1 - β) + Real.log (2*β) * bA2 (1 - β) - dJlog + dJlog2/(4*(1 + (1 - β)^2))

/-- Upper bound for `∫ bT4ub` in region II (`1/4 ≤ β ≤ 3/4`). -/
def U4IIu (β : ℝ) : ℝ :=
  beJ2 (1 - β) + β*Real.log 3 - (β + 3/4)*Real.log 2 - (β + 1/4)*Real.log β + β - 1/4

/-- Value of `∫ bT4ub` in region III (`β ≤ 1/4`). -/
def U4IIIu (β : ℝ) : ℝ := β*Real.log 3

lemma continuousOn_log_uIcc :
    ContinuousOn (fun s : ℝ => Real.log s) (Set.uIcc (1/4:ℝ) (3/4)) := by
  rw [Set.uIcc_of_le (by norm_num : (1/4:ℝ) ≤ 3/4)]
  apply ContinuousOn.log continuousOn_id
  intro x hx
  exact ne_of_gt (by linarith [hx.1] : (0:ℝ) < x)

lemma continuousOn_log_sub (b : ℝ) :
    ContinuousOn (fun s : ℝ => Real.log b - Real.log s) (Set.uIcc (1/4:ℝ) (3/4)) :=
  ContinuousOn.sub continuousOn_const continuousOn_log_uIcc

lemma continuousOn_one_sub_c_sq_mul_log (c : ℝ) :
    ContinuousOn (fun s : ℝ => (1 - c*s^2) * Real.log s) (Set.uIcc (1/4:ℝ) (3/4)) := by
  have h := continuousOn_log_uIcc
  fun_prop

lemma continuousOn_one_sub_c_sq_mul (c b : ℝ) :
    ContinuousOn (fun s : ℝ => (1 - c*s^2) * (Real.log b - Real.log s))
      (Set.uIcc (1/4:ℝ) (3/4)) := by
  have h := continuousOn_log_sub b
  fun_prop

lemma continuousOn_bT3ub (β : ℝ) :
    ContinuousOn (bT3ub β) (Set.uIcc (1/4:ℝ) (3/4)) := by
  have h := continuousOn_log_sub (2*(2-β))
  unfold bT3ub
  fun_prop

lemma intervalIntegrable_log_uIcc :
    IntervalIntegrable (fun s : ℝ => Real.log s) volume (1/4:ℝ) (3/4) :=
  continuousOn_log_uIcc.intervalIntegrable

lemma intervalIntegrable_sq_log_uIcc :
    IntervalIntegrable (fun s : ℝ => s^2 * Real.log s) volume (1/4:ℝ) (3/4) := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le (by norm_num : (1/4:ℝ) ≤ 3/4)]
  apply ContinuousOn.mul
  · fun_prop
  · apply ContinuousOn.log continuousOn_id
    intro x hx
    exact ne_of_gt (by linarith [hx.1] : (0:ℝ) < x)

lemma integral_poly3 (c : ℝ) :
    (∫ s in (1/4:ℝ)..(3/4), (c*s^2 - (3/2)*c^2*s^4 + (5/6)*c^3*s^6))
      = c*(13/96) - (3/2)*c^2*(121/2560) + (5/6)*c^3*(1093/57344) := by
  rw [intervalIntegral.integral_add, intervalIntegral.integral_sub,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, integral_pow, integral_pow, integral_pow]
  · norm_num
  all_goals apply Continuous.intervalIntegrable; fun_prop

lemma integral_one_sub_c_sq (c : ℝ) :
    (∫ s in (1/4:ℝ)..(3/4), (1 - c*s^2)) = 1/2 - c*(13/96) := by
  rw [intervalIntegral.integral_sub, intervalIntegral.integral_const,
      intervalIntegral.integral_const_mul, integral_pow]
  · norm_num
  all_goals apply Continuous.intervalIntegrable; fun_prop

lemma integral_one_sub_c_sq_log (c : ℝ) :
    (∫ s in (1/4:ℝ)..(3/4), (1 - c*s^2) * Real.log s) = dJlog - c*dJlog2 := by
  rw [show (fun s : ℝ => (1 - c*s^2)*Real.log s)
        = (fun s : ℝ => Real.log s - c*(s^2*Real.log s)) by funext s; ring]
  rw [intervalIntegral.integral_sub, intervalIntegral.integral_const_mul,
      integral_log_id, integral_sq_log_id]
  · exact intervalIntegrable_log_uIcc
  · exact intervalIntegrable_sq_log_uIcc.const_mul c

lemma integral_log_part (c b : ℝ) :
    (∫ s in (1/4:ℝ)..(3/4), (1 - c*s^2)*(Real.log b - Real.log s))
      = Real.log b * (1/2 - c*(13/96)) - (dJlog - c*dJlog2) := by
  rw [show (fun s : ℝ => (1 - c*s^2)*(Real.log b - Real.log s))
        = (fun s : ℝ => Real.log b * (1 - c*s^2) - (1 - c*s^2)*Real.log s) by
      funext s; ring]
  rw [intervalIntegral.integral_sub, intervalIntegral.integral_const_mul,
      integral_one_sub_c_sq, integral_one_sub_c_sq_log]
  · apply Continuous.intervalIntegrable; fun_prop
  · exact (continuousOn_one_sub_c_sq_mul_log c).intervalIntegrable

/-- The pointwise majorant `bT3ub` is bounded by the polynomial/log pieces we integrate. -/
lemma bT3ub_le_pieces {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (c : ℝ)
    (hc : c = 1/(4*(2-β)^2)) (s : ℝ) :
    bT3ub β s ≤ (c*s^2 - (3/2)*c^2*s^4 + (5/6)*c^3*s^6)
      + (1 - c*s^2)*(Real.log (2*(2-β)) - Real.log s) := by
  have hv : s^2/(4*(2-β)^2) = c*s^2 := by rw [hc]; ring
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  have hcs : 0 ≤ c*s^2 := mul_nonneg hc0 (sq_nonneg s)
  have hkey : ∀ w : ℝ, 0 ≤ w → (1 - w)*(w - w^2/2 + w^3/3)
      ≤ w - (3/2)*w^2 + (5/6)*w^3 := by
    intro w hw
    nlinarith [pow_nonneg hw 4]
  have h2 := hkey (c*s^2) hcs
  simp only [bT3ub, hv]
  linarith [h2]

lemma integral_bT3ub_le {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    (∫ s in (1/4:ℝ)..(3/4), bT3ub β s) ≤ U3u β := by
  have hb : (0:ℝ) < 2-β := by linarith
  set c : ℝ := 1/(4*(2-β)^2) with hc
  have hcont2 : ContinuousOn
      (fun s : ℝ => (c*s^2 - (3/2)*c^2*s^4 + (5/6)*c^3*s^6)
        + (1 - c*s^2)*(Real.log (2*(2-β)) - Real.log s)) (Set.uIcc (1/4:ℝ) (3/4)) := by
    have h := continuousOn_one_sub_c_sq_mul c (2*(2-β))
    fun_prop
  have hmono : (∫ s in (1/4:ℝ)..(3/4), bT3ub β s) ≤
      (∫ s in (1/4:ℝ)..(3/4), (c*s^2 - (3/2)*c^2*s^4 + (5/6)*c^3*s^6)
        + (1 - c*s^2)*(Real.log (2*(2-β)) - Real.log s)) := by
    apply intervalIntegral.integral_mono_on (by norm_num)
    · exact (continuousOn_bT3ub β).intervalIntegrable
    · exact hcont2.intervalIntegrable
    · intro x hx
      exact bT3ub_le_pieces hβ0 hβ1 c hc x
  have hIa : IntervalIntegrable (fun s : ℝ => c*s^2 - (3/2)*c^2*s^4 + (5/6)*c^3*s^6)
      volume (1/4:ℝ) (3/4) := by
    apply Continuous.intervalIntegrable; fun_prop
  have hIb : IntervalIntegrable
      (fun s : ℝ => (1 - c*s^2)*(Real.log (2*(2-β)) - Real.log s)) volume (1/4:ℝ) (3/4) :=
    (continuousOn_one_sub_c_sq_mul c (2*(2-β))).intervalIntegrable
  have hsplit : (∫ s in (1/4:ℝ)..(3/4), (c*s^2 - (3/2)*c^2*s^4 + (5/6)*c^3*s^6)
        + (1 - c*s^2)*(Real.log (2*(2-β)) - Real.log s))
      = (∫ s in (1/4:ℝ)..(3/4), (c*s^2 - (3/2)*c^2*s^4 + (5/6)*c^3*s^6))
        + (∫ s in (1/4:ℝ)..(3/4), (1 - c*s^2)*(Real.log (2*(2-β)) - Real.log s)) :=
    intervalIntegral.integral_add hIa hIb
  rw [hsplit, integral_poly3, integral_log_part] at hmono
  have heq : c*(13/96) - (3/2)*c^2*(121/2560) + (5/6)*c^3*(1093/57344)
      + (Real.log (2*(2-β))*(1/2 - c*(13/96)) - (dJlog - c*dJlog2)) = U3u β := by
    have hlogmul : Real.log (2*(2-β)) = Real.log 2 + Real.log (2-β) :=
      Real.log_mul (by norm_num) (by linarith : (2:ℝ) - β ≠ 0)
    rw [hlogmul]
    unfold U3u bR3s bA1
    rw [show (1:ℝ) + (1-β) = 2-β by ring, hc]
    ring
  linarith [hmono, le_of_eq heq]



/-! ## The integral of `bT4ub` in the three regions -/

lemma measurable_bT4ub (β : ℝ) : Measurable (bT4ub β) := by
  unfold bT4ub
  refine Measurable.ite measurableSet_Iic ?_ ?_
  · measurability
  · measurability

lemma abs_bT4ub_le {β s : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hs1 : 1/4 ≤ s) (hs2 : s ≤ 3/4) : |bT4ub β s| ≤ 9 := by
  have hs0 : (0:ℝ) < s := by linarith
  have hc2 : cLog2UB ≤ 1 := by unfold cLog2UB; norm_num
  rw [bT4ub]
  by_cases h : s ≤ β
  · rw [if_pos h]
    set S : ℝ := (2-β)^2+β^2 with hS
    have hsS : s^2/(2*S) ≤ 1 := by
      rw [hS, div_le_one (by positivity)]
      nlinarith [sq_nonneg (2-β), sq_nonneg (β - s)]
    have hm0 : 0 ≤ 1 - s^2/(2*S) := by linarith
    have hm1 : 1 - s^2/(2*S) ≤ 1 := by
      have : 0 ≤ s^2/(2*S) := by positivity
      linarith
    have hA0 : 0 ≤ s^2/(4*β^2) := by positivity
    have hA1 : s^2/(4*β^2) ≤ 1/4 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    have hB0 : 0 ≤ Real.log (2*β) - Real.log s := by
      have h1 : Real.log s ≤ Real.log (2*β) := Real.log_le_log hs0 (by linarith)
      linarith
    have hB1 : Real.log (2*β) - Real.log s ≤ 3 := by
      have h1 : Real.log (2*β) ≤ cLog2UB :=
        le_trans (Real.log_le_log (by positivity) (by linarith)) log_two_le_cLog2UB
      have h4 : Real.log ((1:ℝ)/4) = -2*Real.log 2 := by
        rw [Real.log_div (by norm_num) (by norm_num), Real.log_one,
          show (4:ℝ) = 2^2 by norm_num, Real.log_pow]
        ring
      have h5 : Real.log ((1:ℝ)/4) ≤ Real.log s := Real.log_le_log (by norm_num) hs1
      have h7 : Real.log 2 ≤ cLog2UB := log_two_le_cLog2UB
      linarith
    have hfac : (1 - s^2/(2*S))*(s^2/(4*β^2)) + (1 - s^2/(2*S))*(Real.log (2*β) - Real.log s)
        = (1 - s^2/(2*S)) * (s^2/(4*β^2) + (Real.log (2*β) - Real.log s)) := by ring
    rw [hfac, abs_of_nonneg (mul_nonneg hm0 (by linarith))]
    nlinarith [hm0, hm1, hA0, hA1, hB0, hB1]
  · rw [if_neg h]
    have hbs : 0 ≤ β/s := div_nonneg hβ0.le hs0.le
    rw [abs_of_nonneg hbs, div_le_iff₀ hs0]
    linarith

lemma intervalIntegrable_bT4ub_of_bound {β a b : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (h : ∀ x ∈ Set.uIoc a b, |bT4ub β x| ≤ 9) : IntervalIntegrable (bT4ub β) volume a b := by
  refine IntervalIntegrable.mono_fun' (g := fun _ => (9:ℝ)) intervalIntegrable_const ?_ ?_
  · exact (measurable_bT4ub β).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with x hx
    rw [Real.norm_eq_abs]
    exact h x hx

lemma integral_sq_div (c : ℝ) :
    (∫ s in (1/4:ℝ)..(3/4), s^2/c) = (13/96)/c := by
  rw [show (fun s : ℝ => s^2/c) = (fun s : ℝ => c⁻¹ * s^2) by funext s; ring]
  rw [intervalIntegral.integral_const_mul, integral_pow]
  norm_num
  ring

lemma integral_pow4_div (c : ℝ) :
    (∫ s in (1/4:ℝ)..(3/4), s^4/c) = (121/2560)/c := by
  rw [show (fun s : ℝ => s^4/c) = (fun s : ℝ => c⁻¹ * s^4) by funext s; ring]
  rw [intervalIntegral.integral_const_mul, integral_pow]
  norm_num
  ring

lemma continuousOn_log_Icc {β : ℝ} (hβ : 1/4 ≤ β) :
    ContinuousOn (fun s : ℝ => Real.log s) (Set.uIcc (1/4:ℝ) β) := by
  rw [Set.uIcc_of_le hβ]
  apply ContinuousOn.log continuousOn_id
  intro x hx
  exact ne_of_gt (by linarith [hx.1] : (0:ℝ) < x)

lemma continuousOn_log_sub_Icc {β b : ℝ} (hβ : 1/4 ≤ β) :
    ContinuousOn (fun s : ℝ => Real.log b - Real.log s) (Set.uIcc (1/4:ℝ) β) :=
  ContinuousOn.sub continuousOn_const (continuousOn_log_Icc hβ)

lemma integral_sq_quarter {β : ℝ} (hβ : 1/4 ≤ β) :
    (∫ s in (1/4:ℝ)..β, s^2/(4*β^2)) = (β^3 - (1/4:ℝ)^3)/(12*β^2) := by
  rw [show (fun s : ℝ => s^2/(4*β^2)) = (fun s : ℝ => (4*β^2)⁻¹ * s^2) by funext s; ring]
  rw [intervalIntegral.integral_const_mul, integral_pow]
  ring

lemma integral_log_quarter {β : ℝ} (hβ : 1/4 ≤ β) :
    (∫ s in (1/4:ℝ)..β, Real.log (2*β) - Real.log s)
      = (β - 1/4)*Real.log (2*β)
        - (β*Real.log β - β - ((1/4)*Real.log (1/4) - 1/4)) := by
  have h1 : (∫ s in (1/4:ℝ)..β, Real.log (2*β)) = (β - 1/4)*Real.log (2*β) := by
    rw [intervalIntegral.integral_const]
    simp only [smul_eq_mul]
  have h2 : (∫ s in (1/4:ℝ)..β, Real.log s)
      = β*Real.log β - β - ((1/4)*Real.log (1/4) - 1/4) :=
    integral_log_range (by norm_num) hβ
  rw [intervalIntegral.integral_sub
        (f := fun _ : ℝ => Real.log (2*β)) (g := fun s : ℝ => Real.log s)
        (by apply Continuous.intervalIntegrable; fun_prop)
        ((continuousOn_log_Icc hβ).intervalIntegrable), h1, h2]

/-- Region I: for `3/4 ≤ β` the `if` in `bT4ub` always takes the logarithmic branch. -/
lemma integral_bT4ub_I {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hβ : 3/4 ≤ β) :
    (∫ s in (1/4:ℝ)..(3/4), bT4ub β s) = U4Iu β := by
  have h34 : (1/4:ℝ) ≤ 3/4 := by norm_num
  set S : ℝ := (2-β)^2+β^2 with hS
  set c : ℝ := 1/(2*S) with hc
  have hcongr : (∫ s in (1/4:ℝ)..(3/4), bT4ub β s)
      = ∫ s in (1/4:ℝ)..(3/4), ((1 - c*s^2)*(s^2/(4*β^2))
          + (1 - c*s^2)*(Real.log (2*β) - Real.log s)) := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [Set.uIcc_of_le h34] at hs
    rw [bT4ub, if_pos (le_trans hs.2 hβ)]
    have e1 : 1 - s^2/(2*((2-β)^2+β^2)) = 1 - c*s^2 := by rw [hc, hS]; ring
    rw [e1]
  rw [hcongr]
  rw [intervalIntegral.integral_add
      (f := fun s : ℝ => (1 - c*s^2)*(s^2/(4*β^2)))
      (g := fun s : ℝ => (1 - c*s^2)*(Real.log (2*β) - Real.log s))
      (by apply Continuous.intervalIntegrable; fun_prop)
      ((continuousOn_one_sub_c_sq_mul c (2*β)).intervalIntegrable)]
  have hpoly : (∫ s in (1/4:ℝ)..(3/4), (1 - c*s^2)*(s^2/(4*β^2)))
      = (13/96)/(4*β^2) - (121/2560)/(8*β^2*S) := by
    rw [show (fun s : ℝ => (1 - c*s^2)*(s^2/(4*β^2)))
          = (fun s : ℝ => s^2/(4*β^2) - s^4/(8*β^2*S)) by
            funext s; rw [hc]; field_simp; ring]
    rw [intervalIntegral.integral_sub (f := fun s : ℝ => s^2/(4*β^2))
          (g := fun s : ℝ => s^4/(8*β^2*S))
          (by apply Continuous.intervalIntegrable; fun_prop)
          (by apply Continuous.intervalIntegrable; fun_prop),
        integral_sq_div, integral_pow4_div]
  have hlog : (∫ s in (1/4:ℝ)..(3/4), (1 - c*s^2)*(Real.log (2*β) - Real.log s))
      = Real.log (2*β)*(1/2 - c*(13/96)) - (dJlog - c*dJlog2) :=
    integral_log_part c (2*β)
  rw [hpoly, hlog]
  have heq : (13/96)/(4*β^2) - (121/2560)/(8*β^2*S)
      + (Real.log (2*β)*(1/2 - c*(13/96)) - (dJlog - c*dJlog2)) = U4Iu β := by
    have hSe : S = 2*(1+(1-β)^2) := by rw [hS]; ring
    have hb2 : (1:ℝ) - (1-β) = β := by ring
    unfold U4Iu bR4s bA2
    rw [hc, hSe, hb2]
    field_simp
    ring
  rw [heq]

/-- Region III: for `β ≤ 1/4` the `if` in `bT4ub` always takes the `β/s` branch. -/
lemma integral_bT4ub_III {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hβ : β ≤ 1/4) :
    (∫ s in (1/4:ℝ)..(3/4), bT4ub β s) = U4IIIu β := by
  have hcongr : (∫ s in (1/4:ℝ)..(3/4), bT4ub β s)
      = ∫ s in (1/4:ℝ)..(3/4), β/s := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with s hs
    rw [Set.uIoc_of_le (by norm_num : (1/4:ℝ) ≤ 3/4)] at hs
    rw [bT4ub, if_neg]
    intro hle
    linarith [hs.1]
  rw [hcongr]
  have hval : (∫ s in (1/4:ℝ)..(3/4), β/s) = β*(Real.log (3/4) - Real.log (1/4)) := by
    rw [show (fun s : ℝ => β/s) = (fun s : ℝ => β * s⁻¹) by funext s; ring]
    rw [intervalIntegral.integral_const_mul, integral_inv_range (by norm_num) (by norm_num)]
  rw [hval]
  have h3 : Real.log ((3:ℝ)/4) = Real.log 3 - Real.log 4 := Real.log_div (by norm_num) (by norm_num)
  have h1 : Real.log ((1:ℝ)/4) = -Real.log 4 := by
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one]; ring
  unfold U4IIIu
  rw [h3, h1]; ring

/-- Pointwise bound for the logarithmic branch of `bT4ub`. -/
lemma bT4ub_branch_le {β S s : ℝ} (hβ0 : 0 < β) (hS : S = (2-β)^2+β^2) (hs0 : 0 < s)
    (hs : s ≤ β) :
    (1 - s^2/(2*S))*(s^2/(4*β^2)) + (1 - s^2/(2*S))*(Real.log (2*β) - Real.log s)
      ≤ s^2/(4*β^2) + (Real.log (2*β) - Real.log s) := by
  have hSpos : 0 < S := by rw [hS]; nlinarith [sq_nonneg (2-β), sq_nonneg β, hβ0]
  have h2S : (0:ℝ) < 2*S := by linarith
  have hsS : s^2/(2*S) ≤ 1 := by
    rw [div_le_one h2S, hS]
    nlinarith [sq_nonneg (2-β), sq_nonneg (β - s)]
  have hm0 : 0 ≤ 1 - s^2/(2*S) := by linarith
  have hm1 : 1 - s^2/(2*S) ≤ 1 := by
    have : 0 ≤ s^2/(2*S) := by positivity
    linarith
  have hA0 : 0 ≤ s^2/(4*β^2) := by positivity
  have hB0 : 0 ≤ Real.log (2*β) - Real.log s := by
    have h1 : Real.log s ≤ Real.log (2*β) := Real.log_le_log hs0 (by linarith)
    linarith
  have h1 := mul_le_mul_of_nonneg_right hm1 hA0
  have h2 := mul_le_mul_of_nonneg_right hm1 hB0
  linarith

/-- Region II: for `1/4 ≤ β ≤ 3/4` we split at `β` and drop the `(1-m)` factors. -/
lemma integral_bT4ub_II_le {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hβ2 : 1/4 ≤ β) (hβ3 : β ≤ 3/4) :
    (∫ s in (1/4:ℝ)..(3/4), bT4ub β s) ≤ U4IIu β := by
  have h34 : (1/4:ℝ) ≤ 3/4 := by norm_num
  set S : ℝ := (2-β)^2+β^2 with hS
  have hb1 : IntervalIntegrable (bT4ub β) volume (1/4:ℝ) β :=
    intervalIntegrable_bT4ub_of_bound hβ0 hβ1 (fun x hx => by
      rw [Set.uIoc_of_le hβ2] at hx
      exact abs_bT4ub_le hβ0 hβ1 (le_of_lt hx.1) (le_trans hx.2 hβ3))
  have hb2 : IntervalIntegrable (bT4ub β) volume β (3/4:ℝ) :=
    intervalIntegrable_bT4ub_of_bound hβ0 hβ1 (fun x hx => by
      rw [Set.uIoc_of_le hβ3] at hx
      exact abs_bT4ub_le hβ0 hβ1 (le_trans hβ2 (le_of_lt hx.1)) hx.2)
  have hsplit : (∫ s in (1/4:ℝ)..(3/4), bT4ub β s)
      = (∫ s in (1/4:ℝ)..β, bT4ub β s) + (∫ s in β..(3/4), bT4ub β s) :=
    (intervalIntegral.integral_add_adjacent_intervals hb1 hb2).symm
  -- part 1 : bound by the branch, then by the simpler function
  have hI1 : (∫ s in (1/4:ℝ)..β, bT4ub β s)
      ≤ ∫ s in (1/4:ℝ)..β, (s^2/(4*β^2) + (Real.log (2*β) - Real.log s)) := by
    rw [intervalIntegral.integral_congr
      (f := fun s : ℝ => bT4ub β s)
      (g := fun s : ℝ => (1 - s^2/(2*S))*(s^2/(4*β^2))
        + (1 - s^2/(2*S))*(Real.log (2*β) - Real.log s)) (fun s hs => by
          rw [Set.uIcc_of_le hβ2] at hs
          simp only [bT4ub]
          rw [if_pos hs.2, ← hS])]
    apply intervalIntegral.integral_mono_on hβ2
    · apply ContinuousOn.intervalIntegrable
      have h := continuousOn_log_sub_Icc hβ2 (b := 2*β)
      fun_prop
    · apply ContinuousOn.intervalIntegrable
      have h := continuousOn_log_sub_Icc hβ2 (b := 2*β)
      fun_prop
    · intro s hs
      exact bT4ub_branch_le hβ0 hS (by linarith [hs.1]) hs.2
  have hval1 : (∫ s in (1/4:ℝ)..β, (s^2/(4*β^2) + (Real.log (2*β) - Real.log s)))
      = (β^3 - (1/4:ℝ)^3)/(12*β^2)
        + ((β - 1/4)*Real.log (2*β) - (β*Real.log β - β - ((1/4)*Real.log (1/4) - 1/4))) := by
    rw [intervalIntegral.integral_add
          (f := fun s : ℝ => s^2/(4*β^2)) (g := fun s : ℝ => Real.log (2*β) - Real.log s)
          (by apply Continuous.intervalIntegrable; fun_prop)
          ((continuousOn_log_sub_Icc hβ2 (b := 2*β)).intervalIntegrable),
        integral_sq_quarter hβ2, integral_log_quarter hβ2]
  -- part 2 : β/s
  have hI2 : (∫ s in β..(3/4), bT4ub β s) = β*(Real.log (3/4) - Real.log β) := by
    have hcongr2 : (∫ s in β..(3/4), bT4ub β s) = ∫ s in β..(3/4), β/s := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards with s hs
      rw [Set.uIoc_of_le hβ3] at hs
      unfold bT4ub
      rw [if_neg]
      intro hle
      linarith [hs.1]
    rw [hcongr2, show (fun s : ℝ => β/s) = (fun s : ℝ => β * s⁻¹) by funext s; ring,
      intervalIntegral.integral_const_mul, integral_inv_range hβ0 hβ3]
  rw [hsplit]
  have hsum : (∫ s in (1/4:ℝ)..β, bT4ub β s) + (∫ s in β..(3/4), bT4ub β s)
      ≤ ((β^3 - (1/4:ℝ)^3)/(12*β^2)
          + ((β - 1/4)*Real.log (2*β) - (β*Real.log β - β - ((1/4)*Real.log (1/4) - 1/4))))
        + β*(Real.log (3/4) - Real.log β) := by
    have h := add_le_add hI1 (le_of_eq hI2)
    linarith [hval1]
  refine le_trans hsum ?_
  have heq : ((β^3 - (1/4:ℝ)^3)/(12*β^2)
          + ((β - 1/4)*Real.log (2*β) - (β*Real.log β - β - ((1/4)*Real.log (1/4) - 1/4))))
        + β*(Real.log (3/4) - Real.log β) = U4IIu β := by
    have hmul : Real.log (2*β) = Real.log 2 + Real.log β :=
      Real.log_mul (by norm_num) (ne_of_gt hβ0)
    have h4 : Real.log ((1:ℝ)/4) = -2*Real.log 2 := by
      rw [Real.log_div (by norm_num) (by norm_num), Real.log_one,
        show (4:ℝ) = 2^2 by norm_num, Real.log_pow]
      ring
    have h34' : Real.log ((3:ℝ)/4) = Real.log 3 - 2*Real.log 2 := by
      rw [Real.log_div (by norm_num) (by norm_num), show (4:ℝ) = 2^2 by norm_num,
        Real.log_pow]
      norm_num
    have hb2 : (1:ℝ) - (1-β) = β := by ring
    unfold U4IIu beJ2
    rw [hmul, h4, h34', hb2]
    field_simp
    ring
  rw [heq]

/-! ## The rational lower bound for the `q`-terms and the assembly -/

/-- Split an interval integral of a 5-term combination into the sum of the pieces. -/
lemma integral_five {a b : ℝ} {f1 f2 f3 f4 f5 : ℝ → ℝ}
    (h1 : IntervalIntegrable f1 volume a b) (h2 : IntervalIntegrable f2 volume a b)
    (h3 : IntervalIntegrable f3 volume a b) (h4 : IntervalIntegrable f4 volume a b)
    (h5 : IntervalIntegrable f5 volume a b) :
    (∫ x in a..b, (f1 x + f2 x + f3 x - f4 x - f5 x))
      = (∫ x in a..b, f1 x) + (∫ x in a..b, f2 x) + (∫ x in a..b, f3 x)
        - (∫ x in a..b, f4 x) - (∫ x in a..b, f5 x) := by
  have h12 : IntervalIntegrable (fun x => f1 x + f2 x) volume a b := h1.add h2
  have h123 : IntervalIntegrable (fun x => f1 x + f2 x + f3 x) volume a b := h12.add h3
  have h1234 : IntervalIntegrable (fun x => f1 x + f2 x + f3 x - f4 x) volume a b := h123.sub h4
  rw [intervalIntegral.integral_sub (f := fun x => f1 x + f2 x + f3 x - f4 x) (g := f5) h1234 h5,
      intervalIntegral.integral_sub (f := fun x => f1 x + f2 x + f3 x) (g := f4) h123 h4,
      intervalIntegral.integral_add (f := fun x => f1 x + f2 x) (g := f3) h12 h3,
      intervalIntegral.integral_add (f := f1) (g := f2) h1 h2]

lemma continuousOn_q12 (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) :
    ContinuousOn (fun s : ℝ => ((2-β)^2-β^2)/(2*((2-β)^2+s^2))) (Set.uIcc (1/4:ℝ) (3/4)) := by
  apply ContinuousOn.div
  · fun_prop
  · fun_prop
  · intro x hx
    have hk : (0:ℝ) < 2-β := by linarith
    positivity

lemma continuousOn_q23 (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) :
    ContinuousOn (fun s : ℝ => ((2-β)^2-β^2)^2/(8*((2-β)^2+s^2)^2)
      + ((2-β)^2-β^2)^3/(16*((2-β)^2+s^2)^3)) (Set.uIcc (1/4:ℝ) (3/4)) := by
  have hk : (0:ℝ) < 2-β := by linarith
  apply ContinuousOn.add
  · apply ContinuousOn.div
    · fun_prop
    · fun_prop
    · intro x hx; exact ne_of_gt (by positivity)
  · apply ContinuousOn.div
    · fun_prop
    · fun_prop
    · intro x hx; exact ne_of_gt (by positivity)

lemma continuousOn_13h (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) :
    ContinuousOn (fun s : ℝ => (13/5)*((3/2-β)/((3/2-β)^2+s^2)+(1+β)/((1+β)^2+s^2)))
      (Set.uIcc (1/4:ℝ) (3/4)) := by
  have hk : (0:ℝ) < 3/2-β := by linarith
  have hk2 : (0:ℝ) < 1+β := by linarith
  apply ContinuousOn.mul continuousOn_const
  apply ContinuousOn.add
  · apply ContinuousOn.div
    · fun_prop
    · fun_prop
    · intro x hx; exact ne_of_gt (by positivity)
  · apply ContinuousOn.div
    · fun_prop
    · fun_prop
    · intro x hx; exact ne_of_gt (by positivity)

lemma intervalIntegrable_13h (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) :
    IntervalIntegrable (fun s : ℝ => (13/5)*bhh β s) volume (1/4:ℝ) (3/4) := by
  have hk : (0:ℝ) < 3/2-β := by linarith
  have hk2 : (0:ℝ) < 1+β := by linarith
  have hbhh : (fun s : ℝ => (13/5)*bhh β s)
      = fun s : ℝ => (13/5)*((3/2-β)/((3/2-β)^2+s^2)+(1+β)/((1+β)^2+s^2)) := by
    funext s; unfold bhh; ring
  rw [hbhh]
  apply Continuous.intervalIntegrable
  apply Continuous.mul continuous_const
  apply Continuous.add
  · exact Continuous.div continuous_const (by fun_prop) (fun x => ne_of_gt (by positivity))
  · exact Continuous.div continuous_const (by fun_prop) (fun x => ne_of_gt (by positivity))

lemma integral_q23_lower {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    bRq (1-β) ≤ (∫ s in (1/4:ℝ)..(3/4), ((2-β)^2-β^2)^2/(8*((2-β)^2+s^2)^2)
        + ((2-β)^2-β^2)^3/(16*((2-β)^2+s^2)^3)) := by
  set b : ℝ := 2-β with hb
  set c : ℝ := b^2-β^2 with hc
  have hbb : (0:ℝ) < b := by rw [hb]; linarith
  have hc4 : c = 4*(1-β) := by rw [hc, hb]; ring
  have hc0 : 0 ≤ c := by rw [hc4]; linarith
  have hkey : ∀ s ∈ Set.Icc (1/4:ℝ) (3/4),
      c^2/(8*(b^2+9/16)^2) + c^3/(16*(b^2+9/16)^3)
        ≤ c^2/(8*(b^2+s^2)^2) + c^3/(16*(b^2+s^2)^3) := by
    intro s hs
    have hs9 : s^2 ≤ 9/16 := by
      have h : 0 ≤ (3/4 - s)*(3/4 + s) :=
        mul_nonneg (by linarith [hs.2]) (by linarith [hs.1])
      nlinarith [h]
    have hle : b^2+s^2 ≤ b^2+9/16 := by linarith
    have h1' : (1:ℝ)/(b^2+9/16) ≤ 1/(b^2+s^2) :=
      one_div_le_one_div_of_le (by positivity) hle
    have h2 : 1/(b^2+9/16)^2 ≤ 1/(b^2+s^2)^2 := by
      rw [show (1:ℝ)/(b^2+9/16)^2 = (1/(b^2+9/16))^2 by rw [div_pow]; norm_num,
        show (1:ℝ)/(b^2+s^2)^2 = (1/(b^2+s^2))^2 by rw [div_pow]; norm_num]
      exact pow_le_pow_left₀ (by positivity) h1' 2
    have h3 : 1/(b^2+9/16)^3 ≤ 1/(b^2+s^2)^3 := by
      rw [show (1:ℝ)/(b^2+9/16)^3 = (1/(b^2+9/16))^3 by rw [div_pow]; norm_num,
        show (1:ℝ)/(b^2+s^2)^3 = (1/(b^2+s^2))^3 by rw [div_pow]; norm_num]
      exact pow_le_pow_left₀ (by positivity) h1' 3
    have e2 : c^2/(8*(b^2+s^2)^2) = (c^2/8) * (1/(b^2+s^2)^2) := by field_simp
    have e2' : c^2/(8*(b^2+9/16)^2) = (c^2/8) * (1/(b^2+9/16)^2) := by field_simp
    have e3 : c^3/(16*(b^2+s^2)^3) = (c^3/16) * (1/(b^2+s^2)^3) := by field_simp
    have e3' : c^3/(16*(b^2+9/16)^3) = (c^3/16) * (1/(b^2+9/16)^3) := by field_simp
    rw [e2, e2', e3, e3']
    have h2' := mul_le_mul_of_nonneg_left h2 (by positivity : (0:ℝ) ≤ c^2/8)
    have h3' := mul_le_mul_of_nonneg_left h3 (by positivity : (0:ℝ) ≤ c^3/16)
    linarith
  have hmono : (∫ s in (1/4:ℝ)..(3/4),
        (fun s => c^2/(8*(b^2+9/16)^2) + c^3/(16*(b^2+9/16)^3)) s)
      ≤ (∫ s in (1/4:ℝ)..(3/4), (fun s => c^2/(8*(b^2+s^2)^2) + c^3/(16*(b^2+s^2)^3)) s) := by
    apply intervalIntegral.integral_mono_on (by norm_num)
    · apply Continuous.intervalIntegrable; fun_prop
    · apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.add
      · apply ContinuousOn.div
        · fun_prop
        · fun_prop
        · intro x hx; positivity
      · apply ContinuousOn.div
        · fun_prop
        · fun_prop
        · intro x hx; positivity
    · intro s hs
      exact hkey s hs
  have hval : (∫ s in (1/4:ℝ)..(3/4),
        (fun s => c^2/(8*(b^2+9/16)^2) + c^3/(16*(b^2+9/16)^3)) s)
      = c^2/(16*(b^2+9/16)^2) + c^3/(32*(b^2+9/16)^3) := by
    rw [intervalIntegral.integral_const]
    norm_num
    field_simp
    ring
  rw [hval] at hmono
  refine le_trans ?_ hmono
  unfold bRq
  rw [hc4, hb]
  field_simp
  linarith

/-- The lower bound integrand for `boxE`. -/
def boxElb (β s : ℝ) : ℝ :=
  (13/5)*bhh β s + ((2-β)^2-β^2)/(2*((2-β)^2+s^2))
    + (((2-β)^2-β^2)^2/(8*((2-β)^2+s^2)^2) + ((2-β)^2-β^2)^3/(16*((2-β)^2+s^2)^3))
    - bT3ub β s - bT4ub β s

lemma boxElb_le_boxE {β s : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hs1 : 1/4 ≤ s) (hs2 : s ≤ 3/4) : boxElb β s ≤ boxE β s := by
  have h3 := bT3_le hβ0 hβ1 hs1 hs2
  have h4 := bT4_le hβ0 hβ1 hs1 hs2
  have hbhh : (13/5)*bhh β s
      = (13/5)*((3/2-β)/((3/2-β)^2+s^2)+(1+β)/((1+β)^2+s^2)) := by
    unfold bhh; ring
  have hbT3 : bT3 β s = Real.log ((4*(2-β)^2+s^2)/(2*(2-β)*s))*(1-s^2/(4*(2-β)^2)) := rfl
  have hbT4 : bT4 β s = (if s ≤ β then Real.log ((4*β^2+s^2)/(2*β*s))*(1-s^2/(2*((2-β)^2+β^2)))
               else (2-β)*β/(s*Real.sqrt ((2-β)^2+s^2))) := rfl
  have hE : boxE β s = (13/5)*((3/2-β)/((3/2-β)^2+s^2)+(1+β)/((1+β)^2+s^2))
      + ((2-β)^2-β^2)/(2*((2-β)^2+s^2)) + ((2-β)^2-β^2)^2/(8*((2-β)^2+s^2)^2)
      + ((2-β)^2-β^2)^3/(16*((2-β)^2+s^2)^3)
      - Real.log ((4*(2-β)^2+s^2)/(2*(2-β)*s))*(1-s^2/(4*(2-β)^2))
      - (if s ≤ β then Real.log ((4*β^2+s^2)/(2*β*s))*(1-s^2/(2*((2-β)^2+β^2)))
               else (2-β)*β/(s*Real.sqrt ((2-β)^2+s^2))) := rfl
  have hLl : boxElb β s = (13/5)*bhh β s + ((2-β)^2-β^2)/(2*((2-β)^2+s^2))
      + (((2-β)^2-β^2)^2/(8*((2-β)^2+s^2)^2) + ((2-β)^2-β^2)^3/(16*((2-β)^2+s^2)^3))
      - bT3ub β s - bT4ub β s := rfl
  rw [hLl, hE, ← hbhh, ← hbT3, ← hbT4]
  linarith

lemma continuousOn_bT3 (β : ℝ) (hβ2 : β < 2) :
    ContinuousOn (bT3 β) (Set.uIcc (1/4:ℝ) (3/4)) := by
  have h34 : (1/4:ℝ) ≤ 3/4 := by norm_num
  have hb0 : (0:ℝ) < 2-β := by linarith
  unfold bT3
  apply ContinuousOn.mul
  · apply ContinuousOn.log
    · apply ContinuousOn.div
      · fun_prop
      · fun_prop
      · intro x hx
        rw [Set.uIcc_of_le h34] at hx
        have hx0 : (0:ℝ) < x := by linarith [hx.1]
        exact ne_of_gt (by positivity)
    · intro x hx
      rw [Set.uIcc_of_le h34] at hx
      have hx0 : (0:ℝ) < x := by linarith [hx.1]
      have hden : (0:ℝ) < 2*(2-β)*x := by positivity
      have hnum : (0:ℝ) < 4*(2-β)^2+x^2 := by positivity
      exact ne_of_gt (div_pos hnum hden)
  · fun_prop

lemma measurable_bT4 (β : ℝ) : Measurable (bT4 β) := by
  unfold bT4
  refine Measurable.ite measurableSet_Iic ?_ ?_
  · measurability
  · measurability

lemma abs_bT4_le {β s : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hs1 : 1/4 ≤ s) (hs2 : s ≤ 3/4) : |bT4 β s| ≤ 9 := by
  have hs0 : (0:ℝ) < s := by linarith
  rw [bT4]
  by_cases h : s ≤ β
  · rw [if_pos h]
    set S : ℝ := (2-β)^2+β^2 with hS
    have hSpos : 0 < S := by rw [hS]; nlinarith [sq_nonneg (2-β), sq_nonneg β, hβ0]
    have hsS : s^2/(2*S) ≤ 1 := by
      rw [div_le_one (by positivity)]
      rw [hS]
      nlinarith [sq_nonneg (2-β), sq_nonneg (β - s), hβ0]
    have hfac0 : 0 ≤ 1 - s^2/(2*S) := by linarith
    have hfac1 : 1 - s^2/(2*S) ≤ 1 := by
      have : 0 ≤ s^2/(2*S) := by positivity
      linarith
    have hratio : (4*β^2+s^2)/(2*β*s) = 2*β/s + s/(2*β) := by field_simp; ring
    have hlogeq : Real.log ((4*β^2+s^2)/(2*β*s)) = Real.log (2*β/s + s/(2*β)) := by rw [hratio]
    rw [hlogeq]
    have hlo : (1:ℝ) ≤ 2*β/s + s/(2*β) := by
      have h1 : (1:ℝ) ≤ 2*β/s := by
        rw [le_div_iff₀ hs0]; linarith
      have h2 : 0 ≤ s/(2*β) := by positivity
      linarith
    have hhi : 2*β/s + s/(2*β) ≤ 9 := by
      have hb1 : 2*β/s ≤ 8 := by
        rw [div_le_iff₀ hs0]; linarith
      have hb2 : s/(2*β) ≤ 1 := by
        rw [div_le_iff₀ (by positivity)]; linarith
      linarith
    have hlog0 : 0 ≤ Real.log (2*β/s + s/(2*β)) := by
      apply Real.log_nonneg; linarith
    have hlog9 : Real.log (2*β/s + s/(2*β)) ≤ 3 := by
      have h1 : Real.log (2*β/s + s/(2*β)) ≤ Real.log 9 :=
        Real.log_le_log (by positivity) hhi
      have h2 : Real.log (9:ℝ) ≤ 3 := by
        rw [show (9:ℝ) = 3^2 by norm_num, Real.log_pow]
        have h3 := log_three_le_cLog3UB
        have h4 : 2*cLog3UB ≤ 3 := by unfold cLog3UB; norm_num
        push_cast
        linarith
      linarith
    rw [abs_mul, abs_of_nonneg hlog0, abs_of_nonneg hfac0]
    nlinarith [hlog9, hfac1, hfac0]
  · rw [if_neg h]
    have hβ34 : β < 3/4 := by have h' : β < s := not_le.mp h; linarith
    have hb0 : (0:ℝ) < 2-β := by linarith
    have hsq : (2-β) ≤ Real.sqrt ((2-β)^2+s^2) := by
      apply Real.le_sqrt_of_sq_le; nlinarith [sq_nonneg s]
    have hden : s*(2-β) ≤ s*Real.sqrt ((2-β)^2+s^2) :=
      mul_le_mul_of_nonneg_left hsq (by linarith)
    have hnum : 0 ≤ (2-β)*β := mul_nonneg (le_of_lt hb0) (le_of_lt hβ0)
    have hcp : (0:ℝ) < s*(2-β) := mul_pos hs0 hb0
    have h1 : (2-β)*β/(s*Real.sqrt ((2-β)^2+s^2)) ≤ (2-β)*β/(s*(2-β)) :=
      div_le_div_of_nonneg_left hnum hcp hden
    have h2 : (2-β)*β/(s*(2-β)) = β/s := by field_simp
    have h3 : β/s ≤ 4 := by
      rw [div_le_iff₀ hs0]
      linarith
    have hpos : 0 ≤ (2-β)*β/(s*Real.sqrt ((2-β)^2+s^2)) := by positivity
    rw [abs_of_nonneg hpos]
    linarith

lemma intervalIntegrable_bT4 {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    IntervalIntegrable (bT4 β) volume (1/4:ℝ) (3/4) := by
  refine IntervalIntegrable.mono_fun' (g := fun _ => (9:ℝ)) intervalIntegrable_const ?_ ?_
  · exact (measurable_bT4 β).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with x hx
    rw [Real.norm_eq_abs]
    rw [Set.uIoc_of_le (by norm_num : (1/4:ℝ) ≤ 3/4)] at hx
    exact abs_bT4_le hβ0 hβ1 (le_of_lt hx.1) hx.2

lemma intervalIntegrable_boxE {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    IntervalIntegrable (boxE β) volume (1/4:ℝ) (3/4) := by
  have h1 : IntervalIntegrable
      (fun s : ℝ => (13/5)*((3/2-β)/((3/2-β)^2+s^2)+(1+β)/((1+β)^2+s^2)))
      volume (1/4:ℝ) (3/4) :=
    (continuousOn_13h β hβ0 hβ1).intervalIntegrable
  have h2 : IntervalIntegrable (fun s : ℝ => ((2-β)^2-β^2)/(2*((2-β)^2+s^2)))
      volume (1/4:ℝ) (3/4) :=
    (continuousOn_q12 β hβ0 hβ1).intervalIntegrable
  have h3 : IntervalIntegrable (fun s : ℝ => ((2-β)^2-β^2)^2/(8*((2-β)^2+s^2)^2)
      + ((2-β)^2-β^2)^3/(16*((2-β)^2+s^2)^3)) volume (1/4:ℝ) (3/4) :=
    (continuousOn_q23 β hβ0 hβ1).intervalIntegrable
  have h4 : IntervalIntegrable (bT3 β) volume (1/4:ℝ) (3/4) :=
    (continuousOn_bT3 β (by linarith)).intervalIntegrable
  have h5 : IntervalIntegrable (bT4 β) volume (1/4:ℝ) (3/4) := intervalIntegrable_bT4 hβ0 hβ1
  rw [show boxE β = fun s => (13/5)*((3/2-β)/((3/2-β)^2+s^2)+(1+β)/((1+β)^2+s^2))
      + ((2-β)^2-β^2)/(2*((2-β)^2+s^2))
      + (((2-β)^2-β^2)^2/(8*((2-β)^2+s^2)^2) + ((2-β)^2-β^2)^3/(16*((2-β)^2+s^2)^3))
      - bT3 β s - bT4 β s from by
    funext s; unfold boxE bT3 bT4; ring]
  exact (((h1.add h2).add h3).sub h4).sub h5

lemma intervalIntegrable_boxElb {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    IntervalIntegrable (boxElb β) volume (1/4:ℝ) (3/4) := by
  have h1 : IntervalIntegrable (fun s : ℝ => (13/5)*bhh β s) volume (1/4:ℝ) (3/4) :=
    intervalIntegrable_13h β hβ0 hβ1
  have h2 : IntervalIntegrable (fun s : ℝ => ((2-β)^2-β^2)/(2*((2-β)^2+s^2)))
      volume (1/4:ℝ) (3/4) :=
    (continuousOn_q12 β hβ0 hβ1).intervalIntegrable
  have h3 : IntervalIntegrable (fun s : ℝ => ((2-β)^2-β^2)^2/(8*((2-β)^2+s^2)^2)
      + ((2-β)^2-β^2)^3/(16*((2-β)^2+s^2)^3)) volume (1/4:ℝ) (3/4) :=
    (continuousOn_q23 β hβ0 hβ1).intervalIntegrable
  have h4 : IntervalIntegrable (bT3ub β) volume (1/4:ℝ) (3/4) :=
    (continuousOn_bT3ub β).intervalIntegrable
  have h5 : IntervalIntegrable (bT4ub β) volume (1/4:ℝ) (3/4) :=
    intervalIntegrable_bT4ub_of_bound hβ0 hβ1 (fun x hx => by
      rw [Set.uIoc_of_le (by norm_num : (1/4:ℝ) ≤ 3/4)] at hx
      exact abs_bT4ub_le hβ0 hβ1 (le_of_lt hx.1) hx.2)
  rw [show boxElb β = fun s => (13/5)*bhh β s + ((2-β)^2-β^2)/(2*((2-β)^2+s^2))
      + (((2-β)^2-β^2)^2/(8*((2-β)^2+s^2)^2) + ((2-β)^2-β^2)^3/(16*((2-β)^2+s^2)^3))
      - bT3ub β s - bT4ub β s from rfl]
  exact (((h1.add h2).add h3).sub h4).sub h5

lemma integral_assembly {β X Y : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hX : (∫ s in (1/4:ℝ)..(3/4), bT3ub β s) ≤ X)
    (hY : (∫ s in (1/4:ℝ)..(3/4), bT4ub β s) ≤ Y) :
    (13/5)*(Real.arctan (bx1 (1-β)) + Real.arctan (bx2 (1-β)))
        + bq1 (1-β) * Real.arctan (bxq (1-β)) + bRq (1-β) - X - Y
      ≤ (∫ s in (1/4:ℝ)..(3/4), boxE β s) := by
  have h1 : IntervalIntegrable (fun s : ℝ => (13/5)*bhh β s) volume (1/4:ℝ) (3/4) :=
    intervalIntegrable_13h β hβ0 hβ1
  have h2 : IntervalIntegrable (fun s : ℝ => ((2-β)^2-β^2)/(2*((2-β)^2+s^2)))
      volume (1/4:ℝ) (3/4) :=
    (continuousOn_q12 β hβ0 hβ1).intervalIntegrable
  have h3 : IntervalIntegrable (fun s : ℝ => ((2-β)^2-β^2)^2/(8*((2-β)^2+s^2)^2)
      + ((2-β)^2-β^2)^3/(16*((2-β)^2+s^2)^3)) volume (1/4:ℝ) (3/4) :=
    (continuousOn_q23 β hβ0 hβ1).intervalIntegrable
  have h4 : IntervalIntegrable (bT3ub β) volume (1/4:ℝ) (3/4) :=
    (continuousOn_bT3ub β).intervalIntegrable
  have h5 : IntervalIntegrable (bT4ub β) volume (1/4:ℝ) (3/4) :=
    intervalIntegrable_bT4ub_of_bound hβ0 hβ1 (fun x hx => by
      rw [Set.uIoc_of_le (by norm_num : (1/4:ℝ) ≤ 3/4)] at hx
      exact abs_bT4ub_le hβ0 hβ1 (le_of_lt hx.1) hx.2)
  have hdec : (∫ s in (1/4:ℝ)..(3/4), boxElb β s)
      = (∫ s in (1/4:ℝ)..(3/4), (13/5)*bhh β s)
        + (∫ s in (1/4:ℝ)..(3/4), ((2-β)^2-β^2)/(2*((2-β)^2+s^2)))
        + (∫ s in (1/4:ℝ)..(3/4), ((2-β)^2-β^2)^2/(8*((2-β)^2+s^2)^2)
            + ((2-β)^2-β^2)^3/(16*((2-β)^2+s^2)^3))
        - (∫ s in (1/4:ℝ)..(3/4), bT3ub β s)
        - (∫ s in (1/4:ℝ)..(3/4), bT4ub β s) := by
    rw [show boxElb β = fun s => (13/5)*bhh β s + ((2-β)^2-β^2)/(2*((2-β)^2+s^2))
        + (((2-β)^2-β^2)^2/(8*((2-β)^2+s^2)^2) + ((2-β)^2-β^2)^3/(16*((2-β)^2+s^2)^3))
        - bT3ub β s - bT4ub β s from rfl]
    exact integral_five h1 h2 h3 h4 h5
  have hmono : (∫ s in (1/4:ℝ)..(3/4), boxElb β s) ≤ (∫ s in (1/4:ℝ)..(3/4), boxE β s) :=
    intervalIntegral.integral_mono_on (by norm_num) (intervalIntegrable_boxElb hβ0 hβ1)
      (intervalIntegrable_boxE hβ0 hβ1) (fun s hs => boxElb_le_boxE hβ0 hβ1 hs.1 hs.2)
  have hbhh : (∫ s in (1/4:ℝ)..(3/4), (13/5)*bhh β s)
      = (13/5)*(Real.arctan (bx1 (1-β)) + Real.arctan (bx2 (1-β))) := by
    rw [intervalIntegral.integral_const_mul, integral_bhh hβ0 hβ1]
  have hq1 : (∫ s in (1/4:ℝ)..(3/4), ((2-β)^2-β^2)/(2*((2-β)^2+s^2)))
      = bq1 (1-β)*Real.arctan (bxq (1-β)) := integral_q1 hβ0 hβ1
  have hq23 := integral_q23_lower hβ0 hβ1
  linarith [hdec, hmono, hbhh, hq1, hq23, hX, hY]

/-- Region I (`β ≥ 3/4`). -/
lemma region_I {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hβ : 3/4 ≤ β) :
    (13/5)*(Real.arctan (bx1 (1-β)) + Real.arctan (bx2 (1-β)))
        + bq1 (1-β) * Real.arctan (bxq (1-β)) + bRq (1-β) - U3u β - U4Iu β
      ≤ (∫ s in (1/4:ℝ)..(3/4), boxE β s) :=
  integral_assembly hβ0 hβ1 (integral_bT3ub_le hβ0 hβ1) (le_of_eq (integral_bT4ub_I hβ0 hβ1 hβ))

/-- Region II (`1/4 ≤ β ≤ 3/4`). -/
lemma region_II {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hβ2 : 1/4 ≤ β) (hβ3 : β ≤ 3/4) :
    (13/5)*(Real.arctan (bx1 (1-β)) + Real.arctan (bx2 (1-β)))
        + bq1 (1-β) * Real.arctan (bxq (1-β)) + bRq (1-β) - U3u β - U4IIu β
      ≤ (∫ s in (1/4:ℝ)..(3/4), boxE β s) :=
  integral_assembly hβ0 hβ1 (integral_bT3ub_le hβ0 hβ1) (integral_bT4ub_II_le hβ0 hβ1 hβ2 hβ3)

/-- Region III (`β ≤ 1/4`). -/
lemma region_III {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hβ : β ≤ 1/4) :
    (13/5)*(Real.arctan (bx1 (1-β)) + Real.arctan (bx2 (1-β)))
        + bq1 (1-β) * Real.arctan (bxq (1-β)) + bRq (1-β) - U3u β - U4IIIu β
      ≤ (∫ s in (1/4:ℝ)..(3/4), boxE β s) :=
  integral_assembly hβ0 hβ1 (integral_bT3ub_le hβ0 hβ1) (le_of_eq (integral_bT4ub_III hβ0 hβ1 hβ))



/-! ## The endpoint functions and their comparison with the region bounds -/

/-- The `u`-dependent lower bound obtained from the arctan integrals. -/
def PA (u : ℝ) : ℝ :=
  (13/5)*(Real.arctan (bx1 u) + Real.arctan (bx2 u)) + bq1 u * Real.arctan (bxq u) + bRq u

/-- Endpoint form of `PA`. -/
def posF (a b : ℝ) : ℝ :=
  (13/5)*(boxT8 (bx1 b) + boxT8 (bx2 a)) + bq1 a * boxT8 (bxq b) + bRq a

/-- Endpoint form of `U3u`. -/
def U3F (a b : ℝ) : ℝ :=
  bR3s a + (cLog2UB + bL1 b)*bA1 b - cJlogLB + cJlog2UB/(4*(1+b)^2)

/-- Endpoint form of `U4Iu`. -/
def U4IF (a b : ℝ) : ℝ :=
  bR4s b + (cLog2UB + bL2 a)*bA2 b - cJlogLB + cJlog2UB/(4*(1+b^2))

/-- Endpoint form of `U4IIu`. -/
def U4IIF (a b : ℝ) : ℝ :=
  beJ2 a + (3/4-a) - (7/4-b)*cLog2LB + (1-a)*cLog3UB + (5/4-a)*(-blog1m b)

/-- Endpoint form of `U4IIIu`. -/
def U4IIIF (a b : ℝ) : ℝ := (1-a)*cLog3UB


/-! ## Numeric membership lemmas for the auxiliary functions -/

lemma bx1_nonneg {z : ℝ} (hz : 0 ≤ z) : 0 ≤ bx1 z := by
  unfold bx1; apply div_nonneg <;> positivity

lemma bx1_le_one {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) : bx1 z ≤ 1 := by
  unfold bx1
  rw [div_le_one (by positivity)]
  nlinarith

lemma bx2_nonneg {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) : 0 ≤ bx2 z := by
  unfold bx2
  apply div_nonneg
  · linarith
  · nlinarith [sq_nonneg (z - 2)]

lemma bx2_le_one {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) : bx2 z ≤ 1 := by
  unfold bx2
  rw [div_le_one (by nlinarith [sq_nonneg (z - 2)])]
  nlinarith [sq_nonneg (z - 7/4)]

lemma bxq_nonneg {z : ℝ} (hz : 0 ≤ z) : 0 ≤ bxq z := by
  unfold bxq; apply div_nonneg <;> positivity

lemma bxq_le_one {z : ℝ} (hz : 0 ≤ z) : bxq z ≤ 1 := by
  unfold bxq
  rw [div_le_one (by positivity)]
  nlinarith [sq_nonneg (z + 3/4)]

lemma bL1_nonneg {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) : 0 ≤ bL1 u := by
  have hfac : bL1 u = u*(1 - u/2 + u^2/3 - u^3/4 + u^4/5) := by unfold bL1; ring
  rw [hfac]
  have h2 : u^2 ≤ 1 := pow_le_one₀ hu0 hu1
  have h3 : u^3 ≤ 1 := pow_le_one₀ hu0 hu1
  have h4 : 0 ≤ u^4 := by positivity
  have hbr : 0 ≤ 1 - u/2 + u^2/3 - u^3/4 + u^4/5 := by nlinarith
  exact mul_nonneg hu0 hbr

lemma bL2_ge_neg_half {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1/4) : -(1:ℝ)/2 ≤ bL2 u := by
  have h2 : u^2 ≤ u/4 := by
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hu0 (by linarith : u - 1/4 ≤ 0)]
  have h3 : u^3 ≤ u/16 := by nlinarith [mul_nonneg hu0 (sub_nonneg.mpr h2)]
  have h4 : u^4 ≤ u/64 := by nlinarith [mul_nonneg hu0 (sub_nonneg.mpr h3)]
  have h5 : u^5 ≤ u/256 := by nlinarith [mul_nonneg hu0 (sub_nonneg.mpr h4)]
  have h6 : u^6 ≤ u/1024 := by nlinarith [mul_nonneg hu0 (sub_nonneg.mpr h5)]
  unfold bL2
  linarith

lemma cLog2UB_add_bL2_nonneg {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1/4) :
    0 ≤ cLog2UB + bL2 a := by
  have h := bL2_ge_neg_half ha ha1
  have h2 : (1:ℝ)/2 ≤ cLog2UB := by unfold cLog2UB; norm_num
  linarith

/-! ## Comparison of the region bounds with their endpoint forms -/

lemma cJlogLB_le_dJlog : cJlogLB ≤ dJlog := by
  unfold cJlogLB dJlog
  have h1 := cLog3LB_le_log_three
  have h2 := log_two_le_cLog2UB
  linarith

lemma dJlog2_le_cJlog2UB : dJlog2 ≤ cJlog2UB := by
  unfold dJlog2 cJlog2UB
  have h1 := log_three_le_cLog3UB
  have h2 := cLog2LB_le_log_two
  linarith

lemma dJlog2_div_le {β b : ℝ} (hub : 1-β ≤ b) (hβ1 : β < 1) :
    dJlog2/(4*(2-β)^2) ≤ cJlog2UB/(4*(1+b)^2) := by
  have hle : dJlog2 ≤ cJlog2UB := dJlog2_le_cJlog2UB
  have hd0 : dJlog2 ≤ 0 := le_trans hle cJlog2UB_nonpos
  have hb2 : 2-β ≤ (1:ℝ) + b := by linarith
  have h1b : (0:ℝ) < 1+b := by linarith
  have hX : 4*(2-β)^2 ≤ 4*(1+b)^2 := by
    have h : (2-β)^2 ≤ (1+b)^2 := pow_le_pow_left₀ (by linarith) hb2 2
    linarith
  have hY : (0:ℝ) < 4*(1+b)^2 := mul_pos (by norm_num) (pow_pos h1b 2)
  have hZp : (0:ℝ) < 4*(2-β)^2 := by nlinarith
  have s1 : dJlog2/(4*(2-β)^2) ≤ dJlog2/(4*(1+b)^2) := by
    rw [div_le_div_iff₀ hZp hY]
    exact mul_le_mul_of_nonpos_left hX hd0
  have s2 : dJlog2/(4*(1+b)^2) ≤ cJlog2UB/(4*(1+b)^2) := by
    rw [div_le_div_iff₀ hY hY]
    exact mul_le_mul_of_nonneg_right hle hY.le
  linarith

lemma dJlog2_div_le_sq {β b : ℝ} (hub : 1-β ≤ b) (hβ1 : β < 1) :
    dJlog2/(4*(1+(1-β)^2)) ≤ cJlog2UB/(4*(1+b^2)) := by
  have hle : dJlog2 ≤ cJlog2UB := dJlog2_le_cJlog2UB
  have hd0 : dJlog2 ≤ 0 := le_trans hle cJlog2UB_nonpos
  have hu0 : 0 ≤ 1-β := by linarith
  have hsq : (1-β)^2 ≤ b^2 := by nlinarith
  have hX : 4*(1+(1-β)^2) ≤ 4*(1+b^2) := by linarith
  have hY : (0:ℝ) < 4*(1+b^2) := by positivity
  have hZp : (0:ℝ) < 4*(1+(1-β)^2) := by positivity
  have s1 : dJlog2/(4*(1+(1-β)^2)) ≤ dJlog2/(4*(1+b^2)) := by
    rw [div_le_div_iff₀ hZp hY]
    exact mul_le_mul_of_nonpos_left hX hd0
  have s2 : dJlog2/(4*(1+b^2)) ≤ cJlog2UB/(4*(1+b^2)) := by
    rw [div_le_div_iff₀ hY hY]
    exact mul_le_mul_of_nonneg_right hle hY.le
  linarith

lemma posF_le_PA {a b u : ℝ} (ha : 0 ≤ a) (hau : a ≤ u) (hub : u ≤ b) (hb : b ≤ 1) :
    posF a b ≤ PA u := by
  have hb0 : 0 ≤ b := le_trans ha (le_trans hau hub)
  have hu0 : 0 ≤ u := le_trans ha hau
  have hu1 : u ≤ 1 := le_trans hub hb
  have e1 : boxT8 (bx1 b) ≤ Real.arctan (bx1 u) :=
    le_trans (arctan_ge_boxT8 (bx1_nonneg hb0))
      (Real.arctan_mono (bx1_antitone hu0 hub hb))
  have e2 : boxT8 (bx2 a) ≤ Real.arctan (bx2 u) :=
    le_trans (arctan_ge_boxT8 (bx2_nonneg ha (le_trans hau hu1)))
      (Real.arctan_mono (bx2_monotone ha hau hu1))
  have hqb0 : 0 ≤ bxq b := bxq_nonneg hb0
  have hqb1 : bxq b ≤ 1 := bxq_le_one hb0
  have e3 : boxT8 (bxq b) ≤ Real.arctan (bxq u) :=
    le_trans (arctan_ge_boxT8 hqb0)
      (Real.arctan_mono (bxq_antitone hu0 hub hb))
  have hbt : bq1 a ≤ bq1 u := bq1_monotone ha hau
  have hprod : bq1 a * boxT8 (bxq b) ≤ bq1 u * Real.arctan (bxq u) :=
    mul_le_mul hbt e3 (boxT8_nonneg hqb0 hqb1) (bq1_nonneg hu0)
  have hR : bRq a ≤ bRq u := bRq_monotone ha hau hu1
  unfold posF PA
  linarith

lemma U3u_le_U3F {a b β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (ha : 0 ≤ a) (hau : a ≤ 1-β) (hub : 1-β ≤ b) (hb : b ≤ 1) :
    U3u β ≤ U3F a b := by
  have hb0 : 0 ≤ b := le_trans ha (le_trans hau hub)
  have hu0 : 0 ≤ 1-β := by linarith
  have hu1 : 1-β ≤ 1 := by linarith
  have h1 : bR3s (1-β) ≤ bR3s a := bR3s_antitone ha hau hu1
  have hlog2 : Real.log 2 ≤ cLog2UB := log_two_le_cLog2UB
  have hlog2b : Real.log (2-β) ≤ bL1 b := by
    have h := log_one_add_le_bL1 hu0 hu1
    have h2 := bL1_monotone hub
    have he : 2-β = 1+(1-β) := by ring
    rw [he]
    linarith
  have hA : Real.log 2 + Real.log (2-β) ≤ cLog2UB + bL1 b := by linarith
  have hA0 : 0 ≤ Real.log 2 + Real.log (2-β) := by
    have h1 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have h2 : 0 ≤ Real.log (2-β) := Real.log_nonneg (by linarith)
    linarith
  have hA0' : 0 ≤ cLog2UB + bL1 b := by
    have h1 : 0 ≤ cLog2UB := by unfold cLog2UB; norm_num
    have h2 : 0 ≤ bL1 b := bL1_nonneg hb0 hb
    linarith
  have hC : bA1 (1-β) ≤ bA1 b := bA1_monotone hu0 hub
  have hC0 : 0 ≤ bA1 (1-β) := bA1_nonneg hu0
  have hC0' : 0 ≤ bA1 b := bA1_nonneg hb0
  have hprod := mul_le_mul hA hC hC0 hA0'
  have h3 : cJlogLB ≤ dJlog := cJlogLB_le_dJlog
  have h4 := dJlog2_div_le (β := β) (b := b) hub hβ1
  unfold U3u U3F
  linarith

lemma U4Iu_le_U4IF {a b β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hβ : 3/4 ≤ β)
    (ha : 0 ≤ a) (hau : a ≤ 1-β) (hub : 1-β ≤ b) (hb : b ≤ 1/4) :
    U4Iu β ≤ U4IF a b := by
  have hb0 : 0 ≤ b := le_trans ha (le_trans hau hub)
  have hu0 : 0 ≤ 1-β := by linarith
  have hu1 : 1-β ≤ 1/4 := by linarith
  have h1 : bR4s (1-β) ≤ bR4s b := bR4s_monotone hu0 hub hb
  have hlog2b : Real.log (2*β) ≤ cLog2UB + bL2 a := by
    have hmul : Real.log (2*β) = Real.log 2 + Real.log β :=
      Real.log_mul (by norm_num) (ne_of_gt hβ0)
    have hbL2 : Real.log β ≤ bL2 a := by
      have he : β = 1-(1-β) := by ring
      have hl : Real.log (1-(1-β)) ≤ bL2 (1-β) := log_one_sub_le_bL2 hu0 (by linarith)
      have h2 : bL2 (1-β) ≤ bL2 a := bL2_antitone ha hau
      rw [he]; linarith
    have h2 : Real.log 2 ≤ cLog2UB := log_two_le_cLog2UB
    linarith
  have hA0 : 0 ≤ Real.log (2*β) := Real.log_nonneg (by linarith)
  have hA0' : 0 ≤ cLog2UB + bL2 a := cLog2UB_add_bL2_nonneg ha (le_trans hau hu1)
  have hC : bA2 (1-β) ≤ bA2 b := bA2_monotone hu0 hub
  have hC0 : 0 ≤ bA2 (1-β) := bA2_nonneg _
  have hC0' : 0 ≤ bA2 b := bA2_nonneg _
  have hprod := mul_le_mul hlog2b hC hC0 hA0'
  have h3 : cJlogLB ≤ dJlog := cJlogLB_le_dJlog
  have h4 := dJlog2_div_le_sq (β := β) (b := b) hub hβ1
  unfold U4Iu U4IF
  linarith

lemma blog1m_nonpos {b : ℝ} (hb : 0 ≤ b) : blog1m b ≤ 0 := by
  unfold blog1m
  have h2 : 0 ≤ b^2 := by positivity
  have h3 : 0 ≤ b^3 := by positivity
  have h4 : 0 ≤ b^4 := by positivity
  have h5 : 0 ≤ b^5 := by positivity
  have h6 : 0 ≤ b^6 := by positivity
  have h7 : 0 ≤ b^7 := by positivity
  have h8 : 0 ≤ b^8 := by positivity
  have h9 : 0 ≤ b^9 := by positivity
  have h10 : 0 ≤ b^10 := by positivity
  have h11 : 0 ≤ b^11 := by positivity
  have h12 : 0 ≤ b^12 := by positivity
  have h13 : 0 ≤ b^13 := by positivity
  linarith

lemma U4IIu_le_U4IIF {a b β : ℝ} (hβ2 : 1/4 ≤ β) (hβ3 : β ≤ 3/4)
    (ha : 1/4 ≤ a) (hau : a ≤ 1-β) (hub : 1-β ≤ b) (hb : b ≤ 3/4) :
    U4IIu β ≤ U4IIF a b := by
  have ha0 : 0 ≤ a := by linarith
  have hu0 : 0 ≤ 1-β := by linarith
  have hu1 : 1-β ≤ 3/4 := le_trans hub hb
  have h1 : beJ2 (1-β) ≤ beJ2 a := beJ2_antitone ha0 hau hu1
  have h2 : β*Real.log 3 ≤ (1-a)*cLog3UB := by
    have hlog3 : Real.log 3 ≤ cLog3UB := log_three_le_cLog3UB
    have hβa : β ≤ 1-a := by linarith
    have hβ0 : 0 ≤ β := by linarith
    have hc : 0 ≤ cLog3UB := by unfold cLog3UB; norm_num
    have h1 : β*Real.log 3 ≤ β*cLog3UB := mul_le_mul_of_nonneg_left hlog3 hβ0
    have h2 : β*cLog3UB ≤ (1-a)*cLog3UB := mul_le_mul_of_nonneg_right hβa hc
    linarith
  have h3 : -(β+3/4)*Real.log 2 ≤ -(7/4-b)*cLog2LB := by
    have hlog2 : cLog2LB ≤ Real.log 2 := cLog2LB_le_log_two
    have h3a : (7/4-b) ≤ β+3/4 := by linarith
    have hcl : 0 ≤ cLog2LB := by unfold cLog2LB; norm_num
    have h1 : (β+3/4)*cLog2LB ≤ (β+3/4)*Real.log 2 :=
      mul_le_mul_of_nonneg_left hlog2 (by linarith)
    have h2 : (7/4-b)*cLog2LB ≤ (β+3/4)*cLog2LB :=
      mul_le_mul_of_nonneg_right h3a hcl
    linarith
  have h4 : -(β+1/4)*Real.log β ≤ (5/4-a)*(-blog1m b) := by
    have hlogb : blog1m b ≤ Real.log (1-b) :=
      blog1m_le_log_one_sub (by linarith) (by linarith)
    have h1 : Real.log (1-(1-β)) ≥ blog1m (1-β) := blog1m_le_log_one_sub hu0 hu1
    have h2 : blog1m (1-β) ≥ blog1m b := blog1m_antitone (by linarith) hub
    have hβeq : β = 1-(1-β) := by ring
    have h3 : Real.log β ≥ blog1m b := by rw [hβeq]; linarith
    have h3' : -Real.log β ≤ -blog1m b := by linarith
    have hnb : (0:ℝ) ≤ -blog1m b := by
      have := blog1m_nonpos (by linarith : (0:ℝ) ≤ b)
      linarith
    have h4a : β+1/4 ≤ 5/4-a := by linarith
    have h5 : 0 ≤ β+1/4 := by linarith
    have h6 : 0 ≤ 5/4-a := by linarith
    calc -(β+1/4)*Real.log β = (β+1/4)*(-Real.log β) := by ring
      _ ≤ (β+1/4)*(-blog1m b) := mul_le_mul_of_nonneg_left h3' h5
      _ ≤ (5/4-a)*(-blog1m b) := mul_le_mul_of_nonneg_right h4a hnb
  have h5 : β - 1/4 ≤ 3/4 - a := by linarith
  unfold U4IIu U4IIF
  linarith

lemma U4IIIu_le_U4IIIF {a b β : ℝ} (hβ0 : 0 < β) (hβ : β ≤ 1/4) (ha : 3/4 ≤ a)
    (hau : a ≤ 1-β) : U4IIIu β ≤ U4IIIF a b := by
  have hlog3 : Real.log 3 ≤ cLog3UB := log_three_le_cLog3UB
  have hβ0 : 0 ≤ β := by linarith
  have hβa : β ≤ 1-a := by linarith
  have hc : 0 ≤ cLog3UB := by unfold cLog3UB; norm_num
  have h1 : β*Real.log 3 ≤ β*cLog3UB := mul_le_mul_of_nonneg_left hlog3 hβ0
  have h2 : β*cLog3UB ≤ (1-a)*cLog3UB := mul_le_mul_of_nonneg_right hβa hc
  unfold U4IIIu U4IIIF
  linarith

/-- Region I case. -/
lemma case_I {β a b : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hβ : 3/4 ≤ β)
    (ha : 0 ≤ a) (hau : a ≤ 1-β) (hub : 1-β ≤ b) (hb : b ≤ 1/4)
    (hconst : (11:ℝ)/20 ≤ posF a b - U3F a b - U4IF a b) :
    (11:ℝ)/20 ≤ ∫ s in (1/4:ℝ)..(3/4), boxE β s := by
  have h1 := region_I hβ0 hβ1 hβ
  have h2 := posF_le_PA ha hau hub (by linarith : b ≤ 1)
  unfold PA at h2
  have h3 := U3u_le_U3F hβ0 hβ1 ha hau hub (by linarith : b ≤ 1)
  have h4 := U4Iu_le_U4IF hβ0 hβ1 hβ ha hau hub hb
  linarith

/-- Region II case. -/
lemma case_II {β a b : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hβ2 : 1/4 ≤ β) (hβ3 : β ≤ 3/4)
    (ha : 1/4 ≤ a) (hau : a ≤ 1-β) (hub : 1-β ≤ b) (hb : b ≤ 3/4)
    (hconst : (11:ℝ)/20 ≤ posF a b - U3F a b - U4IIF a b) :
    (11:ℝ)/20 ≤ ∫ s in (1/4:ℝ)..(3/4), boxE β s := by
  have h1 := region_II hβ0 hβ1 hβ2 hβ3
  have h2 := posF_le_PA (by linarith : (0:ℝ) ≤ a) hau hub (by linarith : b ≤ 1)
  unfold PA at h2
  have h3 := U3u_le_U3F hβ0 hβ1 (by linarith : (0:ℝ) ≤ a) hau hub (by linarith : b ≤ 1)
  have h4 := U4IIu_le_U4IIF hβ2 hβ3 ha hau hub hb
  linarith

/-- Region III case. -/
lemma case_III {β a b : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hβ : β ≤ 1/4)
    (ha : 3/4 ≤ a) (hau : a ≤ 1-β) (hub : 1-β ≤ b) (hb : b ≤ 1)
    (hconst : (11:ℝ)/20 ≤ posF a b - U3F a b - U4IIIF a b) :
    (11:ℝ)/20 ≤ ∫ s in (1/4:ℝ)..(3/4), boxE β s := by
  have h1 := region_III hβ0 hβ1 hβ
  have h2 := posF_le_PA (by linarith : (0:ℝ) ≤ a) hau hub hb
  unfold PA at h2
  have h3 := U3u_le_U3F hβ0 hβ1 (by linarith : (0:ℝ) ≤ a) hau hub hb
  have h4 := U4IIIu_le_U4IIIF (b := b) hβ0 hβ ha hau
  linarith





set_option maxHeartbeats 4000000 in
theorem boxWindow_B_lower_11_20 {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    (11:ℝ)/20 ≤ ∫ s in (1/4 : ℝ)..(3/4),
      ( (13/5)*((3/2-β)/((3/2-β)^2+s^2)+(1+β)/((1+β)^2+s^2))
        + ((2-β)^2-β^2)/(2*((2-β)^2+s^2))
        + ((2-β)^2-β^2)^2/(8*((2-β)^2+s^2)^2)
        + ((2-β)^2-β^2)^3/(16*((2-β)^2+s^2)^3)
        - Real.log ((4*(2-β)^2+s^2)/(2*(2-β)*s))*(1-s^2/(4*(2-β)^2))
        - (if s ≤ β then Real.log ((4*β^2+s^2)/(2*β*s))*(1-s^2/(2*((2-β)^2+β^2)))
                   else (2-β)*β/(s*Real.sqrt ((2-β)^2+s^2))) ) := by
  show (11:ℝ)/20 ≤ ∫ s in (1/4 : ℝ)..(3/4), boxE β s
  rcases lt_or_ge (1-β) (7/2048 : ℝ) with h1 | h1
  · exact case_I (a := (0:ℝ)) (b := (7/2048 : ℝ)) hβ0 hβ1 (by linarith [h1, show (((7/2048 : ℝ)) ≤ (1/4:ℝ)) by norm_num]) (by norm_num) (by linarith) (by linarith) (by norm_num)
      (by norm_num [posF, U3F, U4IF, U4IIF, U4IIIF, boxT8, bx1, bx2, bxq, bq1, bRq, bR3s, bA1, bA2, bR4s, bL1, bL2, beJ2, blog1m, cLog2UB, cLog2LB, cLog3UB, cLog3LB, cJlogLB, cJlog2UB])
  rcases lt_or_ge (1-β) (9/1024 : ℝ) with h2 | h2
  · exact case_I (a := (7/2048 : ℝ)) (b := (9/1024 : ℝ)) hβ0 hβ1 (by linarith [h2, show (((9/1024 : ℝ)) ≤ (1/4:ℝ)) by norm_num]) (by norm_num) (by linarith) (by linarith) (by norm_num)
      (by norm_num [posF, U3F, U4IF, U4IIF, U4IIIF, boxT8, bx1, bx2, bxq, bq1, bRq, bR3s, bA1, bA2, bR4s, bL1, bL2, beJ2, blog1m, cLog2UB, cLog2LB, cLog3UB, cLog3LB, cJlogLB, cJlog2UB])
  rcases lt_or_ge (1-β) (9/512 : ℝ) with h3 | h3
  · exact case_I (a := (9/1024 : ℝ)) (b := (9/512 : ℝ)) hβ0 hβ1 (by linarith [h3, show (((9/512 : ℝ)) ≤ (1/4:ℝ)) by norm_num]) (by norm_num) (by linarith) (by linarith) (by norm_num)
      (by norm_num [posF, U3F, U4IF, U4IIF, U4IIIF, boxT8, bx1, bx2, bxq, bq1, bRq, bR3s, bA1, bA2, bR4s, bL1, bL2, beJ2, blog1m, cLog2UB, cLog2LB, cLog3UB, cLog3LB, cJlogLB, cJlog2UB])
  rcases lt_or_ge (1-β) (1/32 : ℝ) with h4 | h4
  · exact case_I (a := (9/512 : ℝ)) (b := (1/32 : ℝ)) hβ0 hβ1 (by linarith [h4, show (((1/32 : ℝ)) ≤ (1/4:ℝ)) by norm_num]) (by norm_num) (by linarith) (by linarith) (by norm_num)
      (by norm_num [posF, U3F, U4IF, U4IIF, U4IIIF, boxT8, bx1, bx2, bxq, bq1, bRq, bR3s, bA1, bA2, bR4s, bL1, bL2, beJ2, blog1m, cLog2UB, cLog2LB, cLog3UB, cLog3LB, cJlogLB, cJlog2UB])
  rcases lt_or_ge (1-β) (105/2048 : ℝ) with h5 | h5
  · exact case_I (a := (1/32 : ℝ)) (b := (105/2048 : ℝ)) hβ0 hβ1 (by linarith [h5, show (((105/2048 : ℝ)) ≤ (1/4:ℝ)) by norm_num]) (by norm_num) (by linarith) (by linarith) (by norm_num)
      (by norm_num [posF, U3F, U4IF, U4IIF, U4IIIF, boxT8, bx1, bx2, bxq, bq1, bRq, bR3s, bA1, bA2, bR4s, bL1, bL2, beJ2, blog1m, cLog2UB, cLog2LB, cLog3UB, cLog3LB, cJlogLB, cJlog2UB])
  rcases lt_or_ge (1-β) (161/2048 : ℝ) with h6 | h6
  · exact case_I (a := (105/2048 : ℝ)) (b := (161/2048 : ℝ)) hβ0 hβ1 (by linarith [h6, show (((161/2048 : ℝ)) ≤ (1/4:ℝ)) by norm_num]) (by norm_num) (by linarith) (by linarith) (by norm_num)
      (by norm_num [posF, U3F, U4IF, U4IIF, U4IIIF, boxT8, bx1, bx2, bxq, bq1, bRq, bR3s, bA1, bA2, bR4s, bL1, bL2, beJ2, blog1m, cLog2UB, cLog2LB, cLog3UB, cLog3LB, cJlogLB, cJlog2UB])
  rcases lt_or_ge (1-β) (233/2048 : ℝ) with h7 | h7
  · exact case_I (a := (161/2048 : ℝ)) (b := (233/2048 : ℝ)) hβ0 hβ1 (by linarith [h7, show (((233/2048 : ℝ)) ≤ (1/4:ℝ)) by norm_num]) (by norm_num) (by linarith) (by linarith) (by norm_num)
      (by norm_num [posF, U3F, U4IF, U4IIF, U4IIIF, boxT8, bx1, bx2, bxq, bq1, bRq, bR3s, bA1, bA2, bR4s, bL1, bL2, beJ2, blog1m, cLog2UB, cLog2LB, cLog3UB, cLog3LB, cJlogLB, cJlog2UB])
  rcases lt_or_ge (1-β) (321/2048 : ℝ) with h8 | h8
  · exact case_I (a := (233/2048 : ℝ)) (b := (321/2048 : ℝ)) hβ0 hβ1 (by linarith [h8, show (((321/2048 : ℝ)) ≤ (1/4:ℝ)) by norm_num]) (by norm_num) (by linarith) (by linarith) (by norm_num)
      (by norm_num [posF, U3F, U4IF, U4IIF, U4IIIF, boxT8, bx1, bx2, bxq, bq1, bRq, bR3s, bA1, bA2, bR4s, bL1, bL2, beJ2, blog1m, cLog2UB, cLog2LB, cLog3UB, cLog3LB, cJlogLB, cJlog2UB])
  rcases lt_or_ge (1-β) (423/2048 : ℝ) with h9 | h9
  · exact case_I (a := (321/2048 : ℝ)) (b := (423/2048 : ℝ)) hβ0 hβ1 (by linarith [h9, show (((423/2048 : ℝ)) ≤ (1/4:ℝ)) by norm_num]) (by norm_num) (by linarith) (by linarith) (by norm_num)
      (by norm_num [posF, U3F, U4IF, U4IIF, U4IIIF, boxT8, bx1, bx2, bxq, bq1, bRq, bR3s, bA1, bA2, bR4s, bL1, bL2, beJ2, blog1m, cLog2UB, cLog2LB, cLog3UB, cLog3LB, cJlogLB, cJlog2UB])
  rcases lt_or_ge (1-β) (1/4 : ℝ) with h10 | h10
  · exact case_I (a := (423/2048 : ℝ)) (b := (1/4 : ℝ)) hβ0 hβ1 (by linarith [h10, show (((1/4 : ℝ)) ≤ (1/4:ℝ)) by norm_num]) (by norm_num) (by linarith) (by linarith) (by norm_num)
      (by norm_num [posF, U3F, U4IF, U4IIF, U4IIIF, boxT8, bx1, bx2, bxq, bq1, bRq, bR3s, bA1, bA2, bR4s, bL1, bL2, beJ2, blog1m, cLog2UB, cLog2LB, cLog3UB, cLog3LB, cJlogLB, cJlog2UB])
  rcases lt_or_ge (1-β) (541/2048 : ℝ) with h11 | h11
  · exact case_II (a := (1/4 : ℝ)) (b := (541/2048 : ℝ)) hβ0 hβ1 (by linarith [h11, show (((541/2048 : ℝ)) ≤ (3/4:ℝ)) by norm_num]) (by linarith) (by norm_num) (by linarith) (by linarith) (by norm_num)
      (by norm_num [posF, U3F, U4IF, U4IIF, U4IIIF, boxT8, bx1, bx2, bxq, bq1, bRq, bR3s, bA1, bA2, bR4s, bL1, bL2, beJ2, blog1m, cLog2UB, cLog2LB, cLog3UB, cLog3LB, cJlogLB, cJlog2UB])
  rcases lt_or_ge (1-β) (571/2048 : ℝ) with h12 | h12
  · exact case_II (a := (541/2048 : ℝ)) (b := (571/2048 : ℝ)) hβ0 hβ1 (by linarith [h12, show (((571/2048 : ℝ)) ≤ (3/4:ℝ)) by norm_num]) (by linarith) (by norm_num) (by linarith) (by linarith) (by norm_num)
      (by norm_num [posF, U3F, U4IF, U4IIF, U4IIIF, boxT8, bx1, bx2, bxq, bq1, bRq, bR3s, bA1, bA2, bR4s, bL1, bL2, beJ2, blog1m, cLog2UB, cLog2LB, cLog3UB, cLog3LB, cJlogLB, cJlog2UB])
  rcases lt_or_ge (1-β) (603/2048 : ℝ) with h13 | h13
  · exact case_II (a := (571/2048 : ℝ)) (b := (603/2048 : ℝ)) hβ0 hβ1 (by linarith [h13, show (((603/2048 : ℝ)) ≤ (3/4:ℝ)) by norm_num]) (by linarith) (by norm_num) (by linarith) (by linarith) (by norm_num)
      (by norm_num [posF, U3F, U4IF, U4IIF, U4IIIF, boxT8, bx1, bx2, bxq, bq1, bRq, bR3s, bA1, bA2, bR4s, bL1, bL2, beJ2, blog1m, cLog2UB, cLog2LB, cLog3UB, cLog3LB, cJlogLB, cJlog2UB])
  rcases lt_or_ge (1-β) (159/512 : ℝ) with h14 | h14
  · exact case_II (a := (603/2048 : ℝ)) (b := (159/512 : ℝ)) hβ0 hβ1 (by linarith [h14, show (((159/512 : ℝ)) ≤ (3/4:ℝ)) by norm_num]) (by linarith) (by norm_num) (by linarith) (by linarith) (by norm_num)
      (by norm_num [posF, U3F, U4IF, U4IIF, U4IIIF, boxT8, bx1, bx2, bxq, bq1, bRq, bR3s, bA1, bA2, bR4s, bL1, bL2, beJ2, blog1m, cLog2UB, cLog2LB, cLog3UB, cLog3LB, cJlogLB, cJlog2UB])
  rcases lt_or_ge (1-β) (671/2048 : ℝ) with h15 | h15
  · exact case_II (a := (159/512 : ℝ)) (b := (671/2048 : ℝ)) hβ0 hβ1 (by linarith [h15, show (((671/2048 : ℝ)) ≤ (3/4:ℝ)) by norm_num]) (by linarith) (by norm_num) (by linarith) (by linarith) (by norm_num)
      (by norm_num [posF, U3F, U4IF, U4IIF, U4IIIF, boxT8, bx1, bx2, bxq, bq1, bRq, bR3s, bA1, bA2, bR4s, bL1, bL2, beJ2, blog1m, cLog2UB, cLog2LB, cLog3UB, cLog3LB, cJlogLB, cJlog2UB])
  rcases lt_or_ge (1-β) (177/512 : ℝ) with h16 | h16
  · exact case_II (a := (671/2048 : ℝ)) (b := (177/512 : ℝ)) hβ0 hβ1 (by linarith [h16, show (((177/512 : ℝ)) ≤ (3/4:ℝ)) by norm_num]) (by linarith) (by norm_num) (by linarith) (by linarith) (by norm_num)
      (by norm_num [posF, U3F, U4IF, U4IIF, U4IIIF, boxT8, bx1, bx2, bxq, bq1, bRq, bR3s, bA1, bA2, bR4s, bL1, bL2, beJ2, blog1m, cLog2UB, cLog2LB, cLog3UB, cLog3LB, cJlogLB, cJlog2UB])
  rcases lt_or_ge (1-β) (747/2048 : ℝ) with h17 | h17
  · exact case_II (a := (177/512 : ℝ)) (b := (747/2048 : ℝ)) hβ0 hβ1 (by linarith [h17, show (((747/2048 : ℝ)) ≤ (3/4:ℝ)) by norm_num]) (by linarith) (by norm_num) (by linarith) (by linarith) (by norm_num)
      (by norm_num [posF, U3F, U4IF, U4IIF, U4IIIF, boxT8, bx1, bx2, bxq, bq1, bRq, bR3s, bA1, bA2, bR4s, bL1, bL2, beJ2, blog1m, cLog2UB, cLog2LB, cLog3UB, cLog3LB, cJlogLB, cJlog2UB])
  rcases lt_or_ge (1-β) (197/512 : ℝ) with h18 | h18
  · exact case_II (a := (747/2048 : ℝ)) (b := (197/512 : ℝ)) hβ0 hβ1 (by linarith [h18, show (((197/512 : ℝ)) ≤ (3/4:ℝ)) by norm_num]) (by linarith) (by norm_num) (by linarith) (by linarith) (by norm_num)
      (by norm_num [posF, U3F, U4IF, U4IIF, U4IIIF, boxT8, bx1, bx2, bxq, bq1, bRq, bR3s, bA1, bA2, bR4s, bL1, bL2, beJ2, blog1m, cLog2UB, cLog2LB, cLog3UB, cLog3LB, cJlogLB, cJlog2UB])
  rcases lt_or_ge (1-β) (13/32 : ℝ) with h19 | h19
  · exact case_II (a := (197/512 : ℝ)) (b := (13/32 : ℝ)) hβ0 hβ1 (by linarith [h19, show (((13/32 : ℝ)) ≤ (3/4:ℝ)) by norm_num]) (by linarith) (by norm_num) (by linarith) (by linarith) (by norm_num)
      (by norm_num [posF, U3F, U4IF, U4IIF, U4IIIF, boxT8, bx1, bx2, bxq, bq1, bRq, bR3s, bA1, bA2, bR4s, bL1, bL2, beJ2, blog1m, cLog2UB, cLog2LB, cLog3UB, cLog3LB, cJlogLB, cJlog2UB])
  rcases lt_or_ge (1-β) (879/2048 : ℝ) with h20 | h20
  · exact case_II (a := (13/32 : ℝ)) (b := (879/2048 : ℝ)) hβ0 hβ1 (by linarith [h20, show (((879/2048 : ℝ)) ≤ (3/4:ℝ)) by norm_num]) (by linarith) (by norm_num) (by linarith) (by linarith) (by norm_num)
      (by norm_num [posF, U3F, U4IF, U4IIF, U4IIIF, boxT8, bx1, bx2, bxq, bq1, bRq, bR3s, bA1, bA2, bR4s, bL1, bL2, beJ2, blog1m, cLog2UB, cLog2LB, cLog3UB, cLog3LB, cJlogLB, cJlog2UB])
  rcases lt_or_ge (1-β) (465/1024 : ℝ) with h21 | h21
  · exact case_II (a := (879/2048 : ℝ)) (b := (465/1024 : ℝ)) hβ0 hβ1 (by linarith [h21, show (((465/1024 : ℝ)) ≤ (3/4:ℝ)) by norm_num]) (by linarith) (by norm_num) (by linarith) (by linarith) (by norm_num)
      (by norm_num [posF, U3F, U4IF, U4IIF, U4IIIF, boxT8, bx1, bx2, bxq, bq1, bRq, bR3s, bA1, bA2, bR4s, bL1, bL2, beJ2, blog1m, cLog2UB, cLog2LB, cLog3UB, cLog3LB, cJlogLB, cJlog2UB])
  rcases lt_or_ge (1-β) (985/2048 : ℝ) with h22 | h22
  · exact case_II (a := (465/1024 : ℝ)) (b := (985/2048 : ℝ)) hβ0 hβ1 (by linarith [h22, show (((985/2048 : ℝ)) ≤ (3/4:ℝ)) by norm_num]) (by linarith) (by norm_num) (by linarith) (by linarith) (by norm_num)
      (by norm_num [posF, U3F, U4IF, U4IIF, U4IIIF, boxT8, bx1, bx2, bxq, bq1, bRq, bR3s, bA1, bA2, bR4s, bL1, bL2, beJ2, blog1m, cLog2UB, cLog2LB, cLog3UB, cLog3LB, cJlogLB, cJlog2UB])
  rcases lt_or_ge (1-β) (523/1024 : ℝ) with h23 | h23
  · exact case_II (a := (985/2048 : ℝ)) (b := (523/1024 : ℝ)) hβ0 hβ1 (by linarith [h23, show (((523/1024 : ℝ)) ≤ (3/4:ℝ)) by norm_num]) (by linarith) (by norm_num) (by linarith) (by linarith) (by norm_num)
      (by norm_num [posF, U3F, U4IF, U4IIF, U4IIIF, boxT8, bx1, bx2, bxq, bq1, bRq, bR3s, bA1, bA2, bR4s, bL1, bL2, beJ2, blog1m, cLog2UB, cLog2LB, cLog3UB, cLog3LB, cJlogLB, cJlog2UB])
  rcases lt_or_ge (1-β) (1113/2048 : ℝ) with h24 | h24
  · exact case_II (a := (523/1024 : ℝ)) (b := (1113/2048 : ℝ)) hβ0 hβ1 (by linarith [h24, show (((1113/2048 : ℝ)) ≤ (3/4:ℝ)) by norm_num]) (by linarith) (by norm_num) (by linarith) (by linarith) (by norm_num)
      (by norm_num [posF, U3F, U4IF, U4IIF, U4IIIF, boxT8, bx1, bx2, bxq, bq1, bRq, bR3s, bA1, bA2, bR4s, bL1, bL2, beJ2, blog1m, cLog2UB, cLog2LB, cLog3UB, cLog3LB, cJlogLB, cJlog2UB])
  rcases lt_or_ge (1-β) (297/512 : ℝ) with h25 | h25
  · exact case_II (a := (1113/2048 : ℝ)) (b := (297/512 : ℝ)) hβ0 hβ1 (by linarith [h25, show (((297/512 : ℝ)) ≤ (3/4:ℝ)) by norm_num]) (by linarith) (by norm_num) (by linarith) (by linarith) (by norm_num)
      (by norm_num [posF, U3F, U4IF, U4IIF, U4IIIF, boxT8, bx1, bx2, bxq, bq1, bRq, bR3s, bA1, bA2, bR4s, bL1, bL2, beJ2, blog1m, cLog2UB, cLog2LB, cLog3UB, cLog3LB, cJlogLB, cJlog2UB])
  rcases lt_or_ge (1-β) (159/256 : ℝ) with h26 | h26
  · exact case_II (a := (297/512 : ℝ)) (b := (159/256 : ℝ)) hβ0 hβ1 (by linarith [h26, show (((159/256 : ℝ)) ≤ (3/4:ℝ)) by norm_num]) (by linarith) (by norm_num) (by linarith) (by linarith) (by norm_num)
      (by norm_num [posF, U3F, U4IF, U4IIF, U4IIIF, boxT8, bx1, bx2, bxq, bq1, bRq, bR3s, bA1, bA2, bR4s, bL1, bL2, beJ2, blog1m, cLog2UB, cLog2LB, cLog3UB, cLog3LB, cJlogLB, cJlog2UB])
  rcases lt_or_ge (1-β) (1367/2048 : ℝ) with h27 | h27
  · exact case_II (a := (159/256 : ℝ)) (b := (1367/2048 : ℝ)) hβ0 hβ1 (by linarith [h27, show (((1367/2048 : ℝ)) ≤ (3/4:ℝ)) by norm_num]) (by linarith) (by norm_num) (by linarith) (by linarith) (by norm_num)
      (by norm_num [posF, U3F, U4IF, U4IIF, U4IIIF, boxT8, bx1, bx2, bxq, bq1, bRq, bR3s, bA1, bA2, bR4s, bL1, bL2, beJ2, blog1m, cLog2UB, cLog2LB, cLog3UB, cLog3LB, cJlogLB, cJlog2UB])
  rcases lt_or_ge (1-β) (1475/2048 : ℝ) with h28 | h28
  · exact case_II (a := (1367/2048 : ℝ)) (b := (1475/2048 : ℝ)) hβ0 hβ1 (by linarith [h28, show (((1475/2048 : ℝ)) ≤ (3/4:ℝ)) by norm_num]) (by linarith) (by norm_num) (by linarith) (by linarith) (by norm_num)
      (by norm_num [posF, U3F, U4IF, U4IIF, U4IIIF, boxT8, bx1, bx2, bxq, bq1, bRq, bR3s, bA1, bA2, bR4s, bL1, bL2, beJ2, blog1m, cLog2UB, cLog2LB, cLog3UB, cLog3LB, cJlogLB, cJlog2UB])
  rcases lt_or_ge (1-β) (3/4 : ℝ) with h29 | h29
  · exact case_II (a := (1475/2048 : ℝ)) (b := (3/4 : ℝ)) hβ0 hβ1 (by linarith [h29, show (((3/4 : ℝ)) ≤ (3/4:ℝ)) by norm_num]) (by linarith) (by norm_num) (by linarith) (by linarith) (by norm_num)
      (by norm_num [posF, U3F, U4IF, U4IIF, U4IIIF, boxT8, bx1, bx2, bxq, bq1, bRq, bR3s, bA1, bA2, bR4s, bL1, bL2, beJ2, blog1m, cLog2UB, cLog2LB, cLog3UB, cLog3LB, cJlogLB, cJlog2UB])
  rcases lt_or_ge (1-β) (1:ℝ) with h30 | h30
  · exact case_III (a := (3/4 : ℝ)) (b := (1:ℝ)) hβ0 hβ1 (by linarith [h30, show (((1:ℝ)) ≤ (1:ℝ)) by norm_num]) (by norm_num) (by linarith) (by linarith) (by norm_num)
      (by norm_num [posF, U3F, U4IF, U4IIF, U4IIIF, boxT8, bx1, bx2, bxq, bq1, bRq, bR3s, bA1, bA2, bR4s, bL1, bL2, beJ2, blog1m, cLog2UB, cLog2LB, cLog3UB, cLog3LB, cJlogLB, cJlog2UB])
  · exfalso; linarith

end