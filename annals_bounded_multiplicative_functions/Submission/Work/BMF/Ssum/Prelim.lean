import Mathlib
import Submission.Work.BMF.vkford51_defs
import Submission.Work.BMF.Ssum.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Ford's (5.1)-(5.2): the pieces of the single-term comparison

Supporting lemmas for `Work.BMF.Ssum.norm_ab_sum_sub_Usum_le`, which compares the double sum
`∑_{a ≤ M₁} ∑_{b ≤ M₂} (z + ab)^{-it}` with Ford's smoothed exponential sum `Usum` at `z = n + u`
(K. Ford, *Vinogradov's integral and bounds for the Riemann zeta function*, Proc. LMS 85 (2002),
(5.1)-(5.2)).

Contents:
* the sharp Taylor remainder `taylog_log_remainder` for the degree-`k` Taylor polynomial of
  `log (1 + x)` on `[0,1]` (Ford's (5.1)), proved by the monotonicity of the two remainders;
* `Uphase_two_pi` : `2π · Uphase k t z c = -t · taylog k (c/z)`, i.e. Ford's phase
  `∑_{j≤k} γ_j c^j` is exactly the truncated expansion of `-(t/2π) log (1 + c/z)`;
* `norm_cpow_sub_eZ_mul_le`: the single-term comparison
  `‖(z+c)^{-it} - eZ (logphase t z) · eZ (Uphase k t z c)‖ ≤ t (c/z)^{k+1}/(k+1)`;
* the elementary sum bounds used to reach the final closed form.
-/

namespace Work.BMF.Ssum

open Finset
open scoped BigOperators

noncomputable section

/-! ## The sharp Taylor remainder for `log (1 + x)` -/

lemma taylog_zero (k : ℕ) : taylog k 0 = 0 := by
  rw [taylog]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [zero_pow (by omega : i + 1 ≠ 0)]
  simp

lemma hasDerivAt_taylog (k : ℕ) (y : ℝ) :
    HasDerivAt (taylog k) (∑ i ∈ Finset.range k, (-y) ^ i) y := by
  change HasDerivAt
    (fun z : ℝ => ∑ i ∈ Finset.range k, (-1 : ℝ) ^ i * z ^ (i + 1) / ((i : ℝ) + 1))
    (∑ i ∈ Finset.range k, (-y) ^ i) y
  have h : HasDerivAt
      (fun z : ℝ => ∑ i ∈ Finset.range k, (-1 : ℝ) ^ i * z ^ (i + 1) / ((i : ℝ) + 1))
      (∑ i ∈ Finset.range k, (-1 : ℝ) ^ i * (((i : ℝ) + 1) * y ^ i) / ((i : ℝ) + 1)) y := by
    refine HasDerivAt.fun_sum fun i hi => ?_
    have h1 : HasDerivAt (fun z : ℝ => z ^ (i + 1)) (((i : ℝ) + 1) * y ^ i) y := by
      simpa using hasDerivAt_pow (i + 1) y
    have h2 : HasDerivAt (fun z : ℝ => (-1 : ℝ) ^ i * z ^ (i + 1))
        ((-1 : ℝ) ^ i * (((i : ℝ) + 1) * y ^ i)) y :=
      h1.const_mul ((-1 : ℝ) ^ i)
    exact h2.div_const ((i : ℝ) + 1)
  refine h.congr_deriv ?_
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [show (-y) ^ i = (-1 : ℝ) ^ i * y ^ i from by rw [← neg_one_mul, mul_pow]]
  rw [mul_div_assoc, mul_div_cancel_left₀ (y ^ i) (by positivity : ((i : ℝ) + 1) ≠ 0)]

/-- The derivative of `log (1 + y) - taylog k y` is `(-1)^k y^k / (1+y)`. -/
lemma hasDerivAt_log_sub_taylog (k : ℕ) (y : ℝ) (hy : y ≠ -1) :
    HasDerivAt (fun z : ℝ => Real.log (1 + z) - taylog k z)
      ((-1 : ℝ) ^ k * y ^ k / (1 + y)) y := by
  have hne : (1 : ℝ) + y ≠ 0 := by intro h; exact hy (by linarith)
  have hlog : HasDerivAt (fun z : ℝ => Real.log (1 + z)) (1 / (1 + y)) y := by
    have h1 : HasDerivAt (fun z : ℝ => 1 + z) 1 y := by
      simpa using (hasDerivAt_id y).const_add 1
    simpa using (h1.log hne)
  refine ((hlog.sub (hasDerivAt_taylog k y))).congr_deriv ?_
  have hyn : (-y) ≠ 1 := by intro h; exact hy (by linarith)
  have hgeom : (∑ i ∈ Finset.range k, (-y) ^ i) = (1 - (-y) ^ k) / (1 + y) := by
    rw [geom_sum_eq hyn k, show (-y) - 1 = -(1 + y) by ring, div_neg]
    ring
  rw [hgeom, show (1 : ℝ) - (-y) ^ k = 1 - (-1 : ℝ) ^ k * y ^ k from by
    rw [show (-y) ^ k = ((-1 : ℝ) * y) ^ k from by rw [neg_one_mul], mul_pow]]
  ring

/-- **Ford's (5.1)**: for `0 ≤ x ≤ 1`, the degree-`k` Taylor polynomial of `log (1+x)` differs
from `log (1+x)` by at most `x^{k+1}/(k+1)`.  Proof: `F = (-1)^k (log (1+y) - taylog k y)` is
increasing (derivative `y^k/(1+y) ≥ 0`) and `G = F - y^{k+1}/(k+1)` is decreasing. -/
lemma taylog_log_remainder (k : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |Real.log (1 + x) - taylog k x| ≤ x ^ (k + 1) / ((k : ℝ) + 1) := by
  set F : ℝ → ℝ := fun y => (-1 : ℝ) ^ k * (Real.log (1 + y) - taylog k y) with hF
  set G : ℝ → ℝ := fun y => F y - y ^ (k + 1) / ((k : ℝ) + 1) with hG
  have hFderiv : ∀ y : ℝ, y ≠ -1 → HasDerivAt F (y ^ k / (1 + y)) y := by
    intro y hy
    have h := (hasDerivAt_log_sub_taylog k y hy).const_mul ((-1 : ℝ) ^ k)
    refine h.congr_deriv ?_
    have hk : ((-1 : ℝ) ^ k * (-1 : ℝ) ^ k) = 1 := by
      rw [← mul_pow, show (-1 : ℝ) * (-1) = 1 by norm_num, one_pow]
    calc (-1 : ℝ) ^ k * ((-1 : ℝ) ^ k * y ^ k / (1 + y))
        = ((-1 : ℝ) ^ k * (-1 : ℝ) ^ k) * y ^ k / (1 + y) := by ring
      _ = y ^ k / (1 + y) := by rw [hk, one_mul]
  have hGderiv : ∀ y : ℝ, y ≠ -1 → HasDerivAt G (-(y ^ (k + 1) / (1 + y))) y := by
    intro y hy
    have hne : (1 : ℝ) + y ≠ 0 := by intro h; exact hy (by linarith)
    have h1 := hFderiv y hy
    have h2 : HasDerivAt (fun z : ℝ => z ^ (k + 1) / ((k : ℝ) + 1)) (y ^ k) y := by
      have h3 : HasDerivAt (fun z : ℝ => z ^ (k + 1)) (((k : ℝ) + 1) * y ^ k) y := by
        simpa using hasDerivAt_pow (k + 1) y
      have h4 := h3.div_const ((k : ℝ) + 1)
      rwa [mul_div_cancel_left₀ _ (by positivity : ((k : ℝ) + 1) ≠ 0)] at h4
    have h5 := h1.sub h2
    refine h5.congr_deriv ?_
    field_simp
    ring
  have hFmono : MonotoneOn F (Set.Icc 0 1) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (D := Set.Icc 0 1)
      (f' := fun y : ℝ => y ^ k / (1 + y)) (convex_Icc 0 1) ?_ ?_ ?_
    · intro y hy
      exact ((hFderiv y (by have := hy.1; linarith)).continuousAt).continuousWithinAt
    · intro y hy
      exact (hFderiv y (by have h := (interior_subset hy).1; linarith)).hasDerivWithinAt
    · intro y hy
      have hy' : y ∈ Set.Ioo (0 : ℝ) 1 := by simpa [interior_Icc] using hy
      have hy0 : 0 < y := hy'.1
      positivity
  have hGanti : AntitoneOn G (Set.Icc 0 1) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (D := Set.Icc 0 1)
      (f' := fun y : ℝ => -(y ^ (k + 1) / (1 + y))) (convex_Icc 0 1) ?_ ?_ ?_
    · intro y hy
      exact ((hGderiv y (by have := hy.1; linarith)).continuousAt).continuousWithinAt
    · intro y hy
      exact (hGderiv y (by have h := (interior_subset hy).1; linarith)).hasDerivWithinAt
    · intro y hy
      have hy' : y ∈ Set.Ioo (0 : ℝ) 1 := by simpa [interior_Icc] using hy
      have hy0 : 0 < y := hy'.1
      have hpos : 0 ≤ y ^ (k + 1) / (1 + y) := by positivity
      linarith
  have hxmem : x ∈ Set.Icc (0 : ℝ) 1 := ⟨hx0, hx1⟩
  have hzero : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
  have hF0 : F 0 = 0 := by simp [hF, taylog_zero]
  have hFge : 0 ≤ F x := by
    have h := hFmono hzero hxmem hx0
    rwa [hF0] at h
  have hGx : G x ≤ 0 := by
    have h := hGanti hzero hxmem hx0
    have h0 : G 0 = 0 := by
      simp [hG, hF0, zero_pow (by omega : k + 1 ≠ 0)]
    rwa [h0] at h
  have hbound : F x ≤ x ^ (k + 1) / ((k : ℝ) + 1) := by
    rw [hG] at hGx
    linarith
  have habs : |F x| ≤ x ^ (k + 1) / ((k : ℝ) + 1) := by
    rw [abs_of_nonneg hFge]
    exact hbound
  have hval : F x = (-1 : ℝ) ^ k * (Real.log (1 + x) - taylog k x) := rfl
  have hfin : |Real.log (1 + x) - taylog k x| = |F x| := by
    rw [hval, abs_mul, show |(-1 : ℝ) ^ k| = 1 by
      rw [abs_pow, show |(-1 : ℝ)| = 1 by norm_num, one_pow], one_mul]
  rw [hfin]
  exact habs

/-! ## The phase identity -/

/-- Ford's phase is the truncated expansion of `-(t/2π) log (1 + c/z)`:
`2π · Uphase k t z c = -t · taylog k (c/z)`. -/
lemma Uphase_two_pi (k : ℕ) (t z c : ℝ) (hz : 0 < z) :
    2 * Real.pi * Uphase k t z c = -t * taylog k (c / z) := by
  have hz' : z ≠ 0 := hz.ne'
  have h1 : Uphase k t z c
      = ∑ i ∈ Finset.range k, gam (i + 1) t z * c ^ (i + 1) := by
    rw [Uphase]
    exact Fin.sum_univ_eq_sum_range (fun i => gam (i + 1) t z * c ^ (i + 1)) k
  have h2 : taylog k (c / z)
      = ∑ i ∈ Finset.range k, (-1 : ℝ) ^ i * (c / z) ^ (i + 1) / ((i : ℝ) + 1) := by
    rw [taylog]
  have h3 : 2 * Real.pi * (∑ i ∈ Finset.range k, gam (i + 1) t z * c ^ (i + 1))
      = ∑ i ∈ Finset.range k, 2 * Real.pi * (gam (i + 1) t z * c ^ (i + 1)) :=
    Finset.mul_sum _ _ _
  have h4 : -t * (∑ i ∈ Finset.range k, (-1 : ℝ) ^ i * (c / z) ^ (i + 1) / ((i : ℝ) + 1))
      = ∑ i ∈ Finset.range k, -t * ((-1 : ℝ) ^ i * (c / z) ^ (i + 1) / ((i : ℝ) + 1)) :=
    Finset.mul_sum _ _ _
  have key : ∀ i ∈ Finset.range k,
      2 * Real.pi * (gam (i + 1) t z * c ^ (i + 1))
        = -t * ((-1 : ℝ) ^ i * (c / z) ^ (i + 1) / ((i : ℝ) + 1)) := by
    intro i hi
    rw [gam, div_pow]
    field_simp
    rw [show (-1 : ℝ) ^ (i + 1) = -((-1 : ℝ) ^ i) from by rw [pow_succ]; ring]
    push_cast
    ring
  rw [h1, h2, h3, h4]
  exact Finset.sum_congr rfl key

/-! ## The single-term comparison -/

/-- `eZ u = exp (I · 2πu)`. -/
lemma eZ_eq_exp_I (u : ℝ) :
    eZ u = Complex.exp (Complex.I * ((2 * Real.pi * u : ℝ) : ℂ)) := by
  rw [eZ]
  congr 1
  push_cast
  ring

/-- `exp (-(It) L) = exp (I · (-(tL)))`. -/
lemma exp_neg_I_mul_eq (t L : ℝ) :
    Complex.exp (-(Complex.I * (t : ℂ)) * ((L : ℝ) : ℂ))
      = Complex.exp (Complex.I * ((-(t * L) : ℝ) : ℂ)) := by
  congr 1
  push_cast
  ring

/-- `‖exp (I a) - exp (I b)‖ ≤ |a - b|` for real `a`, `b`. -/
lemma norm_exp_I_sub_le (a b : ℝ) :
    ‖Complex.exp (Complex.I * ((a : ℝ) : ℂ))
        - Complex.exp (Complex.I * ((b : ℝ) : ℂ))‖ ≤ |a - b| := by
  have hcast : Complex.exp (Complex.I * ((a - b : ℝ) : ℂ))
      = Complex.exp (Complex.I * (a : ℂ) - Complex.I * (b : ℂ)) := by
    congr 1
    push_cast
    ring
  have h : Complex.exp (Complex.I * (a : ℂ)) - Complex.exp (Complex.I * (b : ℂ))
      = Complex.exp (Complex.I * (b : ℂ))
          * (Complex.exp (Complex.I * ((a - b : ℝ) : ℂ)) - 1) := by
    rw [hcast, mul_sub, mul_one, ← Complex.exp_add]
    congr 1
    ring_nf
  rw [h, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
  calc ‖Complex.exp (Complex.I * ((a - b : ℝ) : ℂ)) - 1‖ ≤ ‖(a - b : ℝ)‖ :=
        Real.norm_exp_I_mul_ofReal_sub_one_le
    _ = |a - b| := Real.norm_eq_abs _

/-- **Ford's (5.2), one term**: for `z > 0`, `0 ≤ c ≤ z`,
`‖(z+c)^{-it} - eZ (logphase t z) · eZ (Uphase k t z c)‖ ≤ t (c/z)^{k+1}/((k:ℝ)+1)`,
given the Taylor remainder (Ford's (5.1)) and the phase identity for `Uphase`. -/
lemma norm_cpow_sub_eZ_mul_le (k : ℕ) (t : ℝ) (ht : 0 ≤ t) (z c : ℝ) (hz : 0 < z) (hc : 0 ≤ c)
    (hcz : c ≤ z)
    (hTay : |Real.log (1 + c / z) - taylog k (c / z)| ≤ (c / z) ^ (k + 1) / ((k : ℝ) + 1))
    (hPhase : 2 * Real.pi * Uphase k t z c = -t * taylog k (c / z)) :
    ‖(((z + c : ℝ) : ℂ)) ^ (-(Complex.I * (t : ℂ))) - eZ (logphase t z) * eZ (Uphase k t z c)‖
      ≤ t * (c / z) ^ (k + 1) / ((k : ℝ) + 1) := by
  have hz' : z ≠ 0 := hz.ne'
  have hzc_pos : (0 : ℝ) < z + c := by linarith
  have hx0 : (0 : ℝ) ≤ c / z := div_nonneg hc hz.le
  have hx1 : c / z ≤ 1 := (div_le_one hz).mpr hcz
  have h1x : (0 : ℝ) < 1 + c / z := by linarith
  have hreal : 2 * Real.pi * logphase t z = -(t * Real.log z) := by
    rw [logphase]
    field_simp
  have heZ : eZ (logphase t z)
      = Complex.exp (-(Complex.I * (t : ℂ)) * ((Real.log z : ℝ) : ℂ)) := by
    rw [eZ_eq_exp_I, hreal]
    congr 1
    push_cast
    ring
  have hF : ((z + c : ℝ) : ℂ) ^ (-(Complex.I * (t : ℂ)))
      = eZ (logphase t z)
          * Complex.exp (-(Complex.I * (t : ℂ)) * ((Real.log (1 + c / z) : ℝ) : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hzc_pos.ne'),
      ← Complex.ofReal_log hzc_pos.le]
    have hlog : Real.log (z + c) = Real.log z + Real.log (1 + c / z) := by
      have h : z + c = z * (1 + c / z) := by field_simp
      rw [h, Real.log_mul hz' h1x.ne']
    rw [hlog, Complex.ofReal_add, heZ, ← Complex.exp_add]
    congr 1
    ring_nf
  have hdiff : ((z + c : ℝ) : ℂ) ^ (-(Complex.I * (t : ℂ))) - eZ (logphase t z) * eZ (Uphase k t z c)
      = eZ (logphase t z)
          * (Complex.exp (-(Complex.I * (t : ℂ)) * ((Real.log (1 + c / z) : ℝ) : ℂ))
              - Complex.exp (Complex.I * ((2 * Real.pi * Uphase k t z c : ℝ) : ℂ))) := by
    have hQ : eZ (Uphase k t z c)
        = Complex.exp (Complex.I * ((2 * Real.pi * Uphase k t z c : ℝ) : ℂ)) :=
      eZ_eq_exp_I _
    rw [hF, hQ]
    ring_nf
  rw [hdiff, norm_mul, eZ_norm, one_mul]
  calc ‖Complex.exp (-(Complex.I * (t : ℂ)) * ((Real.log (1 + c / z) : ℝ) : ℂ))
        - Complex.exp (Complex.I * ((2 * Real.pi * Uphase k t z c : ℝ) : ℂ))‖
      ≤ |(-(t * Real.log (1 + c / z))) - 2 * Real.pi * Uphase k t z c| := by
        rw [exp_neg_I_mul_eq]
        exact norm_exp_I_sub_le _ _
    _ = t * |Real.log (1 + c / z) - taylog k (c / z)| := by
        rw [hPhase,
          show -(t * Real.log (1 + c / z)) - -t * taylog k (c / z)
              = -(t * (Real.log (1 + c / z) - taylog k (c / z))) by ring,
          abs_neg, abs_mul, abs_of_nonneg ht]
    _ ≤ t * ((c / z) ^ (k + 1) / ((k : ℝ) + 1)) := mul_le_mul_of_nonneg_left hTay ht
    _ = t * (c / z) ^ (k + 1) / ((k : ℝ) + 1) := by ring

/-! ## Sum bounds -/

/-- `∑_{a ≤ M₁} ∑_{b ≤ M₂} (ab)^{k+1} ≤ M₁^{k+2} M₂^{k+2}`. -/
lemma sum_Icc_mul_pow_le (k M₁ M₂ : ℕ) :
    (∑ a ∈ Finset.Icc 1 M₁, ∑ b ∈ Finset.Icc 1 M₂, ((a : ℝ) * (b : ℝ)) ^ (k + 1))
      ≤ (M₁ : ℝ) ^ (k + 2) * (M₂ : ℝ) ^ (k + 2) := by
  rw [Finset.sum_congr rfl
    (fun a _ => Finset.sum_congr rfl (fun b _ => by rw [mul_pow]))]
  rw [← Finset.sum_mul_sum]
  have h₁ : (∑ a ∈ Finset.Icc 1 M₁, (a : ℝ) ^ (k + 1)) ≤ (M₁ : ℝ) ^ (k + 2) := by
    calc (∑ a ∈ Finset.Icc 1 M₁, (a : ℝ) ^ (k + 1))
        ≤ ∑ _a ∈ Finset.Icc 1 M₁, (M₁ : ℝ) ^ (k + 1) := by
          refine Finset.sum_le_sum fun a ha => ?_
          exact pow_le_pow_left₀ (Nat.cast_nonneg a)
            (by exact_mod_cast (Finset.mem_Icc.mp ha).2) _
      _ = (M₁ : ℝ) * (M₁ : ℝ) ^ (k + 1) := by
          rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]
          simp
      _ = (M₁ : ℝ) ^ (k + 2) := by
          rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
          ring
  have h₂ : (∑ b ∈ Finset.Icc 1 M₂, (b : ℝ) ^ (k + 1)) ≤ (M₂ : ℝ) ^ (k + 2) := by
    calc (∑ b ∈ Finset.Icc 1 M₂, (b : ℝ) ^ (k + 1))
        ≤ ∑ _b ∈ Finset.Icc 1 M₂, (M₂ : ℝ) ^ (k + 1) := by
          refine Finset.sum_le_sum fun b hb => ?_
          exact pow_le_pow_left₀ (Nat.cast_nonneg b)
            (by exact_mod_cast (Finset.mem_Icc.mp hb).2) _
      _ = (M₂ : ℝ) * (M₂ : ℝ) ^ (k + 1) := by
          rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]
          simp
      _ = (M₂ : ℝ) ^ (k + 2) := by
          rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
          ring
  exact mul_le_mul h₁ h₂ (Finset.sum_nonneg fun b _ => by positivity) (by positivity)

/-- Triangle inequality reduction for double sums. -/
lemma norm_double_sum_sub_le (F G : ℕ → ℕ → ℂ) (M₁ M₂ : ℕ) :
    ‖∑ a ∈ Finset.Icc 1 M₁, ∑ b ∈ Finset.Icc 1 M₂, F a b‖
      ≤ ‖∑ a ∈ Finset.Icc 1 M₁, ∑ b ∈ Finset.Icc 1 M₂, G a b‖
        + ∑ a ∈ Finset.Icc 1 M₁, ∑ b ∈ Finset.Icc 1 M₂, ‖F a b - G a b‖ := by
  have hsub : (∑ a ∈ Finset.Icc 1 M₁, ∑ b ∈ Finset.Icc 1 M₂, F a b)
      - (∑ a ∈ Finset.Icc 1 M₁, ∑ b ∈ Finset.Icc 1 M₂, G a b)
      = ∑ a ∈ Finset.Icc 1 M₁, ∑ b ∈ Finset.Icc 1 M₂, (F a b - G a b) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a ha => (Finset.sum_sub_distrib (F a) (G a)).symm
  have h1 : ‖∑ a ∈ Finset.Icc 1 M₁, ∑ b ∈ Finset.Icc 1 M₂, (F a b - G a b)‖
      ≤ ∑ a ∈ Finset.Icc 1 M₁, ∑ b ∈ Finset.Icc 1 M₂, ‖F a b - G a b‖ :=
    le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun a ha => norm_sum_le _ _)
  calc ‖∑ a ∈ Finset.Icc 1 M₁, ∑ b ∈ Finset.Icc 1 M₂, F a b‖
      = ‖(∑ a ∈ Finset.Icc 1 M₁, ∑ b ∈ Finset.Icc 1 M₂, G a b)
          + ∑ a ∈ Finset.Icc 1 M₁, ∑ b ∈ Finset.Icc 1 M₂, (F a b - G a b)‖ := by
        congr 1
        rw [← hsub]
        ring
    _ ≤ ‖∑ a ∈ Finset.Icc 1 M₁, ∑ b ∈ Finset.Icc 1 M₂, G a b‖
          + ‖∑ a ∈ Finset.Icc 1 M₁, ∑ b ∈ Finset.Icc 1 M₂, (F a b - G a b)‖ :=
        norm_add_le _ _
    _ ≤ _ := add_le_add le_rfl h1

end

end Work.BMF.Ssum
