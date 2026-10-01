import Mathlib
import Submission.Work.ZeroFreeTables.t23Defs
import Submission.Work.ZeroFreeTables.t23Gclosed
import Submission.Work.ZeroFreeTables.tf72_exp_taylor_upper
import Submission.Work.ZeroFreeTables.testFn72_defs
import Submission.Work.ZeroFreeTables.testFn7_2
import Submission.Work.ZeroFreeTables.HBProps
import Submission.Work.ZeroFreeTables.Tables
import Submission.Work.ZeroFreeTables.TestFn_F_eq_integral
import Submission.Work.ZeroFreeTables.tf72Fc_zero_re
import Submission.Work.ZeroFreeTables.T10Defs

open scoped BigOperators
open MeasureTheory

noncomputable section
namespace Work.ZeroFreeTables

/-!
# The Table 10 row certificates for HB Lemma 6.2

This file proves `table10_62_cert`: for every row `(a,b)` of Heath-Brown's Table 10
(`hbTable10`) the five-term expression of HB Lemma 6.2,

  `F(−λ₁) − F(0) − F(λ₂−λ₁) + f(0)·(3/8 + 3·10⁻⁶)`,

with `F` the Laplace transform of HB Lemma 7.2's optimal test function `tf72T λ`, is
*negative* on the whole region `λ₁ ≤ a`, `λ₂ ∈ [λ₁, b]` for a suitable scale `λ > 0`
(depending on the row).

The analysis is carried out in HB's normalised variables
`hb72g u = (2−u)³(4+6u+u²)`, `hb72G x = ∫₀² hb72g u e^{xu} du`, related to the test
function's transform by `F_λ(z) = hb72G(−z/λ)/30` (the substitution `u = λt`):
with `λ₁ = u`, `λ₂ = v`, `x = u/λ`, `y = (u−v)/λ`,

  `F(−u) − F(0) − F(v−u) + f(0)c = (1/30)(G x − G 0 − G y) + (16λ/15)c`.

* **Region reduction** (`tf72_region`): the pointwise bound
  `e^{ut} − e^{(u−v)t} ≤ e^{at} − e^{(a−b)t}` (valid for `t ≥ 0`, `u ≤ a`, `u ≤ v ≤ b`,
  `b ≥ 0`) gives `F(−u) − F(v−u) ≤ F(−a) − F(b−a)`: the region's supremum sits at the
  corner `(u,v) = (a,b)`.
* **Upper bound at the corner** (`hb72G_le_of_exp_le`, `hb72G_closed`): for `x > 0`,
  `G x = (120 e^{2x}(x−1)² − 32x⁵ + 80x³ + 120x² − 120)/x⁶`, so an upper bound for
  `e^{2x}` bounds `G x` above.
* **Lower bound at `y ≤ 0`** (`hb72G_y_lower`): the alternating Taylor bound
  `Σ_{k<6} t^k/k! ≤ e^t` (`t ≤ 0`) integrated against `hb72g ≥ 0` gives
  `Ty6 y = Σ_{k<6} (∫₀²u^k hb72g) y^k/k! ≤ G y`.
* The remaining content of each row is a rational inequality, discharged by `norm_num`.
-/

/-! ## The Taylor remainder of `exp` and the alternating lower bound -/

/-- The Taylor remainder `e^t - Σ_{k<m} t^k/k!` of `Real.exp` at order `m`. -/
def TRem (m : ℕ) (t : ℝ) : ℝ := Real.exp t - ∑ k ∈ Finset.range m, t ^ k / (k.factorial : ℝ)

lemma TRem_succ_zero (m : ℕ) : TRem (m+1) 0 = 0 := by
  unfold TRem
  rw [Real.exp_zero, Finset.sum_range_succ']
  simp

lemma TRem_hasDerivAt (m : ℕ) (x : ℝ) : HasDerivAt (TRem (m+1)) (TRem m x) x := by
  have hterm : ∀ k ∈ Finset.range (m+1),
      HasDerivAt (fun t : ℝ => t ^ k / (k.factorial : ℝ))
        ((k:ℝ) * x ^ (k-1) / (k.factorial : ℝ)) x := by
    intro k _
    exact (hasDerivAt_pow k x).div_const _
  have hsum0 := HasDerivAt.sum hterm
  have hsum : HasDerivAt
      (fun t : ℝ => ∑ i ∈ Finset.range (m+1), t ^ i / (i.factorial : ℝ))
      (∑ i ∈ Finset.range (m+1), (i:ℝ) * x ^ (i-1) / (i.factorial : ℝ)) x := by
    rw [show (∑ i ∈ Finset.range (m+1), (fun t : ℝ => t ^ i / (i.factorial : ℝ)))
        = (fun t : ℝ => ∑ i ∈ Finset.range (m+1), t ^ i / (i.factorial : ℝ)) from by
          funext t; simp [Finset.sum_apply]] at hsum0
    exact hsum0
  have hkey : (∑ k ∈ Finset.range (m+1), (k:ℝ) * x ^ (k-1) / (k.factorial : ℝ))
      = ∑ k ∈ Finset.range m, x ^ k / (k.factorial : ℝ) := by
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, zero_mul, zero_div, add_zero]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Nat.add_sub_cancel, Nat.factorial_succ]
    push_cast
    field_simp
  rw [hkey] at hsum
  have h2 : HasDerivAt
      (fun t : ℝ => Real.exp t - ∑ i ∈ Finset.range (m+1), t ^ i / (i.factorial : ℝ))
      (Real.exp x - ∑ i ∈ Finset.range m, x ^ i / (i.factorial : ℝ)) x :=
    (Real.hasDerivAt_exp x).sub hsum
  rw [show (fun t : ℝ => Real.exp t - ∑ i ∈ Finset.range (m+1), t ^ i / (i.factorial : ℝ))
        = TRem (m+1) from rfl,
      show (Real.exp x - ∑ i ∈ Finset.range m, x ^ i / (i.factorial : ℝ)) = TRem m x from rfl]
    at h2
  exact h2

lemma TRem_succ_eq_integral (m : ℕ) (t : ℝ) : TRem (m+1) t = ∫ u in (0:ℝ)..t, TRem m u := by
  have hcont : Continuous (TRem m) := by
    unfold TRem
    exact Real.continuous_exp.sub (continuous_finsetSum _ (fun k _ => by fun_prop))
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => TRem_hasDerivAt m x)
    (hcont.intervalIntegrable 0 t)
  rw [h, TRem_succ_zero m]
  ring

/-- The sign pattern of the Taylor remainder: non-negative on the positive axis, and
of sign `(-1)^m` on the negative axis. -/
lemma TRem_sign (m : ℕ) : (∀ t : ℝ, 0 ≤ t → 0 ≤ TRem m t) ∧
    (∀ t : ℝ, t ≤ 0 → 0 ≤ (-1:ℝ)^m * TRem m t) := by
  induction m with
  | zero =>
      refine ⟨fun t _ => ?_, fun t _ => ?_⟩
      · simpa [TRem] using (Real.exp_pos t).le
      · simpa [TRem] using (Real.exp_pos t).le
  | succ m ih =>
      obtain ⟨hA, hB⟩ := ih
      refine ⟨fun t ht => ?_, fun t ht => ?_⟩
      · rw [TRem_succ_eq_integral]
        exact intervalIntegral.integral_nonneg ht (fun u hu => hA u hu.1)
      · rw [TRem_succ_eq_integral, intervalIntegral.integral_symm t (0:ℝ)]
        have h1 : (0:ℝ) ≤ ∫ u in t..0, (-1:ℝ)^m * TRem m u :=
          intervalIntegral.integral_nonneg ht (fun u hu => hB u hu.2)
        rw [intervalIntegral.integral_const_mul] at h1
        have hpow : (-1:ℝ)^(m+1) = -((-1:ℝ)^m) := by rw [pow_succ]; ring
        rw [hpow]
        have : -((-1:ℝ)^m) * (-(∫ u in t..0, TRem m u))
            = (-1:ℝ)^m * ∫ u in t..0, TRem m u := by ring
        rw [this]
        exact h1

/-- **Alternating Taylor bound for `Real.exp`.**  For `t ≤ 0` and even `m`, the partial
sum `Σ_{k<m} t^k/k!` lies below `e^t` (its tail is an alternating series with the sign of
the first omitted term). -/
theorem exp_taylor_alt_lower : ∀ {t : ℝ}, t ≤ 0 → ∀ {m : ℕ}, Even m →
    ∑ k ∈ Finset.range m, t ^ k / ((k.factorial : ℕ) : ℝ) ≤ Real.exp t := by
  intro t ht m hm
  have h := (TRem_sign m).2 t ht
  rw [hm.neg_one_pow] at h
  simp only [one_mul] at h
  unfold TRem at h
  linarith

/-! ## The moments `GA k = ∫₀² u^k hb72g u du` -/

lemma GA_eq' (k : ℕ) : GA k = ∫ t in (0:ℝ)..2, hb72g t * t ^ k := by
  rw [GA_eq k]
  exact intervalIntegral.integral_congr (fun t _ => by rw [mul_comm])

lemma hb72g_eq_poly (u : ℝ) : hb72g u = (2 - u)^3 * (4 + 6*u + u^2) := by
  unfold hb72g; ring

lemma hb72g_nonneg_Icc : ∀ u ∈ Set.Icc (0:ℝ) 2, 0 ≤ hb72g u := by
  intro u hu
  rw [hb72g_eq_poly]
  have h1 : (0:ℝ) ≤ 2 - u := by linarith [hu.2]
  have h2 : (0:ℝ) ≤ 4 + 6*u + u^2 := by nlinarith [sq_nonneg u, hu.1]
  positivity

lemma hb72G_zero : hb72G 0 = 80/3 := by
  have h1 : (∫ t in (0:ℝ)..2, hb72g t) = 80/3 := by
    have h2 : (∫ t in (0:ℝ)..2, t^0 * hb72g t) = 80/3 := by rw [← GA_eq 0, GA_zero]
    have h3 : (∫ t in (0:ℝ)..2, hb72g t) = ∫ t in (0:ℝ)..2, t^0 * hb72g t :=
      intervalIntegral.integral_congr (fun t _ => by rw [pow_zero, one_mul])
    rw [h3]; exact h2
  rw [hb72G]
  rw [intervalIntegral.integral_congr (fun u _ => by rw [zero_mul, Real.exp_zero, mul_one])]
  exact h1

/-- **Lower bound for `hb72G` at non-positive arguments** via the alternating Taylor
expansion of `e^{yu}`, `u ∈ [0,2]`, integrated against the non-negative density `hb72g`. -/
lemma hb72G_y_lower {y : ℝ} (hy : y ≤ 0) : Ty6 y ≤ hb72G y := by
  have hInt : (∫ t in (0:ℝ)..2,
        hb72g t * (∑ k ∈ Finset.range 6, (y*t)^k / (k.factorial:ℝ)))
      = ∑ k ∈ Finset.range 6, GA k * y^k / (k.factorial:ℝ) := by
    calc (∫ t in (0:ℝ)..2, hb72g t * (∑ k ∈ Finset.range 6, (y*t)^k / (k.factorial:ℝ)))
        = ∫ t in (0:ℝ)..2, ∑ k ∈ Finset.range 6,
            hb72g t * ((y*t)^k / (k.factorial:ℝ)) := by
          refine intervalIntegral.integral_congr (fun t _ => ?_)
          rw [Finset.mul_sum]
      _ = ∑ k ∈ Finset.range 6,
            ∫ t in (0:ℝ)..2, hb72g t * ((y*t)^k / (k.factorial:ℝ)) := by
          rw [intervalIntegral.integral_finsetSum]
          intro k _
          exact (by unfold hb72g; fun_prop : Continuous
            (fun t : ℝ => hb72g t * ((y*t)^k / (k.factorial:ℝ)))).intervalIntegrable 0 2
      _ = ∑ k ∈ Finset.range 6, GA k * y^k / (k.factorial:ℝ) := by
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [show (fun t : ℝ => hb72g t * ((y*t)^k / (k.factorial:ℝ)))
              = (fun t : ℝ => (y^k / (k.factorial:ℝ)) * (hb72g t * t^k)) from by
                funext t; rw [mul_pow]; ring]
          rw [intervalIntegral.integral_const_mul, ← GA_eq' k]
          ring
  have hcont1 : Continuous
      (fun t : ℝ => hb72g t * (∑ k ∈ Finset.range 6, (y*t)^k / (k.factorial:ℝ))) := by
    refine Continuous.mul ?_ ?_
    · unfold hb72g; fun_prop
    · exact continuous_finsetSum _ (fun k _ => by fun_prop)
  have hcont2 : Continuous (fun t : ℝ => hb72g t * Real.exp (y*t)) := by
    refine Continuous.mul ?_ ?_
    · unfold hb72g; fun_prop
    · fun_prop
  rw [Ty6, ← hInt, hb72G]
  refine intervalIntegral.integral_mono_on (by norm_num)
    (hcont1.intervalIntegrable 0 2) (hcont2.intervalIntegrable 0 2) (fun t ht => ?_)
  exact mul_le_mul_of_nonneg_left
    (exp_taylor_alt_lower (mul_nonpos_of_nonpos_of_nonneg hy ht.1) (show Even 6 from ⟨3, rfl⟩))
    (hb72g_nonneg_Icc t ht)

/-- **Upper bound for `hb72G` at positive arguments** from an upper bound for `e^{2x}`. -/
lemma hb72G_le_of_exp_le {x E : ℝ} (hx : 0 < x) (hE : Real.exp (2*x) ≤ E) :
    hb72G x ≤ (120*E*(x-1)^2 - 32*x^5 + 80*x^3 + 120*x^2 - 120)/x^6 := by
  rw [hb72G_closed hx.ne']
  have hx6 : (0:ℝ) < x^6 := by positivity
  apply div_le_div_of_nonneg_right _ hx6.le
  nlinarith [sq_nonneg (x-1), hE, Real.exp_pos (2*x)]

lemma tf72F_subst' (lam z : ℝ) (hlam : 0 < lam) :
    (∫ t in (0:ℝ)..(2/lam), Real.exp (-(z * t)) * tf72f lam t) = hb72G (-z / lam) / 30 := by
  have hlamne : lam ≠ 0 := hlam.ne'
  have h2lam : (0:ℝ) < 2/lam := by positivity
  have hpoly : (∫ t in (0:ℝ)..(2/lam), Real.exp (-(z * t)) * tf72f lam t)
      = ∫ t in (0:ℝ)..(2/lam),
          (fun u : ℝ => (lam/30) * (Real.exp (((-z)/lam)*u)
            * ((2-u)^3*(4+6*u+u^2)))) (lam*t) := by
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    have ht' : t ∈ Set.Icc (0:ℝ) (2/lam) := by rwa [Set.uIcc_of_le h2lam.le] at ht
    rw [tf72f_eq_poly lam hlam t ht']
    have hzt : ((-z)/lam)*(lam*t) = -(z*t) := by field_simp
    rw [← hzt]
    ring
  rw [hpoly]
  rw [intervalIntegral.integral_comp_mul_left
      (fun u : ℝ => (lam/30) * (Real.exp (((-z)/lam)*u) * ((2-u)^3*(4+6*u+u^2)))) hlamne]
  rw [show lam * (0:ℝ) = 0 by ring, show lam * (2/lam) = 2 by field_simp, smul_eq_mul]
  rw [intervalIntegral.integral_const_mul]
  have hX : (∫ u in (0:ℝ)..2, Real.exp (((-z)/lam)*u) * ((2-u)^3*(4+6*u+u^2)))
      = ∫ u in (0:ℝ)..2, hb72g u * Real.exp (((-z)/lam)*u) := by
    refine intervalIntegral.integral_congr (fun u _ => ?_)
    rw [hb72g_eq_poly]; ring
  rw [hX, hb72G]
  have hscal : lam⁻¹ * (lam/30 * (∫ u in (0:ℝ)..2, hb72g u * Real.exp (((-z)/lam)*u)))
      = (∫ u in (0:ℝ)..2, hb72g u * Real.exp (((-z)/lam)*u))/30 := by
    field_simp
  rw [hscal]

/-! ## The `F`-translations of the normalised variables -/

lemma tf72F_eq_int (lam : ℝ) (hlam : 0 < lam) (z : ℝ) :
    (tf72T lam hlam).F z = ∫ t in (0:ℝ)..(2/lam), Real.exp (-(z*t)) * tf72f lam t := by
  rw [TestFn_F_eq_integral]
  rfl

lemma tf72F_zero (lam : ℝ) (hlam : 0 < lam) : (tf72T lam hlam).F 0 = 8/9 := by
  show (tf72Fc lam ((0:ℝ) : ℂ)).re = 8/9
  rw [show ((0:ℝ) : ℂ) = 0 from by norm_num]
  exact tf72Fc_zero_re lam hlam

lemma tf72F_neg_eq (lam : ℝ) (hlam : 0 < lam) (a : ℝ) :
    (tf72T lam hlam).F (-a) = hb72G (a/lam)/30 := by
  have h := tf72F_subst' lam (-a) hlam
  have h' : -(-a)/lam = a/lam := by ring
  rw [h'] at h
  rw [tf72F_eq_int]
  exact h

lemma tf72F_ba_eq (lam : ℝ) (hlam : 0 < lam) (a b : ℝ) :
    (tf72T lam hlam).F (b - a) = hb72G ((a-b)/lam)/30 := by
  have h := tf72F_subst' lam (b-a) hlam
  have h' : -(b-a)/lam = (a-b)/lam := by ring
  rw [h'] at h
  rw [tf72F_eq_int]
  exact h

/-! ## The region reduction -/

/-- On the region `u ≤ a`, `u ≤ v ≤ b` (`b ≥ 0`) the difference
`F(−u) − F(v−u)` is bounded by its value at the corner `(a,b)`:
`F(−u) − F(v−u) ≤ F(−a) − F(b−a)`. -/
lemma tf72_region (lam a b u v : ℝ) (hlam : 0 < lam) (hab : a ≤ b) (hb0 : 0 ≤ b)
    (hu : u ≤ a) (huv : u ≤ v) (hvb : v ≤ b) :
    (tf72T lam hlam).F (-u) - (tf72T lam hlam).F (v-u)
      ≤ (tf72T lam hlam).F (-a) - (tf72T lam hlam).F (b-a) := by
  have h2lam : (0:ℝ) < 2/lam := by positivity
  have hle : (0:ℝ) ≤ 2/lam := h2lam.le
  have hint : ∀ w : ℝ,
      IntervalIntegrable (fun t : ℝ => Real.exp (w*t) * tf72f lam t) volume (0:ℝ) (2/lam) := by
    intro w
    refine ContinuousOn.intervalIntegrable_of_Icc hle ?_
    exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn).mul
      ((tf72f_cont lam hlam).mono (fun t ht => ht.1))
  have hL : (tf72T lam hlam).F (-u) - (tf72T lam hlam).F (v-u)
      = (∫ t in (0:ℝ)..(2/lam), Real.exp (u*t) * tf72f lam t)
        - ∫ t in (0:ℝ)..(2/lam), Real.exp ((u-v)*t) * tf72f lam t := by
    rw [tf72F_eq_int lam hlam (-u), tf72F_eq_int lam hlam (v-u)]
    congr 1
    · exact intervalIntegral.integral_congr
        (fun t _ => by rw [show -(-u*t) = u*t from by ring])
    · exact intervalIntegral.integral_congr
        (fun t _ => by rw [show -((v-u)*t) = (u-v)*t from by ring])
  have hR : (tf72T lam hlam).F (-a) - (tf72T lam hlam).F (b-a)
      = (∫ t in (0:ℝ)..(2/lam), Real.exp (a*t) * tf72f lam t)
        - ∫ t in (0:ℝ)..(2/lam), Real.exp ((a-b)*t) * tf72f lam t := by
    rw [tf72F_eq_int lam hlam (-a), tf72F_eq_int lam hlam (b-a)]
    congr 1
    · exact intervalIntegral.integral_congr
        (fun t _ => by rw [show -(-a*t) = a*t from by ring])
    · exact intervalIntegral.integral_congr
        (fun t _ => by rw [show -((b-a)*t) = (a-b)*t from by ring])
  rw [hL, hR]
  rw [← intervalIntegral.integral_sub (hint u) (hint (u-v)),
      ← intervalIntegral.integral_sub (hint a) (hint (a-b))]
  refine intervalIntegral.integral_mono_on hle (hint u |>.sub (hint (u-v)))
    (hint a |>.sub (hint (a-b))) (fun t ht => ?_)
  have ht0 : (0:ℝ) ≤ t := (Set.mem_Icc.mp ht).1
  have hfnn : 0 ≤ tf72f lam t := tf72f_nonneg lam hlam t
  have key : Real.exp (u*t) - Real.exp ((u-v)*t)
      ≤ Real.exp (a*t) - Real.exp ((a-b)*t) := by
    have h1 : Real.exp ((u-v)*t) = Real.exp (u*t) * Real.exp (-(v*t)) := by
      rw [← Real.exp_add]; congr 1; ring
    have h2 : Real.exp ((a-b)*t) = Real.exp (a*t) * Real.exp (-(b*t)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [h1, h2]
    have e1 : Real.exp (-(v*t)) ≥ Real.exp (-(b*t)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have e2 : Real.exp (u*t) ≤ Real.exp (a*t) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have e3 : Real.exp (-(b*t)) ≤ 1 := by
      have := Real.exp_le_exp.mpr (show -(b*t) ≤ 0 by nlinarith)
      simpa using this
    have h5 : Real.exp (u*t) * (1 - Real.exp (-(v*t)))
        ≤ Real.exp (u*t) * (1 - Real.exp (-(b*t))) :=
      mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
    have h6 : Real.exp (u*t) * (1 - Real.exp (-(b*t)))
        ≤ Real.exp (a*t) * (1 - Real.exp (-(b*t))) :=
      mul_le_mul_of_nonneg_right e2 (by linarith)
    nlinarith [h5, h6]
  have g1 : Real.exp (u*t)*tf72f lam t - Real.exp ((u-v)*t)*tf72f lam t
      = (Real.exp (u*t) - Real.exp ((u-v)*t)) * tf72f lam t := by ring
  have g2 : Real.exp (a*t)*tf72f lam t - Real.exp ((a-b)*t)*tf72f lam t
      = (Real.exp (a*t) - Real.exp ((a-b)*t)) * tf72f lam t := by ring
  rw [g1, g2]
  exact mul_le_mul_of_nonneg_right key hfnn

/-! ## The certificate reduction -/

/-- **The certificate step.**  Given the row data `a ≤ b` (with `a,b > 0`), a scale
`λ > 0`, an upper bound `E1` for `e^{2a/λ}` and the rational inequality `hnum`, the
Lemma 6.2 expression of the row is negative on the region `λ₁ ≤ a`, `λ₂ ∈ [λ₁,b]`. -/
theorem tf72_cert_of {a b lam E1 : ℝ} (hlam : 0 < lam) (ha : 0 < a) (hab : a ≤ b)
    (hb0 : 0 ≤ b) (hE1 : Real.exp (2*(a/lam)) ≤ E1)
    (hnum : (1/30) * ((120*E1*((a/lam)-1)^2 - 32*(a/lam)^5 + 80*(a/lam)^3
                + 120*(a/lam)^2 - 120)/(a/lam)^6 - 80/3 - Ty6 ((a-b)/lam))
              + (16*lam/15)*(3*(1/8 + 1/1000000)) < 0) :
    ∀ u v : ℝ, u ≤ a → u ≤ v → v ≤ b →
      (tf72T lam hlam).F (-u) - (tf72T lam hlam).F 0 - (tf72T lam hlam).F (v-u)
        + (tf72T lam hlam).f 0 * (3*(1/8 + 1/1000000)) < 0 := by
  intro u v hu huv hvb
  have hreg := tf72_region lam a b u v hlam hab hb0 hu huv hvb
  have hFa := tf72F_neg_eq lam hlam a
  have hFba := tf72F_ba_eq lam hlam a b
  have hF0 := tf72F_zero lam hlam
  have hx : 0 < a/lam := by positivity
  have hGup := hb72G_le_of_exp_le hx hE1
  have hGly := hb72G_y_lower (show (a-b)/lam ≤ 0 by
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) hlam.le)
  change (tf72T lam hlam).F (-u) - (tf72T lam hlam).F 0 - (tf72T lam hlam).F (v-u)
      + (tf72f lam 0) * (3*(1/8 + 1/1000000)) < 0
  rw [hF0, tf72f_at_zero lam hlam]
  have h1 : (tf72T lam hlam).F (-u) - (tf72T lam hlam).F (v-u)
      ≤ hb72G (a/lam)/30 - Ty6 ((a-b)/lam)/30 := by linarith
  have h2 : hb72G (a/lam)/30 - Ty6 ((a-b)/lam)/30
      ≤ ((120*E1*((a/lam)-1)^2 - 32*(a/lam)^5 + 80*(a/lam)^3 + 120*(a/lam)^2 - 120)/(a/lam)^6
          - Ty6 ((a-b)/lam))/30 := by linarith
  have hkey : (1/30)*(80/3) = 8/9 := by norm_num
  linarith [h1, h2, hnum, hkey]

/-- Region-form numerical certificates for the Table 10 rows, for **HB Lemma 6.2**'s
five-term inequality `F(−λ₁) − F(0) − F(λ₂−λ₁) + f(0)·(3/8) ≥ 0` (the `(C3)` case, where
`HB Lemma 2.5` gives `φ = 1/4`, i.e. `c = 1/8` and `ψ = 3c = 3/8`): for every row `p = (a,b)`
of `hbTable10` there are `lam > 0` such that the left-hand side is **negative** on the whole
region `λ₁ ≤ a`, `λ₂ ∈ [λ₁, b]`, with the test function of HB Lemma 7.2 (`tf72T`). -/
theorem table10_62_cert :
    ∀ p ∈ Work.ZeroFreeTables.tableR Work.ZeroFreeTables.hbTable10,
      ∃ (lam : ℝ) (hl : 0 < lam),
        ∀ u v : ℝ, u ≤ p.1 → u ≤ v → v ≤ p.2 →
          (Work.ZeroFreeTables.tf72T lam hl).F (-u) - (Work.ZeroFreeTables.tf72T lam hl).F 0
            - (Work.ZeroFreeTables.tf72T lam hl).F (v - u)
            + (Work.ZeroFreeTables.tf72T lam hl).f 0 *
                (3 * ((1:ℝ)/8 + 1/1000000)) < 0 := by
  intro p hp
  simp only [tableR, List.mem_map] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  simp only [hbTable10, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> (subst h; push_cast)
  · -- row (34/100, 929/1000)
    have hl : (0:ℝ) < ((97:ℝ)/100) := by norm_num
    refine ⟨((97:ℝ)/100), hl, ?_⟩
    refine tf72_cert_of (a := ((34:ℝ)/100)) (b := ((929:ℝ)/1000)) (lam := ((97:ℝ)/100)) (E1 := (12598937:ℝ)/6250000) hl
      (by norm_num) (by norm_num) (by norm_num) ?_ ?_
    · have hq : 2 * (((34:ℝ)/100) / ((97:ℝ)/100)) = ((68:ℝ)/97) := by norm_num
      rw [hq]
      refine le_trans (tf72_exp_taylor_upper (((68:ℝ)/97)) (by norm_num) (by norm_num)) ?_
      norm_num [Finset.sum_range_succ]
    · norm_num [Ty6_eq]
  · -- row (36/100, 903/1000)
    have hl : (0:ℝ) < ((49:ℝ)/50) := by norm_num
    refine ⟨((49:ℝ)/50), hl, ?_⟩
    refine tf72_cert_of (a := ((36:ℝ)/100)) (b := ((903:ℝ)/1000)) (lam := ((49:ℝ)/50)) (E1 := (6515137:ℝ)/3125000) hl
      (by norm_num) (by norm_num) (by norm_num) ?_ ?_
    · have hq : 2 * (((36:ℝ)/100) / ((49:ℝ)/50)) = ((36:ℝ)/49) := by norm_num
      rw [hq]
      refine le_trans (tf72_exp_taylor_upper (((36:ℝ)/49)) (by norm_num) (by norm_num)) ?_
      norm_num [Finset.sum_range_succ]
    · norm_num [Ty6_eq]
  · -- row (38/100, 887/1000)
    have hl : (0:ℝ) < ((99:ℝ)/100) := by norm_num
    refine ⟨((99:ℝ)/100), hl, ?_⟩
    refine tf72_cert_of (a := ((38:ℝ)/100)) (b := ((887:ℝ)/1000)) (lam := ((99:ℝ)/100)) (E1 := (53868867:ℝ)/25000000) hl
      (by norm_num) (by norm_num) (by norm_num) ?_ ?_
    · have hq : 2 * (((38:ℝ)/100) / ((99:ℝ)/100)) = ((76:ℝ)/99) := by norm_num
      rw [hq]
      refine le_trans (tf72_exp_taylor_upper (((76:ℝ)/99)) (by norm_num) (by norm_num)) ?_
      norm_num [Finset.sum_range_succ]
    · norm_num [Ty6_eq]
  · -- row (40/100, 871/1000)
    have hl : (0:ℝ) < ((1:ℝ)) := by norm_num
    refine ⟨((1:ℝ)), hl, ?_⟩
    refine tf72_cert_of (a := ((40:ℝ)/100)) (b := ((871:ℝ)/1000)) (lam := ((1:ℝ))) (E1 := (222554127:ℝ)/100000000) hl
      (by norm_num) (by norm_num) (by norm_num) ?_ ?_
    · have hq : 2 * (((40:ℝ)/100) / ((1:ℝ))) = ((4:ℝ)/5) := by norm_num
      rw [hq]
      refine le_trans (tf72_exp_taylor_upper (((4:ℝ)/5)) (by norm_num) (by norm_num)) ?_
      norm_num [Finset.sum_range_succ]
    · norm_num [Ty6_eq]
  · -- row (42/100, 856/1000)
    have hl : (0:ℝ) < ((51:ℝ)/50) := by norm_num
    refine ⟨((51:ℝ)/50), hl, ?_⟩
    refine tf72_cert_of (a := ((42:ℝ)/100)) (b := ((856:ℝ)/1000)) (lam := ((51:ℝ)/50)) (E1 := (227852797:ℝ)/100000000) hl
      (by norm_num) (by norm_num) (by norm_num) ?_ ?_
    · have hq : 2 * (((42:ℝ)/100) / ((51:ℝ)/50)) = ((14:ℝ)/17) := by norm_num
      rw [hq]
      refine le_trans (tf72_exp_taylor_upper (((14:ℝ)/17)) (by norm_num) (by norm_num)) ?_
      norm_num [Finset.sum_range_succ]
    · norm_num [Ty6_eq]
  · -- row (44/100, 842/1000)
    have hl : (0:ℝ) < ((103:ℝ)/100) := by norm_num
    refine ⟨((103:ℝ)/100), hl, ?_⟩
    refine tf72_cert_of (a := ((44:ℝ)/100)) (b := ((842:ℝ)/1000)) (lam := ((103:ℝ)/100)) (E1 := (117494579:ℝ)/50000000) hl
      (by norm_num) (by norm_num) (by norm_num) ?_ ?_
    · have hq : 2 * (((44:ℝ)/100) / ((103:ℝ)/100)) = ((88:ℝ)/103) := by norm_num
      rw [hq]
      refine le_trans (tf72_exp_taylor_upper (((88:ℝ)/103)) (by norm_num) (by norm_num)) ?_
      norm_num [Finset.sum_range_succ]
    · norm_num [Ty6_eq]
  · -- row (46/100, 829/1000)
    have hl : (0:ℝ) < ((26:ℝ)/25) := by norm_num
    refine ⟨((26:ℝ)/25), hl, ?_⟩
    refine tf72_cert_of (a := ((46:ℝ)/100)) (b := ((829:ℝ)/1000)) (lam := ((26:ℝ)/25)) (E1 := (60551337:ℝ)/25000000) hl
      (by norm_num) (by norm_num) (by norm_num) ?_ ?_
    · have hq : 2 * (((46:ℝ)/100) / ((26:ℝ)/25)) = ((23:ℝ)/26) := by norm_num
      rw [hq]
      refine le_trans (tf72_exp_taylor_upper (((23:ℝ)/26)) (by norm_num) (by norm_num)) ?_
      norm_num [Finset.sum_range_succ]
    · norm_num [Ty6_eq]
  · -- row (48/100, 816/1000)
    have hl : (0:ℝ) < ((21:ℝ)/20) := by norm_num
    refine ⟨((21:ℝ)/20), hl, ?_⟩
    refine tf72_cert_of (a := ((48:ℝ)/100)) (b := ((816:ℝ)/1000)) (lam := ((21:ℝ)/20)) (E1 := (249499359:ℝ)/100000000) hl
      (by norm_num) (by norm_num) (by norm_num) ?_ ?_
    · have hq : 2 * (((48:ℝ)/100) / ((21:ℝ)/20)) = ((32:ℝ)/35) := by norm_num
      rw [hq]
      refine le_trans (tf72_exp_taylor_upper (((32:ℝ)/35)) (by norm_num) (by norm_num)) ?_
      norm_num [Finset.sum_range_succ]
    · norm_num [Ty6_eq]
  · -- row (50/100, 803/1000)
    have hl : (0:ℝ) < ((53:ℝ)/50) := by norm_num
    refine ⟨((53:ℝ)/50), hl, ?_⟩
    refine tf72_cert_of (a := ((50:ℝ)/100)) (b := ((803:ℝ)/1000)) (lam := ((53:ℝ)/50)) (E1 := (128434597:ℝ)/50000000) hl
      (by norm_num) (by norm_num) (by norm_num) ?_ ?_
    · have hq : 2 * (((50:ℝ)/100) / ((53:ℝ)/50)) = ((50:ℝ)/53) := by norm_num
      rw [hq]
      refine le_trans (tf72_exp_taylor_upper (((50:ℝ)/53)) (by norm_num) (by norm_num)) ?_
      norm_num [Finset.sum_range_succ]
    · norm_num [Ty6_eq]
  · -- row (52/100, 791/1000)
    have hl : (0:ℝ) < ((107:ℝ)/100) := by norm_num
    refine ⟨((107:ℝ)/100), hl, ?_⟩
    refine tf72_cert_of (a := ((52:ℝ)/100)) (b := ((791:ℝ)/1000)) (lam := ((107:ℝ)/100)) (E1 := (264312873:ℝ)/100000000) hl
      (by norm_num) (by norm_num) (by norm_num) ?_ ?_
    · have hq : 2 * (((52:ℝ)/100) / ((107:ℝ)/100)) = ((104:ℝ)/107) := by norm_num
      rw [hq]
      refine le_trans (tf72_exp_taylor_upper (((104:ℝ)/107)) (by norm_num) (by norm_num)) ?_
      norm_num [Finset.sum_range_succ]
    · norm_num [Ty6_eq]
  · -- row (54/100, 780/1000)
    have hl : (0:ℝ) < ((27:ℝ)/25) := by norm_num
    refine ⟨((27:ℝ)/25), hl, ?_⟩
    refine tf72_cert_of (a := ((54:ℝ)/100)) (b := ((780:ℝ)/1000)) (lam := ((27:ℝ)/25)) (E1 := (271828429:ℝ)/100000000) hl
      (by norm_num) (by norm_num) (by norm_num) ?_ ?_
    · have hq : 2 * (((54:ℝ)/100) / ((27:ℝ)/25)) = ((1:ℝ)) := by norm_num
      rw [hq]
      refine le_trans (tf72_exp_taylor_upper (((1:ℝ))) (by norm_num) (by norm_num)) ?_
      norm_num [Finset.sum_range_succ]
    · norm_num [Ty6_eq]
  · -- row (56/100, 769/1000)
    have hl : (0:ℝ) < ((109:ℝ)/100) := by norm_num
    refine ⟨((109:ℝ)/100), hl, ?_⟩
    refine tf72_cert_of (a := ((56:ℝ)/100)) (b := ((769:ℝ)/1000)) (lam := ((109:ℝ)/100)) (E1 := (279413913:ℝ)/100000000) hl
      (by norm_num) (by norm_num) (by norm_num) ?_ ?_
    · have hq : 2 * (((56:ℝ)/100) / ((109:ℝ)/100)) = ((112:ℝ)/109) := by norm_num
      rw [hq]
      refine le_trans (tf72_exp_taylor_upper (((112:ℝ)/109)) (by norm_num) (by norm_num)) ?_
      norm_num [Finset.sum_range_succ]
    · norm_num [Ty6_eq]
  · -- row (58/100, 759/1000)
    have hl : (0:ℝ) < ((11:ℝ)/10) := by norm_num
    refine ⟨((11:ℝ)/10), hl, ?_⟩
    refine tf72_cert_of (a := ((58:ℝ)/100)) (b := ((759:ℝ)/1000)) (lam := ((11:ℝ)/10)) (E1 := (143533697:ℝ)/50000000) hl
      (by norm_num) (by norm_num) (by norm_num) ?_ ?_
    · have hq : 2 * (((58:ℝ)/100) / ((11:ℝ)/10)) = ((58:ℝ)/55) := by norm_num
      rw [hq]
      refine le_trans (tf72_exp_taylor_upper (((58:ℝ)/55)) (by norm_num) (by norm_num)) ?_
      norm_num [Finset.sum_range_succ]
    · norm_num [Ty6_eq]
  · -- row (60/100, 749/1000)
    have hl : (0:ℝ) < ((111:ℝ)/100) := by norm_num
    refine ⟨((111:ℝ)/100), hl, ?_⟩
    refine tf72_cert_of (a := ((60:ℝ)/100)) (b := ((749:ℝ)/1000)) (lam := ((111:ℝ)/100)) (E1 := (294786961:ℝ)/100000000) hl
      (by norm_num) (by norm_num) (by norm_num) ?_ ?_
    · have hq : 2 * (((60:ℝ)/100) / ((111:ℝ)/100)) = ((40:ℝ)/37) := by norm_num
      rw [hq]
      refine le_trans (tf72_exp_taylor_upper (((40:ℝ)/37)) (by norm_num) (by norm_num)) ?_
      norm_num [Finset.sum_range_succ]
    · norm_num [Ty6_eq]
  · -- row (62/100, 739/1000)
    have hl : (0:ℝ) < ((111:ℝ)/100) := by norm_num
    refine ⟨((111:ℝ)/100), hl, ?_⟩
    refine tf72_cert_of (a := ((62:ℝ)/100)) (b := ((739:ℝ)/1000)) (lam := ((111:ℝ)/100)) (E1 := (152801893:ℝ)/50000000) hl
      (by norm_num) (by norm_num) (by norm_num) ?_ ?_
    · have hq : 2 * (((62:ℝ)/100) / ((111:ℝ)/100)) = ((124:ℝ)/111) := by norm_num
      rw [hq]
      refine le_trans (tf72_exp_taylor_upper (((124:ℝ)/111)) (by norm_num) (by norm_num)) ?_
      norm_num [Finset.sum_range_succ]
    · norm_num [Ty6_eq]
  · -- row (64/100, 730/1000)
    have hl : (0:ℝ) < ((28:ℝ)/25) := by norm_num
    refine ⟨((28:ℝ)/25), hl, ?_⟩
    refine tf72_cert_of (a := ((64:ℝ)/100)) (b := ((730:ℝ)/1000)) (lam := ((28:ℝ)/25)) (E1 := (313572277:ℝ)/100000000) hl
      (by norm_num) (by norm_num) (by norm_num) ?_ ?_
    · have hq : 2 * (((64:ℝ)/100) / ((28:ℝ)/25)) = ((8:ℝ)/7) := by norm_num
      rw [hq]
      refine le_trans (tf72_exp_taylor_upper (((8:ℝ)/7)) (by norm_num) (by norm_num)) ?_
      norm_num [Finset.sum_range_succ]
    · norm_num [Ty6_eq]
  · -- row (66/100, 721/1000)
    have hl : (0:ℝ) < ((113:ℝ)/100) := by norm_num
    refine ⟨((113:ℝ)/100), hl, ?_⟩
    refine tf72_cert_of (a := ((66:ℝ)/100)) (b := ((721:ℝ)/1000)) (lam := ((113:ℝ)/100)) (E1 := (321602013:ℝ)/100000000) hl
      (by norm_num) (by norm_num) (by norm_num) ?_ ?_
    · have hq : 2 * (((66:ℝ)/100) / ((113:ℝ)/100)) = ((132:ℝ)/113) := by norm_num
      rw [hq]
      refine le_trans (tf72_exp_taylor_upper (((132:ℝ)/113)) (by norm_num) (by norm_num)) ?_
      norm_num [Finset.sum_range_succ]
    · norm_num [Ty6_eq]
  · -- row (68/100, 712/1000)
    have hl : (0:ℝ) < ((57:ℝ)/50) := by norm_num
    refine ⟨((57:ℝ)/50), hl, ?_⟩
    refine tf72_cert_of (a := ((68:ℝ)/100)) (b := ((712:ℝ)/1000)) (lam := ((57:ℝ)/50)) (E1 := (329691111:ℝ)/100000000) hl
      (by norm_num) (by norm_num) (by norm_num) ?_ ?_
    · have hq : 2 * (((68:ℝ)/100) / ((57:ℝ)/50)) = ((68:ℝ)/57) := by norm_num
      rw [hq]
      refine le_trans (tf72_exp_taylor_upper (((68:ℝ)/57)) (by norm_num) (by norm_num)) ?_
      norm_num [Finset.sum_range_succ]
    · norm_num [Ty6_eq]
  · -- row (70/100, 704/1000)
    have hl : (0:ℝ) < ((23:ℝ)/20) := by norm_num
    refine ⟨((23:ℝ)/20), hl, ?_⟩
    refine tf72_cert_of (a := ((70:ℝ)/100)) (b := ((704:ℝ)/1000)) (lam := ((23:ℝ)/20)) (E1 := (84459427:ℝ)/25000000) hl
      (by norm_num) (by norm_num) (by norm_num) ?_ ?_
    · have hq : 2 * (((70:ℝ)/100) / ((23:ℝ)/20)) = ((28:ℝ)/23) := by norm_num
      rw [hq]
      refine le_trans (tf72_exp_taylor_upper (((28:ℝ)/23)) (by norm_num) (by norm_num)) ?_
      norm_num [Finset.sum_range_succ]
    · norm_num [Ty6_eq]
  · -- row (702/1000, 702/1000)
    have hl : (0:ℝ) < ((23:ℝ)/20) := by norm_num
    refine ⟨((23:ℝ)/20), hl, ?_⟩
    refine tf72_cert_of (a := ((702:ℝ)/1000)) (b := ((702:ℝ)/1000)) (lam := ((23:ℝ)/20)) (E1 := (339014873:ℝ)/100000000) hl
      (by norm_num) (by norm_num) (by norm_num) ?_ ?_
    · have hq : 2 * (((702:ℝ)/1000) / ((23:ℝ)/20)) = ((702:ℝ)/575) := by norm_num
      rw [hq]
      refine le_trans (tf72_exp_taylor_upper (((702:ℝ)/575)) (by norm_num) (by norm_num)) ?_
      norm_num [Finset.sum_range_succ]
    · norm_num [Ty6_eq]

end Work.ZeroFreeTables
