import Mathlib
import Submission.Work.FIArea7.Classical172Defs
import Submission.Work.FIArea7.Prop214Defs
import Submission.Work.FIArea7.jksym_mul_rule_primary
import Submission.Work.FIArea7.sign_re_separation
import Submission.Work.FIArea7.multEpsHilbert
import Submission.Work.FIArea7.cardFilterGnormLe
import Submission.Work.FIArea7.prop214Final
import Submission.Work.FIArea7.squareWaveSepTrunc

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The `w`-side coefficient of the leading term `1` in (20.15). -/
def KA0 (α : GaussianInt → ℂ) (w : GaussianInt) : ℂ :=
  α w * ((1 / 2 : ℂ) * (HilbertInf w.re w.im : ℂ) * JKSym w)

/-- The `w`-side coefficient of the term `sign(vr)`. -/
def KAS (α : GaussianInt → ℂ) (w : GaussianInt) : ℂ :=
  α w * ((1 / 2 : ℂ) * (HilbertInf w.re w.im : ℂ) * ((Int.sign w.im : ℤ) : ℂ) * JKSym w)

/-- The `w`-side coefficient of the `k`-th term of the part of `sign(Re wz)` not
carrying the sign of `w.im`. -/
def KA0k (α : GaussianInt → ℂ) (k : ℤ) (w : GaussianInt) : ℂ :=
  α w * ((1 / 2 : ℂ) * (HilbertInf w.re w.im : ℂ)
    * ((w.toComplex / (‖w.toComplex‖ : ℂ)) ^ k) * JKSym w)

/-- The `w`-side coefficient of the `k`-th term of the part of `sign(Re wz)` carrying the
sign of `w.im`. -/
def KASk (α : GaussianInt → ℂ) (k : ℤ) (w : GaussianInt) : ℂ :=
  α w * ((1 / 2 : ℂ) * (HilbertInf w.re w.im : ℂ) * ((Int.sign w.im : ℤ) : ℂ)
    * ((w.toComplex / (‖w.toComplex‖ : ℂ)) ^ k) * JKSym w)

/-- The `z`-side coefficient of the leading term. -/
def KB0 (β : GaussianInt → ℂ) (z : GaussianInt) : ℂ := β z * JKSym z

/-- The `z`-side coefficient of the term `sign(vr)`. -/
def KBS (β : GaussianInt → ℂ) (z : GaussianInt) : ℂ :=
  β z * (((Int.sign z.re : ℤ) : ℂ) * JKSym z)

/-- The `z`-side coefficient of the `k`-th term, without the sign of `z.re`. -/
def KB0k (β : GaussianInt → ℂ) (k : ℤ) (z : GaussianInt) : ℂ :=
  β z * (((z.toComplex / (‖z.toComplex‖ : ℂ)) ^ k) * JKSym z)

/-- The `z`-side coefficient of the `k`-th term, with the sign of `z.re`. -/
def KBSk (β : GaussianInt → ℂ) (k : ℤ) (z : GaussianInt) : ℂ :=
  β z * (((Int.sign z.re : ℤ) : ℂ) * ((z.toComplex / (‖z.toComplex‖ : ℂ)) ^ k) * JKSym z)

/-- The truncation `Σ_{|k| ≤ K} ĉ_k (w/|w|)^k (z/|z|)^k` of the Fourier series (20.19). -/
def KTrunc (ĉ : ℤ → ℂ) (Kz : ℤ) (w z : GaussianInt) : ℂ :=
  ∑ k ∈ Finset.Icc (-Kz) Kz,
    ĉ k * ((w.toComplex / (‖w.toComplex‖ : ℂ)) ^ k * (z.toComplex / (‖z.toComplex‖ : ℂ)) ^ k)

/-- The truncation error of a single pair `(w,z)`. -/
def KErr (α β : GaussianInt → ℂ) (ĉ : ℤ → ℂ) (Kz : ℤ) (w z : GaussianInt) : ℂ :=
  - (α w * β z * JKSym w * JKSym z * (DirichletSym w z : ℂ)
      * ((1 / 2 : ℂ) * (HilbertInf w.re w.im : ℂ)
          * (((Int.sign w.im - Int.sign z.re : ℤ)) : ℂ)
          * ((((Int.sign ((w * z).re) : ℤ)) : ℂ) - KTrunc ĉ Kz w z)))

/-! ## 2. Norms -/

lemma norm_toComplex_sqrt (z : GaussianInt) :
    ‖z.toComplex‖ = Real.sqrt (((Work.FIPlan.gnorm z : ℕ)) : ℝ) := by
  have h2 : (((Work.FIPlan.gnorm z : ℕ)) : ℝ) = (z.re : ℝ) ^ 2 + (z.im : ℝ) ^ 2 := by
    have h3 : (Work.FIPlan.gnorm z : ℤ) = z.re ^ 2 + z.im ^ 2 := Work.FIArea7.norm_eq z
    exact_mod_cast h3
  have h : ‖(z : ℂ)‖ ^ 2 = (((Work.FIPlan.gnorm z : ℕ)) : ℝ) := by
    rw [Complex.sq_norm, Complex.normSq_apply, h2]
    rw [show ((z : ℂ)).re = (z.re : ℝ) from (GaussianInt.intCast_re z).symm,
      show ((z : ℂ)).im = (z.im : ℝ) from (GaussianInt.intCast_im z).symm]
    ring
  rw [← h, Real.sqrt_sq (norm_nonneg _)]

lemma norm_two_inv : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by
  rw [show (1 / 2 : ℂ) = (((1 / 2 : ℝ)) : ℂ) by norm_num]
  rw [Complex.norm_real, Real.norm_eq_abs]
  norm_num

lemma norm_hilb (u v : ℤ) : ‖(HilbertInf u v : ℂ)‖ = 1 := by
  rw [HilbertInf]; split_ifs <;> (rw [Complex.norm_intCast]; norm_num)

lemma norm_sign_le_one (n : ℤ) : ‖((Int.sign n : ℤ) : ℂ)‖ ≤ 1 := by
  rcases lt_trichotomy n 0 with h | h | h
  · rw [Int.sign_eq_neg_one_of_neg h]; norm_num
  · rw [h, Int.sign_zero]; norm_num
  · rw [Int.sign_eq_one_of_pos h]; norm_num

lemma norm_unit_pow_le (z : GaussianInt) (k : ℤ) :
    ‖(z.toComplex / (‖z.toComplex‖ : ℂ)) ^ k‖ ≤ 1 := by
  by_cases h : z.toComplex = 0
  · rw [h, norm_zero, zero_div]
    rcases eq_or_ne k 0 with hk | hk
    · rw [hk]; simp
    · rw [zero_zpow _ hk]; simp
  · have hnorm : ‖(((‖z.toComplex‖ : ℝ)) : ℂ)‖ = ‖z.toComplex‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    rw [norm_zpow, norm_div, hnorm, div_self (norm_ne_zero_iff.mpr h)]
    simp


lemma mul2_le_one {a b : ℝ} (ha : a ≤ 1) (hb : b ≤ 1) (hb0 : 0 ≤ b) : a * b ≤ 1 := by
  calc a * b ≤ 1 * 1 := mul_le_mul ha hb hb0 zero_le_one
    _ = 1 := by norm_num

lemma mul3_le_one {a b c : ℝ} (ha : a ≤ 1) (hb : b ≤ 1) (hc : c ≤ 1) (hb0 : 0 ≤ b)
    (hc0 : 0 ≤ c) : a * b * c ≤ 1 := by
  have h2 : b * c ≤ 1 := mul2_le_one hb hc hc0
  calc a * b * c = a * (b * c) := by ring
    _ ≤ 1 := mul2_le_one ha h2 (by positivity)

lemma mul4_le_one {a b c d : ℝ} (ha : a ≤ 1) (hb : b ≤ 1) (hc : c ≤ 1) (hd : d ≤ 1)
    (hb0 : 0 ≤ b) (hc0 : 0 ≤ c) (hd0 : 0 ≤ d) : a * b * c * d ≤ 1 := by
  have h3 : b * c * d ≤ 1 := mul3_le_one hb hc hd hc0 hd0
  calc a * b * c * d = a * (b * c * d) := by ring
    _ ≤ 1 := mul2_le_one ha h3 (by positivity)

lemma mul5_le_one {a b c d e : ℝ} (ha : a ≤ 1) (hb : b ≤ 1) (hc : c ≤ 1) (hd : d ≤ 1)
    (he : e ≤ 1) (hb0 : 0 ≤ b) (hc0 : 0 ≤ c) (hd0 : 0 ≤ d) (he0 : 0 ≤ e) :
    a * b * c * d * e ≤ 1 := by
  have h4 : b * c * d * e ≤ 1 := mul4_le_one hb hc hd he hc0 hd0 he0
  calc a * b * c * d * e = a * (b * c * d * e) := by ring
    _ ≤ 1 := mul2_le_one ha h4 (by positivity)

lemma norm_fA0 (w : GaussianInt) :
    ‖(1 / 2 : ℂ) * (HilbertInf w.re w.im : ℂ) * JKSym w‖ ≤ 1 := by
  rw [norm_mul, norm_mul, norm_two_inv, norm_hilb]
  have h := norm_JKSym_le_one w
  have h2 := norm_nonneg (JKSym w)
  nlinarith

lemma norm_fAS (w : GaussianInt) :
    ‖(1 / 2 : ℂ) * (HilbertInf w.re w.im : ℂ) * ((Int.sign w.im : ℤ) : ℂ) * JKSym w‖ ≤ 1 := by
  rw [norm_mul, norm_mul, norm_mul, norm_two_inv, norm_hilb]
  exact mul4_le_one (by norm_num) le_rfl (norm_sign_le_one w.im) (norm_JKSym_le_one w)
    zero_le_one (norm_nonneg _) (norm_nonneg _)

lemma norm_fA0k (w : GaussianInt) (k : ℤ) :
    ‖(1 / 2 : ℂ) * (HilbertInf w.re w.im : ℂ)
      * ((w.toComplex / (‖w.toComplex‖ : ℂ)) ^ k) * JKSym w‖ ≤ 1 := by
  rw [norm_mul, norm_mul, norm_mul, norm_two_inv, norm_hilb]
  exact mul4_le_one (by norm_num) le_rfl (norm_unit_pow_le w k) (norm_JKSym_le_one w)
    zero_le_one (norm_nonneg _) (norm_nonneg _)

lemma norm_fASk (w : GaussianInt) (k : ℤ) :
    ‖(1 / 2 : ℂ) * (HilbertInf w.re w.im : ℂ) * ((Int.sign w.im : ℤ) : ℂ)
      * ((w.toComplex / (‖w.toComplex‖ : ℂ)) ^ k) * JKSym w‖ ≤ 1 := by
  rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_two_inv, norm_hilb]
  exact mul5_le_one (by norm_num) le_rfl (norm_sign_le_one w.im) (norm_unit_pow_le w k)
    (norm_JKSym_le_one w) zero_le_one (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)

lemma norm_fBS (z : GaussianInt) : ‖((Int.sign z.re : ℤ) : ℂ) * JKSym z‖ ≤ 1 := by
  rw [norm_mul]
  exact mul2_le_one (norm_sign_le_one z.re) (norm_JKSym_le_one z) (norm_nonneg _)

lemma norm_fB0k (z : GaussianInt) (k : ℤ) :
    ‖((z.toComplex / (‖z.toComplex‖ : ℂ)) ^ k) * JKSym z‖ ≤ 1 := by
  rw [norm_mul]
  exact mul2_le_one (norm_unit_pow_le z k) (norm_JKSym_le_one z) (norm_nonneg _)

lemma norm_fBSk (z : GaussianInt) (k : ℤ) :
    ‖((Int.sign z.re : ℤ) : ℂ) * ((z.toComplex / (‖z.toComplex‖ : ℂ)) ^ k) * JKSym z‖ ≤ 1 := by
  rw [norm_mul, norm_mul]
  exact mul3_le_one (norm_sign_le_one z.re) (norm_unit_pow_le z k) (norm_JKSym_le_one z)
    (norm_nonneg _) (norm_nonneg _)

/-! ## 3. The coefficients are bounded by `1`, and are supported where `α`, `β` are -/

lemma norm_KA0_le {α : GaussianInt → ℂ} (hα : ∀ w, ‖α w‖ ≤ 1) (w : GaussianInt) :
    ‖KA0 α w‖ ≤ 1 := by
  rw [KA0, norm_mul]
  calc ‖α w‖ * ‖(1 / 2 : ℂ) * (HilbertInf w.re w.im : ℂ) * JKSym w‖ ≤ 1 * 1 :=
        mul_le_mul (hα w) (norm_fA0 w) (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

lemma norm_KAS_le {α : GaussianInt → ℂ} (hα : ∀ w, ‖α w‖ ≤ 1) (w : GaussianInt) :
    ‖KAS α w‖ ≤ 1 := by
  rw [KAS, norm_mul]
  calc ‖α w‖ * ‖(1 / 2 : ℂ) * (HilbertInf w.re w.im : ℂ) * ((Int.sign w.im : ℤ) : ℂ)
        * JKSym w‖ ≤ 1 * 1 :=
        mul_le_mul (hα w) (norm_fAS w) (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

lemma norm_KA0k_le {α : GaussianInt → ℂ} (hα : ∀ w, ‖α w‖ ≤ 1) (k : ℤ) (w : GaussianInt) :
    ‖KA0k α k w‖ ≤ 1 := by
  rw [KA0k, norm_mul]
  calc ‖α w‖ * ‖(1 / 2 : ℂ) * (HilbertInf w.re w.im : ℂ)
        * ((w.toComplex / (‖w.toComplex‖ : ℂ)) ^ k) * JKSym w‖ ≤ 1 * 1 :=
        mul_le_mul (hα w) (norm_fA0k w k) (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

lemma norm_KASk_le {α : GaussianInt → ℂ} (hα : ∀ w, ‖α w‖ ≤ 1) (k : ℤ) (w : GaussianInt) :
    ‖KASk α k w‖ ≤ 1 := by
  rw [KASk, norm_mul]
  calc ‖α w‖ * ‖(1 / 2 : ℂ) * (HilbertInf w.re w.im : ℂ) * ((Int.sign w.im : ℤ) : ℂ)
        * ((w.toComplex / (‖w.toComplex‖ : ℂ)) ^ k) * JKSym w‖ ≤ 1 * 1 :=
        mul_le_mul (hα w) (norm_fASk w k) (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

lemma norm_KB0_le {β : GaussianInt → ℂ} (hβ : ∀ z, ‖β z‖ ≤ 1) (z : GaussianInt) :
    ‖KB0 β z‖ ≤ 1 := by
  rw [KB0, norm_mul]
  calc ‖β z‖ * ‖JKSym z‖ ≤ 1 * 1 :=
        mul_le_mul (hβ z) (norm_JKSym_le_one z) (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

lemma norm_KBS_le {β : GaussianInt → ℂ} (hβ : ∀ z, ‖β z‖ ≤ 1) (z : GaussianInt) :
    ‖KBS β z‖ ≤ 1 := by
  rw [KBS, norm_mul]
  calc ‖β z‖ * ‖((Int.sign z.re : ℤ) : ℂ) * JKSym z‖ ≤ 1 * 1 :=
        mul_le_mul (hβ z) (norm_fBS z) (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

lemma norm_KB0k_le {β : GaussianInt → ℂ} (hβ : ∀ z, ‖β z‖ ≤ 1) (k : ℤ) (z : GaussianInt) :
    ‖KB0k β k z‖ ≤ 1 := by
  rw [KB0k, norm_mul]
  calc ‖β z‖ * ‖((z.toComplex / (‖z.toComplex‖ : ℂ)) ^ k) * JKSym z‖ ≤ 1 * 1 :=
        mul_le_mul (hβ z) (norm_fB0k z k) (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

lemma norm_KBSk_le {β : GaussianInt → ℂ} (hβ : ∀ z, ‖β z‖ ≤ 1) (k : ℤ) (z : GaussianInt) :
    ‖KBSk β k z‖ ≤ 1 := by
  rw [KBSk, norm_mul]
  calc ‖β z‖ * ‖((Int.sign z.re : ℤ) : ℂ) * ((z.toComplex / (‖z.toComplex‖ : ℂ)) ^ k)
        * JKSym z‖ ≤ 1 * 1 :=
        mul_le_mul (hβ z) (norm_fBSk z k) (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

lemma KA0_supp {α : GaussianInt → ℂ} {M : ℝ}
    (h : ∀ w, α w ≠ 0 → Work.FIPlan.IsPrimary w ∧ IsCoprime w.re w.im ∧
      (Work.FIPlan.gnorm w : ℝ) ≤ M)
    {w : GaussianInt} (hw : KA0 α w ≠ 0) :
    Work.FIPlan.IsPrimary w ∧ IsCoprime w.re w.im ∧ (Work.FIPlan.gnorm w : ℝ) ≤ M :=
  h w (fun h0 => hw (by rw [KA0, h0, zero_mul]))

lemma KAS_supp {α : GaussianInt → ℂ} {M : ℝ}
    (h : ∀ w, α w ≠ 0 → Work.FIPlan.IsPrimary w ∧ IsCoprime w.re w.im ∧
      (Work.FIPlan.gnorm w : ℝ) ≤ M)
    {w : GaussianInt} (hw : KAS α w ≠ 0) :
    Work.FIPlan.IsPrimary w ∧ IsCoprime w.re w.im ∧ (Work.FIPlan.gnorm w : ℝ) ≤ M :=
  h w (fun h0 => hw (by rw [KAS, h0, zero_mul]))

lemma KA0k_supp {α : GaussianInt → ℂ} {M : ℝ}
    (h : ∀ w, α w ≠ 0 → Work.FIPlan.IsPrimary w ∧ IsCoprime w.re w.im ∧
      (Work.FIPlan.gnorm w : ℝ) ≤ M)
    (k : ℤ) {w : GaussianInt} (hw : KA0k α k w ≠ 0) :
    Work.FIPlan.IsPrimary w ∧ IsCoprime w.re w.im ∧ (Work.FIPlan.gnorm w : ℝ) ≤ M :=
  h w (fun h0 => hw (by rw [KA0k, h0, zero_mul]))

lemma KASk_supp {α : GaussianInt → ℂ} {M : ℝ}
    (h : ∀ w, α w ≠ 0 → Work.FIPlan.IsPrimary w ∧ IsCoprime w.re w.im ∧
      (Work.FIPlan.gnorm w : ℝ) ≤ M)
    (k : ℤ) {w : GaussianInt} (hw : KASk α k w ≠ 0) :
    Work.FIPlan.IsPrimary w ∧ IsCoprime w.re w.im ∧ (Work.FIPlan.gnorm w : ℝ) ≤ M :=
  h w (fun h0 => hw (by rw [KASk, h0, zero_mul]))

lemma KB0_supp {β : GaussianInt → ℂ} {N : ℝ}
    (h : ∀ z, β z ≠ 0 → Work.FIPlan.IsPrimary z ∧ (Work.FIPlan.gnorm z : ℝ) ≤ N)
    {z : GaussianInt} (hz : KB0 β z ≠ 0) :
    Work.FIPlan.IsPrimary z ∧ (Work.FIPlan.gnorm z : ℝ) ≤ N :=
  h z (fun h0 => hz (by rw [KB0, h0, zero_mul]))

lemma KBS_supp {β : GaussianInt → ℂ} {N : ℝ}
    (h : ∀ z, β z ≠ 0 → Work.FIPlan.IsPrimary z ∧ (Work.FIPlan.gnorm z : ℝ) ≤ N)
    {z : GaussianInt} (hz : KBS β z ≠ 0) :
    Work.FIPlan.IsPrimary z ∧ (Work.FIPlan.gnorm z : ℝ) ≤ N :=
  h z (fun h0 => hz (by rw [KBS, h0, zero_mul]))

lemma KB0k_supp {β : GaussianInt → ℂ} {N : ℝ}
    (h : ∀ z, β z ≠ 0 → Work.FIPlan.IsPrimary z ∧ (Work.FIPlan.gnorm z : ℝ) ≤ N)
    (k : ℤ) {z : GaussianInt} (hz : KB0k β k z ≠ 0) :
    Work.FIPlan.IsPrimary z ∧ (Work.FIPlan.gnorm z : ℝ) ≤ N :=
  h z (fun h0 => hz (by rw [KB0k, h0, zero_mul]))

lemma KBSk_supp {β : GaussianInt → ℂ} {N : ℝ}
    (h : ∀ z, β z ≠ 0 → Work.FIPlan.IsPrimary z ∧ (Work.FIPlan.gnorm z : ℝ) ≤ N)
    (k : ℤ) {z : GaussianInt} (hz : KBSk β k z ≠ 0) :
    Work.FIPlan.IsPrimary z ∧ (Work.FIPlan.gnorm z : ℝ) ≤ N :=
  h z (fun h0 => hz (by rw [KBSk, h0, zero_mul]))

/-! ## 4. The room condition and the sign of an odd integer -/

lemma int_sign_cast_eq {n : ℤ} (hn : n ≠ 0) :
    ((Int.sign n : ℤ) : ℂ) = if 0 < (n : ℝ) then (1 : ℂ) else -1 := by
  rcases lt_trichotomy n 0 with h | h | h
  · rw [Int.sign_eq_neg_one_of_neg h,
      if_neg (by exact_mod_cast (not_lt.mpr h.le) : ¬ (0 : ℝ) < (n : ℝ))]
    norm_num
  · exact absurd h hn
  · rw [Int.sign_eq_one_of_pos h, if_pos (by exact_mod_cast h)]
    norm_num

lemma re_mul_odd {w z : GaussianInt} (hw : Work.FIPlan.IsPrimary w)
    (hz : Work.FIPlan.IsPrimary z) : Odd ((w * z).re) := by
  obtain ⟨hu, hv, _⟩ := hw
  obtain ⟨hr, hs, _⟩ := hz
  rw [re_mul]
  exact (hu.mul hr).sub_even (hv.mul_right z.im)

lemma re_mul_ne_zero {w z : GaussianInt} (hw : Work.FIPlan.IsPrimary w)
    (hz : Work.FIPlan.IsPrimary z) : (w * z).re ≠ 0 := by
  have hodd := re_mul_odd hw hz
  intro h0
  obtain ⟨k, hk⟩ := hodd
  rw [h0] at hk
  omega

lemma abs_re_mul_ge_one {w z : GaussianInt} (hw : Work.FIPlan.IsPrimary w)
    (hz : Work.FIPlan.IsPrimary z) : (1 : ℝ) ≤ |(((w * z).re : ℤ) : ℝ)| := by
  have hne := re_mul_ne_zero hw hz
  have h1 : (1 : ℤ) ≤ |(w * z).re| := by
    have := abs_pos.mpr hne; omega
  rw [← Int.cast_abs]
  exact_mod_cast h1

lemma room_cond {M N : ℝ} (hM : 1 ≤ M) (hN : 1 ≤ N) {α β : GaussianInt → ℂ}
    {w z : GaussianInt}
    (hsw : ∀ w, α w ≠ 0 → Work.FIPlan.IsPrimary w ∧ IsCoprime w.re w.im ∧
      (Work.FIPlan.gnorm w : ℝ) ≤ M)
    (hsz : ∀ z, β z ≠ 0 → Work.FIPlan.IsPrimary z ∧ (Work.FIPlan.gnorm z : ℝ) ≤ N)
    (hw : α w ≠ 0) (hz : β z ≠ 0) :
    ‖w.toComplex‖ * ‖z.toComplex‖
      ≤ ((truncR M N : ℕ) : ℝ) * |(w.toComplex * z.toComplex).re| := by
  obtain ⟨hwP, _, hwM⟩ := hsw w hw
  obtain ⟨hzP, hzN⟩ := hsz z hz
  have hMw : (0 : ℝ) ≤ M := le_trans zero_le_one hM
  have h1 : ‖w.toComplex‖ ≤ Real.sqrt M := by
    rw [norm_toComplex_sqrt]; exact Real.sqrt_le_sqrt hwM
  have h2 : ‖z.toComplex‖ ≤ Real.sqrt N := by
    rw [norm_toComplex_sqrt]; exact Real.sqrt_le_sqrt hzN
  have h3 : ‖w.toComplex‖ * ‖z.toComplex‖ ≤ Real.sqrt M * Real.sqrt N :=
    mul_le_mul h1 h2 (norm_nonneg _) (Real.sqrt_nonneg M)
  have h4 : Real.sqrt M * Real.sqrt N = Real.sqrt (M * N) := (Real.sqrt_mul hMw N).symm
  have h5 : Real.sqrt (M * N) ≤ ((truncR M N : ℕ) : ℝ) := by
    have hceil := Nat.le_ceil (Real.sqrt (M * N))
    simp only [truncR]
    push_cast
    linarith
  have h6 : (1 : ℝ) ≤ |(w.toComplex * z.toComplex).re| := by
    rw [← GaussianInt.toComplex_mul, ← GaussianInt.intCast_re]
    exact abs_re_mul_ge_one hwP hzP
  have h7 : (0 : ℝ) ≤ ((truncR M N : ℕ) : ℝ) := by positivity
  have h8 : (0 : ℝ) < |(w.toComplex * z.toComplex).re| := lt_of_lt_of_le one_pos h6
  calc ‖w.toComplex‖ * ‖z.toComplex‖ ≤ Real.sqrt (M * N) := by rw [← h4]; exact h3
    _ ≤ ((truncR M N : ℕ) : ℝ) := h5
    _ ≤ ((truncR M N : ℕ) : ℝ) * |(w.toComplex * z.toComplex).re| := by
        nlinarith [h6, h7, h8]

/-! ## 5. The pointwise decomposition of `α_w β_z [wz]` -/

lemma hilb_sq (u v : ℤ) : (HilbertInf u v : ℂ) * (HilbertInf u v : ℂ) = 1 := by
  have h : (HilbertInf u v : ℂ) = -1 ∨ (HilbertInf u v : ℂ) = 1 := by
    rw [HilbertInf]; split_ifs <;> simp
  rcases h with h | h <;> rw [h] <;> norm_num

lemma re_ne_zero_of_primary {z : GaussianInt} (hz : Work.FIPlan.IsPrimary z) : z.re ≠ 0 := by
  obtain ⟨ho, _, _⟩ := hz
  intro h0
  obtain ⟨k, hk⟩ := ho
  rw [h0] at hk
  omega

lemma key_pointwise {M N : ℝ} (hM : 1 ≤ M) (hN : 1 ≤ N) {α β : GaussianInt → ℂ}
    {ĉ : ℤ → ℂ} {Kz : ℤ} {C1 : ℝ}
    (hKz : Kz = ((truncK M N : ℕ) : ℤ))
    (hsw : ∀ w, α w ≠ 0 → Work.FIPlan.IsPrimary w ∧ IsCoprime w.re w.im ∧
      (Work.FIPlan.gnorm w : ℝ) ≤ M)
    (hsz : ∀ z, β z ≠ 0 → Work.FIPlan.IsPrimary z ∧ (Work.FIPlan.gnorm z : ℝ) ≤ N)
    (htr : ∀ (w z : ℂ), w ≠ 0 → z ≠ 0 →
      ‖w‖ * ‖z‖ ≤ ((truncR M N : ℕ) : ℝ) * |(w * z).re| →
      ‖(if 0 < (w * z).re then (1 : ℂ) else -1)
        - ∑ k ∈ Finset.Icc (-(Kz)) Kz,
            ĉ k * ((w / (‖w‖ : ℂ)) ^ k * (z / (‖z‖ : ℂ)) ^ k)‖
        ≤ C1 * ((truncR M N : ℕ) : ℝ) / ((truncK M N : ℝ) + 1))
    (w z : GaussianInt) :
    α w * β z * JKSym (w * z)
      = (KA0 α w * KB0 β z + KAS α w * KBS β z
          + (∑ k ∈ Finset.Icc (-Kz) Kz, ĉ k * (KA0k α k w * KBSk β k z))
          - (∑ k ∈ Finset.Icc (-Kz) Kz, ĉ k * (KASk α k w * KB0k β k z)))
        * (DirichletSym w z : ℂ) + KErr α β ĉ Kz w z := by
  by_cases h0 : α w * β z = 0
  · rcases mul_eq_zero.mp h0 with h | h
    · rw [h, zero_mul]
      simp only [KA0, KAS, KA0k, KASk, KB0, KBS, KB0k, KBSk, KErr, h, zero_mul, mul_zero,
        Finset.sum_const_zero]
      ring
    · rw [h, mul_zero]
      simp only [KA0, KAS, KA0k, KASk, KB0, KBS, KB0k, KBSk, KErr, h, zero_mul, mul_zero,
        Finset.sum_const_zero]
      ring
  · have hαw : α w ≠ 0 := fun hh => h0 (by rw [hh, zero_mul])
    have hβz : β z ≠ 0 := fun hh => h0 (by rw [hh, mul_zero])
    obtain ⟨hwP, hwc, hwM⟩ := hsw w hαw
    obtain ⟨hzP, hzN⟩ := hsz z hβz
    have hjk := jksym_mul_rule_primary hwP hwc hzP
    have h15 := multEpsHilbert hwP hwc hzP
    have hgnw : (0 : ℝ) < ((Work.FIPlan.gnorm w : ℕ) : ℝ) := by
      have hne : w ≠ 0 := by
        intro h
        exact re_ne_zero_of_primary hwP (by rw [h]; rfl)
      exact_mod_cast Work.FIArea7.gnorm_pos_of_ne_zero hne
    have hgnz : (0 : ℝ) < ((Work.FIPlan.gnorm z : ℕ) : ℝ) := by
      have hne : z ≠ 0 := by
        intro h
        exact re_ne_zero_of_primary hzP (by rw [h]; rfl)
      exact_mod_cast Work.FIArea7.gnorm_pos_of_ne_zero hne
    have hwzc : w.toComplex ≠ 0 := by
      intro h
      have h1 : ‖w.toComplex‖ = 0 := by rw [h, norm_zero]
      rw [norm_toComplex_sqrt] at h1
      exact (ne_of_gt (Real.sqrt_pos_of_pos hgnw)) h1
    have hzzc : z.toComplex ≠ 0 := by
      intro h
      have h1 : ‖z.toComplex‖ = 0 := by rw [h, norm_zero]
      rw [norm_toComplex_sqrt] at h1
      exact (ne_of_gt (Real.sqrt_pos_of_pos hgnz)) h1
    have hroom := room_cond hM hN hsw hsz hαw hβz
    have htrb : ‖(((Int.sign ((w * z).re) : ℤ)) : ℂ) - KTrunc ĉ Kz w z‖
        ≤ C1 * ((truncR M N : ℕ) : ℝ) / ((truncK M N : ℝ) + 1) := by
      have h1 : (((Int.sign ((w * z).re) : ℤ)) : ℂ)
          = (if 0 < (((w * z).re : ℤ) : ℝ) then (1 : ℂ) else -1) :=
        int_sign_cast_eq (re_mul_ne_zero hwP hzP)
      have h2 : KTrunc ĉ Kz w z
          = ∑ k ∈ Finset.Icc (-(Kz)) Kz,
              ĉ k * ((w.toComplex / (‖w.toComplex‖ : ℂ)) ^ k
                * (z.toComplex / (‖z.toComplex‖ : ℂ)) ^ k) := rfl
      rw [h1, h2]
      have hres := htr w.toComplex z.toComplex hwzc hzzc hroom
      rw [← GaussianInt.toComplex_mul, ← GaussianInt.intCast_re] at hres
      exact hres
    have hHI2 : (HilbertInf w.re w.im : ℂ) * (HilbertInf w.re w.im : ℂ) = 1 :=
      hilb_sq w.re w.im
    have hMeps : (MultEps w z : ℂ)
        = (1 / 2 : ℂ) * (HilbertInf w.re w.im : ℂ)
          * (1 + ((Int.sign w.im : ℤ) : ℂ) * ((Int.sign z.re : ℤ) : ℂ)
            - (((Int.sign w.im : ℤ) : ℂ) - ((Int.sign z.re : ℤ) : ℂ))
              * (((Int.sign ((w * z).re) : ℤ)) : ℂ)) := by
      have h2 : (2 : ℂ) * (MultEps w z : ℂ) * (HilbertInf w.re w.im : ℂ)
          = 1 + ((Int.sign w.im : ℤ) : ℂ) * ((Int.sign z.re : ℤ) : ℂ)
            - (((Int.sign w.im : ℤ) : ℂ) - ((Int.sign z.re : ℤ) : ℂ))
              * (((Int.sign ((w * z).re) : ℤ)) : ℂ) := by
        have h := h15
        rw [Int.sign_mul] at h
        push_cast at h
        linear_combination h
      have h3 : (2 : ℂ) * (MultEps w z : ℂ)
          = (1 + ((Int.sign w.im : ℤ) : ℂ) * ((Int.sign z.re : ℤ) : ℂ)
            - (((Int.sign w.im : ℤ) : ℂ) - ((Int.sign z.re : ℤ) : ℂ))
              * (((Int.sign ((w * z).re) : ℤ)) : ℂ)) * (HilbertInf w.re w.im : ℂ) := by
        calc (2 : ℂ) * (MultEps w z : ℂ)
            = (2 * (MultEps w z : ℂ) * (HilbertInf w.re w.im : ℂ))
                * (HilbertInf w.re w.im : ℂ) := by
              rw [show (2 * (MultEps w z : ℂ) * (HilbertInf w.re w.im : ℂ))
                    * (HilbertInf w.re w.im : ℂ)
                  = 2 * (MultEps w z : ℂ)
                    * ((HilbertInf w.re w.im : ℂ) * (HilbertInf w.re w.im : ℂ)) by ring,
                hHI2, mul_one]
          _ = _ := by rw [h2]
      linear_combination (1 / 2 : ℂ) * h3
    have hsplit : ((((Int.sign ((w * z).re) : ℤ)) : ℂ))
        = KTrunc ĉ Kz w z + (((((Int.sign ((w * z).re) : ℤ)) : ℂ)) - KTrunc ĉ Kz w z) := by
      ring
    have eA : KA0 α w * KB0 β z
        = α w * β z * JKSym w * JKSym z * ((1 / 2 : ℂ) * (HilbertInf w.re w.im : ℂ)) := by
      unfold KA0 KB0; ring
    have eB : KAS α w * KBS β z
        = α w * β z * JKSym w * JKSym z
          * ((1 / 2 : ℂ) * (HilbertInf w.re w.im : ℂ)
            * ((Int.sign w.im : ℤ) : ℂ) * ((Int.sign z.re : ℤ) : ℂ)) := by
      unfold KAS KBS; ring
    have eS2 : (∑ k ∈ Finset.Icc (-Kz) Kz, ĉ k * (KA0k α k w * KBSk β k z))
        = α w * β z * JKSym w * JKSym z
          * ((1 / 2 : ℂ) * (HilbertInf w.re w.im : ℂ) * ((Int.sign z.re : ℤ) : ℂ))
          * KTrunc ĉ Kz w z := by
      rw [KTrunc, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      unfold KA0k KBSk
      ring
    have eS1 : (∑ k ∈ Finset.Icc (-Kz) Kz, ĉ k * (KASk α k w * KB0k β k z))
        = α w * β z * JKSym w * JKSym z
          * ((1 / 2 : ℂ) * (HilbertInf w.re w.im : ℂ) * ((Int.sign w.im : ℤ) : ℂ))
          * KTrunc ĉ Kz w z := by
      rw [KTrunc, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      unfold KASk KB0k
      ring
    have eErr : KErr α β ĉ Kz w z
        = - (α w * β z * JKSym w * JKSym z * (DirichletSym w z : ℂ)
            * ((1 / 2 : ℂ) * (HilbertInf w.re w.im : ℂ)
              * ((((Int.sign w.im : ℤ) : ℂ) - ((Int.sign z.re : ℤ) : ℂ))
                * (((((Int.sign ((w * z).re) : ℤ)) : ℂ)) - KTrunc ĉ Kz w z)))) := by
      unfold KErr
      push_cast
      ring
    rw [hjk, hMeps, eA, eB, eS2, eS1, eErr, hsplit]
    ring

/-! ## 6. Reorganising the double sums -/

lemma sum_sum_sum_mul {s t : Finset GaussianInt} {u : Finset ℤ}
    (f : ℤ → GaussianInt → GaussianInt → ℂ) (ξ : GaussianInt → GaussianInt → ℂ) :
    (∑ w ∈ s, ∑ z ∈ t, (∑ k ∈ u, f k w z) * ξ w z)
      = ∑ k ∈ u, ∑ w ∈ s, ∑ z ∈ t, f k w z * ξ w z := by
  calc (∑ w ∈ s, ∑ z ∈ t, (∑ k ∈ u, f k w z) * ξ w z)
      = ∑ w ∈ s, ∑ z ∈ t, ∑ k ∈ u, f k w z * ξ w z := by
        apply Finset.sum_congr rfl; intro w hw
        apply Finset.sum_congr rfl; intro z hz
        rw [Finset.sum_mul]
    _ = ∑ w ∈ s, ∑ k ∈ u, ∑ z ∈ t, f k w z * ξ w z := by
        apply Finset.sum_congr rfl; intro w hw
        rw [Finset.sum_comm]
    _ = ∑ k ∈ u, ∑ w ∈ s, ∑ z ∈ t, f k w z * ξ w z := by
        rw [Finset.sum_comm]

lemma qbilin_smul_coeff {Rw Rz : ℤ} (c : ℂ) (A B : GaussianInt → ℂ) :
    (∑ w ∈ Work.FIPlan.gBox Rw, ∑ z ∈ Work.FIPlan.gBox Rz,
        (c * (A w * B z)) * ((DirichletSym w z : ℤ) : ℂ))
      = c * QBilin Rw Rz A B := by
  rw [QBilin, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro w hw
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro z hz
  ring

lemma norm_KErr_le {α β : GaussianInt → ℂ} {ĉ : ℤ → ℂ} {Kz : ℤ} {w z : GaussianInt} {D : ℝ}
    (h : ‖(((Int.sign ((w * z).re) : ℤ)) : ℂ) - KTrunc ĉ Kz w z‖ ≤ D) :
    ‖KErr α β ĉ Kz w z‖ ≤ ‖α w‖ * ‖β z‖ * D := by
  have hj1 := norm_JKSym_le_one w
  have hj2 := norm_JKSym_le_one z
  have hξ : ‖(DirichletSym w z : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast, ← Int.cast_abs]
    exact_mod_cast abs_dirichletSym_le_one w z
  have hsv0 : ‖(((Int.sign w.im : ℤ)) : ℂ) - (((Int.sign z.re : ℤ)) : ℂ)‖ ≤ 2 := by
    have h1 := norm_sign_le_one w.im
    have h2 := norm_sign_le_one z.re
    calc ‖(((Int.sign w.im : ℤ)) : ℂ) - (((Int.sign z.re : ℤ)) : ℂ)‖
        ≤ ‖(((Int.sign w.im : ℤ)) : ℂ)‖ + ‖(((Int.sign z.re : ℤ)) : ℂ)‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := add_le_add h1 h2
      _ = 2 := by norm_num
  have hsv : ‖((((Int.sign w.im - Int.sign z.re : ℤ))) : ℂ)‖ ≤ 2 := by
    simpa only [Int.cast_sub] using hsv0
  have hm : ‖(1 / 2 : ℂ) * (HilbertInf w.re w.im : ℂ)
      * ((((Int.sign w.im - Int.sign z.re : ℤ))) : ℂ)
      * (((((Int.sign ((w * z).re) : ℤ)) : ℂ)) - KTrunc ĉ Kz w z)‖ ≤ D := by
    rw [norm_mul, norm_mul, norm_mul, norm_two_inv, norm_hilb]
    have h1 : (1 / 2 : ℝ) * 1 * ‖((((Int.sign w.im - Int.sign z.re : ℤ))) : ℂ)‖ ≤ 1 := by
      nlinarith [hsv, norm_nonneg ((((Int.sign w.im - Int.sign z.re : ℤ))) : ℂ)]
    calc (1 / 2) * 1 * ‖((((Int.sign w.im - Int.sign z.re : ℤ))) : ℂ)‖
          * ‖(((Int.sign ((w * z).re) : ℤ)) : ℂ) - KTrunc ĉ Kz w z‖
        ≤ 1 * D := mul_le_mul h1 h (norm_nonneg _) (by norm_num)
      _ = D := by ring
  rw [KErr, norm_neg, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul]
  calc ‖α w‖ * ‖β z‖ * ‖JKSym w‖ * ‖JKSym z‖ * ‖(DirichletSym w z : ℂ)‖
        * ‖(1 / 2 : ℂ) * (HilbertInf w.re w.im : ℂ)
            * ((((Int.sign w.im - Int.sign z.re : ℤ))) : ℂ)
            * (((((Int.sign ((w * z).re) : ℤ)) : ℂ)) - KTrunc ĉ Kz w z)‖
      ≤ ‖α w‖ * ‖β z‖ * 1 * 1 * 1 * D := by
        gcongr
    _ = ‖α w‖ * ‖β z‖ * D := by ring

/-! ## 7. The truncation bound for a single pair -/

lemma trunc_bound {M N : ℝ} {α β : GaussianInt → ℂ} {ĉ : ℤ → ℂ} {Kz : ℤ} {C1 : ℝ}
    (hKz : Kz = (((truncK M N : ℕ)) : ℤ))
    (hM : 1 ≤ M) (hN : 1 ≤ N)
    (hsw : ∀ w, α w ≠ 0 → Work.FIPlan.IsPrimary w ∧ IsCoprime w.re w.im ∧
      (Work.FIPlan.gnorm w : ℝ) ≤ M)
    (hsz : ∀ z, β z ≠ 0 → Work.FIPlan.IsPrimary z ∧ (Work.FIPlan.gnorm z : ℝ) ≤ N)
    (htr : ∀ (u v : ℂ), u ≠ 0 → v ≠ 0 →
      ‖u‖ * ‖v‖ ≤ ((truncR M N : ℕ) : ℝ) * |(u * v).re| →
      ‖(if 0 < (u * v).re then (1 : ℂ) else -1)
        - ∑ k ∈ Finset.Icc (-(Kz)) Kz, ĉ k * ((u / (‖u‖ : ℂ)) ^ k * (v / (‖v‖ : ℂ)) ^ k)‖
        ≤ C1 * ((truncR M N : ℕ) : ℝ) / ((truncK M N : ℝ) + 1))
    {w z : GaussianInt} (hw : α w ≠ 0) (hz : β z ≠ 0) :
    ‖(((Int.sign ((w * z).re) : ℤ)) : ℂ) - KTrunc ĉ Kz w z‖
      ≤ C1 * ((truncR M N : ℕ) : ℝ) / ((truncK M N : ℝ) + 1) := by
  obtain ⟨hwP, _, _⟩ := hsw w hw
  obtain ⟨hzP, _⟩ := hsz z hz
  have hgnw : (0 : ℝ) < ((Work.FIPlan.gnorm w : ℕ) : ℝ) := by
    have hne : w ≠ 0 := by
      intro h
      exact re_ne_zero_of_primary hwP (by rw [h]; rfl)
    exact_mod_cast Work.FIArea7.gnorm_pos_of_ne_zero hne
  have hgnz : (0 : ℝ) < ((Work.FIPlan.gnorm z : ℕ) : ℝ) := by
    have hne : z ≠ 0 := by
      intro h
      exact re_ne_zero_of_primary hzP (by rw [h]; rfl)
    exact_mod_cast Work.FIArea7.gnorm_pos_of_ne_zero hne
  have hwzc : w.toComplex ≠ 0 := by
    intro h
    have h1 : ‖w.toComplex‖ = 0 := by rw [h, norm_zero]
    rw [norm_toComplex_sqrt] at h1
    exact (ne_of_gt (Real.sqrt_pos_of_pos hgnw)) h1
  have hzzc : z.toComplex ≠ 0 := by
    intro h
    have h1 : ‖z.toComplex‖ = 0 := by rw [h, norm_zero]
    rw [norm_toComplex_sqrt] at h1
    exact (ne_of_gt (Real.sqrt_pos_of_pos hgnz)) h1
  have hroom := room_cond hM hN hsw hsz hw hz
  have h1 : (((Int.sign ((w * z).re) : ℤ)) : ℂ)
      = (if 0 < (((w * z).re : ℤ) : ℝ) then (1 : ℂ) else -1) :=
    int_sign_cast_eq (re_mul_ne_zero hwP hzP)
  have h2 : KTrunc ĉ Kz w z
      = ∑ k ∈ Finset.Icc (-(Kz)) Kz,
          ĉ k * ((w.toComplex / (‖w.toComplex‖ : ℂ)) ^ k
            * (z.toComplex / (‖z.toComplex‖ : ℂ)) ^ k) := rfl
  rw [h1, h2]
  have hres := htr w.toComplex z.toComplex hwzc hzzc hroom
  rw [← GaussianInt.toComplex_mul, ← GaussianInt.intCast_re] at hres
  exact hres

/-! ## 8. FI Proposition 21.4 -/

/-- The truncation index as an integer. -/
def KK (M N : ℝ) : ℤ := (((truncK M N : ℕ)) : ℤ)

/-- The bound of Proposition 21.3. -/
def Bq (C A M N : ℝ) : ℝ :=
  C * (M + N) ^ ((1 : ℝ) / 12) * (M * N) ^ ((11 : ℝ) / 12) * (Real.log (M * N + 2)) ^ A

/-- **FI Proposition 21.4 (21.13)**: the bilinear form `K(M,N) = Σ_w Σ_z α_w β_z [wz]` in the
Jacobi–Kubota symbol satisfies the same bound as the Dirichlet-symbol form of Proposition 21.3,
namely `‖K(M,N)‖ ≤ C·(M+N)^{1/12}·(MN)^{11/12}·(log(MN+2))^A`, for `w` primary primitive and `z`
primary, both coefficients bounded by 1 and supported in the discs `|w|² ≤ M`, `|z|² ≤ N`.

The present result proves `Work.FIArea7.Prop214` (`Submission/Work/FIArea7/Classical172Defs.lean`)
from the hypothesis `h : Work.FIArea7.Prop213` (Prop. 21.3 / (21.10), the Dirichlet-symbol
statement, proved in the separate file `Submission/Work/FIArea7/prop213.lean`).  `[wz]` is
`Work.FIArea7.JKSym (w*z)`, *FI* (20.1): `[z] = i^{(r-1)/2}(s/|r|)` for `z = r + is`, and
`(z/w) = Work.FIArea7.DirichletSym w z = (Re(wz) | |w|²)` is *FI* (19.10).

PROOF ROUTE (*FI* Prop. 21.4, p. 1028 of `REFS/FI_paper_X2Y4.pdf`):
By the multiplier rule *FI* (20.3)/(20.4) (`Work.FIArea7.jksym_mul_rule`; also
`jksym_mul_rule_primary`) one has, for primitive `w, z`,

  `[wz] = ε(w,z)·[w]·[z]·ξ_w(z)`,  `ξ_w(z) = (z/w)`.

(If `wz` is not primitive then `[wz] = 0`, so a non-primitive `w` contributes nothing; the
hypotheses already make `w` primitive.)  The factor `ε(w,z) = ±1` is separated by *FI* (20.15)
together with the Fourier series (20.19) of `t(α) = sign(cos α)`:

  `2ε(w,z)(u,v)_∞ = 1 + sign(vr) − (sign v − sign r)·sign(Re wz)`,
  `sign(Re wz) = Σ_k t̂(k)(wz/|wz|)^k` with `Σ_k |t̂(k)| ≪ log 2R`

(available in the workspace as `Work.FIArea7.exists_squareWave_fourier`, *FI* (20.17)–(20.19); the
series has to be truncated, and the truncation error is controlled by the same (20.18) bound).
Now `sign(Re wz)` is a function of the *product* `wz`, so `(wz/|wz|)^k = (w/|w|)^k·(z/|z|)^k`
factors, and the terms `1`, `sign(vr)`, `sign v − sign r` also separate in `w` and `z` (the last
two via `(20.13)`/`(20.14)`).  Hence `K(M,N)` is a sum of `O(log(MN))` forms of type `Q(M,N)` with
coefficients `α_w[w](w/|w|)^k`, `β_z[z](z/|z|)^k` — still of modulus ≤ 1 and still supported in the
discs — and `h : Work.FIArea7.Prop213` applies to each term. -/
theorem prop214 (h : Work.FIArea7.Prop213) : Work.FIArea7.Prop214 := by
  obtain ⟨C, A, hC, hA, hQ⟩ := h
  obtain ⟨C1, hC1, hsep0⟩ := squareWaveSepTrunc
  refine ⟨2 * C + 2 * (Real.log 8 + 1 / 2) * C1 * C + 625 * C1, A + 1, ?_, ?_, ?_⟩
  · positivity
  · linarith
  · intro M N Rw Rz α β hM hN hα hβ hsw hsz
    have hR2 : 2 ≤ truncR M N := by simp [truncR]
    obtain ⟨ĉ, hĉ1, hĉ2⟩ := hsep0 (truncR M N) hR2
    have hKz : KK M N = (((truncK M N : ℕ)) : ℤ) := rfl
    have htr : ∀ (u v : ℂ), u ≠ 0 → v ≠ 0 →
        ‖u‖ * ‖v‖ ≤ ((truncR M N : ℕ) : ℝ) * |(u * v).re| →
        ‖(if 0 < (u * v).re then (1 : ℂ) else -1)
          - ∑ k ∈ Finset.Icc (-(KK M N)) (KK M N),
              ĉ k * ((u / (‖u‖ : ℂ)) ^ k * (v / (‖v‖ : ℂ)) ^ k)‖
          ≤ C1 * ((truncR M N : ℕ) : ℝ) / ((truncK M N : ℝ) + 1) :=
      fun u v hu hv hr => hĉ2 (truncK M N) u v hu hv hr
    have hpt : ∀ w z : GaussianInt, α w * β z * JKSym (w * z)
        = (KA0 α w * KB0 β z + KAS α w * KBS β z
            + (∑ k ∈ Finset.Icc (-(KK M N)) (KK M N), ĉ k * (KA0k α k w * KBSk β k z))
            - (∑ k ∈ Finset.Icc (-(KK M N)) (KK M N), ĉ k * (KASk α k w * KB0k β k z)))
          * (DirichletSym w z : ℂ) + KErr α β ĉ (KK M N) w z :=
      fun w z => key_pointwise (Kz := KK M N) (C1 := C1) hM hN hKz hsw hsz htr w z
    have hexp : ∀ w z : GaussianInt,
        (KA0 α w * KB0 β z + KAS α w * KBS β z
            + (∑ k ∈ Finset.Icc (-(KK M N)) (KK M N), ĉ k * (KA0k α k w * KBSk β k z))
            - (∑ k ∈ Finset.Icc (-(KK M N)) (KK M N), ĉ k * (KASk α k w * KB0k β k z)))
          * (DirichletSym w z : ℂ)
        = (KA0 α w * KB0 β z) * (DirichletSym w z : ℂ)
          + (KAS α w * KBS β z) * (DirichletSym w z : ℂ)
          + (∑ k ∈ Finset.Icc (-(KK M N)) (KK M N), ĉ k * (KA0k α k w * KBSk β k z))
            * (DirichletSym w z : ℂ)
          - (∑ k ∈ Finset.Icc (-(KK M N)) (KK M N), ĉ k * (KASk α k w * KB0k β k z))
            * (DirichletSym w z : ℂ) := by
      intro w z; ring
    have hS2 : (∑ w ∈ Work.FIPlan.gBox Rw, ∑ z ∈ Work.FIPlan.gBox Rz,
          (∑ k ∈ Finset.Icc (-(KK M N)) (KK M N), ĉ k * (KA0k α k w * KBSk β k z))
            * (DirichletSym w z : ℂ))
        = ∑ k ∈ Finset.Icc (-(KK M N)) (KK M N),
            ĉ k * (QBilin Rw Rz (KA0k α k) (KBSk β k)) := by
      rw [sum_sum_sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      exact qbilin_smul_coeff (ĉ k) (KA0k α k) (KBSk β k)
    have hS1 : (∑ w ∈ Work.FIPlan.gBox Rw, ∑ z ∈ Work.FIPlan.gBox Rz,
          (∑ k ∈ Finset.Icc (-(KK M N)) (KK M N), ĉ k * (KASk α k w * KB0k β k z))
            * (DirichletSym w z : ℂ))
        = ∑ k ∈ Finset.Icc (-(KK M N)) (KK M N),
            ĉ k * (QBilin Rw Rz (KASk α k) (KB0k β k)) := by
      rw [sum_sum_sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      exact qbilin_smul_coeff (ĉ k) (KASk α k) (KB0k β k)
    have hdecomp : KBilin Rw Rz α β
        = QBilin Rw Rz (KA0 α) (KB0 β) + QBilin Rw Rz (KAS α) (KBS β)
          + (∑ k ∈ Finset.Icc (-(KK M N)) (KK M N),
              ĉ k * (QBilin Rw Rz (KA0k α k) (KBSk β k)))
          - (∑ k ∈ Finset.Icc (-(KK M N)) (KK M N),
              ĉ k * (QBilin Rw Rz (KASk α k) (KB0k β k)))
          + (∑ w ∈ Work.FIPlan.gBox Rw, ∑ z ∈ Work.FIPlan.gBox Rz,
              KErr α β ĉ (KK M N) w z) := by
      rw [KBilin]
      rw [show (∑ w ∈ Work.FIPlan.gBox Rw, ∑ z ∈ Work.FIPlan.gBox Rz,
              α w * β z * JKSym (w * z))
          = ∑ w ∈ Work.FIPlan.gBox Rw, ∑ z ∈ Work.FIPlan.gBox Rz,
              ((KA0 α w * KB0 β z + KAS α w * KBS β z
                  + (∑ k ∈ Finset.Icc (-(KK M N)) (KK M N),
                      ĉ k * (KA0k α k w * KBSk β k z))
                  - (∑ k ∈ Finset.Icc (-(KK M N)) (KK M N),
                      ĉ k * (KASk α k w * KB0k β k z)))
                * (DirichletSym w z : ℂ) + KErr α β ĉ (KK M N) w z) from
            Finset.sum_congr rfl (fun w _ => Finset.sum_congr rfl (fun z _ => hpt w z))]
      simp only [hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib]
      rw [hS2, hS1]
      simp only [QBilin]
    have hB1 : ‖QBilin Rw Rz (KA0 α) (KB0 β)‖ ≤ Bq C A M N :=
      hQ M N Rw Rz (KA0 α) (KB0 β) hM hN (norm_KA0_le hα) (norm_KB0_le hβ)
        (fun w hw => KA0_supp hsw hw) (fun z hz => (KB0_supp hsz hz).2)
    have hB2 : ‖QBilin Rw Rz (KAS α) (KBS β)‖ ≤ Bq C A M N :=
      hQ M N Rw Rz (KAS α) (KBS β) hM hN (norm_KAS_le hα) (norm_KBS_le hβ)
        (fun w hw => KAS_supp hsw hw) (fun z hz => (KBS_supp hsz hz).2)
    have hBk0 : ∀ k : ℤ, ‖QBilin Rw Rz (KA0k α k) (KBSk β k)‖ ≤ Bq C A M N :=
      fun k => hQ M N Rw Rz (KA0k α k) (KBSk β k) hM hN (norm_KA0k_le hα k)
        (norm_KBSk_le hβ k) (fun w hw => KA0k_supp hsw k hw)
        (fun z hz => (KBSk_supp hsz k hz).2)
    have hBkS : ∀ k : ℤ, ‖QBilin Rw Rz (KASk α k) (KB0k β k)‖ ≤ Bq C A M N :=
      fun k => hQ M N Rw Rz (KASk α k) (KB0k β k) hM hN (norm_KASk_le hα k)
        (norm_KB0k_le hβ k) (fun w hw => KASk_supp hsw k hw)
        (fun z hz => (KB0k_supp hsz k hz).2)
    have hBqnn : 0 ≤ Bq C A M N := by
      have h1 : 0 < Real.log (M * N + 2) := Real.log_pos (by nlinarith)
      have h2 : 0 < (Real.log (M * N + 2)) ^ A := Real.rpow_pos_of_pos h1 A
      rw [Bq]; positivity
    have hS2b : ‖∑ k ∈ Finset.Icc (-(KK M N)) (KK M N),
          ĉ k * (QBilin Rw Rz (KA0k α k) (KBSk β k))‖
        ≤ (C1 * Real.log (2 * ((truncR M N : ℕ) : ℝ))) * Bq C A M N := by
      calc ‖∑ k ∈ Finset.Icc (-(KK M N)) (KK M N),
              ĉ k * (QBilin Rw Rz (KA0k α k) (KBSk β k))‖
          ≤ ∑ k ∈ Finset.Icc (-(KK M N)) (KK M N),
              ‖ĉ k * (QBilin Rw Rz (KA0k α k) (KBSk β k))‖ := norm_sum_le _ _
        _ ≤ ∑ k ∈ Finset.Icc (-(KK M N)) (KK M N), ‖ĉ k‖ * Bq C A M N :=
            Finset.sum_le_sum (fun k _ => by
              rw [norm_mul]
              exact mul_le_mul_of_nonneg_left (hBk0 k) (norm_nonneg _))
        _ = (∑ k ∈ Finset.Icc (-(KK M N)) (KK M N), ‖ĉ k‖) * Bq C A M N := by
            rw [Finset.sum_mul]
        _ ≤ (C1 * Real.log (2 * ((truncR M N : ℕ) : ℝ))) * Bq C A M N :=
            mul_le_mul_of_nonneg_right (hĉ1 _) hBqnn
    have hS1b : ‖∑ k ∈ Finset.Icc (-(KK M N)) (KK M N),
          ĉ k * (QBilin Rw Rz (KASk α k) (KB0k β k))‖
        ≤ (C1 * Real.log (2 * ((truncR M N : ℕ) : ℝ))) * Bq C A M N := by
      calc ‖∑ k ∈ Finset.Icc (-(KK M N)) (KK M N),
              ĉ k * (QBilin Rw Rz (KASk α k) (KB0k β k))‖
          ≤ ∑ k ∈ Finset.Icc (-(KK M N)) (KK M N),
              ‖ĉ k * (QBilin Rw Rz (KASk α k) (KB0k β k))‖ := norm_sum_le _ _
        _ ≤ ∑ k ∈ Finset.Icc (-(KK M N)) (KK M N), ‖ĉ k‖ * Bq C A M N :=
            Finset.sum_le_sum (fun k _ => by
              rw [norm_mul]
              exact mul_le_mul_of_nonneg_left (hBkS k) (norm_nonneg _))
        _ = (∑ k ∈ Finset.Icc (-(KK M N)) (KK M N), ‖ĉ k‖) * Bq C A M N := by
            rw [Finset.sum_mul]
        _ ≤ (C1 * Real.log (2 * ((truncR M N : ℕ) : ℝ))) * Bq C A M N :=
            mul_le_mul_of_nonneg_right (hĉ1 _) hBqnn
    have hKErrB : ∀ w z : GaussianInt, ‖KErr α β ĉ (KK M N) w z‖
        ≤ ‖α w‖ * ‖β z‖ * (C1 * ((truncR M N : ℕ) : ℝ) / ((truncK M N : ℝ) + 1)) := by
      intro w z
      by_cases h0 : α w * β z = 0
      · have hz : KErr α β ĉ (KK M N) w z = 0 := by
          unfold KErr
          rw [h0]; simp
        rw [hz, norm_zero]; positivity
      · have hαw : α w ≠ 0 := fun hh => h0 (by rw [hh, zero_mul])
        have hβz : β z ≠ 0 := fun hh => h0 (by rw [hh, mul_zero])
        exact norm_KErr_le (trunc_bound hKz hM hN hsw hsz htr hαw hβz)
    have hcountα : ∑ w ∈ Work.FIPlan.gBox Rw, ‖α w‖ ≤ 25 * M ^ 2 := by
      have hsub : (Work.FIPlan.gBox Rw).filter (fun w => α w ≠ 0)
          ⊆ (Work.FIPlan.gBox Rw).filter (fun w => (Work.FIPlan.gnorm w : ℝ) ≤ M) := by
        intro x hx
        simp only [Finset.mem_filter] at hx ⊢
        exact ⟨hx.1, (hsw x hx.2).2.2⟩
      calc ∑ w ∈ Work.FIPlan.gBox Rw, ‖α w‖
          = ∑ w ∈ (Work.FIPlan.gBox Rw).filter (fun w => α w ≠ 0), ‖α w‖ := by
            symm
            exact Finset.sum_filter_of_ne (fun x hx hh => fun h0' => hh (by rw [h0', norm_zero]))
        _ ≤ ∑ w ∈ (Work.FIPlan.gBox Rw).filter (fun w => α w ≠ 0), (1 : ℝ) :=
            Finset.sum_le_sum (fun x hx => hα x)
        _ = (((Work.FIPlan.gBox Rw).filter (fun w => α w ≠ 0)).card : ℝ) := by simp
        _ ≤ (((Work.FIPlan.gBox Rw).filter
                (fun w => (Work.FIPlan.gnorm w : ℝ) ≤ M)).card : ℝ) := by
            exact_mod_cast Finset.card_le_card hsub
        _ ≤ 25 * M ^ 2 := cardFilterGnormLe Rw M hM
    have hcountβ : ∑ z ∈ Work.FIPlan.gBox Rz, ‖β z‖ ≤ 25 * N ^ 2 := by
      have hsub : (Work.FIPlan.gBox Rz).filter (fun z => β z ≠ 0)
          ⊆ (Work.FIPlan.gBox Rz).filter (fun z => (Work.FIPlan.gnorm z : ℝ) ≤ N) := by
        intro x hx
        simp only [Finset.mem_filter] at hx ⊢
        exact ⟨hx.1, (hsz x hx.2).2⟩
      calc ∑ z ∈ Work.FIPlan.gBox Rz, ‖β z‖
          = ∑ z ∈ (Work.FIPlan.gBox Rz).filter (fun z => β z ≠ 0), ‖β z‖ := by
            symm
            exact Finset.sum_filter_of_ne (fun x hx hh => fun h0' => hh (by rw [h0', norm_zero]))
        _ ≤ ∑ z ∈ (Work.FIPlan.gBox Rz).filter (fun z => β z ≠ 0), (1 : ℝ) :=
            Finset.sum_le_sum (fun x hx => hβ x)
        _ = (((Work.FIPlan.gBox Rz).filter (fun z => β z ≠ 0)).card : ℝ) := by simp
        _ ≤ (((Work.FIPlan.gBox Rz).filter
                (fun z => (Work.FIPlan.gnorm z : ℝ) ≤ N)).card : ℝ) := by
            exact_mod_cast Finset.card_le_card hsub
        _ ≤ 25 * N ^ 2 := cardFilterGnormLe Rz N hN
    have hsumErr : ∑ w ∈ Work.FIPlan.gBox Rw, ∑ z ∈ Work.FIPlan.gBox Rz,
          ‖KErr α β ĉ (KK M N) w z‖
        ≤ (C1 * ((truncR M N : ℕ) : ℝ) / ((truncK M N : ℝ) + 1)) * (25 * M ^ 2)
          * (25 * N ^ 2) := by
      calc ∑ w ∈ Work.FIPlan.gBox Rw, ∑ z ∈ Work.FIPlan.gBox Rz,
              ‖KErr α β ĉ (KK M N) w z‖
          ≤ ∑ w ∈ Work.FIPlan.gBox Rw, ∑ z ∈ Work.FIPlan.gBox Rz,
              ‖α w‖ * ‖β z‖
                * (C1 * ((truncR M N : ℕ) : ℝ) / ((truncK M N : ℝ) + 1)) :=
            Finset.sum_le_sum (fun w _ => Finset.sum_le_sum (fun z _ => hKErrB w z))
        _ = ∑ w ∈ Work.FIPlan.gBox Rw, ‖α w‖
              * (∑ z ∈ Work.FIPlan.gBox Rz,
                  ‖β z‖ * (C1 * ((truncR M N : ℕ) : ℝ) / ((truncK M N : ℝ) + 1))) := by
            apply Finset.sum_congr rfl; intro w hw
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl; intro z hz
            ring
        _ = (∑ w ∈ Work.FIPlan.gBox Rw, ‖α w‖)
              * ((∑ z ∈ Work.FIPlan.gBox Rz, ‖β z‖)
                * (C1 * ((truncR M N : ℕ) : ℝ) / ((truncK M N : ℝ) + 1))) := by
            rw [Finset.sum_mul, Finset.sum_mul]
        _ = (C1 * ((truncR M N : ℕ) : ℝ) / ((truncK M N : ℝ) + 1))
              * (∑ w ∈ Work.FIPlan.gBox Rw, ‖α w‖)
              * (∑ z ∈ Work.FIPlan.gBox Rz, ‖β z‖) := by ring
        _ ≤ (C1 * ((truncR M N : ℕ) : ℝ) / ((truncK M N : ℝ) + 1)) * (25 * M ^ 2)
              * (25 * N ^ 2) := by
            gcongr
    have h625 : (C1 * ((truncR M N : ℕ) : ℝ) / ((truncK M N : ℝ) + 1)) * (25 * M ^ 2)
        * (25 * N ^ 2) ≤ 625 * C1 := by
      have hden : (0 : ℝ) < ((truncK M N : ℝ)) + 1 := by positivity
      have hceil : ((truncR M N : ℕ) : ℝ) * M ^ 2 * N ^ 2 ≤ ((truncK M N : ℝ)) + 1 := by
        have h := Nat.le_ceil (((truncR M N : ℕ) : ℝ) * M ^ 2 * N ^ 2)
        simp only [truncK] at h ⊢
        linarith
      have hdiv : ((truncR M N : ℕ) : ℝ) * M ^ 2 * N ^ 2 / ((truncK M N : ℝ) + 1) ≤ 1 :=
        (div_le_one hden).mpr hceil
      calc (C1 * ((truncR M N : ℕ) : ℝ) / ((truncK M N : ℝ) + 1)) * (25 * M ^ 2)
            * (25 * N ^ 2)
          = 625 * C1
              * (((truncR M N : ℕ) : ℝ) * M ^ 2 * N ^ 2 / ((truncK M N : ℝ) + 1)) := by
            ring_nf
        _ ≤ 625 * C1 * 1 := mul_le_mul_of_nonneg_left hdiv (by positivity)
        _ = 625 * C1 := by ring
    have hE : ‖∑ w ∈ Work.FIPlan.gBox Rw, ∑ z ∈ Work.FIPlan.gBox Rz,
          KErr α β ĉ (KK M N) w z‖ ≤ 625 * C1 := by
      have h1 : ‖∑ w ∈ Work.FIPlan.gBox Rw, ∑ z ∈ Work.FIPlan.gBox Rz,
            KErr α β ĉ (KK M N) w z‖
          ≤ ∑ w ∈ Work.FIPlan.gBox Rw, ∑ z ∈ Work.FIPlan.gBox Rz,
              ‖KErr α β ĉ (KK M N) w z‖ := by
        calc ‖∑ w ∈ Work.FIPlan.gBox Rw, ∑ z ∈ Work.FIPlan.gBox Rz,
                KErr α β ĉ (KK M N) w z‖
            ≤ ∑ w ∈ Work.FIPlan.gBox Rw, ‖∑ z ∈ Work.FIPlan.gBox Rz,
                KErr α β ĉ (KK M N) w z‖ := norm_sum_le _ _
          _ ≤ ∑ w ∈ Work.FIPlan.gBox Rw, ∑ z ∈ Work.FIPlan.gBox Rz,
                ‖KErr α β ĉ (KK M N) w z‖ :=
              Finset.sum_le_sum (fun w _ => norm_sum_le _ _)
      exact le_trans h1 (le_trans hsumErr h625)
    have hmain : ‖KBilin Rw Rz α β‖
        ≤ 2 * Bq C A M N + 2 * (C1 * Real.log (2 * ((truncR M N : ℕ) : ℝ))) * Bq C A M N
          + 625 * C1 := by
      calc ‖KBilin Rw Rz α β‖
          = ‖QBilin Rw Rz (KA0 α) (KB0 β) + QBilin Rw Rz (KAS α) (KBS β)
              + (∑ k ∈ Finset.Icc (-(KK M N)) (KK M N),
                  ĉ k * (QBilin Rw Rz (KA0k α k) (KBSk β k)))
              - (∑ k ∈ Finset.Icc (-(KK M N)) (KK M N),
                  ĉ k * (QBilin Rw Rz (KASk α k) (KB0k β k)))
              + (∑ w ∈ Work.FIPlan.gBox Rw, ∑ z ∈ Work.FIPlan.gBox Rz,
                  KErr α β ĉ (KK M N) w z)‖ := by rw [hdecomp]
        _ ≤ ‖QBilin Rw Rz (KA0 α) (KB0 β)‖ + ‖QBilin Rw Rz (KAS α) (KBS β)‖
              + ‖∑ k ∈ Finset.Icc (-(KK M N)) (KK M N),
                  ĉ k * (QBilin Rw Rz (KA0k α k) (KBSk β k))‖
              + ‖∑ k ∈ Finset.Icc (-(KK M N)) (KK M N),
                  ĉ k * (QBilin Rw Rz (KASk α k) (KB0k β k))‖
              + ‖∑ w ∈ Work.FIPlan.gBox Rw, ∑ z ∈ Work.FIPlan.gBox Rz,
                  KErr α β ĉ (KK M N) w z‖ := by
            have e1 := norm_add_le (QBilin Rw Rz (KA0 α) (KB0 β) + QBilin Rw Rz (KAS α) (KBS β)
                + (∑ k ∈ Finset.Icc (-(KK M N)) (KK M N),
                    ĉ k * (QBilin Rw Rz (KA0k α k) (KBSk β k)))
                - (∑ k ∈ Finset.Icc (-(KK M N)) (KK M N),
                    ĉ k * (QBilin Rw Rz (KASk α k) (KB0k β k))))
                (∑ w ∈ Work.FIPlan.gBox Rw, ∑ z ∈ Work.FIPlan.gBox Rz,
                  KErr α β ĉ (KK M N) w z)
            have e2 := norm_sub_le (QBilin Rw Rz (KA0 α) (KB0 β) + QBilin Rw Rz (KAS α) (KBS β)
                + (∑ k ∈ Finset.Icc (-(KK M N)) (KK M N),
                    ĉ k * (QBilin Rw Rz (KA0k α k) (KBSk β k))))
                (∑ k ∈ Finset.Icc (-(KK M N)) (KK M N),
                    ĉ k * (QBilin Rw Rz (KASk α k) (KB0k β k)))
            have e3 := norm_add_le (QBilin Rw Rz (KA0 α) (KB0 β) + QBilin Rw Rz (KAS α) (KBS β))
                (∑ k ∈ Finset.Icc (-(KK M N)) (KK M N),
                    ĉ k * (QBilin Rw Rz (KA0k α k) (KBSk β k)))
            have e4 := norm_add_le (QBilin Rw Rz (KA0 α) (KB0 β)) (QBilin Rw Rz (KAS α) (KBS β))
            linarith
        _ ≤ Bq C A M N + Bq C A M N
              + (C1 * Real.log (2 * ((truncR M N : ℕ) : ℝ))) * Bq C A M N
              + (C1 * Real.log (2 * ((truncR M N : ℕ) : ℝ))) * Bq C A M N + 625 * C1 := by
            gcongr
        _ = 2 * Bq C A M N + 2 * (C1 * Real.log (2 * ((truncR M N : ℕ) : ℝ))) * Bq C A M N
              + 625 * C1 := by ring
    have hfinal : 2 * Bq C A M N
          + 2 * (C1 * Real.log (2 * ((truncR M N : ℕ) : ℝ))) * Bq C A M N + 625 * C1
        ≤ Bq (2 * C + 2 * (Real.log 8 + 1 / 2) * C1 * C + 625 * C1) (A + 1) M N := by
      simp only [Bq]
      exact prop214Final C A C1 (625 * C1) hC hA hC1 M N hM hN le_rfl
    exact le_trans hmain hfinal

end

end Work.FIArea7
