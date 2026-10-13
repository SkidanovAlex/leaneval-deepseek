import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Order.Interval.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# A `C^∞` bump with prescribed first moments

For `a < b` we construct a `C^∞` function `χ` with compact support in the open interval `(a,b)`,
whose integral over `(a,b)` equals `1` and whose first two moments against `deriv χ` are
`∫ χ' = 0` and `∫ t · χ'(t) = -1`.

Both derivative identities are automatic for *any* bump of total mass one supported in `(a,b)`:
`∫ χ' = χ b - χ a = 0` and `∫ t χ'(t) = b χ(b) - a χ(a) - ∫ χ = -1` (integration by parts).
So it suffices to exhibit a nonnegative `C^∞` bump of positive mass supported in a strictly
smaller closed interval `[lo, hi] ⊆ (a,b)` and normalise it.

The building block is the elementary bump `g x = smoothTransition x * smoothTransition (1 - x)`,
which is `C^∞`, nonnegative, positive exactly on `(0,1)` and vanishes off `(0,1)`; its integral
`M = ∫ g` is positive.  We then set
`χ t = ((hi - lo) * M)⁻¹ * g ((t - lo) / (hi - lo))`
with `lo = a + (b-a)/4` and `hi = b - (b-a)/4`, so that `a < lo < hi < b` and
`∫ χ = ((hi-lo)*M)⁻¹ * ((hi-lo) * M) = 1`.
-/

namespace Work.FTS.StrongEps.EComparison

open MeasureTheory Set
open scoped Topology ContDiff Interval

/-- The elementary smooth bump `x ↦ smoothTransition x * smoothTransition (1 - x)`: it is `C^∞`,
nonnegative, and positive exactly on `(0,1)` (it vanishes on `(-∞,0] ∪ [1,∞)`). -/
private noncomputable def bumpG (x : ℝ) : ℝ :=
  Real.smoothTransition x * Real.smoothTransition (1 - x)

private lemma bumpG_contDiff : ContDiff ℝ ∞ bumpG := by
  have h1 : ContDiff ℝ ∞ fun x : ℝ => Real.smoothTransition x :=
    Real.smoothTransition.contDiff
  have h2 : ContDiff ℝ ∞ fun x : ℝ => Real.smoothTransition (1 - x) :=
    Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id)
  exact h1.mul h2

private lemma bumpG_nonneg (x : ℝ) : 0 ≤ bumpG x :=
  mul_nonneg (Real.smoothTransition.nonneg x) (Real.smoothTransition.nonneg (1 - x))

private lemma bumpG_pos_half : bumpG (1 / 2) ≠ 0 := by
  have h1 : 0 < Real.smoothTransition (1 / 2 : ℝ) := Real.smoothTransition.pos_of_pos (by norm_num)
  have h2 : 0 < Real.smoothTransition (1 - 1 / 2 : ℝ) :=
    Real.smoothTransition.pos_of_pos (by norm_num)
  exact ne_of_gt (by simpa [bumpG] using mul_pos h1 h2)

private lemma bumpG_support_subset : Function.support bumpG ⊆ Set.Ioo 0 1 := by
  intro x hx
  rw [Function.mem_support] at hx
  have hx1 : Real.smoothTransition x ≠ 0 := fun h => hx (by rw [bumpG, h, zero_mul])
  have hx2 : Real.smoothTransition (1 - x) ≠ 0 := fun h => hx (by rw [bumpG, h, mul_zero])
  exact ⟨lt_of_not_ge fun h => hx1 (Real.smoothTransition.zero_iff_nonpos.mpr h),
    lt_of_not_ge fun h => hx2 (Real.smoothTransition.zero_iff_nonpos.mpr (by linarith))⟩

private lemma bumpG_support_subset_Ioc : Function.support bumpG ⊆ Set.Ioc 0 1 :=
  fun _ hx => ⟨(bumpG_support_subset hx).1, (bumpG_support_subset hx).2.le⟩

private lemma bumpG_tsupport_subset : tsupport bumpG ⊆ Set.Icc 0 1 :=
  closure_minimal
    (fun _ hx => ⟨(bumpG_support_subset hx).1.le, (bumpG_support_subset hx).2.le⟩)
    isClosed_Icc

private lemma bumpG_hasCompactSupport : HasCompactSupport bumpG :=
  (isCompact_Icc (a := (0 : ℝ)) (b := 1)).of_isClosed_subset (isClosed_tsupport bumpG)
    bumpG_tsupport_subset

private lemma bumpG_continuous : Continuous bumpG := bumpG_contDiff.continuous

private lemma bumpG_integral_pos : 0 < ∫ x, bumpG x :=
  bumpG_continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    bumpG_hasCompactSupport bumpG_nonneg bumpG_pos_half

private lemma bumpG_integral_interval : (∫ u in (0 : ℝ)..1, bumpG u) = ∫ u, bumpG u :=
  intervalIntegral.integral_eq_integral_of_support_subset bumpG_support_subset_Ioc

/-- The affine change of variables for the elementary bump: translating its argument by `A` and
rescaling by `B - A` multiplies the integral by `B - A`. -/
private lemma bumpG_integral_affine {A B : ℝ} (hAB : A < B) :
    ∫ t : ℝ, bumpG ((t - A) / (B - A)) = (B - A) * ∫ u, bumpG u := by
  have hBA : (0 : ℝ) < B - A := sub_pos.mpr hAB
  have hBA' : B - A ≠ 0 := ne_of_gt hBA
  have hsupp : Function.support (fun t : ℝ => bumpG ((t - A) / (B - A))) ⊆ Set.Ioc A B := by
    intro t ht
    rw [Function.mem_support] at ht
    obtain ⟨h1, h2⟩ := bumpG_support_subset ht
    rw [div_pos_iff_of_pos_right hBA] at h1
    rw [div_lt_one hBA] at h2
    exact ⟨by linarith, by linarith⟩
  calc ∫ t : ℝ, bumpG ((t - A) / (B - A))
      = ∫ t in A..B, bumpG ((t - A) / (B - A)) :=
        (intervalIntegral.integral_eq_integral_of_support_subset hsupp).symm
    _ = ∫ s in (0 : ℝ)..(B - A), bumpG (s / (B - A)) := by
        rw [intervalIntegral.integral_comp_sub_right (f := fun s : ℝ => bumpG (s / (B - A)))
          (a := A) (b := B) (d := A)]
        simp only [sub_self]
    _ = (B - A) * ∫ u in (0 : ℝ)..1, bumpG u := by
        rw [intervalIntegral.integral_comp_div (f := bumpG) (a := (0 : ℝ)) (b := B - A) hBA']
        rw [zero_div, div_self hBA', smul_eq_mul]
    _ = (B - A) * ∫ u, bumpG u := by rw [bumpG_integral_interval]

/-- The mass of the elementary bump. -/
private noncomputable def bumpM : ℝ := ∫ u, bumpG u

private lemma bumpM_pos : 0 < bumpM := bumpG_integral_pos

/-- Left endpoint of the support interval: `a + (b-a)/4`. -/
private noncomputable def bumpLo (a b : ℝ) : ℝ := a + (b - a) / 4

/-- Right endpoint of the support interval: `b - (b-a)/4`. -/
private noncomputable def bumpHi (a b : ℝ) : ℝ := b - (b - a) / 4

/-- The width of the support interval. -/
private noncomputable def bumpW (a b : ℝ) : ℝ := bumpHi a b - bumpLo a b

private lemma bumpLo_lt_bumpHi {a b : ℝ} (hab : a < b) : bumpLo a b < bumpHi a b := by
  have h : 0 < b - a := sub_pos.mpr hab
  simp only [bumpLo, bumpHi]
  linarith

private lemma lt_bumpLo {a b : ℝ} (hab : a < b) : a < bumpLo a b := by
  have h : 0 < b - a := sub_pos.mpr hab
  simp only [bumpLo]
  linarith

private lemma bumpHi_lt {a b : ℝ} (hab : a < b) : bumpHi a b < b := by
  have h : 0 < b - a := sub_pos.mpr hab
  simp only [bumpHi]
  linarith

private lemma bumpW_pos {a b : ℝ} (hab : a < b) : 0 < bumpW a b := by
  have h : bumpLo a b < bumpHi a b := bumpLo_lt_bumpHi hab
  simp only [bumpW]
  linarith

private lemma bumpW_ne_zero {a b : ℝ} (hab : a < b) : bumpW a b ≠ 0 := ne_of_gt (bumpW_pos hab)

/-- The bump: a normalised, translated and rescaled copy of the elementary bump, whose support
lies in `(bumpLo a b, bumpHi a b) ⊂ (a,b)`. -/
private noncomputable def bumpChi (a b : ℝ) : ℝ → ℝ :=
  fun t => (bumpW a b * bumpM)⁻¹ * bumpG ((t - bumpLo a b) / bumpW a b)

private lemma bumpChi_contDiff (a b : ℝ) : ContDiff ℝ ∞ (bumpChi a b) := by
  have h : ContDiff ℝ ∞ fun t : ℝ => (t - bumpLo a b) / bumpW a b :=
    (contDiff_id.sub contDiff_const).div_const _
  exact contDiff_const.mul (bumpG_contDiff.comp h)

private lemma bumpChi_support_subset_lo_hi {a b : ℝ} (hab : a < b) :
    Function.support (bumpChi a b) ⊆ Set.Ioo (bumpLo a b) (bumpHi a b) := by
  intro t ht
  rw [Function.mem_support] at ht
  have hg : bumpG ((t - bumpLo a b) / bumpW a b) ≠ 0 := by
    intro h
    exact ht (by rw [bumpChi, h, mul_zero])
  obtain ⟨h1, h2⟩ := bumpG_support_subset hg
  have hw : 0 < bumpW a b := bumpW_pos hab
  rw [div_pos_iff_of_pos_right hw] at h1
  rw [div_lt_one hw] at h2
  simp only [bumpW] at h2
  exact ⟨by linarith, by linarith⟩

private lemma bumpChi_support_subset {a b : ℝ} (hab : a < b) :
    Function.support (bumpChi a b) ⊆ Set.Ioo a b := by
  intro t ht
  obtain ⟨h1, h2⟩ := bumpChi_support_subset_lo_hi hab ht
  exact ⟨lt_trans (lt_bumpLo hab) h1, lt_trans h2 (bumpHi_lt hab)⟩

private lemma bumpChi_tsupport_subset {a b : ℝ} (hab : a < b) :
    tsupport (bumpChi a b) ⊆ Set.Ioo a b := by
  have hcl : tsupport (bumpChi a b) ⊆ Set.Icc (bumpLo a b) (bumpHi a b) :=
    closure_minimal
      (fun x hx => ⟨(bumpChi_support_subset_lo_hi hab hx).1.le,
        (bumpChi_support_subset_lo_hi hab hx).2.le⟩)
      isClosed_Icc
  intro x hx
  obtain ⟨h1, h2⟩ := hcl hx
  exact ⟨lt_of_lt_of_le (lt_bumpLo hab) h1, lt_of_le_of_lt h2 (bumpHi_lt hab)⟩

private lemma bumpChi_hasCompactSupport {a b : ℝ} (hab : a < b) :
    HasCompactSupport (bumpChi a b) :=
  (isCompact_Icc (a := a) (b := b)).of_isClosed_subset (isClosed_tsupport _)
    (fun _ hx => Set.Ioo_subset_Icc_self (bumpChi_tsupport_subset hab hx))

private lemma bumpChi_support_subset_Ioc {a b : ℝ} (hab : a < b) :
    Function.support (bumpChi a b) ⊆ Set.Ioc a b :=
  fun _ hx => ⟨(bumpChi_support_subset hab hx).1, (bumpChi_support_subset hab hx).2.le⟩

private lemma bumpChi_zero_of_notMem_tsupport {a b : ℝ} {t : ℝ}
    (ht : t ∉ tsupport (bumpChi a b)) : bumpChi a b t = 0 := by
  by_contra h
  exact ht (subset_tsupport (bumpChi a b) (Function.mem_support.mpr h))

private lemma bumpChi_zero_at_left {a b : ℝ} (hab : a < b) : bumpChi a b a = 0 :=
  bumpChi_zero_of_notMem_tsupport fun h => absurd (bumpChi_tsupport_subset hab h).1 (lt_irrefl a)

private lemma bumpChi_zero_at_right {a b : ℝ} (hab : a < b) : bumpChi a b b = 0 :=
  bumpChi_zero_of_notMem_tsupport fun h => absurd (bumpChi_tsupport_subset hab h).2 (lt_irrefl b)

private lemma bumpChi_integral {a b : ℝ} (hab : a < b) : (∫ t in a..b, bumpChi a b t) = 1 := by
  rw [intervalIntegral.integral_eq_integral_of_support_subset (bumpChi_support_subset_Ioc hab)]
  have haff := bumpG_integral_affine (A := bumpLo a b) (B := bumpHi a b) (bumpLo_lt_bumpHi hab)
  have hval : (∫ t : ℝ, bumpG ((t - bumpLo a b) / bumpW a b)) = bumpW a b * bumpM := by
    simpa [bumpW, bumpM] using haff
  have hmul : (bumpW a b * bumpM)⁻¹ * (bumpW a b * bumpM) = 1 :=
    inv_mul_cancel₀ (mul_ne_zero (bumpW_ne_zero hab) (ne_of_gt bumpM_pos))
  simp only [bumpChi]
  rw [integral_const_mul, hval, hmul]

private lemma bumpChi_differentiableAt {a b : ℝ} (x : ℝ) :
    DifferentiableAt ℝ (bumpChi a b) x := by
  have h : Differentiable ℝ (bumpChi a b) :=
    (contDiff_infty.mp (bumpChi_contDiff a b) 1).differentiable (by norm_num)
  exact h.differentiableAt

private lemma bumpChi_continuous_deriv {a b : ℝ} : Continuous (deriv (bumpChi a b)) :=
  (contDiff_infty.mp (bumpChi_contDiff a b) 1).continuous_deriv le_rfl

private lemma bumpChi_deriv_integral {a b : ℝ} (hab : a < b) :
    (∫ t in a..b, deriv (bumpChi a b) t) = 0 := by
  rw [intervalIntegral.integral_deriv_eq_sub
    (fun x _ => bumpChi_differentiableAt x) (bumpChi_continuous_deriv.intervalIntegrable a b),
    bumpChi_zero_at_right hab, bumpChi_zero_at_left hab, sub_zero]

private lemma bumpChi_moment {a b : ℝ} (hab : a < b) :
    (∫ t in a..b, t * deriv (bumpChi a b) t) = -1 := by
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun t : ℝ => t) (v := bumpChi a b) (u' := fun _ => (1 : ℝ))
    (v' := deriv (bumpChi a b)) (a := a) (b := b)
    (fun x _ => hasDerivAt_id x) (fun x _ => (bumpChi_differentiableAt x).hasDerivAt)
    intervalIntegrable_const (bumpChi_continuous_deriv.intervalIntegrable a b)
  have hint : (∫ x in a..b, (1 : ℝ) * bumpChi a b x) = 1 := by
    rw [intervalIntegral.integral_congr (fun x _ => one_mul (bumpChi a b x))]
    exact bumpChi_integral hab
  rw [bumpChi_zero_at_right hab, bumpChi_zero_at_left hab, hint] at hIBP
  simp only [mul_zero, sub_zero] at hIBP
  linarith [hIBP]

open MeasureTheory Set in
open scoped Topology ContDiff Interval in
theorem existsBumpMoments {a b : ℝ} (hab : a < b) :
    ∃ χ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ Set.Ioo a b ∧
      (∫ t in a..b, χ t) = 1 ∧ (∫ t in a..b, deriv χ t) = 0 ∧
      (∫ t in a..b, t * deriv χ t) = -1 :=
  ⟨bumpChi a b, bumpChi_contDiff a b, bumpChi_hasCompactSupport hab, bumpChi_tsupport_subset hab,
    bumpChi_integral hab, bumpChi_deriv_integral hab, bumpChi_moment hab⟩

end Work.FTS.StrongEps.EComparison
