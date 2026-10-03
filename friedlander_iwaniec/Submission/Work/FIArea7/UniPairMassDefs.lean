/-
# `Submission.Work.FIArea7.UniPairMassDefs` — the vocabulary of the coprimality-guard removal

The difference `uniModeSum − uniModeSumFree` is supported on the pairs `(z₁,z₂)` of the box that
are **not coprime**; on such a pair the `unitInd` factors (kept in both objects) pin the
`ω`-detection to a single class, so `‖omegaDetect‖ ≤ 1`
(`Work.FIArea7.norm_omegaDetect_le_one`), and the detection congruence moreover forces
`4be ∣ |Δ(z₁,z₂)|` (`omegaDetect_eq_zero_of_not_dvd`).  Combining this with the pointwise bounds
`‖ε z‖ = 1` (the reflection-sign hypothesis on the polar box), `‖betaPrime β z‖ ≤ ‖β z‖` and
`‖uniPow z k‖ = 1` gives the per-`(b,e,k)` estimate `norm_uniModeChar_sub_free_le`, whose
right-hand side is the *weighted non-coprime pair mass* `uniMode_pairInner` / `uniMode_pairMass`.

The estimate of `uniMode_pairMass` (the Möbius/`π`-grouping argument of *FI* §17, `NOTES.md`
§55–56) is the separate lemma `Work.FIArea7.uniMode_pairMass_le`.
-/
import Mathlib
import Submission.Work.FIArea7.GuardRemoval6
import Submission.Work.FIArea7.UniMollify6
import Submission.Work.FIArea7.norm_omegaDetect_le_one

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. The reflection sign on the diagonal, and `‖ε z‖ = 1` -/

/-- `reflSign z z = 1` as soon as `z.re ≠ 0` (the first branch of its definition). -/
lemma reflSign_self {z : GaussianInt} (hz : z.re ≠ 0) : reflSign z z = 1 := by
  rw [reflSign, if_pos (mul_self_pos.mpr hz)]

/-- A primary Gaussian integer has odd (hence non-zero) real part. -/
lemma IsPrimary.re_ne_zero {z : GaussianInt} (h : Work.FIPlan.IsPrimary z) : z.re ≠ 0 := by
  intro h0
  have hodd : Odd z.re := h.1
  rw [h0] at hodd
  obtain ⟨k, hk⟩ := hodd
  omega

lemma InPolarBox.re_ne_zero {Pa : Work.FITop.Params} {φ : ℝ} {z : GaussianInt}
    (hz : Work.FITop3.InPolarBox Pa φ z) : z.re ≠ 0 :=
  IsPrimary.re_ne_zero hz.1

/-- **`ε` is a sign on the polar box.**  From the hypothesis `reflSign z₁z₂ = ε z₁·ε z₂` at
`z₁ = z₂ = z` and `reflSign z z = 1` (`z` is primary on the polar box), `(ε z)² = 1`. -/
lemma norm_eps_eq_one {Pa : Work.FITop.Params} {φ : ℝ} {ε : GaussianInt → ℤ}
    (hε : ∀ z1 z2 : GaussianInt, Work.FITop3.InPolarBox Pa φ z1 →
      Work.FITop3.InPolarBox Pa φ z2 → reflSign z1 z2 = ε z1 * ε z2)
    {z : GaussianInt} (hz : Work.FITop3.InPolarBox Pa φ z) : ‖((ε z : ℤ) : ℂ)‖ = 1 := by
  have h1 : reflSign z z = 1 := reflSign_self (InPolarBox.re_ne_zero hz)
  have h2 : ε z * ε z = 1 := by rw [← h1]; exact (hε z z hz hz).symm
  have h3 : (ε z : ℤ) * (ε z : ℤ) = 1 := h2
  rw [Complex.norm_intCast]
  have h4 : |((ε z : ℤ) : ℝ)| * |((ε z : ℤ) : ℝ)| = 1 := by
    rw [← abs_mul]
    have h5 : ((ε z : ℤ) : ℝ) * ((ε z : ℤ) : ℝ) = 1 := by
      rw [← Int.cast_mul, h3]; norm_num
    rw [h5, abs_one]
  have h6 : 0 ≤ |((ε z : ℤ) : ℝ)| := abs_nonneg _
  nlinarith [h4, h6]

/-! ## 2. The norms of the factors of `uniCoeff` -/

lemma norm_toComplex_pos {z : GaussianInt} (hz : Work.FIPlan.gnorm z ≠ 0) :
    0 < ‖z.toComplex‖ := by
  rw [← Work.FIArea4.sqrt_gnorm z]
  exact Real.sqrt_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero hz)

/-- `‖(z/|z|)^k‖ = 1` — the unit-angle power has modulus one. -/
lemma norm_uniPow (z : GaussianInt) (hz : Work.FIPlan.gnorm z ≠ 0) (k : ℤ) : ‖uniPow z k‖ = 1 := by
  rw [uniPow, norm_zpow]
  have hpos : 0 < ‖z.toComplex‖ := norm_toComplex_pos hz
  have h1 : ‖z.toComplex / ((‖z.toComplex‖ : ℝ) : ℂ)‖ = 1 := by
    rw [norm_div]
    have h2 : ‖((‖z.toComplex‖ : ℝ) : ℂ)‖ = ‖z.toComplex‖ := by
      rw [Complex.norm_def, Complex.normSq_ofReal, ← sq, Real.sqrt_sq_eq_abs,
        abs_of_nonneg (norm_nonneg _)]
    rw [h2, div_self (ne_of_gt hpos)]
  rw [h1, one_zpow]

/-- **`‖uniCoeff ε β k z‖ ≤ ‖β z‖` on the polar box**: `|ε z| = 1`, `‖JKSym‖ ≤ 1`, `‖uniPow‖ = 1`. -/
lemma norm_uniCoeff_le {Pa : Work.FITop.Params} {φ : ℝ} {ε : GaussianInt → ℤ}
    {β : GaussianInt → ℂ} (hε : ∀ z1 z2 : GaussianInt, Work.FITop3.InPolarBox Pa φ z1 →
      Work.FITop3.InPolarBox Pa φ z2 → reflSign z1 z2 = ε z1 * ε z2)
    (k : ℤ) {z : GaussianInt} (hz : Work.FITop3.InPolarBox Pa φ z) :
    ‖uniCoeff ε β k z‖ ≤ ‖β z‖ := by
  rw [uniCoeff, norm_mul, norm_mul, norm_eps_eq_one hε hz]
  have hgn : Work.FIPlan.gnorm z ≠ 0 := by
    intro h0
    have h := hz.2.1
    rw [h0] at h
    simp at h
    linarith [Pa.hN1]
  rw [norm_uniPow z hgn k, one_mul, mul_one]
  exact norm_betaPrime_le β z

/-! ## 3. `omegaDetect` vanishes unless `4be ∣ |Δ|` -/

/-- `Δ` in coordinates: `Δ(z₁,z₂) = r₁s₂ − r₂s₁`. -/
lemma Delta_coord (z1 z2 : GaussianInt) :
    Work.FIPlan.Delta z1 z2 = z1.re * z2.im - z1.im * z2.re := by
  rw [Work.FIPlan.Delta, Zsqrtd.im_mul]
  simp
  ring

/-- On the units modulo `Q` the `ω`-detection congruence `z₁ ≡ ω z₂ (mod Q)` forces `Q ∣ Δ`. -/
lemma dvd_delta_of_omegaDetect_ne_zero (Q e : ℕ) (z1 z2 : GaussianInt)
    (h : omegaDetect Q e z1 z2 ≠ 0) : (Q : ℤ) ∣ Work.FIPlan.Delta z1 z2 := by
  unfold omegaDetect at h
  by_cases hQ : Q = 0
  · rw [dif_pos hQ] at h; exact absurd rfl h
  · haveI : NeZero Q := ⟨hQ⟩
    rw [dif_neg hQ] at h
    obtain ⟨ω, -, hω⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    have hcong : ((z1.re : ZMod Q) = ω * (z2.re : ZMod Q))
        ∧ ((z1.im : ZMod Q) = ω * (z2.im : ZMod Q)) := by
      by_contra hc
      rw [if_neg hc] at hω
      exact hω rfl
    rw [Delta_coord]
    have hre : ((Q : ℤ)) ∣ z1.re - ω.val * z2.re := by
      have h1 : ((z1.re : ℤ) : ZMod Q) = ((ω.val : ℤ) * z2.re : ℤ) := by
        rw [hcong.1]; push_cast; rw [ZMod.natCast_zmod_val]
      have h2 : (z1.re ≡ ω.val * z2.re [ZMOD (Q:ℤ)]) := (ZMod.intCast_eq_intCast_iff _ _ _).mp h1
      simpa using (Int.modEq_iff_dvd.mp h2).neg_right
    have him : ((Q : ℤ)) ∣ z1.im - ω.val * z2.im := by
      have h1 : ((z1.im : ℤ) : ZMod Q) = ((ω.val : ℤ) * z2.im : ℤ) := by
        rw [hcong.2]; push_cast; rw [ZMod.natCast_zmod_val]
      have h2 : (z1.im ≡ ω.val * z2.im [ZMOD (Q:ℤ)]) := (ZMod.intCast_eq_intCast_iff _ _ _).mp h1
      simpa using (Int.modEq_iff_dvd.mp h2).neg_right
    have hkey : z1.re * z2.im - z1.im * z2.re
        = (z1.re - ω.val * z2.re) * z2.im - z2.re * (z1.im - ω.val * z2.im) := by ring
    rw [hkey]
    exact dvd_sub (Dvd.dvd.mul_right hre _) (Dvd.dvd.mul_left him _)

/-- **`omegaDetect` is zero unless `4be ∣ |Δ|`.** -/
lemma omegaDetect_eq_zero_of_not_dvd (b e : ℕ) (z1 z2 : GaussianInt)
    (hΔ : ¬ 4 * b * e ∣ Work.FIPlan.absDelta z1 z2) :
    omegaDetect (4 * b * e) e z1 z2 = 0 := by
  by_contra h
  have hd := dvd_delta_of_omegaDetect_ne_zero (4 * b * e) e z1 z2 h
  apply hΔ
  rw [Work.FIPlan.absDelta]
  have := Int.natAbs_dvd_natAbs.mpr hd
  rwa [Int.natAbs_natCast] at this

/-! ## 4. The weighted non-coprime pair mass -/

/-- The inner (per-`(b,e)`) non-coprime pair mass. -/
def uniMode_pairInner (Pa : Work.FITop.Params) (b e : ℕ) (β : GaussianInt → ℂ) : ℝ :=
  ∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
    ∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
      (if ¬ Work.FIPlan.GaussCoprime z1 z2
          ∧ Nat.Coprime (Work.FIPlan.gnorm z1) (4 * b * e)
          ∧ Nat.Coprime (Work.FIPlan.gnorm z2) (4 * b * e)
          ∧ 4 * b * e ∣ Work.FIPlan.absDelta z1 z2
        then ‖β z1‖ * ‖β z2‖ else 0)

/-- **The weighted non-coprime pair mass of the guard removal** (with the `μ(b)/b`-weights of the
folded-in Möbius expansion). -/
def uniMode_pairMass (Pa : Work.FITop.Params) (X : ℕ) (β : GaussianInt → ℂ) : ℝ :=
  ∑ b ∈ Finset.Icc 1 (uniB Pa), ∑ e ∈ Finset.Icc 1 X,
    (1 / (b : ℝ)) * uniMode_pairInner Pa b e β

end

end Work.FIArea7
