import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBogFS.BogFSCompare
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBogFS.psiSc_bulk_le` — the pointwise bulk comparison `psiSc ↔ fsI1Integrand`

This module proves the pointwise comparison of the honest scaled clean integrand `psiSc`
with FS's model integrand `fsI1Integrand` at the affine model kernel `bogKernel v R ρ μ`,
**on the whole momentum space** (so that it can be used both in the bulk and in the tail
region of the `I₁` estimate of `Work.BoseBogFS.integral_cleanFun_le`).

With `r = ‖t‖`, `u = tauScRad v ρ μ r`, `b = betaSc v h ρ μ t`, `K̃ = (bogKernel v R ρ μ).β r`,
`τ̃ = fsTau ε_T c₁ c₂ r`, `δ = bogDelta R ℓ C`, `B = bogBb R ℓ C`, `η = bogEta v R ρ`, the two
integrands differ by the two-variable increment of the bracket

  `gFun τ b r = τ + b − √((τ+b)²−b²) − b²/(2r²)`

at the pairs `(τ, b) = (u, b)` (honest) and `(τ̃, K̃)` (model):

  `psiSc t − fsI1Integrand t = gFun u b r − gFun τ̃ K̃ r`.

The two regimes are:

* **bulk** (`r ≤ bogT`, whence `K̃ = 8π + ηr =: A`): the `β`-increment bound
  `gFun u b r − gFun u A r ≤ |b − A|(1 + (b+A)/(2r²))` (from `|b−A| ≤ δ+2ηr`, `b ≤ B+ηr`)
  together with antitonicity in `τ` (the honest symbol is *below* FS's, `u ≤ τ̃`) gives
  `≤ (δ+2ηr)(1 + (B+ηr+A)/(2r²))`;
* **tail** (`r > bogT`, whence `K̃ = 0` and `fsI1Integrand t = 0`): `psiSc = gFun u b r`,
  bounded either by `gFun u b r ≤ b²(r²−u)/(2ur²) ≤ 2A²(r²−u)/(2ur²)` (when `b ≤ √2A`)
  or by `gFun u b r ≤ b − b²/(2r²) − bu/(u+b)` together with the perfect-square inequality
  `A ≤ b²/(2r²) + bu/(u+b) + A²(r²−u)/(r²u)` (when `b > √2A`).

The result is the pointwise row consumed by `Work.BoseBogFS.integral_cleanFun_le`.
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox Work.BoseBoxFix Work.BoseFixR

open Work.BoseB6Est (gFun)

namespace Work.BoseBogFS

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 0. The two definitions as `gFun`, and the kernel's tail -/

lemma tauScRad_zero (v : E3 → ℝ) (ρ μ : ℝ) : tauScRad v ρ μ 0 = 0 := by
  rw [tauScRad, tauSmRad]
  simp [Work.BoseBoxFock.tauProf_eq_zero_of_le_one]

/-- The honest scaled clean bracket is `gFun` at the honest data. -/
lemma psiSc_eq_gFun (v : E3 → ℝ) (h : ScatSol v) (ρ μ : ℝ) (t : E3) :
    psiSc v h ρ μ t = gFun (tauScRad v ρ μ ‖t‖) (betaSc v h ρ μ t) ‖t‖ := by
  rw [psiSc, Work.BoseB6.bogZeroPoint, Work.BoseB6Est.gFun, tauSc_eq_tauScRad]

/-- FS's model integrand is `gFun` at the model data. -/
lemma fsI1Integrand_eq_gFun (K : Work.BoseB6Est.FsKernel) (eT c1 c2 : ℝ) (t : E3) :
    Work.BoseB6Est.fsI1Integrand K eT c1 c2 t
      = gFun (Work.BoseB6.fsTau eT c1 c2 ‖t‖) (K.β ‖t‖) ‖t‖ := by
  rw [Work.BoseB6Est.fsI1Integrand, Work.BoseB6Est.cleanBracket]
  simp only [Work.BoseB6Est.nrm, eucNorm3_eq_norm]
  rw [Work.BoseB6Est.gFun]

/-- `(bogKernel v R ρ μ).β r = 0` beyond the kernel's cutoff, in the form
`max 0 (bogT v R μ) < r` (no sign hypothesis on `bogT`). -/
lemma bogKernel_beta_eq_zero_of_gt (v : E3 → ℝ) (R ρ μ : ℝ) {r : ℝ}
    (hr : max 0 (bogT v R μ) < r) :
    (bogKernel v R ρ μ).β r = 0 := by
  have h : ¬ (r ∈ Set.Icc (0 : ℝ) (max 0 (bogT v R μ))) := fun hc =>
    absurd hc.2 (not_le.mpr hr)
  show (if r ∈ Set.Icc (0 : ℝ) (max 0 (bogT v R μ))
      then 8 * Real.pi + max 0 (bogEta v R ρ) * r else 0) = 0
  rw [if_neg h]

/-! ## 1. FS's model symbol is below the parabola `r²` -/

/-- `fsTau ε_T c₁ c₂ r ≤ r²`: each kinked parabola is bounded by `r²` (the positivity of the
two thresholds is what makes `max (|r| − cᵢ) 0 ≤ r`). -/
lemma fsTau_le_sq {eT c1 c2 r : ℝ} (hε0 : 0 ≤ eT) (hε1 : eT ≤ 1)
    (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2) (hr : 0 ≤ r) :
    Work.BoseB6.fsTau eT c1 c2 r ≤ r ^ 2 := by
  have habs : |r| = r := abs_of_nonneg hr
  have h1 : (max (|r| - c1) 0) ^ 2 ≤ r ^ 2 := by
    refine pow_le_pow_left₀ (le_max_right _ _) ?_ 2
    exact max_le (by rw [habs]; linarith) hr
  have h2 : (max (|r| - c2) 0) ^ 2 ≤ r ^ 2 := by
    refine pow_le_pow_left₀ (le_max_right _ _) ?_ 2
    exact max_le (by rw [habs]; linarith) hr
  rw [Work.BoseB6.fsTau]
  nlinarith [h1, h2, hε0, hε1]

/-! ## 2. The real-variable cores -/

/-- **The perfect-square inequality**: for `0 < A < b` and `u > 0`,
`2A − A²/b ≤ bu/(u+b) + A²/u`, since
`bu² + A²(u+b) − (2A − A²/b)u(u+b) = ((b−A)u − Ab)²/b ≥ 0`. -/
lemma two_mul_sub_sq_div_le {A b u : ℝ} (hA : 0 < A) (hb : A < b) (hu : 0 < u) :
    2 * A - A ^ 2 / b ≤ b * u / (u + b) + A ^ 2 / u := by
  have hb0 : 0 < b := lt_trans hA hb
  have h1 : b * u / (u + b) + A ^ 2 / u - (2 * A - A ^ 2 / b)
      = ((b - A) * u - A * b) ^ 2 / (b * u * (u + b)) := by
    have hbne : b ≠ 0 := ne_of_gt hb0
    have hune : u ≠ 0 := ne_of_gt hu
    have hubne : u + b ≠ 0 := ne_of_gt (by linarith)
    field_simp
    ring
  have h2 : 0 ≤ ((b - A) * u - A * b) ^ 2 / (b * u * (u + b)) :=
    div_nonneg (sq_nonneg _) (by positivity)
  rw [← sub_nonneg, h1]
  exact h2

/-- **The tail inequality**: for `0 < u ≤ r²`, `0 < A`, `b ≥ √2·A`,
`A ≤ b²/(2r²) + bu/(u+b) + A²(r²−u)/(r²u)`.

Indeed `bu/(u+b) + A²/u ≥ 2A − A²/b` (perfect square), so the left-hand side is at least
`A − A²/b + (b²/2 − A²)/r²`, and both terms are nonnegative. -/
lemma sq_div_add_le {A b r u : ℝ} (hA : 0 < A) (hb : Real.sqrt 2 * A ≤ b) (hr : 0 < r)
    (hu : 0 < u) (huR : u ≤ r ^ 2) :
    A ≤ b ^ 2 / (2 * r ^ 2) + b * u / (u + b) + A ^ 2 * (r ^ 2 - u) / (r ^ 2 * u) := by
  have hsqrt1 : (1 : ℝ) < Real.sqrt 2 := by
    have h1 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    nlinarith
  have hAb : A < b := by
    have h1 : A < Real.sqrt 2 * A := by
      have := mul_lt_mul_of_pos_right hsqrt1 hA
      simpa using this
    exact lt_of_lt_of_le h1 hb
  have hb0 : 0 < b := lt_trans hA hAb
  have hkeep := two_mul_sub_sq_div_le hA hAb hu
  have hsq : 0 ≤ b ^ 2 / 2 - A ^ 2 := by
    have h2 : (Real.sqrt 2 * A) ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ (by positivity) hb 2
    have h3 : (Real.sqrt 2 * A) ^ 2 = 2 * A ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    linarith
  have hsplit : b ^ 2 / (2 * r ^ 2) + b * u / (u + b) + A ^ 2 * (r ^ 2 - u) / (r ^ 2 * u)
      = (b ^ 2 / (2 * r ^ 2) - A ^ 2 / r ^ 2) + (b * u / (u + b) + A ^ 2 / u) := by
    have hrne : r ≠ 0 := ne_of_gt hr
    have hune : u ≠ 0 := ne_of_gt hu
    field_simp
    ring
  have hmain : A - A ^ 2 / b + (b ^ 2 / 2 - A ^ 2) / r ^ 2 ≥ 0 := by
    have h1 : 0 ≤ A - A ^ 2 / b := by
      have heq : A - A ^ 2 / b = A * (b - A) / b := by
        field_simp
      rw [heq]
      exact div_nonneg (mul_nonneg hA.le (by linarith)) hb0.le
    have h2 : 0 ≤ (b ^ 2 / 2 - A ^ 2) / r ^ 2 := div_nonneg hsq (by positivity)
    linarith
  have hexp : (b ^ 2 / (2 * r ^ 2) - A ^ 2 / r ^ 2) = (b ^ 2 / 2 - A ^ 2) / r ^ 2 := by
    field_simp
  rw [hsplit, hexp]
  linarith

/-- **The bulk row** (`K̃ = A`): the `β`-increment at the honest `τ = u` (from `|b−A| ≤ δ+2ηr`
and `b ≤ B+ηr`) plus the `τ`-increment of `u` against the model point `r²` (from
`gFun_tau_diff`, the `τ`-part at `r²` itself being dominated by the one at `tT ≤ r²`). -/
lemma gFun_bulk_le {u b tT A r δ B η : ℝ} (hr : 0 < r) (hu : 0 < u) (hu_le : u ≤ r ^ 2)
    (hb : 0 ≤ b) (hA : 0 ≤ A) (htTnn : 0 ≤ tT) (htTr : tT ≤ r ^ 2) (hδ : 0 ≤ δ) (hη : 0 ≤ η)
    (hβc : |b - A| ≤ δ + 2 * η * r) (hβu : b ≤ B + η * r)
    (hfac : 0 ≤ 1 + (B + η * r + A) / (2 * r ^ 2)) :
    gFun u b r - gFun tT A r
      ≤ (δ + 2 * η * r) * (1 + (B + η * r + A) / (2 * r ^ 2))
        + 2 * A ^ 2 * (r ^ 2 - u) / (r ^ 2 * (2 * u)) := by
  have h1 : gFun u b r - gFun u A r ≤ |b - A| * (1 + (b + A) / (2 * r ^ 2)) :=
    le_trans (le_abs_self _) (gFun_beta_diff_abs_le hu hu_le hb hA)
  have h3 : |b - A| ≤ δ + 2 * η * r := hβc
  have h4 : (1 + (b + A) / (2 * r ^ 2)) ≤ (1 + (B + η * r + A) / (2 * r ^ 2)) := by
    have hbA : b + A ≤ B + η * r + A := by linarith
    have hpos : 0 < 2 * r ^ 2 := by positivity
    linarith [div_le_div_of_nonneg_right hbA hpos.le]
  have h5 : |b - A| * (1 + (b + A) / (2 * r ^ 2))
      ≤ (δ + 2 * η * r) * (1 + (B + η * r + A) / (2 * r ^ 2)) := by
    have hc : 0 ≤ 1 + (b + A) / (2 * r ^ 2) := by
      have h1 : 0 ≤ b + A := by linarith
      have h2 : 0 < 2 * r ^ 2 := by positivity
      linarith [div_nonneg h1 h2.le]
    have hd : 0 ≤ δ + 2 * η * r := by
      have h1 : 0 ≤ 2 * η * r := by positivity
      linarith
    exact mul_le_mul h3 h4 hc hd
  have hβ : gFun u b r - gFun u A r
      ≤ (δ + 2 * η * r) * (1 + (B + η * r + A) / (2 * r ^ 2)) := le_trans h1 h5
  have h6 : gFun u A r - gFun (r ^ 2) A r ≤ 2 * A ^ 2 * (r ^ 2 - u) / (r ^ 2 * (2 * u + A)) :=
    le_trans (le_abs_self _) (Work.BoseB6Est.gFun_tau_diff hu.le hu_le hA hr)
  have h7 : gFun (r ^ 2) A r ≤ gFun tT A r := gFun_tau_anti htTnn htTr hA
  have h8 : 2 * A ^ 2 * (r ^ 2 - u) / (r ^ 2 * (2 * u + A))
      ≤ 2 * A ^ 2 * (r ^ 2 - u) / (r ^ 2 * (2 * u)) := by
    have hnum : 0 ≤ 2 * A ^ 2 * (r ^ 2 - u) :=
      mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg A)) (by linarith)
    have hd1 : 0 < r ^ 2 * (2 * u) := by
      refine mul_pos (pow_pos hr 2) ?_
      linarith
    have hd2 : r ^ 2 * (2 * u) ≤ r ^ 2 * (2 * u + A) :=
      mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg r)
    exact div_le_div_of_nonneg_left hnum hd1 hd2
  linarith

/-- **The tail row** (`K̃ = 0`, so that `fsI1Integrand t = 0`): here only `psiSc = gFun u b r`
has to be bounded, and the `τ`-deficit term of the target is available as a payer. -/
lemma gFun_tail_le {u b A r δ B η : ℝ} (hr : 0 < r) (hu : 0 < u) (hu_le : u ≤ r ^ 2)
    (hb : 0 ≤ b) (hA : 0 < A) (hδ : 0 ≤ δ) (hη : 0 ≤ η)
    (hbA : b - A ≤ δ)
    (hF : δ ≤ (δ + 2 * η * r) * (1 + (B + η * r + A) / (2 * r ^ 2))) :
    gFun u b r
      ≤ (δ + 2 * η * r) * (1 + (B + η * r + A) / (2 * r ^ 2))
        + 2 * A ^ 2 * (r ^ 2 - u) / (r ^ 2 * (2 * u)) := by
  have hS : 2 * A ^ 2 * (r ^ 2 - u) / (r ^ 2 * (2 * u)) = A ^ 2 * (r ^ 2 - u) / (r ^ 2 * u) := by
    have hrne : r ≠ 0 := ne_of_gt hr
    have hune : u ≠ 0 := ne_of_gt hu
    field_simp
  rw [hS]
  rcases le_or_gt b (Real.sqrt 2 * A) with hb2 | hb2
  · have h1 := gFun_beta_le hu hu_le hb
    have h2 : b ^ 2 ≤ 2 * A ^ 2 := by
      have h2a : b ^ 2 ≤ (Real.sqrt 2 * A) ^ 2 := pow_le_pow_left₀ hb hb2 2
      have h2b : (Real.sqrt 2 * A) ^ 2 = 2 * A ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
      linarith
    have h3 : b ^ 2 * (r ^ 2 - u) / (2 * u * r ^ 2) ≤ A ^ 2 * (r ^ 2 - u) / (r ^ 2 * u) := by
      rw [div_le_div_iff₀ (by positivity : (0:ℝ) < 2 * u * r ^ 2)
        (by positivity : (0:ℝ) < r ^ 2 * u)]
      have h4 : b ^ 2 * ((r ^ 2 - u) * (r ^ 2 * u)) ≤ (2 * A ^ 2) * ((r ^ 2 - u) * (r ^ 2 * u)) :=
        mul_le_mul_of_nonneg_right h2
          (mul_nonneg (by linarith) (mul_nonneg (sq_nonneg r) hu.le))
      linarith [h4]
    have hFnn : 0 ≤ (δ + 2 * η * r) * (1 + (B + η * r + A) / (2 * r ^ 2)) :=
      le_trans hδ hF
    linarith
  · have hb2' : Real.sqrt 2 * A < b := hb2
    have h1 : gFun u b r ≤ b ^ 2 / (u + b) - b ^ 2 / (2 * r ^ 2) := by
      rw [gFun_eq_div hu.le hb]
      have hpos : 0 < u + b := by linarith
      have hle : u + b ≤ u + b + Real.sqrt (u ^ 2 + 2 * u * b) :=
        le_add_of_nonneg_right (Real.sqrt_nonneg _)
      exact sub_le_sub_right (div_le_div_of_nonneg_left (sq_nonneg b) hpos hle) _
    have h2 := sq_div_add_le hA hb2.le hr hu hu_le
    have h3 : b ^ 2 / (u + b) = b - b * u / (u + b) := by
      have hpos : 0 < u + b := by linarith
      field_simp
      ring
    have h4 : b ^ 2 / (u + b) - b ^ 2 / (2 * r ^ 2)
        ≤ (b - A) + A ^ 2 * (r ^ 2 - u) / (r ^ 2 * u) := by
      rw [h3]
      linarith
    have h5 : (b - A) + A ^ 2 * (r ^ 2 - u) / (r ^ 2 * u)
        ≤ δ + A ^ 2 * (r ^ 2 - u) / (r ^ 2 * u) := by
      linarith
    linarith

/-! ## 3. The target -/

theorem psiSc_bulk_le {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {R ρ μ : ℝ} {t : EuclideanSpace ℝ (Fin 3)}
    (hR : 0 < R) (hv : ∀ x, 0 ≤ v x) (hvrad : _root_.BoseGases.IsRadial v)
    (hav : 0 < _root_.BoseGases.a v) (hρ : 0 < ρ)
    (heT0 : 0 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT)
    (heT1 : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT ≤ 1)
    (hc1 : 0 < Work.BoseBogFS.bogC1 v ρ μ) (hc2 : 0 < Work.BoseBogFS.bogC2 v ρ μ)
    (hbnn : 0 ≤ Work.BoseBogFS.betaSc v h ρ μ t)
    (hτpos : 0 < Work.BoseBogFS.tauScRad v ρ μ ‖t‖)
    (hβc : |Work.BoseBogFS.betaSc v h ρ μ t
        - (8 * Real.pi + Work.BoseBogFS.bogEta v R ρ * ‖t‖)|
      ≤ Work.BoseBogFS.bogDelta R (Work.BoseFixR.ell v μ) Work.BoseBogFS.chiTC
        + 2 * Work.BoseBogFS.bogEta v R ρ * ‖t‖)
    (hβu : Work.BoseBogFS.betaSc v h ρ μ t
      ≤ Work.BoseBogFS.bogBb R (Work.BoseFixR.ell v μ) Work.BoseBogFS.chiTC
        + Work.BoseBogFS.bogEta v R ρ * ‖t‖) :
    Work.BoseBogFS.psiSc v h ρ μ t
        - Work.BoseB6Est.fsI1Integrand (Work.BoseBogFS.bogKernel v R ρ μ)
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
            (Work.BoseBogFS.bogC1 v ρ μ) (Work.BoseBogFS.bogC2 v ρ μ) t
      ≤ (Work.BoseBogFS.bogDelta R (Work.BoseFixR.ell v μ) Work.BoseBogFS.chiTC
            + 2 * Work.BoseBogFS.bogEta v R ρ * ‖t‖)
          * (1 + (Work.BoseBogFS.bogBb R (Work.BoseFixR.ell v μ) Work.BoseBogFS.chiTC
              + Work.BoseBogFS.bogEta v R ρ * ‖t‖
              + (8 * Real.pi + Work.BoseBogFS.bogEta v R ρ * ‖t‖)) / (2 * ‖t‖ ^ 2))
        + 2 * (8 * Real.pi + Work.BoseBogFS.bogEta v R ρ * ‖t‖) ^ 2
            * (‖t‖ ^ 2 - Work.BoseBogFS.tauScRad v ρ μ ‖t‖)
            / (‖t‖ ^ 2 * (2 * Work.BoseBogFS.tauScRad v ρ μ ‖t‖)) := by
  have hP : 0 < ρ * _root_.BoseGases.a v := mul_pos hρ hav
  have hsn : ‖t‖ ≠ 0 := by
    intro h0
    rw [h0, tauScRad_zero] at hτpos
    exact lt_irrefl 0 hτpos
  have hr : 0 < ‖t‖ := lt_of_le_of_ne (norm_nonneg t) (Ne.symm hsn)
  have hu : 0 < tauScRad v ρ μ ‖t‖ := hτpos
  have hu_le : tauScRad v ρ μ ‖t‖ ≤ ‖t‖ ^ 2 :=
    tauScRad_le_sq v hP hc1 hc2 heT0 heT1 (norm_nonneg t)
  have hη : 0 ≤ Work.BoseBogFS.bogEta v R ρ := bogEta_nonneg v hR.le hρ.le
  have hδ : 0 ≤ Work.BoseBogFS.bogDelta R (Work.BoseFixR.ell v μ) Work.BoseBogFS.chiTC := by
    rw [bogDelta]
    exact mul_nonneg (mul_nonneg (by positivity) chiTC_nonneg) (sq_nonneg _)
  have hBnn : 0 ≤ Work.BoseBogFS.bogBb R (Work.BoseFixR.ell v μ) Work.BoseBogFS.chiTC := by
    rw [bogBb]
    have h1 : 0 ≤ Work.BoseBogFS.chiTC * (R / ell v μ) ^ 2 :=
      mul_nonneg chiTC_nonneg (sq_nonneg _)
    nlinarith [Real.pi_pos, h1]
  have hBδ : Work.BoseBogFS.bogBb R (Work.BoseFixR.ell v μ) Work.BoseBogFS.chiTC
      = 8 * Real.pi + Work.BoseBogFS.bogDelta R (Work.BoseFixR.ell v μ) Work.BoseBogFS.chiTC := by
    rw [bogBb, bogDelta]
    ring
  have htTnn : 0 ≤ Work.BoseB6.fsTau (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
      (bogC1 v ρ μ) (bogC2 v ρ μ) ‖t‖ :=
    Work.BoseB6Est.fsTau_nonneg heT0 heT1 (norm_nonneg t)
  have htTr : Work.BoseB6.fsTau (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
      (bogC1 v ρ μ) (bogC2 v ρ μ) ‖t‖ ≤ ‖t‖ ^ 2 :=
    fsTau_le_sq heT0 heT1 hc1.le hc2.le (norm_nonneg t)
  have hAmem : (0:ℝ) ≤ 8 * Real.pi + Work.BoseBogFS.bogEta v R ρ * ‖t‖ := by
    have h1 : 0 ≤ Work.BoseBogFS.bogEta v R ρ * ‖t‖ := mul_nonneg hη (norm_nonneg t)
    linarith [Real.pi_pos]
  have hApos : (0:ℝ) < 8 * Real.pi + Work.BoseBogFS.bogEta v R ρ * ‖t‖ := by
    have h1 : 0 ≤ Work.BoseBogFS.bogEta v R ρ * ‖t‖ := mul_nonneg hη (norm_nonneg t)
    linarith [Real.pi_pos]
  have hqnn : 0 ≤ (Work.BoseBogFS.bogBb R (Work.BoseFixR.ell v μ) Work.BoseBogFS.chiTC
      + Work.BoseBogFS.bogEta v R ρ * ‖t‖ + (8 * Real.pi + Work.BoseBogFS.bogEta v R ρ * ‖t‖))
      / (2 * ‖t‖ ^ 2) := by
    have h1 : 0 ≤ Work.BoseBogFS.bogBb R (Work.BoseFixR.ell v μ) Work.BoseBogFS.chiTC
        + Work.BoseBogFS.bogEta v R ρ * ‖t‖ + (8 * Real.pi + Work.BoseBogFS.bogEta v R ρ * ‖t‖) := by
      have h2 : 0 ≤ Work.BoseBogFS.bogEta v R ρ * ‖t‖ := mul_nonneg hη (norm_nonneg t)
      linarith [hBnn, h2, hAmem]
    have h3 : 0 < 2 * ‖t‖ ^ 2 := by positivity
    exact div_nonneg h1 h3.le
  have hfac : 0 ≤ 1 + (Work.BoseBogFS.bogBb R (Work.BoseFixR.ell v μ) Work.BoseBogFS.chiTC
      + Work.BoseBogFS.bogEta v R ρ * ‖t‖ + (8 * Real.pi + Work.BoseBogFS.bogEta v R ρ * ‖t‖))
      / (2 * ‖t‖ ^ 2) := by linarith [hqnn]
  have hdh : 0 ≤ Work.BoseBogFS.bogDelta R (Work.BoseFixR.ell v μ) Work.BoseBogFS.chiTC
      + 2 * Work.BoseBogFS.bogEta v R ρ * ‖t‖ := by
    have h2 : 0 ≤ 2 * Work.BoseBogFS.bogEta v R ρ * ‖t‖ := by positivity
    linarith
  have hL : Work.BoseBogFS.psiSc v h ρ μ t
        - Work.BoseB6Est.fsI1Integrand (Work.BoseBogFS.bogKernel v R ρ μ)
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
            (Work.BoseBogFS.bogC1 v ρ μ) (Work.BoseBogFS.bogC2 v ρ μ) t
      = gFun (tauScRad v ρ μ ‖t‖) (betaSc v h ρ μ t) ‖t‖
        - gFun (Work.BoseB6.fsTau (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
            (bogC1 v ρ μ) (bogC2 v ρ μ) ‖t‖)
          ((Work.BoseBogFS.bogKernel v R ρ μ).β ‖t‖) ‖t‖ := by
    rw [psiSc_eq_gFun, fsI1Integrand_eq_gFun]
  rw [hL]
  rcases le_or_gt ‖t‖ (max 0 (bogT v R μ)) with hbulk | hfar
  · have hT : 0 ≤ bogT v R μ := by
      by_contra hcon
      push_neg at hcon
      rw [max_eq_left hcon.le] at hbulk
      linarith
    have hrT : ‖t‖ ≤ bogT v R μ := by rwa [max_eq_right hT] at hbulk
    have hKβ : (Work.BoseBogFS.bogKernel v R ρ μ).β ‖t‖
        = 8 * Real.pi + Work.BoseBogFS.bogEta v R ρ * ‖t‖ :=
      bogKernel_beta v R ρ μ hη hT (norm_nonneg t) hrT
    rw [hKβ]
    have hmain := gFun_bulk_le (u := tauScRad v ρ μ ‖t‖) (b := betaSc v h ρ μ t)
      (tT := Work.BoseB6.fsTau (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
        (bogC1 v ρ μ) (bogC2 v ρ μ) ‖t‖)
      (A := 8 * Real.pi + Work.BoseBogFS.bogEta v R ρ * ‖t‖) (r := ‖t‖)
      (δ := Work.BoseBogFS.bogDelta R (Work.BoseFixR.ell v μ) Work.BoseBogFS.chiTC)
      (B := Work.BoseBogFS.bogBb R (Work.BoseFixR.ell v μ) Work.BoseBogFS.chiTC)
      (η := Work.BoseBogFS.bogEta v R ρ)
      hr hu hu_le hbnn hAmem htTnn htTr hδ hη hβc hβu hfac
    exact hmain
  · have hKβ : (Work.BoseBogFS.bogKernel v R ρ μ).β ‖t‖ = 0 :=
      bogKernel_beta_eq_zero_of_gt v R ρ μ hfar
    rw [hKβ, gFun_beta_zero htTnn, sub_zero]
    have hbA : betaSc v h ρ μ t - (8 * Real.pi + Work.BoseBogFS.bogEta v R ρ * ‖t‖)
        ≤ Work.BoseBogFS.bogDelta R (Work.BoseFixR.ell v μ) Work.BoseBogFS.chiTC := by
      rw [hBδ] at hβu
      linarith
    have hF : Work.BoseBogFS.bogDelta R (Work.BoseFixR.ell v μ) Work.BoseBogFS.chiTC
        ≤ (Work.BoseBogFS.bogDelta R (Work.BoseFixR.ell v μ) Work.BoseBogFS.chiTC
            + 2 * Work.BoseBogFS.bogEta v R ρ * ‖t‖)
          * (1 + (Work.BoseBogFS.bogBb R (Work.BoseFixR.ell v μ) Work.BoseBogFS.chiTC
              + Work.BoseBogFS.bogEta v R ρ * ‖t‖
              + (8 * Real.pi + Work.BoseBogFS.bogEta v R ρ * ‖t‖)) / (2 * ‖t‖ ^ 2)) := by
      have h2 : 0 ≤ Work.BoseBogFS.bogEta v R ρ * ‖t‖ := mul_nonneg hη (norm_nonneg t)
      calc Work.BoseBogFS.bogDelta R (Work.BoseFixR.ell v μ) Work.BoseBogFS.chiTC
          ≤ (Work.BoseBogFS.bogDelta R (Work.BoseFixR.ell v μ) Work.BoseBogFS.chiTC
              + 2 * Work.BoseBogFS.bogEta v R ρ * ‖t‖) * 1 := by linarith
        _ ≤ (Work.BoseBogFS.bogDelta R (Work.BoseFixR.ell v μ) Work.BoseBogFS.chiTC
              + 2 * Work.BoseBogFS.bogEta v R ρ * ‖t‖)
            * (1 + (Work.BoseBogFS.bogBb R (Work.BoseFixR.ell v μ) Work.BoseBogFS.chiTC
                + Work.BoseBogFS.bogEta v R ρ * ‖t‖
                + (8 * Real.pi + Work.BoseBogFS.bogEta v R ρ * ‖t‖)) / (2 * ‖t‖ ^ 2)) := by
          apply mul_le_mul_of_nonneg_left (by linarith [hqnn]) hdh
    have hmain := gFun_tail_le (u := tauScRad v ρ μ ‖t‖) (b := betaSc v h ρ μ t)
      (A := 8 * Real.pi + Work.BoseBogFS.bogEta v R ρ * ‖t‖) (r := ‖t‖)
      (δ := Work.BoseBogFS.bogDelta R (Work.BoseFixR.ell v μ) Work.BoseBogFS.chiTC)
      (B := Work.BoseBogFS.bogBb R (Work.BoseFixR.ell v μ) Work.BoseBogFS.chiTC)
      (η := Work.BoseBogFS.bogEta v R ρ)
      hr hu hu_le hbnn hApos hδ hη hbA hF
    linarith [hmain]

end Work.BoseBogFS
