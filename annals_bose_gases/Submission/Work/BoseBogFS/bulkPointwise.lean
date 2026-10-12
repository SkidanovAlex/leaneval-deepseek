import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBogFS.psiSc_bulk_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBogFS

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# `Work.BoseBogFS.bulkPointwise` — the pointwise bulk row of the `I₁` comparison

The bulk comparison error `psiSc − fsI1Integrand` of `psiSc_bulk_le` is bounded on the
annulus `4c₁ ≤ ‖t‖ ≤ T` by the radial majorant

  `bulkRadial δ η B A c₁ ε_T T r`
    `= (δ+2ηr)(1 + (B+ηT+A)/(2r²)) + A²(36c₁/r³ + 12ε_T/r²)`

with `δ = bogDelta R ℓ chiTC`, `η = bogEta v R ρ`, `B = bogBb R ℓ chiTC`,
`A = 8π + ηT`.

Its two ingredients are the `τ`-bounds of the honest kinetic symbol: on `r ≥ 4c₁`
the symbol never drops below `r²/8` (`tauScRad_ge_eighth`), while its deficit is
`r² − τ ≤ 3c₁r + ε_T r²` (`tauScRad_deficit_le`); together they give
`(r²−τ)/(r²τ) ≤ 36c₁/r³ + 12ε_T/r²` (`bulkTauTerm_le`), which is how the
logarithmic row `∫ dr/r` of FS's `lem:BogIntegral` arises.
-/

noncomputable section

/-- The radial majorant of the bulk row:
`G(r) = (δ+2ηr)(1 + (B+ηT+A)/(2r²)) + A²(36c₁/r³ + 12ε_T/r²)`. -/
def bulkRadial (δ η B A c1 eT T r : ℝ) : ℝ :=
  (δ + 2 * η * r) * (1 + (B + η * T + A) / (2 * r ^ 2))
    + A ^ 2 * (36 * c1 / r ^ 3 + 12 * eT / r ^ 2)

/-- The profile is nonnegative. -/
private lemma tauProf_nonneg_aux (s : ℝ) : 0 ≤ Work.BoseBoxFock.tauProf s := by
  have h : (max 0 (s - 2)) ^ 2 ≤ Work.BoseBoxFock.tauProf s := by
    have := Work.BoseBoxFock.tauProf_spec.2.2.1 s
    simpa only [Work.BoseBoxFock.tauProf] using this
  linarith [sq_nonneg (max 0 (s - 2))]

/-- The kink bound of the profile: `(max 0 (r−2c))² ≤ c²τ̃(r/c)` for `c > 0`. -/
private lemma tauProf_sq_kink_le {c r : ℝ} (hc : 0 < c) :
    (max 0 (r - 2 * c)) ^ 2 ≤ c ^ 2 * Work.BoseBoxFock.tauProf (r / c) := by
  have h1 : (max 0 (r / c - 2)) ^ 2 ≤ Work.BoseBoxFock.tauProf (r / c) := by
    have := Work.BoseBoxFock.tauProf_spec.2.2.1 (r / c)
    simpa only [Work.BoseBoxFock.tauProf] using this
  have h2 : max 0 (r - 2 * c) = c * max 0 (r / c - 2) := by
    rw [mul_max_of_nonneg 0 (r / c - 2) hc.le]
    congr 1
    · ring
    · field_simp
  rw [h2]
  calc (c * max 0 (r / c - 2)) ^ 2 = c ^ 2 * (max 0 (r / c - 2)) ^ 2 := by ring
    _ ≤ c ^ 2 * Work.BoseBoxFock.tauProf (r / c) :=
        mul_le_mul_of_nonneg_left h1 (sq_nonneg c)

/-- **The symbol never drops below `r²/8` on the annulus** `4c₁ ≤ r`.

(⚠ renamed from `tauScRad_ge_eighth`: the standalone module
`Submission/Work/BoseBogFS/tauScRad_ge_eighth.lean` declares a lemma of that name with the
slightly weaker hypothesis set `{hP, hc1, heT0, heT1, h3}`, so the two cannot coexist in one
import cone.  This copy is the `c₂`-explicit one, used only inside this module.) -/
lemma tauScRad_ge_eighth_bulk {v : E3 → ℝ} {ρ μ r : ℝ}
    (hP : 0 < ρ * _root_.BoseGases.a v)
    (hc1 : 0 < bogC1 v ρ μ) (hc2 : 0 < bogC2 v ρ μ)
    (heT0 : 0 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT)
    (heT1 : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT ≤ 1 / 2)
    (hr4 : 4 * bogC1 v ρ μ ≤ r) :
    r ^ 2 / 8 ≤ tauScRad v ρ μ r := by
  rw [tauScRad_eq v hP r]
  have hr : 0 < r := lt_of_lt_of_le (by linarith) hr4
  have hk := tauProf_sq_kink_le (c := bogC1 v ρ μ) (r := r) hc1
  have hmax : r / 2 ≤ max 0 (r - 2 * bogC1 v ρ μ) := by
    have h2 : r / 2 ≤ r - 2 * bogC1 v ρ μ := by linarith
    exact le_trans h2 (le_max_right _ _)
  have hk1 : (r / 2) ^ 2 ≤ (bogC1 v ρ μ) ^ 2 * Work.BoseBoxFock.tauProf (r / bogC1 v ρ μ) :=
    le_trans (pow_le_pow_left₀ (by positivity) hmax 2) hk
  have h1e : (1 : ℝ) / 2 ≤ 1 - (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT := by
    linarith
  have hstep : (1 / 2) * (r / 2) ^ 2
      ≤ (1 - (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT)
        * ((bogC1 v ρ μ) ^ 2 * Work.BoseBoxFock.tauProf (r / bogC1 v ρ μ)) := by
    have hnn : 0 ≤ (r / 2) ^ 2 := sq_nonneg _
    have h1 : (1 / 2) * (r / 2) ^ 2
        ≤ (1 - (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT) * (r / 2) ^ 2 := by
      linarith [mul_le_mul_of_nonneg_right h1e hnn]
    have h2 : (1 - (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT) * (r / 2) ^ 2
        ≤ (1 - (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT)
          * ((bogC1 v ρ μ) ^ 2 * Work.BoseBoxFock.tauProf (r / bogC1 v ρ μ)) :=
      mul_le_mul_of_nonneg_left hk1 (by linarith)
    linarith [h1, h2]
  have hgoal : r ^ 2 / 8
      ≤ (1 - (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT)
        * ((bogC1 v ρ μ) ^ 2 * Work.BoseBoxFock.tauProf (r / bogC1 v ρ μ)) := by
    have heq : (1 / 2) * (r / 2) ^ 2 = r ^ 2 / 8 := by ring
    linarith [hstep, heq.le, heq.ge]
  have hnn2 : 0 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
      * ((bogC2 v ρ μ) ^ 2 * Work.BoseBoxFock.tauProf (r / bogC2 v ρ μ)) :=
    mul_nonneg heT0 (mul_nonneg (sq_nonneg _) (tauProf_nonneg_aux _))
  linarith [hgoal, hnn2]

/-- **The `τ`-deficit on the annulus**: `r² − τ_s,r ≤ 3c₁r + ε_T r²` for `r ≥ 0`. -/
lemma tauScRad_deficit_le {v : E3 → ℝ} {ρ μ r : ℝ}
    (hP : 0 < ρ * _root_.BoseGases.a v)
    (hc1 : 0 < bogC1 v ρ μ) (hc2 : 0 < bogC2 v ρ μ)
    (heT0 : 0 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT)
    (heT1 : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT ≤ 1) (hr : 0 ≤ r) :
    r ^ 2 - tauScRad v ρ μ r
      ≤ 3 * bogC1 v ρ μ * r + (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT * r ^ 2 := by
  rw [tauScRad_eq v hP r]
  have hA := sq_sub_c_sq_tauProf_le (c := bogC1 v ρ μ) (r := r) hc1 hr
  have hBnn : 0 ≤ (bogC2 v ρ μ) ^ 2 * Work.BoseBoxFock.tauProf (r / bogC2 v ρ μ) :=
    mul_nonneg (sq_nonneg _) (tauProf_nonneg_aux _)
  have hsplit : r ^ 2 - ((1 - (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT)
        * (bogC1 v ρ μ) ^ 2 * Work.BoseBoxFock.tauProf (r / bogC1 v ρ μ)
      + (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT * (bogC2 v ρ μ) ^ 2
        * Work.BoseBoxFock.tauProf (r / bogC2 v ρ μ))
      = (1 - (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT)
          * (r ^ 2 - (bogC1 v ρ μ) ^ 2 * Work.BoseBoxFock.tauProf (r / bogC1 v ρ μ))
        + (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
          * (r ^ 2 - (bogC2 v ρ μ) ^ 2 * Work.BoseBoxFock.tauProf (r / bogC2 v ρ μ)) := by
    ring
  rw [hsplit]
  have h1 : (1 - (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT)
      * (r ^ 2 - (bogC1 v ρ μ) ^ 2 * Work.BoseBoxFock.tauProf (r / bogC1 v ρ μ))
      ≤ (1 - (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT) * (3 * bogC1 v ρ μ * r) :=
    mul_le_mul_of_nonneg_left hA (by linarith)
  have h2 : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
      * (r ^ 2 - (bogC2 v ρ μ) ^ 2 * Work.BoseBoxFock.tauProf (r / bogC2 v ρ μ))
      ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT * r ^ 2 :=
    mul_le_mul_of_nonneg_left (by linarith [hBnn]) heT0
  have hprod : 0 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT * bogC1 v ρ μ * r :=
    mul_nonneg (mul_nonneg heT0 hc1.le) hr
  nlinarith [h1, h2, hprod]

/-- **The `τ`-term of the bulk row**: for `4c₁ ≤ r`,
`(r²−τ_s,r)/(r²τ_s,r) ≤ 36c₁/r³ + 12ε_T/r²`. -/
lemma bulkTauTerm_le {v : E3 → ℝ} {ρ μ r : ℝ}
    (hP : 0 < ρ * _root_.BoseGases.a v)
    (hc1 : 0 < bogC1 v ρ μ) (hc2 : 0 < bogC2 v ρ μ)
    (heT0 : 0 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT)
    (heT1 : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT ≤ 1 / 2)
    (hr4 : 4 * bogC1 v ρ μ ≤ r) :
    (r ^ 2 - tauScRad v ρ μ r) / (r ^ 2 * tauScRad v ρ μ r)
      ≤ 36 * bogC1 v ρ μ / r ^ 3
        + 12 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT / r ^ 2 := by
  have hr : 0 < r := lt_of_lt_of_le (by linarith) hr4
  have hu8 := tauScRad_ge_eighth_bulk hP hc1 hc2 heT0 heT1 hr4
  have hu : 0 < tauScRad v ρ μ r := lt_of_lt_of_le (by positivity) hu8
  have hdef := tauScRad_deficit_le hP hc1 hc2 heT0 (by linarith) hr.le
  have hnum : 0 ≤ r ^ 2 - tauScRad v ρ μ r :=
    sub_nonneg.mpr (tauScRad_le_sq v hP hc1 hc2 heT0 (by linarith) hr.le)
  have hfirst : (r ^ 2 - tauScRad v ρ μ r) / (r ^ 2 * tauScRad v ρ μ r)
      = ((r ^ 2 - tauScRad v ρ μ r) / tauScRad v ρ μ r) / r ^ 2 := by
    field_simp
  rw [hfirst]
  have hstep : ((r ^ 2 - tauScRad v ρ μ r) / tauScRad v ρ μ r) / r ^ 2
      ≤ ((3 * bogC1 v ρ μ * r
          + (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT * r ^ 2)
          / (r ^ 2 / 8)) / r ^ 2 := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    refine le_trans (div_le_div_of_nonneg_left hnum (by positivity) hu8) ?_
    exact div_le_div_of_nonneg_right hdef (by positivity)
  have hval : ((3 * bogC1 v ρ μ * r
        + (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT * r ^ 2) / (r ^ 2 / 8)) / r ^ 2
      = 24 * bogC1 v ρ μ / r ^ 3
        + 8 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT / r ^ 2 := by
    have hrne : r ≠ 0 := ne_of_gt hr
    field_simp
    ring
  rw [hval] at hstep
  have h4 : 24 * bogC1 v ρ μ / r ^ 3 ≤ 36 * bogC1 v ρ μ / r ^ 3 :=
    div_le_div_of_nonneg_right (by linarith) (by positivity)
  have h5 : 8 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT / r ^ 2
      ≤ 12 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT / r ^ 2 :=
    div_le_div_of_nonneg_right (by linarith) (by positivity)
  linarith [hstep, h4, h5]

/-- **The pointwise bulk row**: on `4c₁ ≤ ‖t‖ ≤ T` the bulk comparison error is
bounded by the radial majorant `bulkRadial`. -/
lemma bulkRow_pointwise {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R ρ μ : ℝ} {t : E3}
    (hR : 0 < R) (hv : ∀ x, 0 ≤ v x) (hvrad : _root_.BoseGases.IsRadial v)
    (hav : 0 < _root_.BoseGases.a v) (hρ : 0 < ρ)
    (heT0 : 0 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT)
    (heT1 : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT ≤ 1 / 2)
    (hc1 : 0 < bogC1 v ρ μ) (hc2 : 0 < bogC2 v ρ μ)
    (hbnn : 0 ≤ betaSc v h ρ μ t)
    (hβc : |betaSc v h ρ μ t - (8 * Real.pi + bogEta v R ρ * ‖t‖)|
        ≤ bogDelta R (Work.BoseFixR.ell v μ) chiTC + 2 * bogEta v R ρ * ‖t‖)
    (hβu : betaSc v h ρ μ t ≤ bogBb R (Work.BoseFixR.ell v μ) chiTC + bogEta v R ρ * ‖t‖)
    (ht : 4 * bogC1 v ρ μ ≤ ‖t‖) (ht2 : ‖t‖ ≤ bogT v R μ) :
    psiSc v h ρ μ t
      - Work.BoseB6Est.fsI1Integrand (bogKernel v R ρ μ)
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
          (bogC1 v ρ μ) (bogC2 v ρ μ) t
      ≤ bulkRadial (bogDelta R (Work.BoseFixR.ell v μ) chiTC) (bogEta v R ρ)
          (bogBb R (Work.BoseFixR.ell v μ) chiTC)
          (8 * Real.pi + bogEta v R ρ * bogT v R μ) (bogC1 v ρ μ)
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT (bogT v R μ) ‖t‖ := by
  have hP : 0 < ρ * _root_.BoseGases.a v := mul_pos hρ hav
  have hη0 : 0 ≤ bogEta v R ρ := bogEta_nonneg v hR.le hρ.le
  have htpos : 0 < ‖t‖ := lt_of_lt_of_le (by linarith) ht
  have hu : 0 < tauScRad v ρ μ ‖t‖ :=
    lt_of_lt_of_le (by positivity) (tauScRad_ge_eighth_bulk hP hc1 hc2 heT0 heT1 ht)
  have hbulk := psiSc_bulk_le (v := v) (h := h) (R := R) (ρ := ρ) (μ := μ) (t := t)
    hR hv hvrad hav hρ heT0 (by linarith) hc1 hc2 hbnn hu hβc hβu
  have hτterm : (‖t‖ ^ 2 - tauScRad v ρ μ ‖t‖) / (‖t‖ ^ 2 * tauScRad v ρ μ ‖t‖)
      ≤ 36 * bogC1 v ρ μ / ‖t‖ ^ 3
        + 12 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT / ‖t‖ ^ 2 :=
    bulkTauTerm_le hP hc1 hc2 heT0 heT1 ht
  have hA2 : (8 * Real.pi + bogEta v R ρ * ‖t‖) ^ 2
      ≤ (8 * Real.pi + bogEta v R ρ * bogT v R μ) ^ 2 := by
    have hle : 8 * Real.pi + bogEta v R ρ * ‖t‖ ≤ 8 * Real.pi + bogEta v R ρ * bogT v R μ := by
      nlinarith [hη0, ht2]
    have h0 : 0 ≤ 8 * Real.pi + bogEta v R ρ * ‖t‖ := by nlinarith [hη0, Real.pi_pos]
    exact pow_le_pow_left₀ h0 hle 2
  have hY0 : 0 ≤ 36 * bogC1 v ρ μ / ‖t‖ ^ 3
      + 12 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT / ‖t‖ ^ 2 := by positivity
  have hτbound : 2 * (8 * Real.pi + bogEta v R ρ * ‖t‖) ^ 2
        * (‖t‖ ^ 2 - tauScRad v ρ μ ‖t‖) / (‖t‖ ^ 2 * (2 * tauScRad v ρ μ ‖t‖))
      ≤ (8 * Real.pi + bogEta v R ρ * bogT v R μ) ^ 2
        * (36 * bogC1 v ρ μ / ‖t‖ ^ 3
          + 12 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT / ‖t‖ ^ 2) := by
    have hX : (8 * Real.pi + bogEta v R ρ * ‖t‖) ^ 2
          * ((‖t‖ ^ 2 - tauScRad v ρ μ ‖t‖) / (‖t‖ ^ 2 * tauScRad v ρ μ ‖t‖))
        = 2 * (8 * Real.pi + bogEta v R ρ * ‖t‖) ^ 2
            * (‖t‖ ^ 2 - tauScRad v ρ μ ‖t‖) / (‖t‖ ^ 2 * (2 * tauScRad v ρ μ ‖t‖)) := by
      field_simp
    rw [← hX]
    exact le_trans (mul_le_mul_of_nonneg_left hτterm (sq_nonneg _))
      (mul_le_mul_of_nonneg_right hA2 hY0)
  have hβmono : (bogDelta R (Work.BoseFixR.ell v μ) chiTC + 2 * bogEta v R ρ * ‖t‖)
        * (1 + (bogBb R (Work.BoseFixR.ell v μ) chiTC + bogEta v R ρ * ‖t‖
            + (8 * Real.pi + bogEta v R ρ * ‖t‖)) / (2 * ‖t‖ ^ 2))
      ≤ (bogDelta R (Work.BoseFixR.ell v μ) chiTC + 2 * bogEta v R ρ * ‖t‖)
        * (1 + (bogBb R (Work.BoseFixR.ell v μ) chiTC + bogEta v R ρ * bogT v R μ
            + (8 * Real.pi + bogEta v R ρ * bogT v R μ)) / (2 * ‖t‖ ^ 2)) := by
    have hδnn : 0 ≤ bogDelta R (Work.BoseFixR.ell v μ) chiTC := by
      rw [bogDelta]
      exact mul_nonneg (mul_nonneg (by positivity) chiTC_nonneg) (sq_nonneg _)
    have hfac : 0 ≤ bogDelta R (Work.BoseFixR.ell v μ) chiTC + 2 * bogEta v R ρ * ‖t‖ := by
      have h2 : 0 ≤ 2 * bogEta v R ρ * ‖t‖ :=
        mul_nonneg (mul_nonneg (by norm_num) hη0) (norm_nonneg t)
      linarith
    apply mul_le_mul_of_nonneg_left _ hfac
    apply add_le_add le_rfl
    apply div_le_div_of_nonneg_right _ (by positivity)
    have hmul : bogEta v R ρ * ‖t‖ ≤ bogEta v R ρ * bogT v R μ :=
      mul_le_mul_of_nonneg_left ht2 hη0
    linarith [hmul]
  rw [bulkRadial]
  linarith [hbulk, hτbound, hβmono]

end

end Work.BoseBogFS
