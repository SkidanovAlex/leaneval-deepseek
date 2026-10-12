import ChallengeDeps
import Submission.Work.BoseBogFS.ViewBridge
import Submission.Work.BoseBogFS.abs_W1_le_viewFS
import Submission.Work.BoseBogFS.chat_le_mass_sub_ae
import Submission.Work.BoseBogFS.honest_W1_mass_rows
import Submission.Work.BoseBogFS.tauSm_ge_kink
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBogFS.honest_rows_basic` — the three one-mode rows of the honest
# denominator estimate

The honest `𝒞`-slot (`Work.BoseBogFS.honestKAP`) leaves FS's denominator row
`𝒜(k) + ℬ(k) ≥ 2ρŴ₁(0)(1 − C(μa³)R²/a²)` as its only analytic hypothesis.  This module
supplies its three one-mode inputs at the honest family
`D μ = Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ` (`E := (D μ).E`):

* `honest_abs_W1_le` — `|Ŵ₁(k)| ≤ 16πa` for **every** mode (FS `eq:WSestimate`); this is the
  global bound used outside the cut-off ball, where `Ŵ₁(k)` may be negative;
* `honest_W1_lowband` — on the cut-off ball `‖kmom k‖ ≤ Λ_N = uvRad ℓ N` the cut factor is `1`
  and the **second-order variation** of `Ŵ₁` applies,
  `Ŵ₁(k) ≥ (∫W₁)(1 − R²‖kmom k‖²/2)`;
* `honest_tau_kink` — the kinetic kink row
  `(1 − ε_T)((‖kmom k‖ − (sℓ)⁻¹)₊)² ≤ τ(k)`.

Only `honest_W1_lowband` needs the disjointness regime `R ≤ ℓ·chiR0` (for the integrability of
`W₁ = wScaled ℓ (g₀)`, `wScaled_g0_integrable`); the other two are unconditional beyond the
standing hypotheses.
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseBogFS

open _root_.BoseGases Submission.BoseGases Work.UBB Work.UBBInputs3 Work.BoseBox
open Work.BoseBoxFix Work.BoseFixR Work.BoseB7

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- **FS `eq:WSestimate` at the honest family**: `|Ŵ₁(k)| ≤ 16πa` for every mode.  This is
`Work.BoseBogFS.abs_W1_le_viewFS` (the cut factor is bounded by `1`, and the uncut estimate is
`L¹`-domination) specialised to `(HonestBoxFam v h fc fu HM μ).E`. -/
theorem honest_abs_W1_le {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} {HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ}
    {R : ℝ} (μ : ℝ) (hview : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).viewFS v h μ)
    (hv : ∀ x, 0 ≤ v x) (hvrad : _root_.BoseGases.IsRadial v) (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hRℓ : R ≤ Work.BoseFixR.ell v μ * Submission.BoseGases.chiR0)
    (k : Work.BoseBoxFock.Lab (HM μ).N) :
    |(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1 k| ≤ 16 * π * _root_.BoseGases.a v := by
  have hviewR : Work.BoseBogFS.RViewFS v h μ
      (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F
      (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).T
      (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E
      (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).gHat0 :=
    RViewFS_of_canonical (v := v) (h := h) (μ := μ) hview
  have h := abs_W1_le_viewFS (v := v) (h := h) (μ := μ)
    (F := (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F)
    (T := (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).T)
    (E := (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E)
    (gHat0 := (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).gHat0)
    hviewR hv hvrad hR hv_supp hRℓ k
  exact h

/-- **The kinetic kink row at the honest family**:
`(1 − ε_T)((‖kmom k‖ − (sℓ)⁻¹)₊)² ≤ τ(k)`.  The parameters `ε_T, s, d, ℓ` come from the
`FSParamsView` inside `viewFS`; the content is `Work.BoseBogFS.tauSm_ge_kink`. -/
theorem honest_tau_kink {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} {HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ}
    (μ : ℝ) (hview : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).viewFS v h μ)
    (k : Work.BoseBoxFock.Lab (HM μ).N) :
    (1 - (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.eT)
        * (max 0 (‖(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.kmom k‖
            - ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.s
              * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.ell)⁻¹)) ^ 2
      ≤ (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.tau k := by
  have hP : Work.BoseB7.FSParamsView (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E :=
    hview.1.some
  have h0 : 0 ≤ (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.eT := by
    rw [hP.eT_eq]; exact Work.BoseBox.fsXp_nonneg hP.t_pos.le
  have h1 : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.eT ≤ 1 := by
    rw [hP.eT_eq]
    exact Work.BoseBox.fsXp_le_one hP.t_pos hP.t_le_one (by norm_num)
  have hs : 0 < (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.s := by
    rw [hP.s_eq]; exact Work.BoseBox.fsXp_pos hP.t_pos
  have hd : 0 < (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.d := by
    rw [hP.d_eq]; exact Work.BoseBox.fsXp_pos hP.t_pos
  have hℓ : 0 < (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.ell :=
    Work.BoseB7.ell_pos _ hP
  have hrow := tauSm_ge_kink (eT := (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.eT)
    (s := (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.s)
    (d := (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.d)
    (ℓ := (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.ell)
    h0 h1 hs hd hℓ ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.kmom k)
  simpa only [Work.BoseBoxFock.HonestBoxFam, Work.BoseBoxFock.KzEnvHon,
    Work.BoseFixR.KzEnvFs] using hrow

/-- **The second-order variation of `Ŵ₁` on the cut-off ball.**  For `‖kmom k‖ ≤ Λ_N` the cut
factor `ζ = uvCut fu Λ_N` is `1`, so `E.W1 k = Ŵ₁(kmom k)`, and the a.e. sandwich
`W₁ = g₀/(χ⋆χ)` (`wScaled_g0_ae_bounds`) with `supp W₁ ⊆ ball 0 R` gives
`Work.BoseBogFS.chat_le_mass_sub_ae`. -/
theorem honest_W1_lowband {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} {HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ}
    {R r₁ C : ℝ}
    (hR : 0 < R) (hv : ∀ x, 0 ≤ v x) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hC : 0 ≤ C) (hr₁ : 0 < r₁)
    (hT : ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ r₁ →
      |Submission.BoseGases.conv3 Submission.BoseGases.chi Submission.BoseGases.chi x - 1|
        ≤ C * ‖x‖ ^ 2)
    (μ : ℝ) (hμ : 0 < μ) (hav : 0 < _root_.BoseGases.a v)
    (hRℓ : R ≤ Work.BoseFixR.ell v μ * Submission.BoseGases.chiR0)
    (hreg : R / Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ≤ r₁)
    (hcond : C * (R / Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 2 ≤ 1 / 2)
    (k : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).Mode)
    (hk : ‖(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.kmom k‖
        ≤ Work.BoseBoxFock.uvRad (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) (HM μ).N) :
    (∫ x, Work.BoseFixR.W1fun v h (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) x)
        * (1 - R ^ 2 * ‖(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.kmom k‖ ^ 2 / 2)
      ≤ (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1 k := by
  have hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := sideAt_pos_honest hμ hav
  have hRℓ' : R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v) * Submission.BoseGases.chiR0 := by
    rw [ell_eq] at hRℓ
    exact hRℓ
  -- the cut factor is `1` on the ball
  have hζ : Work.BoseBoxFock.uvCut fu
      (Work.BoseBoxFock.uvRad (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) (HM μ).N)
      ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.kmom k) = 1 := by
    rw [Work.BoseBoxFock.uvCut]
    refine fu.one _ ?_
    by_cases h0 : Work.BoseBoxFock.uvRad (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) (HM μ).N ≤ 0
    · exact le_trans (div_nonpos_of_nonneg_of_nonpos (norm_nonneg _) h0) (by norm_num)
    · rw [div_le_one (not_le.mp h0)]
      exact hk
  -- the a.e. facts of `W₁ = g₀/(χ⋆χ(·/ℓ))`
  have hb := Submission.BoseGases.wScaled_g0_ae_bounds (v := v) (R := R)
    (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) (r₁ := r₁) (C := C)
    hR hv hvrad hv_supp h hC hr₁ hT hℓ hreg hcond
  have hg0nn : ∀ᵐ x : EuclideanSpace ℝ (Fin 3), 0 ≤ Submission.BoseGases.g0 v h x :=
    Submission.BoseGases.g0_nonneg_ae (v := v) (R := R) hR hv hvrad hv_supp h
  have hg0supp : ∀ x : EuclideanSpace ℝ (Fin 3), R ≤ ‖x‖ →
      Submission.BoseGases.g0 v h x = 0 :=
    fun x hx => Submission.BoseGases.g0_zero_of_norm_ge (v := v) (R := R) hv_supp hx h
  have hWint : Integrable
      (Work.BoseFixR.W1fun v h (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))) := by
    have hh := Submission.BoseGases.wScaled_g0_integrable (v := v) (R := R)
      (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) hR hv_supp h hℓ hRℓ'
    simpa only [Work.BoseFixR.W1fun] using hh
  have hW1 : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1 k
      = Work.BoseBoxFock.uvCut fu
          (Work.BoseBoxFock.uvRad (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) (HM μ).N)
          ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.kmom k)
        * Work.BoseFixR.chat
            (Work.BoseFixR.W1fun v h (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
            ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.kmom k) := rfl
  rw [hW1, hζ, one_mul]
  refine chat_le_mass_sub_ae
    (Wt := Work.BoseFixR.W1fun v h (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
    hWint (le_of_lt hR) ?_ ?_ ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.kmom k)
  · filter_upwards [hb, hg0nn] with x hx hx0
    simp only [Work.BoseFixR.W1fun]
    linarith [hx.1, hx0]
  · filter_upwards [hb, hg0nn] with x hx hx0 hRlt
    simp only [Work.BoseFixR.W1fun]
    have h0 : Submission.BoseGases.g0 v h x = 0 := hg0supp x (le_of_lt hRlt)
    rw [h0, mul_zero] at hx
    linarith [hx.1]

end Work.BoseBogFS
