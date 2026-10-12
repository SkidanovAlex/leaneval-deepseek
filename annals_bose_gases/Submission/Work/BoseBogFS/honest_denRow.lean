import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BoseBogFS.honestKAP
import Submission.Work.BoseBogFS.honest_rows_basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBogFS.honest_denRow` — FS's denominator row at the honest family

This is the **last analytic input** of the honest `𝒞`-slot.  FS's inequality (`thm:BogHamDiag`,
the display after `eq:LowerBoundHBog`)

```
𝒜(k) + ℬ(k) ≥ 2 ρ Ŵ₁(0) (1 − C (μa³) R²/a²)   for every mode k
```

reads, at the honest family `D μ = Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ`
(`E := (D μ).E`, `ℓ := sideAt μ (a v)`, `Λ := uvRad ℓ (HM μ).N`),

```
2 ρ (E.W1 0) (1 − honestDD v μ R) ≤ E.tau k + 2 ρ E.W1 k ,
```

with the explicit slack `honestDD v μ R = 8192 ε₀ (R/a)² ≥ 4096 μaR²` (FS's `C(μa³)R²/a²`).

## The proof

FS's own argument, at the two one-mode rows of
`Work.BoseBogFS.honest_rows_basic`:

* **inside the cut-off ball** (`‖kmom k‖ ≤ Λ`): the cut factor `ζ_Λ` is `1`, so
  `E.W1 k = Ŵ₁(kmom k)` and the second-order variation gives
  `E.W1 k ≥ (∫W₁)(1 − R²‖kmom k‖²/2) ≥ (E.W1 0)(1 − δ_D)` whenever
  `R²‖kmom k‖²/2 ≤ δ_D` (`hin`); the kinetic term is non-negative
  (`honest_tau_kink`), so the row holds;
* **outside the ball**: `E.tau k ≥ (1−ε_T)((‖kmom k‖ − (sℓ)⁻¹)₊)² ≥ 128 π a μ` (`hout`, the
  kinetic-domination row) while `2 ρ E.W1 k ≥ −32 π ρ a ≥ −64 π μ a` (`honest_abs_W1_le` and
  `ρ ≤ 2μ`), which pays the right-hand side `2ρE.W1 0(1−δ_D) ≤ 4μ·12πa = 48πaμ`.

## The two regime rows `hin`/`hout` are the `N`-window

Both are statements about the **choice of the lattice cube size** `N = (HM μ).N`, exactly as in
`Work.BoseBoxFock.RB4boxDomFS` (`∃ Nmin, Nmin μ ≤ (HM μ).N`):

* `hout` needs `Λ_N = πN/(2ℓ) ≳ √(μa)`, i.e. `(1−ε_T)π²N² ≥ 1536 K_ℓ²`, a *lower* bound on `N`;
* `hin` needs `R²Λ_N²/2 ≤ 8192 ε₀ (R/a)²`, i.e. `π²N²μa ≤ 65536 ε₀ K_ℓ²`, an *upper* bound.

The two are compatible for every `μ` because `ε₀ ≥ μa³`:
`1536 K_ℓ² ≲ π²N² ≲ 65536 K_ℓ² ε₀/(μa³)`.
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

/-- `ρ ≤ 2μ` in the close region (`Adm` + `CloseCondFS`): the threshold is at most `μ/2`. -/
theorem rho_le_two_of_close (v : EuclideanSpace ℝ (Fin 3) → ℝ) {ε₀ μ ρ : ℝ}
    (hε₀1 : ε₀ ≤ 1) (hav : 0 < a v) (hadm : Adm v ε₀ μ) (hclose : CloseCondFS v μ ρ) :
    ρ ≤ 2 * μ := by
  have hμ : 0 < μ := hadm.1
  have ht : μ * a v ^ 3 ≤ 1 := le_trans hadm.2.1 hε₀1
  have hKl1 : 1 ≤ (paramsAt μ (a v)).Kl := Kl_ge_one v hμ hav ht
  have hKlpos : 0 < (paramsAt μ (a v)).Kl := lt_of_lt_of_le one_pos hKl1
  have hK2 : ((paramsAt μ (a v)).Kl) ^ (-(2 : ℝ)) ≤ 1 := by
    rw [Real.rpow_neg hKlpos.le, Real.rpow_two]
    exact inv_le_one_of_one_le₀ (by nlinarith)
  have h214 : (2 : ℝ) ^ 14 = 16384 := by norm_num
  have hc1 : ((paramsAt μ (a v)).Kl) ^ (-(2 : ℝ)) / ((2 : ℝ) ^ 14 * π)
      ≤ 1 / ((2 : ℝ) ^ 14 * π) :=
    div_le_div_of_nonneg_right hK2 (by positivity)
  have hc2 : (1 : ℝ) / ((2 : ℝ) ^ 14 * π) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity), h214]
    nlinarith [Real.pi_gt_three]
  have hthr : closeThresholdFS v μ ≤ μ / 2 := by
    rw [closeThresholdFS]
    calc μ * ((paramsAt μ (a v)).Kl) ^ (-(2 : ℝ)) / ((2 : ℝ) ^ 14 * π)
        = μ * (((paramsAt μ (a v)).Kl) ^ (-(2 : ℝ)) / ((2 : ℝ) ^ 14 * π)) := by ring
      _ ≤ μ * (1 / ((2 : ℝ) ^ 14 * π)) := mul_le_mul_of_nonneg_left hc1 hμ.le
      _ ≤ μ * (1 / 2) := mul_le_mul_of_nonneg_left hc2 hμ.le
      _ = μ / 2 := by ring
  have habs := abs_le.mp hclose
  linarith [habs.2, hthr]

/-- **FS's denominator row at the honest family.**  From the two one-mode rows of
`Work.BoseBogFS.honest_rows_basic` and the two `N`-window rows `hin`/`hout`. -/
theorem honest_denRow {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} {HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ}
    {R r₁ C ε₀ : ℝ}
    (hR : 0 < R) (hv : ∀ x, 0 ≤ v x) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hC : 0 ≤ C) (hr₁ : 0 < r₁)
    (hT : ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ r₁ →
      |Submission.BoseGases.conv3 Submission.BoseGases.chi Submission.BoseGases.chi x - 1|
        ≤ C * ‖x‖ ^ 2)
    (hε₀1 : ε₀ ≤ 1) (hav : 0 < a v)
    (hRℓ : ∀ μ : ℝ, Adm v ε₀ μ → R ≤ Work.BoseFixR.ell v μ * Submission.BoseGases.chiR0)
    (hreg : ∀ μ : ℝ, Adm v ε₀ μ → R / Work.BoseBox.sideAt μ (a v) ≤ r₁)
    (hcond : ∀ μ : ℝ, Adm v ε₀ μ →
      C * (R / Work.BoseBox.sideAt μ (a v)) ^ 2 ≤ 1 / 4)
    (hδD1 : ∀ μ : ℝ, Adm v ε₀ μ → honestDD v μ R ≤ 1 / 2)
    (hin : ∀ μ : ℝ, Adm v ε₀ μ → (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).viewFS v h μ →
      ∀ k : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).Mode,
        ‖(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.kmom k‖
            ≤ Work.BoseBoxFock.uvRad (Work.BoseBox.sideAt μ (a v)) (HM μ).N →
          R ^ 2 * ‖(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.kmom k‖ ^ 2 / 2
            ≤ honestDD v μ R)
    (hout : ∀ μ : ℝ, Adm v ε₀ μ → (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).viewFS v h μ →
      ∀ k : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).Mode,
        Work.BoseBoxFock.uvRad (Work.BoseBox.sideAt μ (a v)) (HM μ).N
            < ‖(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.kmom k‖ →
          128 * π * (a v) * μ
            ≤ (1 - (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.eT)
              * (max 0 (‖(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.kmom k‖
                  - ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.s
                    * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.ell)⁻¹)) ^ 2) :
    ∀ μ : ℝ, Adm v ε₀ μ → (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).viewFS v h μ →
      ∀ ρ : ℝ, CloseCondFS v μ ρ → ∀ k : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).Mode,
        2 * ρ * ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1 0) * (1 - honestDD v μ R)
          ≤ (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.tau k
            + 2 * ρ * ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1 k) := by
  intro μ hadm hview ρ hclose k
  have hμ : 0 < μ := hadm.1
  have hρpos : 0 < ρ := rho_pos_of_close v hε₀1 hav hadm hclose
  have hρ2 : ρ ≤ 2 * μ := rho_le_two_of_close v hε₀1 hav hadm hclose
  have hℓpos : 0 < Work.BoseBox.sideAt μ (a v) := sideAt_pos_honest hμ hav
  -- the two mass bounds of `E.W1 0 = ∫W₁`
  have hcond2 : C * (R / Work.BoseBox.sideAt μ (a v)) ^ 2 ≤ 1 / 2 := by
    have h2 := hcond μ hadm
    linarith
  have hb := W1_mass_bounds (v := v) (h := h) (R := R)
    (ℓ := Work.BoseBox.sideAt μ (a v)) (r₁ := r₁) (C := C)
    hR hv hvrad hv_supp hC hr₁ hℓpos hT (hreg μ hadm) hcond2
  have hW0eq := honest_E_W1_zero (h := h) fc fu HM μ
  have hmasslo : 8 * π * a v ≤ (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1 0 := by
    rw [hW0eq]; exact hb.1
  have hmasshi : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1 0 ≤ 12 * π * a v := by
    rw [hW0eq]
    have h2 := hcond μ hadm
    have hstep : 8 * π * a v * (1 + 2 * C * (R / Work.BoseBox.sideAt μ (a v)) ^ 2)
        ≤ 8 * π * a v * (1 + 2 * (1 / 4)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith [hb.2, hstep]
  have habs := honest_abs_W1_le μ hview hv hvrad hR hv_supp (hRℓ μ hadm) k
  have hkink := honest_tau_kink μ hview k
  have hP : Work.BoseB7.FSParamsView (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E :=
    hview.1.some
  have heT1 : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.eT ≤ 1 := by
    rw [hP.eT_eq]
    exact Work.BoseBox.fsXp_le_one hP.t_pos hP.t_le_one (by norm_num)
  have hτ0 : 0 ≤ (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.tau k := by
    have h0 : 0 ≤ (1 - (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.eT)
        * (max 0 (‖(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.kmom k‖
            - ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.s
              * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.ell)⁻¹)) ^ 2 :=
      mul_nonneg (by linarith) (sq_nonneg _)
    linarith [hkink]
  have hav0 : 0 < a v := hav
  by_cases hk : ‖(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.kmom k‖
      ≤ Work.BoseBoxFock.uvRad (Work.BoseBox.sideAt μ (a v)) (HM μ).N
  · -- inside the cut-off ball: the second-order variation
    have hlow := honest_W1_lowband (v := v) (h := h) (fc := fc) (fu := fu) (HM := HM)
      hR hv hvrad hv_supp hC hr₁ hT μ hμ hav (hRℓ μ hadm) (hreg μ hadm) hcond2 k hk
    have hstep := hin μ hadm hview k hk
    have hW0nn : 0 ≤ ∫ x, Work.BoseFixR.W1fun v h (Work.BoseBox.sideAt μ (a v)) x :=
      le_trans (by positivity) hb.1
    have hD : 1 - honestDD v μ R
        ≤ 1 - R ^ 2 * ‖(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.kmom k‖ ^ 2 / 2 := by
      linarith [hstep]
    have h1 : (∫ x, Work.BoseFixR.W1fun v h (Work.BoseBox.sideAt μ (a v)) x)
          * (1 - honestDD v μ R)
        ≤ (∫ x, Work.BoseFixR.W1fun v h (Work.BoseBox.sideAt μ (a v)) x)
          * (1 - R ^ 2 * ‖(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.kmom k‖ ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left hD hW0nn
    have h2 : (∫ x, Work.BoseFixR.W1fun v h (Work.BoseBox.sideAt μ (a v)) x)
          * (1 - honestDD v μ R)
        ≤ (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1 k := le_trans h1 hlow
    have h3 : 2 * ρ * ((∫ x, Work.BoseFixR.W1fun v h (Work.BoseBox.sideAt μ (a v)) x)
          * (1 - honestDD v μ R))
        ≤ 2 * ρ * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1 k :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    rw [hW0eq]
    nlinarith [h3, hτ0]
  · -- outside: the kinetic term dominates
    have houtk := hout μ hadm hview k (lt_of_not_ge hk)
    have htaulow : 128 * π * a v * μ ≤ (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.tau k :=
      le_trans houtk hkink
    have hbnd : -(16 * π * a v) ≤ (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1 k := by
      linarith [abs_le.mp habs]
    have h2ρ : -(64 * π * a v * μ) ≤ 2 * ρ * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1 k := by
      have hρ0 : 0 ≤ ρ := le_of_lt hρpos
      have h1 : 2 * ρ * (-(16 * π * a v))
          ≤ 2 * ρ * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1 k :=
        mul_le_mul_of_nonneg_left hbnd (by positivity)
      have h2 : -(64 * π * a v * μ) ≤ 2 * ρ * (-(16 * π * a v)) := by
        nlinarith [hρ2, Real.pi_pos, hav0]
      linarith [h1, h2]
    have hrhs : 2 * ρ * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1 0
          * (1 - honestDD v μ R)
        ≤ 48 * π * a v * μ := by
      have hρ0 : 0 ≤ ρ := le_of_lt hρpos
      have hW0 : 0 ≤ (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1 0 :=
        le_trans (by positivity) hmasslo
      have hDD0 : 0 ≤ honestDD v μ R := by
        rw [honestDD]
        have hε0 : 0 ≤ ε₀ := le_of_lt (lt_of_lt_of_le (mul_pos hadm.1 (pow_pos hav 3)) hadm.2.1)
        positivity
      have hD1 : 1 - honestDD v μ R ≤ 1 := by linarith [hδD1 μ hadm, hDD0]
      have hstep0 : 2 * ρ * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1 0
            * (1 - honestDD v μ R)
          ≤ 2 * ρ * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1 0 * 1 :=
        mul_le_mul_of_nonneg_left hD1 (by positivity)
      have hstep1 : 2 * ρ * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1 0
          ≤ 2 * ρ * (12 * π * a v) := mul_le_mul_of_nonneg_left hmasshi (by positivity)
      have hstep2 : 2 * ρ * (12 * π * a v) ≤ 2 * (2 * μ) * (12 * π * a v) := by
        have h24 : 0 ≤ 24 * π * a v := by positivity
        have hprod : 0 ≤ 24 * π * a v * (2 * μ - ρ) := mul_nonneg h24 (by linarith)
        linarith [hprod]
      linarith [hstep0, hstep1, hstep2]
    linarith [htaulow, h2ρ, hrhs]

end Work.BoseBogFS
