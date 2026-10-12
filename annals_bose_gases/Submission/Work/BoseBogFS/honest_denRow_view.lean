import ChallengeDeps
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Submission.Work.BoseBoxFock.AllDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBogFS.honest_denRow_view` — FS's denominator row at the honest family, `All` view

FS's inequality (`thm:BogHamDiag`, the display after `eq:LowerBoundHBog`)

```
𝒜(k) + ℬ(k) ≥ 2 ρ Ŵ₁(0) (1 − C (μa³) R²/a²)   for every mode k
```

reads, at the honest family `D μ = Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ`
(`E := (D μ).E`, `δ_D := honestDD v μ R = 8192 μ (a v)³ (R/a v)²`),

```
2 ρ (E.W1 0) (1 − δ_D) ≤ E.tau k + 2 ρ E.W1 k .
```

This is the `viewFSAll` version of `Work.BoseBogFS.honest_denRow`.  The two `N`-window rows
`hin`/`hout` of the latter constrain the lattice size `(HM μ).N`, which `HonestModes` leaves
*free*, so they are not consequences of the view; here they are replaced by a three-range
split of the momentum `p = ‖kmom k‖` against the *view's own* cut-off radius `Λ`, which
satisfies `4 K_L √(μa) ≤ Λ`, together with the standard diluteness threshold
`μ a³ ≤ ε₀ ≤ 2^{−1000}` (which gives `1024 ≤ K_L` and `ε_T ≤ 1/4`):

* `R²p²/2 ≤ δ_D`: then `p ≤ 128√(μa) ≤ 4096√(μa) ≤ Λ`, so the cut factor is `1`,
  `E.W1 k = Ŵ₁(p)`, and the second-order variation `Ŵ₁(p) ≥ (∫W₁)(1 − R²p²/2)` gives
  `E.W1 k ≥ Ŵ₁(0)(1 − δ_D)`; the kinetic term is non-negative;
* `R²p²/2 > δ_D`: then `p > 128√(μa)`, while `(sℓ)⁻¹ = √(μa)(μa³)^{1/646} ≤ √(μa)`, so the
  kink row `E.tau k ≥ (1−ε_T)(p − (sℓ)⁻¹)²` gives `E.tau k ≥ (3/4)(7p/8)² ≥ p²/2 ≥ 8192μa`.
  - `p ≤ Λ`: the same second-order variation, and `δ_D = 8192μaR² ≤ 1/2` gives
    `2ρŴ₁(0)(R²p²/2 − δ_D) ≤ 32π μaR² p² ≤ p²/2 ≤ E.tau k`;
  - `p > Λ`: the cut factor vanishes, so `E.W1 k ≥ −16πa`, and `p²/2 ≥ 8192μa` dominates
    `128πμa = 64πμa + 64πμa ≥ LHS − 2ρ(−16πa)`.

All constants are comfortable (`1024 ≥ 7`, `147/256 > 1/2`, `8192 ≥ 128π`).
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
set_option maxHeartbeats 1000000

/-! ## 0. The numeric input `ε_T = t^{23/1292} ≤ 1/4` -/

/-- `ε_T = t^{23/1292} ≤ 1/4` for `0 < t ≤ 2^{-1000}` (indeed `≤ 2^{-17.8}`).  Sharper than
`Work.BoseBogFS.rpow_23_le_half`; the extra factor is what lets the kinetic kink pay the
second-order variation of `Ŵ₁` below the cut-off radius. -/
theorem rpow_23_le_quarter {t : ℝ} (ht₀ : 0 < t) (htε : t ≤ (1 / 2) ^ 1000) :
    t ^ ((23 : ℝ) / 1292) ≤ 1 / 4 := by
  have hz : (0 : ℝ) ≤ (23 : ℝ) / 1292 := by norm_num
  have h₁ : t ^ ((23 : ℝ) / 1292) ≤ ((1 / 2 : ℝ) ^ 1000) ^ ((23 : ℝ) / 1292) :=
    Real.rpow_le_rpow ht₀.le htε hz
  have h₂ : ((1 / 2 : ℝ) ^ 1000) ^ ((23 : ℝ) / 1292) = (1 / 2 : ℝ) ^ ((5750 : ℝ) / 323) := by
    rw [← Real.rpow_natCast (x := (1 / 2 : ℝ)) (n := 1000),
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    congr 1
    norm_num
  rw [h₂] at h₁
  have h₃ : (2 : ℝ) ≤ (5750 : ℝ) / 323 := by norm_num
  have h₄ : (1 / 2 : ℝ) ^ ((5750 : ℝ) / 323) ≤ (1 / 2 : ℝ) ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) h₃
  have h₅ : (1 / 2 : ℝ) ^ (2 : ℝ) = 1 / 4 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  linarith [h₁, h₄, h₅.le]

/-! ## 1. The denominator row at an arbitrary `viewFSAll` datum -/

/-- **FS's denominator row from the `All` view alone.**  The hypotheses on `μ` are the three
regime rows (`R ≤ ℓ χ_{R₀}`, `R/ℓ ≤ r₁`, `C(R/ℓ)² ≤ 1/2`) plus `honestDD v μ R ≤ 1/2`, and the
diluteness threshold `ε₀ ≤ 2^{-1000}`; no condition on the lattice size is used. -/
theorem denRow_of_viewFSAll {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v}
    {D : Work.BoseFixR.KzDatum} {μ R r₁ C ε₀ : ℝ}
    (hview : D.viewFSAll v h μ)
    (hR : 0 < R) (hv : ∀ x, 0 ≤ v x) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R)
    (hav : 0 < _root_.BoseGases.a v) (hC : 0 ≤ C) (hr₁ : 0 < r₁)
    (hT : ∀ x : ℝ³, ‖x‖ ≤ r₁ →
      |Submission.BoseGases.conv3 Submission.BoseGases.chi Submission.BoseGases.chi x - 1|
        ≤ C * ‖x‖ ^ 2)
    (hε₀1 : ε₀ ≤ (1 / 2) ^ 1000) (hadm : Work.BoseBoxFix.Adm v ε₀ μ)
    (hRℓ : R ≤ Work.BoseFixR.ell v μ * Submission.BoseGases.chiR0)
    (hreg : R / Work.BoseFixR.ell v μ ≤ r₁)
    (hcond : C * (R / Work.BoseFixR.ell v μ) ^ 2 ≤ 1 / 2)
    (hDD1 : honestDD v μ R ≤ 1 / 2) :
    ∀ ρ : ℝ, Work.BoseBoxFock.CloseCondFS v μ ρ → ∀ k : D.Mode,
      2 * ρ * (D.E.W1 0) * (1 - honestDD v μ R)
        ≤ D.E.tau k + 2 * ρ * (D.E.W1 k) := by
  intro ρ hclose k
  -- (a) the view
  have hview' : Work.BoseBoxFock.RViewFSAll v h μ D.F D.T D.E D.gHat0 := hview
  unfold Work.BoseBoxFock.RViewFSAll at hview'
  obtain ⟨hFSP, hmu, hac, hell, hbigM, hbP, hdP, hsP, heTP, hintM, hgHat0, htau, hAenv,
    hBenv, hcut, hw1om, hw1om0, hhatChi, hhatChiSq, hfL, hNH, hCn, hgate⟩ := hview'
  have hvE : Work.BoseB7.FSParamsView D.E := Classical.choice hFSP
  obtain ⟨fuc, Λ, hΛle, hW1eq⟩ := hcut
  -- (b) diluteness data
  have hμpos : 0 < μ := hadm.1
  have hav' : 0 < _root_.BoseGases.a v := hav
  have htpos : 0 < hvE.t := hvE.t_pos
  have ht1 : hvE.t ≤ 1 := hvE.t_le_one
  have ht_eq : hvE.t = μ * (_root_.BoseGases.a v) ^ 3 := by
    rw [← hvE.mu_eq, hmu, hac]
  have htε : hvE.t ≤ (1 / 2) ^ 1000 := by
    rw [ht_eq]
    exact le_trans hadm.2.1 hε₀1
  -- (c) `ε_T`
  have heTv : D.E.eT = hvE.t ^ ((23 : ℝ) / 1292) := by
    rw [hvE.eT_eq, Work.BoseBox.fsXp]
    congr 1
    norm_num
  have heTq : D.E.eT ≤ 1 / 4 := by rw [heTv]; exact rpow_23_le_quarter htpos htε
  have heT1 : D.E.eT ≤ 1 := by linarith
  have heT0 : 0 ≤ D.E.eT := by rw [heTv]; exact Real.rpow_nonneg htpos.le _
  have hs_pos : 0 < D.E.s := by rw [hvE.s_eq]; exact Work.BoseBox.fsXp_pos htpos
  have hd_pos : 0 < D.E.d := by rw [hvE.d_eq]; exact Work.BoseBox.fsXp_pos htpos
  have hEℓpos : 0 < D.E.ell := Work.BoseB7.ell_pos D.E hvE
  -- (d) `1024 ≤ K_L`
  have hKLv : D.E.KL = hvE.t ^ (-(21 / 646 : ℝ)) := by
    have h6 : (Work.BoseBox.fsXp hvE.t 6) ^ 2 = Work.BoseBox.fsXp hvE.t 12 := by
      rw [Work.BoseBox.fsXp_pow htpos.le 6 2]
      congr 1
      norm_num
    have h8 : Work.BoseBox.fsXp hvE.t (-(3 / 2)) * Work.BoseBox.fsXp hvE.t 12
        = Work.BoseBox.fsXp hvE.t (21 / 2) := by
      rw [Work.BoseBox.fsXp_mul htpos (-(3 / 2)) 12]
      congr 1
      norm_num
    have h9 : (Work.BoseBox.fsXp hvE.t (21 / 2))⁻¹ = Work.BoseBox.fsXp hvE.t (-(21 / 2)) :=
      Work.BoseBox.fsXp_inv htpos (21 / 2)
    have h10 : Work.BoseBox.fsXp hvE.t (-(21 / 2)) = hvE.t ^ (-(21 / 646 : ℝ)) := by
      rw [Work.BoseBox.fsXp]
      congr 1
      norm_num
    rw [hvE.KL_eq, Work.BoseB7.KL, hvE.Kl_eq, hvE.d_eq, Real.rpow_neg_one, h6, h8, h9, h10]
  have hKL1024 : 1024 ≤ D.E.KL := by rw [hKLv]; exact rpow_neg21_ge htpos htε
  -- (e) the scale `u = √(μa)`, the cut-off radius `Λ`, and the kink shift `(sℓ)⁻¹`
  have hu_eq : D.E.mu * D.E.aScat = μ * (_root_.BoseGases.a v) := by rw [hmu, hac]
  have hu_nn : 0 ≤ Real.sqrt (D.E.mu * D.E.aScat) := Real.sqrt_nonneg _
  have hu_pos : 0 < Real.sqrt (D.E.mu * D.E.aScat) :=
    Real.sqrt_pos.mpr (by rw [hu_eq]; positivity)
  have hΛbig : 4096 * Real.sqrt (D.E.mu * D.E.aScat) ≤ Λ := by
    have h1 : 1024 * Real.sqrt (D.E.mu * D.E.aScat)
        ≤ D.E.KL * Real.sqrt (D.E.mu * D.E.aScat) :=
      mul_le_mul_of_nonneg_right hKL1024 hu_nn
    linarith [hΛle, h1]
  have hS1 : D.E.s * D.E.ell
      = (Work.BoseBox.fsXp hvE.t 1 * Work.BoseBox.fsXp hvE.t (-(3 / 2)))
        * (D.E.mu * D.E.aScat) ^ (-(1 / 2 : ℝ)) := by
    rw [hvE.s_eq, hvE.ell_eq, Work.BoseB7.side, hvE.Kl_eq]
    ring
  have hS2 : Work.BoseBox.fsXp hvE.t 1 * Work.BoseBox.fsXp hvE.t (-(3 / 2))
      = hvE.t ^ (-(1 / 646 : ℝ)) := by
    rw [Work.BoseBox.fsXp_mul htpos 1 (-(3 / 2)), Work.BoseBox.fsXp]
    congr 1
    norm_num
  have hS3 : (D.E.mu * D.E.aScat) ^ (-(1 / 2 : ℝ))
      = (Real.sqrt (D.E.mu * D.E.aScat))⁻¹ := by
    rw [Real.rpow_neg (by rw [hu_eq]; positivity) (1 / 2), Real.sqrt_eq_rpow]
  have hSe : D.E.s * D.E.ell
      = hvE.t ^ (-(1 / 646 : ℝ)) * (Real.sqrt (D.E.mu * D.E.aScat))⁻¹ := by
    rw [hS1, hS2, hS3]
  have hsl_eq : (D.E.s * D.E.ell)⁻¹
      = Real.sqrt (D.E.mu * D.E.aScat) * hvE.t ^ (1 / 646 : ℝ) := by
    rw [hSe, mul_inv, inv_inv, ← Real.rpow_neg htpos.le, neg_neg]
    ring
  have hsl_le : (D.E.s * D.E.ell)⁻¹ ≤ Real.sqrt (D.E.mu * D.E.aScat) := by
    rw [hsl_eq]
    have h1 : hvE.t ^ (1 / 646 : ℝ) ≤ 1 := Real.rpow_le_one htpos.le ht1 (by norm_num)
    have h2 : Real.sqrt (D.E.mu * D.E.aScat) * hvE.t ^ (1 / 646 : ℝ)
        ≤ Real.sqrt (D.E.mu * D.E.aScat) * 1 :=
      mul_le_mul_of_nonneg_left h1 hu_nn
    simpa using h2
  -- (f) the healing length and the two mass bounds of `Ŵ₁(0) = ∫W₁`
  have hℓpos : 0 < Work.BoseFixR.ell v μ := by
    rw [Work.BoseFixR.ell_eq]
    exact Work.BoseBogFS.sideAt_pos_honest hμpos hav'
  have hb := W1_mass_bounds (v := v) (h := h) (R := R) (ℓ := Work.BoseFixR.ell v μ)
    (r₁ := r₁) (C := C) hR hv hvrad hv_supp hC hr₁ hℓpos hT hreg hcond
  have hkm0 : D.F.kmom 0 = 0 := by
    have h1 : D.F.kmom 0 = -D.F.kmom 0 := by
      have h2 := D.F.kmom_neg 0
      rwa [neg_zero] at h2
    have h2 : (2 : ℝ) • D.F.kmom 0 = 0 := by
      rw [two_smul ℝ (D.F.kmom 0)]
      exact eq_neg_iff_add_eq_zero.mp h1
    rcases smul_eq_zero.mp h2 with h3 | h3
    · norm_num at h3
    · exact h3
  have hW1k_eq : D.E.W1 k = Work.BoseBoxFock.uvCut fuc Λ (D.F.kmom k)
      * Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ)) (D.F.kmom k) :=
    congrFun hW1eq k
  have hW10eq : D.E.W1 0 = ∫ x, Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ) x := by
    have h1 : D.E.W1 0 = Work.BoseBoxFock.uvCut fuc Λ (D.F.kmom 0)
        * Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ)) (D.F.kmom 0) :=
      congrFun hW1eq 0
    rw [h1, hkm0, Work.BoseBoxFock.uvCut, norm_zero, zero_div,
      Work.BoseBoxFix.LowCut.one fuc 0 (by norm_num : (0 : ℝ) ≤ 1), one_mul]
    exact Work.BoseBogFS.chat_zero_eq_integral_uncond _
  have hmasslo : 8 * π * _root_.BoseGases.a v ≤ D.E.W1 0 := by
    rw [hW10eq]
    exact hb.1
  have hmasshi : D.E.W1 0 ≤ 16 * π * _root_.BoseGases.a v := by
    rw [hW10eq]
    have h1 : 1 + 2 * C * (R / Work.BoseFixR.ell v μ) ^ 2 ≤ 2 := by linarith [hcond]
    have h2 : 8 * π * _root_.BoseGases.a v
          * (1 + 2 * C * (R / Work.BoseFixR.ell v μ) ^ 2)
        ≤ 8 * π * _root_.BoseGases.a v * 2 :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    linarith [hb.2, h2]
  -- (g) `|Ŵ₁(k)| ≤ 16πa` (the cut factor is in `[0,1]`)
  have habs : |D.E.W1 k| ≤ 16 * π * _root_.BoseGases.a v := by
    rw [hW1k_eq]
    calc |Work.BoseBoxFock.uvCut fuc Λ (D.F.kmom k)
            * Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ)) (D.F.kmom k)|
        = |Work.BoseBoxFock.uvCut fuc Λ (D.F.kmom k)|
            * |Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ))
                (D.F.kmom k)| := abs_mul _ _
      _ ≤ 1 * |Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ))
              (D.F.kmom k)| :=
          mul_le_mul_of_nonneg_right (abs_uvCut_le_one fuc Λ (D.F.kmom k)) (abs_nonneg _)
      _ = |Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ))
              (D.F.kmom k)| := one_mul _
      _ ≤ 16 * π * _root_.BoseGases.a v :=
          Work.BoseB7AK.W1rows.W1hat_abs_le hR hℓpos (fun x => hv x) hvrad hv_supp h hRℓ
            (D.F.kmom k)
  -- (h) the a.e. sandwich of `W₁`
  have hb_ae := Submission.BoseGases.wScaled_g0_ae_bounds (v := v) (R := R)
    (ℓ := Work.BoseFixR.ell v μ) (r₁ := r₁) (C := C) hR hv hvrad hv_supp h hC hr₁ hT
    hℓpos hreg hcond
  have hg0nn : ∀ᵐ x : ℝ³, 0 ≤ Submission.BoseGases.g0 v h x :=
    Submission.BoseGases.g0_nonneg_ae (v := v) (R := R) hR hv hvrad hv_supp h
  have hg0supp : ∀ x : ℝ³, R ≤ ‖x‖ → Submission.BoseGases.g0 v h x = 0 :=
    fun x hx => Submission.BoseGases.g0_zero_of_norm_ge (v := v) (R := R) hv_supp hx h
  have hWint : MeasureTheory.Integrable (Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ)) := by
    have hh := Submission.BoseGases.wScaled_g0_integrable (v := v) (R := R)
      (ℓ := Work.BoseFixR.ell v μ) hR hv_supp h hℓpos hRℓ
    simpa only [Work.BoseFixR.W1fun] using hh
  have hWnn : ∀ᵐ x : ℝ³, 0 ≤ Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ) x := by
    filter_upwards [hb_ae, hg0nn] with x hx hx0
    simp only [Work.BoseFixR.W1fun]
    linarith [hx.1, hx0]
  have hWsupp : ∀ᵐ x : ℝ³, R < ‖x‖ →
      Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ) x = 0 := by
    filter_upwards [hb_ae, hg0nn] with x hx hx0 hRlt
    simp only [Work.BoseFixR.W1fun]
    have h0 : Submission.BoseGases.g0 v h x = 0 := hg0supp x (le_of_lt hRlt)
    rw [h0, mul_zero] at hx
    linarith [hx.1, hx.2]
  -- (i) the `τ`-pin in the `E`-vocabulary, and the two kink rows
  have htau' : D.E.tau = fun k => Work.BoseBoxFock.tauSm D.E.eT D.E.s D.E.d D.E.ell (D.F.kmom k) := by
    rw [htau, ← heTP, ← hsP, ← hdP, ← hell]
  have htautk : D.E.tau k
      = Work.BoseBoxFock.tauSm D.E.eT D.E.s D.E.d D.E.ell (D.F.kmom k) := congrFun htau' k
  -- (j) the momentum `p`
  set p : ℝ := ‖D.F.kmom k‖ with hp_def
  have hp_nn : 0 ≤ p := by rw [hp_def]; exact norm_nonneg _
  have hτkink : (1 - D.E.eT) * (max 0 (p - (D.E.s * D.E.ell)⁻¹)) ^ 2 ≤ D.E.tau k := by
    have hrow := tauSm_ge_kink (eT := D.E.eT) (s := D.E.s) (d := D.E.d) (ℓ := D.E.ell)
      heT0 heT1 hs_pos hd_pos hEℓpos (D.F.kmom k)
    rw [htautk]
    simpa only [hp_def] using hrow
  have hτ0 : 0 ≤ D.E.tau k :=
    le_trans (mul_nonneg (by linarith) (sq_nonneg _)) hτkink
  -- (k) the `δ_D`-arithmetic
  have hdd_eq : honestDD v μ R = 8192 * (μ * (_root_.BoseGases.a v)) * R ^ 2 := by
    rw [honestDD, max_eq_right hμpos.le, div_pow]
    field_simp
  have hdd_nn : 0 ≤ honestDD v μ R := by
    rw [hdd_eq]
    positivity
  have hμaR : 8192 * (μ * (_root_.BoseGases.a v) * R ^ 2) ≤ 1 / 2 := by
    have h := hDD1
    rw [hdd_eq] at h
    linarith [h]
  have hR2pos : 0 < R ^ 2 := pow_pos hR 2
  have hε01 : ε₀ ≤ 1 := le_trans hε₀1 (by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 : ℝ) / 2 ≤ 1) 1000
    simpa using h)
  have hρpos : 0 < ρ := rho_pos_of_close v hε01 hav' hadm hclose
  have hρ2 : ρ ≤ 2 * μ := rho_le_two_of_close v hε01 hav' hadm hclose
  have hΛpos : 0 < Λ := lt_of_lt_of_le (by positivity) hΛbig
  -- (l) the cut factor is `1` on `‖q‖ ≤ Λ`; the second-order variation there
  have hcut_one {q : ℝ³} (hq : ‖q‖ ≤ Λ) : Work.BoseBoxFock.uvCut fuc Λ q = 1 := by
    rw [Work.BoseBoxFock.uvCut]
    exact Work.BoseBoxFix.LowCut.one fuc _ (by
      rw [div_le_one hΛpos]
      exact hq)
  have hsecond : ∀ q : D.Mode, ‖D.F.kmom q‖ ≤ Λ →
      (D.E.W1 0) * (1 - R ^ 2 * ‖D.F.kmom q‖ ^ 2 / 2) ≤ D.E.W1 q := by
    intro q hq
    have h1 : D.E.W1 q
        = Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ)) (D.F.kmom q) := by
      rw [congrFun hW1eq q, hcut_one hq, one_mul]
    rw [h1, hW10eq]
    exact chat_le_mass_sub_ae (Wt := Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ))
      hWint hR.le hWnn hWsupp (D.F.kmom q)
  have hW0nn : 0 ≤ D.E.W1 0 := le_trans (by positivity) hmasslo
  by_cases hcase : R ^ 2 * p ^ 2 / 2 ≤ honestDD v μ R
  · -- ---- range 1: `R²p²/2 ≤ δ_D` ----
    have hp128 : p ≤ 128 * Real.sqrt (D.E.mu * D.E.aScat) := by
      have h1 : R ^ 2 * (p ^ 2 / 2) ≤ R ^ 2 * (8192 * (μ * (_root_.BoseGases.a v))) := by
        have h := hcase
        rw [hdd_eq] at h
        linarith [h]
      have h2 : p ^ 2 / 2 ≤ 8192 * (μ * (_root_.BoseGases.a v)) :=
        (mul_le_mul_iff_of_pos_left hR2pos).mp h1
      have h3 : p ^ 2 ≤ 16384 * (μ * (_root_.BoseGases.a v)) := by linarith [h2]
      have h4 : (128 * Real.sqrt (D.E.mu * D.E.aScat)) ^ 2
          = 16384 * (μ * (_root_.BoseGases.a v)) := by
        rw [mul_pow, Real.sq_sqrt (by rw [hu_eq]; positivity), hu_eq]
        norm_num
      have h5 : p ^ 2 ≤ (128 * Real.sqrt (D.E.mu * D.E.aScat)) ^ 2 := by
        rw [h4]
        exact h3
      calc p = Real.sqrt (p ^ 2) := (Real.sqrt_sq hp_nn).symm
        _ ≤ Real.sqrt ((128 * Real.sqrt (D.E.mu * D.E.aScat)) ^ 2) := Real.sqrt_le_sqrt h5
        _ = 128 * Real.sqrt (D.E.mu * D.E.aScat) := Real.sqrt_sq (by positivity)
    have hpΛ : p ≤ Λ := by
      have h1 : 128 * Real.sqrt (D.E.mu * D.E.aScat)
          ≤ 4096 * Real.sqrt (D.E.mu * D.E.aScat) :=
        mul_le_mul_of_nonneg_right (by norm_num) hu_nn
      linarith [hp128, h1, hΛbig]
    have hstep : (D.E.W1 0) * (1 - R ^ 2 * p ^ 2 / 2) ≤ D.E.W1 k := by
      have hk : ‖D.F.kmom k‖ ≤ Λ := by simpa only [hp_def] using hpΛ
      simpa only [hp_def] using hsecond k hk
    have hstep' : (D.E.W1 0) * (1 - honestDD v μ R) ≤ D.E.W1 k := by
      have hA : 1 - honestDD v μ R ≤ 1 - R ^ 2 * p ^ 2 / 2 := by linarith [hcase]
      have ha : (D.E.W1 0) * (1 - honestDD v μ R) ≤ (D.E.W1 0) * (1 - R ^ 2 * p ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left hA hW0nn
      linarith [ha, hstep]
    have hfin0 : 2 * ρ * ((D.E.W1 0) * (1 - honestDD v μ R)) ≤ 2 * ρ * (D.E.W1 k) :=
      mul_le_mul_of_nonneg_left hstep' (by linarith : (0 : ℝ) ≤ 2 * ρ)
    have hfin : 2 * ρ * (D.E.W1 0) * (1 - honestDD v μ R) ≤ 2 * ρ * (D.E.W1 k) := by
      have hid : 2 * ρ * ((D.E.W1 0) * (1 - honestDD v μ R))
          = 2 * ρ * (D.E.W1 0) * (1 - honestDD v μ R) := by ring
      linarith [hfin0, hid.le]
    linarith [hfin, hτ0]
  · -- ---- range 2/3: `R²p²/2 > δ_D` ----
    have hII : honestDD v μ R < R ^ 2 * p ^ 2 / 2 := lt_of_not_ge hcase
    have hII' : 8192 * (μ * (_root_.BoseGases.a v)) * R ^ 2 < R ^ 2 * p ^ 2 / 2 := by
      rwa [hdd_eq] at hII
    have hp2big : 16384 * (μ * (_root_.BoseGases.a v)) < p ^ 2 := by
      have h1 : 2 * (8192 * (μ * (_root_.BoseGases.a v)) * R ^ 2) < 2 * (R ^ 2 * p ^ 2 / 2) :=
        by linarith [hII']
      have h2 : R ^ 2 * (16384 * (μ * (_root_.BoseGases.a v))) < R ^ 2 * p ^ 2 := by
        linarith [h1]
      exact (mul_lt_mul_iff_of_pos_left hR2pos).mp h2
    have hp_gt : 128 * Real.sqrt (D.E.mu * D.E.aScat) < p := by
      have h4 : (128 * Real.sqrt (D.E.mu * D.E.aScat)) ^ 2
          = 16384 * (μ * (_root_.BoseGases.a v)) := by
        rw [mul_pow, Real.sq_sqrt (by rw [hu_eq]; positivity), hu_eq]
        norm_num
      have h5 : (128 * Real.sqrt (D.E.mu * D.E.aScat)) ^ 2 < p ^ 2 := by
        rw [h4]
        exact hp2big
      by_contra hcon
      push Not at hcon
      have h6 : p ^ 2 ≤ (128 * Real.sqrt (D.E.mu * D.E.aScat)) ^ 2 :=
        pow_le_pow_left₀ hp_nn hcon 2
      linarith [h5, h6]
    have hthr8 : (D.E.s * D.E.ell)⁻¹ ≤ p / 8 := by
      have h1 : Real.sqrt (D.E.mu * D.E.aScat) < p / 8 := by linarith [hp_gt]
      linarith [hsl_le, h1]
    have hp2 : p ^ 2 / 2 ≤ D.E.tau k := by
      have h1 : (3 / 4 : ℝ) ≤ 1 - D.E.eT := by linarith [heTq]
      have h2 : (7 * p / 8) ≤ max 0 (p - (D.E.s * D.E.ell)⁻¹) :=
        le_trans (by linarith [hthr8]) (le_max_right _ _)
      have h3 : (7 * p / 8) ^ 2 ≤ (max 0 (p - (D.E.s * D.E.ell)⁻¹)) ^ 2 :=
        pow_le_pow_left₀ (by linarith [hp_nn]) h2 2
      have h4 : (3 / 4 : ℝ) * (7 * p / 8) ^ 2 ≤ D.E.tau k :=
        le_trans (mul_le_mul_of_nonneg_right h1 (sq_nonneg (7 * p / 8)))
          (le_trans (mul_le_mul_of_nonneg_left h3 (by linarith [heT1] : (0 : ℝ) ≤ 1 - D.E.eT)) hτkink)
      have h5 : p ^ 2 / 2 ≤ (3 / 4 : ℝ) * (7 * p / 8) ^ 2 := by
        nlinarith [sq_nonneg p]
      linarith [h4, h5]
    have hτ8192 : 8192 * (μ * (_root_.BoseGases.a v)) ≤ D.E.tau k := by
      have h : 2 * (8192 * (μ * (_root_.BoseGases.a v))) ≤ p ^ 2 := by linarith [hp2big]
      linarith [hp2]
    by_cases hpΛ : p ≤ Λ
    · -- ---- range 2: `p ≤ Λ` ----
      have hk : ‖D.F.kmom k‖ ≤ Λ := by simpa only [hp_def] using hpΛ
      have h2nd := hsecond k hk
      have hstep : (D.E.W1 0) * (1 - R ^ 2 * p ^ 2 / 2) ≤ D.E.W1 k := by
        simpa only [hp_def] using h2nd
      have hpay : 2 * ρ * (D.E.W1 0) * (R ^ 2 * p ^ 2 / 2 - honestDD v μ R) ≤ D.E.tau k := by
        have h0 : R ^ 2 * p ^ 2 / 2 - honestDD v μ R ≤ R ^ 2 * p ^ 2 / 2 := by linarith [hdd_nn]
        have h1 : 2 * ρ * (D.E.W1 0) * (R ^ 2 * p ^ 2 / 2 - honestDD v μ R)
            ≤ 2 * ρ * (D.E.W1 0) * (R ^ 2 * p ^ 2 / 2) :=
          mul_le_mul_of_nonneg_left h0 (by positivity)
        have h2 : 2 * ρ * (D.E.W1 0) * (R ^ 2 * p ^ 2 / 2)
            = ρ * (D.E.W1 0) * R ^ 2 * p ^ 2 := by ring
        have h3 : ρ * (D.E.W1 0) ≤ 2 * μ * (16 * π * _root_.BoseGases.a v) := by
          have h4 := mul_le_mul hρ2 hmasshi hW0nn (by positivity : (0 : ℝ) ≤ 2 * μ)
          linarith [h4]
        have h5 : ρ * (D.E.W1 0) * R ^ 2 * p ^ 2
            ≤ (2 * μ * (16 * π * _root_.BoseGases.a v)) * (R ^ 2 * p ^ 2) := by
          have h5' : (ρ * (D.E.W1 0)) * (R ^ 2 * p ^ 2)
              ≤ (2 * μ * (16 * π * _root_.BoseGases.a v)) * (R ^ 2 * p ^ 2) :=
            mul_le_mul_of_nonneg_right h3 (by positivity)
          linarith [h5']
        have h6 : (2 * μ * (16 * π * _root_.BoseGases.a v)) * (R ^ 2 * p ^ 2)
            = 32 * π * (μ * _root_.BoseGases.a v) * R ^ 2 * p ^ 2 := by ring
        have h7 : 32 * π * (μ * _root_.BoseGases.a v) * R ^ 2 ≤ 1 / 2 := by
          have h8 : μ * _root_.BoseGases.a v * R ^ 2 ≤ 1 / 16384 := by linarith [hμaR]
          have h9 : 32 * π * (μ * _root_.BoseGases.a v * R ^ 2)
              ≤ 32 * π * (1 / 16384 : ℝ) :=
            mul_le_mul_of_nonneg_left h8 (by positivity)
          have h10 : 32 * π * (1 / 16384 : ℝ) ≤ 1 / 2 := by
            have h11 : π ≤ 256 := by linarith [Real.pi_lt_four]
            linarith
          linarith [h9, h10]
        have h12 : 32 * π * (μ * _root_.BoseGases.a v) * R ^ 2 * p ^ 2 ≤ p ^ 2 / 2 := by
          have h13 : (32 * π * (μ * _root_.BoseGases.a v) * R ^ 2) * p ^ 2 ≤ (1 / 2) * p ^ 2 :=
            mul_le_mul_of_nonneg_right h7 (sq_nonneg p)
          linarith [h13]
        linarith [h1, h2.le, h5, h6.le, h12, hp2]
      have hstep2 : 2 * ρ * ((D.E.W1 0) * (1 - R ^ 2 * p ^ 2 / 2))
          ≤ 2 * ρ * (D.E.W1 k) :=
        mul_le_mul_of_nonneg_left hstep (by linarith : (0 : ℝ) ≤ 2 * ρ)
      have hsum := add_le_add hstep2 hpay
      have hid : 2 * ρ * ((D.E.W1 0) * (1 - R ^ 2 * p ^ 2 / 2))
            + 2 * ρ * ((D.E.W1 0) * (R ^ 2 * p ^ 2 / 2 - honestDD v μ R))
          = 2 * ρ * (D.E.W1 0) * (1 - honestDD v μ R) := by ring
      linarith [hsum, hid.le, add_comm (D.E.tau k) (2 * ρ * (D.E.W1 k))]
    · -- ---- range 3: `Λ < p` ----
      have hWk : -(16 * π * _root_.BoseGases.a v) ≤ D.E.W1 k := (abs_le.mp habs).1
      have h32ρ : -(64 * π * (μ * (_root_.BoseGases.a v)))
          ≤ 2 * ρ * (-(16 * π * _root_.BoseGases.a v)) := by
        have h1 : ρ * (_root_.BoseGases.a v) ≤ (2 * μ) * (_root_.BoseGases.a v) :=
          mul_le_mul_of_nonneg_right hρ2 hav'.le
        have h2 : 32 * π * (ρ * (_root_.BoseGases.a v))
            ≤ 32 * π * ((2 * μ) * (_root_.BoseGases.a v)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
        have h3 : 32 * π * ((2 * μ) * (_root_.BoseGases.a v))
            = 64 * π * (μ * (_root_.BoseGases.a v)) := by ring
        linarith [h2, h3.le]
      have hτ128 : 128 * π * (μ * (_root_.BoseGases.a v)) ≤ D.E.tau k := by
        have h1 : 128 * π ≤ 8192 := by linarith [Real.pi_lt_four]
        have h2 : 128 * π * (μ * (_root_.BoseGases.a v))
            ≤ 8192 * (μ * (_root_.BoseGases.a v)) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
        linarith [hτ8192, h2]
      have hsup : -(64 * π * (μ * (_root_.BoseGases.a v))) ≤ 2 * ρ * (D.E.W1 k) :=
        le_trans h32ρ (mul_le_mul_of_nonneg_left hWk (by linarith : (0 : ℝ) ≤ 2 * ρ))
      have hLHS : 2 * ρ * (D.E.W1 0) * (1 - honestDD v μ R)
          ≤ 64 * π * (μ * (_root_.BoseGases.a v)) := by
        have h1 : 1 - honestDD v μ R ≤ 1 := by linarith [hdd_nn]
        have h2 : 2 * ρ * (D.E.W1 0) * (1 - honestDD v μ R) ≤ 2 * ρ * (D.E.W1 0) * 1 := by
          have h2nn : 0 ≤ (2 * ρ) * (D.E.W1 0) :=
            mul_nonneg (by linarith [hρpos] : (0 : ℝ) ≤ 2 * ρ) hW0nn
          exact mul_le_mul_of_nonneg_left h1 h2nn
        have h3 : 2 * ρ * (D.E.W1 0) ≤ 2 * (2 * μ) * (16 * π * _root_.BoseGases.a v) := by
          have h4 : (2 * ρ) * (D.E.W1 0) ≤ (2 * (2 * μ)) * (16 * π * _root_.BoseGases.a v) :=
            mul_le_mul (by linarith [hρ2]) hmasshi hW0nn (by linarith [hμpos] : (0 : ℝ) ≤ 2 * (2 * μ))
          linarith [h4]
        have h5 : 2 * (2 * μ) * (16 * π * _root_.BoseGases.a v)
            = 64 * π * (μ * (_root_.BoseGases.a v)) := by ring
        linarith [h2, h3, h5.le]
      linarith [hLHS, hsup, hτ128]

/-! ## 2. The requested statement -/

theorem honest_denRow_view {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut}
    {HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ} {R : ℝ}
    (hR : 0 < R) (hv : ∀ x, 0 ≤ v x) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R) (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).viewFSAll v h μ →
      ∀ ρ : ℝ, Work.BoseBoxFock.CloseCondFS v μ ρ →
      ∀ k : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).Mode,
        2 * ρ * ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1 0)
            * (1 - Work.BoseBogFS.honestDD v μ R)
          ≤ (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.tau k
            + 2 * ρ * ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1 k) := by
  obtain ⟨C, hC, r₁, hr₁, hT⟩ := Submission.BoseGases.conv3chi_second_order_bound
  obtain ⟨εr, hεr0, hreg⟩ :=
    existsAdmRegime (v := v) (R := R) (C := C) (r₁ := r₁) hR hav hC hr₁
  obtain ⟨εd, hεd0, hdd⟩ := exists_adm_honestDD_le v hav hR
  refine ⟨min (min εr εd) ((1 / 2) ^ 1000), lt_min (lt_min hεr0 hεd0) (by norm_num), ?_⟩
  intro μ hadm hview ρ hclose k
  have hAdr : Work.BoseBoxFix.Adm v εr μ :=
    adm_mono (le_trans (min_le_left (min εr εd) ((1 / 2) ^ 1000)) (min_le_left εr εd)) hadm
  have hAdd : Work.BoseBoxFix.Adm v εd μ :=
    adm_mono (le_trans (min_le_left (min εr εd) ((1 / 2) ^ 1000)) (min_le_right εr εd)) hadm
  have hr := hreg μ hAdr
  exact denRow_of_viewFSAll (v := v) (h := h)
    (D := Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ) (μ := μ) (R := R) (r₁ := r₁) (C := C)
    (ε₀ := min (min εr εd) ((1 / 2) ^ 1000))
    hview hR hv hvrad hv_supp hav hC hr₁ hT (min_le_right _ _) hadm hr.1 hr.2.1 hr.2.2
    (hdd μ hAdd) ρ hclose k

end Work.BoseBogFS
