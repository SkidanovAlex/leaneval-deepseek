import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1.Up.Core
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.Up.FreeGap` — the gap branch at *every* threshold, and the free-threshold assembly

Cycle-free (`Up`-renamed) copy of the corpus's `Work.BoseFixB1.gapAtAll_aux`
(`Submission/Work/BoseFixB1B/gapAtAll.lean`), which re-runs the proof of
`Up.perBoxF_of_gapPayment` with the threshold coefficient chosen from the *prescribed* `γ > 0`
(`c' ^ 2 * γ = c₀ + 1`).  Consequence: the dichotomy of `PerBoxF` can be taken at **any**
positive threshold, so the flat branch (the residual) may be stated in its weakest possible form
`∃ γ > 0, PerBoxFlatFree v h R γ` — the prover chooses `γ` as small as they please.

This is a *strict* improvement over the fixed threshold `(1/10)^100` of
`Up.perBoxF_thick_of_flatBranch`: at FS's parameters the particle number `n ≈ μ|B(u)|` is
astronomically large, so with `γ = 10^{-100}` the flat band `n₊ ≤ γ n ‖Φ‖²` still contains states
with a *single* fully excited slot (`n₊ ≈ ‖Φ‖²`), which are *not* mean-field states and are paid
by the kinetic word rather than by the pair term.  A prover of the free-threshold atom may take
`γ ≪ 1/n`, which removes those states from the flat band.

Nothing here is new mathematics: the `gapAtAll_aux` proof is copied verbatim.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseFixB1.Up

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

theorem gapAtAll_aux (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) (γ : ℝ) (hγ : 0 < γ) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
          (u : EuclideanSpace ℝ (Fin 3)),
          γ * (n : ℝ) * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
            ≤ Work.UBBInputs8.cnPlusBoxInd (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                (Φ : Submission.BoseGases.X n → ℝ) →
          Work.BoseFixB1.PerBoxF v h R (1 / 4) C μ n Φ u := by
  obtain ⟨ε₁, hε₁, hsplit⟩ :=
    Work.BoseFixB1S.SbPotHalvesB1Fix (v := v) h hv hv1 hvrad hR hv_supp hav
  obtain ⟨ε₂, CW, hε₂, hCW0, hWle⟩ :=
    w1MassB_le_const_mul_chiMass_regime (v := v) h hv hvrad hR hv_supp
  obtain ⟨εr, hεr, hreg2⟩ := Work.BoseFixB1.regime_sideAt_ge (v := v) hav hR
  -- ## the explicit constants (all independent of the prescribed threshold `γ`)
  have hCs0 : 0 ≤ Submission.BoseGases.chiSupAbs
      * Submission.BoseGases.chiSmallDecay Work.BoseBox.mValue :=
    mul_nonneg Submission.BoseGases.chiSupAbs_nonneg
      (Submission.BoseGases.chiSmallDecay_nonneg _)
  have hKav0 : 0 ≤ 16 * π * Submission.BoseGases.chiSupAbs
      * Submission.BoseGases.chiSmallDecay Work.BoseBox.mValue
      / Work.SmallBoxSliding.smallConvLower Work.BoseBox.mValue :=
    div_nonneg (mul_nonneg (mul_nonneg (by positivity)
      Submission.BoseGases.chiSupAbs_nonneg)
      (Submission.BoseGases.chiSmallDecay_nonneg _))
      (le_of_lt (Work.SmallBoxSliding.smallConvLower_pos _))
  set Cs : ℝ := Submission.BoseGases.chiSupAbs
      * Submission.BoseGases.chiSmallDecay Work.BoseBox.mValue with hCs
  set Kav : ℝ := 16 * π * Submission.BoseGases.chiSupAbs
      * Submission.BoseGases.chiSmallDecay Work.BoseBox.mValue
      / Work.SmallBoxSliding.smallConvLower Work.BoseBox.mValue with hKav
  set c₀ : ℝ := (1 / 4) * CW * Cs ^ 2 + Kav * Cs with hc₀
  have hc₀0 : 0 ≤ c₀ := by
    rw [hc₀]
    exact add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCW0) (sq_nonneg Cs))
      (mul_nonneg hKav0 hCs0)
  -- ## the threshold coefficient `c'` chosen from the *prescribed* `γ`
  -- so that `c' ^ 2 * γ = c₀ + 1`: this is the single place where `γ` enters the arithmetic
  set c' : ℝ := Real.sqrt ((c₀ + 1) / γ) with hc'
  have hc'0 : 0 ≤ c' := Real.sqrt_nonneg _
  have hc'2 : c' ^ 2 = (c₀ + 1) / γ := Real.sq_sqrt (div_nonneg (by linarith) hγ.le)
  have hγeq : c' ^ 2 * γ = c₀ + 1 := by
    rw [hc'2, div_mul_cancel₀ _ (ne_of_gt hγ)]
  obtain ⟨ε₃, hε₃, hreg3⟩ := gapRegime_of_adm (v := v) hav (c' := c') hc'0
  refine ⟨min (min (min ε₁ ε₂) ε₃) (min εr 1), 1,
    lt_min (lt_min (lt_min hε₁ hε₂) hε₃) (lt_min hεr one_pos), zero_le_one, ?_⟩
  intro μ hAdm n Φ u hpay
  have hμ : 0 < μ := hAdm.1
  have hΦc : Continuous (Φ : Submission.BoseGases.X n → ℝ) := Φ.contDiff.continuous
  -- the admissible thresholds
  have hAdm₁ : Work.BoseBoxFix.Adm v ε₁ μ :=
    Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_left _ _) (le_trans (min_le_left _ _)
      (min_le_left _ _)))
  have hAdm₂ : Work.BoseBoxFix.Adm v ε₂ μ :=
    Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_left _ _) (le_trans (min_le_left _ _)
      (min_le_right _ _)))
  have hAdm₃ : Work.BoseBoxFix.Adm v ε₃ μ :=
    Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_left _ _) (min_le_right _ _))
  have hAdmr : Work.BoseBoxFix.Adm v εr μ :=
    Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_right _ _) (min_le_left _ _))
  -- the parameter facts
  have hℓ0 : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := Work.BoseFixB1.adm_ell_pos hAdm
  have hd0 : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d := Work.BoseFixB1.adm_d_pos hAdm
  have hM1 : 1 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M := by
    rw [Work.BoseFixB1.M_eq_mValue]; norm_num [Work.BoseBox.mValue]
  have hdil : μ * (_root_.BoseGases.a v) ^ 3 ≤ εr :=
    le_trans hAdm.2.1 (le_trans (min_le_right _ _) (min_le_left _ _))
  obtain ⟨hR16, hRχ'⟩ := hreg2 μ hμ hdil
  have hA0 : 0 ≤ _root_.BoseGases.a v := le_of_lt hav
  -- ### the ingredients
  have hF := psiWeight_integral_le_thick (μ := μ) hμ (M := (Work.BoseBox.paramsAt μ
    (_root_.BoseGases.a v)).M) (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (d := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) hM1 hℓ0 u hΦc
  have hsc := scountB_le (M := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M)
    (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (d := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) hM1 u hΦc
  have hWle' := hWle μ hAdm₂ u
  have hfib := fibSum_le (v := v) (h := h) hv hvrad hR hv_supp hM1 hℓ0 hd0 hR16 hRχ' u hΦc
  have hchi := chiSum_le (M := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M)
    (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (d := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) hM1 u hΦc
  have hpair0 := pairSum_nonneg (v := v) hv (M := (Work.BoseBox.paramsAt μ
    (_root_.BoseGases.a v)).M) (u := u) (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (d := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)
    (Φ : Submission.BoseGases.X n → ℝ)
  have hW0 := w1MassB_nonneg (M := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M)
    (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (d := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) h hv hvrad hR hv_supp hℓ0 hd0 u
  have hN0 := normB_nonneg (v := v) (μ := μ) (n := n) (Φ : Submission.BoseGases.X n → ℝ)
  have hchi0 := chiMass_nonneg (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
    (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
  have hsplit' := sbPot_split (v := v) (h := h) (R := R) hv_supp hR hv hvrad hv1 hAdm hΦc u hR16 hRχ'
  have hsb : sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ)
      = sbKin (v := v) μ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M u
          (Φ : Submission.BoseGases.X n → ℝ)
        + (-(μ * fibSum h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u (Φ : Submission.BoseGases.X n → ℝ))
            + pairSum v (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u (Φ : Submission.BoseGases.X n → ℝ)) := by
    rw [sbWord, hsplit']
  have hgap := sbKin_ge_mu_av_cnPlus (M := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M)
    (u := u) (Φ := (Φ : Submission.BoseGases.X n → ℝ)) (c' := c')
    (by positivity) hμ.le hc'0 (mul_pos hd0 hℓ0) (Work.BoseFixB1.Up.adm_eT_pos hAdm)
    (hreg3 μ hAdm₃) (Work.BoseFixB1.tBwordKinInd_nonneg _)
  -- ### the arithmetic
  unfold PerBoxF
  simp only [Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB] at hpay ⊢
  set N : ℝ := ∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
      (Φ x) ^ 2 with hN
  set χ : ℝ := chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u with hχ
  set W : ℝ := w1MassB h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u with hW
  set Fterm : ℝ := ∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
      (Φ x) ^ 2 * Work.SmallBoxSliding.psiWeight 1 μ
        (nCountB (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u x
        / chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) with hFt
  set nps : ℝ := Work.UBBInputs8.cnPlusBoxInd (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
      (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
      (Φ : Submission.BoseGases.X n → ℝ) with hnps
  -- the two final bounds
  have hLHS : (1 / 4) * (W * Fterm) - (1 / 2) * μ ^ 2 * W * N
      - 1 * (μ ^ 2 * (_root_.BoseGases.a v)
            * ((R / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
                  * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)) ^ 2
              + (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
                * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ)) * χ * N
          + μ * (_root_.BoseGases.a v) * N)
      ≤ (1 / 4) * CW * (_root_.BoseGases.a v) * μ * (n : ℝ) * Cs ^ 2 * N := by
    have hn : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have h4 : 0 ≤ χ⁻¹ := inv_nonneg.mpr hchi0
    have h5 : 0 ≤ μ * (χ⁻¹ * ((n : ℝ) * Cs ^ 2 * N) + μ * N) := by positivity
    -- the F-term, with the smooth count replaced by `n Cs² N`
    have h6 : Fterm ≤ μ * (χ⁻¹ * ((n : ℝ) * Cs ^ 2 * N) + μ * N) := by
      have hmid : χ⁻¹ * scountB (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
            (Φ : Submission.BoseGases.X n → ℝ)
          ≤ χ⁻¹ * ((n : ℝ) * Cs ^ 2 * N) := mul_le_mul_of_nonneg_left hsc h4
      have hmid2 : χ⁻¹ * scountB (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
            (Φ : Submission.BoseGases.X n → ℝ) + μ * N
          ≤ χ⁻¹ * ((n : ℝ) * Cs ^ 2 * N) + μ * N := by linarith
      exact le_trans hF (mul_le_mul_of_nonneg_left hmid2 hμ.le)
    have h7 : (1 / 4 : ℝ) * (W * Fterm)
        ≤ (1 / 4 : ℝ) * (W * (μ * (χ⁻¹ * ((n : ℝ) * Cs ^ 2 * N) + μ * N))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h6 hW0) (by norm_num)
    have h9 : (1 / 4 : ℝ) * (W * (μ * (χ⁻¹ * ((n : ℝ) * Cs ^ 2 * N) + μ * N)))
        = (1 / 4) * W * μ * (χ⁻¹ * ((n : ℝ) * Cs ^ 2 * N)) + (1 / 4) * W * μ ^ 2 * N := by
      ring
    have h10 : χ * χ⁻¹ ≤ 1 := by
      rcases eq_or_lt_of_le hchi0 with h | h
      · rw [← h, inv_zero, mul_zero]; norm_num
      · rw [mul_inv_cancel₀ (ne_of_gt h)]
    have h11 : W * χ⁻¹ ≤ CW * (_root_.BoseGases.a v) := by
      have h1 : W * χ⁻¹ ≤ (CW * (_root_.BoseGases.a v) * χ) * χ⁻¹ :=
        mul_le_mul_of_nonneg_right hWle' h4
      have h2 : (CW * (_root_.BoseGases.a v) * χ) * χ⁻¹
          = CW * (_root_.BoseGases.a v) * (χ * χ⁻¹) := by ring
      have h3 : CW * (_root_.BoseGases.a v) * (χ * χ⁻¹)
          ≤ CW * (_root_.BoseGases.a v) * 1 :=
        mul_le_mul_of_nonneg_left h10 (mul_nonneg hCW0 hA0)
      linarith [h1, h2, h3]
    have h12 : (1 / 4 : ℝ) * W * μ * (χ⁻¹ * ((n : ℝ) * Cs ^ 2 * N))
        ≤ (1 / 4) * CW * (_root_.BoseGases.a v) * μ * (n : ℝ) * Cs ^ 2 * N := by
      have hfac : (0:ℝ) ≤ (1/4) * μ * ((n : ℝ) * Cs^2 * N) := by positivity
      have h1 : (W * χ⁻¹) * ((1/4) * μ * ((n : ℝ) * Cs^2 * N))
          ≤ (CW * (_root_.BoseGases.a v)) * ((1/4) * μ * ((n : ℝ) * Cs^2 * N)) :=
        mul_le_mul_of_nonneg_right h11 hfac
      calc (1 / 4 : ℝ) * W * μ * (χ⁻¹ * ((n : ℝ) * Cs ^ 2 * N))
          = (W * χ⁻¹) * ((1/4) * μ * ((n : ℝ) * Cs^2 * N)) := by ring
        _ ≤ (CW * (_root_.BoseGases.a v)) * ((1/4) * μ * ((n : ℝ) * Cs^2 * N)) := h1
        _ = (1/4) * CW * (_root_.BoseGases.a v) * μ * (n : ℝ) * Cs ^ 2 * N := by ring
    have h13 : 0 ≤ (1 / 4 : ℝ) * W * μ ^ 2 * N := by positivity
    have h14 : 0 ≤ μ * (_root_.BoseGases.a v) * N := by positivity
    have h15 : 0 ≤ μ ^ 2 * (_root_.BoseGases.a v)
        * ((R / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
              * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)) ^ 2
          + (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
            * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ)) * χ * N := by
      have hKB : (0:ℝ) ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB :=
        le_of_lt (Work.BoseFixB1.paramsAt_KB_pos hAdm)
      have h3 : (0:ℝ) ≤ (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ) :=
        Real.rpow_nonneg (mul_nonneg hμ.le (pow_nonneg hA0 3)) _
      positivity
    linarith [h7, h9, h12, h13, h14, h15]
  have hRHS : c' ^ 2 * μ * (_root_.BoseGases.a v) * nps
      - μ * Kav * (_root_.BoseGases.a v) * (n : ℝ) * Cs * N
      ≤ sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ) := by
    rw [hsb]
    have h1 : μ * fibSum h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u (Φ : Submission.BoseGases.X n → ℝ)
        ≤ μ * (Kav * (_root_.BoseGases.a v) * chiSum
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
            (Φ : Submission.BoseGases.X n → ℝ)) :=
      mul_le_mul_of_nonneg_left hfib hμ.le
    have h2 : μ * (Kav * (_root_.BoseGases.a v) * chiSum
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
            (Φ : Submission.BoseGases.X n → ℝ))
        ≤ μ * (Kav * (_root_.BoseGases.a v) * ((n : ℝ) * Cs * N)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hchi (mul_nonneg hKav0 hA0)) hμ.le
    have h3 : μ * (Kav * (_root_.BoseGases.a v) * ((n : ℝ) * Cs * N))
        = μ * Kav * (_root_.BoseGases.a v) * (n : ℝ) * Cs * N := by ring
    linarith [h1, h2, h3, hgap, hpair0]
  have hkey : (1 / 4) * CW * (_root_.BoseGases.a v) * μ * (n : ℝ) * Cs ^ 2 * N
      ≤ c' ^ 2 * μ * (_root_.BoseGases.a v) * nps
        - μ * Kav * (_root_.BoseGases.a v) * (n : ℝ) * Cs * N := by
    have h1 : c' ^ 2 * μ * (_root_.BoseGases.a v) * nps
        ≥ μ * (_root_.BoseGases.a v) * ((n : ℝ) * N) * (c₀ + 1) := by
      have h2 : c' ^ 2 * μ * (_root_.BoseGases.a v) * (γ * (n : ℝ) * N)
          ≤ c' ^ 2 * μ * (_root_.BoseGases.a v) * nps :=
        mul_le_mul_of_nonneg_left hpay (by positivity)
      have h3 : c' ^ 2 * μ * (_root_.BoseGases.a v) * (γ * (n : ℝ) * N)
          = μ * (_root_.BoseGases.a v) * ((n : ℝ) * N) * (c' ^ 2 * γ) := by ring
      rw [hγeq] at h3
      linarith [h2, h3]
    have h2 : μ * (_root_.BoseGases.a v) * ((n : ℝ) * N) * (c₀ + 1)
        = (1 / 4) * CW * (_root_.BoseGases.a v) * μ * (n : ℝ) * Cs ^ 2 * N
          + μ * Kav * (_root_.BoseGases.a v) * (n : ℝ) * Cs * N
          + μ * (_root_.BoseGases.a v) * ((n : ℝ) * N) := by
      rw [hc₀]; ring
    have h3 : 0 ≤ μ * (_root_.BoseGases.a v) * ((n : ℝ) * N) := by positivity
    linarith [h1, h2, h3]
  calc (1 / 4) * (W * Fterm) - (1 / 2) * μ ^ 2 * W * N
      - 1 * (μ ^ 2 * (_root_.BoseGases.a v)
            * ((R / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
                  * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)) ^ 2
              + (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
                * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ)) * χ * N
          + μ * (_root_.BoseGases.a v) * N)
      ≤ (1 / 4) * CW * (_root_.BoseGases.a v) * μ * (n : ℝ) * Cs ^ 2 * N := hLHS
    _ ≤ c' ^ 2 * μ * (_root_.BoseGases.a v) * nps
        - μ * Kav * (_root_.BoseGases.a v) * (n : ℝ) * Cs * N := hkey
    _ ≤ sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ) := hRHS

/-- **The gap branch at every prescribed threshold.**  For every `γ > 0` there are `ε₀ > 0` and
`C ≥ 0` (depending on `γ`) such that every admissible state whose sliding-box excited count
`n₊(B) = cnPlusBoxInd …` dominates `γ·n·‖Φ‖²` satisfies `PerBoxF` at `c₁ = 1/4`. -/
theorem gapAtAll (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) (γ : ℝ) (hγ : 0 < γ) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
          (u : EuclideanSpace ℝ (Fin 3)),
          γ * (n : ℝ) * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
            ≤ Work.UBBInputs8.cnPlusBoxInd (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                (Φ : Submission.BoseGases.X n → ℝ) →
          Work.BoseFixB1.PerBoxF v h R (1 / 4) C μ n Φ u :=
  gapAtAll_aux (v := v) (h := h) (hv := hv) (hv1 := hv1) (hvrad := hvrad)
    (R := R) (hR := hR) (hv_supp := hv_supp) (hav := hav) (γ := γ) (hγ := hγ)

/-- **The flat branch with free threshold and free constants** — the residual of
`Work.BoseFixB1.perBoxFWeight_holds` in its *weakest* form (the prover chooses `γ` and `c₁`). -/
def PerBoxFlatFree (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) (R γ : ℝ) : Prop :=
  ∃ ε₀ c₁ C : ℝ, 0 < ε₀ ∧ 0 < c₁ ∧ 0 ≤ C ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
        (u : EuclideanSpace ℝ (Fin 3)),
        u ∈ Work.SmallBoxSliding.goodSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ →
        ¬ IsThinBox v h μ u →
        Work.UBBInputs8.cnPlusBoxInd (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
            (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
            (Φ : Submission.BoseGases.X n → ℝ)
          < γ * (n : ℝ) * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) →
        Work.BoseFixB1.PerBoxF v h R c₁ C μ n Φ u

/-- **Monotonicity of `PerBoxF` in the constants.**  `PerBoxF`'s left side reads
`c₁·X − ½μ²·W·N − C·Y` with `X = W·∫Φ²F(t) ≥ 0` and
`Y = μ²(a v)Γ·χ-mass·N + μ(a v)N ≥ 0`, so lowering `c₁` and raising `C` only lowers it. -/
theorem perBoxF_mono_up {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {R : ℝ}
    {ε₀ c₁ c₁' C C' μ : ℝ} (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hAdm : Work.BoseBoxFix.Adm v ε₀ μ) (hc : c₁' ≤ c₁) (hC : C ≤ C')
    {n : ℕ} {Φ : Work.BoseKinLoc.BoxState n (sideAt μ (_root_.BoseGases.a v))}
    {u : EuclideanSpace ℝ (Fin 3)} (hp : Work.BoseFixB1.PerBoxF v h R c₁ C μ n Φ u) :
    Work.BoseFixB1.PerBoxF v h R c₁' C' μ n Φ u := by
  have hμ : 0 < μ := hAdm.1
  have ha : 0 ≤ a v := le_of_lt (adm_a_pos hAdm)
  have hℓ : 0 < sideAt μ (a v) := adm_ell_pos hAdm
  have hd : 0 < (paramsAt μ (a v)).d := adm_d_pos hAdm
  have hW : 0 ≤ w1MassB h (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u :=
    w1MassB_nonneg h hv hvrad hR hv_supp hℓ hd u
  have hA : 0 ≤ ∫ x in abox n (sideAt μ (a v)), (Φ x) ^ 2 *
      psiWeight 1 μ (nCountB (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u x /
        chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u) :=
    integral_nonneg fun x => mul_nonneg (sq_nonneg _)
      (perBoxFCase_psiWeight_nonneg (by norm_num) hμ
        (div_nonneg (nCountB_nonneg x) (chiMass_nonneg _ _ _ _)))
  have hX : 0 ≤ w1MassB h (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u *
      (∫ x in abox n (sideAt μ (a v)), (Φ x) ^ 2 *
        psiWeight 1 μ (nCountB (paramsAt μ (a v)).M (sideAt μ (a v))
          (paramsAt μ (a v)).d u x /
          chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u)) :=
    mul_nonneg hW hA
  have hY : 0 ≤ μ ^ 2 * (a v) * ((R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
        + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
      * chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u
      * normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
      + μ * (a v) * normB v μ n (Φ : Submission.BoseGases.X n → ℝ) := by
    have hKB : 0 ≤ (paramsAt μ (a v)).KB := le_of_lt (paramsAt_KB_pos hAdm)
    have h3 : 0 ≤ (μ * (a v) ^ 3) ^ (1 / 2 : ℝ) :=
      Real.rpow_nonneg (mul_nonneg hμ.le (pow_nonneg ha 3)) _
    have hS : 0 ≤ (R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
        + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ) :=
      add_nonneg (sq_nonneg _) (mul_nonneg (pow_nonneg hKB 3) h3)
    have hN0 : 0 ≤ normB v μ n (Φ : Submission.BoseGases.X n → ℝ) := normB_nonneg _
    have hχ : 0 ≤ chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u :=
      chiMass_nonneg _ _ _ _
    have h1 : 0 ≤ μ ^ 2 * (a v) * ((R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
          + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
        * chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u
        * normB v μ n (Φ : Submission.BoseGases.X n → ℝ) :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg μ) ha) hS) hχ) hN0
    have h2 : 0 ≤ μ * (a v) * normB v μ n (Φ : Submission.BoseGases.X n → ℝ) :=
      mul_nonneg (mul_nonneg hμ.le ha) hN0
    linarith
  unfold Work.BoseFixB1.PerBoxF at hp ⊢
  nlinarith [mul_le_mul_of_nonneg_right hc hX, mul_le_mul_of_nonneg_right hC hY]

/-- **The target's `∃ ε₀ c₁ C`-conclusion from the free-threshold flat atom.**  The gap branch is
available at *every* threshold (`Up.gapAtAll`), so the flat branch may be stated at the prover's
own `γ`; together with the PROVED thin case (`Up.perBoxF_thin_holds`) the three branches cover
every state of the good set. -/
theorem perBoxFWeight_of_flatFree {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v)
    (hfree : ∃ γ : ℝ, 0 < γ ∧ PerBoxFlatFree v h R γ) :
    ∃ ε₀ c₁ C : ℝ, 0 < ε₀ ∧ 0 < c₁ ∧ 0 ≤ C ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
          (u : EuclideanSpace ℝ (Fin 3)),
          u ∈ Work.SmallBoxSliding.goodSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ →
          Work.BoseFixB1.PerBoxF v h R c₁ C μ n Φ u := by
  obtain ⟨γ, hγ, ε₀f, c₁f, Cf, hε₀f, hc₁f, hCf, hF⟩ := hfree
  obtain ⟨ε₀g, Cg, hε₀g, hCg, hG⟩ :=
    gapAtAll (v := v) h hv hv1 hvrad hR hv_supp hav γ hγ
  obtain ⟨ε₀t, c₁t, Ct, hε₀t, hc₁t, hCt, hT⟩ :=
    perBoxF_thin_holds (v := v) (h := h) (R := R) hv hvrad hR hv_supp
  refine ⟨min ε₀t (min ε₀f ε₀g), min c₁t (min c₁f (1 / 4)), max Ct (max Cf Cg),
    lt_min hε₀t (lt_min hε₀f hε₀g), lt_min hc₁t (lt_min hc₁f (by norm_num)),
    le_trans hCt (le_max_left Ct (max Cf Cg)), ?_⟩
  intro μ hAdm n Φ u hu
  have hAdmt : Work.BoseBoxFix.Adm v ε₀t μ :=
    Adm.mono (ε₀' := min ε₀t (min ε₀f ε₀g)) (ε₀ := ε₀t) hAdm (min_le_left _ _)
  have hAdmf : Work.BoseBoxFix.Adm v ε₀f μ :=
    Adm.mono (ε₀' := min ε₀t (min ε₀f ε₀g)) (ε₀ := ε₀f) hAdm
      (le_trans (min_le_right _ _) (min_le_left _ _))
  have hAdmg : Work.BoseBoxFix.Adm v ε₀g μ :=
    Adm.mono (ε₀' := min ε₀t (min ε₀f ε₀g)) (ε₀ := ε₀g) hAdm
      (le_trans (min_le_right _ _) (min_le_right _ _))
  have hc₁ : min c₁t (min c₁f (1 / 4)) ≤ c₁t := min_le_left _ _
  have hc₁f' : min c₁t (min c₁f (1 / 4)) ≤ c₁f :=
    le_trans (min_le_right _ _) (min_le_left _ _)
  have hc₁' : min c₁t (min c₁f (1 / 4)) ≤ 1 / 4 :=
    le_trans (min_le_right _ _) (min_le_right _ _)
  have hCt' : Ct ≤ max Ct (max Cf Cg) := le_max_left _ _
  have hCf' : Cf ≤ max Ct (max Cf Cg) := le_trans (le_max_left Cf Cg) (le_max_right _ _)
  have hCg' : Cg ≤ max Ct (max Cf Cg) := le_trans (le_max_right Cf Cg) (le_max_right _ _)
  by_cases hthin : IsThinBox v h μ u
  · exact perBoxF_mono_up (v := v) (h := h) (R := R) hv hvrad hR hv_supp hAdmt hc₁ hCt'
      (hT μ hAdmt n Φ u hu hthin)
  · by_cases hcase : γ * (n : ℝ) * normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
        ≤ Work.UBBInputs8.cnPlusBoxInd (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
            (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
            (Φ : Submission.BoseGases.X n → ℝ)
    · exact perBoxF_mono_up (v := v) (h := h) (R := R) hv hvrad hR hv_supp hAdmg hc₁' hCg'
        (hG μ hAdmg n Φ u hcase)
    · exact perBoxF_mono_up (v := v) (h := h) (R := R) hv hvrad hR hv_supp hAdmf hc₁f' hCf'
        (hF μ hAdmf n Φ u hu hthin (not_le.mp hcase))

end Work.BoseFixB1.Up
