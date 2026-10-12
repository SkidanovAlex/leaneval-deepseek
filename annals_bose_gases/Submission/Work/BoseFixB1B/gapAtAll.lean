import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1.perBoxF_thick
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1B.gapAtAll` — the "gap pays" branch of `PerBoxF` at *every* threshold

`Work.BoseFixB1.perBoxF_of_gapPayment` (`Submission/Work/BoseFixB1/perBoxF_thick.lean`) produces
*some* threshold `γ_gap > 0` (explicitly `≤ 10^{-100}`) at which the excited count
`n₊(B) = cnPlusBoxInd … Φ` of the sliding box pays for `PerBoxF` at `c₁ = 1/4`:

    γ_gap · n · ‖Φ‖² ≤ n₊(B)   ⟹   `PerBoxF v h R (1/4) C μ n Φ u`.

The assembly `Work.BoseFixB1B.perBoxF_of_branches` (the dichotomy of FS `thm:smallbox`: the flat
branch below the threshold, the gap branch above it) needs the gap branch at the *flat branch's own*
threshold `γ₀`, which may be **smaller** than `γ_gap`; monotonicity in `γ` only covers `γ ≥ γ_gap`
(`Work.BoseFixB1S.perBoxGapAt_mono`).  This file supplies the missing half: the branch holds at
*every* prescribed `γ > 0`, with the constant `C` and the diluteness threshold `ε₀` depending on `γ`.

## The mathematics

Nothing new is needed beyond a re-run of the proof of `perBoxF_of_gapPayment` with the threshold
coefficient chosen from `γ`.  That proof reduces the crux to the single parameter identity
`c' ^ 2 * γ = c₀ + 1`, where

* `c' > 0` is the constant of FS `eq:appgapestimate` in the form
  `Work.BoseFixB1.sbKin_ge_mu_av_cnPlus`: `c' ^ 2 · μ(a v) · n₊(B) ≤ sbKin`;
* `c₀ = (1/4)·C_W·C_s² + K_av·C_s` is the *fixed* constant that has to be paid for by the gap
  (`C_W` from `w1MassB_le_const_mul_chiMass_regime`, `C_s = chiSupAbs·chiSmallDecay mValue`,
  `K_av` the fibre constant of `fibSum_le`).

The payment is monotone in `c'`: given *any* prescribed `γ > 0` we choose
`c' = sqrt((c₀ + 1)/γ)`, so that `c' ^ 2 · γ = c₀ + 1` exactly, and the same arithmetic closes.
The price is that `c'` now depends on `γ`, hence so does the diluteness threshold
`ε₀ ≤ (2(1+π⁻²)c'² + 1)^{-1292/13}` furnished by `gapRegime_of_adm`; this is legitimate because
both `∃ ε₀` and `∃ C` are allowed to depend on `γ` (`C = 1` works in all cases).

The proof below is therefore the body of `perBoxF_of_gapPayment` with the block
`set csq := 10^{100}(c₀+1)+1`, `c' = sqrt csq`, `γ = (c₀+1)/csq` replaced by the two lines
`c' = sqrt((c₀+1)/γ)`, `c' ^ 2 * γ = c₀ + 1`; everything else is unchanged.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- **The gap branch of `PerBoxF` at every prescribed threshold `γ > 0`** (the auxiliary form,
stated in the `Work.BoseFixB1` namespace so that the copied argument resolves exactly as in
`perBoxF_of_gapPayment`). -/
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
    (by positivity) hμ.le hc'0 (mul_pos hd0 hℓ0) (Work.BoseFixB1.adm_eT_pos hAdm)
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
end Work.BoseFixB1

namespace Work.BoseFixB1B

/-- **FS `thm:smallbox`, gap branch, at every prescribed threshold**: for every `γ > 0` there are
`ε₀ > 0` and `C ≥ 0` (both depending on `γ`) such that every admissible state whose sliding-box
excited count `n₊(B) = cnPlusBoxInd …` dominates `γ·n·‖Φ‖²` satisfies `PerBoxF` at `c₁ = 1/4`. -/
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
  Work.BoseFixB1.gapAtAll_aux (v := v) (h := h) (hv := hv) (hv1 := hv1) (hvrad := hvrad)
    (R := R) (hR := hR) (hv_supp := hv_supp) (hav := hav) (γ := γ) (hγ := hγ)

end Work.BoseFixB1B
