import ChallengeDeps
import Submission.Work.BoseFixB1S.profCubeMom1_le
import Submission.Work.BoseFixB1S.profCubeMom2_le
import Submission.Work.BoseFixB1S.symAFsParamsB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

noncomputable section

open MeasureTheory
open scoped Real Topology BigOperators

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## The cube two-cut comparison at FS's parameters

The cube twin of `Work.BoseFixB1S.symA_mix_at_params`: the FS-parameter instance of the PROVED
`Work.BoseFixB1S.symACube_fsKinCoeff_mix_scaled` at `a = ℓ d`, `C = 1/s`, `ε = ε_T` and
`β = symACube M 1 (fsKinCoeff ((1/s)/2)) 0`.

The two moment criteria of that comparison — `K₁ ≤ 1/s` and `8K₂ ≤ (1−d)²/s²` — are supplied by the
explicit bounds `profCubeMom1_le` (`K₁ ≤ 1 + K₂`) and `profCubeMom2_le` (`K₂ ≤ cubeMomBound M`)
through the pure-real arithmetic `cubeSymArith`, whose smallness threshold `cubeSymScale M` is met
as soon as `μ a³ ≤ cubeSymEps0 M` (because `s = (μ a³)^{1/323}`).  The scalar criteria `0 < s`,
`d ≤ 1/2`, `eT ≤ 1/2` are the *ball* ones (`symACriteriaB1`), which are the same for the cube
cutoff. -/
lemma symACube_mix_at_params {μ a : ℝ}
    (hcrit : 0 < (Work.BoseBox.paramsAt μ a).s ∧ (Work.BoseBox.paramsAt μ a).d ≤ 1 / 2 ∧
      (Work.BoseBox.paramsAt μ a).eT ≤ 1 / 2)
    (hscale : (Work.BoseBox.paramsAt μ a).s ≤ cubeSymScale (Work.BoseBox.paramsAt μ a).M)
    (hell : 0 < Work.BoseBox.sideAt μ a) (hdpos : 0 < (Work.BoseBox.paramsAt μ a).d)
    (heT0 : 0 ≤ (Work.BoseBox.paramsAt μ a).eT) (q : E3) :
    Work.BoseFixB1S.symACube (Work.BoseBox.paramsAt μ a).M
        (Work.BoseBox.sideAt μ a * (Work.BoseBox.paramsAt μ a).d)
        (Submission.BoseGases.fsKinCoeff (Work.BoseFixB1.sbCut μ a)) q
      ≤ (1 - (Work.BoseBox.paramsAt μ a).eT) * Submission.BoseGases.fsKinCoeff
          ((2 * ((Work.BoseBox.paramsAt μ a).s * Work.BoseBox.sideAt μ a))⁻¹) ‖q‖
        + (Work.BoseBox.paramsAt μ a).eT * Submission.BoseGases.fsKinCoeff
            ((2 * ((Work.BoseBox.paramsAt μ a).d * (Work.BoseBox.paramsAt μ a).s
              * Work.BoseBox.sideAt μ a))⁻¹) ‖q‖
        + ((Work.BoseBox.sideAt μ a * (Work.BoseBox.paramsAt μ a).d) ^ 2)⁻¹
          * Work.BoseFixB1S.symACube (Work.BoseBox.paramsAt μ a).M 1
              (Submission.BoseGases.fsKinCoeff ((2 * (Work.BoseBox.paramsAt μ a).s)⁻¹)) 0 := by
  obtain ⟨hs0, hdle, heTle⟩ := hcrit
  have hC : 0 < ((Work.BoseBox.paramsAt μ a).s)⁻¹ := inv_pos.mpr hs0
  have ha' : 0 < Work.BoseBox.sideAt μ a * (Work.BoseBox.paramsAt μ a).d := mul_pos hell hdpos
  have hMone : 1 ≤ (Work.BoseBox.paramsAt μ a).M := by
    show 1 ≤ Work.BoseBox.mValue
    norm_num [Work.BoseBox.mValue]
  -- the two explicit cube moment bounds, and the arithmetic of the threshold
  have hK2 := profCubeMom2_le (Work.BoseBox.paramsAt μ a).M hMone
  have hK1 := profCubeMom1_le (Work.BoseBox.paramsAt μ a).M hMone
  obtain ⟨hcrit1, hcrit2⟩ :=
    cubeSymArith (Work.BoseBox.paramsAt μ a).M hK2 hK1 hs0 hscale hdle
  have hcrit1' : ((2 * Real.pi) ^ 3)⁻¹ *
        (∫ t : E3, (profHatCube (Work.BoseBox.paramsAt μ a).M t) ^ 2 * ‖t‖)
        ≤ ((Work.BoseBox.paramsAt μ a).s)⁻¹ := by
    simpa [one_div] using hcrit1
  have hcrit2' : 8 * (((2 * Real.pi) ^ 3)⁻¹ *
        (∫ t : E3, (profHatCube (Work.BoseBox.paramsAt μ a).M t) ^ 2 * ‖t‖ ^ 2))
        ≤ (1 - (Work.BoseBox.paramsAt μ a).d) ^ 2 * (((Work.BoseBox.paramsAt μ a).s)⁻¹) ^ 2 := by
    simpa [one_div] using hcrit2
  have h := Work.BoseFixB1S.symACube_fsKinCoeff_mix_scaled (Work.BoseBox.paramsAt μ a).M hMone
      (a := Work.BoseBox.sideAt μ a * (Work.BoseBox.paramsAt μ a).d)
      (C := ((Work.BoseBox.paramsAt μ a).s)⁻¹) (d := (Work.BoseBox.paramsAt μ a).d)
      (ε := (Work.BoseBox.paramsAt μ a).eT)
      (β := Work.BoseFixB1S.symACube (Work.BoseBox.paramsAt μ a).M 1
        (Submission.BoseGases.fsKinCoeff (((Work.BoseBox.paramsAt μ a).s)⁻¹ / 2)) 0)
      ha' hC (le_of_lt hdpos) hdle heT0 heTle hcrit1' hcrit2' (le_refl _) q
  -- the four elementary identifications of the cut-offs
  have hsb : ((Work.BoseBox.paramsAt μ a).s)⁻¹
        / (Work.BoseBox.sideAt μ a * (Work.BoseBox.paramsAt μ a).d)
      = Work.BoseFixB1.sbCut μ a := by
    rw [Work.BoseFixB1.sbCut]; field_simp
  have hc1 : (Work.BoseBox.paramsAt μ a).d * ((Work.BoseBox.paramsAt μ a).s)⁻¹
        / (2 * (Work.BoseBox.sideAt μ a * (Work.BoseBox.paramsAt μ a).d))
      = (2 * ((Work.BoseBox.paramsAt μ a).s * Work.BoseBox.sideAt μ a))⁻¹ := by field_simp
  have hc2 : ((Work.BoseBox.paramsAt μ a).s)⁻¹
        / (2 * (Work.BoseBox.sideAt μ a * (Work.BoseBox.paramsAt μ a).d))
      = (2 * ((Work.BoseBox.paramsAt μ a).d * (Work.BoseBox.paramsAt μ a).s
          * Work.BoseBox.sideAt μ a))⁻¹ := by field_simp
  have ht : ((Work.BoseBox.paramsAt μ a).s)⁻¹ / 2
      = (2 * (Work.BoseBox.paramsAt μ a).s)⁻¹ := by field_simp
  rw [hsb, hc1, hc2, ht, div_eq_inv_mul] at h
  exact h

end

theorem symACubeFsParams {v : EuclideanSpace ℝ (Fin 3) → ℝ} :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ q : EuclideanSpace ℝ (Fin 3),
      Work.BoseFixB1S.symACube (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
            * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)
          (Submission.BoseGases.fsKinCoeff (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v))) q
        ≤ (1 - (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT)
            * Submission.BoseGases.fsKinCoeff
                ((2 * ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
                  * Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))⁻¹) ‖q‖
          + (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
            * Submission.BoseGases.fsKinCoeff
                ((2 * ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
                  * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
                  * Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))⁻¹) ‖q‖
          + ((Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
              * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) ^ 2)⁻¹
            * Work.BoseFixB1S.symACube (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M 1
                (Submission.BoseGases.fsKinCoeff
                  ((2 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s)⁻¹)) 0 := by
  refine ⟨min Work.BoseFixB1.KH.symAEps0 (cubeSymEps0 Work.BoseBox.mValue),
    lt_min Work.BoseFixB1.KH.symAEps0_pos (cubeSymEps0_pos Work.BoseBox.mValue), ?_⟩
  intro μ hAdm q
  have ha : 0 < _root_.BoseGases.a v := Work.BoseFixB1.adm_a_pos hAdm
  have hpar : μ * (_root_.BoseGases.a v) ^ 3 ≤ Work.BoseFixB1.KH.symAEps0 :=
    le_trans hAdm.2.1 (min_le_left _ _)
  obtain ⟨hs0, hdle, heTle, -, -⟩ := symACriteriaB1 hAdm.1 ha hpar
  have hcube : μ * (_root_.BoseGases.a v) ^ 3
      ≤ cubeSymEps0 (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M :=
    le_trans hAdm.2.1 (min_le_right _ _)
  have hscale : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
      ≤ cubeSymScale (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M := by
    have hpos : 0 < cubeSymScale (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M :=
      cubeSymScale_pos _
    show Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) 1 ≤ cubeSymScale _
    rw [Work.BoseBox.fsXp]
    calc (μ * (_root_.BoseGases.a v) ^ 3) ^ ((1 : ℝ) / 323)
        ≤ (cubeSymEps0 (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M)
            ^ ((1 : ℝ) / 323) :=
          Real.rpow_le_rpow (mul_nonneg hAdm.1.le (pow_nonneg ha.le 3)) hcube (by norm_num)
      _ = (cubeSymScale (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M ^ (323 : ℝ))
            ^ ((1 : ℝ) / 323) := by
          rw [cubeSymEps0]
      _ = cubeSymScale (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            ^ ((323 : ℝ) * ((1 : ℝ) / 323)) :=
          (Real.rpow_mul hpos.le 323 ((1 : ℝ) / 323)).symm
      _ = cubeSymScale (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M := by
          rw [show (323 : ℝ) * ((1 : ℝ) / 323) = 1 by norm_num, Real.rpow_one]
  exact symACube_mix_at_params ⟨hs0, hdle, heTle⟩ hscale (Work.BoseFixB1.adm_ell_pos hAdm)
    (Work.BoseFixB1.adm_d_pos hAdm) (Work.BoseFixB1.adm_eT_bounds hAdm).1 q

end Work.BoseFixB1S
