import Mathlib
import Submission.Work.ThomBordism.boundarySign_chartLocal
import Submission.Work.ThomBordism.boundaryChartAtTail
import Submission.Work.Surgery.Boundary
import Submission.Work.PTGeometric.FlatSource
import Submission.Work.ThomBordism.BCUDefs
import Submission.Work.ThomBordism.chartTr_relHmapOf
import Submission.Work.ThomBordism.bcu_profile2_continuousAt
import Submission.Work.ThomBordism.bcu_profile2_properties
import Submission.Work.ThomBordism.exists_bcu_bump
import Submission.Work.ThomBordism.bsu_modelEquation
import Submission.Work.ThomBordism.boundarySign_transfer_bdry
import Submission.Work.ThomBordism.continuous_bcuPhi_and_mem
import Submission.Work.ThomBordism.relHmapOf_injective_of_chartTr_generator
import Submission.Work.ThomBordism.PosAtlas.chartTr_eq_of_affine_transition
import Submission.Work.PTGeometric.chart_coord_zero_of_mem_boundary
import Submission.Work.Orient.exists_halfBallGood_piece

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The uniform boundary sign of the boundary chart, via the collapse map

`Work.ThomBordism.boundarySign_boundaryChartAt_univ` is proved by transferring the per-instance
chart-local sign (`Work.ThomBordism.boundarySign_chartLocal`) to the standard half-ball model along
the explicit collapse map
`Φ z := profile2 0 (χ z) (τ • (chartAt y z - chartAt y y))` (`Work.ThomBordism.bcuPhi`), where `χ`
is a bump function supported inside the chart at `y` and `τ > 0` is a small scale.  The constant `c`
is inherited from the model (`Work.ThomBordism.bsu_modelEquation`); it is never computed.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

open CategoryTheory
open scoped Manifold Topology ContDiff

namespace Work.ThomBordism

noncomputable section

/-- The `0`-th coordinate of `bcuVa`. -/
theorem bcuVa_coord (n : ℕ) (W : TopCat) [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    (y : W) (τ : ℝ) (z : W) :
    (bcuVa n W y τ z) 0 = τ * ((((chartAt (EuclideanHalfSpace (n + 1)) y) z).1 0) -
      (((chartAt (EuclideanHalfSpace (n + 1)) y) y).1 0)) := by
  simp [bcuVa, bcuCh]

/-- On the chart source, `bcuVa` vanishes only at `y`. -/
theorem bcuVa_eq_zero_iff (n : ℕ) (W : TopCat) [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    {y z : W} {τ : ℝ} (hτ : τ ≠ 0) (hz : z ∈ (chartAt (EuclideanHalfSpace (n + 1)) y).source) :
    bcuVa n W y τ z = 0 ↔ z = y := by
  rw [bcuVa, smul_eq_zero]
  constructor
  · rintro (h | h)
    · exact absurd h hτ
    · have h1 : (chartAt (EuclideanHalfSpace (n + 1)) y) z =
          (chartAt (EuclideanHalfSpace (n + 1)) y) y := by
        refine Subtype.ext ?_
        exact sub_eq_zero.mp h
      exact (chartAt (EuclideanHalfSpace (n + 1)) y).injOn hz (mem_chart_source _ y) h1
  · rintro rfl
    simp [bcuVa]

/-- `bcuVa` is injective on the chart source. -/
theorem bcuVa_injOn (n : ℕ) (W : TopCat) [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    {y z z' : W} {τ : ℝ} (hτ : τ ≠ 0)
    (hz : z ∈ (chartAt (EuclideanHalfSpace (n + 1)) y).source)
    (hz' : z' ∈ (chartAt (EuclideanHalfSpace (n + 1)) y).source)
    (h : bcuVa n W y τ z = bcuVa n W y τ z') : z = z' := by
  have h1 : bcuCh n W y z - bcuCh n W y y = bcuCh n W y z' - bcuCh n W y y := by
    have := h
    rw [bcuVa, bcuVa] at this
    exact smul_right_injective (EuclideanSpace ℝ (Fin (n + 1))) hτ this
  have h2 : bcuCh n W y z = bcuCh n W y z' := by
    have := congrArg (fun v => v + bcuCh n W y y) h1
    simpa using this
  have h3 : (chartAt (EuclideanHalfSpace (n + 1)) y) z =
      (chartAt (EuclideanHalfSpace (n + 1)) y) z' := Subtype.ext h2
  exact (chartAt (EuclideanHalfSpace (n + 1)) y).injOn hz hz' h3

/-- `bcuVa` is nonnegative in its `0`-th coordinate on the chart source. -/
theorem bcuVa_coord_nonneg (n : ℕ) (W : TopCat) [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    {y : W} (hy : y ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
    {τ : ℝ} (hτ : 0 ≤ τ) {z : W}
    (hz : z ∈ (chartAt (EuclideanHalfSpace (n + 1)) y).source) :
    0 ≤ (bcuVa n W y τ z) 0 := by
  have hy0 : (((chartAt (EuclideanHalfSpace (n + 1)) y) y).1 :
      EuclideanSpace ℝ (Fin (n + 1))) 0 = 0 :=
    Work.Orient.Boundary.chartAt_boundary_coord_zero n W hy
  have hz0 : 0 ≤ (((chartAt (EuclideanHalfSpace (n + 1)) y) z).1 :
      EuclideanSpace ℝ (Fin (n + 1))) 0 := ((chartAt (EuclideanHalfSpace (n + 1)) y) z).2
  rw [bcuVa_coord, hy0, sub_zero]
  exact mul_nonneg hτ hz0

/-- `bcuVa` vanishes in its `0`-th coordinate at boundary points. -/
theorem bcuVa_coord_eq_zero_of_boundary (n : ℕ) (W : TopCat) [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 W]
    {y z : W} (hy : y ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
    {τ : ℝ} (hz : z ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
    (hzsrc : z ∈ (chartAt (EuclideanHalfSpace (n + 1)) y).source) :
    (bcuVa n W y τ z) 0 = 0 := by
  have hy0 : (((chartAt (EuclideanHalfSpace (n + 1)) y) y).1 :
      EuclideanSpace ℝ (Fin (n + 1))) 0 = 0 :=
    Work.Orient.Boundary.chartAt_boundary_coord_zero n W hy
  have hz0 : (((chartAt (EuclideanHalfSpace (n + 1)) y) z).1 :
      EuclideanSpace ℝ (Fin (n + 1))) 0 = 0 :=
    Work.PTGeometric.chart_coord_zero_of_mem_boundary n W hzsrc hz
  rw [bcuVa_coord, hy0, hz0, sub_zero, mul_zero]

/-- **The collapse does not vanish away from `y`.** -/
theorem bcuPhi_ne_zero (n : ℕ) (W : TopCat) [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    {y : W} (hy : y ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
    {τ : ℝ} (hτ : 0 < τ) {χ : W → ℝ}
    (hχ01 : ∀ z, 0 ≤ χ z ∧ χ z ≤ 1)
    (hout : ∀ z, z ∉ (chartAt (EuclideanHalfSpace (n + 1)) y).source → χ z = 0)
    {z : W} (hz : z ≠ y) : bcuPhi n W y τ χ z ≠ 0 := by
  intro hcon
  by_cases hmem : z ∈ (chartAt (EuclideanHalfSpace (n + 1)) y).source
  · have hv0 : bcuVa n W y τ z ≠ 0 :=
      fun h0 => hz ((bcuVa_eq_zero_iff n W (ne_of_gt hτ) hmem).mp h0)
    have hv0' : 0 ≤ (bcuVa n W y τ z) 0 := bcuVa_coord_nonneg n W hy (le_of_lt hτ) hmem
    rw [bcuPhi_apply] at hcon
    by_cases h1 : χ z ≤ 1 / 2
    · rw [BCU.profile2, if_pos h1] at hcon
      exact BCU.bcu_northPole_ne_zero n hcon
    · by_cases h2 : χ z ≤ 3 / 4
      · have hlt1 : 1 / 2 < χ z := lt_of_not_ge h1
        have hφ0 : 0 ≤ (3 / 4 - χ z) * 2 * Real.pi :=
          mul_nonneg (by linarith) (by positivity)
        have hφ1 : (3 / 4 - χ z) * 2 * Real.pi ≤ Real.pi / 2 := by
          have h4 : (3 / 4 - χ z) * 2 ≤ 1 / 2 := by linarith
          nlinarith [Real.pi_pos]
        have hcos : 0 ≤ Real.cos ((3 / 4 - χ z) * 2 * Real.pi) :=
          Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hφ1⟩
        have hsin : 0 ≤ Real.sin ((3 / 4 - χ z) * 2 * Real.pi) :=
          Real.sin_nonneg_of_mem_Icc ⟨hφ0, by linarith [Real.pi_pos]⟩
        rw [BCU.profile2, if_neg h1, if_pos h2] at hcon
        have hnorm := BCU.bcu_sphPhase_norm_eq_one ((3 / 4 - χ z) * 2 * Real.pi)
          (bcuVa n W y τ z) hv0 hcos hsin hv0'
        rw [hcon] at hnorm
        simp at hnorm
      · have hlt : 3 / 4 < χ z := lt_of_not_ge h2
        have hp0 : 0 ≤ (1 - χ z) * 4 := mul_nonneg (by linarith [(hχ01 z).2]) (by norm_num)
        have hp1 : (1 - χ z) * 4 ≤ 1 := by linarith [(hχ01 z).2]
        have hcoef : 0 < (1 - χ z) * 4 / ‖bcuVa n W y τ z‖ + (1 - (1 - χ z) * 4) := by
          rcases eq_or_lt_of_le hp0 with hp | hp
          · rw [← hp]; simp
          · have h3 : 0 < (1 - χ z) * 4 / ‖bcuVa n W y τ z‖ :=
              div_pos hp (norm_pos_iff.mpr hv0)
            have h4 : 0 ≤ 1 - (1 - χ z) * 4 := by linarith
            linarith
        have harg : ((1 - χ z) * 4 / ‖bcuVa n W y τ z‖ + (1 - (1 - χ z) * 4)) •
            bcuVa n W y τ z ≠ 0 := smul_ne_zero (ne_of_gt hcoef) hv0
        rw [BCU.profile2, if_neg h1, if_neg h2, BCU.shiftPhase2] at hcon
        rw [smul_zero, add_zero] at hcon
        exact harg ((BCU.bcu_clampBall_eq_zero _).mp hcon)
  · rw [bcuPhi_eq_northPole n W y τ χ z (hout z hmem)] at hcon
    exact BCU.bcu_northPole_ne_zero n hcon

/-- **The boundary preservation of the collapse** (as a disjunction). -/
theorem bcuPhi_bdry_disj (n : ℕ) (W : TopCat) [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 W]
    {y z : W} (hy : y ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
    (hz : z ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
    {τ : ℝ} (hτ : 0 < τ) {χ : W → ℝ}
    (hχ01 : ∀ z, 0 ≤ χ z ∧ χ z ≤ 1)
    (hout : ∀ z, z ∉ (chartAt (EuclideanHalfSpace (n + 1)) y).source → χ z = 0)
    (hy1 : χ y = 1) :
    (bcuPhi n W y τ χ z) 0 = 0 ∨ ‖bcuPhi n W y τ χ z‖ = 1 := by
  by_cases hmem : z ∈ (chartAt (EuclideanHalfSpace (n + 1)) y).source
  · have hz0 : (bcuVa n W y τ z) 0 = 0 := bcuVa_coord_eq_zero_of_boundary n W hy hz hmem
    by_cases hχ : χ z ≤ 1 / 2
    · rw [bcuPhi_apply, BCU.profile2, if_pos hχ, BCU.bcu_northPole_norm]
      exact Or.inr rfl
    · by_cases hv : bcuVa n W y τ z = 0
      · have hzy : z = y := (bcuVa_eq_zero_iff n W (ne_of_gt hτ) hmem).mp hv
        rw [bcuPhi_apply, hzy, bcuVa_self, hy1, bcu_profile2_one_zero]
        exact Or.inl rfl
      · obtain ⟨ha, hb⟩ := (Work.ThomBordism.bcu_profile2_properties n).2.1 0
          (bcuVa n W y τ z) (χ z) rfl hz0 hv
        rw [bcuPhi_apply]
        exact hb
  · rw [bcuPhi_eq_northPole n W y τ χ z (hout z hmem), BCU.bcu_northPole_norm]
    exact Or.inr rfl

/-- **The fibre of the collapse at the prescribed interior value.** -/
theorem bcuPhi_eq_of_eq (n : ℕ) (W : TopCat) [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 W]
    {y x₀ : W} (hy : y ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
    {τ : ℝ} (hτ : 0 < τ)
    (hVpos : 0 < (bcuVa n W y τ x₀) 0)
    (hVeq : ∀ z ∈ (chartAt (EuclideanHalfSpace (n + 1)) y).source,
      bcuVa n W y τ z = bcuVa n W y τ x₀ → z = x₀)
    {χ : W → ℝ} (hχ01 : ∀ z, 0 ≤ χ z ∧ χ z ≤ 1)
    (hout : ∀ z, z ∉ (chartAt (EuclideanHalfSpace (n + 1)) y).source → χ z = 0)
    (S : Set W) (hS : ∀ z ∈ S, χ z = 1) (hyS : y ∈ S)
    (hSray : ∀ z ∈ (chartAt (EuclideanHalfSpace (n + 1)) y).source,
      (∃ m : ℝ, 0 ≤ m ∧ m ≤ 1 ∧ bcuVa n W y τ z = m • bcuVa n W y τ x₀) → z ∈ S)
    (hVne : bcuVa n W y τ x₀ ≠ 0)
    (hVnorm : ‖bcuVa n W y τ x₀‖ ≤ 1 / 2)
    {z : W} (hz : bcuPhi n W y τ χ z = bcuVa n W y τ x₀) : z = x₀ := by
  by_cases hmem : z ∈ (chartAt (EuclideanHalfSpace (n + 1)) y).source
  · have hv0 : bcuVa n W y τ z ≠ 0 := by
      intro h0
      have hzy := (bcuVa_eq_zero_iff n W (ne_of_gt hτ) hmem).mp h0
      rw [bcuPhi_apply, hzy, bcuVa_self, hS y hyS, bcu_profile2_one_zero] at hz
      exact hVne hz.symm
    have hv0' : 0 ≤ (bcuVa n W y τ z) 0 := bcuVa_coord_nonneg n W hy (le_of_lt hτ) hmem

    rw [bcuPhi_apply] at hz
    by_cases hχ : χ z ≤ 1 / 2
    · rw [BCU.profile2, if_pos hχ] at hz
      have hnorm := congrArg norm hz
      rw [BCU.bcu_northPole_norm] at hnorm
      linarith [norm_nonneg (bcuVa n W y τ x₀)]
    · by_cases hχ2 : χ z ≤ 3 / 4
      · have hlt1 : 1 / 2 < χ z := lt_of_not_ge hχ
        have hφ0 : 0 ≤ (3 / 4 - χ z) * 2 * Real.pi :=
          mul_nonneg (by linarith) (by positivity)
        have hφ1 : (3 / 4 - χ z) * 2 * Real.pi ≤ Real.pi / 2 := by
          have h4 : (3 / 4 - χ z) * 2 ≤ 1 / 2 := by linarith
          nlinarith [Real.pi_pos]
        have hcos : 0 ≤ Real.cos ((3 / 4 - χ z) * 2 * Real.pi) :=
          Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hφ1⟩
        have hsin : 0 ≤ Real.sin ((3 / 4 - χ z) * 2 * Real.pi) :=
          Real.sin_nonneg_of_mem_Icc ⟨hφ0, by linarith [Real.pi_pos]⟩
        rw [BCU.profile2, if_neg hχ, if_pos hχ2] at hz
        have hnorm := BCU.bcu_sphPhase_norm_eq_one ((3 / 4 - χ z) * 2 * Real.pi)
          (bcuVa n W y τ z) hv0 hcos hsin hv0'
        rw [hz] at hnorm
        linarith [norm_nonneg (bcuVa n W y τ x₀)]
      · have hlt : 3 / 4 < χ z := lt_of_not_ge hχ2
        have hfib := (Work.ThomBordism.bcu_profile2_properties n).2.2.2.2.2
          0 (bcuVa n W y τ z) (bcuVa n W y τ x₀) (χ z) rfl hv0' hv0 hVpos hVnorm hz
        rw [smul_zero, add_zero] at hfib
        rcases hfib with hconj | halg
        · exact hVeq z hmem hconj.2
        · by_cases hχ1 : χ z = 1
          · have h := halg
            rw [hχ1] at h
            norm_num at h
            exact hVeq z hmem h
          · exfalso
            set p : ℝ := (1 - χ z) * 4 with hpdef
            have hp0 : 0 < p := by
              rw [hpdef]
              have hlt : χ z < 1 := lt_of_le_of_ne (hχ01 z).2 hχ1
              nlinarith
            have hp1 : p < 1 := by
              rw [hpdef]
              have : 0 < 1 - χ z := by linarith [(hχ01 z).2]
              linarith
            set lam : ℝ := p / ‖bcuVa n W y τ z‖ + (1 - p) with hldef
            have hlam : 0 < lam := by
              rw [hldef]
              have h3 : 0 < p / ‖bcuVa n W y τ z‖ := div_pos hp0 (norm_pos_iff.mpr hv0)
              have h4 : 0 < 1 - p := by linarith
              linarith
            have heq : lam • bcuVa n W y τ z = bcuVa n W y τ x₀ := by
              rw [← halg]
            have hmu : bcuVa n W y τ z = lam⁻¹ • bcuVa n W y τ x₀ := by
              rw [← heq, ← smul_assoc, smul_eq_mul, inv_mul_cancel₀ (ne_of_gt hlam), one_smul]
            have hmu0 : 0 ≤ lam⁻¹ := le_of_lt (inv_pos.mpr hlam)
            have hmu1 : lam⁻¹ ≤ 1 := by
              have hnorm_v : lam * ‖bcuVa n W y τ z‖ = ‖bcuVa n W y τ x₀‖ := by
                have hh := congrArg norm heq
                rwa [norm_smul, Real.norm_eq_abs, abs_of_pos hlam] at hh
              have hexp : lam * ‖bcuVa n W y τ z‖ = p + (1 - p) * ‖bcuVa n W y τ z‖ := by
                rw [hldef]
                field_simp
              have hvle : ‖bcuVa n W y τ z‖ ≤ ‖bcuVa n W y τ x₀‖ := by
                nlinarith [hp0, hp1, hnorm_v, hexp, hVnorm]
              have hVpos : 0 < ‖bcuVa n W y τ x₀‖ := norm_pos_iff.mpr hVne
              have hinv : lam⁻¹ = ‖bcuVa n W y τ z‖ / ‖bcuVa n W y τ x₀‖ := by
                field_simp
                linarith [hnorm_v]
              rw [hinv, div_le_one hVpos]
              exact hvle
            have hzS : z ∈ S := hSray z hmem ⟨lam⁻¹, hmu0, hmu1, hmu⟩
            have h1 := hS z hzS
            rw [h1] at hpdef
            rw [hpdef] at hp0
            norm_num at hp0
  · rw [bcuPhi_eq_northPole n W y τ χ z (hout z hmem)] at hz
    have hnorm := congrArg norm hz
    rw [BCU.bcu_northPole_norm] at hnorm
    linarith [norm_nonneg (bcuVa n W y τ x₀)]

/-! ## Comparing `bcuVa` with `x₀` through the interior chart -/

/-- **Injectivity of `bcuVa` at `x₀`**, using only `x₀ ∈ (icChart n W y).source`. -/
theorem bcuVa_eq_of_icChart (n : ℕ) (W : TopCat) [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 W]
    {y x₀ : W} {τ : ℝ} (hτ : τ ≠ 0)
    (hx₀ : x₀ ∈ (Work.PTGeometric.icChart n W y).source)
    {z : W} (hz : z ∈ (chartAt (EuclideanHalfSpace (n + 1)) y).source)
    (h : bcuVa n W y τ z = bcuVa n W y τ x₀) : z = x₀ := by
  have h1 : ((chartAt (EuclideanHalfSpace (n + 1)) y) z).1 =
      ((chartAt (EuclideanHalfSpace (n + 1)) y) x₀).1 := by
    have h' := h
    rw [bcuVa, bcuVa] at h'
    have h2 := smul_right_injective (EuclideanSpace ℝ (Fin (n + 1))) hτ h'
    have h3 := congrArg (fun v => v + bcuCh n W y y) h2
    simpa using h3
  have h2 : (extChartAt (modelWithCornersEuclideanHalfSpace (n + 1)) y) z =
      (extChartAt (modelWithCornersEuclideanHalfSpace (n + 1)) y) x₀ := by
    rw [extChartAt_coe]
    simp only [Function.comp_apply]
    rw [modelWithCornersEuclideanHalfSpace_toFun (n + 1)]
    exact h1
  have hz' : z ∈ (extChartAt (modelWithCornersEuclideanHalfSpace (n + 1)) y).source := by
    rwa [extChartAt_source]
  calc z = (extChartAt (modelWithCornersEuclideanHalfSpace (n + 1)) y).symm
        ((extChartAt (modelWithCornersEuclideanHalfSpace (n + 1)) y) z) :=
        ((extChartAt (modelWithCornersEuclideanHalfSpace (n + 1)) y).left_inv hz').symm
    _ = (extChartAt (modelWithCornersEuclideanHalfSpace (n + 1)) y).symm
        ((extChartAt (modelWithCornersEuclideanHalfSpace (n + 1)) y) x₀) := by rw [h2]
    _ = (Work.PTGeometric.icChart n W y).symm ((Work.PTGeometric.icChart n W y) x₀) := by
        rw [Work.PTGeometric.icChart_coe_symm, Work.PTGeometric.icChart_coe]
    _ = x₀ := (Work.PTGeometric.icChart n W y).left_inv hx₀

/-- `bcuVa` does not vanish at `x₀` (for `x₀` in the interior chart). -/
theorem bcuVa_ne_zero_of_icChart (n : ℕ) (W : TopCat) [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 W]
    {y x₀ : W} (hy : y ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
    {τ : ℝ} (hτ : τ ≠ 0)
    (hx₀ : x₀ ∈ (Work.PTGeometric.icChart n W y).source)
    (hint : x₀ ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) :
    bcuVa n W y τ x₀ ≠ 0 := by
  intro h0
  have h1 : ((chartAt (EuclideanHalfSpace (n + 1)) y) x₀).1 =
      ((chartAt (EuclideanHalfSpace (n + 1)) y) y).1 := by
    have h' := h0
    rw [bcuVa] at h'
    have h2 := smul_eq_zero.mp h'
    rcases h2 with h2 | h2
    · exact absurd h2 hτ
    · have h3 := congrArg (fun v => v + bcuCh n W y y) h2
      simpa [bcuCh] using h3
  have h2 : (extChartAt (modelWithCornersEuclideanHalfSpace (n + 1)) y) x₀ =
      (extChartAt (modelWithCornersEuclideanHalfSpace (n + 1)) y) y := by
    rw [extChartAt_coe]
    simp only [Function.comp_apply]
    rw [modelWithCornersEuclideanHalfSpace_toFun (n + 1)]
    exact h1
  have hval : (Work.PTGeometric.icChart n W y) x₀ = (Work.PTGeometric.icChart n W y) y := by
    rw [Work.PTGeometric.icChart_coe]
    exact h2
  have h3 : x₀ = y := by
    calc x₀ = (Work.PTGeometric.icChart n W y).symm ((Work.PTGeometric.icChart n W y) x₀) :=
          ((Work.PTGeometric.icChart n W y).left_inv hx₀).symm
      _ = (Work.PTGeometric.icChart n W y).symm ((Work.PTGeometric.icChart n W y) y) :=
          congrArg _ hval
      _ = (extChartAt (modelWithCornersEuclideanHalfSpace (n + 1)) y).symm
            ((extChartAt (modelWithCornersEuclideanHalfSpace (n + 1)) y) y) := by
          rw [Work.PTGeometric.icChart_coe_symm, Work.PTGeometric.icChart_coe]
      _ = y := (extChartAt (modelWithCornersEuclideanHalfSpace (n + 1)) y).left_inv
          (by rw [extChartAt_source]; exact mem_chart_source _ y)
  rw [h3] at hint
  exact hint hy

/-- The `0`-th coordinate of `bcuVa` at `x₀` is positive. -/
theorem bcuVa_coord_pos_of_icChart (n : ℕ) (W : TopCat) [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 W]
    {y x₀ : W} (hy : y ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
    {τ : ℝ} (hτ : 0 < τ)
    (hx₀ : x₀ ∈ (Work.PTGeometric.icChart n W y).source) :
    0 < (bcuVa n W y τ x₀) 0 := by
  have h1 : 0 < ((Work.PTGeometric.icChart n W y) x₀) 0 :=
    Work.ThomBordism.icChart_coord_pos n W y hx₀
  have h2 : ((Work.PTGeometric.icChart n W y) x₀) 0 =
      (((chartAt (EuclideanHalfSpace (n + 1)) y) x₀).1 : EuclideanSpace ℝ (Fin (n + 1))) 0 := by
    rw [Work.PTGeometric.icChart_coe, extChartAt_coe]
    simp only [Function.comp_apply]
    rw [modelWithCornersEuclideanHalfSpace_toFun (n + 1)]
  rw [bcuVa_coord, Work.Orient.Boundary.chartAt_boundary_coord_zero n W hy, sub_zero, ← h2]
  exact mul_pos hτ h1


/-- **A bump function with prescribed compact support.**  On a compact Hausdorff space, given a
compact set `S` inside an open set `U`, there is a continuous `χ : W → [0,1]` equal to `1` on `S`
and vanishing outside a compact subset of `U`. -/
theorem exists_bump_isCompact (W : TopCat) [CompactSpace W] [T2Space W]
    (U : Set W) (hU : IsOpen U) (S : Set W) (hS : IsCompact S) (hSU : S ⊆ U) :
    ∃ (χ : W → ℝ) (K : Set W), Continuous χ ∧ (∀ z, 0 ≤ χ z ∧ χ z ≤ 1) ∧
      (∀ z ∈ S, χ z = 1) ∧ IsCompact K ∧ K ⊆ U ∧ (∀ z ∉ K, χ z = 0) := by
  have hmem : U ∈ nhdsSet S := hU.mem_nhdsSet.mpr hSU
  obtain ⟨V, hVopen, hSV, hVcl⟩ := hS.exists_isOpen_closure_subset hmem
  have hSint : S ⊆ interior (closure V) :=
    hSV.trans (interior_maximal subset_closure hVopen)
  have hdisj : Disjoint ((interior (closure V))ᶜ : Set W) S := by
    rw [Set.disjoint_left]
    intro z hz hzS
    exact hz (hSint hzS)
  obtain ⟨f, hf0, hf1, hfIcc⟩ :=
    exists_continuous_zero_one_of_isClosed isOpen_interior.isClosed_compl hS.isClosed hdisj
  refine ⟨fun z => f z, closure V, f.continuous, fun z => ⟨(hfIcc z).1, (hfIcc z).2⟩,
    fun z hz => hf1 hz, isClosed_closure.isCompact, hVcl, ?_⟩
  intro z hz
  exact hf0 (fun hzi => hz (interior_subset hzi))




/-- The `ℝ^{n+1} → ℝⁿ` tail map of the surgery area agrees with the one of the `PTGeometric` area. -/
theorem tailCLM_eq_surgery (n : ℕ) :
    (Work.PTGeometric.tailCLM n : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ]
        EuclideanSpace ℝ (Fin n)) = Work.Surgery.tailCLM n := by
  ext x k
  rw [Work.PTGeometric.tailCLM_apply, Work.Surgery.tailCLM_apply]

/-- The extended chart of the half-space model at `y`, read in the ambient model space. -/
theorem extChartAt_eq_chartAt_coe (n : ℕ) {W : TopCat}
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W] (y z : W) :
    (extChartAt (modelWithCornersEuclideanHalfSpace (n + 1)) y) z =
      (((chartAt (EuclideanHalfSpace (n + 1)) y) z).1 : EuclideanSpace ℝ (Fin (n + 1))) := by
  rw [extChartAt_coe]
  simp only [Function.comp_apply]
  rw [modelWithCornersEuclideanHalfSpace_toFun]

theorem boundarySign_boundaryChartAt_univ (n : ℕ) (hn : 1 ≤ n) :
    ∃ c : ℤ, (c = 1 ∨ c = -1) ∧
      ∀ (W : TopCat) [CompactSpace W] [T2Space W]
        [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
        [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) ((⊤ : ENat) : WithTop ENat) W]
        {y : W} (hy : y ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
        {r : ℝ} (hr : 0 < r) (hgood : Work.Orient.halfBallGood (n + 1) W y r)
        {x₀ : W} (hx₀ : x₀ ∈ Work.Orient.halfBallPiece (n + 1) W y r)
        (hx₀int : x₀ ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
        (hx₀e : x₀ ∈ (Work.PTGeometric.icChart n W y).source)
        (w : (Work.Cohomology.relChains W
          ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)).homology (n + 1))
        (hw : (HomologicalComplex.homologyMap
              (Work.Orient.relPunct W ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
                x₀ hx₀int) (n + 1)).hom w
            = Work.PTGeometric.HOF.chartTr (Work.PTGeometric.icChart n W y) x₀ hx₀e
                (Work.PTGeometric.HOF.eucFam (n + 1) (by omega)
                  (Work.PTGeometric.icChart n W y x₀))),
      Work.Orient.locClass
        (TopCat.of ↥((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)) n
        ((Work.Cohomology.hPairδ W
          ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) n).hom w) ⟨y, hy⟩
      = c • Work.PTGeometric.HOF.chartTr (W := TopCat.of
            ↥((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W))
          (Work.Surgery.boundaryChartAt (n := n) ⟨y, hy⟩) ⟨y, hy⟩
          (Work.Surgery.boundaryChartAt_mem_source (n := n) ⟨y, hy⟩)
          (Work.PTGeometric.HOF.eucFam n hn
            (Work.Surgery.boundaryChartAt (n := n) ⟨y, hy⟩ ⟨y, hy⟩)) := by
  classical
  obtain ⟨c, hc, hmodel⟩ := bsu_modelEquation n hn
  refine ⟨c, hc, ?_⟩
  intro W _cptW _t2W _chW _ismW y hy r hr hgood x₀ hx₀ hx₀int hx₀e w hw
  haveI : IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 W := inferInstance
  -- ===================== the model =====================
  obtain ⟨csM, imM, hbM, _hcolM, hcptM⟩ := stdHalfBallCharted n
  letI : ChartedSpace (EuclideanHalfSpace (n + 1)) ↥(stdHalfBall (n + 1)) := csM
  haveI : IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) ∞ ↥(stdHalfBall (n + 1)) := imM
  haveI : IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 ↥(stdHalfBall (n + 1)) :=
    inferInstance
  haveI : CompactSpace ↥(stdHalfBall (n + 1)) := hcptM
  let W' : TopCat := TopCat.of ↥(stdHalfBall (n + 1))
  have hW'def : W' = TopCat.of ↥(stdHalfBall (n + 1)) := rfl
  let B' : Set W' := stdHalfBallBdry (n + 1)
  have hB'def : B' = stdHalfBallBdry (n + 1) := rfl
  let y' : W' := ⟨(0 : EuclideanSpace ℝ (Fin (n + 1))), zero_mem_stdHalfBall (n + 1)⟩
  have hy'def : y' = ⟨(0 : EuclideanSpace ℝ (Fin (n + 1))), zero_mem_stdHalfBall (n + 1)⟩ := rfl
  have hB'eq : (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W' = B' := hbM
  have hy'B' : y' ∈ B' := by
    show (⟨(0 : EuclideanSpace ℝ (Fin (n + 1))), zero_mem_stdHalfBall (n + 1)⟩ :
      ↥(stdHalfBall (n + 1))) ∈ Work.ThomBordism.stdHalfBallBdry (n + 1)
    rw [Work.ThomBordism.stdHalfBallBdry]
    exact Or.inl (by simp)
  obtain ⟨r', hr'pos, hgood'M, U, hUopen, hy'U, hUsub⟩ :=
    Work.Orient.exists_halfBallGood_piece (n + 1) W' y'
  obtain ⟨ε, hεpos, hballU⟩ := Metric.isOpen_iff.mp hUopen y' hy'U
  -- ===================== the chart at y and the scale =====================
  let c₀ : EuclideanSpace ℝ (Fin (n + 1)) := ((chartAt (EuclideanHalfSpace (n + 1)) y) y).1
  have hc₀ : c₀ = ((chartAt (EuclideanHalfSpace (n + 1)) y) y).1 := rfl
  let c₁ : EuclideanSpace ℝ (Fin (n + 1)) := ((chartAt (EuclideanHalfSpace (n + 1)) y) x₀).1
  have hc₁ : c₁ = ((chartAt (EuclideanHalfSpace (n + 1)) y) x₀).1 := rfl
  have hNle : ‖c₁ - c₀‖ ≤ r / 2 := by
    have h1 : dist ((chartAt (EuclideanHalfSpace (n + 1)) y) x₀).1
        ((chartAt (EuclideanHalfSpace (n + 1)) y) y).1 ≤ r / 2 :=
      Metric.mem_closedBall.mp hx₀.1
    rw [dist_eq_norm] at h1
    rwa [hc₁, hc₀]
  obtain ⟨τ, hτpos, hτsmall⟩ : ∃ τ : ℝ, 0 < τ ∧ τ * ‖c₁ - c₀‖ < min (min ε 1) (1 / 2) := by
    rcases eq_or_lt_of_le (norm_nonneg (c₁ - c₀)) with h0 | h0
    · exact ⟨1, one_pos, by rw [← h0, mul_zero]; positivity⟩
    · refine ⟨min (min ε 1) (1 / 2) / (‖c₁ - c₀‖ + 1), by positivity, ?_⟩
      have hden : 0 < ‖c₁ - c₀‖ + 1 := by positivity
      have hm : 0 < min (min ε 1) (1 / 2) :=
        lt_min (lt_min hεpos one_pos) (by norm_num : (0 : ℝ) < 1 / 2)
      have hfrac : ‖c₁ - c₀‖ / (‖c₁ - c₀‖ + 1) < 1 := by
        rw [div_lt_one hden]; linarith [norm_nonneg (c₁ - c₀)]
      calc min (min ε 1) (1 / 2) / (‖c₁ - c₀‖ + 1) * ‖c₁ - c₀‖
          = min (min ε 1) (1 / 2) * (‖c₁ - c₀‖ / (‖c₁ - c₀‖ + 1)) := by ring
        _ < min (min ε 1) (1 / 2) * 1 := mul_lt_mul_of_pos_left hfrac hm
        _ = min (min ε 1) (1 / 2) := mul_one _
  have hτne : τ ≠ 0 := ne_of_gt hτpos
  have hVa₀ : bcuVa n W y τ x₀ = τ • (c₁ - c₀) := by
    rw [bcuVa, bcuCh, bcuCh, ← hc₁, ← hc₀]
  have hVnorm : ‖bcuVa n W y τ x₀‖ = τ * ‖c₁ - c₀‖ := by
    rw [hVa₀, norm_smul, Real.norm_eq_abs, abs_of_pos hτpos]
  have hVltε : ‖bcuVa n W y τ x₀‖ < ε := by
    rw [hVnorm]
    exact lt_of_lt_of_le hτsmall (le_trans (min_le_left _ _) (min_le_left _ _))
  have hVlt1 : ‖bcuVa n W y τ x₀‖ < 1 := by
    rw [hVnorm]
    exact lt_of_lt_of_le hτsmall (le_trans (min_le_left _ _) (min_le_right _ _))
  have hVle : ‖bcuVa n W y τ x₀‖ ≤ 1 / 2 := by
    rw [hVnorm]; exact le_of_lt (lt_of_lt_of_le hτsmall (min_le_right _ _))
  have hVpos : 0 < (bcuVa n W y τ x₀) 0 := bcuVa_coord_pos_of_icChart n W hy hτpos hx₀e
  have hVne : bcuVa n W y τ x₀ ≠ 0 := bcuVa_ne_zero_of_icChart n W hy hτne hx₀e hx₀int
  have hVeq : ∀ z ∈ (chartAt (EuclideanHalfSpace (n + 1)) y).source,
      bcuVa n W y τ z = bcuVa n W y τ x₀ → z = x₀ :=
    fun z hz h => bcuVa_eq_of_icChart n W hτne hx₀e hz h
  -- ===================== the bump =====================
  have hSsub : Work.Orient.halfBallPiece (n + 1) W y r ⊆
      (chartAt (EuclideanHalfSpace (n + 1)) y).source := fun z hz => hz.2
  have hScomp : IsCompact (Work.Orient.halfBallPiece (n + 1) W y r) :=
    Work.Orient.halfBallPiece_isCompact y r hr hgood
  obtain ⟨V₀, hV₀open, hSV₀, hV₀cl⟩ := hScomp.exists_isOpen_closure_subset
    ((chartAt (EuclideanHalfSpace (n + 1)) y).open_source.mem_nhdsSet.mpr hSsub)
  obtain ⟨χ, K, hχc, hχ01, hχS, hKc, hKsub, hχ0⟩ :=
    exists_bump_isCompact W (chartAt (EuclideanHalfSpace (n + 1)) y).source
      (chartAt (EuclideanHalfSpace (n + 1)) y).open_source (closure V₀)
      isClosed_closure.isCompact hV₀cl
  have hpiece_y : y ∈ Work.Orient.halfBallPiece (n + 1) W y r :=
    Work.Orient.mem_halfBallPiece_center hr
  have hyV₀ : y ∈ V₀ := hSV₀ hpiece_y
  have hx₀V₀ : x₀ ∈ V₀ := hSV₀ hx₀
  have hyS : y ∈ closure V₀ := subset_closure hyV₀
  have hx₀S : x₀ ∈ closure V₀ := subset_closure hx₀V₀
  have hy1 : χ y = 1 := hχS y hyS
  have hχout : ∀ z, z ∉ (chartAt (EuclideanHalfSpace (n + 1)) y).source → χ z = 0 :=
    fun z hz => hχ0 z (fun h => hz (hKsub h))
  have hvan : ∀ z ∈ (chartAt (EuclideanHalfSpace (n + 1)) y).source,
      bcuVa n W y τ z = 0 → χ z = 1 := by
    intro z hz h0
    rw [(bcuVa_eq_zero_iff n W hτne hz).mp h0]
    exact hy1
  obtain ⟨hΦcont, hΦmem⟩ := continuous_bcuPhi_and_mem n W y hy τ hτpos χ K hχc hχ01 hKc hKsub
    hχ0 hvan (fun t₀ v₀ h1 h2 h3 => bcu_profile2_continuousAt n t₀ v₀ h1 h2 h3)
  let B : Set W := (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W
  have hBdef : B = (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W := rfl
  have hwB : (HomologicalComplex.homologyMap
        (Work.Orient.relPunct W B x₀ hx₀int) (n + 1)).hom w
      = Work.PTGeometric.HOF.chartTr (Work.PTGeometric.icChart n W y) x₀ hx₀e
          (Work.PTGeometric.HOF.eucFam (n + 1) (by omega)
            (Work.PTGeometric.icChart n W y x₀)) := hw
  -- ===================== the two maps =====================
  let Φ : W ⟶ W' := TopCat.ofHom ⟨fun z => (⟨bcuPhi n W y τ χ z, hΦmem z⟩ : W'),
    hΦcont.subtype_mk hΦmem⟩
  have hΦapply : ∀ z : W, ((Φ z : W') : EuclideanSpace ℝ (Fin (n + 1))) = bcuPhi n W y τ χ z :=
    fun z => rfl
  have hΦbdry : ∀ z : ↥B,
      Φ z.1 ∈ B' := by
    intro z
    rw [hB'def, Work.ThomBordism.stdHalfBallBdry]
    exact bcuPhi_bdry_disj n W hy z.2 hτpos hχ01 hχout hy1
  have hΦbcont : Continuous fun z : ↥B =>
      (⟨⟨bcuPhi n W y τ χ z.1, hΦmem z.1⟩, hΦbdry z⟩ : ↥B') :=
    Continuous.subtype_mk ((hΦcont.subtype_mk hΦmem).comp continuous_subtype_val) hΦbdry
  let Φb : TopCat.of ↥B ⟶ TopCat.of ↥B' :=
    TopCat.ofHom ⟨fun z => (⟨⟨bcuPhi n W y τ χ z.1, hΦmem z.1⟩, hΦbdry z⟩ : ↥B'), hΦbcont⟩
  have hΦb_apply : ∀ z, ((Φb z : ↥B') : W') = Φ z.1 := fun z => rfl
  have hΦy : Φ y = y' := by
    show (⟨bcuPhi n W y τ χ y, hΦmem y⟩ : W') = y'
    exact Subtype.ext (bcuPhi_self n W y τ χ hy1)
  have hΦb_y : Φb (⟨y, hy⟩ : ↥B) =
      (⟨y', hy'B'⟩ : ↥B') := by
    refine Subtype.ext ?_
    rw [hΦb_apply, hΦy]
  have hpairb : ∀ z : ↥B,
      z ∉ ({⟨y, hy⟩} : Set ↥B) →
      Φb z ∉ ({Φb (⟨y, hy⟩ : ↥B)} :
        Set ↥B') := by
    intro z hz hcon
    simp only [Set.mem_singleton_iff] at hz hcon
    refine hz (Subtype.ext ?_)
    have h1 : Φ z.1 = Φ y := by
      rw [← hΦb_apply z,
        ← hΦb_apply (⟨y, hy⟩ : ↥B), hcon]
    have h2 : bcuPhi n W y τ χ z.1 = 0 := by
      have h3 := congrArg (fun u : W' => ((u : EuclideanSpace ℝ (Fin (n + 1))))) h1
      rw [hΦapply, hΦapply] at h3
      rw [bcuPhi_self n W y τ χ hy1] at h3
      exact h3
    exact absurd h2 (bcuPhi_ne_zero n W hy hτpos hχ01 hχout (fun hzy => hz (Subtype.ext hzy)))
  -- ===================== the open set U₀ and the chart eU =====================
  let U₀ : Set W := V₀ ∩ ((chartAt (EuclideanHalfSpace (n + 1)) y).source ∩
    bcuVa n W y τ ⁻¹' Metric.ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
  have hU₀def : U₀ = V₀ ∩ ((chartAt (EuclideanHalfSpace (n + 1)) y).source ∩
    bcuVa n W y τ ⁻¹' Metric.ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := rfl
  have hU₀open : IsOpen U₀ := by
    rw [hU₀def]
    refine hV₀open.inter ?_
    refine ContinuousOn.isOpen_inter_preimage ?_ (chartAt (EuclideanHalfSpace (n + 1)) y).open_source
      Metric.isOpen_ball
    have h2 : ContinuousOn (fun z => (((chartAt (EuclideanHalfSpace (n + 1)) y) z).1))
        (chartAt (EuclideanHalfSpace (n + 1)) y).source :=
      continuous_subtype_val.comp_continuousOn
        (chartAt (EuclideanHalfSpace (n + 1)) y).continuousOn_toFun
    have h4 : ContinuousOn (fun _ : W => (((chartAt (EuclideanHalfSpace (n + 1)) y) y).1))
        (chartAt (EuclideanHalfSpace (n + 1)) y).source := continuousOn_const
    have h3 : ContinuousOn
        (fun z => τ • (((chartAt (EuclideanHalfSpace (n + 1)) y) z).1 -
          (((chartAt (EuclideanHalfSpace (n + 1)) y) y).1)))
        (chartAt (EuclideanHalfSpace (n + 1)) y).source :=
      (h2.sub h4).const_smul τ
    exact h3
  have hΦeq_U₀ : ∀ z ∈ U₀, bcuPhi n W y τ χ z = bcuVa n W y τ z := by
    intro z hz
    have h1 : χ z = 1 := hχS z (subset_closure hz.1)
    have h2 : ‖bcuVa n W y τ z‖ < 1 := by
      have h2' : bcuVa n W y τ z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 := hz.2.2
      rwa [Metric.mem_ball, dist_zero_right] at h2'
    rw [bcuPhi_apply, h1, (Work.ThomBordism.bcu_profile2_properties n).2.2.1]
    exact BCU.bcu_clampBall_eq_self _ (le_of_lt h2)
  have hx₀U₀ : x₀ ∈ U₀ := by
    rw [hU₀def]
    refine ⟨hx₀V₀, hV₀cl (subset_closure hx₀V₀), ?_⟩
    rw [Set.mem_preimage, Metric.mem_ball, dist_zero_right, hVnorm]
    exact lt_of_lt_of_le hτsmall (le_trans (min_le_left _ _) (min_le_right _ _))
  have hΦx₀ : bcuPhi n W y τ χ x₀ = bcuVa n W y τ x₀ := hΦeq_U₀ x₀ hx₀U₀
  -- ===================== the fibre at x₀ =====================
  have hSray : ∀ z ∈ (chartAt (EuclideanHalfSpace (n + 1)) y).source,
      (∃ m : ℝ, 0 ≤ m ∧ m ≤ 1 ∧ bcuVa n W y τ z = m • bcuVa n W y τ x₀) →
        z ∈ closure V₀ := by
    intro z hz hray
    obtain ⟨m, hm0, hm1, hm⟩ := hray
    apply subset_closure
    refine hSV₀ ?_
    have hzeq : ((chartAt (EuclideanHalfSpace (n + 1)) y) z).1 =
        (1 - m) • c₀ + m • c₁ := by
      have h1 : τ • (((chartAt (EuclideanHalfSpace (n + 1)) y) z).1 -
          ((chartAt (EuclideanHalfSpace (n + 1)) y) y).1) = τ • (m • (c₁ - c₀)) := by
        have h := hm
        rw [hVa₀] at h
        simpa only [bcuVa, bcuCh, smul_comm m τ (c₁ - c₀)] using h
      have h2 : ((chartAt (EuclideanHalfSpace (n + 1)) y) z).1 -
          ((chartAt (EuclideanHalfSpace (n + 1)) y) y).1 = m • (c₁ - c₀) :=
        smul_right_injective _ hτne h1
      have h3 : ((chartAt (EuclideanHalfSpace (n + 1)) y) z).1 =
          ((chartAt (EuclideanHalfSpace (n + 1)) y) y).1 + m • (c₁ - c₀) := by
        rw [← h2]; abel
      rw [h3, hc₀]
      module
    have hdist : dist ((chartAt (EuclideanHalfSpace (n + 1)) y) z).1
        ((chartAt (EuclideanHalfSpace (n + 1)) y) y).1 ≤ r / 2 := by
      rw [dist_eq_norm, hzeq, hc₀]
      have hsub : (1 - m) • c₀ + m • c₁ - c₀ = m • (c₁ - c₀) := by module
      rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hm0]
      calc m * ‖c₁ - c₀‖ ≤ 1 * ‖c₁ - c₀‖ :=
            mul_le_mul_of_nonneg_right hm1 (norm_nonneg _)
        _ = ‖c₁ - c₀‖ := one_mul _
        _ ≤ r / 2 := hNle
    exact ⟨Metric.mem_closedBall.mpr hdist, hz⟩
  -- ===================== the model-side inequality =====================
  have hΦx₀E : ((Φ x₀ : W') : EuclideanSpace ℝ (Fin (n + 1))) = bcuVa n W y τ x₀ := by
    rw [hΦapply, hΦx₀]
  have hdist_sub : ∀ a b : W', dist a b =
      dist ((a : W') : EuclideanSpace ℝ (Fin (n + 1)))
        ((b : W') : EuclideanSpace ℝ (Fin (n + 1))) :=
    fun a b => Subtype.dist_eq a b
  have hx₀'U : Φ x₀ ∈ U := by
    apply hballU
    rw [Metric.mem_ball, hdist_sub, hΦx₀E,
      show (((y' : W') : EuclideanSpace ℝ (Fin (n + 1)))) = 0 from rfl, dist_zero_right]
    exact hVltε
  have hx₀intE : Φ x₀ ∉ stdHalfBallBdry (n + 1) := by
    rw [← Work.ThomBordism.mem_stdHalfBallInterior_iff (n + 1) (Φ x₀)]
    exact ⟨by rw [hΦx₀E]; exact hVpos, by rw [hΦx₀E]; exact hVlt1⟩
  have hx₀srcE : Φ x₀ ∈ (Work.ThomBordism.stdIntChart (n + 1)).source := by
    refine ⟨?_, ?_⟩
    · rw [hΦx₀E]; exact hVpos
    · rw [hΦx₀E]; exact hVlt1
  have hΦinj : ∀ z : W, Φ z = Φ x₀ → z = x₀ := by
    intro z hz
    have h2 : bcuPhi n W y τ χ z = bcuPhi n W y τ χ x₀ := by
      have h3 := congrArg (fun u : W' => ((u : EuclideanSpace ℝ (Fin (n + 1))))) hz
      rw [hΦapply, hΦapply] at h3
      exact h3
    rw [hΦx₀] at h2
    exact bcuPhi_eq_of_eq n W hy hτpos hVpos hVeq hχ01 hχout (closure V₀) hχS hyS hSray hVne hVle h2
  -- ===================== the interior chart eU =====================
  let eU : OpenPartialHomeomorph W (EuclideanSpace ℝ (Fin (n + 1))) :=
    (bcuChart n W y τ hτne).restr U₀
  have heU : eU = (bcuChart n W y τ hτne).restr U₀ := rfl
  have heU_src : eU.source = (Work.PTGeometric.icChart n W y).source ∩ U₀ := by
    rw [heU, OpenPartialHomeomorph.restr_source, bcuChart_source, hU₀open.interior_eq]
  have hx₀eU : x₀ ∈ eU.source := by
    rw [heU_src]; exact ⟨hx₀e, hx₀U₀⟩
  have heU_val : ∀ z ∈ eU.source, eU z = bcuVa n W y τ z := by
    intro z hz
    rw [heU_src] at hz
    rw [heU, OpenPartialHomeomorph.restr_apply]
    exact bcuChart_apply n W y τ hτne (by rw [bcuChart_source]; exact hz.1)
  -- ===================== the transfer at x₀ =====================
  have hΦs : ∀ z, z ∈ eU.source → (⟨bcuPhi n W y τ χ z, hΦmem z⟩ : W') ∈
      (Work.ThomBordism.stdIntChart (n + 1)).source := by
    intro z hz
    rw [heU_src] at hz
    have h1 : ((⟨bcuPhi n W y τ χ z, hΦmem z⟩ : W') : EuclideanSpace ℝ (Fin (n + 1))) =
        bcuVa n W y τ z := hΦeq_U₀ z hz.2
    have h2 : 0 < (bcuVa n W y τ z) 0 := by
      have h3 : 0 < ((Work.PTGeometric.icChart n W y) z) 0 :=
        Work.ThomBordism.icChart_coord_pos n W y hz.1
      have h4 : ((Work.PTGeometric.icChart n W y) z) 0 =
          (((chartAt (EuclideanHalfSpace (n + 1)) y) z).1 : EuclideanSpace ℝ (Fin (n + 1))) 0 := by
        rw [Work.PTGeometric.icChart_coe, extChartAt_coe]
        simp only [Function.comp_apply]
        rw [modelWithCornersEuclideanHalfSpace_toFun (n + 1)]
      rw [bcuVa_coord, Work.Orient.Boundary.chartAt_boundary_coord_zero n W hy, sub_zero, ← h4]
      exact mul_pos hτpos h3
    have hb : ‖bcuVa n W y τ z‖ < 1 := by
      have h2' : bcuVa n W y τ z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
        (hU₀def ▸ hz.2).2.2
      rwa [Metric.mem_ball, dist_zero_right] at h2'
    have h2' : 0 < (((⟨bcuPhi n W y τ χ z, hΦmem z⟩ : W') :
        EuclideanSpace ℝ (Fin (n + 1)))) 0 := by
      rw [h1]; exact h2
    have hb' : ‖((⟨bcuPhi n W y τ χ z, hΦmem z⟩ : W') :
        EuclideanSpace ℝ (Fin (n + 1)))‖ < 1 := by
      rw [h1]; exact hb
    exact ⟨h2', hb'⟩
  have hΦe : ∀ z, z ∈ eU.source → (Work.ThomBordism.stdIntChart (n + 1))
      ((⟨bcuPhi n W y τ χ z, hΦmem z⟩ : W')) = eU z := by
    intro z hz
    rw [heU_src] at hz
    have h1 : eU z = bcuVa n W y τ z := heU_val z (by rw [heU_src]; exact hz)
    show bcuPhi n W y τ χ z = eU z
    rw [h1, hΦeq_U₀ z hz.2]
  have hInt : Work.PTGeometric.HOF.RelHmapOf (n + 1) Φ ({x₀} : Set W) ({Φ x₀} : Set W')
      (fun z hz hzx => hz (hΦinj z hzx))
      (Work.PTGeometric.HOF.chartTr (Work.PTGeometric.icChart n W y) x₀ hx₀e
        (Work.PTGeometric.HOF.eucFam (n + 1) (by omega) (Work.PTGeometric.icChart n W y x₀)))
    = Work.PTGeometric.HOF.chartTr (W := W') (Work.ThomBordism.stdIntChart (n + 1)) (Φ x₀) hx₀srcE
        (Work.PTGeometric.HOF.eucFam (n + 1) (by omega)
          ((Work.ThomBordism.stdIntChart (n + 1)) (Φ x₀))) := by
    have hA : Function.Bijective (τ⁻¹ • (1 : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ]
        EuclideanSpace ℝ (Fin (n + 1)))) := by
      constructor
      · intro u v huv
        have huv' : τ⁻¹ • u = τ⁻¹ • v := by
          simpa only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply] using huv
        exact smul_right_injective _ (inv_ne_zero hτne) huv'
      · intro w
        exact ⟨τ • w, by simp [smul_smul, mul_inv_cancel₀ hτne, inv_mul_cancel₀ hτne]⟩
    have hdet : 0 < LinearMap.det ((τ⁻¹ • (1 : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ]
        EuclideanSpace ℝ (Fin (n + 1)))).toLinearMap) := by
      rw [ContinuousLinearMap.toLinearMap_smul, ContinuousLinearMap.toLinearMap_one,
        LinearMap.det_smul]
      have hone : LinearMap.det (1 : EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ]
          EuclideanSpace ℝ (Fin (n + 1))) = 1 := by
        rw [show (1 : EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
          = LinearMap.id from rfl, LinearMap.det_id]
      rw [hone, mul_one, finrank_euclideanSpace, Fintype.card_fin]
      exact pow_pos (inv_pos.mpr hτpos) _
    have htrans : ∀ z ∈ eU.target,
        (Work.PTGeometric.icChart n W y) (eU.symm z)
          = (τ⁻¹ • (1 : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ]
              EuclideanSpace ℝ (Fin (n + 1)))) z + c₀ := by
      intro z hz
      have hzsrc : eU.symm z ∈ eU.source := eU.symm.map_source hz
      have h1 : eU (eU.symm z) = z := eU.right_inv hz
      have h2 : eU (eU.symm z) = τ • ((Work.PTGeometric.icChart n W y) (eU.symm z) - c₀) := by
        rw [heU_val _ hzsrc, bcuVa, bcuCh, bcuCh]
        congr 1
        rw [Work.PTGeometric.icChart_coe, extChartAt_coe, Function.comp_apply,
          modelWithCornersEuclideanHalfSpace_toFun (n + 1)]
      have h3 : z = τ • ((Work.PTGeometric.icChart n W y) (eU.symm z) - c₀) :=
        (congrArg (fun w => w = τ • ((Work.PTGeometric.icChart n W y) (eU.symm z) - c₀)) h1).mp h2
      rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply]
      conv_rhs => rw [h3]
      rw [smul_smul, inv_mul_cancel₀ hτne, one_smul]
      abel
    have hrel := Work.ThomBordism.chartTr_relHmapOf (N := n + 1) (W := W) (W' := W') (by omega) eU
      (Work.ThomBordism.stdIntChart (n + 1)) Φ.hom x₀ hx₀eU hΦs hΦe
      (fun z hz hzx => hz (hΦinj z hzx))
    rw [Work.ThomBordism.PosAtlas.chartTr_eq_of_affine_transition (n := n + 1) (by omega) eU
      (Work.PTGeometric.icChart n W y) (τ⁻¹ • (1 : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ]
        EuclideanSpace ℝ (Fin (n + 1)))) hA c₀ htrans hdet x₀ hx₀eU hx₀e] at hrel
    exact hrel
  -- ===================== the boundary chart, the rescaled chart =====================
  let eb : OpenPartialHomeomorph ↥B (EuclideanSpace ℝ (Fin n)) :=
    Work.Surgery.boundaryChartAt (n := n) (⟨y, hy⟩ : ↥B)
  have hebdef : eb = Work.Surgery.boundaryChartAt (n := n) (⟨y, hy⟩ : ↥B) := rfl
  have hyeb : (⟨y, hy⟩ : ↥B) ∈ eb.source :=
    Work.Surgery.boundaryChartAt_mem_source (n := n) (⟨y, hy⟩ : ↥B)
  let eby : EuclideanSpace ℝ (Fin n) := eb ⟨y, hy⟩
  have hebydef : eby = eb ⟨y, hy⟩ := rfl
  have hbndChart_val : ∀ (z : W) (hz : z ∈ B) (hs : (⟨z, hz⟩ : ↥B) ∈ eb.source),
      eb (⟨z, hz⟩ : ↥B) = (Work.Surgery.tailCLM n) (bcuCh n W y z) := by
    intro z hz hs
    have h := Work.Surgery.boundaryChartAt_apply (n := n) (x := (⟨y, hy⟩ : ↥B))
      (y := (⟨z, hz⟩ : ↥B)) hs
    have h2 : (extChartAt (modelWithCornersEuclideanHalfSpace (n + 1)) ((⟨y, hy⟩ : ↥B) : W))
        (((⟨z, hz⟩ : ↥B) : W)) = bcuCh n W y z :=
      extChartAt_eq_chartAt_coe n y z
    rw [hebdef, h, h2]
  have hU_b_open : IsOpen (Subtype.val ⁻¹' U₀ : Set ↥B) := hU₀open.preimage continuous_subtype_val
  have hyU₀ : y ∈ U₀ := by
    rw [hU₀def]
    refine ⟨hyV₀, mem_chart_source _ y, ?_⟩
    show bcuVa n W y τ y ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1
    rw [bcuVa_self]
    exact Metric.mem_ball_self (by norm_num)
  have hyU_b : (⟨y, hy⟩ : ↥B) ∈ (Subtype.val ⁻¹' U₀ : Set ↥B) := hyU₀
  let ebS : OpenPartialHomeomorph ↥B (EuclideanSpace ℝ (Fin n)) :=
    (eb.transHomeomorph ((Work.ThomBordism.scaleHomeo n τ hτne).trans
      (Homeomorph.addRight (-(τ • eby))))).restr (Subtype.val ⁻¹' U₀)
  have hebSdef : ebS = (eb.transHomeomorph ((Work.ThomBordism.scaleHomeo n τ hτne).trans
      (Homeomorph.addRight (-(τ • eby))))).restr (Subtype.val ⁻¹' U₀) := rfl
  have hebS_src : ebS.source = eb.source ∩ (Subtype.val ⁻¹' U₀ : Set ↥B) := by
    rw [hebSdef, OpenPartialHomeomorph.restr_source, OpenPartialHomeomorph.transHomeomorph_source,
      hU_b_open.interior_eq]
  have hyebS : (⟨y, hy⟩ : ↥B) ∈ ebS.source := by
    rw [hebS_src]; exact ⟨hyeb, hyU_b⟩
  have hebS_val : ∀ z : ↥B, ebS z = τ • (eb z) - τ • eby := by
    intro z
    rw [hebSdef, OpenPartialHomeomorph.restr_apply,
      OpenPartialHomeomorph.transHomeomorph_apply, Function.comp_apply,
      Homeomorph.trans_apply, Work.ThomBordism.scaleHomeo_apply, Homeomorph.coe_addRight]
    simp only [sub_eq_add_neg]
  have hΦs' : ∀ z, z ∈ ebS.source → Φb z ∈ (stdFlatChart n).source := by
    intro z hz
    rw [hebS_src] at hz
    have hzU : z.1 ∈ U₀ := hz.2
    have hχ1 : χ z.1 = 1 := hχS z.1 (subset_closure hzU.1)
    have hVlt : ‖bcuVa n W y τ z.1‖ < 1 := by
      have h2' : bcuVa n W y τ z.1 ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
        (hU₀def ▸ hzU).2.2
      rwa [Metric.mem_ball, dist_zero_right] at h2'
    have hΦz : bcuPhi n W y τ χ z.1 = bcuVa n W y τ z.1 := by
      rw [bcuPhi_apply, hχ1, (Work.ThomBordism.bcu_profile2_properties n).2.2.1]
      exact BCU.bcu_clampBall_eq_self _ (le_of_lt hVlt)
    have h0 : (bcuVa n W y τ z.1) 0 = 0 :=
      bcuVa_coord_eq_zero_of_boundary n W hy z.2 (hU₀def ▸ hzU).2.1
    have hproj : ((Φb z).1.1 : EuclideanSpace ℝ (Fin (n + 1))) = bcuPhi n W y τ χ z.1 := by
      show ((Φ z.1 : W') : EuclideanSpace ℝ (Fin (n + 1))) = bcuPhi n W y τ χ z.1
      exact hΦapply z.1
    have h2' : (((Φb z).1.1 : EuclideanSpace ℝ (Fin (n + 1)))) 0 = 0 := by
      rw [hproj, hΦz]; exact h0
    have hb' : ‖((Φb z).1.1 : EuclideanSpace ℝ (Fin (n + 1)))‖ < 1 := by
      rw [hproj, hΦz]; exact hVlt
    exact ⟨h2', hb'⟩
  have hΦ' : ∀ z, z ∈ ebS.source → (stdFlatChart n) (Φb z) = ebS z := by
    intro z hz
    rw [hebS_src] at hz
    have hzU : z.1 ∈ U₀ := hz.2
    have hχ1 : χ z.1 = 1 := hχS z.1 (subset_closure hzU.1)
    have hVlt : ‖bcuVa n W y τ z.1‖ < 1 := by
      have h2' : bcuVa n W y τ z.1 ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
        (hU₀def ▸ hzU).2.2
      rwa [Metric.mem_ball, dist_zero_right] at h2'
    have hΦz : bcuPhi n W y τ χ z.1 = bcuVa n W y τ z.1 := by
      rw [bcuPhi_apply, hχ1, (Work.ThomBordism.bcu_profile2_properties n).2.2.1]
      exact BCU.bcu_clampBall_eq_self _ (le_of_lt hVlt)
    have hproj : ((Φb z).1.1 : EuclideanSpace ℝ (Fin (n + 1))) = bcuPhi n W y τ χ z.1 := by
      rw [show (Φb z).1.1 = ((Φ z.1 : W') : EuclideanSpace ℝ (Fin (n + 1))) from
        congrArg (fun t : W' => ((t : W') : EuclideanSpace ℝ (Fin (n + 1)))) (hΦb_apply z)]
      exact hΦapply z.1
    have hL : (stdFlatChart n) (Φb z) = (Work.PTGeometric.tailCLM n) (bcuVa n W y τ z.1) :=
      calc (stdFlatChart n) (Φb z)
          = (Work.PTGeometric.tailCLM n) (bcuPhi n W y τ χ z.1) := by
            show (Work.PTGeometric.tailCLM n)
              ((Φb z).1.1 : EuclideanSpace ℝ (Fin (n + 1))) = _
            rw [hproj]
        _ = (Work.PTGeometric.tailCLM n) (bcuVa n W y τ z.1) := by rw [hΦz]
    have hR : ebS z = τ • ((Work.Surgery.tailCLM n) (bcuCh n W y z.1) -
        (Work.Surgery.tailCLM n) (bcuCh n W y y)) := by
      rw [hebS_val z,
        show eb z = (Work.Surgery.tailCLM n) (bcuCh n W y z.1) from hbndChart_val z.1 z.2 hz.1,
        show eby = (Work.Surgery.tailCLM n) (bcuCh n W y y) from hbndChart_val y hy hyeb]
      rw [← smul_sub]
    rw [hL, hR]
    rw [Work.ThomBordism.tailCLM_eq_surgery n]
    show (Work.Surgery.tailCLM n) (bcuVa n W y τ z.1) =
      τ • ((Work.Surgery.tailCLM n) (bcuCh n W y z.1) -
        (Work.Surgery.tailCLM n) (bcuCh n W y y))
    rw [show bcuVa n W y τ z.1 = τ • (bcuCh n W y z.1 - bcuCh n W y y) from rfl]
    rw [map_smul, map_sub]
  have hinjB : ∀ z : ↥B, z ≠ ⟨y, hy⟩ → Φb z ≠ Φb ⟨y, hy⟩ := by
    intro z hz h
    exact hpairb z (by simpa using hz) (by simpa using h)
  have hpair0 : ∀ z : ↥B, z ∉ ({⟨y, hy⟩} : Set ↥B) → Φb z ∉ ({Φb ⟨y, hy⟩} : Set ↥B') :=
    fun z hz h => hz (by_contra (fun hzx => hinjB z hzx h))
  have hyeb' : Φb ⟨y, hy⟩ ∈ (stdFlatChart n).source := hΦs' ⟨y, hy⟩ hyebS
  have hChartB : Work.PTGeometric.HOF.RelHmapOf n Φb ({⟨y, hy⟩} : Set ↥B)
      ({Φb ⟨y, hy⟩} : Set ↥B') hpairb
      (Work.PTGeometric.HOF.chartTr (W := TopCat.of ↥B) eb ⟨y, hy⟩ hyeb
        (Work.PTGeometric.HOF.eucFam n hn (eb ⟨y, hy⟩)))
    = Work.PTGeometric.HOF.chartTr (W := TopCat.of ↥B') (stdFlatChart n) (Φb ⟨y, hy⟩) hyeb'
        (Work.PTGeometric.HOF.eucFam n hn ((stdFlatChart n) (Φb ⟨y, hy⟩))) := by
    have hmain := Work.ThomBordism.chartTr_relHmapOf (N := n) (W := TopCat.of ↥B)
      (W' := TopCat.of ↥B') hn ebS (stdFlatChart n) Φb.hom ⟨y, hy⟩ hyebS hΦs' hΦ' hinjB
    have hAb : Function.Bijective (τ • (1 : EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n))) := by
      constructor
      · intro u v huv
        have huv' : τ • u = τ • v := by
          simpa only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply] using huv
        exact smul_right_injective _ hτne huv'
      · intro w
        exact ⟨τ⁻¹ • w, by simp [smul_smul, mul_inv_cancel₀ hτne, inv_mul_cancel₀ hτne]⟩
    have hdetS : 0 < LinearMap.det ((τ • (1 : EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n))).toLinearMap) := by
      rw [ContinuousLinearMap.toLinearMap_smul, ContinuousLinearMap.toLinearMap_one,
        LinearMap.det_smul]
      have hone : LinearMap.det (1 : EuclideanSpace ℝ (Fin n) →ₗ[ℝ]
          EuclideanSpace ℝ (Fin n)) = 1 := by
        rw [show (1 : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
          = LinearMap.id from rfl, LinearMap.det_id]
      rw [hone, mul_one, finrank_euclideanSpace, Fintype.card_fin]
      exact pow_pos hτpos _
    have htransS : ∀ z ∈ eb.target,
        ebS (eb.symm z) = (τ • (1 : EuclideanSpace ℝ (Fin n) →L[ℝ]
          EuclideanSpace ℝ (Fin n))) z + (-(τ • eby)) := by
      intro z hz
      rw [hebS_val, eb.right_inv hz]
      simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, sub_eq_add_neg]
    have hconv1 : Work.PTGeometric.HOF.RelHmapOf n Φb ({⟨y, hy⟩} : Set ↥B)
        ({Φb ⟨y, hy⟩} : Set ↥B') hpairb
        (Work.PTGeometric.HOF.chartTr (W := TopCat.of ↥B) eb ⟨y, hy⟩ hyeb
          (Work.PTGeometric.HOF.eucFam n hn (eb ⟨y, hy⟩)))
      = Work.PTGeometric.HOF.RelHmapOf n Φb ({⟨y, hy⟩} : Set ↥B)
        ({Φb ⟨y, hy⟩} : Set ↥B') hpairb
        (Work.PTGeometric.HOF.chartTr (W := TopCat.of ↥B) ebS ⟨y, hy⟩ hyebS
          (Work.PTGeometric.HOF.eucFam n hn (ebS ⟨y, hy⟩))) := by
      rw [← Work.ThomBordism.PosAtlas.chartTr_eq_of_affine_transition (n := n) (W := TopCat.of ↥B)
        hn eb ebS (τ • (1 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) hAb
        (-(τ • eby)) htransS hdetS (⟨y, hy⟩ : ↥B) hyeb hyebS]
    have hconv2 : Work.PTGeometric.HOF.RelHmapOf n Φb ({⟨y, hy⟩} : Set ↥B)
        ({Φb ⟨y, hy⟩} : Set ↥B') hpairb
        (Work.PTGeometric.HOF.chartTr (W := TopCat.of ↥B) eb ⟨y, hy⟩ hyeb
          (Work.PTGeometric.HOF.eucFam n hn (eb ⟨y, hy⟩)))
      = Work.PTGeometric.HOF.RelHmapOf n Φb ({⟨y, hy⟩} : Set ↥B)
        ({Φb ⟨y, hy⟩} : Set ↥B') hpair0
        (Work.PTGeometric.HOF.chartTr (W := TopCat.of ↥B) ebS ⟨y, hy⟩ hyebS
          (Work.PTGeometric.HOF.eucFam n hn (ebS ⟨y, hy⟩))) :=
      hconv1.trans (LinearMap.congr_fun (Work.PTGeometric.HOF.RelHmapOf_congr rfl hpairb hpair0) _)
    rw [hconv2]
    exact hmain
  have hinjb : Function.Injective (Work.PTGeometric.HOF.RelHmapOf n Φb ({⟨y, hy⟩} : Set ↥B)
      ({Φb ⟨y, hy⟩} : Set ↥B') hpairb) :=
    Work.ThomBordism.relHmapOf_injective_of_chartTr_generator (n := n) hn Φb eb hyeb
      (stdFlatChart n) hyeb' hpairb hChartB
  -- ===================== the naturality square and the model pin =====================
  have hw_compat : Work.Cohomology.subtypeIncl W B ≫ Φ = Φb ≫ Work.Cohomology.subtypeIncl W' B' := by
    apply TopCat.ext
    intro z
    exact (hΦb_apply z).symm
  let wtilde : (Work.Cohomology.relChains W' B').homology (n + 1) :=
    (HomologicalComplex.homologyMap
      (Work.Cohomology.relChainsMapOf W W' B B' Φ Φb hw_compat) (n + 1)).hom w
  have hwtilde : wtilde = (HomologicalComplex.homologyMap
      (Work.Cohomology.relChainsMapOf W W' B B' Φ Φb hw_compat) (n + 1)).hom w := rfl
  have hx₀int' : Φ x₀ ∉ B' := hx₀intE
  have hγ : Work.PTGeometric.HOF.RelHmapOf (n + 1) Φ ({x₀} : Set W) ({Φ x₀} : Set W')
      (fun z hz hzx => hz (hΦinj z hzx))
      ((HomologicalComplex.homologyMap (Work.Orient.relPunct W B x₀ hx₀int) (n + 1)).hom w)
      = (HomologicalComplex.homologyMap
          (Work.Orient.relPunct W' B' (Φ x₀) hx₀int') (n + 1)).hom wtilde := by
    have hsq := relChainsMapOf_relPunct_aux B B' Φ Φb hw_compat hx₀int hx₀int'
      (fun z hz hzx => hz (hΦinj z hzx))
    have h2 : (HomologicalComplex.homologyMap (Work.Orient.relPunct W' B' (Φ x₀) hx₀int')
          (n + 1)).hom wtilde
        = (HomologicalComplex.homologyMap
            ((Work.Cohomology.relChainsMapOf W W' B B' Φ Φb hw_compat)
              ≫ (Work.Orient.relPunct W' B' (Φ x₀) hx₀int')) (n + 1)).hom w := by
      rw [← ModuleCat.comp_apply, ← HomologicalComplex.homologyMap_comp]
    rw [h2, hsq, HomologicalComplex.homologyMap_comp, ModuleCat.comp_apply]
    exact LinearMap.congr_fun (Work.PTGeometric.HOF.RelHmapOf_eq (n := n + 1) Φ ({x₀} : Set W)
      ({Φ x₀} : Set W') (fun z hz hzx => hz (hΦinj z hzx)))
      ((HomologicalComplex.homologyMap (Work.Orient.relPunct W B x₀ hx₀int) (n + 1)).hom w)
  have hpin : (HomologicalComplex.homologyMap (Work.Orient.relPunct W' B' (Φ x₀) hx₀int')
        (n + 1)).hom wtilde
      = Work.PTGeometric.HOF.chartTr (W := W') (Work.ThomBordism.stdIntChart (n + 1)) (Φ x₀) hx₀srcE
          (Work.PTGeometric.HOF.eucFam (n + 1) (by omega)
            ((Work.ThomBordism.stdIntChart (n + 1)) (Φ x₀))) := by
    rw [← hγ, hwB]
    exact hInt
  have hyeq : ((Φb ⟨y, hy⟩ : ↥B') : W') = y' := by
    rw [hΦb_apply, hΦy]
  have hgood'' : Work.Orient.halfBallGood (n + 1) W' (((Φb ⟨y, hy⟩ : ↥B') : W')) r' := by
    rw [hyeq]; exact hgood'M
  have hx₀'' : Φ x₀ ∈ Work.Orient.halfBallPiece (n + 1) W' (((Φb ⟨y, hy⟩ : ↥B') : W')) r' := by
    rw [hyeq]; exact hUsub hx₀'U
  have hEq' : Work.Orient.locClass (TopCat.of ↥B') n
      ((Work.Cohomology.hPairδ W' B' n).hom wtilde) (Φb ⟨y, hy⟩)
    = c • Work.PTGeometric.HOF.chartTr (W := TopCat.of ↥B') (stdFlatChart n) (Φb ⟨y, hy⟩) hyeb'
        (Work.PTGeometric.HOF.eucFam n hn ((stdFlatChart n) (Φb ⟨y, hy⟩))) := by
    have h := hmodel csM (inferInstance : IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1
      ↥(stdHalfBall (n + 1))) hbM ((Φb ⟨y, hy⟩ : ↥B') : ↥(stdHalfBall (n + 1)))
      ((Φb ⟨y, hy⟩ : ↥B').2) hyeb' (Φ x₀) hx₀srcE hx₀intE hr'pos hgood'' hx₀'' wtilde hpin
    exact h
  have hfin := boundarySign_transfer_bdry (n := n) (hn := hn) (c := c) (W := W)
    (B := (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) (y := y) (hy := hy)
    (eb := Work.Surgery.boundaryChartAt (n := n) (⟨y, hy⟩ : ↥((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)))
    (hyeb := Work.Surgery.boundaryChartAt_mem_source (n := n) (⟨y, hy⟩ : ↥((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)))
    (hx₀int := hx₀int) (w := w)
    (W' := W') (B' := B') (hB' := hB'eq) (Φ := Φ) (Φb := Φb) (hΦb := hΦb_apply)
    (hpairb := hpairb) (hΦinj := hΦinj) (eb' := stdFlatChart n) (hyeb' := hyeb')
    (r' := r') (hr' := hr'pos) (hgood' := hgood'') (hx₀' := hx₀'') (hx₀int' := hx₀intE)
    (w' := wtilde) (hγ := hγ) (hChartB := hChartB) (hEq' := hEq') (hinjb := hinjb)
  exact hfin


end

end Work.ThomBordism
