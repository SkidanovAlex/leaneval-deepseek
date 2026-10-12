import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB1Cube.Free.Props
import Submission.Work.BoseB1Cube.Free.RowOneLedgerWideF
import Submission.Work.BoseB1Cube.boxM2_sub_w1MassB_ge_of_windowDichotomy
import Submission.Work.BoseB1Cube.boxMassGeGateArb
import Submission.Work.BoseB1Cube.smallRowsBundleWide
import Submission.Work.BoseFixB1.PBGamma_le_of_dilute
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseB1Cube

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB Work.BoseFixB1
  Work.SmallBoxSliding

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "X" => Submission.BoseGases.X

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 16000000

theorem LargeWinNodeF {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) : Work.BoseB1Cube.LargeWinPropF v h R := by
  classical
  intro Cn hCn
  -- ## 1. the analytic ingredients, each at its own diluteness threshold
  obtain ⟨εP, κ, CP, hεP, hκ0, hCP0, hrung⟩ :=
    sbWordCube_ge_payPortR3 h hv hv1 hvrad hR hv_supp hav
  obtain ⟨εG, hεG, hGates⟩ := boxDataGatesContDiff h hv hv1 hvrad hR hv_supp hav
  obtain ⟨εW, KW, hεW, hKW0, hWrow⟩ :=
    Work.BoseFixB1S.w1MassB_le_const_mul_boxMass h hv hv1 hvrad hR hv_supp hav
  obtain ⟨εM, hεM, hM2le2⟩ := bM2_le_two_mul_bW h hv hv1 hvrad hR hv_supp hav
  obtain ⟨εγ, hεγ, hγ⟩ := gammaRegimeAt (v := v) hav hR
  obtain ⟨εV, hεV, hVgate⟩ :=
    boxMassGeGateArb h hv hv1 hvrad hR hv_supp hav (64 * Cn) (by positivity)
  obtain ⟨εR3, hεR3, hR3row⟩ := shiftR3Row (v := v) h hv hv1 hvrad hR hv_supp hav (Cn := Cn) hCn
  obtain ⟨εw, hεw, hwd⟩ := windowShiftDichotomy h hv hv1 hvrad hR hv_supp hav 1 le_rfl
  obtain ⟨ε₂, hε₂, hrow2⟩ :=
    boxM2_sub_w1MassB_ge_of_windowDichotomy h hv hv1 hvrad hR hv_supp hav 1 le_rfl
  -- ## 2. the constants
  set D₁ : ℝ := KW with hD₁def
  have hD₁0 : 0 ≤ D₁ := by rw [hD₁def]; exact hKW0
  set D₂ : ℝ := 8 * Real.pi * (Submission.BoseGases.chiSupAbs
    * Submission.BoseGases.chiSmallDecay Work.BoseBox.mValue) ^ 2 with hD₂def
  have hD₂0 : 0 ≤ D₂ := by rw [hD₂def]; positivity
  set C : ℝ := max CP (2 * D₁ * Cn + 3 * D₁ / 4 + 4 * D₂ * Cn
    + 8 * (2 + κ) * Cn ^ 2 / (_root_.BoseGases.a v) + 130) + 1 with hCdef
  have hCPle : CP ≤ C := by
    rw [hCdef]
    linarith [le_max_left CP (2 * D₁ * Cn + 3 * D₁ / 4 + 4 * D₂ * Cn
      + 8 * (2 + κ) * Cn ^ 2 / (_root_.BoseGases.a v) + 130)]
  have hC0 : 0 ≤ C := by
    rw [hCdef]
    have h2 : (0 : ℝ) ≤ 2 * D₁ * Cn := by nlinarith [hD₁0, hCn]
    have h3 : (0 : ℝ) ≤ 3 * D₁ / 4 := by linarith
    have h4 : (0 : ℝ) ≤ 4 * D₂ * Cn := by nlinarith [hD₂0, hCn]
    have h5 : (0 : ℝ) ≤ 8 * (2 + κ) * Cn ^ 2 / (_root_.BoseGases.a v) :=
      div_nonneg (mul_nonneg (by linarith [hκ0]) (sq_nonneg Cn)) hav.le
    have h1 : (0 : ℝ) ≤ 2 * D₁ * Cn + 3 * D₁ / 4 + 4 * D₂ * Cn
        + 8 * (2 + κ) * Cn ^ 2 / (_root_.BoseGases.a v) + 130 := by linarith
    have h6 : max CP (2 * D₁ * Cn + 3 * D₁ / 4 + 4 * D₂ * Cn
        + 8 * (2 + κ) * Cn ^ 2 / (_root_.BoseGases.a v) + 130) = max CP
        (2 * D₁ * Cn + 3 * D₁ / 4 + 4 * D₂ * Cn
          + 8 * (2 + κ) * Cn ^ 2 / (_root_.BoseGases.a v) + 130) := rfl
    rw [h6] at *
    linarith [le_max_right CP (2 * D₁ * Cn + 3 * D₁ / 4 + 4 * D₂ * Cn
      + 8 * (2 + κ) * Cn ^ 2 / (_root_.BoseGases.a v) + 130)]
  have hCredC : 2 * D₁ * Cn + 3 * D₁ / 4 + 4 * D₂ * Cn ≤ C := by
    rw [hCdef]
    have h5 : (0 : ℝ) ≤ 8 * (2 + κ) * Cn ^ 2 / (_root_.BoseGases.a v) :=
      div_nonneg (mul_nonneg (by linarith [hκ0]) (sq_nonneg Cn)) hav.le
    have h2 : 2 * D₁ * Cn + 3 * D₁ / 4 + 4 * D₂ * Cn
        ≤ 2 * D₁ * Cn + 3 * D₁ / 4 + 4 * D₂ * Cn
          + 8 * (2 + κ) * Cn ^ 2 / (_root_.BoseGases.a v) + 130 := by linarith
    linarith [h2, le_max_right CP (2 * D₁ * Cn + 3 * D₁ / 4 + 4 * D₂ * Cn
      + 8 * (2 + κ) * Cn ^ 2 / (_root_.BoseGases.a v) + 130)]
  have hCaC : 4 * 2 * (2 * 1 + κ) * Cn ^ 2 ≤ C * (_root_.BoseGases.a v) := by
    have h2 : 8 * (2 + κ) * Cn ^ 2 / (_root_.BoseGases.a v) * (_root_.BoseGases.a v)
        = 8 * (2 + κ) * Cn ^ 2 := by rw [div_mul_cancel₀ _ (ne_of_gt hav)]
    have h6 : (0 : ℝ) ≤ 2 * D₁ * Cn := by nlinarith [hD₁0, hCn]
    have h7 : (0 : ℝ) ≤ 4 * D₂ * Cn := by nlinarith [hD₂0, hCn]
    have h3 : 8 * (2 + κ) * Cn ^ 2 / (_root_.BoseGases.a v) ≤ C := by
      rw [hCdef]
      have h5 : 8 * (2 + κ) * Cn ^ 2 / (_root_.BoseGases.a v)
          ≤ 2 * D₁ * Cn + 3 * D₁ / 4 + 4 * D₂ * Cn
            + 8 * (2 + κ) * Cn ^ 2 / (_root_.BoseGases.a v) + 130 := by linarith
      linarith [h5, le_max_right CP (2 * D₁ * Cn + 3 * D₁ / 4 + 4 * D₂ * Cn
        + 8 * (2 + κ) * Cn ^ 2 / (_root_.BoseGases.a v) + 130)]
    have h5 : 8 * (2 + κ) * Cn ^ 2 ≤ C * (_root_.BoseGases.a v) := by
      have h8 := mul_le_mul_of_nonneg_right h3 hav.le
      linarith [h2, h8]
    nlinarith [h5]
  set KgD : ℝ := 2 * Cn * (D₂ + D₁ / 2) + 8 * Cn ^ 2 * C + 2 * C + 1 with hKgDdef
  have hKgD0 : 0 ≤ KgD := by
    rw [hKgDdef]
    have h1 : (0 : ℝ) ≤ 2 * Cn * (D₂ + D₁ / 2) :=
      mul_nonneg (by linarith [hCn]) (by linarith [hD₁0, hD₂0])
    have h2 : (0 : ℝ) ≤ 8 * Cn ^ 2 * C :=
      mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg Cn)) hC0
    linarith [h1, h2]
  obtain ⟨εbg, hεbg, hbggate⟩ := bGapCoeff_gate (v := v) hav KgD hKgD0
  -- the `Γ`-threshold
  obtain ⟨εΓ, hεΓ, hΓle⟩ := Work.BoseFixB1.PBGamma_le_of_dilute (v := v)
    (c := min (min (1 / (8 * (max κ 1))) (1 / (128 * Cn ^ 2 * (2 + κ))))
      (min (1 / (10 * (C * (_root_.BoseGases.a v) + 1))) (1 / 4)))
    (by
      refine lt_min (lt_min (div_pos one_pos (by positivity)) (div_pos one_pos (by positivity)))
        (lt_min (div_pos one_pos (by positivity)) (by norm_num)))
  -- ## 3. the merged diluteness threshold
  let T : Finset ℝ := {εP, εG, εW, εM, εγ, εV, εR3, εΓ, εbg, εw, ε₂, 1}
  have hT : T.Nonempty := by simp [T]
  set ε₀ : ℝ := T.min' hT with hε₀def
  have hε₀pos : 0 < ε₀ := by
    rw [hε₀def, Finset.lt_min'_iff]
    intro y hy
    simp only [T, Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [hεP, hεG, hεW, hεM, hεγ, hεV, hεR3, hεΓ, hεbg, hεw, hε₂, one_pos]
  have hle₀ : ∀ {ε' : ℝ}, ε' ∈ T → ε₀ ≤ ε' := by
    intro ε' hε'
    rw [hε₀def]
    exact Finset.min'_le T ε' hε'
  refine ⟨ε₀, hε₀pos, ?_⟩
  intro μ hAdm n Ψ u hu hnotwin hΨc hsupp hI hnlo hnhi
  have AdmOf : ∀ {ε' : ℝ}, ε' ∈ T → Work.BoseBoxFix.Adm v ε' μ :=
    fun hε' => Work.BoseFixB1.Adm.mono hAdm (hle₀ hε')
  have hAdmP : Work.BoseBoxFix.Adm v εP μ := AdmOf (by simp [T])
  have hAdmG : Work.BoseBoxFix.Adm v εG μ := AdmOf (by simp [T])
  have hAdmW : Work.BoseBoxFix.Adm v εW μ := AdmOf (by simp [T])
  have hAdmM : Work.BoseBoxFix.Adm v εM μ := AdmOf (by simp [T])
  have hAdmγ : Work.BoseBoxFix.Adm v εγ μ := AdmOf (by simp [T])
  have hAdmV : Work.BoseBoxFix.Adm v εV μ := AdmOf (by simp [T])
  have hAdmR3 : Work.BoseBoxFix.Adm v εR3 μ := AdmOf (by simp [T])
  have hAdmΓ : Work.BoseBoxFix.Adm v εΓ μ := AdmOf (by simp [T])
  have hAdmbg : Work.BoseBoxFix.Adm v εbg μ := AdmOf (by simp [T])
  have hAdmw : Work.BoseBoxFix.Adm v εw μ := AdmOf (by simp [T])
  have hAdm₂ : Work.BoseBoxFix.Adm v ε₂ μ := AdmOf (by simp [T])
  have hAdm1 : Work.BoseBoxFix.Adm v 1 μ := AdmOf (by simp [T])
  have hμ : 0 < μ := hAdm.1
  have hℓ : 0 < Work.BoseFixB1.bSide v μ := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < Work.BoseFixB1.bD v μ := Work.BoseFixB1.adm_d_pos hAdm
  have hdil1 : μ * (_root_.BoseGases.a v) ^ 3 ≤ 1 := hAdm1.2.1
  have hVgood : 1 ≤ μ * Work.BoseFixB1.bV v μ u :=
    Work.BoseFixB1.SectorAux.one_le_mu_boxMassGood hav hμ hdil1 hu
  -- the gate `a v ≤ μ·PBW` and its variants
  have hgate : (_root_.BoseGases.a v) ≤ μ * Work.BoseFixB1B.PBW h μ u :=
    le_of_lt (lt_of_not_ge hnotwin)
  have hnot' : ¬ (Work.BoseFixB1B.PBW h μ u ≤ 1 * (_root_.BoseGases.a v) / μ) := by
    rw [one_mul]
    intro hle
    have h2 : Work.BoseFixB1.bW v h μ u * μ ≤ _root_.BoseGases.a v := (le_div_iff₀ hμ).mp hle
    exact hnotwin (by simpa [mul_comm] using h2)
  have hV64 : 64 * Cn ≤ μ * Work.BoseFixB1B.PBBV v μ u := hVgate μ hAdmV u hu hgate
  -- the shift hypothesis (branch 2 of the window dichotomy)
  have hshift : ∀ z : E3, ‖z‖ ≤ R →
      (1 - 2 * Work.BoseFixB1B.PBΓ v μ) * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ)
        (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u
        ≤ ∫ x : E3, Submission.BoseGases.chiSmallB (Work.BoseFixB1.bM v μ)
            (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u x
          * Submission.BoseGases.chiSmallB (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bD v μ) u (x - z) := by
    intro z hz
    rcases hwd μ hAdmw u hu with h1 | h2
    · exact absurd h1 hnot'
    · exact h2 z hz
  -- ## 4. the state-level abbreviations
  set V : ℝ := Work.BoseFixB1.bV v μ u with hVdef
  set χ : ℝ := Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
    (Work.BoseFixB1.bD v μ) u with hχdef
  set Γ : ℝ := Work.BoseFixB1B.PBΓ v μ with hΓdef
  set M₁ : ℝ := Work.BoseFixB1.bW v h μ u with hM₁def
  set M₂ : ℝ := Work.BoseFixB1.bM2 v h μ u with hM₂def
  set G : ℝ := Submission.BoseGases.g0w0Mass h * χ with hGdef
  have hVb : Work.BoseFixB1.bV v μ u = V := hVdef.symm
  have hVPBb : Work.BoseFixB1B.PBBV v μ u = V := by rw [hVdef]; rfl
  have hχPB : Work.SmallBoxSliding.chiMass (Work.BoseFixB1B.PBM v μ) (Work.BoseFixB1B.PBℓ v μ)
      (Work.BoseFixB1B.PBd v μ) u = χ := by rw [hχdef]; rfl
  have hΓPB : Work.BoseFixB1B.PBΓ v μ = Γ := hΓdef.symm
  have hM₁PB : Work.BoseFixB1B.PBW h μ u = M₁ := by rw [hM₁def]; rfl
  have hnlo' : Cn * μ * V ≤ (n : ℝ) := by rw [← hVb]; exact hnlo
  have hnhi' : (n : ℝ) ≤ 2 * Cn * μ * V := by rw [← hVb]; exact hnhi
  have hV0 : 0 < V := by
    rw [hVdef]
    exact Work.BoseFixB1.boxMass_pos_of_goodSet hℓ hd hμ hu
  have hχ0 : 0 ≤ χ := by rw [hχdef]; exact Work.SmallBoxSliding.chiMass_nonneg _ _ _ _
  have hM₁0 : 0 ≤ M₁ := by
    rw [hM₁def]
    exact Work.BoseFixB1.w1MassB_nonneg h hv hvrad hR hv_supp hℓ hd u
  have hG0 : 0 ≤ G := by
    rw [hGdef]
    exact mul_nonneg (Work.SmallBoxA0.g0w0Mass_nonneg_general hR hv_supp h) hχ0
  obtain ⟨hR16, hRχ, hd8, hΓpos', hΓhalf, _hΓsharp⟩ := hγ hAdmγ
  have hΓ0 : 0 ≤ Γ := by rw [hΓdef]; linarith [hΓpos']
  have hΓhalf' : 2 * Γ ≤ 1 / 2 := by rw [hΓdef]; exact hΓhalf
  have hM2le : M₂ ≤ 2 * M₁ := by rw [hM₂def, hM₁def]; exact hM2le2 μ hAdmM u
  have hM2ub : M₂ - M₁ ≤ 2 * M₁ := by linarith [hM2le]
  -- the mass comparison `(1 − 2Γ)·g₀ω₀·χ ≤ M₂ − M₁`
  have hM2m : (1 - 1 * (2 * Γ)) * G ≤ M₂ - M₁ := by
    have hraw := hrow2 μ hAdm₂ u hu hnot'
    have hB2 : Work.BoseFixB1S.boxM2 (Work.BoseFixB1B.PBBV v μ u) (Work.BoseFixB1B.PBB v μ u)
        (Submission.BoseGases.wSmallPair (Work.BoseFixB1B.PBM v μ) (Work.BoseFixB1B.PBℓ v μ)
          (Work.BoseFixB1B.PBd v μ) u (Submission.BoseGases.g2 v h)) = M₂ := by
      rw [hM₂def]; rfl
    have hL : (1 - 2 * Work.BoseFixB1B.PBΓ v μ) * Submission.BoseGases.g0w0Mass h
        * Work.SmallBoxSliding.chiMass (Work.BoseFixB1B.PBM v μ) (Work.BoseFixB1B.PBℓ v μ)
          (Work.BoseFixB1B.PBd v μ) u = (1 - 1 * (2 * Γ)) * G := by
      rw [hχPB, hΓPB, hGdef]; ring
    rw [hL, hB2, hM₁PB] at hraw
    exact hraw
  have hGle2 : G ≤ 2 * M₁ := by
    have h1 : (1 : ℝ) / 2 ≤ 1 - 1 * (2 * Γ) := by linarith [hΓhalf]
    have h2 : (1 : ℝ) / 2 * G ≤ (1 - 1 * (2 * Γ)) * G := mul_le_mul_of_nonneg_right h1 hG0
    have h3 : M₂ - M₁ ≤ M₁ := by linarith [hM2le]
    linarith [h2, hM2m, h3]
  -- the upper mass rows
  have hM1ub : M₁ ≤ D₁ * (_root_.BoseGases.a v) * V := by
    have h1 := hWrow μ hAdmW u
    rw [hM₁def, hD₁def, hVdef]
    simpa only [Work.BoseFixB1.bW, Work.BoseFixB1.bM, Work.BoseFixB1.bSide, Work.BoseFixB1.bD,
      Work.BoseFixB1.bV] using h1
  have hGub : G ≤ D₂ * (_root_.BoseGases.a v) * V := by
    have hM48 : 1 ≤ Work.BoseFixB1.bM v μ := by
      rw [Work.BoseFixB1.bM, Work.BoseFixB1.M_eq_mValue]; norm_num [Work.BoseBox.mValue]
    have hχb := Work.BoseFixB1S.chiMass_le_const_mul_boxMass (M := Work.BoseFixB1.bM v μ)
      hM48 hℓ hd u
    have hMe : Work.BoseFixB1.bM v μ = Work.BoseBox.mValue := rfl
    have hχb' : χ ≤ (Submission.BoseGases.chiSupAbs
        * Submission.BoseGases.chiSmallDecay Work.BoseBox.mValue) ^ 2 * V := by
      rw [hχdef, hVdef]
      simpa only [Work.BoseFixB1.bV, hMe] using hχb
    have hGle : Submission.BoseGases.g0w0Mass h ≤ 8 * Real.pi * (_root_.BoseGases.a v) :=
      Work.SmallBoxA0.g0w0Mass_le_av hR hv hvrad hv_supp h
    calc G ≤ (8 * Real.pi * (_root_.BoseGases.a v)) *
            ((Submission.BoseGases.chiSupAbs
              * Submission.BoseGases.chiSmallDecay Work.BoseBox.mValue) ^ 2 * V) := by
          rw [hGdef]
          exact mul_le_mul hGle hχb' hχ0 (by positivity)
      _ = D₂ * (_root_.BoseGases.a v) * V := by rw [hD₂def]; ring
  -- the `Γ`-smallnesses
  have hΓκ : κ * Γ ≤ 1 / 8 := by
    have h1 : Work.BoseFixB1B.PBΓ v μ ≤ 1 / (8 * (max κ 1)) :=
      le_trans (hΓle μ hAdmΓ) (le_trans (min_le_left _ _) (min_le_left _ _))
    have h2 : κ ≤ max κ 1 := le_max_left _ _
    have hΓpos2 : 0 < Work.BoseFixB1B.PBΓ v μ := by linarith [hΓpos']
    have h2pos : (0 : ℝ) < max κ 1 := lt_of_lt_of_le one_pos (le_max_right κ 1)
    have h4 : κ * Work.BoseFixB1B.PBΓ v μ ≤ (max κ 1) * (1 / (8 * (max κ 1))) :=
      mul_le_mul h2 h1 (le_of_lt hΓpos2) (le_of_lt h2pos)
    have h5 : (max κ 1) * (1 / (8 * (max κ 1))) = 1 / 8 := by
      rw [mul_one_div, div_eq_iff (mul_ne_zero (by norm_num : (8 : ℝ) ≠ 0) (ne_of_gt h2pos))]
      ring
    rw [hΓdef]
    linarith [h4, h5]
  have hΓCaT : Γ ≤ 1 / (10 * (C * (_root_.BoseGases.a v) + 1)) := by
    rw [hΓdef]
    exact le_trans (hΓle μ hAdmΓ) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hΓrow : 128 * Cn ^ 2 * (2 + κ) * Γ ≤ 1 := by
    rw [hΓdef]
    have h1 : Work.BoseFixB1B.PBΓ v μ ≤ 1 / (128 * Cn ^ 2 * (2 + κ)) :=
      le_trans (hΓle μ hAdmΓ) (le_trans (min_le_left _ _) (min_le_right _ _))
    have h2 : 0 < 128 * Cn ^ 2 * (2 + κ) := by
      refine mul_pos (mul_pos (by norm_num) (pow_pos (by linarith [hCn]) 2)) (by linarith [hκ0])
    rw [le_div_iff₀ h2] at h1
    linarith [h1]
  have hδ0 : (0 : ℝ) ≤ 2 * Γ := by linarith [hΓ0]
  have hK1 : (0 : ℝ) ≤ 1 := by norm_num
  have hD₀2 : (0 : ℝ) ≤ 2 := by norm_num
  have hKδ' : 1 * (2 * Γ) ≤ 1 / 2 := by linarith [hΓhalf']
  have hμV1 : 1 ≤ μ * V := by rw [hVdef]; exact hVgood
  have hμVc : 64 * Cn ≤ μ * V := by rw [hVdef]; exact hV64
  -- ## 5. the counts
  set S : ℝ := Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
    (Work.BoseFixB1.bA v μ u) Ψ with hSdef
  set Q : ℝ := Work.BoseFixB1S.boxQCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
    (Work.BoseFixB1.bA v μ u) Ψ with hQdef
  set Pc : ℝ := Work.BoseFixB1S.boxPairCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
    (Work.BoseFixB1.bA v μ u) Ψ with hPcdef
  set t : ℝ := (n : ℝ) / V with htdef
  set c₀ : ℝ := Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v) with hc₀def
  obtain ⟨hVpos, _hWdef, _hM1nn, _hM2le', hPcnn, hcS2⟩ := hGates μ hAdmG n Ψ hΨc u hu hI
  have hS0 : 0 ≤ S := by
    rw [hSdef]
    exact Finset.sum_nonneg (fun i _ => integral_nonneg (fun x => sq_nonneg _))
  have hQ0 : 0 ≤ Q := by
    rw [hQdef]
    exact Finset.sum_nonneg (fun i _ => integral_nonneg (fun x => sq_nonneg _))
  have hPc0 : 0 ≤ Pc := by rw [hPcdef]; exact hPcnn
  have hS2S : S ^ 2 - S ≤ Pc := by rw [hPcdef]; simpa only [pow_two] using hcS2
  have hsq : S + Q = t * V := by
    rw [hSdef, hQdef, htdef]
    simp only [Work.BoseFixB1.bA]
    have hsplit := Work.BoseFixB1S.b1sCountSplit (N := n) (ℓ := Work.BoseFixB1.bSide v μ)
      (volA := Work.BoseFixB1.bV v μ u) hℓ hVpos
      (Work.SmallBoxSliding.measurableSet_dlBox _ _ _)
      (by simp only [Work.BoseFixB1.bV, Work.SmallBoxSliding.boxMass_eq_measureReal,
        MeasureTheory.Measure.real_def])
      (Work.SmallBoxSliding.dlBox_subset_acube _ _ _) hΨc.continuous hsupp
    rw [hsplit, hI, mul_one]
    rw [div_mul_cancel₀ _ (ne_of_gt hV0)]
  have ht0 : 0 ≤ t := by
    rw [htdef]; exact div_nonneg (Nat.cast_nonneg n) hV0.le
  have htw : t ≤ 2 * Cn * μ := by
    rw [htdef]
    exact (div_le_iff₀ hV0).mpr (by linarith [hnhi'])
  have h4 : 4 * μ ≤ t := by
    rw [htdef, le_div_iff₀ hV0]
    have h1 : 4 * (μ * V) ≤ Cn * (μ * V) := mul_le_mul_of_nonneg_right hCn (by linarith [hμV1])
    nlinarith [hnlo', h1]
  -- ## 6. the gap gate and the `R₃` row for the target's count window
  have hbg' : (D₂ + D₁ / 2) * (_root_.BoseGases.a v) * t
      + 2 * C * (_root_.BoseGases.a v) * μ
      + 4 * Cn * C * (_root_.BoseGases.a v) * t
      ≤ Work.BoseFixB1.bGapCoeff v μ := by
    have hμa0 : (0 : ℝ) ≤ μ * (_root_.BoseGases.a v) := mul_nonneg hμ.le hav.le
    have h1 : (D₂ + D₁ / 2) * (_root_.BoseGases.a v) * t
        ≤ (2 * Cn * (D₂ + D₁ / 2)) * (μ * (_root_.BoseGases.a v)) := by
      nlinarith [htw, ht0, hD₁0, hD₂0, hμ, hav.le, hCn]
    have h2 : 4 * Cn * C * (_root_.BoseGases.a v) * t
        ≤ (8 * Cn ^ 2 * C) * (μ * (_root_.BoseGases.a v)) := by
      have h4 : 4 * Cn * C * t ≤ 4 * Cn * C * (2 * Cn * μ) :=
        mul_le_mul_of_nonneg_left htw
          (mul_nonneg (mul_nonneg (by norm_num) (by linarith [hCn])) hC0)
      nlinarith [h4, hμa0, hav.le, hC0, hμ]
    have h3 : 2 * C * (_root_.BoseGases.a v) * μ = (2 * C) * (μ * (_root_.BoseGases.a v)) := by
      ring
    have h4 : (2 * Cn * (D₂ + D₁ / 2) + 8 * Cn ^ 2 * C + 2 * C)
        * (μ * (_root_.BoseGases.a v)) ≤ KgD * (μ * (_root_.BoseGases.a v)) := by
      rw [hKgDdef]
      exact mul_le_mul_of_nonneg_right (by linarith [hD₁0, hD₂0, hC0, hCn]) hμa0
    have hgg := hbggate μ hAdmbg
    linarith [h1, h2, h3, h4, hgg]
  have hR3' : 2 * (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) ^ 3 * t * χ
      ≤ μ ^ 2 * Γ * M₁ := by
    have h2 := hR3row (μ := μ) hAdmR3 u hu hshift
      (show (n : ℝ) ≤ 2 * Cn * μ * Work.BoseFixB1B.PBBV v μ u by
        rw [hVPBb]; exact hnhi')
    rw [hVPBb, hχPB, hΓPB, hM₁PB, ← htdef] at h2
    exact h2
  have hR3led : 2 * C * (_root_.BoseGases.a v)
      * ((Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) ^ 3 * t * χ)
      ≤ C * μ ^ 2 * (_root_.BoseGases.a v) * Γ * M₁ := by
    have h1 := mul_le_mul_of_nonneg_left hR3' (mul_nonneg hC0 hav.le)
    have e1 : 2 * C * (_root_.BoseGases.a v)
        * ((Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) ^ 3 * t * χ)
        = C * (_root_.BoseGases.a v)
          * (2 * ((Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) ^ 3 * t * χ)) := by ring
    have e2 : C * (_root_.BoseGases.a v) * (μ ^ 2 * Γ * M₁)
        = C * μ ^ 2 * (_root_.BoseGases.a v) * Γ * M₁ := by ring
    linarith [h1, e1, e2]
  -- ## 7. the bundle and the ledger
  have hsmall : M₁ * (S / V) / V + μ * M₁ / (2 * V) + M₁ / (4 * V ^ 2)
      + (1 / 2) * (1 + κ * Γ) * G * (t / V)
      + (1 / 2) * (1 - 1 * (2 * Γ)) * G * (S / V) / V
      + (1 / 2) * G * (2 * 1 + κ) * Γ * t ^ 2 + C * (_root_.BoseGases.a v) * (c₀ ^ 3 * t * χ)
      ≤ (1 / 2) * μ ^ 2 * M₁ :=
    smallRowsBundleWide (V := V) (μ := μ) (a := _root_.BoseGases.a v) (χ := χ)
      (G := G) (M₁ := M₁) (S := S) (Q := Q) (c₀ := c₀) (Γ := Γ) (κ := κ) (KK := 1) (C := C)
      (n := (n : ℝ)) (Cn := Cn) hV0 hμ hΓ0 hκ0 hC0 hM₁0 hG0 hS0 hQ0 hχ0
      (le_of_lt (Work.BoseFixB1S.sbCut_pos hμ hav)) (Nat.cast_nonneg n) hCn hsq h4 htw hμVc
      (by norm_num) le_rfl hKδ' hΓκ hGle2 hR3' hΓCaT hΓrow
  have hled : (1 / 18) * μ * t * M₁
      ≤ payLedgerF V μ (_root_.BoseGases.a v) Γ κ G M₁ (M₂ - M₁) S Q t Pc
          (Work.BoseFixB1.bGapCoeff v μ) C (c₀ ^ 3 * t * χ) :=
    rowOneLedgerWideF (V := V) (μ := μ) (a := _root_.BoseGases.a v) (Γ := Γ) (κ := κ) (K := 1)
      (D₀ := 2) (D₁ := D₁) (D₂ := D₂) (δ := 2 * Γ) (G := G) (M₁ := M₁) (MΔ := M₂ - M₁)
      (S := S) (Q := Q) (t := t) (Pc := Pc) (bg := Work.BoseFixB1.bGapCoeff v μ) (C := C)
      (Cn := Cn) (caT := c₀ ^ 3 * t * χ)
      hV0 hμ hav.le hΓ0 hκ0 hC0 hCn hM₁0 hG0 hS0 hQ0 hsq ht0 h4 hS2S hPc0 hGle2 hM2m hM2ub
      hM1ub hGub hδ0 (le_refl (2 * Γ)) hK1 hD₀2 hD₁0 hD₂0 hΓκ hKδ' hμV1 hbg' hsmall
  -- ## 8. the payment rung and the definitional bridge
  have hn1 : 1 ≤ n := by
    have h8 : 4 * μ * V ≤ (n : ℝ) := by
      have h7 : 4 * μ * V ≤ t * V := mul_le_mul_of_nonneg_right h4 hV0.le
      have h9 : t * V = (n : ℝ) := by rw [htdef, div_mul_cancel₀ _ (ne_of_gt hV0)]
      linarith [h7, h9]
    have h10 : (4 : ℝ) ≤ (n : ℝ) := by nlinarith [h8, hμV1]
    exact_mod_cast (by linarith : (1 : ℝ) ≤ (n : ℝ))
  have hr := hrung μ hAdmP n Ψ u hu hn1 hΨc hI hsupp
  have hsbcut : (0 : ℝ) ≤ Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v) :=
    le_of_lt (Work.BoseFixB1S.sbCut_pos hμ hav)
  have hmono := payPortR3Lower_mono_C (v := v) h (μ := μ) (n := n) (Φ := Ψ) (u := u)
    (κ := κ) (C := CP) (C' := C) hCPle hav.le hμ.le hsbcut hV0 hS0 hQ0 hχ0
  have hpay := payPortR3Lower_eqF (v := v) (h := h) (μ := μ) (n := n) (Φ := Ψ) (u := u)
    (κ := κ) (C := C) (V := V) (χ := χ) (Γ := Γ) (M₁ := M₁) (M₂ := M₂) (S := S) (Q := Q)
    (Pc := Pc) (t := t) (c₀ := c₀) (G := G)
    hVdef hχdef hΓdef hM₁def hM₂def hSdef hQdef hPcdef htdef hc₀def hGdef
  have hfin : payLedgerF V μ (_root_.BoseGases.a v) Γ κ G M₁ (M₂ - M₁) S Q t Pc
      (Work.BoseFixB1.bGapCoeff v μ) C (c₀ ^ 3 * t * χ)
      ≤ Work.BoseFixB1B.sbWordCube v h μ u Ψ := by
    rw [← hpay]
    exact le_trans hmono hr
  exact le_trans hled hfin

end Work.BoseB1Cube
