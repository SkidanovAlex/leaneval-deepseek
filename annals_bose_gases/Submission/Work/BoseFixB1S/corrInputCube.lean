import ChallengeDeps
import Mathlib.MeasureTheory.Function.L2Space
import Submission.Work.BoseFixB1.KH.corr.corrInputB1KH
import Submission.Work.BoseFixB1S.CubeWindow.cruxPtCube
import Submission.Work.BoseFixB1S.CubeWindow.cubeArithN
import Submission.Work.BoseFixB1S.CubeWindow.cutWordsCube
import Submission.Work.BoseFixB1S.CubeWindow.marginalCube
import Submission.Work.BoseFixB1S.CubeWindow.planchMargCube
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.corrInputCube`

The intersection-mean correction at the **cube** cutoff `chiSmallB` (FS's `χ_B` with the cosine
bump), i.e. the cube twin of `Work.BoseFixB1S.CorrInput` (`Work.BoseFixB1S.cruxCorrB1`), proved by
the mean-shift assembly `Work.BoseFixB1S.CubeWindow.cruxPtCube` + the `u`-marginals
(`CubeWindow.marginalCube`, `CubeWindow.planchMargCube`), the flat mean bound
(`Work.BoseFixB1S.corr.corrMeanSqKH`), the `chiScale` `L²` bound (`Work.BoseFixB1.KH.corr.chiL2`),
the cube cut-word bounds (`CubeWindow.cutWordsCube`, at decay order `N = 17`) and the parameter
arithmetic (`CubeWindow.cubeArithN`).

The cut-word constants carried by `cutWordsCube` are *cutoff-aware* (`(ℓd)s^{2N-5}` and
`(ℓd)⁻¹s^{2N-7}`), which is why the arithmetic is stated at those explicit exponents rather than in
the fixed-constant form of the ball-cutoff chapter: the window `chiSmall 48` is only `C^47`, so the
`N = 265`-derivative route of `corrCutWordsSharp` is unavailable at the cube cutoff.
-/

noncomputable section
open MeasureTheory
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseFixB1S

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open _root_.BoseGases

/-! ## 1. The cube mean-mismatch abbreviations (twins of `corrSt`, `corrBC`, …) -/

/-- The `u`-windowed mean-free state `χ_{B(u)}·(w − c)` at the cube cutoff. -/
def cubeSt (v : E3 → ℝ) (μ : ℝ) (w : E3 → ℝ) (c : ℝ) : E3 → E3 → ℝ :=
  fun u z => Submission.BoseGases.chiSmallB (Work.BoseBox.paramsAt μ (a v)).M
      (Work.BoseBox.sideAt μ (a v)) (Work.BoseBox.paramsAt μ (a v)).d u z * (w z - c)

/-- The function-level unfolding of `cubeSt`. -/
lemma cubeSt_fun (v : E3 → ℝ) (μ : ℝ) (w : E3 → ℝ) (c : ℝ) (u : E3) :
    cubeSt v μ w c u = fun z => Submission.BoseGases.chiSmallB
      (Work.BoseBox.paramsAt μ (a v)).M
      (Work.BoseBox.sideAt μ (a v)) (Work.BoseBox.paramsAt μ (a v)).d u z * (w z - c) := rfl

/-- The sliding-box mean `|B(u)|⁻¹∫_{B(u)}w`. -/
def cubeBC (v : E3 → ℝ) (μ : ℝ) (w : E3 → ℝ) (u : E3) : ℝ :=
  (1 / Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (a v))
      (Work.BoseBox.paramsAt μ (a v)).d u) *
    ∫ z' in Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (a v))
      (Work.BoseBox.paramsAt μ (a v)).d u, w z'

/-- The flat mean `ℓ⁻³∫_{acube ℓ}w`. -/
def cubeMean (v : E3 → ℝ) (μ : ℝ) (w : E3 → ℝ) : ℝ :=
  (1 / (Work.BoseBox.sideAt μ (a v)) ^ 3) *
    ∫ z in Submission.BoseGases.acube (Work.BoseBox.sideAt μ (a v)), w z

/-- The flat mean-square `Q` of the correction step. -/
def cubeQ (v : E3 → ℝ) (μ : ℝ) (w : E3 → ℝ) : ℝ :=
  ∫ z in Submission.BoseGases.acube (Work.BoseBox.sideAt μ (a v)), (w z - cubeMean v μ w) ^ 2

/-- The sliding-mean form on the left of the correction inequality. -/
def cubeA (v : E3 → ℝ) (μ : ℝ) (w : E3 → ℝ) : E3 → ℝ :=
  fun u => Work.BSKinetic.Decomp.bsW
    (Submission.BoseGases.fsKinCoeff (Work.BoseFixB1.sbCut μ (a v)))
    (cubeSt v μ w (cubeBC v μ w u) u)

/-- The flat-mean form on the right of the correction inequality. -/
def cubeB (v : E3 → ℝ) (μ : ℝ) (w : E3 → ℝ) (c : ℝ) : E3 → ℝ :=
  fun u => Work.BSKinetic.Decomp.bsW
    (Submission.BoseGases.fsKinCoeff (Work.BoseFixB1.sbCut μ (a v)))
    (cubeSt v μ w c u)

/-- The squared sliding mean of `w − c`. -/
def cubeBm (v : E3 → ℝ) (μ : ℝ) (w : E3 → ℝ) (c : ℝ) : E3 → ℝ :=
  fun u => (cubeBC v μ (fun z => w z - c) u) ^ 2

/-- The `L²`-norm of the `p`-transform of the mean-free state. -/
def cubeH (v : E3 → ℝ) (μ : ℝ) (w : E3 → ℝ) (c : ℝ) : E3 → ℝ :=
  fun u => Real.sqrt (∫ p : E3,
    ‖Work.BSKinetic.Decomp.bsPsi (cubeSt v μ w c u) p‖ ^ 2)

/-- The cross term of the mean-shift expansion. -/
def cubeX (v : E3 → ℝ) (μ : ℝ) (w : E3 → ℝ) (c : ℝ) : E3 → ℝ :=
  fun u => |cubeBC v μ (fun z => w z - c) u| * cubeH v μ w c u

/-- The logarithmic factor `L = 1 + (ℓd)⁻¹ + |log d|` of the flat mean-square bound. -/
def cubeL (v : E3 → ℝ) (μ : ℝ) : ℝ :=
  1 + ((Work.BoseBox.sideAt μ (a v)) * (Work.BoseBox.paramsAt μ (a v)).d)⁻¹
    + |Real.log (Work.BoseBox.paramsAt μ (a v)).d|

/-- The `N = 17` cut-word constant multiplying the mass term. -/
def cubeKq (Cq : ℝ) (v : E3 → ℝ) (μ : ℝ) : ℝ :=
  Cq * ((Work.BoseBox.sideAt μ (a v)) * (Work.BoseBox.paramsAt μ (a v)).d)
    * (Work.BoseBox.paramsAt μ (a v)).s ^ (2 * 17 - 5)

/-- The `N = 17` cut-word constant multiplying the cross term. -/
def cubeKe (Ce : ℝ) (v : E3 → ℝ) (μ : ℝ) : ℝ :=
  Ce * (((Work.BoseBox.sideAt μ (a v)) * (Work.BoseBox.paramsAt μ (a v)).d))⁻¹
    * (Work.BoseBox.paramsAt μ (a v)).s ^ (2 * 17 - 7)

/-! ## 2. The assembly -/

theorem corrInputCube {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ g : EuclideanSpace ℝ (Fin 3) → ℝ, ContDiff ℝ (⊤ : ENat) g →
        ((2 * Real.pi) ^ 3)⁻¹ *
            (∫ u : EuclideanSpace ℝ (Fin 3), Work.BSKinetic.Decomp.bsW
              (Submission.BoseGases.fsKinCoeff (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)))
              (fun z : EuclideanSpace ℝ (Fin 3) =>
                Submission.BoseGases.chiSmallB
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                    (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u z *
                  (g z - (1 / Work.SmallBoxSliding.boxMass
                      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) *
                    ∫ z' in Submission.BoseGases.dlBox
                      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u, g z')))
          ≤ ((2 * Real.pi) ^ 3)⁻¹ *
                (∫ u : EuclideanSpace ℝ (Fin 3), Work.BSKinetic.Decomp.bsW
                  (Submission.BoseGases.fsKinCoeff (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)))
                  (fun z : EuclideanSpace ℝ (Fin 3) =>
                    Submission.BoseGases.chiSmallB
                        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u z *
                      (g z - (1 / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3) *
                        ∫ z' in Submission.BoseGases.acube
                          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)), g z')))
              + (Work.BoseBox.bValue / (4 * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 2)) *
                  (∫ z in Submission.BoseGases.acube
                    (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
                    (g z - (1 / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3) *
                      ∫ z' in Submission.BoseGases.acube
                        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)), g z') ^ 2) := by
  -- the five inputs
  obtain ⟨Cq, Ce, hCqnn, hCenn, hcut⟩ :=
    CubeWindow.cutWordsCube 17 48 (by norm_num) (by norm_num)
  obtain ⟨ε_m, hεm, C₁, hC₁nn, hmean⟩ := Work.BoseFixB1S.corr.corrMeanSqKH h
  have hchi : Work.BoseFixB1.KH.corr.ChiL2 := Work.BoseFixB1.KH.corr.chiL2
  by_cases hav : 0 < _root_.BoseGases.a v
  · obtain ⟨ε_a, hεa, harith⟩ :=
      CubeWindow.cubeArithN 17 (by norm_num) Cq Ce C₁
        (Submission.BoseGases.chiNormSq)⁻¹ hCqnn hCenn hC₁nn
        (inv_nonneg.mpr (le_of_lt Submission.BoseGases.chiNormSq_pos)) hav
    refine ⟨min (min ε_m ε_a) 1, lt_min (lt_min hεm hεa) one_pos, ?_⟩
    intro μ hμ g hg
    have hμm : Work.BoseBoxFix.Adm v ε_m μ :=
      Work.BoseFixB1.Adm.mono hμ (le_trans (min_le_left _ _) (min_le_left _ _))
    have hμa : Work.BoseBoxFix.Adm v ε_a μ :=
      Work.BoseFixB1.Adm.mono hμ (le_trans (min_le_left _ _) (min_le_right _ _))
    have hμ1 : μ * (_root_.BoseGases.a v) ^ 3 ≤ 1 :=
      le_trans (Work.BoseFixB1.adm_dilute hμ) (min_le_right _ _)
    have hμ0 : 0 < μ := Work.BoseFixB1.adm_mu_pos hμ
    have hℓp : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) :=
      Work.BoseFixB1.adm_ell_pos hμ
    have hdp : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d :=
      Work.BoseFixB1.adm_d_pos hμ
    have hsp : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s :=
      Work.BoseFixB1.adm_s_pos hμ
    have ht : 0 < μ * (_root_.BoseGases.a v) ^ 3 := by positivity
    have hd1 : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d ≤ 1 := by
      rw [Work.BoseFixB1.d_eq_fsXp]
      exact Work.BoseBox.fsXp_le_one ht hμ1 (by norm_num)
    have hs1 : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s ≤ 1 := by
      show Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) 1 ≤ 1
      exact Work.BoseBox.fsXp_le_one ht hμ1 (by norm_num)
    have hM48 : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M = 48 := by
      simp [Work.BoseBox.paramsAt, Work.BoseBox.fsParams, Work.BoseBox.mValue]
    have hM1 : 1 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M := by rw [hM48]; norm_num
    have hM5 : 5 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M := by rw [hM48]; norm_num
    have hM18 : 17 + 1 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M := by
      rw [hM48]; norm_num
    -- the cut-word instance at this `μ`
    have hcutI := hcut (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (d := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)
      (s := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s)
      (c := Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v))
      hℓp hdp hd1 hsp hs1
      (show Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)
          = ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
              * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
              * Work.BoseBox.sideAt μ (_root_.BoseGases.a v))⁻¹ from rfl)
    have hQnn : 0 ≤ cubeQ v μ g := by
      rw [cubeQ]; exact integral_nonneg fun z => sq_nonneg _
    have hsubd : ContDiff ℝ (⊤ : ENat) (fun z : E3 => g z - cubeMean v μ g) :=
      hg.sub contDiff_const
    have hsubc : Continuous (fun z : E3 => g z - cubeMean v μ g) := hsubd.continuous
    have hmarg := CubeWindow.marginalCube (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
      hM1 hℓp hdp (c := Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v))
    have hAint : Integrable (cubeA v μ g) := (hmarg g hg).2.1
    have hBint : Integrable (cubeB v μ g (cubeMean v μ g)) :=
      (hmarg (fun z : E3 => g z - cubeMean v μ g) hsubd).1
    obtain ⟨hBmint, hBmbound⟩ := hmean μ hμm (fun z : E3 => g z - cubeMean v μ g) hsubd
    have hPlan := CubeWindow.planchMargCube (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
      hM1 hℓp hdp (w := fun z : E3 => g z - cubeMean v μ g) hsubd
      (hmarg (fun z : E3 => g z - cubeMean v μ g) hsubd).2.2.1
      (hmarg (fun z : E3 => g z - cubeMean v μ g) hsubd).2.2.2
    have hH2int : Integrable (fun u : E3 => (cubeH v μ g (cubeMean v μ g) u) ^ 2) := by
      refine hPlan.1.congr (Filter.Eventually.of_forall fun u => ?_)
      simp only [cubeH]
      exact (Real.sq_sqrt (integral_nonneg fun p => sq_nonneg _)).symm
    have hH2val : ∫ u : E3, (cubeH v μ g (cubeMean v μ g) u) ^ 2
        = (2 * Real.pi) ^ 3 *
          (∫ z : E3, (Submission.BoseGases.chiScale
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) z) ^ 2
            * (g z - cubeMean v μ g) ^ 2) := by
      calc ∫ u : E3, (cubeH v μ g (cubeMean v μ g) u) ^ 2
          = ∫ u : E3, ∫ p : E3, ‖Work.BSKinetic.Decomp.bsPsi
              (cubeSt v μ g (cubeMean v μ g) u) p‖ ^ 2 := by
            refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
            simp only [cubeH]
            exact Real.sq_sqrt (integral_nonneg fun p => sq_nonneg _)
        _ = (2 * Real.pi) ^ 3 *
            (∫ z : E3, (Submission.BoseGases.chiScale
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) z) ^ 2
              * (g z - cubeMean v μ g) ^ 2) := hPlan.2
    have hH2bound : ∫ u : E3, (cubeH v μ g (cubeMean v μ g) u) ^ 2
        ≤ (2 * Real.pi) ^ 3 * (Submission.BoseGases.chiNormSq)⁻¹ * cubeQ v μ g := by
      rw [hH2val]
      have hchi' := hchi (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) hℓp
        (fun z : E3 => g z - cubeMean v μ g) hsubc
      calc (2 * Real.pi) ^ 3 *
            (∫ z : E3, (Submission.BoseGases.chiScale
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) z) ^ 2
              * (g z - cubeMean v μ g) ^ 2)
          ≤ (2 * Real.pi) ^ 3 * ((Submission.BoseGases.chiNormSq)⁻¹ *
              (∫ z in Submission.BoseGases.acube (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
                (g z - cubeMean v μ g) ^ 2)) :=
            mul_le_mul_of_nonneg_left hchi' (by positivity)
        _ = (2 * Real.pi) ^ 3 * (Submission.BoseGases.chiNormSq)⁻¹ * cubeQ v μ g := by
            rw [cubeQ]
            ring
    have hAbsBm : AEStronglyMeasurable
        (fun u : E3 => |cubeBC v μ (fun z : E3 => g z - cubeMean v μ g) u|) := by
      have h1 : AEStronglyMeasurable
          (fun u : E3 => Real.sqrt (cubeBm v μ g (cubeMean v μ g) u)) :=
        Real.continuous_sqrt.comp_aestronglyMeasurable hBmint.aestronglyMeasurable
      refine h1.congr (Filter.Eventually.of_forall fun u => ?_)
      simp only [cubeBm]
      exact Real.sqrt_sq_eq_abs _
    have hHaes : AEStronglyMeasurable (cubeH v μ g (cubeMean v μ g)) := by
      have h1 : AEStronglyMeasurable
          (fun u : E3 => Real.sqrt (∫ p : E3, ‖Work.BSKinetic.Decomp.bsPsi
            (cubeSt v μ g (cubeMean v μ g) u) p‖ ^ 2)) :=
        Real.continuous_sqrt.comp_aestronglyMeasurable hPlan.1.aestronglyMeasurable
      exact h1
    have hBm_memLp : MemLp
        (fun u : E3 => |cubeBC v μ (fun z : E3 => g z - cubeMean v μ g) u|) 2 := by
      refine (MeasureTheory.memLp_two_iff_integrable_sq hAbsBm).mpr ?_
      refine hBmint.congr (Filter.Eventually.of_forall fun u => ?_)
      simp only [cubeBm]
      exact (sq_abs _).symm
    have hH_memLp : MemLp (cubeH v μ g (cubeMean v μ g)) 2 :=
      (MeasureTheory.memLp_two_iff_integrable_sq hHaes).mpr hH2int
    -- the cut-word constants at decay order `N = 17`, and the `L`/`sB` factors (written raw)
    let Kq : ℝ := Cq * ((Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)
      * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s ^ (2 * 17 - 5)
    let Ke : ℝ := Ce * (((Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d))⁻¹
      * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s ^ (2 * 17 - 7)
    let Lv : ℝ := 1 + ((Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)⁻¹
      + |Real.log (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d|
    let sB : ℝ := (((Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) ^ 3)⁻¹
    let A₁ : ℝ := Cq * ((Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)
      * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s ^ (2 * 17 - 5)
      * C₁ * Lv ^ 3 * sB
    let B₁ : ℝ := 2 * Real.sqrt (Ce
        * (((Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d))⁻¹
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s ^ (2 * 17 - 7)
        * C₁ * Lv ^ 3 * sB * (2 * Real.pi) ^ 3 * (Submission.BoseGases.chiNormSq)⁻¹)
    have hKqnn' : 0 ≤ Kq := by
      rw [show Kq = Cq * ((Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s ^ (2 * 17 - 5) from rfl]
      exact mul_nonneg (mul_nonneg hCqnn (mul_nonneg hℓp.le hdp.le)) (pow_nonneg hsp.le _)
    have hXcs : ∫ u : E3, cubeX v μ g (cubeMean v μ g) u
        ≤ Real.sqrt (C₁ * Lv ^ 3 * sB * cubeQ v μ g)
          * Real.sqrt ((2 * Real.pi) ^ 3 * (Submission.BoseGases.chiNormSq)⁻¹ * cubeQ v μ g) := by
      have hcs := Work.BSKinetic.Decomp.abs_integral_mul_le_sqrt_mul_sqrt hBm_memLp hH_memLp
      have h1 : ∫ u : E3, cubeX v μ g (cubeMean v μ g) u
          ≤ Real.sqrt (∫ u : E3, (|cubeBC v μ (fun z : E3 => g z - cubeMean v μ g) u|) ^ 2)
            * Real.sqrt (∫ u : E3, (cubeH v μ g (cubeMean v μ g) u) ^ 2) :=
        le_trans (le_abs_self _) hcs
      refine le_trans h1 (mul_le_mul ?_ (Real.sqrt_le_sqrt hH2bound) (Real.sqrt_nonneg _)
        (Real.sqrt_nonneg _))
      refine Real.sqrt_le_sqrt (le_trans ?_ hBmbound)
      exact le_of_eq (integral_congr_ae (Filter.Eventually.of_forall fun u => by
        simp only [cubeBm]
        exact sq_abs _))
    have hpt : ∀ u : E3, cubeA v μ g u
        ≤ cubeB v μ g (cubeMean v μ g) u
          + Kq * cubeBm v μ g (cubeMean v μ g) u
          + 2 * Real.sqrt Ke * cubeX v μ g (cubeMean v μ g) u := by
      intro u
      obtain ⟨hInt_u, hQ_u, hE_u⟩ := hcutI u
      have hKqnn : 0 ≤ Kq := hKqnn'
      have hcrux := CubeWindow.cruxPtCube (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (d := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)
        (κ := Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) hℓp hdp
        (M := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M) hM5 hg u hKqnn hQ_u hE_u hInt_u
        (cubeMean v μ g)
      have hring : 2 * (|cubeBC v μ (fun z : E3 => g z - cubeMean v μ g) u|
            * Real.sqrt Ke
            * Real.sqrt (∫ p : E3, ‖Work.BSKinetic.Decomp.bsPsi
                (cubeSt v μ g (cubeMean v μ g) u) p‖ ^ 2))
          = 2 * Real.sqrt Ke * cubeX v μ g (cubeMean v μ g) u := by
        rw [cubeX, cubeH]
        ring
      simp only [cubeA, cubeB, cubeBm, cubeX, cubeH, cubeSt_fun, cubeBC]
        at hcrux hring ⊢
      linarith only [hcrux, hring]
    have hXint : Integrable (cubeX v μ g (cubeMean v μ g)) := by
      have hdom : Integrable (fun u : E3 =>
          (cubeBm v μ g (cubeMean v μ g) u + (cubeH v μ g (cubeMean v μ g) u) ^ 2) / 2) :=
        (hBmint.add hH2int).div_const 2
      refine hdom.mono' (hAbsBm.mul hHaes) ?_
      refine Filter.Eventually.of_forall fun u => ?_
      simp only [Real.norm_eq_abs, cubeX]
      have hb : 0 ≤ |cubeBC v μ (fun z : E3 => g z - cubeMean v μ g) u| := abs_nonneg _
      have hh : 0 ≤ cubeH v μ g (cubeMean v μ g) u := Real.sqrt_nonneg _
      simp only [abs_of_nonneg (mul_nonneg hb hh), cubeBm]
      nlinarith [sq_nonneg (|cubeBC v μ (fun z : E3 => g z - cubeMean v μ g) u|
          - cubeH v μ g (cubeMean v μ g) u),
        sq_abs (cubeBC v μ (fun z : E3 => g z - cubeMean v μ g) u)]
    have hXint' : Integrable
        (fun u : E3 => 2 * Real.sqrt Ke * cubeX v μ g (cubeMean v μ g) u) :=
      hXint.const_mul _
    have hBmint' : Integrable
        (fun u : E3 => Kq * cubeBm v μ g (cubeMean v μ g) u) :=
      hBmint.const_mul _
    have hsumint : Integrable
        (fun u : E3 => (cubeB v μ g (cubeMean v μ g) u
            + Kq * cubeBm v μ g (cubeMean v μ g) u)
          + 2 * Real.sqrt Ke * cubeX v μ g (cubeMean v μ g) u) :=
      (hBint.add hBmint').add hXint'
    have hsBnn : 0 ≤ sB := by
      rw [show sB = (((Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) ^ 3)⁻¹ from rfl]
      exact inv_nonneg.mpr (pow_nonneg (mul_pos hℓp hdp).le 3)
    have hLnn : 0 ≤ Lv := by
      rw [show Lv = 1 + ((Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)⁻¹
          + |Real.log (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d| from rfl]
      have h1 : 0 < ((Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)⁻¹ :=
        inv_pos.mpr (mul_pos hℓp hdp)
      have h2 : 0 ≤ |Real.log (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d| := abs_nonneg _
      linarith
    have hcanon : ((2 * Real.pi) ^ 3)⁻¹ * (A₁ + B₁)
        ≤ Work.BoseBox.bValue / (4 * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 2) :=
      harith μ hμ0 (Work.BoseFixB1.adm_dilute hμa)
    have hchain : ∫ u : E3, cubeA v μ g u
        ≤ (∫ u : E3, cubeB v μ g (cubeMean v μ g) u)
          + (Kq * (∫ u : E3, cubeBm v μ g (cubeMean v μ g) u)
              + 2 * Real.sqrt Ke * (∫ u : E3, cubeX v μ g (cubeMean v μ g) u)) := by
      have hI1 : ∫ u : E3, ((fun u : E3 => cubeB v μ g (cubeMean v μ g) u)
            + (fun u : E3 => Kq * cubeBm v μ g (cubeMean v μ g) u)) u
          = (∫ u : E3, cubeB v μ g (cubeMean v μ g) u)
            + (∫ u : E3, (fun u : E3 => Kq * cubeBm v μ g (cubeMean v μ g) u) u) :=
        MeasureTheory.integral_add hBint hBmint'
      have hI2 : (∫ u : E3, (fun u : E3 => Kq * cubeBm v μ g (cubeMean v μ g) u) u)
          = Kq * (∫ u : E3, cubeBm v μ g (cubeMean v μ g) u) :=
        MeasureTheory.integral_const_mul _ _
      have hI3 : ∫ u : E3, (((fun u : E3 => cubeB v μ g (cubeMean v μ g) u)
            + (fun u : E3 => Kq * cubeBm v μ g (cubeMean v μ g) u))
            + (fun u : E3 => 2 * Real.sqrt Ke * cubeX v μ g (cubeMean v μ g) u)) u
          = (∫ u : E3, ((fun u : E3 => cubeB v μ g (cubeMean v μ g) u)
                + (fun u : E3 => Kq * cubeBm v μ g (cubeMean v μ g) u)) u)
            + (∫ u : E3, (fun u : E3 => 2 * Real.sqrt Ke
                * cubeX v μ g (cubeMean v μ g) u) u) :=
        MeasureTheory.integral_add (hBint.add hBmint') hXint'
      have hI4 : (∫ u : E3, (fun u : E3 => 2 * Real.sqrt Ke
              * cubeX v μ g (cubeMean v μ g) u) u)
          = 2 * Real.sqrt Ke * (∫ u : E3, cubeX v μ g (cubeMean v μ g) u) :=
        MeasureTheory.integral_const_mul _ _
      have hmono := MeasureTheory.integral_mono hAint hsumint hpt
      calc ∫ u : E3, cubeA v μ g u
          ≤ ∫ u : E3, (((fun u : E3 => cubeB v μ g (cubeMean v μ g) u)
                + (fun u : E3 => Kq * cubeBm v μ g (cubeMean v μ g) u))
              + (fun u : E3 => 2 * Real.sqrt Ke * cubeX v μ g (cubeMean v μ g) u)) u := hmono
        _ = (∫ u : E3, cubeB v μ g (cubeMean v μ g) u)
              + (Kq * (∫ u : E3, cubeBm v μ g (cubeMean v μ g) u)
                + 2 * Real.sqrt Ke * (∫ u : E3, cubeX v μ g (cubeMean v μ g) u)) := by
            rw [hI3, hI1, hI2, hI4]; ring_nf
    have hA1 : Kq * (∫ u : E3, cubeBm v μ g (cubeMean v μ g) u) ≤ A₁ * cubeQ v μ g := by
      calc Kq * (∫ u : E3, cubeBm v μ g (cubeMean v μ g) u)
          ≤ Kq * (C₁ * Lv ^ 3 * sB * cubeQ v μ g) :=
            mul_le_mul_of_nonneg_left hBmbound hKqnn'
        _ = A₁ * cubeQ v μ g := by
            rw [show A₁ = Kq * C₁ * Lv ^ 3 * sB from rfl]
            ring
    have hA2 : 2 * Real.sqrt Ke * (∫ u : E3, cubeX v μ g (cubeMean v μ g) u)
        ≤ B₁ * cubeQ v μ g := by
      have hcs := Work.BoseFixB1.KH.corr.sqrt_mul_sqrt_mul
        (a := C₁ * Lv ^ 3 * sB)
        (b := (2 * Real.pi) ^ 3 * (Submission.BoseGases.chiNormSq)⁻¹) (Q := cubeQ v μ g)
        (mul_nonneg (mul_nonneg hC₁nn (pow_nonneg hLnn 3)) hsBnn)
        (mul_nonneg (by positivity) (inv_nonneg.mpr (le_of_lt Submission.BoseGases.chiNormSq_pos)))
        hQnn
      have hB₁ : B₁ = 2 * Real.sqrt Ke
          * Real.sqrt (C₁ * Lv ^ 3 * sB
              * ((2 * Real.pi) ^ 3 * (Submission.BoseGases.chiNormSq)⁻¹)) := by
        rw [show B₁ = 2 * Real.sqrt (Ce
              * (((Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d))⁻¹
              * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s ^ (2 * 17 - 7)
              * C₁ * Lv ^ 3 * sB * (2 * Real.pi) ^ 3
              * (Submission.BoseGases.chiNormSq)⁻¹) from rfl,
          show Ke = Ce * (((Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d))⁻¹
              * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s ^ (2 * 17 - 7) from rfl,
          show Ce * (((Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d))⁻¹
              * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s ^ (2 * 17 - 7)
              * C₁ * Lv ^ 3 * sB * (2 * Real.pi) ^ 3
              * (Submission.BoseGases.chiNormSq)⁻¹
            = (Ce * (((Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d))⁻¹
              * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s ^ (2 * 17 - 7))
              * ((C₁ * Lv ^ 3 * sB)
                * ((2 * Real.pi) ^ 3 * (Submission.BoseGases.chiNormSq)⁻¹)) from by ring,
          Real.sqrt_mul (by positivity)]
        ring
      calc 2 * Real.sqrt Ke * (∫ u : E3, cubeX v μ g (cubeMean v μ g) u)
          ≤ 2 * Real.sqrt Ke * (Real.sqrt (C₁ * Lv ^ 3 * sB * cubeQ v μ g)
              * Real.sqrt ((2 * Real.pi) ^ 3 * (Submission.BoseGases.chiNormSq)⁻¹
                  * cubeQ v μ g)) :=
            mul_le_mul_of_nonneg_left hXcs (by positivity)
        _ = B₁ * cubeQ v μ g := by
            rw [hB₁, hcs]
            ring
    have hcorr : Kq * (∫ u : E3, cubeBm v μ g (cubeMean v μ g) u)
          + 2 * Real.sqrt Ke * (∫ u : E3, cubeX v μ g (cubeMean v μ g) u)
        ≤ (A₁ + B₁) * cubeQ v μ g := by
      calc _ ≤ A₁ * cubeQ v μ g + B₁ * cubeQ v μ g := add_le_add hA1 hA2
        _ = (A₁ + B₁) * cubeQ v μ g := by ring
    have hfinal : ((2 * Real.pi) ^ 3)⁻¹ * (∫ u : E3, cubeA v μ g u)
        ≤ ((2 * Real.pi) ^ 3)⁻¹ * (∫ u : E3, cubeB v μ g (cubeMean v μ g) u)
          + (Work.BoseBox.bValue / (4 * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 2))
              * cubeQ v μ g := by
      have hpi : 0 < ((2 * Real.pi) ^ 3)⁻¹ := inv_pos.mpr (by positivity)
      have hY : ((2 * Real.pi) ^ 3)⁻¹ *
            (Kq * (∫ u : E3, cubeBm v μ g (cubeMean v μ g) u)
              + 2 * Real.sqrt Ke * (∫ u : E3, cubeX v μ g (cubeMean v μ g) u))
          ≤ (Work.BoseBox.bValue / (4 * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 2))
              * cubeQ v μ g := by
        calc ((2 * Real.pi) ^ 3)⁻¹ *
              (Kq * (∫ u : E3, cubeBm v μ g (cubeMean v μ g) u)
                + 2 * Real.sqrt Ke * (∫ u : E3, cubeX v μ g (cubeMean v μ g) u))
            ≤ ((2 * Real.pi) ^ 3)⁻¹ * ((A₁ + B₁) * cubeQ v μ g) :=
              mul_le_mul_of_nonneg_left hcorr (le_of_lt hpi)
          _ = (((2 * Real.pi) ^ 3)⁻¹ * (A₁ + B₁)) * cubeQ v μ g := by ring
          _ ≤ (Work.BoseBox.bValue / (4 * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 2))
                * cubeQ v μ g := mul_le_mul_of_nonneg_right hcanon hQnn
      calc ((2 * Real.pi) ^ 3)⁻¹ * (∫ u : E3, cubeA v μ g u)
          ≤ ((2 * Real.pi) ^ 3)⁻¹ *
            ((∫ u : E3, cubeB v μ g (cubeMean v μ g) u)
              + (Kq * (∫ u : E3, cubeBm v μ g (cubeMean v μ g) u)
                + 2 * Real.sqrt Ke * (∫ u : E3, cubeX v μ g (cubeMean v μ g) u))) :=
            mul_le_mul_of_nonneg_left hchain (le_of_lt hpi)
        _ = ((2 * Real.pi) ^ 3)⁻¹ * (∫ u : E3, cubeB v μ g (cubeMean v μ g) u)
              + ((2 * Real.pi) ^ 3)⁻¹ *
                (Kq * (∫ u : E3, cubeBm v μ g (cubeMean v μ g) u)
                  + 2 * Real.sqrt Ke * (∫ u : E3, cubeX v μ g (cubeMean v μ g) u)) := by ring_nf
        _ ≤ ((2 * Real.pi) ^ 3)⁻¹ * (∫ u : E3, cubeB v μ g (cubeMean v μ g) u)
              + (Work.BoseBox.bValue / (4 * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 2))
                  * cubeQ v μ g := add_le_add (le_refl _) hY
    exact hfinal
  · exact ⟨1, one_pos, fun μ hμ g hg => absurd (Work.BoseFixB1.adm_a_pos hμ) hav⟩

end Work.BoseFixB1S
