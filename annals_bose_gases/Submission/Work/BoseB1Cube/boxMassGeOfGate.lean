import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB1Cube.bM2_le_two_mul_bW
import Submission.Work.BoseB1Cube.boxMassGateLower
import Submission.Work.BoseB1Cube.flatArm37RowOneBadL
import Submission.Work.BoseB1Cube.flatArm37RowOneGoodLower
import Submission.Work.BoseB1Cube.gammaSmallAt
import Submission.Work.BoseB1Cube.sbWordCubePairArm
import Submission.Work.BoseB1Cube.smallRowsBundle
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB1Cube.boxMassGeOfGate`

The gate `a(v) ≤ μ·∬w_{1,B(u)}` on FS's good set forces the sliding-box volume to be large:
`64 ≤ μ·|B(u)|`.

## Proof (architecture)

Let `ℓ = PBℓ v μ = sideAt μ (a v)`, `d = PBd v μ`, `δ = μ^{-1/3}`, `χ_B = chiSmallB 48 ℓ d u`,
`χ = chiMass = ∫χ_B²`, `V = boxMass = |B(u)| = |dlBox ℓ d u|`.

1. The sharp per-box mass law (`w1MassB_le_sharp` at `δ = 1`) and the gate give
   `a ≤ μ·PBW ≤ μ·16πa·χ`, so `1/(16π) ≤ μ·χ`.
2. Split on whether the box `dlBox ℓ d u` lies in the *sliver* `{‖x‖ ≥ ℓ(1/2−ε)}` for the
   parameter `ε := min (1/2) √(1/(1024πC))`, where `C` is the constant of the sliver bound
   (`chiMassLeSliverCube`, proved from the boundary flatness `chi_boundary_taylor`):
   * if it does, then `χ ≤ Cε²V`, so `1/(16π) ≤ μCε²V` gives `μV ≥ 1/(16πCε²) ≥ 64`
     (by the choice of `ε`);
   * if it does not, some `x ∈ dlBox ℓ d u` has `‖x‖ < ℓ(1/2−ε)`.  Writing
     `e_j = shortSide ℓ d u j` (so `V = ∏_j e_j`) and `β_j = max 0 (|((ℓd)•u)_j| − ℓd/2)`,
     the geometry (`shortSideBetaGeom`) gives `e_j ≥ δ`, `e_j ≤ ℓd`,
     `∑_j β_j² ≤ ℓ²(1/2−ε)²` and `β_j = ℓ/2 − e_j` whenever `e_j < ℓd`; the pure arithmetic
     lemma `boxMassGeArith` (whose hypothesis `8δ ≤ ℓd`, `512δ ≤ ℓ` are the parameter gates
     `ellParamGatesGe`) then yields `64δ³ ≤ V`, i.e. `μV ≥ 64μδ³ = 64`.
-/

namespace Work.BoseB1Cube

open MeasureTheory

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The target -/

theorem boxMassGeOfGate {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ u : EuclideanSpace ℝ (Fin 3),
        u ∈ Work.SmallBoxSliding.goodSet (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBd v μ) μ →
        (_root_.BoseGases.a v) ≤ μ * Work.BoseFixB1B.PBW h μ u →
        64 ≤ μ * Work.BoseFixB1B.PBBV v μ u := by
  -- 1. the sharp mass law at `δ = 1`
  obtain ⟨εs, hεs, hsharp⟩ :=
    w1MassB_le_sharp h hv hv1 hvrad hR hv_supp hav (δ := 1) (by norm_num)
  -- 2. the sliver constant
  obtain ⟨C, hCpos, hCsliver⟩ := chiMassLeSliverCube (M := Work.BoseBox.mValue)
    (by norm_num [Work.BoseBox.mValue])
  -- 3. the parameter gates
  obtain ⟨εg, hεg, hεg1, hparams⟩ := ellParamGatesGe (v := v) hav
  -- 4. the sliver parameter
  set ε : ℝ := min (1 / 2) (Real.sqrt (1 / (1024 * Real.pi * C))) with hεdef
  have hεpos : 0 < ε := lt_min (by norm_num) (Real.sqrt_pos.mpr (by positivity))
  have hεle : ε ≤ 1 / 2 := min_le_left _ _
  have hεsq : C * ε ^ 2 ≤ 1 / (1024 * Real.pi) := by
    have hlt : ε ≤ Real.sqrt (1 / (1024 * Real.pi * C)) := min_le_right _ _
    have hnn : (0 : ℝ) ≤ 1 / (1024 * Real.pi * C) := by positivity
    have h2 : ε ^ 2 ≤ 1 / (1024 * Real.pi * C) := by
      calc ε ^ 2 ≤ (Real.sqrt (1 / (1024 * Real.pi * C))) ^ 2 :=
            pow_le_pow_left₀ hεpos.le hlt 2
        _ = 1 / (1024 * Real.pi * C) := Real.sq_sqrt hnn
    calc C * ε ^ 2 ≤ C * (1 / (1024 * Real.pi * C)) := mul_le_mul_of_nonneg_left h2 hCpos.le
      _ = 1 / (1024 * Real.pi) := by field_simp
  refine ⟨min (min εs εg) 1, lt_min (lt_min hεs hεg) one_pos, ?_⟩
  intro μ hAdm u hu hg
  have hμ : 0 < μ := Work.BoseFixB1.adm_mu_pos hAdm
  have ha : 0 < _root_.BoseGases.a v := Work.BoseFixB1.adm_a_pos hAdm
  have hAdms : Work.BoseBoxFix.Adm v εs μ :=
    Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_left _ _) (min_le_left _ _))
  have hAdmg : Work.BoseBoxFix.Adm v εg μ :=
    Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_left _ _) (min_le_right _ _))
  -- parameters
  obtain ⟨hgA, hgB, hgd2, hgδpos, hgreg⟩ := hparams μ hAdmg
  have hℓpos : 0 < Work.BoseFixB1B.PBℓ v μ := Work.BoseFixB1.adm_ell_pos hAdm
  have hdpos : 0 < Work.BoseFixB1B.PBd v μ := Work.BoseFixB1.adm_d_pos hAdm
  have hd1 : Work.BoseFixB1B.PBd v μ ≤ 1 := le_trans hgd2 (by norm_num)
  have hδpos : 0 < μ ^ (-(1 / 3 : ℝ)) := Real.rpow_pos_of_pos hμ _
  -- the gate bounds the cutoff mass from below
  have hchi : 1 / (16 * Real.pi) ≤ μ * Work.SmallBoxSliding.chiMass (Work.BoseFixB1B.PBM v μ)
      (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBd v μ) u := by
    have h2 := hsharp μ hAdms u
    have h3 : (1 + (1 : ℝ)) * (8 * Real.pi * _root_.BoseGases.a v)
          * Work.SmallBoxSliding.chiMass (Work.BoseFixB1B.PBM v μ) (Work.BoseFixB1B.PBℓ v μ)
              (Work.BoseFixB1B.PBd v μ) u
        = 16 * Real.pi * _root_.BoseGases.a v
          * Work.SmallBoxSliding.chiMass (Work.BoseFixB1B.PBM v μ) (Work.BoseFixB1B.PBℓ v μ)
              (Work.BoseFixB1B.PBd v μ) u := by ring
    rw [h3] at h2
    have h4 : _root_.BoseGases.a v ≤ μ * (16 * Real.pi * _root_.BoseGases.a v
        * Work.SmallBoxSliding.chiMass (Work.BoseFixB1B.PBM v μ) (Work.BoseFixB1B.PBℓ v μ)
            (Work.BoseFixB1B.PBd v μ) u) :=
      le_trans hg (mul_le_mul_of_nonneg_left h2 hμ.le)
    have h5 : (1 : ℝ) ≤ 16 * Real.pi * μ
        * Work.SmallBoxSliding.chiMass (Work.BoseFixB1B.PBM v μ) (Work.BoseFixB1B.PBℓ v μ)
            (Work.BoseFixB1B.PBd v μ) u := by
      have h6 : (1 : ℝ) * _root_.BoseGases.a v
          ≤ (16 * Real.pi * μ
              * Work.SmallBoxSliding.chiMass (Work.BoseFixB1B.PBM v μ) (Work.BoseFixB1B.PBℓ v μ)
                  (Work.BoseFixB1B.PBd v μ) u) * _root_.BoseGases.a v := by
        calc (1 : ℝ) * _root_.BoseGases.a v = _root_.BoseGases.a v := by ring
          _ ≤ μ * (16 * Real.pi * _root_.BoseGases.a v
              * Work.SmallBoxSliding.chiMass (Work.BoseFixB1B.PBM v μ) (Work.BoseFixB1B.PBℓ v μ)
                  (Work.BoseFixB1B.PBd v μ) u) := h4
          _ = (16 * Real.pi * μ
              * Work.SmallBoxSliding.chiMass (Work.BoseFixB1B.PBM v μ) (Work.BoseFixB1B.PBℓ v μ)
                  (Work.BoseFixB1B.PBd v μ) u) * _root_.BoseGases.a v := by ring
      exact le_of_mul_le_mul_right h6 ha
    have hpos : (0 : ℝ) < 16 * Real.pi := by positivity
    rw [div_le_iff₀ hpos]
    calc (1 : ℝ) = 1 := rfl
      _ ≤ 16 * Real.pi * μ
          * Work.SmallBoxSliding.chiMass (Work.BoseFixB1B.PBM v μ) (Work.BoseFixB1B.PBℓ v μ)
              (Work.BoseFixB1B.PBd v μ) u := h5
      _ = μ * Work.SmallBoxSliding.chiMass (Work.BoseFixB1B.PBM v μ) (Work.BoseFixB1B.PBℓ v μ)
              (Work.BoseFixB1B.PBd v μ) u * (16 * Real.pi) := by ring
  -- the box volume is nonnegative
  have hVnn : 0 ≤ Work.SmallBoxSliding.boxMass (Work.BoseFixB1B.PBℓ v μ)
      (Work.BoseFixB1B.PBd v μ) u := by
    rw [Work.SmallBoxSliding.boxMass_eq_measureReal, MeasureTheory.Measure.real_def]
    exact ENNReal.toReal_nonneg
  -- the main dichotomy
  by_cases hsl : ∀ x : E3, x ∈ Submission.BoseGases.dlBox (Work.BoseFixB1B.PBℓ v μ)
      (Work.BoseFixB1B.PBd v μ) u → (Work.BoseFixB1B.PBℓ v μ) * (1 / 2 - ε) ≤ ‖x‖
  · -- SLIVER CASE: the cutoff mass is tiny, so the box must be large
    have hsl' := hCsliver hℓpos hdpos hεpos hεle u hsl
    have hchain : 1 / (16 * Real.pi) ≤ μ * (C * ε ^ 2)
        * Work.SmallBoxSliding.boxMass (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBd v μ) u := by
      calc 1 / (16 * Real.pi) ≤ μ * Work.SmallBoxSliding.chiMass (Work.BoseFixB1B.PBM v μ)
            (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBd v μ) u := hchi
        _ ≤ μ * (C * ε ^ 2 * Work.SmallBoxSliding.boxMass (Work.BoseFixB1B.PBℓ v μ)
              (Work.BoseFixB1B.PBd v μ) u) := mul_le_mul_of_nonneg_left hsl' hμ.le
        _ = μ * (C * ε ^ 2) * Work.SmallBoxSliding.boxMass (Work.BoseFixB1B.PBℓ v μ)
              (Work.BoseFixB1B.PBd v μ) u := by ring
    have hCε2pos : 0 < C * ε ^ 2 := mul_pos hCpos (pow_pos hεpos 2)
    have h2 : 64 * (C * ε ^ 2) ≤ 1 / (16 * Real.pi) := by
      calc 64 * (C * ε ^ 2) ≤ 64 * (1 / (1024 * Real.pi)) :=
            mul_le_mul_of_nonneg_left hεsq (by norm_num)
        _ = 1 / (16 * Real.pi) := by ring
    have h4 : 64 * (C * ε ^ 2) ≤ (μ * Work.SmallBoxSliding.boxMass
        (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBd v μ) u) * (C * ε ^ 2) := by
      calc 64 * (C * ε ^ 2) ≤ 1 / (16 * Real.pi) := h2
        _ ≤ μ * (C * ε ^ 2) * Work.SmallBoxSliding.boxMass (Work.BoseFixB1B.PBℓ v μ)
              (Work.BoseFixB1B.PBd v μ) u := hchain
        _ = (μ * Work.SmallBoxSliding.boxMass (Work.BoseFixB1B.PBℓ v μ)
              (Work.BoseFixB1B.PBd v μ) u) * (C * ε ^ 2) := by ring
    exact le_of_mul_le_mul_right h4 hCε2pos
  · -- NON-SLIVER CASE: the box reaches the ball, and the geometry gives `V ≥ 64δ³`
    push Not at hsl
    obtain ⟨x, hxmem, hxlt⟩ := hsl
    obtain ⟨hlo, hhi, hβnn, hclip, hcons⟩ :=
      shortSideBetaGeom (ℓ := Work.BoseFixB1B.PBℓ v μ) (d := Work.BoseFixB1B.PBd v μ)
        (μ := μ) (ε := ε) hℓpos hdpos hd1 hgd2 hμ hgreg hεpos.le hεle hu hxmem hxlt.le
    have hhalf : (1 / 2 - ε) ^ 2 ≤ 1 / 4 := by nlinarith [hεpos.le, hεle]
    have hcons' : ∑ j : Fin 3, (max 0 (|((Work.BoseFixB1B.PBℓ v μ
          * Work.BoseFixB1B.PBd v μ) • u).ofLp j| - Work.BoseFixB1B.PBℓ v μ
            * Work.BoseFixB1B.PBd v μ / 2)) ^ 2
        ≤ (Work.BoseFixB1B.PBℓ v μ) ^ 2 / 4 := by
      calc ∑ j : Fin 3, (max 0 (|((Work.BoseFixB1B.PBℓ v μ
              * Work.BoseFixB1B.PBd v μ) • u).ofLp j| - Work.BoseFixB1B.PBℓ v μ
                * Work.BoseFixB1B.PBd v μ / 2)) ^ 2
          ≤ (Work.BoseFixB1B.PBℓ v μ) ^ 2 * (1 / 2 - ε) ^ 2 := hcons
        _ ≤ (Work.BoseFixB1B.PBℓ v μ) ^ 2 * (1 / 4) :=
            mul_le_mul_of_nonneg_left hhalf (by positivity)
        _ = (Work.BoseFixB1B.PBℓ v μ) ^ 2 / 4 := by ring
    have h64 := boxMassGeArith (ℓ := Work.BoseFixB1B.PBℓ v μ)
      (d := Work.BoseFixB1B.PBd v μ) (δ := μ ^ (-(1 / 3 : ℝ))) hℓpos hdpos hδpos hgA hgB
      (fun j : Fin 3 => Work.SmallBoxSliding.shortSide (Work.BoseFixB1B.PBℓ v μ)
        (Work.BoseFixB1B.PBd v μ) u j)
      (fun j : Fin 3 => max 0 (|((Work.BoseFixB1B.PBℓ v μ * Work.BoseFixB1B.PBd v μ) • u).ofLp j|
        - Work.BoseFixB1B.PBℓ v μ * Work.BoseFixB1B.PBd v μ / 2))
      hlo hhi hβnn hclip hcons'
    -- `boxMass` is the product of the short sides
    have hbm : Work.SmallBoxSliding.boxMass (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBd v μ) u
        = ∏ j : Fin 3, Work.SmallBoxSliding.shortSide (Work.BoseFixB1B.PBℓ v μ)
            (Work.BoseFixB1B.PBd v μ) u j := by
      rw [Work.BoseFixB1S.oneBodyB1.sqrtW.boxMassProdB1 hℓpos hdpos hd1 u]
      refine Finset.prod_congr rfl (fun j _ => ?_)
      exact max_eq_right (by linarith [hlo j, hδpos] : (0 : ℝ) ≤
        Work.SmallBoxSliding.shortSide (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBd v μ) u j)
    rw [Work.BoseFixB1B.PBBV, hbm]
    -- `μ·δ³ = 1`
    have hcube : μ * (μ ^ (-(1 / 3 : ℝ))) ^ 3 = 1 := by
      rw [← Real.rpow_natCast (μ ^ (-(1 / 3 : ℝ))) 3,
        ← Real.rpow_mul (x := μ) hμ.le (-(1 / 3)) ((3 : ℕ) : ℝ),
        show (-(1 / 3 : ℝ) * ((3 : ℕ) : ℝ)) = -1 by norm_num, Real.rpow_neg_one]
      exact mul_inv_cancel₀ (ne_of_gt hμ)
    calc (64 : ℝ) = 64 * (μ * (μ ^ (-(1 / 3 : ℝ))) ^ 3) := by rw [hcube, mul_one]
      _ = μ * (64 * (μ ^ (-(1 / 3 : ℝ))) ^ 3) := by ring
      _ ≤ μ * ∏ j : Fin 3, Work.SmallBoxSliding.shortSide (Work.BoseFixB1B.PBℓ v μ)
            (Work.BoseFixB1B.PBd v μ) u j := mul_le_mul_of_nonneg_left h64 hμ.le

end Work.BoseB1Cube
