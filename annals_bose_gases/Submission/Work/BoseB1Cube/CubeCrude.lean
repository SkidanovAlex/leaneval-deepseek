import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB1Cube.CubeCrudeGood
import Submission.Work.BoseFixB1C.trimOffInteriorCube
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB1Cube.CubeCrude` — the crude per-`u` bound, assembled from two pieces

`Work.BoseB1Cube.CubeCrude` (FS `final_v2.tex` l.4083 at the cube cutoff, for *every* window `u`)
is assembled here from

* `Work.BoseB1Cube.CubeCrudeGood` — the same bound on FS's good set.  It is **implied by the
  per-box row** `CubePerBox` (`Work.BoseB1Cube.cubeCrudeGood_of_cubePerBox`, PROVED), and
* `Work.BoseB1Cube.CubeCrudeBand` — the residual on the *outer band* `cube ∖ goodSet`, where the
  small box pokes out of the big one.

Off the sliding cube the bound is **free and exact**: `sbWordCube = sbKinCube + sbPot`,
`sbPot = 0` on the far set (`Work.BoseFixB1B.sbPot_eq_zero_of_mem_farSet`; the potential slot is
window-free) and `sbKinCube ≥ 0` (`Work.BoseFixB1C.sbKinCube_nonneg`), while the right-hand side is
`≤ 0`; the only geometric input is `Work.BoseFixB1B.cube_compl_subset_farSet`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseB1Cube

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The crude per-`u` bound on the outer band** `cube ∖ goodSet` — the only place where
`CubeCrude` is not already supplied by the per-box row.  This is the cube twin of FS l.4083 read
on the partial boxes. -/
def CubeCrudeBand (v : E3 → ℝ) (h : ScatSol v) : Prop :=
  ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
    ∀ (J : ℝ) (μ : ℝ), Adm v ε₀ μ →
      J ≤ (paramsAt μ (a v)).KB ^ 3 →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))),
        IsLowB v h J μ n Φ →
        ∀ u : E3,
          u ∈ Work.BoseFixB1B.cube (sideAt μ (a v)) (paramsAt μ (a v)).d →
          u ∉ Work.SmallBoxSliding.goodSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ →
          -(C * (μ ^ 2 * (a v)
                  * Work.SmallBoxSliding.chiMass (paramsAt μ (a v)).M (sideAt μ (a v))
                      (paramsAt μ (a v)).d u
                + μ * (a v)))
              * normB v μ n (Φ : X n → ℝ)
            ≤ Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ)

/-- **The matched word is nonnegative off the sliding cube** — the potential slot is window-free
and vanishes on the far set, the kinetic slot is a sum of squares. -/
theorem sbWordCube_nonneg_of_notMem_cube {v : E3 → ℝ} {h : ScatSol v} {ε₀ μ : ℝ}
    (hAdm : Adm v ε₀ μ) {n : ℕ} {u : E3}
    (hu : u ∉ Work.BoseFixB1B.cube (sideAt μ (a v)) (paramsAt μ (a v)).d)
    (Φ : X n → ℝ) :
    0 ≤ Work.BoseFixB1B.sbWordCube v h μ u Φ := by
  have hℓ : 0 < sideAt μ (a v) := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < (paramsAt μ (a v)).d := Work.BoseFixB1.adm_d_pos hAdm
  have hfar : u ∈ Work.SmallBoxSliding.farSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ :=
    Work.BoseFixB1B.cube_compl_subset_farSet hu
  have hpot : Work.BoseFixB1.sbPot h μ u Φ = 0 :=
    Work.BoseFixB1B.sbPot_eq_zero_of_mem_farSet (v := v) (h := h) (μ := μ) (n := n) hℓ hd hfar Φ
  rw [Work.BoseFixB1C.sbWordCube_eq_add, hpot, add_zero]
  exact Work.BoseFixB1C.sbKinCube_nonneg hAdm u Φ

/-- **The crude per-`u` bound from its good-set and band pieces** (at `0 < a v`, which is what makes
the trivial off-the-cube clause hold: the right-hand side is then `≤ 0`). -/
theorem cubeCrude_of_pieces {v : E3 → ℝ} {h : ScatSol v} (hav : 0 < a v)
    (hG : CubeCrudeGood v h) (hB : CubeCrudeBand v h) : CubeCrude v h := by
  obtain ⟨εg, Cg, hεg, hCg, hgood⟩ := hG
  obtain ⟨εb, Cb, hεb, hCb, hband⟩ := hB
  refine ⟨min εg εb, max Cg Cb, lt_min hεg hεb, le_trans hCg (le_max_left _ _), ?_⟩
  intro J μ hAdm hJK n Φ u hlow
  have hAdmg : Adm v εg μ := Work.BoseFixB1.Adm.mono hAdm (min_le_left _ _)
  have hAdmb : Adm v εb μ := Work.BoseFixB1.Adm.mono hAdm (min_le_right _ _)
  have hμ : 0 < μ := Work.BoseFixB1.adm_mu_pos hAdm
  have ha : 0 ≤ a v := le_of_lt hav
  have hχ : 0 ≤ Work.SmallBoxSliding.chiMass (paramsAt μ (a v)).M (sideAt μ (a v))
      (paramsAt μ (a v)).d u := Work.SmallBoxSliding.chiMass_nonneg _ _ _ _
  have hN : 0 ≤ normB v μ n (Φ : X n → ℝ) := Work.BoseFixB1.normB_nonneg _
  have hK : 0 ≤ μ ^ 2 * (a v) * Work.SmallBoxSliding.chiMass (paramsAt μ (a v)).M
        (sideAt μ (a v)) (paramsAt μ (a v)).d u + μ * (a v) :=
    add_nonneg (mul_nonneg (mul_nonneg (sq_nonneg μ) ha) hχ) (mul_nonneg hμ.le ha)
  by_cases hmem : u ∈ Work.SmallBoxSliding.goodSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ
  · have h1 := hgood J μ hAdmg hJK n Φ u hmem hlow
    have hle : (Cg * (μ ^ 2 * (a v) * Work.SmallBoxSliding.chiMass (paramsAt μ (a v)).M
          (sideAt μ (a v)) (paramsAt μ (a v)).d u + μ * (a v))) * normB v μ n (Φ : X n → ℝ)
        ≤ ((max Cg Cb) * (μ ^ 2 * (a v) * Work.SmallBoxSliding.chiMass (paramsAt μ (a v)).M
          (sideAt μ (a v)) (paramsAt μ (a v)).d u + μ * (a v))) * normB v μ n (Φ : X n → ℝ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hK) hN
    linarith [h1, hle]
  · by_cases hcube : u ∈ Work.BoseFixB1B.cube (sideAt μ (a v)) (paramsAt μ (a v)).d
    · have h1 := hband J μ hAdmb hJK n Φ hlow u hcube hmem
      have hle : (Cb * (μ ^ 2 * (a v) * Work.SmallBoxSliding.chiMass (paramsAt μ (a v)).M
            (sideAt μ (a v)) (paramsAt μ (a v)).d u + μ * (a v))) * normB v μ n (Φ : X n → ℝ)
          ≤ ((max Cg Cb) * (μ ^ 2 * (a v) * Work.SmallBoxSliding.chiMass (paramsAt μ (a v)).M
            (sideAt μ (a v)) (paramsAt μ (a v)).d u + μ * (a v))) * normB v μ n (Φ : X n → ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hK) hN
      linarith [h1, hle]
    · have h1 := sbWordCube_nonneg_of_notMem_cube (h := h) hAdm hcube (Φ : X n → ℝ)
      have h2 : 0 ≤ ((max Cg Cb) * (μ ^ 2 * (a v) * Work.SmallBoxSliding.chiMass
            (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u + μ * (a v)))
          * normB v μ n (Φ : X n → ℝ) :=
        mul_nonneg (mul_nonneg (le_trans hCg (le_max_left _ _)) hK) hN
      linarith [h1, h2]

/-- **`CubeCrude` from the per-box row and the outer band alone** — the two residuals of §3 of
`FINDING_cube_chapter.md`. -/
theorem cubeCrude_of_cubePerBox_and_band {v : E3 → ℝ} (h : ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hav : 0 < a v)
    (hF : CubePerBox v h R) (hB : CubeCrudeBand v h) : CubeCrude v h :=
  cubeCrude_of_pieces hav (cubeCrudeGood_of_cubePerBox h hv hv1 hvrad hR hv_supp hav hF) hB

end Work.BoseB1Cube
