import ChallengeDeps
import Mathlib.Algebra.Order.Ring.Star
import Submission.Work.BoseB1Cube.autocorrShiftOfBudget
import Submission.Work.BoseB1Cube.chiSmallB_fderiv_bounds
import Submission.Work.BoseB1Cube.smallWinNodes
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB1Cube.swhMassRowsProved`

The two **mass rows** of the sliding-box chapter at FS's own parameters, under the explicit
`chiMass`-threshold hypothesis

    (1/δ)·R²·(C·chiSupAbs·(1/ℓ + 1/(ℓd)))²·(ℓd)³  ≤  chiMass M ℓ d u        (H)

(at `ℓ = bSide v μ`, `d = bD v μ`, `M = bM v μ = 48`):

* (FS `eq:w1>`)  `(1−δ)·8π(a v)·chiMass ≤ bW = w1MassB`;
* (FS `eq:w>g`)  `(1−δ)·g0w0Mass h·chiMass ≤ bM2 − bW`.

## Proof

(H) is exactly the **autocorrelation defect budget** of `chiSmallB`, with the constant
`C := C_geo` of the PROVED `Work.BoseB1Cube.chiSmallB_fderiv_bounds` (which bounds
`sup_x ‖∇χ_B x‖ ≤ C_geo·chiSupAbs·(1/ℓ+1/(ℓd))` and
`∫‖∇χ_B‖ ≤ C_geo·chiSupAbs·(1/ℓ+1/(ℓd))·(ℓd)³`).  Hence (H) gives

    (R²/2)·sup‖∇χ_B‖·∫‖∇χ_B‖ ≤ δ·chiMass ,

and the PROVED `Work.BoseB1Cube.autocorr_sub_le` (FS's second-order Taylor/L²-modulus bound for
the autocorrelation defect of a smooth compactly supported `χ`) turns this into the *shift
hypothesis*

    (1−δ)·chiMass ≤ ∫ x, χ_B x·χ_B (x−z)      (‖z‖ ≤ R) .

Both rows are then the PROVED integration step of FS `lm:w2>w1`:

* `Work.BoseB1Cube.shiftMassLower` — the shear identity
  (`Work.BoseFixB1S.shear_integral_identity`) plus the pointwise comparison
  `g₀(x−y)χ_B(x)χ_B(y) ≤ w₁(x,y)` a.e. give
  `(1−δ)·8π(a v)·chiMass ≤ w1MassB`;
* `Work.BoseFixB1S.boxM2SubBoxM1GeConvChiMass` — the same argument at the `ω₀`-weighted kernel
  gives `(1−δ)·g0w0Mass h·chiMass ≤ boxM2 − boxM1`, and `boxM1 = w1MassB`
  (`Work.AprioriCount.boxM1_eq_w1MassB`).

The regime gates (`0 < ℓ`, `0 < d`, `R ≤ ℓd/16`, `R ≤ ℓ·chiR0`) are supplied by
`Work.BoseFixB1.regime_sideAt_ge` at a small diluteness `ε₀`, and `bM v μ = 48` definitionally.

Nothing here is new mathematics: every analytic input is a proved lemma of the corpus; the file
records the assembly at the frozen statement.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseB1Cube

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB Work.BoseFixB1
  Work.SmallBoxSliding

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

theorem swhMassRowsProved {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) :
    ∀ δ : ℝ, 0 < δ → ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 < C ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ → ∀ u : EuclideanSpace ℝ (Fin 3),
        u ∈ Work.SmallBoxSliding.goodSet (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) μ →
        (1 / δ) * R ^ 2
            * (C * Submission.BoseGases.chiSupAbs
                * (1 / Work.BoseFixB1.bSide v μ
                   + 1 / (Work.BoseFixB1.bSide v μ * Work.BoseFixB1.bD v μ))) ^ 2
            * (Work.BoseFixB1.bSide v μ * Work.BoseFixB1.bD v μ) ^ 3
          ≤ Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bD v μ) u →
        (1 - δ) * (8 * Real.pi * _root_.BoseGases.a v)
            * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                (Work.BoseFixB1.bD v μ) u
          ≤ Work.BoseFixB1.bW v h μ u
        ∧ (1 - δ) * Submission.BoseGases.g0w0Mass h
              * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                  (Work.BoseFixB1.bD v μ) u
          ≤ Work.BoseFixB1.bM2 v h μ u - Work.BoseFixB1.bW v h μ u := by
  intro δ hδ
  -- the geometric constant of `chiSmallB_fderiv_bounds` at the fixed regularity `mValue = 48`
  obtain ⟨Cg, hCgpos, hCg⟩ := chiSmallB_fderiv_bounds (M := 48) (by norm_num)
  -- the diluteness gates (`R ≤ ℓd/16`, `R ≤ ℓ·chiR0`)
  obtain ⟨εr, hεr, hreg⟩ := Work.BoseFixB1.regime_sideAt_ge (v := v) hav hR
  refine ⟨min εr 1, Cg, lt_min hεr one_pos, hCgpos, ?_⟩
  intro μ hAdm u _hu hmass
  have hμ : 0 < μ := hAdm.1
  have hdil : μ * (_root_.BoseGases.a v) ^ 3 ≤ εr := le_trans hAdm.2.1 (min_le_left _ _)
  obtain ⟨hR16, hRχ⟩ := hreg μ hμ hdil
  have hℓ : 0 < Work.BoseFixB1.bSide v μ := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < Work.BoseFixB1.bD v μ := Work.BoseFixB1.adm_d_pos hAdm
  -- the regularity is the fixed `mValue = 48`
  have hMb : Work.BoseFixB1.bM v μ = 48 := by
    simp [Work.BoseFixB1.bM, Work.BoseBox.paramsAt, Work.BoseBox.fsParams, Work.BoseBox.mValue]
  rw [hMb] at hmass
  -- the derivative bounds at the fixed regularity
  obtain ⟨hsup, hint⟩ := hCg (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) hℓ hd u
  -- the budget (H) is exactly the hypothesis of the shift derivation
  have hshift : ∀ z : E3, ‖z‖ ≤ R →
      (1 - δ) * Work.SmallBoxSliding.chiMass 48 (Work.BoseFixB1.bSide v μ)
          (Work.BoseFixB1.bD v μ) u
        ≤ ∫ x : E3, Submission.BoseGases.chiSmallB 48 (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bD v μ) u x
            * Submission.BoseGases.chiSmallB 48 (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bD v μ) u (x - z) :=
    autocorrShiftOfBudget (M := 48) (by norm_num) (ℓ := Work.BoseFixB1.bSide v μ)
      (d := Work.BoseFixB1.bD v μ) (δ := δ) (R := R) hℓ hd hδ u (C := Cg
        * Submission.BoseGases.chiSupAbs
        * (1 / Work.BoseFixB1.bSide v μ
            + 1 / (Work.BoseFixB1.bSide v μ * Work.BoseFixB1.bD v μ))) hsup hint hmass
  refine ⟨?_, ?_⟩
  · -- (FS `eq:w1>`) the `w₁`-mass row
    have hb := shiftMassLower (v := v) (R := R) hv_supp hR hv hvrad hv1 h (M := 48) (by norm_num)
      (ℓ := Work.BoseFixB1.bSide v μ) (d := Work.BoseFixB1.bD v μ) (θ := δ) hℓ hd hR16 hRχ u hshift
    -- `bW = w1MassB` at the frozen parameters
    show (1 - δ) * (8 * Real.pi * _root_.BoseGases.a v)
        * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bD v μ) u
      ≤ Work.BoseFixB1.w1MassB h (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
          (Work.BoseFixB1.bD v μ) u
    exact hb
  · -- (FS `eq:w>g`) the `M₂`-mass row
    have hb := Work.BoseFixB1S.boxM2SubBoxM1GeConvChiMass (v := v) (R := R) hv_supp hR hv hvrad
      hv1 h (M := 48) (by norm_num) (ℓ := Work.BoseFixB1.bSide v μ) (d := Work.BoseFixB1.bD v μ)
      (θ := δ) hℓ hd hR16 hRχ u hshift
    rw [Work.AprioriCount.boxM1_eq_w1MassB (h := h) (M := 48) (by norm_num) hℓ hd u] at hb
    show (1 - δ) * Submission.BoseGases.g0w0Mass h
        * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bD v μ) u
      ≤ Work.BoseFixB1.bM2 v h μ u - Work.BoseFixB1.bW v h μ u
    exact hb

end Work.BoseB1Cube
