import ChallengeDeps
import Submission.Work.BoseB1Cube.windowShiftDichotomy
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB1Cube.boxM2_sub_w1MassB_ge_of_windowDichotomy`

The **mass-difference row** `lm:w2>w1` of FS at the sliding box, in the dichotomy form:

    (1 − 2·Γ) · (g₀ω₀-mass) · chiMass  ≤  boxM2 − w1MassB      whenever  `w1MassB > C·(a v)/μ`,

where `Γ = PBΓ v μ = K_B³ (μ(a v)³)^{1/2}` and `chiMass = ∫ χ_{B(u)}²`.

## Proof

* `windowShiftDichotomy` (with the *same* constant `C`) splits every admissible `(μ,u)` into
  `PBW ≤ C(a v)/μ`, which is exactly the hypothesis we are given the negation of, and the
  **shift bound**

      (1 − 2 Γ)·chiMass ≤ ∫ χ_B(x)·χ_B(x − z)        (‖z‖ ≤ R) .          (S)

* `regime_sideAt_ge` supplies the two geometric gates `R ≤ ℓd/16` and `R ≤ ℓ·chiR0`
  (`ℓ = PBℓ v μ = sideAt μ (a v)`, `d = PBd v μ`).
* `Work.BoseFixB1S.boxM2SubBoxM1GeConvChiMass` then converts (S) + the gates into

      (1 − θ)·(g₀ω₀-mass)·chiMass ≤ boxM2 − boxM1 ,     θ := 2 Γ ,

  `boxM2 = ∬_{B(u)×B(u)} w_{2,B(u)}`, `boxM1 = ∫_{B(u)} (w_{1,B(u)})-fibre`.
* The last step is the **mass identity** `PBW h μ u = boxM1 ℓ (dlBox ℓ d u) (wSmall1Pair …)`
  (gate 1 of `Work.BoseFixB1.boxMassGates`; reproved here from `boxM1_eq_nested` so that the
  import cone stays minimal): every localised kernel vanishes off the sliding box in each
  variable, so the nested integral over `ℝ³ × ℝ³` computing `w1MassB` collapses onto the box.
-/

namespace Work.BoseB1Cube

/-- **The mass identity** at the sliding box: `w1MassB = boxM1` there.  This is
`Work.BoseFixB1B.wsc_PBW_eq_boxM1`, reproved from `Work.BoseFixB1.boxM1_eq_nested` to keep the
import cone of this file minimal. -/
theorem PBW_eq_boxM1_dl {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {μ : ℝ}
    {u : EuclideanSpace ℝ (Fin 3)}
    (hℓ : 0 < Work.BoseFixB1B.PBℓ v μ) (hd : 0 < Work.BoseFixB1B.PBd v μ)
    (hM : 1 ≤ Work.BoseFixB1B.PBM v μ) :
    Work.BoseFixB1B.PBW h μ u
      = Work.BoseFixB1S.boxM1 (Work.BoseFixB1B.PBℓ v μ)
          (Submission.BoseGases.dlBox (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBd v μ) u)
          (Submission.BoseGases.wSmall1Pair h (Work.BoseFixB1B.PBM v μ)
            (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBd v μ) u) := by
  rw [Work.BoseFixB1B.PBW,
    Work.BoseFixB1.boxM1_eq_nested (ℓ := Work.BoseFixB1B.PBℓ v μ)
      (d := Work.BoseFixB1B.PBd v μ) u
      (w := Submission.BoseGases.wSmall1Pair h (Work.BoseFixB1B.PBM v μ)
        (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBd v μ) u)]
  · rfl
  · intro x y hxy
    exact Work.BoseFixB1.wSmallPair_eq_zero_of_notMem_dlBox hM hℓ hd u hxy

theorem boxM2_sub_w1MassB_ge_of_windowDichotomy {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (h : Work.UBB.ScatSol v) (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1)
    (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) (C : ℝ) (hC : 1 ≤ C) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ u ∈ Work.SmallBoxSliding.goodSet (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBd v μ) μ,
        ¬ (Work.BoseFixB1B.PBW h μ u ≤ C * _root_.BoseGases.a v / μ) →
        (1 - 2 * Work.BoseFixB1B.PBΓ v μ) * Submission.BoseGases.g0w0Mass h
            * Work.SmallBoxSliding.chiMass (Work.BoseFixB1B.PBM v μ) (Work.BoseFixB1B.PBℓ v μ)
                (Work.BoseFixB1B.PBd v μ) u
          ≤ Work.BoseFixB1S.boxM2 (Work.BoseFixB1B.PBBV v μ u) (Work.BoseFixB1B.PBB v μ u)
              (Submission.BoseGases.wSmallPair (Work.BoseFixB1B.PBM v μ) (Work.BoseFixB1B.PBℓ v μ)
                (Work.BoseFixB1B.PBd v μ) u (Submission.BoseGases.g2 v h))
            - Work.BoseFixB1B.PBW h μ u := by
  -- ### The two thresholds: the window dichotomy and the geometric regime
  obtain ⟨εw, hεw0, hwd⟩ := windowShiftDichotomy h hv hv1 hvrad hR hv_supp hav C hC
  obtain ⟨εr, hεr0, hreg⟩ := Work.BoseFixB1.regime_sideAt_ge (v := v) hav hR
  refine ⟨min εw εr, lt_min hεw0 hεr0, ?_⟩
  intro μ hAdm u hu hnot
  have hμ0 : 0 < μ := hAdm.1
  have hAdmw : Work.BoseBoxFix.Adm v εw μ :=
    ⟨hμ0, le_trans hAdm.2.1 (min_le_left _ _), hAdm.2.2⟩
  have hAdmr : Work.BoseBoxFix.Adm v εr μ :=
    ⟨hμ0, le_trans hAdm.2.1 (min_le_right _ _), hAdm.2.2⟩
  -- ### The dichotomy: the first branch is excluded, so the shift bound (S) holds
  have hshift : ∀ z : EuclideanSpace ℝ (Fin 3), ‖z‖ ≤ R →
      (1 - 2 * Work.BoseFixB1B.PBΓ v μ)
          * Work.SmallBoxSliding.chiMass (Work.BoseFixB1B.PBM v μ) (Work.BoseFixB1B.PBℓ v μ)
              (Work.BoseFixB1B.PBd v μ) u
        ≤ ∫ x : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.chiSmallB
              (Work.BoseFixB1B.PBM v μ) (Work.BoseFixB1B.PBℓ v μ)
              (Work.BoseFixB1B.PBd v μ) u x
            * Submission.BoseGases.chiSmallB (Work.BoseFixB1B.PBM v μ)
              (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBd v μ) u (x - z) :=
    (hwd μ hAdmw u hu).resolve_left hnot
  -- ### The geometric gates
  obtain ⟨hR16, hRχ⟩ := hreg μ hμ0 hAdmr.2.1
  have hℓ : 0 < Work.BoseFixB1B.PBℓ v μ := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < Work.BoseFixB1B.PBd v μ := Work.BoseFixB1.adm_d_pos hAdm
  have hM : 1 ≤ Work.BoseFixB1B.PBM v μ := Work.BoseFixB1B.one_le_PBM v μ
  -- ### The mass-difference row `lm:w2>w1` at `θ = 2Γ`
  have hkey := Work.BoseFixB1S.boxM2SubBoxM1GeConvChiMass (v := v) (R := R)
    hv_supp hR hv hvrad hv1 h (M := Work.BoseFixB1B.PBM v μ) hM
    (ℓ := Work.BoseFixB1B.PBℓ v μ) (d := Work.BoseFixB1B.PBd v μ)
    (θ := 2 * Work.BoseFixB1B.PBΓ v μ) hℓ hd hR16 hRχ u hshift
  -- ### `boxM1 = w1MassB` at the sliding box, and the `abbrev` unfoldings
  rw [← PBW_eq_boxM1_dl (v := v) (h := h) (μ := μ) (u := u) hℓ hd hM] at hkey
  simpa only [Work.BoseFixB1B.PBBV, Work.BoseFixB1B.PBB] using hkey

end Work.BoseB1Cube
