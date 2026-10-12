import ChallengeDeps
import Mathlib.Algebra.Order.Ring.Star
import Submission.Work.BoseSWE.boxMass_ge_clipMass
import Submission.Work.BoseSWE.massiveBulkRow
import Submission.Work.BoseSWE.massiveDefect
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseSWE

/-- **Node N2′ of the `BoseSWE` route**: a *massive* box (`χ_m ≥ d^108·(ℓd)³`) is `Regular`.
Recipe (see `Submission/Work/BoseSWE/BRIEF.md` §3): (i) the L²-form autocorrelation defect
(`∫χ² − ∫χ(x)χ(x−z) ≤ (‖z‖²/2)∫‖∇χ‖²`, from the PROVED bricks
`Work.BoseB1Cube.shiftDiff_sq_pointwise`/`autocorr_sub_le` — NOT the `sorry`-tainted
`autocorr_sub_le_sq`); (ii) the gradient bound `‖∇χ_B‖₂²/χ_m ≤ C(ℓ⁻²r^{-1/2} + (ℓd)⁻²r^{-1/48})`,
`r = χ_m/(ℓd)³ ≥ d^108`, via Glaeser `|∇A|² ≤ 2‖D²A‖A` for the `C^∞` bump `A = chiScale ℓ` and
Hölder for the cos⁴⁸ cube factor; (iii) the PROVED
`Work.BoseB1Cube.w1MassB_ge_of_autocorr` + `boxM2_sub_boxM1_ge_of_autocorr` at `δ = 1/50`, with
`∫g₀ = 8πa` (the bricks' side hypotheses `R ≤ ℓd/16`, `R ≤ ℓ/16` come from the existential `ε₀`,
via `Work.BoseFixGlue.Pot.ellB_ge`-type facts); (iv) the clipping geometry
`bV ≥ (min ℓ (ℓd) (μ^{-1/3}))³` giving `μ·bV ≥ X^{−148} ≥ 1000`. -/
theorem massiveRegularNode_holds {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) : Work.BoseSWE.MassiveRegularNode v h := by
  classical
  -- ## the five thresholds
  obtain ⟨εreg, hεreg, hreg⟩ := Work.BoseFixB1.regime_sideAt_ge (v := v) hav hR
  obtain ⟨εadm, hεadm, hadm⟩ :=
    Work.BoseFixB1S.admGoodSetRegime2 (v := v) h hv hv1 hvrad hR hv_supp hav
  obtain ⟨εdef, hεdef, hdef⟩ := massiveDefect (v := v) h hv hv1 hvrad hR hv_supp hav
  obtain ⟨εclip, hεclip, hclip⟩ := boxMass_ge_clipMass (v := v) hav
  obtain ⟨εbulk, hεbulk, hbulk⟩ :=
    massiveBulkRow (v := v) h hv hv1 hvrad hR hv_supp hav ⟨εdef, hεdef, hdef⟩
  refine ⟨min (min εreg εadm) (min εclip (min εbulk εdef)),
    lt_min (lt_min hεreg hεadm) (lt_min hεclip (lt_min hεbulk hεdef)), ?_⟩
  intro μ hAdm u hu hmass
  -- ## the monotone reductions of `Adm`
  have hAdmR : Work.BoseBoxFix.Adm v εreg μ :=
    Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_left _ _) (min_le_left _ _))
  have hAdmA : Work.BoseBoxFix.Adm v εadm μ :=
    Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_left _ _) (min_le_right _ _))
  have hAdmC : Work.BoseBoxFix.Adm v εclip μ :=
    Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_right _ _) (min_le_left _ _))
  have hAdmB : Work.BoseBoxFix.Adm v εbulk μ :=
    Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hAdmD : Work.BoseBoxFix.Adm v εdef μ :=
    Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  -- ## the regime at the sliding box
  obtain ⟨h16ℓ, h16ℓd, hd0, hd1, hbV0, hbVle, hbVs, hmuV⟩ := hadm μ hAdmA u hu
  have hμ : 0 < μ := hAdm.1
  have hℓ : 0 < Work.BoseFixB1.bSide v μ := Work.BoseFixB1.adm_ell_pos (v := v) hAdm
  have hd : 0 < Work.BoseFixB1.bD v μ := Work.BoseFixB1.adm_d_pos (v := v) hAdm
  have hM1 : 1 ≤ Work.BoseFixB1.bM v μ := by
    rw [Work.BoseFixB1.bM, Work.BoseFixB1.M_eq_mValue, Work.BoseBox.mValue]
    norm_num
  have hR16 : R ≤ Work.BoseFixB1.bSide v μ * Work.BoseFixB1.bD v μ / 16 :=
    (hreg μ hμ (hAdmR.2.1)).1
  have hRχ : R ≤ Work.BoseFixB1.bSide v μ * Submission.BoseGases.chiR0 :=
    (hreg μ hμ (hAdmR.2.1)).2
  -- ## the massive hypothesis is non-vacuous
  have hχpos : 0 < Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ)
      (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u := by
    refine lt_of_lt_of_le ?_ hmass
    positivity
  -- ## the pointwise defect (at loss 1/50) on this box
  have hshift : ∀ z : EuclideanSpace ℝ (Fin 3), ‖z‖ ≤ R →
      (49 / 50) * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ)
          (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u
        ≤ ∫ x : EuclideanSpace ℝ (Fin 3),
            Submission.BoseGases.chiSmallB (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                (Work.BoseFixB1.bD v μ) u x
              * Submission.BoseGases.chiSmallB (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                (Work.BoseFixB1.bD v μ) u (x - z) :=
    hdef μ hAdmD u hu hmass
  refine ⟨?_, ?_, ?_⟩
  · -- ## conjunct 1: the `w₁`-mass row
    exact hbulk μ hAdmB u hu hmass
  · -- ## conjunct 2: FS `lm:w2>w1` via `boxM2SubBoxM1GeConvChiMass`
    have hshift' : ∀ z : EuclideanSpace ℝ (Fin 3), ‖z‖ ≤ R →
        (1 - (1 / 50 : ℝ)) * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ)
            (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u
          ≤ ∫ x : EuclideanSpace ℝ (Fin 3),
              Submission.BoseGases.chiSmallB (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                  (Work.BoseFixB1.bD v μ) u x
                * Submission.BoseGases.chiSmallB (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                  (Work.BoseFixB1.bD v μ) u (x - z) := by
      intro z hz
      simpa only [show (1 : ℝ) - 1 / 50 = 49 / 50 by norm_num] using hshift z hz
    have hbox := Work.BoseFixB1S.boxM2SubBoxM1GeConvChiMass (v := v) (θ := 1 / 50)
      hv_supp hR hv hvrad hv1 h
      hM1 hℓ hd hR16 hRχ u hshift'
    have hM1eq : Work.BoseFixB1S.boxM1 (Work.BoseFixB1.bSide v μ)
        (Submission.BoseGases.dlBox (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u)
        (Submission.BoseGases.wSmall1Pair h (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
          (Work.BoseFixB1.bD v μ) u) = Work.BoseFixB1.bW v h μ u :=
      Work.AprioriCount.boxM1_eq_w1MassB (v := v) (h := h) (M := Work.BoseFixB1.bM v μ) hM1 hℓ hd u
    rw [Work.BoseFixB1.bM2, Work.BoseFixB1.bV, Work.BoseFixB1.bA, ← hM1eq]
    have hc : (1 : ℝ) - 1 / 50 = 49 / 50 := by norm_num
    rw [hc] at hbox
    exact hbox
  · -- ## conjunct 3: the clipping geometry
    exact hclip μ hAdmC u hu hχpos

/-! ## How the recipe is realised here (bricks proved in this directory)

* `Work.BoseSWE.glaeserPointwise` — the pointwise Glaeser inequality `‖∇f x‖² ≤ 2N f x` for a
  nonnegative `C²` function with `‖D²f‖ ≤ N` (proved on the segment `s ↦ f(x − s∇f(x)/‖∇f x‖)`);
* `Work.BoseSWE.chiScaleGlaeser` — its instantiation at the `ℓ`-scale bump `chiScale ℓ`;
* `Work.BoseSWE.chiSmallGradHolder` — the pointwise Hölder bound for the cos⁴⁸ cube factor;
* those two give `Work.BoseSWE.massiveDefect`: the `L²`-defect
  `Work.BoseB1Cube.chiMass_sub_autoCorr_le` plus the sharp gradient bound
  `∫‖∇χ_B‖² ≤ 2‖D²chi‖∞ℓ⁻²χ_m^{1/2}(ℓd)^{3/2} + C_c²(ℓd)⁻²χ_m^{47/48}ℓ^{1/16}` and the massive
  threshold `d^{108}(ℓd)³ ≤ χ_m` yield `(49/50)χ_m ≤ ∫χ_B(x)χ_B(x−z)` for `‖z‖ ≤ R`;
* `Work.BoseSWE.massiveBulkRow` — the first mass row from that defect (`w1MassB_eq_autocorr_gen`,
  `wSmall1Pair_denom_bounds`, `∫g₀ = 8πa`);
* conjunct 2 is the PROVED `Work.BoseFixB1S.boxM2SubBoxM1GeConvChiMass` (FS `lm:w2>w1`) fed by
  the same defect, with `Work.AprioriCount.boxM1_eq_w1MassB`;
* `Work.BoseSWE.boxMass_ge_clipMass` — the clipping geometry (conjunct 3).
-/

end Work.BoseSWE
