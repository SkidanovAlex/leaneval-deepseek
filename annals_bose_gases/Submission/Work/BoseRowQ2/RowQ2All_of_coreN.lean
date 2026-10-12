import ChallengeDeps
import Submission.Work.BoseRowQ2.RowsN
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowQ2.RowQ2All_of_coreN` — the assembly of row 3 via the `NH` core

**Live again** (lead's NH ruling 2026-10-08, `LEAD_RULING_NH.md`): `RowQ2AllRegimeN` follows from
the core `RowQ2AllCoreN` (`RowsN.lean`), at the cube size and threshold the core produces.  The
earlier "SUPERSEDED / the core is false" note is **retracted**: it rested on the flawed step
`⟨T.N⟩ = 1` for the one-particle witness (in fact `⟨T.N⟩ = ‖u‖²`, see `RowsN.lean`'s header).

The budget (lead's `LEAD_RULING_NH.md` §2):

* `2ρŴ₁ω(0)⟨Gop⟩ ≤ 2ρŴ₁ω(0)[(1+ε)⟨Σ_k a_k†a_k⟩ + (1+1/ε)(C₁/κ_lat)²⟨T.N⟩]` (`GchiAtN`),
* the second summand is `≤ (b/800)ℓ⁻²⟨T.N⟩` (`ArithAt2` times `⟨T.N⟩ ≥ 0`),
* `2ρ(1+ε)Ŵ₁ω(0)⟨Σ_k a_k†a_k⟩ ≤ ⟨Q₂^ex,all⟩ + (b/800)ℓ⁻²⟨n₊⟩ + (b/800)ε_T(dℓ)⁻²⟨NH⟩`
  (`MainAtN`, at the *current* `NH`),
* and `(b/800) + (b/800) = b/400` is exactly the `ℓ⁻²` half of
  `gapOpT = ℓ⁻²n₊ + ε_T(dℓ)⁻²n₊^H`, the `NH` half being `b/800 ≤ b/400`.

The *mask* assembly `Work.BoseRowQ2.RowQ2AllRegimeN_of_coreMask` (`MaskRow.lean`) is kept as a
record of the alternative route (it is unconditional, but it needs the *widened* gap word).
-/

noncomputable section

open scoped BigOperators Pointwise

namespace Work.BoseRowQ2

open Work.BoseB7 Work.BoseB7A Work.BoseFixR Work.BoseBoxFock Work.BoseBoxFix Work.UBB
open Work.BoseGateFS

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- **The corrected row 3 in the dilute régime, at a cube size and threshold the
row produces.** -/
theorem RowQ2AllRegimeN_of_coreN {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v}
    {fc fu : LowCut} {R εg : ℝ} (hεg1 : εg ≤ 1)
    (hav : 0 < _root_.BoseGases.a v)
    (hw0 : ∀ (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ), 0 < μ →
      μ * (_root_.BoseGases.a v) ^ 3 ≤ εg →
      0 ≤ (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0)
    (hcore : RowQ2AllCoreN (h := h) (fc := fc) (fu := fu) R εg) :
    ∃ Ng : ℝ → ℕ, ∃ εg' : ℝ, 0 < εg' ∧ εg' ≤ εg ∧
      RowQ2AllRegimeN (h := h) (fc := fc) (fu := fu) Ng R εg' := by
  obtain ⟨Ng, εg', hpos, hle, C₁, hC₁, κ_lat, ε, hκpos, hεpos, hAr, hAr2, hG, hM⟩ := hcore
  have hεg1' : εg' ≤ 1 := le_trans hle hεg1
  refine ⟨Ng, εg', hpos, hle, ?_⟩
  intro HM hNg μ hμ hε ρ hρ Ψ
  have hArith' : ArithAt (v := v) (h := h) (fc := fc) (fu := fu) (96 / Real.pi) HM μ ρ (ε μ) :=
    hAr hεg1' HM hNg μ hμ hε ρ hρ
  have hArith2' : ArithAt2 (v := v) (h := h) (fc := fc) (fu := fu) C₁ (κ_lat μ) HM μ ρ (ε μ) :=
    hAr2 hεg1' HM hNg μ hμ hε ρ hρ
  have hG' : GchiAtN (v := v) (h := h) (fc := fc) (fu := fu) C₁ (κ_lat μ) HM μ (ε μ) :=
    hG hεg1' HM hNg μ hμ hε ρ hρ
  have hM' : MainAtN (v := v) (h := h) (fc := fc) (fu := fu) HM μ ρ (ε μ) :=
    hM hεg1' HM hNg μ hμ hε ρ hρ
  have hw : 0 ≤ (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0 :=
    hw0 HM μ hμ (le_trans hε hle)
  have hpos2 : 0 ≤ 2 * ρ * (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0 :=
    mul_nonneg (mul_nonneg (by norm_num) hρ.1) hw
  have hNnn : 0 ≤ (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
      (Work.BoseRowsFS.honT v h fc fu HM μ).N :=
    (Work.BoseRowsFS.honT v h fc fu HM μ).N_nonneg Ψ
  have hNHnn : 0 ≤ (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
      (Work.BoseRowsFS.honT v h fc fu HM μ).NH :=
    (Work.BoseRowsFS.honT v h fc fu HM μ).NH_nonneg Ψ
  -- the `GchiAtN` row, weighted
  have hkey := mul_le_mul_of_nonneg_left (hG' Ψ) hpos2
  -- the second correction, inside the freed `b/800` of the `ℓ⁻²` slot
  have hcorr2 := mul_le_mul_of_nonneg_right hArith2' hNnn
  have hb : (0 : ℝ) < (Work.BoseRowsFS.honE v h fc fu HM μ).b := by
    rw [Work.BoseRowsFS.honE_b]; norm_num
  have hb800 : (0 : ℝ) ≤ (Work.BoseRowsFS.honE v h fc fu HM μ).b / 800 := by positivity
  have hb400 : (0 : ℝ) ≤ (Work.BoseRowsFS.honE v h fc fu HM μ).b / 400 := by positivity
  have heT0 : (0 : ℝ) ≤ (Work.BoseRowsFS.honE v h fc fu HM μ).eT := by
    rw [Work.BoseRowsFS.honE_eT_eq]
    exact Real.rpow_nonneg (le_of_lt (mul_pos hμ (pow_pos hav 3))) _
  have hdl0 : (0 : ℝ) ≤ ((Work.BoseRowsFS.honE v h fc fu HM μ).d
      * (Work.BoseRowsFS.honE v h fc fu HM μ).ell) ^ (-(2 : ℝ)) :=
    rpow_neg_two_nonneg _
  have hl0 : (0 : ℝ) ≤ (Work.BoseRowsFS.honE v h fc fu HM μ).ell ^ (-(2 : ℝ)) :=
    rpow_neg_two_nonneg _
  -- the gap word, spelled at the honest environment
  have hgap : (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
        ((Work.BoseRowsFS.honT v h fc fu HM μ).gapOpT
          (KzEnvAt (Work.BoseRowsFS.honE v h fc fu HM μ) ρ))
      = (Work.BoseRowsFS.honE v h fc fu HM μ).ell ^ (-(2 : ℝ))
          * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
              (Work.BoseRowsFS.honT v h fc fu HM μ).N
        + ((Work.BoseRowsFS.honE v h fc fu HM μ).eT
            * ((Work.BoseRowsFS.honE v h fc fu HM μ).d
                * (Work.BoseRowsFS.honE v h fc fu HM μ).ell) ^ (-(2 : ℝ)))
          * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
              (Work.BoseRowsFS.honT v h fc fu HM μ).NH := by
    rw [TildeData.qw_gapOpT]
    rfl
  rw [hgap]
  calc 2 * ρ * (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0
        * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
            ((Work.BoseRowsFS.honT v h fc fu HM μ).Gop
              (Work.BoseRowsFS.honE v h fc fu HM μ))
      ≤ 2 * ρ * (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0
        * ((1 + ε μ) * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
              (Work.BoseRowsFS.honF v h fc fu HM μ).allNumOp
            + (1 + 1 / (ε μ)) * (C₁ / κ_lat μ) ^ 2
              * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
                  (Work.BoseRowsFS.honT v h fc fu HM μ).N) := hkey
    _ = 2 * ρ * (1 + ε μ) * (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0
          * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
              (Work.BoseRowsFS.honF v h fc fu HM μ).allNumOp
        + 2 * ρ * (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0 * (1 + 1 / (ε μ))
          * (C₁ / κ_lat μ) ^ 2
          * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
              (Work.BoseRowsFS.honT v h fc fu HM μ).N := by ring
    _ ≤ ((Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
            ((Work.BoseRowsFS.honF v h fc fu HM μ).Q2exAll
              (KzEnvAt (Work.BoseRowsFS.honE v h fc fu HM μ) ρ))
          + ((Work.BoseRowsFS.honE v h fc fu HM μ).b / 800)
              * (Work.BoseRowsFS.honE v h fc fu HM μ).ell ^ (-(2 : ℝ))
              * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
                  (Work.BoseRowsFS.honT v h fc fu HM μ).N
          + ((Work.BoseRowsFS.honE v h fc fu HM μ).b / 800)
              * ((Work.BoseRowsFS.honE v h fc fu HM μ).eT
                  * ((Work.BoseRowsFS.honE v h fc fu HM μ).d
                      * (Work.BoseRowsFS.honE v h fc fu HM μ).ell) ^ (-(2 : ℝ)))
              * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
                  (Work.BoseRowsFS.honT v h fc fu HM μ).NH)
        + ((Work.BoseRowsFS.honE v h fc fu HM μ).b / 800)
            * (Work.BoseRowsFS.honE v h fc fu HM μ).ell ^ (-(2 : ℝ))
            * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
                (Work.BoseRowsFS.honT v h fc fu HM μ).N :=
        add_le_add (hM' Ψ) hcorr2
    _ = (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
            ((Work.BoseRowsFS.honF v h fc fu HM μ).Q2exAll
              (KzEnvAt (Work.BoseRowsFS.honE v h fc fu HM μ) ρ))
          + ((Work.BoseRowsFS.honE v h fc fu HM μ).b / 400)
              * (Work.BoseRowsFS.honE v h fc fu HM μ).ell ^ (-(2 : ℝ))
              * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
                  (Work.BoseRowsFS.honT v h fc fu HM μ).N
          + ((Work.BoseRowsFS.honE v h fc fu HM μ).b / 800)
              * ((Work.BoseRowsFS.honE v h fc fu HM μ).eT
                  * ((Work.BoseRowsFS.honE v h fc fu HM μ).d
                      * (Work.BoseRowsFS.honE v h fc fu HM μ).ell) ^ (-(2 : ℝ)))
              * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
                  (Work.BoseRowsFS.honT v h fc fu HM μ).NH := by ring
    _ ≤ (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
            ((Work.BoseRowsFS.honF v h fc fu HM μ).Q2exAll
              (KzEnvAt (Work.BoseRowsFS.honE v h fc fu HM μ) ρ))
          + ((Work.BoseRowsFS.honE v h fc fu HM μ).b / 400)
              * ((Work.BoseRowsFS.honE v h fc fu HM μ).ell ^ (-(2 : ℝ))
                  * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
                      (Work.BoseRowsFS.honT v h fc fu HM μ).N
                + ((Work.BoseRowsFS.honE v h fc fu HM μ).eT
                    * ((Work.BoseRowsFS.honE v h fc fu HM μ).d
                        * (Work.BoseRowsFS.honE v h fc fu HM μ).ell) ^ (-(2 : ℝ)))
                  * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
                      (Work.BoseRowsFS.honT v h fc fu HM μ).NH) := by
        have h1 : 0 ≤ ((Work.BoseRowsFS.honE v h fc fu HM μ).b / 800)
            * (((Work.BoseRowsFS.honE v h fc fu HM μ).eT
                * ((Work.BoseRowsFS.honE v h fc fu HM μ).d
                    * (Work.BoseRowsFS.honE v h fc fu HM μ).ell) ^ (-(2 : ℝ))))
            * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
                (Work.BoseRowsFS.honT v h fc fu HM μ).NH :=
          mul_nonneg (mul_nonneg hb800 (mul_nonneg heT0 hdl0)) hNHnn
        nlinarith [h1, mul_nonneg hb800 hNnn, mul_nonneg hb800 hNHnn,
          mul_nonneg hl0 hNnn, mul_nonneg (mul_nonneg heT0 hdl0) hNHnn,
          mul_nonneg hb400 (mul_nonneg hl0 hNnn), hNnn, hNHnn, hb800, hb400]

end Work.BoseRowQ2
