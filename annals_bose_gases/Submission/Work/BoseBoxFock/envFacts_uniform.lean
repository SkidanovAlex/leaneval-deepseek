import ChallengeDeps
import Submission.Work.BoseBoxFock.honestEnvNumeric
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseBoxFock/envFacts_uniform.lean`

**The environment bundle of the honest family, uniform in the mode data.**

`Work.BoseBoxFock.EnvFactsAt` collects the numerical facts of the honest box
environment at a fixed `μ`: positivity and size of the box side (`E.ell`),
the diluteness rows (`1 ≤ μℓ³`, `ℓ⁻³ ≤ Cμ`, `𝓜 ≤ Cμℓ³`), the scattering-length
bounds on `Ŵ₁`, `Ŵ₁ω` and `Ŵ₁ω(0)`, the sign rows `0 ≤ Ŵ₁ω(0)`,
`0 ≤ cHCF E (8π a)`, and the parity rows.

`Work.BoseBoxFock.honestEnvNumeric` proves

    ∃ ε₀ C, 0 < ε₀ ∧ 0 ≤ C ∧ ∀ μ, Adm v ε₀ μ → EnvFactsAt v h fc fu HM μ C

with the mode data `HM` a *parameter*: `C` is allowed to depend on `HM`.  The
consumer (`Work.BoseBoxFock.errKafz_dominates`, and through it the §9–§11
assembly) needs the *same* `ε₀, C` to work for **every** honest mode family
`HM : ∀ μ, HonestModes v μ` at once, since the mode data is chosen inside the
proof of the final theorem and must not influence the constants.  This is that
statement, and the whole point of the file is that the constants produced here,

    `ε₀ = min ε 1`  (from `WindowRegime`, which is independent of `HM`),
    `C   = max 1 (16π)`,

are *explicit*: nothing in the bound ever sees `HM` except through the index
type `Lab (HM μ).N` of the rows that are universally quantified over the modes.

The proof is the assembly of `honestEnvNumeric` with `HM` introduced inside the
existential — the one-per-row helper lemmas there (`honestFam_W1_abs_le`,
`honestFam_W1omega_abs_le`, `honestFam_W1omega0_le`, `honestFam_bigM_le`,
`honestFam_ell_inv_le`, `honestEnvFam_ell_pos`, `honestEnvFam_parity`,
`cHCF_nonneg`, `honestEnvFam_W1omega0_nonneg`) all take `HM` as a parameter and
produce constants (`16π`, `1`) that do not mention it.
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory

namespace Work.BoseBoxFock

set_option linter.unusedVariables false

/-- **The environment facts of the honest family, uniformly in the mode data.**

There are `ε₀ > 0` and `C ≥ 0`, depending only on the interaction `v` (and the
low cut-offs `fc`, `fu`), such that for *every* honest mode family
`HM : ∀ μ, HonestModes v μ` and every admissible chemical potential
`μ` (`Adm v ε₀ μ`), the bundle `EnvFactsAt v h fc fu HM μ C` holds. -/
theorem envFacts_uniform (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R) (hav : 0 < BoseGases.a v)
    (fc fu : Work.BoseBoxFix.LowCut) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
      ∀ (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ) (μ : ℝ),
        Work.BoseBoxFix.Adm v ε₀ μ → EnvFactsAt v h fc fu HM μ C := by
  obtain ⟨ε, hεpos, hε⟩ := Work.BoseFixR.WindowRegime h hv hv1 hvrad hR hv_supp hav
  refine ⟨min ε 1, max 1 (16 * Real.pi), lt_min hεpos one_pos,
    le_trans zero_le_one (le_max_left 1 (16 * Real.pi)), ?_⟩
  intro HM μ hAdm
  obtain ⟨hμ, htε, hOK⟩ := hAdm
  have hAdmε : Work.BoseBoxFix.Adm v ε μ := ⟨hμ, le_trans htε (min_le_left ε 1), hOK⟩
  obtain ⟨hRℓ, h157, -, -⟩ := hε μ hAdmε
  have ht1 : μ * BoseGases.a v ^ 3 ≤ 1 := le_trans htε (min_le_right ε 1)
  have hℓpos : 0 < Work.BoseBox.sideAt μ (BoseGases.a v) := by
    have hh := honestEnvFam_ell_pos v h fc fu HM hμ hav
    rwa [show (HonestBoxFam v h fc fu HM μ).E.ell = Work.BoseBox.sideAt μ (BoseGases.a v)
      from rfl] at hh
  have hellpos : 0 < (HonestBoxFam v h fc fu HM μ).E.ell :=
    honestEnvFam_ell_pos v h fc fu HM hμ hav
  have h157' : (1 : ℝ) ≤ μ * Work.BoseBox.sideAt μ (BoseGases.a v) ^ 3 := by linarith
  have hW0 : 0 ≤ (HonestBoxFam v h fc fu HM μ).E.W1omega0 :=
    honestEnvFam_W1omega0_nonneg v h hR hv hvrad hv_supp fc fu HM μ
  obtain ⟨hτ, hχ, hW1p, hWωp⟩ := honestEnvFam_parity v h fc fu HM μ
  refine ⟨hellpos, rfl, rfl, ?_, ?_, ?_, ?_, ?_, hW0, ?_, ?_, ?_, hW1p, hWωp, hτ, hχ⟩
  · -- `1 ≤ μℓ³`
    rw [show (HonestBoxFam v h fc fu HM μ).E.ell = Work.BoseBox.sideAt μ (BoseGases.a v)
      from rfl]
    linarith
  · -- `ℓ^{-3} ≤ Cμ`
    exact le_trans (honestFam_ell_inv_le v h fc fu HM hμ hav h157')
      (le_mul_of_one_le_left hμ.le (le_max_left 1 (16 * Real.pi)))
  · -- `𝓜 ≤ Cμℓ³`
    refine le_trans (honestFam_bigM_le v h fc fu HM hμ hav ht1) ?_
    exact mul_le_mul_of_nonneg_right
      (le_mul_of_one_le_left hμ.le (le_max_left 1 (16 * Real.pi))) (pow_nonneg hellpos.le 3)
  · -- `|Ŵ₁(k)| ≤ Ca`
    intro k
    exact le_trans (honestFam_W1_abs_le v h hv hvrad hR hv_supp hav fc fu HM hRℓ hℓpos k)
      (mul_le_mul_of_nonneg_right (le_max_right 1 (16 * Real.pi)) hav.le)
  · -- `|Ŵ₁ω(k)| ≤ Ca`
    intro k
    exact le_trans (honestFam_W1omega_abs_le v h hv hvrad hR hv_supp hav fc fu HM hRℓ hℓpos k)
      (mul_le_mul_of_nonneg_right (le_max_right 1 (16 * Real.pi)) hav.le)
  · -- `Ŵ₁ω(0) ≤ Ca`
    exact le_trans (honestFam_W1omega0_le v h hv hvrad hR hv_supp hav fc fu HM hRℓ hℓpos)
      (mul_le_mul_of_nonneg_right (le_max_right 1 (16 * Real.pi)) hav.le)
  · -- `Ŵ₁ω(0) = Ŵ₁ω(0)` (the two definitions of the zero mode)
    exact honestEnvFam_W1omega_zero_eq v h fc fu HM μ
  · -- `0 ≤ cHCF E (8π·(a v))`
    exact cHCF_nonneg (HonestBoxFam v h fc fu HM μ).E v hellpos hW0 hav

end Work.BoseBoxFock
