import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBoxFock.AllDefs
import Submission.Work.BoseBoxFock.model_kafz_all
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.RB4boxDomFSAll_of_bridge` — FS §8's domination, `All` vocabulary

Design item 5 glue (D3), row 3: the `All`-vocabulary copy of
`Work.BoseBoxFock.RB4boxDomFS_of_bridge` (`BoseBoxFock/RB4boxDomFS_of_bridge.lean`).

`RB4boxDomFSAll` is the *existential-`Nmin`* form of FS §8 (`prop:Hamilton2ndQuant`) at the
concrete honest model `HonestBoxFam v h fc fu HM`, with `valFS` replaced by `valFSAll`: for
every family of honest mode data `HM` whose cube is large enough, and every admissible `μ`,
every low (`eq:aprioriPsi`) `n₊`-restricted box state `Φ` satisfies

  `(⨅_{ρ ≥ 0} valFSAll ρ)·‖Φ‖² ≤ wordB(Φ) + errKafz v R μ C·‖Φ‖²`.

The proof is the original's word for word, with two replacements:

* the **model floor** is `Work.BoseBoxFock.model_kafz_all` in place of the clean re-delivery
  `Clean.model_kafz` of `thm:Kafz`: the floor is an infimum of the window Rayleigh quotients of
  `KzOpFSAll`, which is exactly what `RB4boxDomAtAll` consumes (`valFS ≤ valFSAll` goes the
  *wrong* way for this step, so the `All` floor is genuinely needed);
* the **bounded-belowness** of `ρ ↦ valFSAll ρ` is `bddBelow_valFSAll_range_rho` (proved, from
  `valFS ≤ valFSAll` and `bddBelow_valFS_range_rho`), with the extra env fact
  `E.W1omega 0 = E.W1omega0` (the 11th conjunct of `EnvFactsAt`).

The `envFacts_uniform` half of the environment bundle is reused verbatim: the environment
facts do not mention `valFS` at all.  Nothing else changes — `box_to_model`'s conclusion is
about the model vector `Ψ`, so it is shared with the non-`All` route.

The statement is copied from `Submission/Work/BOSE_ALL_STATEMENTS.lean.txt` (item 5 glue).
-/

namespace Work.BoseBoxFock

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

open scoped Real Topology BigOperators
open MeasureTheory Filter Metric

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox
open Work.BoseBoxFix Work.BoseFixR

/-- **FS §8, `All` vocabulary**: `RB4boxDomFSAll` from FS's bridge `box_to_model` (BF3) and
the corrected model floor `model_kafz_all` (FS `thm:Kafz`). -/
theorem RB4boxDomFSAll_of_bridge (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R) (hav : 0 < _root_.BoseGases.a v)
    (fc fu : Work.BoseBoxFix.LowCut) (J : ℝ) (hB3 : Work.BoseBoxFix.NodeB3B v h R fc) :
    Work.BoseBoxFock.RB4boxDomFSAll v h R J fc fu := by
  classical
  -- the three thresholds and constants
  obtain ⟨Nmin, εb, Cb, hεb, hCb, hb⟩ :=
    box_to_model v h hv hv1 hvrad hR hv_supp hav fc fu J hB3
  -- the environment facts and the *`All`* model floor (FS `thm:Kafz` with the label-`0` row)
  obtain ⟨⟨εw, Cw, hεw, hCw, hw⟩, ⟨εm, Cm, hεm, hCm, hm⟩⟩ :=
    And.intro (Clean.envFacts_uniform v h hv hv1 hvrad hR hv_supp hav fc fu)
      (model_kafz_all v h hv hv1 hvrad hR hv_supp hav fc fu)
  refine ⟨Nmin, ?_⟩
  intro HM hN
  refine ⟨min (min εb εm) εw, Cb + Cm, lt_min (lt_min hεb hεm) hεw, add_nonneg hCb hCm, ?_⟩
  intro μ hAdm hJKB n Φ hn hlow hspec
  have hadm1 : Work.BoseBoxFix.Adm v (min (min εb εm) εw) μ := hAdm
  have hAdmb : Work.BoseBoxFix.Adm v εb μ :=
    ⟨hAdm.1, le_trans hAdm.2.1 (le_trans (min_le_left _ _) (min_le_left _ _)), hAdm.2.2⟩
  have hAdmm : Work.BoseBoxFix.Adm v εm μ :=
    ⟨hAdm.1, le_trans hAdm.2.1 (le_trans (min_le_left _ _) (min_le_right _ _)), hAdm.2.2⟩
  have hAdmw : Work.BoseBoxFix.Adm v εw μ :=
    ⟨hAdm.1, le_trans hAdm.2.1 (min_le_right _ _), hAdm.2.2⟩
  -- the environment facts (for the bounded-belowness of `ρ ↦ valFSAll ρ`)
  obtain ⟨hell0, hell, -, -, -, -, -, hWωabs, hWω0, -, hωval, -, -, -, -, -⟩ :=
    hw HM μ hAdmw
  -- the bounded-belowness of `ρ ↦ valFSAll ρ`
  have hbdd : BddBelow (Set.range (fun ρ : {ρ : ℝ // 0 ≤ ρ} =>
      (HonestBoxFam v h fc fu HM μ).valFSAll ρ.1)) := by
    refine bddBelow_valFSAll_range_rho v h fc fu HM μ (Cw * BoseGases.a v)
      (∑ s ∈ Work.BoseB7.excited (Lab (HM μ).N),
        (HonestBoxFam v h fc fu HM μ).E.hatChiSq s ^ 2)
      hAdm.1 hav hWω0 hωval hWωabs (Finset.sum_nonneg fun s _ => sq_nonneg _) le_rfl
  have hν : 0 ≤ Work.BoseBoxFix.normB v μ n Φ := integral_nonneg fun x => sq_nonneg _
  rcases lt_or_eq_of_le hν with hpos | hzero
  · -- ## the main case: the bridge's window state, then the floor at it
    obtain ⟨Ψ, hΨne, hΨwin, hΨbnd⟩ := hb HM hN μ hAdmb hJKB n Φ hn hpos hlow hspec
    have hfl := hm HM μ hAdmm n hn Ψ hΨne hΨwin
    set ν : ℝ := Work.BoseBoxFix.normB v μ n Φ with hνdef
    set bb : ℝ := Work.BoseB4.bomb (HM μ).m Ψ Ψ with hbbdef
    have hbb0 : 0 ≤ bb := Work.BoseB4.Bomb_self_nonneg Ψ
    have hbbpos : 0 < bb := by
      rcases lt_or_eq_of_le hbb0 with h' | h'
      · exact h'
      · exfalso
        exact hΨne (Work.BoseB4.Bomb_self_eq_zero h'.symm)
    -- the ratio form, from the two bounds at `Ψ`
    have hAle : (⨅ (ρ : {ρ : ℝ // 0 ≤ ρ}), (HonestBoxFam v h fc fu HM μ).valFSAll ρ.1)
        - Work.BoseFixR.errKafz v R μ Cm
        ≤ Work.BoseBoxFix.wordB v h μ n Φ / ν + Work.BoseFixR.errKafz v R μ Cb := by
      refine le_of_mul_le_mul_right ?_ hbbpos
      rw [hbbdef]
      exact le_trans hfl hΨbnd
    -- multiply by `ν > 0`
    have hAν : (⨅ (ρ : {ρ : ℝ // 0 ≤ ρ}), (HonestBoxFam v h fc fu HM μ).valFSAll ρ.1) * ν
        ≤ Work.BoseBoxFix.wordB v h μ n Φ + Work.BoseFixR.errKafz v R μ (Cb + Cm) * ν := by
      have h1 := mul_le_mul_of_nonneg_right hAle hν
      have h2 : (Work.BoseBoxFix.wordB v h μ n Φ / ν) * ν = Work.BoseBoxFix.wordB v h μ n Φ := by
        rw [div_mul_cancel₀ _ (ne_of_gt hpos)]
      have h2b : (Work.BoseBoxFix.wordB v h μ n Φ / ν + Work.BoseFixR.errKafz v R μ Cb) * ν
          = (Work.BoseBoxFix.wordB v h μ n Φ / ν) * ν + Work.BoseFixR.errKafz v R μ Cb * ν := by
        ring
      have h3 : (⨅ (ρ : {ρ : ℝ // 0 ≤ ρ}), (HonestBoxFam v h fc fu HM μ).valFSAll ρ.1) * ν
          - Work.BoseFixR.errKafz v R μ Cm * ν
          = ((⨅ (ρ : {ρ : ℝ // 0 ≤ ρ}), (HonestBoxFam v h fc fu HM μ).valFSAll ρ.1)
              - Work.BoseFixR.errKafz v R μ Cm) * ν := by ring
      have h4 : Work.BoseBoxFix.wordB v h μ n Φ
            + Work.BoseFixR.errKafz v R μ (Cb + Cm) * ν
          = (Work.BoseBoxFix.wordB v h μ n Φ + Work.BoseFixR.errKafz v R μ Cb * ν)
            + Work.BoseFixR.errKafz v R μ Cm * ν := by
        rw [errKafz_add]; ring
      linarith [h1, h2, h2b, h3, h4]
    -- the statement's left-hand side is the same infimum
    rw [← iInf_mul_const_eq (fun ρ : {ρ : ℝ // 0 ≤ ρ} =>
        (HonestBoxFam v h fc fu HM μ).valFSAll ρ.1) hν hbdd]
    exact hAν
  · -- ## the degenerate case: the state vanishes on the box, so `wordB = 0`
    have hz : Work.BoseBoxFix.normB v μ n Φ = 0 := hzero.symm
    have hℓ : 0 < Work.BoseBox.sideAt μ (BoseGases.a v) :=
      Work.BoseBox.sideAt_pos hAdm.1 hav
    have hword : Work.BoseBoxFix.wordB v h μ n Φ = 0 :=
      wordB_eq_zero_of_normB_eq_zero hℓ hz
    haveI : Nonempty {ρ : ℝ // 0 ≤ ρ} := ⟨⟨0, le_rfl⟩⟩
    rw [hz, hword]
    simp

end Work.BoseBoxFock

namespace Work.BoseAllGlue

/-- The `Work.BoseAllGlue` name of `Work.BoseBoxFock.RB4boxDomFSAll_of_bridge`. -/
alias RB4boxDomFSAll_of_bridge := Work.BoseBoxFock.RB4boxDomFSAll_of_bridge

end Work.BoseAllGlue
