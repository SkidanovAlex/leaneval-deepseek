import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBoxFock.box_to_model
import Submission.Work.BoseBoxFock.cleanFloorAndEnv
import Submission.Work.BoseKinLoc.Sector.boxFormB_eq_zero_of_eq_zero_on_abox
import Submission.Work.BoseKinLoc.Sector.eq_zero_on_abox_of_sqNormB_eq_zero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.RB4boxDomFS_of_bridge` — FS §8's domination at the honest family

`RB4boxDomFS` is the *existential-`Nmin`* form of FS §8 (`prop:Hamilton2ndQuant`) at the
concrete honest model `HonestBoxFam v h fc fu HM`: for every family of honest mode data `HM`
whose cube is large enough, and every admissible `μ`, every low (`eq:aprioriPsi`)
`n₊`-restricted box state `Φ` satisfies

  `(⨅_{ρ ≥ 0} valFS ρ)·‖Φ‖² ≤ wordB(Φ) + errKafz v R μ C·‖Φ‖²`.

## The proof (two ingredients, exactly as the design `BOX_TO_MODEL_ROUTE.md` §1/§2 prescribes)

* **the bridge** `box_to_model` (FS §8, node BF3): for every such `Φ` there is a *model*
  window state `Ψ ≠ 0` with `⟨Ψ, H2ndHon Ψ⟩ ≤ (wordB/normB + errKafz C_b)·⟨Ψ, Ψ⟩`
  (that is `prop:Hamilton2ndQuant` in the form the assembly consumes: the box energy of `Φ`
  dominates the *model* energy at the image of `Φ`);
* **the model floor** `Clean.model_kafz` (FS `thm:Kafz`, node BF4; the clean re-delivery
  `cleanFloorAndEnv` of `model_kafz` and `envFacts_uniform`, whose cones are currently blocked by
  the `F9` fallout in `Work.BoseFixR.RB5FSFixAux`/`Work.BoseGateFS.GateHonest` — see
  `FINDING_RB4boxDomFS_of_bridge.md` §4): for every *window* `Ψ ≠ 0`,
  `(⨅_ρ valFS ρ − errKafz C_m)·⟨Ψ, Ψ⟩ ≤ ⟨Ψ, H2ndHon Ψ⟩`.

Chaining the two at the bridge's `Ψ` gives `⨅_ρ valFS ρ ≤ wordB/normB + errKafz (C_b + C_m)`,
and multiplying by `‖Φ‖² ≥ 0` (the *homogeneous* form, so that no division by a possibly
vanishing norm is needed) gives the domination with `C = C_b + C_m`; the constants are the
pointwise minima of the three thresholds (`box_to_model`, `model_kafz`, and the environment
facts that supply the bounded-belowness of `ρ ↦ valFS ρ`).

The two `⨅`-manipulations are the only bookkeeping:

* `iInf_mul_const_eq`: `(⨅_ρ a_ρ)·c = ⨅_ρ (a_ρ·c)` for `c ≥ 0` (the order isomorphism
  `x ↦ x·c` for `c > 0`, plus `c = 0`), so that the statement `⨅_ρ valFS ρ ≤ …` can be
  transported to the *statement's* left-hand side `⨅_ρ (valFS ρ·‖Φ‖²)`;
* the degenerate case `‖Φ‖² = 0`: the state vanishes on the box, hence `wordB = 0`
  (`Work.BoseKinLoc.Sector.eq_zero_on_abox_of_sqNormB_eq_zero` +
  `boxFormB_eq_zero_of_eq_zero_on_abox`), and the left-hand side is `0`.

`Adm` is monotone in its threshold, so all three thresholds can be intersected.
-/

namespace Work.BoseBoxFock

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped Real Topology BigOperators
open MeasureTheory Filter Metric

/-- `errKafz` is additive in its constant (it is linear in `C`). -/
lemma errKafz_add (v : ℝ³ → ℝ) (R μ C₁ C₂ : ℝ) :
    Work.BoseFixR.errKafz v R μ (C₁ + C₂)
      = Work.BoseFixR.errKafz v R μ C₁ + Work.BoseFixR.errKafz v R μ C₂ := by
  simp only [Work.BoseFixR.errKafz]
  ring

/-- **The infimum commutes with multiplication by a nonnegative constant.**  (The `≤`
direction is the one that needs the order isomorphism `x ↦ x * c`; the bounded-belowness
of the range is what makes the infimum non-junk.) -/
lemma iInf_mul_const_eq {ι : Type*} [Nonempty ι] (f : ι → ℝ) {c : ℝ} (hc : 0 ≤ c)
    (hb : BddBelow (Set.range f)) : (⨅ i, f i) * c = ⨅ i, f i * c := by
  rcases eq_or_lt_of_le hc with h | h
  · subst h
    simp
  · simpa using (OrderIso.map_ciInf (OrderIso.mulRight₀ c h) (f := f) hb)

/-- **The degenerate case**: a box state vanishing a.e. on the box has `wordB = 0` — both
the kinetic and the potential words are integrals over the box of terms involving `Φ`. -/
lemma wordB_eq_zero_of_normB_eq_zero {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v} {μ : ℝ} {n : ℕ}
    {Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (BoseGases.a v))}
    (hℓ : 0 < Work.BoseBox.sideAt μ (BoseGases.a v))
    (h0 : Work.BoseBoxFix.normB v μ n Φ = 0) : Work.BoseBoxFix.wordB v h μ n Φ = 0 := by
  have hzero : Work.BoseKinLoc.sqNormB n (Work.BoseBox.sideAt μ (BoseGases.a v))
      (Φ : Submission.BoseGases.X n → ℝ) = 0 := by
    simpa [Work.BoseBoxFix.normB] using h0
  have hΦ0 : ∀ x ∈ Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (BoseGases.a v)),
      (Φ : Submission.BoseGases.X n → ℝ) x = 0 :=
    Work.BoseKinLoc.Sector.eq_zero_on_abox_of_sqNormB_eq_zero hℓ Φ.contDiff.continuous hzero
  rw [Work.BoseBoxFix.wordB]
  exact Work.BoseKinLoc.Sector.boxFormB_eq_zero_of_eq_zero_on_abox hℓ hΦ0

theorem RB4boxDomFS_of_bridge (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1)
    (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R) (hav : 0 < BoseGases.a v)
    (fc fu : Work.BoseBoxFix.LowCut) (J : ℝ)
    (hB3 : Work.BoseBoxFix.NodeB3B v h R fc) : RB4boxDomFS v h R J fc fu := by
  classical
  -- the three thresholds and constants
  obtain ⟨Nmin, εb, Cb, hεb, hCb, hb⟩ :=
    box_to_model v h hv hv1 hvrad hR hv_supp hav fc fu J hB3
  obtain ⟨⟨εw, Cw, hεw, hCw, hw⟩, ⟨εm, Cm, hεm, hCm, hm⟩⟩ :=
    cleanFloorAndEnv v h hv hv1 hvrad hR hv_supp hav fc fu
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
  -- the environment facts (for the bounded-belowness of `ρ ↦ valFS ρ`)
  obtain ⟨hell0, hell, -, -, -, -, -, hWωabs, hWω0, -, -, -, -, -, -, -⟩ := hw HM μ hAdmw
  -- the bounded-belowness of `ρ ↦ valFS ρ`
  have hbdd : BddBelow (Set.range (fun ρ : {ρ : ℝ // 0 ≤ ρ} =>
      (HonestBoxFam v h fc fu HM μ).valFS ρ.1)) := by
    refine bddBelow_valFS_range_rho v h fc fu HM μ (Cw * BoseGases.a v)
      (∑ s ∈ Work.BoseB7.excited (Lab (HM μ).N),
        (HonestBoxFam v h fc fu HM μ).E.hatChiSq s ^ 2)
      hAdm.1 hav hWω0 hWωabs (Finset.sum_nonneg fun s _ => sq_nonneg _) le_rfl
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
    have hAle : (⨅ (ρ : {ρ : ℝ // 0 ≤ ρ}), (HonestBoxFam v h fc fu HM μ).valFS ρ.1)
        - Work.BoseFixR.errKafz v R μ Cm
        ≤ Work.BoseBoxFix.wordB v h μ n Φ / ν + Work.BoseFixR.errKafz v R μ Cb := by
      refine le_of_mul_le_mul_right ?_ hbbpos
      rw [hbbdef]
      exact le_trans hfl hΨbnd
    -- multiply by `ν > 0`
    have hAν : (⨅ (ρ : {ρ : ℝ // 0 ≤ ρ}), (HonestBoxFam v h fc fu HM μ).valFS ρ.1) * ν
        ≤ Work.BoseBoxFix.wordB v h μ n Φ + Work.BoseFixR.errKafz v R μ (Cb + Cm) * ν := by
      have h1 := mul_le_mul_of_nonneg_right hAle hν
      have h2 : (Work.BoseBoxFix.wordB v h μ n Φ / ν) * ν = Work.BoseBoxFix.wordB v h μ n Φ := by
        rw [div_mul_cancel₀ _ (ne_of_gt hpos)]
      have h2b : (Work.BoseBoxFix.wordB v h μ n Φ / ν + Work.BoseFixR.errKafz v R μ Cb) * ν
          = (Work.BoseBoxFix.wordB v h μ n Φ / ν) * ν + Work.BoseFixR.errKafz v R μ Cb * ν := by
        ring
      have h3 : (⨅ (ρ : {ρ : ℝ // 0 ≤ ρ}), (HonestBoxFam v h fc fu HM μ).valFS ρ.1) * ν
          - Work.BoseFixR.errKafz v R μ Cm * ν
          = ((⨅ (ρ : {ρ : ℝ // 0 ≤ ρ}), (HonestBoxFam v h fc fu HM μ).valFS ρ.1)
              - Work.BoseFixR.errKafz v R μ Cm) * ν := by ring
      have h4 : Work.BoseBoxFix.wordB v h μ n Φ
            + Work.BoseFixR.errKafz v R μ (Cb + Cm) * ν
          = (Work.BoseBoxFix.wordB v h μ n Φ + Work.BoseFixR.errKafz v R μ Cb * ν)
            + Work.BoseFixR.errKafz v R μ Cm * ν := by
        rw [errKafz_add]; ring
      linarith [h1, h2, h2b, h3, h4]
    -- the statement's left-hand side is the same infimum
    rw [← iInf_mul_const_eq (fun ρ : {ρ : ℝ // 0 ≤ ρ} =>
        (HonestBoxFam v h fc fu HM μ).valFS ρ.1) hν hbdd]
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
