import ChallengeDeps
import Submission.Work.BoseFixB1.RegimeAux
import Submission.Work.BoseFixB2.Arith.bigM_ge_eight
import Submission.Work.BoseFixB2.Sector.integrableOn_fsT_fibre_smooth
import Submission.Work.BoseFixB2.Sector.jointProj_aP_eq_zero
import Submission.Work.BoseFixB2.Sector.normB_secProj_sum
import Submission.Work.BoseFixB2.Sector.secProj_contDiff_symm
import Submission.Work.BoseFixB2.Sector.secProj_orthogonal
import Submission.Work.BoseFixB2.Sector.secProj_resolution
import Submission.Work.BoseKinLoc.Word.kinFormB_nonneg
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB2.DvApriori.BandDefs` — the import environment of the
FS §6 `eq:dvapriori` (`d₁,d₂`) node.

This module collects, for the children of the `dOne_dTwo_le` node, the two corpora that the
node's proof spans:

* the **new** box vocabulary `Work.BoseKinLoc` (`boxFormB`/`kinFormB`/`fsT`, `secProj`,
  `jointProj`, the `BoxState` class) together with its sector algebra
  (`secProj_resolution`/`secProj_orthogonal`/`jointProj_aP_eq_zero`/`jointProj_orthogonal`/
  `jointProj_const_slot_zero`, `kinFormB_nonneg`, `integrableOn_fsT_fibre_smooth`);
* the **old** centred-box vocabulary `Submission.BoseGases` (`aP`/`aQ`, `wPairC`,
  `pairSet`, `abox`, `q1word`/`q3word`/`q4word`/`qLHSword`, `cnPlus`) with the proved
  FS §5 potential estimates `qcross_w_d11`, `qcross_w_d13_quarter`, `qcross_w_d2_quarter`
  (`Submission.Work.WCrossD2`/`APrioriClosed`) and the potential lower bound
  `potapp_q4` (`Submission.PotAppFull`).

The two vocabularies agree definitionally on the shared objects: `Work.BoseKinLoc.fibre`,
`Work.BoseKinLoc.aP = Submission.BoseGases.aP`, and
`Work.BoseKinLoc.wLoc ℓ h 0 = Submission.BoseGases.wPairC ℓ h`, so a statement mixing them
is meaningful.
-/

namespace Work.BoseFixB2.DvApriori

open Submission.BoseGases Work.BoseKinLoc

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 2. The two parts of the box word and their polarisations -/

/-- The kinetic part of the frozen box word `wordB` (`kinFormB` at FS's parameters). -/
noncomputable def kinPart (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) (μ : ℝ)
    (n : ℕ) (Φ : Submission.BoseGases.X n → ℝ) : ℝ :=
  Work.BoseKinLoc.kinFormB n (Work.BoseFixB2.fsSide v μ) (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b Φ

/-- The potential part of the frozen box word `wordB` (the multiplication term). -/
noncomputable def potPart (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) (μ : ℝ)
    (n : ℕ) (Φ : Submission.BoseGases.X n → ℝ) : ℝ :=
  ∫ x in Submission.BoseGases.abox n (Work.BoseFixB2.fsSide v μ),
      (Φ x) ^ 2 * Work.BoseKinLoc.potWordU n v (Submission.BoseGases.g0 v h) (Work.BoseFixB2.fsSide v μ) μ 0 x

/-- The polarisation of the kinetic part of the box word. -/
noncomputable def polKin (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) (μ : ℝ)
    (n : ℕ) (Φ Ψ : Submission.BoseGases.X n → ℝ) : ℝ :=
  (kinPart v h μ n (fun x => Φ x + Ψ x) - kinPart v h μ n (fun x => Φ x - Ψ x)) / 4

/-- The polarisation of the potential part of the box word. -/
noncomputable def polPot (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) (μ : ℝ)
    (n : ℕ) (Φ Ψ : Submission.BoseGases.X n → ℝ) : ℝ :=
  (potPart v h μ n (fun x => Φ x + Ψ x) - potPart v h μ n (fun x => Φ x - Ψ x)) / 4

/-! ## 3. The parameter ranges at `Adm` -/

/-- The parameters `d, s, ε_T, b` of `paramsAt μ (a v)` are in the ranges required by
`kinFormB_nonneg`: `0 < d`, `0 < s`, `0 ≤ ε_T ≤ 1`, `0 ≤ b`. -/
theorem params_facts {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ} (hμ : 0 < μ)
    (hav : 0 < _root_.BoseGases.a v) (ht1 : μ * (_root_.BoseGases.a v) ^ 3 ≤ 1) :
    0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
      ∧ 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
      ∧ 0 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
      ∧ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT ≤ 1
      ∧ 0 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b := by
  have ht : (0 : ℝ) < μ * (_root_.BoseGases.a v) ^ 3 := by positivity
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [show (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
        = Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) 6 from rfl, Work.BoseBox.fsXp]
    exact Real.rpow_pos_of_pos ht _
  · rw [show (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
        = Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) 1 from rfl, Work.BoseBox.fsXp]
    exact Real.rpow_pos_of_pos ht _
  · rw [show (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
        = Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) (23 / 4) from rfl, Work.BoseBox.fsXp]
    exact (Real.rpow_pos_of_pos ht _).le
  · rw [show (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
        = Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) (23 / 4) from rfl, Work.BoseBox.fsXp]
    exact Real.rpow_le_one ht.le ht1 (by norm_num)
  · rw [show (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b = Work.BoseBox.bValue from rfl,
      Work.BoseBox.bValue]
    norm_num

/-- `wordB` splits into its kinetic and potential parts (definitional). -/
theorem wordB_eq_kinPart_add_potPart {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    {h : Work.UBB.ScatSol v} {μ : ℝ} {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ} :
    Work.BoseBoxFix.wordB v h μ n Φ = kinPart v h μ n Φ + potPart v h μ n Φ := rfl

/-- **`polB` is the sum of the polarisations of the two parts** of the box word. -/
theorem polB_eq_polKin_add_polPot {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    {h : Work.UBB.ScatSol v} {μ : ℝ} {n : ℕ} {Φ Ψ : Submission.BoseGases.X n → ℝ} :
    Work.BoseFixB2.polB v h μ n Φ Ψ = polKin v h μ n Φ Ψ + polPot v h μ n Φ Ψ := by
  have h1 : Work.BoseBoxFix.wordB v h μ n (fun x => Φ x + Ψ x)
      = kinPart v h μ n (fun x => Φ x + Ψ x) + potPart v h μ n (fun x => Φ x + Ψ x) := rfl
  have h2 : Work.BoseBoxFix.wordB v h μ n (fun x => Φ x - Ψ x)
      = kinPart v h μ n (fun x => Φ x - Ψ x) + potPart v h μ n (fun x => Φ x - Ψ x) := rfl
  simp only [Work.BoseFixB2.polB, polKin, polPot]
  rw [h1, h2]
  ring

end Work.BoseFixB2.DvApriori



