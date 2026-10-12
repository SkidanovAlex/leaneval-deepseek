import ChallengeDeps
import Submission.Work.FSKernelCompare
import Submission.Work.QDecompSimpler
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Session-213 Step-0 — the w₂-A0/Bogolubov bridge (closed exact identities)

(Work-in-progress module; Session-213.  The first closed pieces of the
w₂-A0/Bogolubov re-derivation identified in the Session-212 structural
audit — connecting `A0Core`'s pure-real ∬w₂-A0-form to the ACTUAL
`qLHSword` structure.)

* `q0word_w2_mass_sub` — the **∬w₂-substitution in the actual q0-word**
  (the condensate piece of the potential): from the closed exact value
  `Q0Ren.q0_chosen_expect` (`q0word(g₀,g₂) = ½ℓ⁻³·(∫g₂)·cS2 − 8πaμ·cS1`) and
  `g2_integral_eq_av_add_g0w0` (`∫g₂ = 8π(av) + g0w0Mass`),

      q0word(g₀,g₂)Φ = ½ℓ⁻³·(8π(av) + g0w0Mass)·cS2(Φ) − 8π(av)·μ·cS1(Φ)

  — i.e. `q0word = q0RenVal + ½ℓ⁻³·g0w0Mass·cS2`, the `ĝω(0)`-excess of the
  ∬w₂-mass over ∬w₁ (`SmallBoxKernelMass.wPair_g2_g0_box_mass` at the word
  level).  This is exactly the substitution `∬w₂ = ∬w₁ + ĝω(0)·ℓ³` in the
  condensate expression.
* `qLHSword_a0_w2_form` — the **bridge identity** (closed, from the exact
  `PotChosen.potsplit_chosen` + `q0word_w2_mass_sub`):

      qLHSword(wPairC v, wPairC g₀)Φ
        = [½ℓ⁻³(8π(av)+g0w0Mass)·cS2 − 8π(av)μ·cS1]     (the ∬w₂-A0 value)
          + q1word(g₀,g₂)Φ + q2word(g₀,g₂)Φ + q3word(g₀)Φ + q4word(v,ω₀)Φ .

  i.e. the condensate/A0 part of `qLHSword` EQUALS its ∬w₂-A0-form plus the
  (exact) q1..q4 word corrections — the precise statement the Bogolubov
  `A₂`-treatment (`Fock2Mode`), the kinetic-gap absorption and the
  `A0Core` square conversion act on (the open multi-session core; see
  SmallBoxDesignNote Sessions 212–213).
-/

noncomputable section

open MeasureTheory Metric
open scoped Real BigOperators ENNReal Topology ContDiff

namespace Submission

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box
set_option autoImplicit false
set_option linter.unusedVariables false

namespace BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- **∬w₂-substitution in the actual q0-word**: `q0word(g₀,g₂)Φ =
½ℓ⁻³·(8π(av)+g0w0Mass)·cS2(Φ) − 8π(av)·μ·cS1(Φ)` — the condensate piece
with the ∬w₂-mass displayed (from `Q0Ren.q0_chosen_expect` +
`g2_integral_eq_av_add_g0w0`). -/
lemma q0word_w2_mass_sub {N : ℕ} {v : ℝ³ → ℝ} {R ℓ : ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hℓ : 0 < ℓ) (hRℓ : R ≤ ℓ * chiR0) (μ : ℝ) {Φ : X N → ℝ}
    (hΦc : Continuous Φ) :
    q0word (N := N) ℓ μ (wPairC ℓ (g0 v h)) (wPairC ℓ (g2 v h)) Φ
      = (1 / 2) * (ℓ ^ 3)⁻¹ * (8 * π * a v + g0w0Mass (v := v) h) * cS2 ℓ Φ
        - (8 * π * a v) * μ * cS1 ℓ Φ := by
  have hv0 := q0_chosen_expect (N := N) (v := v) (R := R) (ℓ := ℓ) hR hv_nonneg hvrad
    hv_supp h hℓ hRℓ μ (Φ := Φ) hΦc
  have hM : (∫ z : ℝ³, g2 v h z) = 8 * π * a v + g0w0Mass (v := v) h := by
    dsimp [g0w0Mass]
    exact g2_integral_eq_av_add_g0w0 hR hv_nonneg hvrad hv_supp h
  have hident : q0word (N := N) ℓ μ (wPairC ℓ (g0 v h)) (wPairC ℓ (g2 v h)) Φ
      = (1 / 2) * (ℓ ^ 3)⁻¹ * (∫ z : ℝ³, g2 v h z) * cS2 ℓ Φ
        - (8 * π * a v) * μ * cS1 ℓ Φ := by
    simpa [q0word, w1Fibre, wPairC, wPairU] using hv0
  rw [hident, hM]

/-- **The bridge identity (closed)**: `qLHSword`'s condensate/A0 part equals
its ∬w₂-A0-form plus the exact q1..q4 word corrections — the exact potsplit
(`PotChosen.potsplit_chosen`) with the q0-value substituted by its ∬w₂-form
(`q0word_w2_mass_sub`).  The Bogolubov `A₂`-treatment, kinetic-gap
absorption and `A0Core` square conversion act on the q-word block on the
RHS. -/
lemma qLHSword_a0_w2_form {N : ℕ} {ℓ μ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ}
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    qLHSword (N := N) ℓ μ (wPairC ℓ v) (wPairC ℓ (g0 v h)) Φ
      = (1 / 2) * (ℓ ^ 3)⁻¹ * (8 * π * a v + g0w0Mass (v := v) h) * cS2 ℓ Φ
        - (8 * π * a v) * μ * cS1 ℓ Φ
        + q1word (N := N) ℓ μ (wPairC ℓ (g0 v h)) (wPairC ℓ (g2 v h)) Φ
        + q2word (N := N) ℓ μ (wPairC ℓ (g0 v h)) (wPairC ℓ (g2 v h)) Φ
        + q3word (N := N) ℓ (wPairC ℓ (g0 v h)) Φ
        + q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ := by
  have hp := potsplit_chosen (N := N) (ℓ := ℓ) (μ := μ) hℓ hv_nonneg hvrad hv_memL1
    hR hv_supp h hRℓ hΦc
  have hq0 := q0word_w2_mass_sub hR hv_nonneg hvrad hv_supp h hℓ hRℓ μ hΦc
  rw [hq0] at hp
  exact hp


/-- **q2-word exact split isolating the A₂ (Bogolubov) object**: from the
`PotWords.q2word` definition with the chosen kernels
(`w₁ := wPairC(g₀)`, `w₂ := wPairC(g₂)`),

    q2word(g₀,g₂)Φ = q1PairWord(Φ) + q2PairWord(Φ) − μ·qOneMass(Φ) + q4PairWord(Φ)

where `q4PairWord := Σ_p∫(P_iP_jΦ)(Q_jQ_iΦ)·w₁` is FS's `A₂` — the two-Q
word that the Bogolubov treatment (`Fock2Mode` two-mode bound) handles
together with the kinetic gap (the row-6 gate; q1/q2PairWord/qOneMass have
their exact slot-sandwich/peel forms closed — `Q1Peel`, `q2PairWord_eq_slot_
sandwich`).  This is the exact identity against which the `A₂`-Bogolubov
sub-bound attaches inside `qLHSword_a0_w2_form`. -/
lemma q2word_a2_split {N : ℕ} {ℓ μ : ℝ} {v : ℝ³ → ℝ}
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) {Φ : X N → ℝ} :
    q2word (N := N) ℓ μ (wPairC ℓ (g0 v h)) (wPairC ℓ (g2 v h)) Φ
      = q1PairWord (ℓ := ℓ) (v := v) h (Φ := Φ)
        + q2PairWord (ℓ := ℓ) (v := v) h (Φ := Φ)
        - μ * qOneMass (ℓ := ℓ) (v := v) h (Φ := Φ)
        + q4PairWord (ℓ := ℓ) (v := v) h (Φ := Φ) := by
  simp [q2word, q1PairWord, q2PairWord, q4PairWord, qOneMass, w1Fibre, wPairC]

end BoseGases

end Submission
