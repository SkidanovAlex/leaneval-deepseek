import ChallengeDeps
import Submission.Work.SmallBoxSliding.Assembly
import Submission.Work.UBB.lambda_le_wordInf_of_spectral
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.UBB.Assembly` — the UBB assembly proper

This module is the assembly: it derives `Work.UBB.UBB` (FS `thm:LHY-Box` in the
canonical corpus form consumed by `Submission.UBBtoGc`) from the **named
sibling inputs** of `Defs.lean`, with all the logical and arithmetic glue
proved here.

## The chain (each step proved, no `sorry`)

1. `spectralInput_of_pieces` — the per-state spectral input (FS `eq:ToProve`)
   follows from the two sibling chapters:
   `AprioriNPlus` (FS `thm:aprioriHLambda`, the `n₊` window for low states —
   sibling `SmallBoxSliding`) and `BogoliubovLow` (FS §9–11, the Bogoliubov
   bound *under* that window — sibling `SmallBoxBogolubov*`).  The composition
   is the one-line `hBog Φ (hApriori Φ hΦ) hΦ`: the a-priori chapter delivers
   exactly the `n₊`-hypothesis the Bogoliubov chapter consumes.
2. `fsShape_of_inputs` — the shifted (FS) box bound `FSShape` from
   `SpectralInput` + the dictionary `WordBridge`, using the proved dichotomy
   `lambda_le_wordInf_of_spectral` (this is FS's "let Ψ be a low state; if such
   a state does not exist, there is nothing to prove").
3. `boxShape_of_inputs` / `uniformBoxBound` — `BoxShape`/`UBB` from the same
   inputs, via the *exact* dictionary `Arith.boxShape_iff_fsShape`.
4. `hubb_of_UBBExists` — the consumer-facing shape (identical to the `hubb`
   hypothesis of `Submission.UniformBox.hbox_of_uniform_box_av` and
   `Submission.UBBtoGc.hpres_of_UBB`: the corpus side consumes `UBB` verbatim).

## Where the sharp constant and the exponents live

* the sharp `128/(15√π)` is the *definition* `lhyC`, used in `Lambda`/`Theta`
  and never weakened: `Lambda A K η₀ ρ = −4πρ²A(1 − lhyC√(ρA³) + K(ρA³)^{1/2+η₀})`;
* the error exponent `1/2 + η₀` is explicit everywhere, and
  `Arith.theta_ge_lambda` pins the *only* constraint on the FS a-priori
  parameter: `J ≥ lhyC` (with `0 < J ≤ K_B³` this is compatible, FS's
  `K_B ≥ 1`);
* every *other* constant is existentially quantified and freely chosen
  (`C`, `K_B`, `K_ℓ`, `ε₀`) — the "Session-100b" scoping of
  `SmallBoxDesignNote.md`: only `lhyC` and the exponent are rigid for
  `theorem_1_2`.
-/

noncomputable section

open _root_.BoseGases
open Submission.BoseGases
set_option autoImplicit false
set_option linter.dupNamespace false

namespace Work.UBB

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Filter Metric MeasureTheory
open scoped ContDiff Topology Real

/-! ## 1. The decomposition into the two sibling inputs -/

/-- **The decomposition of the deep input** (proved): the per-state spectral
input FS `eq:ToProve` follows from

* `AprioriNPlus` — the a-priori `n₊` window for low states
  (FS `thm:aprioriHLambda`; sibling `Work.SmallBoxSliding`, with the
  arithmetic `Work.SmallBoxSliding.Assembly.apriori_nplus_window_assembly`
  already CLOSED and the `hslide` localisation, the `𝒯_B` kinetic residual
  of `Work.SmallBoxTBWord` and FS `thm:smallbox`
  (`Work.SmallBoxDLBound`/`Work.SmallBoxA0`) as its remaining named inputs), and
* `BogoliubovLow` — the Bogoliubov bound *under* that window (FS §9–11;
  sibling `Work.SmallBoxBogolubov*`, whose own named residual is the
  kinetic/localisation input).

The composition is immediate: `AprioriNPlus` produces exactly the `n₊`
hypothesis that `BogoliubovLow` consumes. -/
theorem spectralInput_of_pieces {v : ℝ³ → ℝ} {h : ScatSol v} {J ε₀ η₀ : ℝ}
    {W : ℕ → ℝ → ℝ}
    (ha1 : AprioriNPlus v h J W ε₀) (ha2 : BogoliubovLow v h J W ε₀ η₀) :
    SpectralInput v h J ε₀ η₀ := by
  rcases ha2 with ⟨C, hC, hlow⟩
  refine ⟨C, hC, ?_⟩
  intro L hL N hN Φ hΦ
  exact hlow L hL N hN Φ (ha1 L hL N hN Φ hΦ) hΦ

/-! ## 2. The box bound in FS's shifted normalisation -/

/-- **`FSShape` from the named inputs** (proved): the per-state spectral input
plus the word/Hamiltonian dictionary and the arithmetic choice `J ≥ c` give
FS's `thm:LHY-Box` in its own chemical-potential normalisation, at
`μ := N/L³`.  The dichotomy (`lambda_le_wordInf_of_spectral`) is FS's
"if such a state does not exist, then there is nothing to prove". -/
theorem fsShape_of_inputs {v : ℝ³ → ℝ} {h : ScatSol v} {J ε₀ η₀ : ℝ}
    (hA : 0 ≤ a v) (hJ : lhyC ≤ J) (hbridge : WordBridge v h)
    (hspec : SpectralInput v h J ε₀ η₀) :
    ∃ C : ℝ, 0 ≤ C ∧ FSShape v (a v) C ε₀ η₀ := by
  rcases hspec with ⟨C, hC, hspec⟩
  refine ⟨C, hC, ?_⟩
  intro L hL N hN
  have hinf : Lambda (a v) C η₀ (dens N L) ≤ wordInf N L (dens N L) v h :=
    lambda_le_wordInf_of_spectral (hA := hA) (hC := hC) (hJ := hJ) hspec L hL N hN
  have hbr := hbridge L hL N
  linarith

/-- **The FS-shaped box bound at the corpus per-box level**: FS `thm:LHY-Box`
stated for the per-box shifted energy density `wordInf` (equivalently the
sibling's `eB N L ρ v h / L³`, by `wordInf_eq_eB_div`).  This is FS's theorem
*before* the word/Hamiltonian dictionary `WordBridge` is applied, so a
sibling chapter can deliver it without touching `𝓜`/`boxEnergy` at all. -/
def FSShapeE (v : ℝ³ → ℝ) (h : ScatSol v) (C ε₀ η₀ : ℝ) : Prop :=
  ∀ L : ℝ, 1 ≤ L → ∀ N : ℕ, dens N L * (a v) ^ 3 ≤ ε₀ →
    Lambda (a v) C η₀ (dens N L) ≤ wordInf N L (dens N L) v h

/-- **`FSShapeE` from the named inputs** (proved): the per-state spectral input
plus the arithmetic choice `J ≥ c` give FS's box theorem at the corpus per-box
level.  (`fsShape_of_inputs` is the same with the dictionary applied.) -/
theorem fsShapeE_of_inputs {v : ℝ³ → ℝ} {h : ScatSol v} {J ε₀ η₀ : ℝ}
    (hA : 0 ≤ a v) (hJ : lhyC ≤ J) (hspec : SpectralInput v h J ε₀ η₀) :
    ∃ C : ℝ, 0 ≤ C ∧ FSShapeE v h C ε₀ η₀ := by
  rcases hspec with ⟨C, hC, hspec⟩
  exact ⟨C, hC, fun L hL N hN =>
    lambda_le_wordInf_of_spectral (hA := hA) (hC := hC) (hJ := hJ) hspec L hL N hN⟩

/-- The word/Hamiltonian dictionary converts `FSShapeE` into FS's statement
about the canonical box energy density. -/
theorem fsShape_of_fsShapeE {v : ℝ³ → ℝ} {h : ScatSol v} {C ε₀ η₀ : ℝ}
    (hE : FSShapeE v h C ε₀ η₀) (hbr : WordBridge v h) : FSShape v (a v) C ε₀ η₀ := by
  intro L hL N hN
  linarith [hE L hL N hN, hbr L hL N]

/-! ## 3. UBB -/

/-- **The UBB assembly** (proved from the named inputs): the canonical corpus
box bound `BoxShape` follows. -/
theorem boxShape_of_inputs {v : ℝ³ → ℝ} {h : ScatSol v} {J ε₀ η₀ : ℝ}
    (hA : 0 ≤ a v) (hJ : lhyC ≤ J) (hbridge : WordBridge v h)
    (hspec : SpectralInput v h J ε₀ η₀) :
    ∃ C : ℝ, 0 ≤ C ∧ BoxShape v (a v) C ε₀ η₀ := by
  rcases fsShape_of_inputs (v := v) (h := h) (J := J) (ε₀ := ε₀) (η₀ := η₀)
      hA hJ hbridge hspec with ⟨C, hC, hfs⟩
  exact ⟨C, hC, boxShape_iff_fsShape.mpr hfs⟩

/-- **`UBB` from the named inputs** (the headline of this area): with
`0 < ε₀`, `c ≤ J`, `0 ≤ a v`, the word/Hamiltonian dictionary and the per-state
spectral input, the uniform dilute box bound `UBB v η₀` holds. -/
theorem UBB_of_inputs {v : ℝ³ → ℝ} {h : ScatSol v} {J ε₀ η₀ : ℝ}
    (hε₀ : 0 < ε₀) (hA : 0 ≤ a v) (hJ : lhyC ≤ J) (hbridge : WordBridge v h)
    (hspec : SpectralInput v h J ε₀ η₀) :
    UBB v η₀ :=
  let ⟨C, hC, hb⟩ := boxShape_of_inputs hA hJ hbridge hspec
  ⟨ε₀, hε₀, C, hC, hb⟩

/-- **The UBB assembly, in the shape of the deliverable** (the target theorem of
this area): `UBB` from the two sibling chapters' named inputs
(`AprioriNPlus`: FS `thm:aprioriHLambda`, sibling `SmallBoxSliding`;
`BogoliubovLow`: FS §9–11, sibling `SmallBoxBogolubov*`), the dictionary
`WordBridge`, and the arithmetic side conditions. -/
theorem uniformBoxBound {v : ℝ³ → ℝ} {h : ScatSol v} {J ε₀ η₀ : ℝ} {W : ℕ → ℝ → ℝ}
    (hε₀ : 0 < ε₀) (hA : 0 ≤ a v) (hJ : lhyC ≤ J) (hbridge : WordBridge v h)
    (ha1 : AprioriNPlus v h J W ε₀)
    (ha2 : BogoliubovLow v h J W ε₀ η₀) :
    UBB v η₀ :=
  UBB_of_inputs hε₀ hA hJ hbridge (spectralInput_of_pieces ha1 ha2)

/-- The assembly in two stages, isolating the dictionary `WordBridge` to the
last step: the deep content produces `FSShapeE` (`fsShapeE_of_inputs`), and the
dictionary converts it (`fsShape_of_fsShapeE`). -/
theorem uniformBoxBound_two_stage {v : ℝ³ → ℝ} {h : ScatSol v} {J ε₀ η₀ : ℝ}
    (hε₀ : 0 < ε₀) (hA : 0 ≤ a v) (hJ : lhyC ≤ J) (hbridge : WordBridge v h)
    (hspec : SpectralInput v h J ε₀ η₀) : UBB v η₀ :=
  UBB_of_inputs hε₀ hA hJ hbridge hspec

/-! ## 4. Consumer shapes

The corpus side (`Submission/UBBtoGc.hpres_of_UBB` /
`Submission.UniformBox.hbox_of_uniform_box_av` / `Work/EndgameCheck`) consumes
`UBB` in the `∃η₀`-packaged form.  These two lemmas are the exact interfaces;
they are pure `simpa`s. -/

/-- The `∃η₀`-packaged shape consumed by the endgame (`Work.EndgameCheck`,
`Submission.UniformBox`). -/
theorem ubbExists_of_UBB {v : ℝ³ → ℝ} {η₀ η : ℝ} (hη₀ : 0 < η₀)
    (hη₀le : η₀ ≤ 1 / 2) (hηlt : η < η₀) (h : UBB v η₀) : UBBExists v η := by
  rcases h with ⟨ε₀, hε₀, C, hC, hb⟩
  exact ⟨η₀, hη₀, hη₀le, hηlt, ε₀, hε₀, C, hC, hb⟩

/-- The consumer shape, written exactly as the `hubb` hypothesis of
`Submission.UniformBox.hbox_of_uniform_box_av` /
`Submission.UBBtoGc.hpres_of_UBB`. -/
theorem hubb_of_UBBExists {v : ℝ³ → ℝ} {η : ℝ} (h : UBBExists v η) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ η₀ ≤ 1 / 2 ∧ η < η₀ ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, 1 ≤ L → ∀ N : ℕ,
        ((N : ℝ) / L ^ 3) * (a v) ^ 3 ≤ ε₀ →
        lhyRhs (a v) C (1 / 2 + η₀) ((N : ℝ) / L ^ 3) ≤ boxEnergy N L v / L ^ 3 := by
  simpa [UBBExists, BoxShape, dens] using h

/-! ## 5. The corpus a-priori arithmetic, integrated

`Work.SmallBoxSliding.Assembly.apriori_nplus_window_assembly` is CLOSED
(sorry-free) and is exactly the arithmetic that turns the sliding localisation
+ the energy hypothesis `hEgc` into the two windows of FS `eq:apriorinn+`.
Re-exported here so that the `AprioriNPlus` input of §1 has a proved
arithmetic core and the *only* residual of that chapter is visible in one
place. -/

/-- FS `eq:apriorinn+`, second conjunct (the excited-count window), from the
sliding identity `hslide`, the energy hypothesis `hE` and the two numeric-shape
hypotheses — the CLOSED corpus arithmetic. -/
theorem cnPlus_le_window_of_corpus {N : ℕ} {ℓ μ b : ℝ} (hℓ : 0 < ℓ) (hμ : 0 < μ)
    (hb : 0 < b)
    {a R J K_B K_ℓ om c₁ C E : ℝ} (ha : 0 ≤ a) (hKB : 0 < K_B) (hKℓ : 0 < K_ℓ)
    (hJ : 0 ≤ J) (hR : 0 ≤ R) (hom : 0 ≤ om) (hc₁ : 0 < c₁) (hC : 0 ≤ C)
    {Φ : X N → ℝ}
    (hE : E ≤ - 4 * π * μ ^ 2 * a * ℓ ^ 3 * (1 - J * (μ * a ^ 3) ^ (1 / 2 : ℝ)))
    (hslide : R + (b / (2 * ℓ ^ 2)) * cnPlus ℓ Φ
        - 4 * π * μ ^ 2 * a * ℓ ^ 3 * (1 + K_B ^ 3 * (μ * a ^ 3) ^ (1 / 2 : ℝ)) ≤ E)
    (hwindow : |(N : ℝ) - μ * ℓ ^ 3| ≤ Real.sqrt om * Real.sqrt (R / c₁))
    (hcnShape : (2 * ℓ ^ 2 / b) * (4 * π * μ ^ 2 * a * ℓ ^ 3 * (J + K_B ^ 3)
          * (μ * a ^ 3) ^ (1 / 2 : ℝ))
        ≤ C * μ * ℓ ^ 3 * K_B ^ 3 * K_ℓ ^ 2 * (μ * a ^ 3) ^ (1 / 2 : ℝ))
    (hwinShape : Real.sqrt om
          * Real.sqrt (4 * π * μ ^ 2 * a * ℓ ^ 3 * (J + K_B ^ 3)
              * (μ * a ^ 3) ^ (1 / 2 : ℝ) / c₁) / ℓ ^ 3
        ≤ μ * C * K_B ^ (3 / 2 : ℝ) * K_ℓ * (μ * a ^ 3) ^ (1 / 4 : ℝ)) :
    cnPlus ℓ Φ ≤ C * μ * ℓ ^ 3 * K_B ^ 3 * K_ℓ ^ 2 * (μ * a ^ 3) ^ (1 / 2 : ℝ) :=
  (Work.SmallBoxSliding.apriori_nplus_window_assembly hℓ hμ hb ha hKB hKℓ hJ hR hom hc₁ hC
    hE hslide hwindow hcnShape hwinShape).1

end Work.UBB
