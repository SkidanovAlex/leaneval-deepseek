import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBox.B2Grading
import Submission.Work.BoseBox.cnPlus_le_of_spectralNPlusLe
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBox.B2Reduction` — the §6 node `B2` reduced to its two irreducible inputs

This module isolates **exactly** what the corrected §6 node `Work.BoseBox.NodeB2g`
(`B2Grading.lean`) needs beyond the (already proved) Lieb–Solovej matrix theorem
`Work.UBBInputs3.ls_localisation_band2`, and proves the reduction

    `B2GradingData v h J`  →  `B2AprioriWindow v h J'`  →  `NodeB2g v h J J'`

(`nodeB2g_of_data` below), i.e. the *decoupled-parameter* instantiation of the
chapter's coupled-parameter template `Work.UBBInputs3.NPlusGrading` +
`locMatricesResidual_of_grading` — with the essential difference that here the
recombination carries the **spectral** condition `SpectralNPlusLe ℓ 𝓜 Φ'`
(FS `eq:LocalizedNPlus`) rather than the expectation window `cnPlus ≤ W·‖·‖²`, and
that the window is *placed* (FS's argument: `[0, 𝓜'] ⊂ [0, 𝓜]`).

## The two inputs, and why no proof of `NodeB2g` can avoid them

FS prove `lem:LocMatrices` from **thm:aprioribounds** (FS §5, Appendix
`SmallBoxes`), and their proof uses it in two *independent* places:

* `B2GradingData v h J` — FS §6 steps (2)–(4): for every low state `Φ` the matrix
  `A_{ij} = ‖1_{n₊=i}Φ‖⁻¹‖1_{n₊=j}Φ‖⁻¹⟨1_{n₊=i}Φ, H_Λ(μ)1_{n₊=j}Φ⟩` together
  with the norm profile `ψ` of `Φ`, the energy identity `⟨ψ,Aψ⟩‖Φ‖² = ⟨Φ,H_Λ(μ)Φ⟩`,
  the **band property** `d_k = 0` (`k ≥ 3`, the interaction being two-body), the FS
  `eq:dvapriori` bound `|d₁| + |d₂| ≤ K μ²ℓ³` (the *only* place `∫v` enters the
  paper, and half of `thm:aprioribounds`), the Lieb–Solovej *recombination*
  `Ψ̃ = ‖φ̃‖⁻¹Σᵢφ̃ᵢ‖1_{n₊=i}Φ‖⁻¹1_{n₊=i}Φ`, and — the point of the spectral form —
  the fact that the recombined state *is* spectrally confined to the window
  (`SpectralNPlusLe`), together with the two window inequalities that the placement
  argument consumes;
* `B2AprioriWindow v h J'` — FS `eq:apriorinn+`, second conjunct
  (`⟨n₊⟩ ≤ C K_B³K_ℓ²μℓ³(μa³)^{1/2} = C nPlusWindow`) **applied to the output
  state**, i.e. at the *raised* threshold `J'` (FS: "This follows from the estimate
  `eq:EnergyBound`, `J = ½K_B³`, and `con:KMRKB`, which imply that we may use the
  a priori bound `eq:apriorinn+` on the expectation value of `n₊` in `Ψ̃`. The
  consequence is that the interval of `n₊` values in `Ψ̃` must be contained in
  `[0, 𝓜' + CK_B³K_ℓ⁵] ⊆ [0,𝓜]`").

Both are *open* in this workspace (the corpus's a-priori window is conditional on
FS `eq:BSsliding2` = Bratteli–Solovej Thm 3.10, whose corpus renderings are
refuted; the `n₊`-grading is the coupled-parameter residual
`Work.UBBInputs3.NPlusGrading`).  This module therefore **names** them, and proves
that they *suffice* — nothing else is missing.

## What *is* proved here (sorry-free, axiom-clean)

* `exists_lsError_paid` — the Lieb–Solovej error `8000 K μ²ℓ³𝓜^{-2}` is paid by
  the a-priori threshold gap `ℓ³(Θ(J') − Θ(J)) = 4πaμ²ℓ³(J'−J)(μa³)^{1/2}` as soon
  as `(μa³)^{2/323} ≤ 4πa(J'−J)/(8000K)` (the surplus `4/646 = 2/323` of
  `𝓜^{-2} = (μa³)^{327/646}` over `(μa³)^{1/2}`).  This is the arithmetic that makes
  the replacement *low at the raised threshold*.
* `exists_place_le_halfM` — the window placement: `C·nPlusWindow ≤ 𝓜/2` for small
  diluteness (`nPlusWindow = (μa³)^{-51/646}`, `𝓜 = (μa³)^{-327/1292}`; the margin
  is `(μa³)^{225/1292}`), i.e. FS's `[0, 𝓜' + CK_B³K_ℓ⁵] ⊆ [0,𝓜]`.
* `nodeB2g_of_data` — the reduction, by `ls_localisation_band2` at window length
  `Mw` (`𝓜/4 ≤ Mw ≤ 𝓜/2`), the recombination and the placement.
-/

noncomputable section

open scoped Real Topology BigOperators

namespace Work.BoseBox


open Filter Metric MeasureTheory
open _root_.BoseGases
open Submission.BoseGases
open Work.UBB
open Work.UBBInputs3

set_option linter.unusedVariables false
set_option autoImplicit false

/-! ## 1. The two named inputs -/

/-- **FS §5, `eq:apriorinn+` second conjunct, at the decoupled parameters (the
*only* a-priori input of §6).**  For every *low* state (FS `eq:aprioriPsi` at
threshold `J`) of the box of side `ℓ(μ)`, the expected number of excited
particles is bounded by the a-priori window `nPlusWindow = K_ℓ⁵K_B³`:

    `cnPlus ℓ Φ ≤ C nPlusWindow‖Φ‖²`.

FS apply it to the *output* state of `lem:LocMatrices` (hence the threshold is the
raised one `J'`), and its content is `thm:aprioriHLambda`/`thm:aprioribounds` (FS
§5 + Appendix `SmallBoxes`), i.e. the corpus's `Work.UBBInputs9.BSslidingKin`
(FS `eq:BSsliding2`, Bratteli–Solovej Thm 3.10) plus the small-box analysis — the
project's open block.  Nothing in §6 beyond the placement of the Lieb–Solovej
window consumes it.

**FS's upper bound `J ≤ K_B³` is part of the statement** (the two windows are
`J`-free, while the low threshold `Θ(a v,J,μ) = −4πμ²(a v)(1−J√(μ(a v)³))` grows
linearly in `J`; for large `J` *every* state is low, so without the bound the
statement is **false** — this is exactly the refutation of the sibling node
`Work.BoseBox.nodeB1_holds`, machine-checked as
`Work.BoseBox.nodeB1_false_of_state` in `nodeB1_holds.lean`, whose test state
`(x 0)₁(x 1)₁(x 2)₁` has `cnPlus = 3‖Φ‖²`).  FS's own line is "for a
`0<J≤K_B³`".  In `nodeB2g_of_data` the bound is discharged for the *fixed* gap
`J'` by the smallness of the diluteness (`K_B³ = (μa³)^{-18/323} → ∞`,
`exists_KB3_ge`). -/
def B2AprioriWindow (v : ℝ³ → ℝ) (h : ScatSol v) (J : ℝ) : Prop :=
  ∃ C₁ ε₀ : ℝ, 0 ≤ C₁ ∧ 0 < ε₀ ∧
    ∀ μ : ℝ, 0 < μ → μ * (a v) ^ 3 ≤ ε₀ →
      ParamsOK (paramsAt μ (a v)) (μ * (a v) ^ 3) →
      J ≤ (paramsAt μ (a v)).KB ^ 3 →
      ∀ n : ℕ, ∀ Φ : CSBox n (sideAt μ (a v)),
        IsLow (paramsAt μ (a v)) μ v h J n Φ →
        cnPlus (sideAt μ (a v)) (Φ : X n → ℝ)
          ≤ C₁ * nPlusWindow (paramsAt μ (a v)) μ (a v)
              * norm2N n (sideAt μ (a v)) (Φ : X n → ℝ)

/-- **FS §6 steps (2)–(4), at the decoupled parameters: the `n₊`-grading of the box
word, its band structure, the `eq:dvapriori` bound and the recombination.**

For every low box state `Φ` (particle number `n` free, box side `ℓ = ℓ(μ)`) there
are a number of blocks `nn`, a Hermitian matrix `A` supported on `iRange nn` (the
matrix of `boxWordU` in the grading `n₊ = ΣᵢQᵢ`), the norm profile `ψv` of `Φ`
(a *unit* vector), and a window length `Mw ∈ [𝓜/4, 𝓜/2]` with `Mw ≤ nn`, such that

* (**energy identity**) `⟨ψv,Aψv⟩·‖Φ‖² = ⟨Φ,H_Λ(μ)Φ⟩`;
* (**band ≤ 2**) `d_k = 0` for `k ≥ 3` — the potential is a two-body operator, so it
  changes `n₊` by at most two;
* (**`eq:dvapriori`**) `|d₁| + |d₂| ≤ Kμ²ℓ³` — FS's bound on the first two
  off-diagonals, the only place `∫v` enters the paper (also part of
  `thm:aprioribounds`);
* (**recombination**) for every unit vector `φ` supported in a window
  `[n₀, n₀+Mw) ⊆ [0,nn]` of `Mw` consecutive indices, a box state `Φ'` *of the same
  centred-box norm*, whose word exceeds `⟨φ,Aφ⟩·‖Φ‖²` by nothing, which is
  **spectrally confined** (`SpectralNPlusLe ℓ 𝓜₂ Φ'` for every `𝓜₂ ≥ n₀+Mw`, FS
  `eq:LocalizedNPlus`), and whose `n₊`-expectation is at least `n₀‖Φ'‖²` (the
  window's *position* is visible in `⟨n₊⟩`, which is what FS's placement argument
  exploits).

This is the chapter's `Work.UBBInputs3.NPlusGrading` at the decoupled parameters —
with the recombination clause strengthened to the spectral form the §8–§11
analysis needs (`NodeRestricted` is stated on `SpectralNPlusLe`), which is exactly
the point of the correction of this node.

**FS's upper bound `J ≤ K_B³` is part of the datum**, exactly as in
`B2AprioriWindow` and for the same reason: the band/`eq:dvapriori` clause is
`J`-free while the low class grows with `J` (for large `J` *every* state is low, by
the mechanism that refutes the sibling node `nodeB1_holds`,
`Work.BoseBox.nodeB1_false_of_state`), and the off-diagonal sums grow with the
particle number, which is free.  For the node's *fixed* `J` the bound is again
automatic at small diluteness (`exists_KB3_ge`). -/
def B2GradingData (v : ℝ³ → ℝ) (h : ScatSol v) (J : ℝ) : Prop :=
  ∃ K ε₀ : ℝ, 0 ≤ K ∧ 0 < ε₀ ∧
    ∀ μ : ℝ, 0 < μ → μ * (a v) ^ 3 ≤ ε₀ →
      ParamsOK (paramsAt μ (a v)) (μ * (a v) ^ 3) →
      J ≤ (paramsAt μ (a v)).KB ^ 3 →
      ∀ n : ℕ, ∀ Φ : CSBox n (sideAt μ (a v)),
        IsLow (paramsAt μ (a v)) μ v h J n Φ →
        ∃ (nn : ℕ) (A : ℤ → ℤ → ℂ) (ψv : ℤ → ℂ) (Mw : ℕ),
          3 ≤ Mw ∧ bigM (paramsAt μ (a v)) (a v) μ / 4 ≤ (Mw : ℝ) ∧
          (Mw : ℝ) ≤ bigM (paramsAt μ (a v)) (a v) μ / 2 ∧ Mw ≤ nn ∧
          (∀ i j, A i j ≠ 0 → i ∈ iRange nn ∧ j ∈ iRange nn) ∧
          (∀ i j, A j i = star (A i j)) ∧
          (∀ j, ψv j ≠ 0 → j ∈ iRange nn) ∧
          normSq (iRange nn) ψv = 1 ∧
          qform A (iRange nn) ψv ψv * norm2N n (sideAt μ (a v)) (Φ : X n → ℝ)
            = boxWordU n (sideAt μ (a v)) μ (paramsAt μ (a v)).d (paramsAt μ (a v)).s
                (paramsAt μ (a v)).eT (paramsAt μ (a v)).b v h 0 (Φ : X n → ℝ) ∧
          (∀ k : ℤ, 3 ≤ k → dk A nn ψv k = 0) ∧
          (|dk A nn ψv 1| + |dk A nn ψv 2| ≤ K * μ ^ 2 * sideAt μ (a v) ^ 3) ∧
          (∀ (n₀ : ℤ) (φ : ℤ → ℂ), 0 ≤ n₀ → n₀ + (Mw : ℤ) ≤ (nn : ℤ) →
            (∀ j, φ j ≠ 0 → n₀ ≤ j ∧ j < n₀ + (Mw : ℤ)) → normSq (iRange nn) φ = 1 →
            ∃ Φ' : CSBox n (sideAt μ (a v)),
              norm2N n (sideAt μ (a v)) (Φ' : X n → ℝ)
                = norm2N n (sideAt μ (a v)) (Φ : X n → ℝ) ∧
              boxWordU n (sideAt μ (a v)) μ (paramsAt μ (a v)).d (paramsAt μ (a v)).s
                  (paramsAt μ (a v)).eT (paramsAt μ (a v)).b v h 0 (Φ' : X n → ℝ)
                ≤ qform A (iRange nn) φ φ * norm2N n (sideAt μ (a v)) (Φ : X n → ℝ) ∧
              (∀ 𝓜₂ : ℝ, (n₀ : ℝ) + (Mw : ℝ) ≤ 𝓜₂ →
                SpectralNPlusLe (sideAt μ (a v)) 𝓜₂ (Φ' : X n → ℝ)) ∧
              (n₀ : ℝ) * norm2N n (sideAt μ (a v)) (Φ' : X n → ℝ)
                ≤ cnPlus (sideAt μ (a v)) (Φ' : X n → ℝ))

/-! ## 2. The arithmetic of the §6 proof

Both inequalities below are comparisons of powers of the diluteness `t = μa³`; at
FS's parameter choice *every* exponent is an integer multiple of `1/646 = 1/(2·323)`
(`fsXp`), and the two windows are `nPlusWindow = (μa³)^{-51/646}`,
`𝓜 = K_M(μa³)^{-1/4} = (μa³)^{-327/1292}`. -/

/-- **The Lieb–Solovej error is paid by the a-priori threshold gap.**  FS
`eq:EnergyBound`'s loss, in the form `8000 K μ²ℓ³𝓜^{-2}` it takes in
`nodeB2g_of_data` (the factor `8000 = (100/Mw²)·5·16` with `Mw ≥ 𝓜/4` and
`|d₁| + 4|d₂| ≤ 5Kμ²ℓ³`), is dominated by
`4πaμ²ℓ³(J'−J)(μa³)^{1/2} = ℓ³(Θ(a,J',μ) − Θ(a,J,μ))` — the amount by which
raising the threshold from `J` to `J'` enlarges the low class.  Since
`𝓜^{-2} = (μa³)^{327/646} = (μa³)^{2/323}(μa³)^{1/2}` and `(μa³)^{2/323} → 0`, any
fixed gap `J' − J > 0` pays the error for small diluteness. -/
lemma exists_lsError_paid {a Kg J J' : ℝ} (ha : 0 < a) (hK : 0 ≤ Kg) (hJJ : J < J') :
    ∃ ε : ℝ, 0 < ε ∧ ∀ μ : ℝ, 0 < μ → μ * a ^ 3 ≤ ε →
      8000 * Kg / bigM (paramsAt μ a) a μ ^ 2
        ≤ 4 * π * a * (J' - J) * (μ * a ^ 3) ^ (1 / 2 : ℝ) := by
  have hB : 0 < 4 * π * a * (J' - J) := by
    have h1 : 0 < J' - J := by linarith
    positivity
  refine ⟨min 1 ((4 * π * a * (J' - J) / (8000 * Kg + 1)) ^ (323 / 2 : ℝ)),
    lt_min one_pos (Real.rpow_pos_of_pos (by positivity) _), ?_⟩
  intro μ hμ hle
  have ht : 0 < μ * a ^ 3 := by positivity
  have hle' : μ * a ^ 3 ≤ (4 * π * a * (J' - J) / (8000 * Kg + 1)) ^ (323 / 2 : ℝ) :=
    le_trans hle (min_le_right _ _)
  have hte : (μ * a ^ 3) ^ (2 / 323 : ℝ) ≤ 4 * π * a * (J' - J) / (8000 * Kg + 1) := by
    have h1 : (μ * a ^ 3) ^ (2 / 323 : ℝ)
        ≤ ((4 * π * a * (J' - J) / (8000 * Kg + 1)) ^ (323 / 2 : ℝ)) ^ (2 / 323 : ℝ) :=
      Real.rpow_le_rpow ht.le hle' (by norm_num)
    have h2 : ((4 * π * a * (J' - J) / (8000 * Kg + 1)) ^ (323 / 2 : ℝ)) ^ (2 / 323 : ℝ)
        = 4 * π * a * (J' - J) / (8000 * Kg + 1) := by
      rw [← Real.rpow_mul (by positivity)]
      norm_num
    linarith [h2]
  have hKt : 8000 * Kg * (μ * a ^ 3) ^ (2 / 323 : ℝ) ≤ 4 * π * a * (J' - J) := by
    have hden : 0 < 8000 * Kg + 1 := by linarith
    have h1 : 8000 * Kg * (μ * a ^ 3) ^ (2 / 323 : ℝ)
        ≤ 8000 * Kg * (4 * π * a * (J' - J) / (8000 * Kg + 1)) :=
      mul_le_mul_of_nonneg_left hte (by linarith)
    have h2 : 8000 * Kg * (4 * π * a * (J' - J) / (8000 * Kg + 1))
        ≤ 4 * π * a * (J' - J) := by
      rw [mul_div_assoc', div_le_iff₀ hden]
      nlinarith [hB]
    linarith
  have hbig : 1 / bigM (paramsAt μ a) a μ ^ 2 = (μ * a ^ 3) ^ (327 / 646 : ℝ) := by
    rw [inv_bigM_sq_paramsAt hμ ha]
    dsimp [fsXp]
    congr 1
    norm_num
  have hsplit : (μ * a ^ 3) ^ (327 / 646 : ℝ)
      = (μ * a ^ 3) ^ (2 / 323 : ℝ) * (μ * a ^ 3) ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_add ht]
    congr 1
    norm_num
  rw [show 8000 * Kg / bigM (paramsAt μ a) a μ ^ 2
      = 8000 * Kg * (1 / bigM (paramsAt μ a) a μ ^ 2) by ring, hbig, hsplit]
  calc 8000 * Kg * ((μ * a ^ 3) ^ (2 / 323 : ℝ) * (μ * a ^ 3) ^ (1 / 2 : ℝ))
      = (8000 * Kg * (μ * a ^ 3) ^ (2 / 323 : ℝ)) * (μ * a ^ 3) ^ (1 / 2 : ℝ) := by ring
    _ ≤ (4 * π * a * (J' - J)) * (μ * a ^ 3) ^ (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_right hKt (Real.rpow_nonneg ht.le _)
    _ = 4 * π * a * (J' - J) * (μ * a ^ 3) ^ (1 / 2 : ℝ) := by ring

/-- **The window placement: `C·nPlusWindow ≤ 𝓜/2` for small diluteness.**  FS's
step "the interval of `n₊` values in `Ψ̃` must be contained in
`[0, 𝓜' + CK_B³K_ℓ⁵] ⊆ [0,𝓜]` by `con:KBellKM`", with the constants explicit:
`nPlusWindow = (μa³)^{-51/646}` versus `𝓜 = (μa³)^{-327/1292}`, a margin
`(μa³)^{225/1292}` which dominates any fixed constant `C`. -/
lemma exists_place_le_halfM {a C : ℝ} (ha : 0 < a) (hC : 0 ≤ C) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ μ : ℝ, 0 < μ → μ * a ^ 3 ≤ ε →
      C * nPlusWindow (paramsAt μ a) μ a ≤ bigM (paramsAt μ a) a μ / 2 := by
  rcases eq_or_lt_of_le hC with h0 | hpos
  · refine ⟨1, one_pos, fun μ hμ _ => ?_⟩
    rw [← h0, zero_mul]
    exact div_nonneg (bigM_pos_of_params hμ ha).le (by norm_num)
  · have h2C : 0 < 2 * C := by linarith
    refine ⟨min 1 ((1 / (2 * C)) ^ (1292 / 225 : ℝ)),
      lt_min one_pos (Real.rpow_pos_of_pos (by positivity) _), ?_⟩
    intro μ hμ hle
    have ht : 0 < μ * a ^ 3 := by positivity
    have hle' : μ * a ^ 3 ≤ (1 / (2 * C)) ^ (1292 / 225 : ℝ) := le_trans hle (min_le_right _ _)
    have hte : (μ * a ^ 3) ^ (225 / 1292 : ℝ) ≤ 1 / (2 * C) := by
      have h1 : (μ * a ^ 3) ^ (225 / 1292 : ℝ)
          ≤ ((1 / (2 * C)) ^ (1292 / 225 : ℝ)) ^ (225 / 1292 : ℝ) :=
        Real.rpow_le_rpow ht.le hle' (by norm_num)
      have h2 : ((1 / (2 * C)) ^ (1292 / 225 : ℝ)) ^ (225 / 1292 : ℝ) = 1 / (2 * C) := by
        rw [← Real.rpow_mul (by positivity)]
        norm_num
      linarith [h2]
    have hCt : C ≤ (1 / 2) * ((μ * a ^ 3) ^ (225 / 1292 : ℝ))⁻¹ := by
      have hstep : C * (μ * a ^ 3) ^ (225 / 1292 : ℝ) ≤ 1 / 2 := by
        have h3 := mul_le_mul_of_nonneg_left hte hC
        have h4 : C * (1 / (2 * C)) = 1 / 2 := by field_simp
        linarith [h3, h4]
      calc C = C * (μ * a ^ 3) ^ (225 / 1292 : ℝ) * ((μ * a ^ 3) ^ (225 / 1292 : ℝ))⁻¹ := by
            field_simp
        _ ≤ (1 / 2) * ((μ * a ^ 3) ^ (225 / 1292 : ℝ))⁻¹ :=
            mul_le_mul_of_nonneg_right hstep (by positivity)
    have hinv : ((μ * a ^ 3) ^ (225 / 1292 : ℝ))⁻¹ = (μ * a ^ 3) ^ (-(225 / 1292) : ℝ) := by
      rw [Real.rpow_neg ht.le]
    rw [nPlusWindow_paramsAt hμ ha, bigM_paramsAt hμ ha,
      show fsXp (μ * a ^ 3) (-(51 / 2)) = (μ * a ^ 3) ^ (-(51 / 646) : ℝ) from by
        dsimp [fsXp]; congr 1; norm_num,
      show fsXp (μ * a ^ 3) (-(327 / 4)) = (μ * a ^ 3) ^ (-(327 / 1292) : ℝ) from by
        dsimp [fsXp]; congr 1; norm_num]
    calc C * (μ * a ^ 3) ^ (-(51 / 646) : ℝ)
        ≤ ((1 / 2) * (μ * a ^ 3) ^ (-(225 / 1292) : ℝ)) * (μ * a ^ 3) ^ (-(51 / 646) : ℝ) := by
          rw [← hinv]
          exact mul_le_mul_of_nonneg_right hCt (Real.rpow_nonneg ht.le _)
      _ = (1 / 2) * ((μ * a ^ 3) ^ (-(225 / 1292) : ℝ) * (μ * a ^ 3) ^ (-(51 / 646) : ℝ)) := by
          ring
      _ = (1 / 2) * (μ * a ^ 3) ^ (-(327 / 1292) : ℝ) := by
          rw [← Real.rpow_add ht]
          congr 1
          norm_num
      _ = (μ * a ^ 3) ^ (-(327 / 1292) : ℝ) / 2 := by ring

/-- **The Lieb–Solovej error in absolute terms**: `(100/Mw²)(|d₁| + 4|d₂|) ≤
8000Kμ²ℓ³𝓜^{-2}` as soon as `Mw ≥ 𝓜/4` and `|d₁| + 4|d₂| ≤ 5Kμ²ℓ³` (the
`eq:dvapriori` bound `|d₁| + |d₂| ≤ Kμ²ℓ³` gives the `5`). -/
lemma lsError_abs_le {Kg μ ℓ 𝓜 : ℝ} {Mw nn : ℕ} {A : ℤ → ℤ → ℂ} {ψv : ℤ → ℂ}
    (h𝓜 : 0 < 𝓜) (hMwlo : 𝓜 / 4 ≤ (Mw : ℝ))
    (hdv5 : |dk A nn ψv 1| + 4 * |dk A nn ψv 2| ≤ 5 * (Kg * μ ^ 2 * ℓ ^ 3)) :
    (100 / (Mw : ℝ) ^ 2) * (|dk A nn ψv 1| + 4 * |dk A nn ψv 2|)
      ≤ 8000 * Kg * μ ^ 2 * ℓ ^ 3 / 𝓜 ^ 2 := by
  have hMwpos : 0 < (Mw : ℝ) := by linarith
  have hMsq : (𝓜 / 4) ^ 2 ≤ (Mw : ℝ) ^ 2 := by nlinarith [hMwlo, h𝓜]
  have h100 : 100 / (Mw : ℝ) ^ 2 ≤ 100 / (𝓜 / 4) ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) hMsq
  have h100' : 100 / (𝓜 / 4) ^ 2 = 1600 / 𝓜 ^ 2 := by
    field_simp
    ring
  have hY : 0 ≤ 5 * (Kg * μ ^ 2 * ℓ ^ 3) := by
    have h1 : (0 : ℝ) ≤ |dk A nn ψv 1| + 4 * |dk A nn ψv 2| := by positivity
    linarith [hdv5, h1]
  calc (100 / (Mw : ℝ) ^ 2) * (|dk A nn ψv 1| + 4 * |dk A nn ψv 2|)
      ≤ (100 / (Mw : ℝ) ^ 2) * (5 * (Kg * μ ^ 2 * ℓ ^ 3)) :=
        mul_le_mul_of_nonneg_left hdv5 (by positivity)
    _ ≤ (1600 / 𝓜 ^ 2) * (5 * (Kg * μ ^ 2 * ℓ ^ 3)) := by
        rw [← h100']
        exact mul_le_mul_of_nonneg_right h100 hY
    _ = 8000 * Kg * μ ^ 2 * ℓ ^ 3 / 𝓜 ^ 2 := by ring

/-- **The threshold gap pays the Lieb–Solovej error**: multiplying
`8000K/𝓜² ≤ 4πa(J'−J)(μa³)^{1/2}` by `μ²ℓ³ ≥ 0` gives the absolute form used in
the reduction. -/
lemma threshold_pays {a Kg μ ℓ 𝓜 J J' : ℝ} (hμ : 0 ≤ μ) (hℓ : 0 ≤ ℓ)
    (h : 8000 * Kg / 𝓜 ^ 2 ≤ 4 * π * a * (J' - J) * (μ * a ^ 3) ^ (1 / 2 : ℝ)) :
    8000 * Kg * μ ^ 2 * ℓ ^ 3 / 𝓜 ^ 2
      ≤ ℓ ^ 3 * 4 * π * μ ^ 2 * a * (J' - J) * (μ * a ^ 3) ^ (1 / 2 : ℝ) := by
  have h1 := mul_le_mul_of_nonneg_right h (by positivity : (0:ℝ) ≤ μ ^ 2 * ℓ ^ 3)
  have h2 : 8000 * Kg / 𝓜 ^ 2 * (μ ^ 2 * ℓ ^ 3) = 8000 * Kg * μ ^ 2 * ℓ ^ 3 / 𝓜 ^ 2 := by ring
  have h3 : (4 * π * a * (J' - J) * (μ * a ^ 3) ^ (1 / 2 : ℝ)) * (μ ^ 2 * ℓ ^ 3)
      = ℓ ^ 3 * 4 * π * μ ^ 2 * a * (J' - J) * (μ * a ^ 3) ^ (1 / 2 : ℝ) := by ring
  linarith [h1, h2, h3]

/-- **The a-priori threshold gap**: `ℓ³(Θ(a,J',μ) − Θ(a,J,μ)) = 4πaμ²ℓ³(J'−J)√(μa³)`
(`Θ` is `eq:aprioriPsi`'s threshold, increasing in `J`). -/
lemma theta_gap (a ℓ μ J J' : ℝ) :
    ℓ ^ 3 * Theta a J' μ - ℓ ^ 3 * Theta a J μ
      = ℓ ^ 3 * 4 * π * μ ^ 2 * a * (J' - J) * (μ * a ^ 3) ^ (1 / 2 : ℝ) := by
  have hsq : Real.sqrt (μ * a ^ 3) = (μ * a ^ 3) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
  have hkey : Theta a J' μ - Theta a J μ
      = 4 * π * μ ^ 2 * a * Real.sqrt (μ * a ^ 3) * (J' - J) := by
    dsimp [Theta]
    ring
  rw [← mul_sub, hkey, hsq]
  ring

/-- **FS's upper bound on the a-priori parameter is automatic for fixed `J'`**: since
`K_B = (μa³)^{-6/323}` at FS's choice, `K_B³ = (μa³)^{-18/323} → ∞`, so for every fixed
`J' > 0` and every sufficiently small diluteness `μa³`, `J' ≤ K_B³`.  (This is the
reason the corrected §5 input `B2AprioriWindow` — with FS's bound `J ≤ K_B³` inside —
is applicable to the *fixed* raised threshold `J'` of `NodeB2g`.) -/
lemma exists_KB3_ge {a J' : ℝ} (ha : 0 < a) (hJ' : 0 < J') :
    ∃ ε : ℝ, 0 < ε ∧ ∀ μ : ℝ, 0 < μ → μ * a ^ 3 ≤ ε →
      J' ≤ (paramsAt μ a).KB ^ 3 := by
  refine ⟨min 1 (J' ^ (-(323 / 18) : ℝ)), lt_min one_pos (Real.rpow_pos_of_pos hJ' _), ?_⟩
  intro μ hμ hle
  have ht : 0 < μ * a ^ 3 := by positivity
  have hle' : μ * a ^ 3 ≤ J' ^ (-(323 / 18) : ℝ) := le_trans hle (min_le_right _ _)
  have hKB : (paramsAt μ a).KB = fsXp (μ * a ^ 3) (-6) := rfl
  have hcube : (fsXp (μ * a ^ 3) (-6)) ^ 3 = fsXp (μ * a ^ 3) (-18) := by
    rw [fsXp_pow ht.le]
    norm_num
  have hrp : fsXp (μ * a ^ 3) (-18) = (μ * a ^ 3) ^ (-(18 / 323) : ℝ) := by
    dsimp [fsXp]
    congr 1
    norm_num
  have hkey : (J' ^ (-(323 / 18) : ℝ)) ^ (-(18 / 323) : ℝ) = J' := by
    rw [← Real.rpow_mul hJ'.le]
    norm_num
  rw [hKB, hcube, hrp]
  calc J' = (J' ^ (-(323 / 18) : ℝ)) ^ (-(18 / 323) : ℝ) := hkey.symm
    _ ≤ (μ * a ^ 3) ^ (-(18 / 323) : ℝ) :=
        Real.rpow_le_rpow_of_nonpos ht hle' (by norm_num)

/-! ## 3. The reduction: FS §6 from the two inputs -/

/-- **`NodeB2g` from the two inputs** — FS §6 `lem:LocMatrices`, with the
Lieb–Solovej matrix theorem `ls_localisation_band2` (proved in this workspace)
doing the linear algebra, and nothing else assumed.

The proof is FS's, verbatim:

1. apply `ls_localisation_band2` to the matrix `A` of the grading at window length
   `Mw ≤ 𝓜/2`: there is a unit vector `φ` supported in a window `[n₀, n₀+Mw)` with
   `⟨φ,Aφ⟩ ≤ ⟨ψ,Aψ⟩ + (100/Mw²)(|d₁| + 4|d₂|)`;
2. recombine `φ` into a box state `Φ'` of the same centred-box norm and word
   `≤ ⟨φ,Aφ⟩‖Φ‖²`, spectrally confined to the window and with
   `n₀‖Φ'‖² ≤ ⟨n₊⟩(Φ')`;
3. `Φ'` is *low at the raised threshold* `J'`: its word exceeds `Φ`'s by at most the
   Lieb–Solovej error `8000Kμ²ℓ³𝓜^{-2}`, which the threshold gap
   `ℓ³(Θ(J')−Θ(J))` pays (`exists_lsError_paid`);
4. FS's placement: the a-priori window at `J'` (`B2AprioriWindow`, applied to
   `Φ'`, which is low at `J'`) gives `n₀ ≤ C₁nPlusWindow ≤ 𝓜/2`
   (`exists_place_le_halfM`), hence `n₀ + Mw ≤ 𝓜` and the spectral confinement
   `SpectralNPlusLe ℓ 𝓜 Φ'` follows from the recombination clause;
5. the error constant is `K = 8000K_{dv}` and `ε₀` the minimum of the five
   smallness thresholds. -/
theorem nodeB2g_of_data {v : ℝ³ → ℝ} {h : ScatSol v} {J J' : ℝ}
    (hav : 0 < a v) (hlhy : lhyC ≤ J) (hJJ : J < J')
    (hg : B2GradingData v h J) (ha : B2AprioriWindow v h J') :
    NodeB2g v h J J' := by
  obtain ⟨Kg, εg, hKg, hεg, hgd⟩ := hg
  obtain ⟨C₁, εa, hC₁, hεa, haw⟩ := ha
  have hlhypos : 0 < lhyC := by
    dsimp [lhyC]
    positivity
  have hJpos : 0 < J := by linarith
  have hJ'pos : 0 < J' := by linarith
  obtain ⟨εs, hεs, hpaid⟩ := exists_lsError_paid (a := a v) hav hKg hJJ
  obtain ⟨εw, hεw, hplace⟩ := exists_place_le_halfM (a := a v) hav hC₁
  obtain ⟨εk, hεk, hkb⟩ := exists_KB3_ge (a := a v) hav hJ'pos
  obtain ⟨εj, hεj, hjb⟩ := exists_KB3_ge (a := a v) hav hJpos
  refine ⟨8000 * Kg,
    min (min εg εa) (min εs (min εw (min (min εk εj) 1))), by positivity,
    lt_min (lt_min hεg hεa)
      (lt_min hεs (lt_min hεw (lt_min (lt_min hεk hεj) one_pos))), ?_⟩
  intro μ hμ hle hpar n Φ hlow
  have ht1 : μ * (a v) ^ 3 ≤ εg :=
    le_trans hle (le_trans (min_le_left _ _) (min_le_left _ _))
  have ht2 : μ * (a v) ^ 3 ≤ εa :=
    le_trans hle (le_trans (min_le_left _ _) (min_le_right _ _))
  have ht3 : μ * (a v) ^ 3 ≤ εs :=
    le_trans hle (le_trans (min_le_right _ _) (min_le_left _ _))
  have ht4 : μ * (a v) ^ 3 ≤ εw :=
    le_trans hle (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_left _ _)))
  have ht5 : μ * (a v) ^ 3 ≤ εk :=
    le_trans hle (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_left _ _) (min_le_left _ _)))))
  have ht6 : μ * (a v) ^ 3 ≤ εj :=
    le_trans hle (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_left _ _) (min_le_right _ _)))))
  obtain ⟨nn, A, ψv, Mw, hMw3, hMwlo, hMwhi, hMwnn, hAsupp, hAherm, hψsupp, hψnorm,
    hE, hband, hdv, hrec⟩ := hgd μ hμ ht1 hpar (hjb μ hμ ht6) n Φ hlow
  obtain ⟨n₀, h0, h1, φ, hsupp, hφnorm, hineq⟩ :=
    ls_localisation_band2 A nn Mw ψv hMw3 hMwnn hAsupp hAherm hψsupp hψnorm hband
  obtain ⟨Φ', hnorm', hword', hspec', hlowwin'⟩ := hrec n₀ φ h0 h1 hsupp hφnorm
  -- (0) basic positivity
  have hKl : 0 < (paramsAt μ (a v)).Kl := by
    rw [paramsAt]
    dsimp [fsParams, fsXp]
    exact Real.rpow_pos_of_pos (by positivity) _
  have hMpos : 0 < bigM (paramsAt μ (a v)) (a v) μ := bigM_pos_of_params hμ hav
  have hN : 0 ≤ norm2N n (sideAt μ (a v)) (Φ : X n → ℝ) := by
    dsimp [norm2N]
    exact integral_nonneg (fun x => sq_nonneg _)
  have hNpos : 0 < norm2N n (sideAt μ (a v)) (Φ : X n → ℝ) := by
    simpa [norm2N, sideAt] using Φ.sq_pos
  -- (1) the Lieb–Solovej error, absolute form
  have hdv5 : |dk A nn ψv 1| + 4 * |dk A nn ψv 2|
      ≤ 5 * (Kg * μ ^ 2 * sideAt μ (a v) ^ 3) := by
    linarith [hdv, abs_nonneg (dk A nn ψv 1), abs_nonneg (dk A nn ψv 2)]
  have hlerr := lsError_abs_le (ℓ := sideAt μ (a v))
    (𝓜 := bigM (paramsAt μ (a v)) (a v) μ) hMpos hMwlo hdv5
  -- (2) the word of the recombination, against `Φ`
  have hword : boxWordU n (sideAt μ (a v)) μ (paramsAt μ (a v)).d (paramsAt μ (a v)).s
        (paramsAt μ (a v)).eT (paramsAt μ (a v)).b v h 0 (Φ' : X n → ℝ)
      ≤ boxWordU n (sideAt μ (a v)) μ (paramsAt μ (a v)).d (paramsAt μ (a v)).s
          (paramsAt μ (a v)).eT (paramsAt μ (a v)).b v h 0 (Φ : X n → ℝ)
        + 8000 * Kg * μ ^ 2 * sideAt μ (a v) ^ 3
            / bigM (paramsAt μ (a v)) (a v) μ ^ 2 * norm2N n (sideAt μ (a v)) (Φ : X n → ℝ) := by
    have hineq' : qform A (iRange nn) φ φ ≤ qform A (iRange nn) ψv ψv
        + 8000 * Kg * μ ^ 2 * sideAt μ (a v) ^ 3
            / bigM (paramsAt μ (a v)) (a v) μ ^ 2 := by
      linarith [hineq, hlerr]
    have h1 := mul_le_mul_of_nonneg_right hineq' hN
    have h2 : (qform A (iRange nn) ψv ψv
          + 8000 * Kg * μ ^ 2 * sideAt μ (a v) ^ 3
              / bigM (paramsAt μ (a v)) (a v) μ ^ 2)
          * norm2N n (sideAt μ (a v)) (Φ : X n → ℝ)
        = boxWordU n (sideAt μ (a v)) μ (paramsAt μ (a v)).d (paramsAt μ (a v)).s
            (paramsAt μ (a v)).eT (paramsAt μ (a v)).b v h 0 (Φ : X n → ℝ)
          + 8000 * Kg * μ ^ 2 * sideAt μ (a v) ^ 3
              / bigM (paramsAt μ (a v)) (a v) μ ^ 2 * norm2N n (sideAt μ (a v)) (Φ : X n → ℝ) := by
      calc (qform A (iRange nn) ψv ψv
            + 8000 * Kg * μ ^ 2 * sideAt μ (a v) ^ 3
                / bigM (paramsAt μ (a v)) (a v) μ ^ 2)
            * norm2N n (sideAt μ (a v)) (Φ : X n → ℝ)
          = qform A (iRange nn) ψv ψv * norm2N n (sideAt μ (a v)) (Φ : X n → ℝ)
            + 8000 * Kg * μ ^ 2 * sideAt μ (a v) ^ 3
                / bigM (paramsAt μ (a v)) (a v) μ ^ 2 * norm2N n (sideAt μ (a v)) (Φ : X n → ℝ) := by
            ring
        _ = boxWordU n (sideAt μ (a v)) μ (paramsAt μ (a v)).d (paramsAt μ (a v)).s
              (paramsAt μ (a v)).eT (paramsAt μ (a v)).b v h 0 (Φ : X n → ℝ)
            + 8000 * Kg * μ ^ 2 * sideAt μ (a v) ^ 3
                / bigM (paramsAt μ (a v)) (a v) μ ^ 2 * norm2N n (sideAt μ (a v)) (Φ : X n → ℝ) := by
            rw [hE]
    linarith [hword', h1, h2]
  -- (3) `Φ'` is low at the raised threshold `J'`
  have hlow' : IsLow (paramsAt μ (a v)) μ v h J' n Φ' := by
    have hlowΦ : boxWordU n (sideAt μ (a v)) μ (paramsAt μ (a v)).d (paramsAt μ (a v)).s
        (paramsAt μ (a v)).eT (paramsAt μ (a v)).b v h 0 (Φ : X n → ℝ)
        ≤ lowLevel (paramsAt μ (a v)) μ v J * norm2N n (sideAt μ (a v)) (Φ : X n → ℝ) :=
      hlow
    have hpay : 8000 * Kg * μ ^ 2 * sideAt μ (a v) ^ 3
          / bigM (paramsAt μ (a v)) (a v) μ ^ 2
        ≤ sideAt μ (a v) ^ 3 * 4 * π * μ ^ 2 * (a v) * (J' - J)
            * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ) :=
      threshold_pays hμ.le (boxSide_pos hμ hav hKl).le (hpaid μ hμ ht3)
    have hdΘ := theta_gap (a v) (sideAt μ (a v)) μ J J'
    have hgoal : boxWordU n (sideAt μ (a v)) μ (paramsAt μ (a v)).d (paramsAt μ (a v)).s
          (paramsAt μ (a v)).eT (paramsAt μ (a v)).b v h 0 (Φ : X n → ℝ)
          + 8000 * Kg * μ ^ 2 * sideAt μ (a v) ^ 3
              / bigM (paramsAt μ (a v)) (a v) μ ^ 2 * norm2N n (sideAt μ (a v)) (Φ : X n → ℝ)
        ≤ sideAt μ (a v) ^ 3 * Theta (a v) J' μ
            * norm2N n (sideAt μ (a v)) (Φ : X n → ℝ) := by
      have h2 : 8000 * Kg * μ ^ 2 * sideAt μ (a v) ^ 3
            / bigM (paramsAt μ (a v)) (a v) μ ^ 2 * norm2N n (sideAt μ (a v)) (Φ : X n → ℝ)
          ≤ (sideAt μ (a v) ^ 3 * Theta (a v) J' μ - sideAt μ (a v) ^ 3 * Theta (a v) J μ)
              * norm2N n (sideAt μ (a v)) (Φ : X n → ℝ) := by
        rw [hdΘ]
        exact mul_le_mul_of_nonneg_right hpay hN
      have hlowLevel : lowLevel (paramsAt μ (a v)) μ v J
          = sideAt μ (a v) ^ 3 * Theta (a v) J μ := rfl
      nlinarith [hlowΦ, h2, hN]
    have hfinal : boxWordU n (sideAt μ (a v)) μ (paramsAt μ (a v)).d (paramsAt μ (a v)).s
          (paramsAt μ (a v)).eT (paramsAt μ (a v)).b v h 0 (Φ' : X n → ℝ)
        ≤ lowLevel (paramsAt μ (a v)) μ v J' * norm2N n (sideAt μ (a v)) (Φ' : X n → ℝ) := by
      have hlvl : lowLevel (paramsAt μ (a v)) μ v J'
          = sideAt μ (a v) ^ 3 * Theta (a v) J' μ := rfl
      rw [hlvl, hnorm']
      linarith [hword, hgoal]
    exact hfinal
  -- (4) FS's placement of the window
  have hcn := haw μ hμ ht2 hpar (hkb μ hμ ht5) n Φ' hlow'
  have hinst : (n₀ : ℝ) * norm2N n (sideAt μ (a v)) (Φ' : X n → ℝ)
      ≤ (C₁ * nPlusWindow (paramsAt μ (a v)) μ (a v))
          * norm2N n (sideAt μ (a v)) (Φ' : X n → ℝ) := le_trans hlowwin' hcn
  have hNpos' : 0 < norm2N n (sideAt μ (a v)) (Φ' : X n → ℝ) := by
    rw [hnorm']
    exact hNpos
  have hn₀ : (n₀ : ℝ) ≤ C₁ * nPlusWindow (paramsAt μ (a v)) μ (a v) :=
    le_of_mul_le_mul_right hinst hNpos'
  have hplace' := hplace μ hμ ht4
  have hwin : (n₀ : ℝ) + (Mw : ℝ) ≤ bigM (paramsAt μ (a v)) (a v) μ := by
    linarith [hn₀, hplace', hMwhi]
  exact ⟨Φ', hlow', hnorm', hword, hspec' _ hwin⟩

/-! ## 4. The dependency on the §5 node, and the statement proposal

The sibling §5 node of this chapter (`Nodes.NodeB1`, its prover's verdict
`declare_false` recorded in `nodeB1_holds.lean`) is **false as stated**: it carries only
`lhyC ≤ J`, no upper bound on the a-priori parameter, and for large `J` every state is
low while both windows are `J`-free (`nodeB1_false_of_state`).  The corrected node
carries FS's own `0 < J ≤ K_B³`; `NodeB1KB` below is that statement, and
`B2AprioriWindow_of_NodeB1KB` shows that its second clause is exactly the §5 input §6
needs.  This is what a caller must close *before* `nodeB2g_spectral_holds`. -/

/-- **The corrected §5 node**: `NodeB1` with FS's upper bound `J ≤ K_B³` (FS
`thm:aprioribounds`: "for a `0<J≤K_B³`") inserted in the quantifier, i.e. the repair
demanded by the refutation `nodeB1_false_of_state` of `nodeB1_holds`. -/
def NodeB1KB (v : ℝ³ → ℝ) (h : ScatSol v) (J : ℝ) : Prop :=
  ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧
    ∀ μ : ℝ, 0 < μ → ParamsOK (paramsAt μ (a v)) (μ * (a v) ^ 3) →
      J ≤ (paramsAt μ (a v)).KB ^ 3 →
      ∀ n : ℕ, ∀ Φ : CSBox n (sideAt μ (a v)),
        IsLow (paramsAt μ (a v)) μ v h J n Φ →
        (|(n : ℝ) - μ * sideAt μ (a v) ^ 3| ≤ C₁ * (1 + nWindow (paramsAt μ (a v)) μ (a v))) ∧
        (cnPlus (sideAt μ (a v)) (Φ : X n → ℝ)
          ≤ (C₂ * nPlusWindow (paramsAt μ (a v)) μ (a v) + 1)
            * norm2N n (sideAt μ (a v)) (Φ : X n → ℝ))

/-- **The §5 input of §6 from the corrected §5 node.**  `NodeB1KB`'s second clause is
`cnPlus ℓ Φ ≤ (nPlusWindow + 1)‖Φ‖²`; since `nPlusWindow ≥ 1` for `μa³ ≤ 1` this is the
window `2(C₁+1)·nPlusWindow‖Φ‖²` of `B2AprioriWindow`. -/
lemma B2AprioriWindow_of_NodeB1KB {v : ℝ³ → ℝ} {h : ScatSol v} {J : ℝ} (hav : 0 < a v)
    (h1 : NodeB1KB v h J) : B2AprioriWindow v h J := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hN1⟩ := h1
  refine ⟨C₂ + 1, 1, by positivity, one_pos, ?_⟩
  intro μ hμ hsmall hpar hKB n Φ hlow
  obtain ⟨-, hcn⟩ := hN1 μ hμ hpar hKB n Φ hlow
  have hwin1 : 1 ≤ nPlusWindow (paramsAt μ (a v)) μ (a v) := by
    rw [nPlusWindow_paramsAt hμ hav]
    have hle := fsXp_le_fsXp (t := μ * (a v) ^ 3) (a := 0) (b := -(51 / 2))
      (by positivity) hsmall (by norm_num)
    simpa [fsXp] using hle
  have hN : 0 ≤ norm2N n (sideAt μ (a v)) (Φ : X n → ℝ) := by
    dsimp [norm2N]
    exact integral_nonneg (fun x => sq_nonneg _)
  have hcoef : C₂ * nPlusWindow (paramsAt μ (a v)) μ (a v) + 1
      ≤ (C₂ + 1) * nPlusWindow (paramsAt μ (a v)) μ (a v) := by
    nlinarith [hwin1, hC₂]
  calc cnPlus (sideAt μ (a v)) (Φ : X n → ℝ)
      ≤ (C₂ * nPlusWindow (paramsAt μ (a v)) μ (a v) + 1)
          * norm2N n (sideAt μ (a v)) (Φ : X n → ℝ) := hcn
    _ ≤ ((C₂ + 1) * nPlusWindow (paramsAt μ (a v)) μ (a v))
          * norm2N n (sideAt μ (a v)) (Φ : X n → ℝ) :=
        mul_le_mul_of_nonneg_right hcoef hN
    _ = (C₂ + 1) * nPlusWindow (paramsAt μ (a v)) μ (a v)
          * norm2N n (sideAt μ (a v)) (Φ : X n → ℝ) := by ring

/-- **The §6 node from the corrected §5 node and the grading datum** — the exact
dependency of `nodeB2g_spectral_holds`: it needs the corrected `NodeB1KB` **at the
raised threshold** (the a-priori window applied to the output state, which is what
places the Lieb–Solovej window at `[0,𝓜]`), together with the `n₊`-grading of the box
word.  Nothing else. -/
theorem nodeB2g_of_nodeB1KB_and_data {v : ℝ³ → ℝ} {h : ScatSol v} {J J' : ℝ}
    (hav : 0 < a v) (hlhy : lhyC ≤ J) (hJJ : J < J')
    (hB1 : NodeB1KB v h J') (hg : B2GradingData v h J) :
    NodeB2g v h J J' :=
  nodeB2g_of_data hav hlhy hJJ hg (B2AprioriWindow_of_NodeB1KB hav hB1)

/-- **The statement proposal** (FS's standing assumptions restored): with the
hypotheses of the paper's Theorem 1.1 (`0 ≤ v`, `MemLp v 1`, radial, compact support —
the list the chapter's own `nodeB1_holds`, `CFibreAmb_holds`, `compareBox_of_inputs`
carry), the §6 node follows from the two inputs; this is the shape in which the node is
provable, since the localised kernels `w_u` and the `∫v`-estimate `eq:dvapriori` that
the inputs need are only available under those assumptions. -/
theorem nodeB2g_of_data_fs {v : ℝ³ → ℝ} {h : ScatSol v} {J J' : ℝ} (hv : 0 ≤ v)
    (hvrad : _root_.BoseGases.IsRadial v) (hav : 0 < a v) (hlhy : lhyC ≤ J) (hJJ : J < J')
    (hg : B2GradingData v h J) (ha : B2AprioriWindow v h J') :
    NodeB2g v h J J' :=
  nodeB2g_of_data hav hlhy hJJ hg ha

/-! ## The §5 node `NodeB1` fed into §6

`Work.BoseBox.B2AprioriWindow` (the a-priori `n₊`-window at the raised threshold) is the
*only* §5 input of the §6 reduction `nodeB2g_of_data`.  It is the second conjunct of the
chapter's §5 node `Work.BoseBox.NodeB1` (`Nodes.lean`), with the free constant adjusted:
for `μa³ ≤ ε₀ ≤ 1` one has `nPlusWindow ≥ 1`, hence
`C₂·nPlusWindow + 1 ≤ (C₂+1)·nPlusWindow`.  This lemma is the glue that lets a proof of
`NodeB1` (the a-priori block of FS §5 / App. `SmallBoxes`) feed the §6 replacement. -/
lemma B2AprioriWindow_of_NodeB1 {v : ℝ³ → ℝ} {h : ScatSol v} {J : ℝ} (hav : 0 < a v)
    (h1 : NodeB1 v h J) : B2AprioriWindow v h J := by
  obtain ⟨C₁, C₂, ε₀, hC₁, hC₂, hε₀, hN1⟩ := h1
  refine ⟨C₂ + 1, min ε₀ 1, by positivity, lt_min hε₀ one_pos, ?_⟩
  intro μ hμ hsmall hpar hKB n Φ hlow
  obtain ⟨-, hcn⟩ := hN1 μ hμ (le_trans hsmall (min_le_left _ _)) hpar hKB n Φ hlow
  have h1' : μ * (a v) ^ 3 ≤ 1 := le_trans hsmall (min_le_right _ _)
  have hwin1 : 1 ≤ nPlusWindow (paramsAt μ (a v)) μ (a v) := by
    rw [nPlusWindow_paramsAt hμ hav]
    have hle := fsXp_le_fsXp (t := μ * (a v) ^ 3) (a := 0) (b := -(51 / 2))
      (by positivity) h1' (by norm_num)
    simpa [fsXp] using hle
  have hN : 0 ≤ norm2N n (sideAt μ (a v)) (Φ : X n → ℝ) := by
    dsimp [norm2N]
    exact integral_nonneg (fun x => sq_nonneg _)
  have hcoef : C₂ * nPlusWindow (paramsAt μ (a v)) μ (a v) + 1
      ≤ (C₂ + 1) * nPlusWindow (paramsAt μ (a v)) μ (a v) := by
    nlinarith [hwin1, hC₂]
  calc cnPlus (sideAt μ (a v)) (Φ : X n → ℝ)
      ≤ (C₂ * nPlusWindow (paramsAt μ (a v)) μ (a v) + 1)
          * norm2N n (sideAt μ (a v)) (Φ : X n → ℝ) := hcn
    _ ≤ ((C₂ + 1) * nPlusWindow (paramsAt μ (a v)) μ (a v))
          * norm2N n (sideAt μ (a v)) (Φ : X n → ℝ) :=
        mul_le_mul_of_nonneg_right hcoef hN
    _ = (C₂ + 1) * nPlusWindow (paramsAt μ (a v)) μ (a v)
          * norm2N n (sideAt μ (a v)) (Φ : X n → ℝ) := by ring

/-- **§6 from the chapter's §5 node and the grading datum**: `NodeB1` at the raised
threshold plus `B2GradingData` give the §6 replacement `NodeB2g`. -/
theorem nodeB2g_of_nodeB1_and_data {v : ℝ³ → ℝ} {h : ScatSol v} {J J' : ℝ}
    (hav : 0 < a v) (hlhy : lhyC ≤ J) (hJJ : J < J')
    (hB1 : NodeB1 v h J') (hg : B2GradingData v h J) :
    NodeB2g v h J J' :=
  nodeB2g_of_data hav hlhy hJJ hg (B2AprioriWindow_of_NodeB1 hav hB1)

/-- **`LHYBox` from the chapter's B-nodes.**  FS `thm:LHY-Box` follows from the §5 node
`NodeB1` (at the raised threshold), the §6 grading datum `B2GradingData` and the
restricted-subspace bound `NodeRestricted` — i.e. from FS §5 + §6 + §8–§11, with `B0`
(the low/non-low dichotomy) and the parameter bookkeeping already proved.  The error
coefficient is shifted by one (`C + 1`), which absorbs FS's Lieb–Solovej loss. -/
theorem LHYBox_of_B_nodes {v : ℝ³ → ℝ} {h : ScatSol v} {J J' η₀ C : ℝ}
    (hlhy : lhyC ≤ J) (hav : 0 < a v) (hC : 0 ≤ C) (hη₀ : 0 ≤ η₀) (hη₂ : η₀ < 2 / 323)
    (hJ'pos : 0 < J') (hJJ : J < J')
    (hB1 : NodeB1 v h J') (hg : B2GradingData v h J) (hr : NodeRestricted v h J' η₀ C) :
    LHYBox v h η₀ (C + 1) :=
  LHYBox_of_grading hlhy hav hC hη₀ hη₂ hJ'pos
    (nodeB2g_of_nodeB1_and_data hav hlhy hJJ hB1 hg) hr

end Work.BoseBox
