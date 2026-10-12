import ChallengeDeps
import Submission.Work.BoseBox.B2Reduction
import Submission.Work.BoseKinLoc.Residuals
import Submission.Work.BoseTop.Pressure
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! LEAD-FROZEN (curric-46, 2026-10-03). Corrected BoseBox vocabulary and node statements: box-restricted form boxFormB over symmetric BoxStates. Design: BOSE_BOXNODES_LEAD.md (workspace root). Do not edit. The node theorems are separate requests. -/

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Filter Metric

namespace Work.BoseBoxFix

open _root_.BoseGases Submission.BoseGases Work.UBB Work.UBBInputs3 Work.BoseBox

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 0. Vocabulary -/

/-- FS `eq:Def_HB2` `H_Λ(μ)` on `L²(Λⁿ)` at FS's parameters: BoseKinLoc's box-restricted form. -/
def wordB (v : ℝ³ → ℝ) (h : ScatSol v) (μ : ℝ) (n : ℕ) (Φ : X n → ℝ) : ℝ :=
  Work.BoseKinLoc.boxFormB n v (g0 v h) (sideAt μ (a v)) μ (paramsAt μ (a v)).d
    (paramsAt μ (a v)).s (paramsAt μ (a v)).eT (paramsAt μ (a v)).b Φ

/-- `‖Φ‖²_{L²(Λⁿ)}`. -/
def normB (v : ℝ³ → ℝ) (μ : ℝ) (n : ℕ) (Φ : X n → ℝ) : ℝ :=
  Work.BoseKinLoc.sqNormB n (sideAt μ (a v)) Φ

/-- FS `eq:aprioriPsi` (low state at threshold `J`). -/
def IsLowB (v : ℝ³ → ℝ) (h : ScatSol v) (J μ : ℝ) (n : ℕ) (Φ : X n → ℝ) : Prop :=
  wordB v h μ n Φ ≤ sideAt μ (a v) ^ 3 * Theta (a v) J μ * normB v μ n Φ

/-- FS `eq:EnergyBoxRes1` for one state. -/
def BoxBoundB (v : ℝ³ → ℝ) (h : ScatSol v) (η₀ C μ : ℝ) (n : ℕ) (Φ : X n → ℝ) : Prop :=
  sideAt μ (a v) ^ 3 * Lambda (a v) C η₀ μ * normB v μ n Φ ≤ wordB v h μ n Φ

/-- The admissible chemical potentials: small diluteness and FS `sec:params`. -/
def Adm (v : ℝ³ → ℝ) (ε₀ μ : ℝ) : Prop :=
  0 < μ ∧ μ * a v ^ 3 ≤ ε₀ ∧ ParamsOK (paramsAt μ (a v)) (μ * a v ^ 3)

/-- **FS `thm:LHY-Box`** on `L²_sym(Λⁿ)`, `n` free: the B-side target. -/
def LHYBoxB (v : ℝ³ → ℝ) (h : ScatSol v) (η₀ C : ℝ) : Prop :=
  ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Adm v ε₀ μ →
    ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))),
      BoxBoundB v h η₀ C μ n Φ

/-! ## 1. §5 (`NodeB1B`) and its §6 input -/

/-- **FS `thm:aprioribounds`, `eq:apriorinn+`** on symmetric box states. -/
def NodeB1B (v : ℝ³ → ℝ) (h : ScatSol v) (J : ℝ) : Prop :=
  ∃ C₁ C₂ ε₀ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ 0 < ε₀ ∧ ∀ μ : ℝ, Adm v ε₀ μ →
    J ≤ (paramsAt μ (a v)).KB ^ 3 →
    ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))),
      0 < normB v μ n Φ → IsLowB v h J μ n Φ →
      |(n : ℝ) - μ * sideAt μ (a v) ^ 3| ≤ C₁ * nWindow (paramsAt μ (a v)) μ (a v) ∧
      cnPlus (sideAt μ (a v)) (Φ : X n → ℝ)
        ≤ C₂ * nPlusWindow (paramsAt μ (a v)) μ (a v) * normB v μ n Φ

/-- The only §5 input of §6 (second conjunct of `NodeB1B`). -/
def B2AprioriWindowB (v : ℝ³ → ℝ) (h : ScatSol v) (J : ℝ) : Prop :=
  ∃ C₁ ε₀ : ℝ, 0 ≤ C₁ ∧ 0 < ε₀ ∧ ∀ μ : ℝ, Adm v ε₀ μ →
    J ≤ (paramsAt μ (a v)).KB ^ 3 →
    ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))),
      0 < normB v μ n Φ → IsLowB v h J μ n Φ →
      cnPlus (sideAt μ (a v)) (Φ : X n → ℝ)
        ≤ C₁ * nPlusWindow (paramsAt μ (a v)) μ (a v) * normB v μ n Φ

/-! ## 2. §6 -/

/-- **FS §6 steps (2)–(4) + `eq:dvapriori`** (corrected): box-restricted word, symmetric
states, positive norm, and the recombination demanded only for windows with *negative*
energy `⟨φ,Aφ⟩ < 0` (FS's proof uses exactly this; for `⟨φ,Aφ⟩ ≥ 0` the old clause asked for
an unrelated state). -/
def B2GradingDataB (v : ℝ³ → ℝ) (h : ScatSol v) (J : ℝ) : Prop :=
  ∃ K ε₀ : ℝ, 0 ≤ K ∧ 0 < ε₀ ∧ ∀ μ : ℝ, Adm v ε₀ μ →
    J ≤ (paramsAt μ (a v)).KB ^ 3 →
    ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))),
      0 < normB v μ n Φ → IsLowB v h J μ n Φ →
      ∃ (nn : ℕ) (A : ℤ → ℤ → ℂ) (ψv : ℤ → ℂ) (Mw : ℕ),
        3 ≤ Mw ∧ bigM (paramsAt μ (a v)) (a v) μ / 4 ≤ (Mw : ℝ) ∧
        (Mw : ℝ) ≤ bigM (paramsAt μ (a v)) (a v) μ / 2 ∧ Mw ≤ nn ∧
        (∀ i j, A i j ≠ 0 → i ∈ iRange nn ∧ j ∈ iRange nn) ∧
        (∀ i j, A j i = star (A i j)) ∧
        (∀ j, ψv j ≠ 0 → j ∈ iRange nn) ∧
        normSq (iRange nn) ψv = 1 ∧
        qform A (iRange nn) ψv ψv * normB v μ n Φ = wordB v h μ n Φ ∧
        (∀ k : ℤ, 3 ≤ k → dk A nn ψv k = 0) ∧
        (|dk A nn ψv 1| + |dk A nn ψv 2| ≤ K * μ ^ 2 * sideAt μ (a v) ^ 3) ∧
        (∀ (n₀ : ℤ) (φ : ℤ → ℂ), 0 ≤ n₀ → n₀ + (Mw : ℤ) ≤ (nn : ℤ) →
          (∀ j, φ j ≠ 0 → n₀ ≤ j ∧ j < n₀ + (Mw : ℤ)) → normSq (iRange nn) φ = 1 →
          qform A (iRange nn) φ φ < 0 →
          ∃ Φ' : Work.BoseKinLoc.BoxState n (sideAt μ (a v)),
            normB v μ n Φ' = normB v μ n Φ ∧
            wordB v h μ n Φ' ≤ qform A (iRange nn) φ φ * normB v μ n Φ ∧
            (∀ 𝓜₂ : ℝ, (n₀ : ℝ) + (Mw : ℝ) ≤ 𝓜₂ →
              SpectralNPlusLe (sideAt μ (a v)) 𝓜₂ (Φ' : X n → ℝ)) ∧
            (n₀ : ℝ) * normB v μ n Φ' ≤ cnPlus (sideAt μ (a v)) (Φ' : X n → ℝ))

/-- **FS `lem:LocMatrices`** (corrected): replacement form on symmetric box states. -/
def NodeB2gB (v : ℝ³ → ℝ) (h : ScatSol v) (J J' : ℝ) : Prop :=
  ∃ K ε₀ : ℝ, 0 ≤ K ∧ 0 < ε₀ ∧ ∀ μ : ℝ, Adm v ε₀ μ →
    ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))),
      0 < normB v μ n Φ → IsLowB v h J μ n Φ →
      ∃ Φ' : Work.BoseKinLoc.BoxState n (sideAt μ (a v)),
        IsLowB v h J' μ n Φ' ∧
        normB v μ n Φ' = normB v μ n Φ ∧
        wordB v h μ n Φ' ≤ wordB v h μ n Φ
          + K * μ ^ 2 * sideAt μ (a v) ^ 3 / bigM (paramsAt μ (a v)) (a v) μ ^ 2
              * normB v μ n Φ ∧
        SpectralNPlusLe (sideAt μ (a v)) (bigM (paramsAt μ (a v)) (a v) μ) (Φ' : X n → ℝ)

/-! ## 3. §7–§11 -/

/-- **FS §7–§11** on the spectrally restricted class (corrected vocabulary). -/
def NodeRestrictedB (v : ℝ³ → ℝ) (h : ScatSol v) (J η₀ C : ℝ) : Prop :=
  ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Adm v ε₀ μ →
    J ≤ (paramsAt μ (a v)).KB ^ 3 →
    ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))),
      IsLowB v h J μ n Φ →
      SpectralNPlusLe (sideAt μ (a v)) (bigM (paramsAt μ (a v)) (a v) μ) (Φ : X n → ℝ) →
      BoxBoundB v h η₀ C μ n Φ

/-! ### §7 vocabulary: FS's smooth low-momentum localisation `Q_L = Q f_L(√−Δ)` -/

/-- FS's cut-off `f`: smooth, non-increasing, `f = 1` on `(-∞,1]`, `f = 0` on `[2,∞)`. -/
structure LowCut where
  f : ℝ → ℝ
  smooth : ContDiff ℝ (⊤ : ℕ∞) f
  anti : Antitone f
  one : ∀ s : ℝ, s ≤ 1 → f s = 1
  zero : ∀ s : ℝ, 2 ≤ s → f s = 0

/-- `f(√−Δ/κ)` applied to `θψ` (extension by `0` off `Λ = acube ℓ`), in the corpus's
`p`-convention (`kinFT`, `e^{-i⟨p,y⟩}`): `(2π)⁻³∫_p e^{i⟨p,x⟩} f(|p|/κ) (θψ)^(p) dp`.  Real part
(the multiplier is real and even, so the imaginary part vanishes). -/
def lowMult (fc : LowCut) (κ ℓ : ℝ) (ψ : ℝ³ → ℝ) (x : ℝ³) : ℝ :=
  ((((2 * π) ^ 3)⁻¹ : ℝ) * ∫ p : ℝ³, Complex.exp (Complex.I * (inner ℝ p x : ℂ)) *
      ((fc.f (‖p‖ / κ) : ℝ) : ℂ) *
        Submission.BoseGases.kinFT (fun z : ℝ³ => (((acube ℓ).indicator ψ z : ℝ) : ℂ)) p).re

/-- The slot-`j` lift of `lowMult`. -/
def lowSlot (fc : LowCut) (κ ℓ : ℝ) {n : ℕ} (j : Fin n) (Φ : X n → ℝ) (x : X n) : ℝ :=
  lowMult fc κ ℓ (fun z => Φ (Function.update x j z)) (x j)

/-- FS `Q̃₃^{(1)} = Σ_{i≠j}(P_iQ_{L,j}w₁Q_jQ_i + h.c.)` as a quadratic form:
`⟨Φ,P_iQ_{L,j}w₁Q_jQ_iΦ⟩ = ⟨f_L(√−Δ_j)Q_jP_iΦ, w₁Q_jQ_iΦ⟩`. -/
def q3lowWord (fc : LowCut) (κ ℓ : ℝ) (w1 : ℝ³ → ℝ³ → ℝ) {n : ℕ} (Φ : X n → ℝ) : ℝ :=
  2 * ∑ p ∈ pairSet n, ∫ x in abox n ℓ,
    lowSlot fc κ ℓ p.2 (aQ ℓ p.2 (aP ℓ p.1 Φ)) x * aQ ℓ p.2 (aQ ℓ p.1 Φ) x
      * w1 (x p.1) (x p.2)

/-- FS `n₊^H = Σᵢ Q_i 1_{(d⁻²ℓ⁻¹,∞)}(√−Δ_i) Q_i` on `L²(Λⁿ)` (box-restricted). -/
def nPlusHB (ℓ d : ℝ) {n : ℕ} (Φ : X n → ℝ) : ℝ :=
  ℓ ^ (-3 : ℤ) * ∑ i : Fin n, ∫ x in abox n ℓ,
    Work.BoseKinLoc.indU ℓ 0 (x i) * Work.BoseKinLoc.momForm ℓ d 0 (Work.BoseKinLoc.fibre n i Φ x)

/-- **FS `lem:Q3-splitting1` (`eq:ReduceQ3`)**, as a per-state inequality for every box state
with at most `2μℓ³` particles (FS assume `eq:apriorinn+` only through `n ≤ Cμℓ³`).  The cut-off
is FS's `K_L√(μa) = (d²ℓ)⁻¹` (`eq:KL_d`), so `K_ℓK_L = d⁻²` and `(K_ℓK_L)^{1-M} = d^{2(M-1)}`. -/
def NodeB3B (v : ℝ³ → ℝ) (h : ScatSol v) (R : ℝ) (fc : LowCut) : Prop :=
  ∃ C ε₀ : ℝ, 0 ≤ C ∧ 0 < ε₀ ∧ ∀ μ : ℝ, Adm v ε₀ μ →
    ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))),
      (n : ℝ) ≤ 2 * μ * sideAt μ (a v) ^ 3 →
      q3word (sideAt μ (a v)) (wLoc (sideAt μ (a v)) (g0 v h) 0) (Φ : X n → ℝ)
        + (1 / 4) * q4word (sideAt μ (a v)) (wLoc (sideAt μ (a v)) v 0)
            (omC (Classical.choose h)) (Φ : X n → ℝ)
        + (paramsAt μ (a v)).b / 100 *
            (sideAt μ (a v) ^ (-2 : ℤ) * cnPlus (sideAt μ (a v)) (Φ : X n → ℝ)
              + (paramsAt μ (a v)).eT * ((paramsAt μ (a v)).d * sideAt μ (a v)) ^ (-2 : ℤ)
                  * nPlusHB (sideAt μ (a v)) (paramsAt μ (a v)).d (Φ : X n → ℝ))
      ≥ q3lowWord fc ((paramsAt μ (a v)).d ^ 2 * sideAt μ (a v))⁻¹ (sideAt μ (a v))
            (wLoc (sideAt μ (a v)) (g0 v h) 0) (Φ : X n → ℝ)
        - C * μ ^ 2 * a v * sideAt μ (a v) ^ 3
            * ((paramsAt μ (a v)).d ^ (2 * ((paramsAt μ (a v)).M - 1))
                + R ^ 2 / sideAt μ (a v) ^ 2)
            * normB v μ n Φ


end Work.BoseBoxFix
