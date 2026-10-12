import ChallengeDeps
import Submission.Work.BoseBoxFix.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB2.Defs` — the vocabulary of FS §6 (`lem:LocMatrices`)

Subproject `BoseFixB2` (node D4).  The frozen lead vocabulary is
`Work.BoseBoxFix` (`Submission/Work/BoseBoxFix/Defs.lean`): `wordB`/`normB` (the
box-restricted word `boxFormB`/`sqNormB` on symmetric `BoxState`s), `IsLowB`,
`BoxBoundB`, `Adm`, `B2GradingDataB`.  This module adds **only the objects that
the proof of FS §6 needs**, and nothing else.

FS §6 (proof of `lem:LocMatrices`, `final_v2.tex` ll. 1365–1445) grades the box
state `Ψ` by the spectrum of the excitation-number operator `n₊ = ΣᵢQᵢ`,
`Qᵢ = 1 − Pᵢ` (`Pᵢ` = box mean in slot `i`), forms the matrix

    𝒜_{ij} = ‖1_{n₊=i}Ψ‖⁻¹‖1_{n₊=j}Ψ‖⁻¹⟨1_{n₊=i}Ψ, H_Λ(μ)1_{n₊=j}Ψ⟩

and the norm profile `ψ = (‖1_{n₊=i}Ψ‖)`, and proves: the energy identity
`⟨ψ,𝒜ψ⟩ = ⟨Ψ,HΨ⟩`, the band property (`𝒜^{(k)} = 0` for `k ≥ 3`), FS
`eq:dvapriori` (`|d₁|,|d₂| ≤ Cμ²ℓ³∫v`) and the recombination.

## The objects defined here

* `blockOp ℓ S k Φ`, `jointProj ℓ S Φ` — the **joint sector projection**
  `E_S = ∏_{i∈S}Q_i ∏_{j∉S}P_j`, applied to `Φ`.  The recursion runs over the
  slots `0,…,k−1` (each slot contributing its own `Q` or `P`), which keeps every
  statement in the concrete world of functions `X n → ℝ` and box integrals — the
  home of the whole corpus (`aP_add`, `aP_idem`, `aP_comm`, `aQ_ortho_box`, …).
* `secProj ℓ k Φ = Σ_{|S|=k} E_S Φ` — the **`n₊ = k` sector** of `Φ`.
* `polB v h μ n Φ Ψ` — the **polarised box word**, defined as FS do, by
  `4·polB Φ Ψ = wordB (Φ+Ψ) − wordB (Φ−Ψ)`; the analytic content (that this is
  a symmetric bilinear form, i.e. that `wordB` is a quadratic form on smooth
  states) is a separate delegation (`Sector.Polar`).
* `vecZ`, `gradePsi`, `gradeA`, `gradeMw`, `gradeNn` — the §6 data
  `(nn, A, ψv, Mw)` built from the sectors of `Φ`, with the FS convention "if any
  of the norms are zero we set the element to zero" (`gradeA`'s guard).
* `dOne`, `dTwo` — FS's `d₁` and `d₂`, the first two diagonal expectations of
  `𝒜`, in the form in which `eq:dvapriori` is proved.

## Conventions

* Indices of the grading are `ℤ → ℤ → ℂ` (the coding of `MatLoc`: `iRange nn`,
  `dk`, `qform`, `normSq` are `Work.UBBInputs3`'s).  `vecZ i` is the sector of
  `Φ` at index `i` for `0 ≤ i ≤ n` and `0` otherwise; `gradeA` vanishes outside
  `iRange nn × iRange nn` and whenever one of the two sector norms vanishes.
* `gradeMw 𝓜 = ⌈𝓜/4⌉₊ + 1` and `gradeNn n 𝓜 = max n (gradeMw 𝓜)`; the window
  inequalities `𝓜/4 ≤ Mw ≤ 𝓜/2` and `Mw ≤ nn` then hold as soon as `𝓜 ≥ 8`
  (`gradeMw_spec`).
* Everything is stated for FS's parameters `ℓ = sideAt μ (a v)`,
  `P = paramsAt μ (a v)`; `wordB`/`normB` are the frozen `BoxFix` ones.
-/

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Filter Metric

namespace Work.BoseFixB2

open Submission.BoseGases Work.BoseKinLoc Work.BoseBox Work.BoseBoxFix Work.UBB Work.UBBInputs3

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The joint sector projections `E_S` -/

/-- **The iterated slot operator of the set `S`.**  `blockOp ℓ S k Φ` applies, for
each slot `j = 0, 1, …, k−1` (in increasing order) the slot-`j` operator `aQ ℓ j` if
`j ∈ S` and `aP ℓ j` if `j ∉ S`, starting from `Φ`.  Slots `j ≥ n` are ignored. -/
noncomputable def blockOp (ℓ : ℝ) {n : ℕ} (S : Finset ℕ) : ℕ → (X n → ℝ) → (X n → ℝ)
  | 0, Φ => Φ
  | (k + 1), Φ =>
      if h : k < n then
        (if k ∈ S then aQ ℓ ⟨k, h⟩ (blockOp ℓ S k Φ)
         else aP ℓ ⟨k, h⟩ (blockOp ℓ S k Φ))
      else blockOp ℓ S k Φ

/-- **The joint sector projection** `E_S = ∏_{i∈S}Q_i ∏_{j∉S}P_j` applied to `Φ`
(the slots run over `0,…,n−1`; `S` is a set of *natural* indices, only its part
`< n` matters). -/
noncomputable def jointProj (ℓ : ℝ) {n : ℕ} (S : Finset ℕ) (Φ : X n → ℝ) : X n → ℝ :=
  blockOp ℓ S n Φ

/-- **The `n₊ = k` sector of `Φ`**: `secProj ℓ k Φ = Σ_{S ⊆ {0,…,n−1}, |S| = k} E_S Φ`.
This is FS's `1_{n₊=k}Ψ`; it vanishes identically for `k > n`. -/
noncomputable def secProj (ℓ : ℝ) {n : ℕ} (k : ℕ) (Φ : X n → ℝ) : X n → ℝ :=
  ∑ S ∈ (Finset.range n).powersetCard k, jointProj ℓ S Φ

@[simp] lemma blockOp_zero (ℓ : ℝ) {n : ℕ} (S : Finset ℕ) (Φ : X n → ℝ) :
    blockOp ℓ S 0 Φ = Φ := rfl

/-- The one-step unfolding of `blockOp` at a slot `k < n`. -/
lemma blockOp_succ {ℓ : ℝ} {n : ℕ} (S : Finset ℕ) {k : ℕ} (hk : k < n) (Φ : X n → ℝ) :
    blockOp ℓ S (k + 1) Φ
      = if k ∈ S then aQ ℓ ⟨k, hk⟩ (blockOp ℓ S k Φ)
        else aP ℓ ⟨k, hk⟩ (blockOp ℓ S k Φ) := by
  rw [blockOp]
  simp only [hk, dif_pos]

/-- `blockOp` at the empty slot set: the full box mean in every slot, i.e. the
composition of all the slot mean projections. -/
lemma blockOp_empty_one {ℓ : ℝ} {n : ℕ} (hn : 0 < n) (Φ : X n → ℝ) :
    blockOp ℓ (∅ : Finset ℕ) 1 Φ = aP ℓ ⟨0, hn⟩ Φ := by
  rw [blockOp_succ (k := 0) ∅ hn Φ]
  simp

/-- The recursion form of `jointProj`: the slot-`j` operator is applied *after* the
slots `< j`. -/
lemma jointProj_eq_blockOp (ℓ : ℝ) {n : ℕ} (S : Finset ℕ) (Φ : X n → ℝ) :
    jointProj ℓ S Φ = blockOp ℓ S n Φ := rfl

/-- `blockOp` depends on `S` only through `S ∩ {0,…,k−1}`. -/
lemma blockOp_congr_set {ℓ : ℝ} {n : ℕ} {S T : Finset ℕ} (h : ∀ j < n, (j ∈ S ↔ j ∈ T))
    (k : ℕ) (hk : k ≤ n) (Φ : X n → ℝ) : blockOp ℓ S k Φ = blockOp ℓ T k Φ := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have hkn : k < n := Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk
      rw [blockOp_succ S hkn, blockOp_succ T hkn, ih (Nat.le_of_lt hkn)]
      by_cases hmem : k ∈ S
      · rw [if_pos hmem, if_pos ((h k hkn).mp hmem)]
      · rw [if_neg hmem, if_neg (fun hc => hmem ((h k hkn).mpr hc))]

/-! ## 2. The polarised box word -/

/-- **FS §6's `𝒜_{ij}` numerator**: the polarisation of the frozen box word
`wordB` on smooth states, in the form of the proof of `lem:LocMatrices`
(`𝒜_{ij}‖1_iΨ‖‖1_jΨ‖ = ⟨1_iΨ, H_Λ1_jΨ⟩`). -/
noncomputable def polB (v : ℝ³ → ℝ) (h : ScatSol v) (μ : ℝ) (n : ℕ)
    (Φ Ψ : X n → ℝ) : ℝ :=
  (wordB v h μ n (fun x => Φ x + Ψ x) - wordB v h μ n (fun x => Φ x - Ψ x)) / 4

/-- The polarised form restricted to the sectors of a fixed state `Φ`. -/
noncomputable def secPol (v : ℝ³ → ℝ) (h : ScatSol v) (μ : ℝ) (n : ℕ) (ℓ : ℝ)
    (Φ : X n → ℝ) (i j : ℕ) : ℝ :=
  polB v h μ n (secProj ℓ i Φ) (secProj ℓ j Φ)

/-! ## 2b. The bilinear forms of the box word

FS §6's band argument (`lem:LocMatrices`: only the `𝒜^{(k)}`, `k ≤ 2`, are non-zero) is a
statement about the *bilinear* form of `wordB`: the kinetic part is a sum of slot-`i` forms
sandwiched by the slot-`i` mean-free projection `Q_i` (the `fsT` pieces apply `Q_u`
internally), and the potential part is the multiplication form by `potWordU`.  These are
the objects in which the joint-sector vanishing arguments of `Band/` and `Recomb/` run. -/

/-- The **polarisation of the one-body form `fsT`**. -/
noncomputable def fsTbil (ℓ d s εT b : ℝ) (u : ℝ³) (f g : ℝ³ → ℝ) : ℝ :=
  (Work.BoseKinLoc.fsT ℓ d s εT b u (fun z => f z + g z)
    - Work.BoseKinLoc.fsT ℓ d s εT b u (fun z => f z - g z)) / 4

/-- The **slot-`i` kinetic bilinear form** of the localised box word (the polarisation of the
`i`-th summand of `kinFormB`). -/
noncomputable def kinBil (N : ℕ) (ℓ d s εT b : ℝ) (i : Fin N) (Φ Ψ : X N → ℝ) : ℝ :=
  ℓ ^ (-3 : ℤ) * ∫ x in abox N ℓ,
    Work.BoseKinLoc.indU ℓ 0 (x i) *
      fsTbil ℓ d s εT b 0 (Work.BoseKinLoc.fibre N i Φ x)
        (Work.BoseKinLoc.fibre N i Ψ x)

/-- The **potential bilinear form** of the localised box word. -/
noncomputable def potBil (N : ℕ) (v g : ℝ³ → ℝ) (ℓ μ : ℝ) (Φ Ψ : X N → ℝ) : ℝ :=
  ∫ x in abox N ℓ, Φ x * Ψ x * Work.BoseKinLoc.potWordU N v g ℓ μ 0 x

/-! ## 3. The §6 data `(nn, A, ψv, Mw)` -/

/-- The window length `Mw` of the §6 replacement: `⌈𝓜/4⌉ + 1`, so that
`𝓜/4 ≤ Mw` and `Mw ≤ 𝓜/2` for `𝓜 ≥ 8`. -/
noncomputable def gradeMw (𝓜 : ℝ) : ℕ := ⌈𝓜 / 4⌉₊ + 1

/-- The number of blocks `nn` of the §6 replacement: large enough to contain the
`n+1` sectors of an `n`-particle state (`n+1` so that `iRange nn` contains the last
sector index `n`) and the window `Mw`. -/
noncomputable def gradeNn (n : ℕ) (𝓜 : ℝ) : ℕ := max (n + 1) (gradeMw 𝓜)

/-- The sector of `Φ` at the integer index `i` (zero outside `0 ≤ i ≤ n`), as a
function `X n → ℝ`. -/
noncomputable def vecZ {n : ℕ} (ℓ : ℝ) (Φ : X n → ℝ) (i : ℤ) : X n → ℝ :=
  if 0 ≤ i ∧ i ≤ (n : ℤ) then secProj ℓ i.toNat Φ else 0

/-- **The norm profile `ψ` of FS §6**: `ψ_i = ‖1_{n₊=i}Ψ‖/‖Ψ‖`, extended by `0`. -/
noncomputable def gradePsi (v : ℝ³ → ℝ) (h : ScatSol v) (μ : ℝ) (n : ℕ) (ℓ : ℝ)
    (Φ : X n → ℝ) (i : ℤ) : ℂ :=
  if 0 ≤ i ∧ i ≤ (n : ℤ) then
    ((Real.sqrt (normB v μ n (vecZ ℓ Φ i)) / Real.sqrt (normB v μ n Φ) : ℝ) : ℂ)
  else 0

/-- **The matrix `𝒜` of FS §6**: `𝒜_{ij} = ‖1_iΨ‖⁻¹‖1_jΨ‖⁻¹⟨1_iΨ,H_Λ1_jΨ⟩`, with
FS's convention that the element is `0` if one of the two norms vanishes. -/
noncomputable def gradeA (v : ℝ³ → ℝ) (h : ScatSol v) (μ : ℝ) (n : ℕ) (ℓ : ℝ)
    (Φ : X n → ℝ) (i j : ℤ) : ℂ :=
  if 0 ≤ i ∧ i ≤ (n : ℤ) ∧ 0 ≤ j ∧ j ≤ (n : ℤ)
      ∧ 0 < normB v μ n (vecZ ℓ Φ i) ∧ 0 < normB v μ n (vecZ ℓ Φ j) then
    ((polB v h μ n (vecZ ℓ Φ i) (vecZ ℓ Φ j)
        / (Real.sqrt (normB v μ n (vecZ ℓ Φ i)) * Real.sqrt (normB v μ n (vecZ ℓ Φ j))) : ℝ) : ℂ)
  else 0

/-- **FS's `d₁`**: the first diagonal expectation of `𝒜`, i.e.
`2Σᵢ⟨1_{n₊=i}Ψ, H_Λ1_{n₊=i+1}Ψ⟩/‖Ψ‖²`. -/
noncomputable def dOne (v : ℝ³ → ℝ) (h : ScatSol v) (μ : ℝ) (n : ℕ) (ℓ : ℝ)
    (Φ : X n → ℝ) : ℝ :=
  2 * (∑ i ∈ Finset.range n, polB v h μ n (secProj ℓ i Φ) (secProj ℓ (i + 1) Φ))
    / normB v μ n Φ

/-- **FS's `d₂`**: the second diagonal expectation of `𝒜`, i.e.
`2Σᵢ⟨1_{n₊=i}Ψ, H_Λ1_{n₊=i+2}Ψ⟩/‖Ψ‖²`. -/
noncomputable def dTwo (v : ℝ³ → ℝ) (h : ScatSol v) (μ : ℝ) (n : ℕ) (ℓ : ℝ)
    (Φ : X n → ℝ) : ℝ :=
  2 * (∑ i ∈ Finset.range (n - 1), polB v h μ n (secProj ℓ i Φ) (secProj ℓ (i + 2) Φ))
    / normB v μ n Φ

/-! ## 4. The arithmetic of the window -/

/-- The window inequalities of §6: for `𝓜 ≥ 8`, `3 ≤ Mw`, `𝓜/4 ≤ Mw ≤ 𝓜/2` and
`Mw ≤ nn`. -/
lemma gradeMw_spec {𝓜 : ℝ} (h𝓜 : 8 ≤ 𝓜) :
    3 ≤ gradeMw 𝓜 ∧ 𝓜 / 4 ≤ (gradeMw 𝓜 : ℝ) ∧ (gradeMw 𝓜 : ℝ) ≤ 𝓜 / 2 ∧
      gradeMw 𝓜 ≤ gradeNn 0 𝓜 := by
  have hceil_ge : 𝓜 / 4 ≤ (⌈𝓜 / 4⌉₊ : ℝ) := Nat.le_ceil _
  have hceil_lt : ((⌈𝓜 / 4⌉₊ : ℕ) : ℝ) < 𝓜 / 4 + 1 := Nat.ceil_lt_add_one (by linarith)
  have h3 : (3 : ℕ) ≤ ⌈𝓜 / 4⌉₊ + 1 := by
    have h2 : (2 : ℝ) ≤ (⌈𝓜 / 4⌉₊ : ℝ) := by linarith
    have : 2 ≤ ⌈𝓜 / 4⌉₊ := by exact_mod_cast h2
    omega
  refine ⟨by simpa [gradeMw] using h3, ?_, ?_, le_max_right _ _⟩
  · have : (⌈𝓜 / 4⌉₊ : ℝ) ≤ (gradeMw 𝓜 : ℝ) := by
      simp only [gradeMw]; push_cast; linarith
    linarith
  · have : (gradeMw 𝓜 : ℝ) < 𝓜 / 4 + 2 := by
      simp only [gradeMw]; push_cast; linarith
    linarith

/-- `gradeNn` dominates the particle number and `Mw`. -/
lemma le_gradeNn (n : ℕ) {𝓜 : ℝ} : n ≤ gradeNn n 𝓜 := by
  simp only [gradeNn]; omega

lemma succ_le_gradeNn (n : ℕ) {𝓜 : ℝ} : n + 1 ≤ gradeNn n 𝓜 := le_max_left _ _

lemma gradeMw_le_gradeNn (n : ℕ) (𝓜 : ℝ) : gradeMw 𝓜 ≤ gradeNn n 𝓜 := le_max_right _ _

/-! ## 5. FS's parameters -/

/-- FS's box side at the chemical potential `μ`: `ℓ = sideAt μ (a v)`. -/
noncomputable def fsSide (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) : ℝ :=
  Work.BoseBox.sideAt μ (_root_.BoseGases.a v)

/-- FS's matrix window `𝓜 = bigM (paramsAt μ (a v)) (a v) μ` (FS `eq:DefM`). -/
noncomputable def fsM (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) : ℝ :=
  Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)) (_root_.BoseGases.a v) μ

/-- The window length `Mw = gradeMw 𝓜` at FS's parameters. -/
noncomputable def fsRmw (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) : ℕ :=
  gradeMw (fsM v μ)

/-- The number of blocks `nn = gradeNn n 𝓜` at FS's parameters. -/
noncomputable def fsNn (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) (n : ℕ) : ℕ :=
  gradeNn n (fsM v μ)

/-- The `n₊ = k` sector of `Φ` at FS's parameters. -/
noncomputable def fsSec (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) {n : ℕ}
    (k : ℕ) (Φ : X n → ℝ) : X n → ℝ :=
  secProj (fsSide v μ) k Φ

/-- The slot-`i` kinetic bilinear form at FS's parameters. -/
noncomputable def kinBilFS (v : ℝ³ → ℝ) (μ : ℝ) {n : ℕ} (i : Fin n)
    (Φ Ψ : X n → ℝ) : ℝ :=
  kinBil n (fsSide v μ) (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b i Φ Ψ

/-- The admissible chemical potentials: small diluteness and FS `sec:params`. -/
lemma Adm_mono {v : EuclideanSpace ℝ (Fin 3) → ℝ} {ε ε' : ℝ} (hle : ε ≤ ε') {μ : ℝ}
    (h : Work.BoseBoxFix.Adm v ε μ) : Work.BoseBoxFix.Adm v ε' μ :=
  ⟨h.1, le_trans h.2.1 hle, h.2.2⟩

end Work.BoseFixB2
