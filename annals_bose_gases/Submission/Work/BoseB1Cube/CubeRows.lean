import ChallengeDeps
import Submission.Work.BoseFixB1.Up.flatWordKinDense
import Submission.Work.BoseFixB1.perBoxMF_cases
import Submission.Work.BoseFixB1B.matchedWindowDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB1Cube.CubeRows` — the **matched-window (cube-cutoff) flat rows**

The frozen flat-branch residual of the corpus is `Work.BoseFixB1.Up.FlatWordKin`
(`Submission/Work/BoseFixB1/Up/FlatRowsDelta.lean`):

    in the band `n₊(B(u)) < γ n ‖Φ‖²` on good, non-thin sliding boxes,

    `½W₂(τ²‖Φ‖² + V) − μW₁τ‖Φ‖² − C·flatErrB − flatSlackB − Δ ≤ sbWord`,

with `W₁ = w1MassB`, `W₂ = flatPairMass`, `τ = flatTau`, `N = normB`, `V = flatVar`,
`Δ = ½(W₂−W₁)(τ²N+V)`.  Its right-hand side is the *frozen* sliding word `sbWord`, whose kinetic
slot carries the **ball** window `chiB` while its potential slot's kernels carry the **cube** bump
`chiSmallB`.  That mismatch is what makes the frozen statement false at the corner boxes
(`Work.BoseFixB1B.FINDING_perBoxFTotal_session2.md`): at the admissible `u` whose box misses the
ball, `chiB ≡ 0` as a function, so the frozen kinetic slot vanishes while the demand does not.

**This module is the matched-window repair.**  Everything in `FlatWordKin` is *window-free* (it is
built from `nCountB`, `chiMass`, `w1MassB`, `flatPairSum`, `flatErrB`, `flatSlackB` — none of which
mentions a cutoff) **except the word on the right-hand side**.  Replacing that word by the matched
`Work.BoseFixB1B.sbWordCube` (the single-cutoff sliding word whose kinetic slot carries the *same*
bump `chiSmallB` as the kernels) gives a statement in which the corner obstruction is gone: the
spectral slot `cubeSpectral` is alive exactly where the box is.  This is FS's own modelling
(`eq:chiBdefinition`: ONE `χ_B` for both slots).

The definitions here are **verbatim copies** of `Up.FlatRowsDelta.lean` /
`Up/flatWordKinDense.lean` / `Up/flatWordKinDiluteDefs.lean` with `sbWord ↦ sbWordCube`; the glue
lemmas are the corresponding proved ones (they are window-blind: they only use the monotonicity of
the error bracket).

## Contents

* `CubeFlatWordLe v h R μ Φ u C` — the word inequality `(R)` with the matched word;
* `CubeFlatWordKin v h R` — the band residual (the analytic frontier of the cube chapter);
* `CubeFlatWordKinDense` / `CubeFlatWordKinDilute` — the density split (`τ ≥ Kμ` / `τ < Kμ`)
  and their proved glue `cubeFlatWordKin_of_dense_dilute`;
* `CubeFlatWordKinDiluteFlat` / `CubeFlatWordKinDiluteBand` — the dilute half split at
  `n₊(B) = 0`, and their proved glue `cubeFlatWordKinDilute_of_flat_band`.

The two *glue* steps and the monotonicity `cubeFlatWordLe_mono` are proved here; the four leaf
statements are the chapter's residuals.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseB1Cube

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding Work.BoseFixB1

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The fixed band threshold `T = 10^{-100}` of the cube chapter — the same constant that meets
the proved gap branch `Work.BoseFixB1.Up.perBoxF_of_gapPayment` (whose `γ_g` satisfies
`γ_g ≤ 10^{-100}`). -/
noncomputable def cubeBandT : ℝ := (1 / 10 : ℝ) ^ (100 : ℕ)

theorem cubeBandT_pos : 0 < cubeBandT := by
  rw [cubeBandT]; positivity

theorem cubeBandT_le_one : cubeBandT ≤ 1 := by
  rw [cubeBandT]; norm_num

/-- **The word-level flat inequality at the matched (cube) window** — verbatim
`Work.BoseFixB1.Up.FlatWordLe` with the frozen word `sbWord` replaced by the matched
`Work.BoseFixB1B.sbWordCube`.  Its body is *not* definitionally equal to `FlatWordLe` (the
right-hand side differs), so it is a fresh definition; every other atom is shared. -/
def CubeFlatWordLe (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (R μ : ℝ)
    {n : ℕ} (Φ : X n → ℝ) (u : E3) (C : ℝ) : Prop :=
  (1 / 2) * Work.BoseFixB1.flatPairMass v (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
        (Work.BoseFixB1.pD v μ) u
      * (Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
            (Work.BoseFixB1.pD v μ) u Φ ^ 2
          * Work.BoseBoxFix.normB v μ n Φ
        + Work.BoseFixB1.Up.flatVar v μ Φ u)
    - μ * Work.BoseFixB1.w1MassB h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
          (Work.BoseFixB1.pD v μ) u
        * Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
            (Work.BoseFixB1.pD v μ) u Φ
        * Work.BoseBoxFix.normB v μ n Φ
    - C * Work.BoseFixB1.Up.flatErrB v R μ Φ u
    - Work.BoseFixB1.Up.flatSlackB v h μ Φ u
    - (1 / 2)
        * (Work.BoseFixB1.flatPairMass v (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
              (Work.BoseFixB1.pD v μ) u
            - Work.BoseFixB1.w1MassB h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                (Work.BoseFixB1.pD v μ) u)
        * (Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
              (Work.BoseFixB1.pD v μ) u Φ ^ 2
            * Work.BoseBoxFix.normB v μ n Φ
          + Work.BoseFixB1.Up.flatVar v μ Φ u)
  ≤ Work.BoseFixB1B.sbWordCube v h μ u Φ

/-- Monotonicity of `CubeFlatWordLe` in its error constant — the window-blind twin of
`Work.BoseFixB1.Up.flatWordLe_mono` (only the nonnegativity of `flatErrB` is used). -/
theorem cubeFlatWordLe_mono {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R μ : ℝ} {n : ℕ} {Φ : X n → ℝ}
    {u : E3} {C C' : ℝ} {ε : ℝ} (hAdm : Work.BoseBoxFix.Adm v ε μ) (hC : C ≤ C')
    (hle : CubeFlatWordLe v h R μ Φ u C) : CubeFlatWordLe v h R μ Φ u C' := by
  have hfE := Work.BoseFixB1.Up.flatErrB_nonneg (h := h) (R := R) (μ := μ) (Φ := Φ) (u := u) hAdm
  have : C * Work.BoseFixB1.Up.flatErrB v R μ Φ u
      ≤ C' * Work.BoseFixB1.Up.flatErrB v R μ Φ u :=
    mul_le_mul_of_nonneg_right hC hfE
  unfold CubeFlatWordLe at hle ⊢
  linarith

/-- **The matched-window flat (`band`) residual** — `Work.BoseFixB1.Up.FlatWordKin` with the
matched word and the **fixed** band threshold `T = 10^{-100}` (which the PROVED gap branch
`Work.BoseFixB1.Up.perBoxF_of_gapPayment`, with its own `γ_g ≤ 10^{-100}`, meets: the per-box
trichotomy is "`γ_g n‖Φ‖² ≤ n₊` (gap, PROVED) or `n₊ ≤ 10^{-100}n‖Φ‖²` (this residual)", exactly
as in `Work.BoseFixB1.Up.perBoxF_thick_of_flatBranch`).  On good, non-thin boxes, the matched
word dominates the mean-field expression, with the free payer `sbWordCube` itself (the budget of
the Δ-augmented ledger permits `P ≤ sbKinCube`; here the whole word is available, and `sbKinCube`
is its kinetic half).

The band hypothesis carries **no lower bound** on `n₊`: the exactly flat states (`n₊ = 0`) are
included, which is what makes the flat-zero arm of the chapter unnecessary (the dilute half splits
them off into `CubeFlatWordKinDiluteFlat`). -/
def CubeFlatWordKin (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (R : ℝ) : Prop :=
  ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (BoseGases.a v)))
        (u : E3),
        u ∈ Work.SmallBoxSliding.goodSet (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) μ →
        ¬ Work.BoseFixB1.IsThinBox v h μ u →
        Work.BoseFixB1.Up.nPlusB v μ u n (Φ : X n → ℝ)
            ≤ cubeBandT * (n : ℝ) * Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ) →
        CubeFlatWordLe v h R μ (Φ : X n → ℝ) u C

/-- **The dense case** (`K μ ≤ τ`) of the matched flat residual — the pair-condensate energy
`½W₂(τ²N+V)` supplies a headroom of order `τ²N` here. -/
def CubeFlatWordKinDense (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (R K : ℝ) : Prop :=
  ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (BoseGases.a v)))
        (u : E3),
        u ∈ Work.SmallBoxSliding.goodSet (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) μ →
        ¬ Work.BoseFixB1.IsThinBox v h μ u →
        Work.BoseFixB1.Up.nPlusB v μ u n (Φ : X n → ℝ)
            ≤ cubeBandT * (n : ℝ) * Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ) →
        K * μ ≤ Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
            (Work.BoseFixB1.pD v μ) u (Φ : X n → ℝ) →
        CubeFlatWordLe v h R μ (Φ : X n → ℝ) u C

/-- **The dilute case** (`τ < K μ`) of the matched flat residual. -/
def CubeFlatWordKinDilute (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (R K : ℝ) : Prop :=
  ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (BoseGases.a v)))
        (u : E3),
        u ∈ Work.SmallBoxSliding.goodSet (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) μ →
        ¬ Work.BoseFixB1.IsThinBox v h μ u →
        Work.BoseFixB1.Up.nPlusB v μ u n (Φ : X n → ℝ)
            ≤ cubeBandT * (n : ℝ) * Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ) →
        Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
            (Work.BoseFixB1.pD v μ) u (Φ : X n → ℝ) < K * μ →
        CubeFlatWordLe v h R μ (Φ : X n → ℝ) u C

/-- **The glue of the density split.**  At a fixed split point `K` the two cases exhaust the states
(`Kμ ≤ τ` or `τ < Kμ`), and `CubeFlatWordLe` is monotone in `C`, so the constants merge by
`min`/`max`.  The window-blind twin of `Work.BoseFixB1.Up.flatWordKin_of_dense_dilute`. -/
theorem cubeFlatWordKin_of_dense_dilute {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R K : ℝ}
    (hD : CubeFlatWordKinDense v h R K) (hd : CubeFlatWordKinDilute v h R K) :
    CubeFlatWordKin v h R := by
  obtain ⟨ε₁, C₁, hε₁, hC₁, hpr₁⟩ := hD
  obtain ⟨ε₂, C₂, hε₂, hC₂, hpr₂⟩ := hd
  refine ⟨min ε₁ ε₂, max C₁ C₂, lt_min hε₁ hε₂, le_max_of_le_left hC₁, ?_⟩
  intro μ hA n Φ u hg ht hb
  have hA₁ : Work.BoseBoxFix.Adm v ε₁ μ := Work.BoseFixB1.Adm.mono hA (min_le_left _ _)
  have hA₂ : Work.BoseBoxFix.Adm v ε₂ μ := Work.BoseFixB1.Adm.mono hA (min_le_right _ _)
  rcases le_or_gt (K * μ) (Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
      (Work.BoseFixB1.pD v μ) u (Φ : X n → ℝ)) with hden | hdil
  · exact cubeFlatWordLe_mono hA₁ (le_max_left _ _)
      (hpr₁ μ hA₁ n Φ u hg ht hb hden)
  · exact cubeFlatWordLe_mono hA₂ (le_max_right _ _)
      (hpr₂ μ hA₂ n Φ u hg ht hb hdil)

/-- **The exactly flat case of the dilute residual** (`n₊(B) = 0`, `τ < μ`) at the matched
window — verbatim `Work.BoseFixB1.Up.FlatWordKinDiluteFlat` with the matched word. -/
def CubeFlatWordKinDiluteFlat (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (R : ℝ) : Prop :=
  ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (BoseGases.a v)))
        (u : E3),
        u ∈ Work.SmallBoxSliding.goodSet (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) μ →
        ¬ Work.BoseFixB1.IsThinBox v h μ u →
        Work.BoseFixB1.Up.nPlusB v μ u n (Φ : X n → ℝ) = 0 →
        Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
            (Work.BoseFixB1.pD v μ) u (Φ : X n → ℝ) < μ →
        CubeFlatWordLe v h R μ (Φ : X n → ℝ) u C

/-- **The genuinely excited case of the dilute residual** (`0 < n₊(B) < γ n ‖Φ‖²`, `τ < μ`) at
the matched window.  This is the residual of the dilute half: the fibre and pair deviations are
only perturbative here and have to be handled jointly (see
`Work.BoseFixB1.Up.FlatRowsDelta.lean`, "the joint residual vs. splitting"). -/
def CubeFlatWordKinDiluteBand (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (R : ℝ) : Prop :=
  ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (BoseGases.a v)))
        (u : E3),
        u ∈ Work.SmallBoxSliding.goodSet (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) μ →
        ¬ Work.BoseFixB1.IsThinBox v h μ u →
        0 < Work.BoseFixB1.Up.nPlusB v μ u n (Φ : X n → ℝ) →
        Work.BoseFixB1.Up.nPlusB v μ u n (Φ : X n → ℝ)
            ≤ cubeBandT * (n : ℝ) * Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ) →
        Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
            (Work.BoseFixB1.pD v μ) u (Φ : X n → ℝ) < μ →
        CubeFlatWordLe v h R μ (Φ : X n → ℝ) u C

/-- **The glue of the dilute split.**  The two cases exhaust the dilute states (the only dichotomy
is `n₊ = 0` versus `n₊ > 0`), and `CubeFlatWordLe` is monotone in `C`.  The window-blind twin of
`Work.BoseFixB1.Up.flatWordKinDilute_of_flat_band`. -/
theorem cubeFlatWordKinDilute_of_flat_band {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R : ℝ}
    (hf : CubeFlatWordKinDiluteFlat v h R) (hb : CubeFlatWordKinDiluteBand v h R) :
    CubeFlatWordKinDilute v h R 1 := by
  obtain ⟨ε₁, C₁, hε₁, hC₁, hpr₁⟩ := hf
  obtain ⟨ε₂, C₂, hε₂, hC₂, hpr₂⟩ := hb
  refine ⟨min ε₁ ε₂, max C₁ C₂, lt_min hε₁ hε₂, le_max_of_le_left hC₁, ?_⟩
  intro μ hAdm n Φ u hu ht hband hdil
  have hA₁ : Work.BoseBoxFix.Adm v ε₁ μ := Work.BoseFixB1.Adm.mono hAdm (min_le_left _ _)
  have hA₂ : Work.BoseBoxFix.Adm v ε₂ μ := Work.BoseFixB1.Adm.mono hAdm (min_le_right _ _)
  have hdil' : Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
      (Work.BoseFixB1.pD v μ) u (Φ : X n → ℝ) < μ := by simpa using hdil
  rcases lt_or_eq_of_le (Work.BoseFixB1.Up.nPlusB_nonneg v μ u n (Φ : X n → ℝ)) with hpos | hzero
  · exact cubeFlatWordLe_mono hA₂ (le_max_right _ _)
      (hpr₂ μ hA₂ n Φ u hu ht hpos hband hdil')
  · exact cubeFlatWordLe_mono hA₁ (le_max_left _ _)
      (hpr₁ μ hA₁ n Φ u hu ht hzero.symm hdil')

end Work.BoseB1Cube
