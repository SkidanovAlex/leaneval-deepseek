import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1.PerSectorSmooth
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1.perSectorSmooth_holds` — the per-sector smooth-density rung

Target (fixed, kept verbatim below): `Work.BoseFixB1.PerSectorSmooth v h R` — FS `thm:smallbox`
read on a single occupancy sector of the sliding box with the `F`-weight at the *smooth* density
`t = nCountB/chiMass` (a function of the configuration alone).

## What this file contains

* `SectorSmoothIneq` — the displayed inequality of `PerSectorSmooth` at *fixed* constants
  `c, C`, so that the two case-cores below can be stated without repeating it;
* `PerSectorSmoothAt` — `PerSectorSmooth` with the constants exhibited;
* `sectorDensLow` / `PerSectorSmoothLowDensAt` / `PerSectorSmoothHighDensAt` — the **case split**
  on the mean smooth density `∫Φ_k²·t` versus `μ·m_k` (the corpus's own
  `psiWeight_one_le_mu_sq` threshold: `F(t) ≤ μ²` for `t ≤ 2μ`), i.e. FS's "flat vs dense"
  dichotomy at the *smooth* weight;
* `perSectorSmoothAt_of_cases` — the (trivial) assembly of the two cases at *equal* constants;
* `perSectorSmoothAt_mono` — monotonicity of the constant triple (`c` down, `C` up, `ε₀` down),
  which is what reconciles the two cores' constants;
* `perSectorSmooth_of_cores` — **the reduction**: `PerSectorSmooth` follows from its two case-cores;
* `perSectorSmooth_holds` — the target, still carrying its `sorry` pending the cores.

`FINDING_perSectorSmooth_route.md` records the ledger, the reason the `K_peak`/"profile" pathology
of the sibling residuals does *not* apply here (the fibre cost is weighted by the *same* local
`χ_B(x)²` as the debit), the two exact missing ingredients (the *plateau-normalised* fibre bound and
the dense-regime `A₂`/pairing ledger), and the families that kill the siblings but satisfy this
statement.  This file is a SKELETON: it is not in the Solution closure and does not carry the target.
-/

namespace Work.BoseFixB1

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding Work.FockBridge

set_option autoImplicit false
set_option linter.unusedVariables false

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

/-- **The displayed inequality of `PerSectorSmooth` at fixed constants**: the verbatim body of
`PerSectorSmooth`, with the constants `c, C` exhibited (so that it can be reused by the two
case-cores). -/
def SectorSmoothIneq (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) (R : ℝ)
    (c C μ : ℝ) {n : ℕ} (Φ : Work.BoseKinLoc.BoxState n (bSide v μ))
    (u : EuclideanSpace ℝ (Fin 3)) (k : ℕ) : Prop :=
  c * (bW v h μ u *
      (∫ x in abox n (bSide v μ),
        (sectorPiece (bA v μ u) k (Φ : X n → ℝ) x) ^ 2 *
          psiWeight 1 μ (nCountB (bM v μ) (bSide v μ) (bD v μ) u x
            / chiMass (bM v μ) (bSide v μ) (bD v μ) u)))
  - (1 / 2) * μ ^ 2 * bW v h μ u
      * sectorMass (bSide v μ) (bA v μ u) (Φ : X n → ℝ) k
  - C * bErr v R μ u * sectorMass (bSide v μ) (bA v μ u) (Φ : X n → ℝ) k
  ≤ sbKin (v := v) μ (bM v μ) u (sectorPiece (bA v μ u) k (Φ : X n → ℝ))
    + sbPot h μ u (sectorPiece (bA v μ u) k (Φ : X n → ℝ))

/-- **The mean smooth density of the sector piece**, against the background `μ·m_k`:
`∫Φ_k²·t ≤ μ·m_k` with `t = nCountB/chiMass`. -/
def sectorDensLow (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) {n : ℕ}
    (Φ : Work.BoseKinLoc.BoxState n (bSide v μ)) (u : EuclideanSpace ℝ (Fin 3)) (k : ℕ) : Prop :=
  (∫ x in abox n (bSide v μ),
      (sectorPiece (bA v μ u) k (Φ : X n → ℝ) x) ^ 2 *
        (nCountB (bM v μ) (bSide v μ) (bD v μ) u x
          / chiMass (bM v μ) (bSide v μ) (bD v μ) u))
    ≤ μ * sectorMass (bSide v μ) (bA v μ u) (Φ : X n → ℝ) k

/-- `PerSectorSmooth` with the constants exhibited. -/
def PerSectorSmoothAt (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) (R : ℝ)
    (ε₀ c C : ℝ) : Prop :=
  ∀ μ : ℝ, Adm v ε₀ μ →
    ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (bSide v μ))
      (u : EuclideanSpace ℝ (Fin 3)),
      u ∈ goodSet (bSide v μ) (bD v μ) μ →
      ∀ k ∈ Finset.range (n + 1), SectorSmoothIneq v h R c C μ Φ u k

/-- **The low-density core** (the case `∫Φ_k²t ≤ μ·m_k`): the statement is *implied* by the
`F(t) ≤ μ²` bound (`Work.BoseFixB1S.psiWeightShapeB1.psiWeight_one_le_mu_sq`) for the debit, so the
only content is the fibre cost — see `FINDING_perSectorSmooth_route.md` §7. -/
def PerSectorSmoothLowDensAt (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) (R : ℝ)
    (ε₀ c C : ℝ) : Prop :=
  ∀ μ : ℝ, Adm v ε₀ μ →
    ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (bSide v μ))
      (u : EuclideanSpace ℝ (Fin 3)),
      u ∈ goodSet (bSide v μ) (bD v μ) μ →
      ∀ k ∈ Finset.range (n + 1), sectorDensLow v μ Φ u k → SectorSmoothIneq v h R c C μ Φ u k

/-- **The high-density core** (the case `¬ ∫Φ_k²t ≤ μ·m_k`): FS's dense/condensed ledger at the
smooth weight — the corpus's frontier (`DenseArm` / `SectorCountSmallboxBox` / `flatArmSliding`).
See `FINDING_perSectorSmooth_route.md` §3–§4. -/
def PerSectorSmoothHighDensAt (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) (R : ℝ)
    (ε₀ c C : ℝ) : Prop :=
  ∀ μ : ℝ, Adm v ε₀ μ →
    ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (bSide v μ))
      (u : EuclideanSpace ℝ (Fin 3)),
      u ∈ goodSet (bSide v μ) (bD v μ) μ →
      ∀ k ∈ Finset.range (n + 1), ¬ sectorDensLow v μ Φ u k → SectorSmoothIneq v h R c C μ Φ u k

/-- **The assembly at equal constants**: the two case-cores give `PerSectorSmoothAt`, because
`sectorDensLow` is decidable and the two cores cover the two branches. -/
theorem perSectorSmoothAt_of_cases {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {R ε₀ c C : ℝ} (hL : PerSectorSmoothLowDensAt v h R ε₀ c C)
    (hH : PerSectorSmoothHighDensAt v h R ε₀ c C) :
    PerSectorSmoothAt v h R ε₀ c C := by
  intro μ hμ n Φ u hu k hk
  by_cases hd : sectorDensLow v μ Φ u k
  · exact hL μ hμ n Φ u hu k hk hd
  · exact hH μ hμ n Φ u hu k hk hd

/-! ## Monotonicity of the constant triple

`SectorSmoothIneq` reads `c·X − ½μ²bW·m_k − C·Y ≤ (the word)` with `X = bW·∫Φ_k²F(t) ≥ 0` and
`Y = bErr·m_k ≥ 0`.  Hence lowering `c` (keeping `bW ≥ 0`) and raising `C` (keeping
`bErr·m_k ≥ 0`) only makes the left-hand side smaller, and lowering `ε₀` shrinks the admissible
`μ`-range (`Work.BoseBoxFix.Adm.mono`). -/

lemma bW_nonneg {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} (hv : 0 ≤ v)
    (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) {ε₀ μ : ℝ}
    (hadm : Adm v ε₀ μ) (u : EuclideanSpace ℝ (Fin 3)) : 0 ≤ bW v h μ u :=
  w1MassB_nonneg (v := v) (M := bM v μ) (ℓ := bSide v μ) (d := bD v μ) h hv hvrad hR hv_supp
    (adm_ell_pos hadm) (adm_d_pos hadm) u

lemma sectorMass_nonneg {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ} {n : ℕ}
    (Φ : Work.BoseKinLoc.BoxState n (bSide v μ)) (u : EuclideanSpace ℝ (Fin 3)) (k : ℕ) :
    0 ≤ sectorMass (bSide v μ) (bA v μ u) (Φ : X n → ℝ) k :=
  ENNReal.toReal_nonneg

lemma bErr_nonneg {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    {ε₀ μ : ℝ} (hadm : Adm v ε₀ μ) {R : ℝ} (hR : 0 < R) (u : EuclideanSpace ℝ (Fin 3)) :
    0 ≤ bErr v R μ u := by
  have hμ : 0 < μ := hadm.1
  have ha : 0 ≤ a v := le_of_lt (adm_a_pos hadm)
  have hsu : 0 ≤ (R / (bSide v μ * bD v μ)) ^ 2 := sq_nonneg _
  have hKB : 0 ≤ (paramsAt μ (a v)).KB := le_of_lt (paramsAt_KB_pos hadm)
  have hr : 0 ≤ (μ * (a v) ^ 3) ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg (mul_nonneg hμ.le (pow_nonneg ha 3)) _
  have hchi : 0 ≤ chiMass (bM v μ) (bSide v μ) (bD v μ) u := chiMass_nonneg _ _ _ _
  have hΓ : 0 ≤ (R / (bSide v μ * bD v μ)) ^ 2
      + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ) := by
    have : 0 ≤ (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ) :=
      mul_nonneg (pow_nonneg hKB 3) hr
    linarith
  simp only [bErr, bM, bSide, bD]
  have h1 : 0 ≤ μ ^ 2 * a v * ((R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
      + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
      * chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u :=
    mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg μ) ha) hΓ) hchi
  have h2 : 0 ≤ μ * a v := mul_nonneg hμ.le ha
  linarith

/-- **Monotonicity of `SectorSmoothIneq` in the constants.**  The left side reads
`c·X − ½μ²·bW·m_k − C·Y` with `X = bW·∫Φ_k²F(t) ≥ 0` and `Y = bErr·m_k ≥ 0`; lowering `c` and
raising `C` therefore only lowers it. -/
lemma SectorSmoothIneq_mono {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {R : ℝ} (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) (hR : 0 < R)
    {ε₀ c C c' C' μ : ℝ} (hadm : Adm v ε₀ μ) (hc : c' ≤ c) (hC : C ≤ C')
    {n : ℕ} (Φ : Work.BoseKinLoc.BoxState n (bSide v μ)) (u : EuclideanSpace ℝ (Fin 3)) (k : ℕ)
    (hmain : SectorSmoothIneq v h R c C μ Φ u k) :
    SectorSmoothIneq v h R c' C' μ Φ u k := by
  have hμ₀ : 0 < μ := hadm.1
  have hW : 0 ≤ bW v h μ u := bW_nonneg hv hvrad hR hv_supp hadm u
  have hm : 0 ≤ sectorMass (bSide v μ) (bA v μ u) (Φ : X n → ℝ) k :=
    sectorMass_nonneg Φ u k
  have hE : 0 ≤ bErr v R μ u := bErr_nonneg h hadm hR u
  have hI : 0 ≤ (∫ x in abox n (bSide v μ),
        (sectorPiece (bA v μ u) k (Φ : X n → ℝ) x) ^ 2 *
          psiWeight 1 μ (nCountB (bM v μ) (bSide v μ) (bD v μ) u x
            / chiMass (bM v μ) (bSide v μ) (bD v μ) u)) := by
    apply integral_nonneg
    intro x
    have ht : 0 ≤ nCountB (bM v μ) (bSide v μ) (bD v μ) u x
        / chiMass (bM v μ) (bSide v μ) (bD v μ) u := by
      apply div_nonneg
      · simp only [nCountB]
        exact Finset.sum_nonneg fun i _ => sq_nonneg _
      · exact chiMass_nonneg _ _ _ _
    have hps : 0 ≤ psiWeight 1 μ (nCountB (bM v μ) (bSide v μ) (bD v μ) u x
        / chiMass (bM v μ) (bSide v μ) (bD v μ) u) := by
      have hden : 0 ≤ 1 + (nCountB (bM v μ) (bSide v μ) (bD v μ) u x
          / chiMass (bM v μ) (bSide v μ) (bD v μ) u) * μ⁻¹ := by
        have := mul_nonneg ht (le_of_lt (inv_pos.mpr hμ₀))
        linarith
      simp only [psiWeight, one_mul]
      exact div_nonneg (sq_nonneg _) hden
    exact mul_nonneg (sq_nonneg _) hps
  have hX : 0 ≤ bW v h μ u * (∫ x in abox n (bSide v μ),
        (sectorPiece (bA v μ u) k (Φ : X n → ℝ) x) ^ 2 *
          psiWeight 1 μ (nCountB (bM v μ) (bSide v μ) (bD v μ) u x
            / chiMass (bM v μ) (bSide v μ) (bD v μ) u)) := mul_nonneg hW hI
  have hY : 0 ≤ bErr v R μ u * sectorMass (bSide v μ) (bA v μ u) (Φ : X n → ℝ) k :=
    mul_nonneg hE hm
  have hstep : c' * (bW v h μ u * (∫ x in abox n (bSide v μ),
        (sectorPiece (bA v μ u) k (Φ : X n → ℝ) x) ^ 2 *
          psiWeight 1 μ (nCountB (bM v μ) (bSide v μ) (bD v μ) u x
            / chiMass (bM v μ) (bSide v μ) (bD v μ) u)))
      - C' * (bErr v R μ u * sectorMass (bSide v μ) (bA v μ u) (Φ : X n → ℝ) k)
      ≤ c * (bW v h μ u * (∫ x in abox n (bSide v μ),
        (sectorPiece (bA v μ u) k (Φ : X n → ℝ) x) ^ 2 *
          psiWeight 1 μ (nCountB (bM v μ) (bSide v μ) (bD v μ) u x
            / chiMass (bM v μ) (bSide v μ) (bD v μ) u)))
      - C * (bErr v R μ u * sectorMass (bSide v μ) (bA v μ u) (Φ : X n → ℝ) k) := by
    nlinarith [mul_le_mul_of_nonneg_right hc hX, mul_le_mul_of_nonneg_right hC hY]
  simp only [SectorSmoothIneq] at hmain ⊢
  nlinarith [hstep, hmain]

/-- **Monotonicity in the constant triple.** -/
theorem perSectorSmoothAt_mono {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {R : ℝ} (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) (hR : 0 < R)
    (hav : 0 < a v) {ε₀ c C ε₀' c' C' : ℝ} (hε : ε₀' ≤ ε₀) (hc : c' ≤ c) (hC : C ≤ C')
    (hmain : PerSectorSmoothAt v h R ε₀ c C) :
    PerSectorSmoothAt v h R ε₀' c' C' := by
  intro μ hμ n Φ u hu k hk
  exact SectorSmoothIneq_mono hv hvrad hv_supp hR (Adm.mono hμ hε) hc hC Φ u k
    (hmain μ (Adm.mono hμ hε) n Φ u hu k hk)

/-- **The reduction**: `PerSectorSmooth` follows from its two case-cores.  (The cores are exactly
the two halves of FS's `thm:smallbox` dichotomy re-run at the smooth weight.) -/
theorem perSectorSmooth_of_cores {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {R ε₁ c₁ C₁ ε₂ c₂ C₂ : ℝ} (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) (hR : 0 < R)
    (hav : 0 < a v) (hε₁ : 0 < ε₁) (hc₁ : 0 < c₁) (hC₁ : 0 ≤ C₁)
    (hε₂ : 0 < ε₂) (hc₂ : 0 < c₂) (hC₂ : 0 ≤ C₂)
    (hL : PerSectorSmoothLowDensAt v h R ε₁ c₁ C₁)
    (hH : PerSectorSmoothHighDensAt v h R ε₂ c₂ C₂) :
    PerSectorSmooth v h R := by
  refine ⟨min ε₁ ε₂, min c₁ c₂, max C₁ C₂, lt_min hε₁ hε₂, lt_min hc₁ hc₂,
    le_max_of_le_left hC₁, ?_⟩
  intro μ hμ n Φ u hu k hk
  have hε : min ε₁ ε₂ ≤ ε₁ := min_le_left _ _
  have hε' : min ε₁ ε₂ ≤ ε₂ := min_le_right _ _
  have hc : min c₁ c₂ ≤ c₁ := min_le_left _ _
  have hc' : min c₁ c₂ ≤ c₂ := min_le_right _ _
  have hC : C₁ ≤ max C₁ C₂ := le_max_left _ _
  have hC' : C₂ ≤ max C₁ C₂ := le_max_right _ _
  have hμ₁ : Adm v ε₁ μ := Adm.mono (ε₀' := min ε₁ ε₂) (ε₀ := ε₁) hμ hε
  have hμ₂ : Adm v ε₂ μ := Adm.mono (ε₀' := min ε₁ ε₂) (ε₀ := ε₂) hμ hε'
  by_cases hd : sectorDensLow v μ Φ u k
  · exact SectorSmoothIneq_mono hv hvrad hv_supp hR (Adm.mono hμ hε) hc hC Φ u k
      (hL μ hμ₁ n Φ u hu k hk hd)
  · exact SectorSmoothIneq_mono hv hvrad hv_supp hR (Adm.mono hμ hε') hc' hC' Φ u k
      (hH μ hμ₂ n Φ u hu k hk hd)

theorem perSectorSmooth_holds {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) :
    Work.BoseFixB1.PerSectorSmooth v h R := by sorry

end Work.BoseFixB1
