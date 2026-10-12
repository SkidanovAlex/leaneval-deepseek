import ChallengeDeps
import Submission.Work.BoseFixB1S.boxPairQCount_eqB1
import Submission.Work.BoseFixB1S.boxPeelGen
import Submission.Work.BoseFixB1S.boxQSum_sub_boxA2_blockSum
import Submission.Work.BoseFixB1S.boxSupport_count_eq
import Submission.Work.BoseFixB1S.mf_boxQ0_ge_flatCount
import Submission.Work.BoseFixB1S.perBoxGapBranchB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1S.mfRows` — the flat-branch rows of
# `Work.BoseFixB1S.perBoxMeanFieldB1`, in the `mf*` vocabulary

This module fixes the *objects* of the flat branch's Cauchy–Schwarz rows (the pair counts and the
weighted pair masses) and proves the one purely combinatorial identity of the branch, the count
split `S + Q = n‖Φ‖²` (`mfCountSplit`).  The four *estimates* on these objects are proved in
sibling modules (`mfPairRowLower`, `mfA2RowLower`, `mfFibLines`, `perBoxGapBranchB1Gen`).

Notation (all at FS's parameters: `ℓ = sideAt μ (a v)`, `d = (paramsAt μ (a v)).d`,
`V = mfV v μ u = boxMass ℓ d u`, `A = boxA v μ u = dlBox ℓ d u`, `w₁ = boxW1 h μ u`):

* `mfS v μ n Φ u = Σᵢ∫(P_iΦ)²` — the condensate count;
* `mfQ v μ n Φ u = Σᵢ∫(Q_iΦ)²` — the excited count (`cnPlusBoxInd`);
* `mfPc v μ n Φ u = Σ_{i≠j}∫(P_iP_jΦ)²` — the condensate pair count;
* `mfPCMass h μ n Φ u = Σ_{i≠j}∫(P_iQ_jΦ)²w₁` (`(P Q)`-mass, bounded by `boxPQw_mass_leB1`);
* `mfPPMass h μ n Φ u = Σ_{i≠j}∫(P_iP_jΦ)²w₁` (equal to `(M₁/V²)·Pc`, `boxWeightedPairMass`);
* `mfQQMass h μ n Φ u = Σ_{i≠j}∫(Q_iQ_jΦ)²w₁` (the `A₂`-pairing partner mass);
* `mfPairBlockSum h μ n Φ u = ½Σ_{i≠j}∫block` (the exact potsplit pair block);
* `mfFibQ`, `mfFibQP` — the two `μ`-fibre lines;
* `mfA2 h μ n Φ u` — FS's pairing word `A₂` at the box projections.
-/

namespace Work.BoseFixB1S

open MeasureTheory Metric Filter
open scoped Real Topology BigOperators ENNReal
open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding Work.BoseFixB1

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

/-! ## 1. The objects -/

/-- The condensate pair count `Pc = Σ_{i≠j}∫(P_iP_jΦ)²`. -/
abbrev mfPc (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) (n : ℕ)
    (Φ : Submission.BoseGases.X n → ℝ) (u : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  boxPairCount (mfV v μ u) (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) (boxA v μ u) Φ

/-- The unweighted `(P Q)`-pair count `⟨n₀n₊⟩ = Σ_{i≠j}∫(P_iQ_jΦ)²` (the operator expectation
of `n₀n₊`; `mfPCMass` is its `w₁`-weighted version). -/
abbrev mfN0NQ (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) (n : ℕ)
    (Φ : Submission.BoseGases.X n → ℝ) (u : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  ∑ p ∈ Submission.BoseGases.pairSet n,
    ∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
      (Work.UBBInputs8.boxPInd (mfV v μ u) (boxA v μ u) p.1
        (Work.UBBInputs8.boxQInd (mfV v μ u) (boxA v μ u) p.2 Φ) x) ^ 2

/-- The `w₁`-weighted `(P Q)`-pair mass `Σ_{i≠j}∫(P_iQ_jΦ)²w₁`. -/
abbrev mfPCMass {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) (μ : ℝ) (n : ℕ)
    (Φ : Submission.BoseGases.X n → ℝ) (u : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  ∑ p ∈ Submission.BoseGases.pairSet n,
    ∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
      (Work.UBBInputs8.boxPInd (mfV v μ u) (boxA v μ u) p.1
        (Work.UBBInputs8.boxQInd (mfV v μ u) (boxA v μ u) p.2 Φ) x) ^ 2
        * boxW1 h μ u (x p.1) (x p.2)

/-- The `w₁`-weighted `(P P)`-pair mass `Σ_{i≠j}∫(P_iP_jΦ)²w₁`. -/
abbrev mfPPMass {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) (μ : ℝ) (n : ℕ)
    (Φ : Submission.BoseGases.X n → ℝ) (u : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  ∑ p ∈ Submission.BoseGases.pairSet n,
    ∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
      (Work.UBBInputs8.boxPInd (mfV v μ u) (boxA v μ u) p.1
        (Work.UBBInputs8.boxPInd (mfV v μ u) (boxA v μ u) p.2 Φ) x) ^ 2
        * boxW1 h μ u (x p.1) (x p.2)

/-- The `w₁`-weighted `(Q Q)`-pair mass `Σ_{i≠j}∫(Q_iQ_jΦ)²w₁`. -/
abbrev mfQQMass {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) (μ : ℝ) (n : ℕ)
    (Φ : Submission.BoseGases.X n → ℝ) (u : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  ∑ p ∈ Submission.BoseGases.pairSet n,
    ∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
      (Work.UBBInputs8.boxQInd (mfV v μ u) (boxA v μ u) p.2
        (Work.UBBInputs8.boxQInd (mfV v μ u) (boxA v μ u) p.1 Φ) x) ^ 2
        * boxW1 h μ u (x p.1) (x p.2)

/-- The pair-block sum `½Σ_{i≠j}∫block` of the exact potsplit identity. -/
abbrev mfPairBlockSum {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) (μ : ℝ)
    (n : ℕ) (Φ : Submission.BoseGases.X n → ℝ) (u : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  (1 / 2) * ∑ p ∈ Submission.BoseGases.pairSet n,
    ∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
      boxPairBlock (mfV v μ u) (boxA v μ u) (boxW h μ u) (omC (Classical.choose h)) Φ p x

/-- The `Q`-fibre line `Σ_i∫(Q_iΦ)²·fib(x_i)`. -/
abbrev mfFibQ {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) (μ : ℝ) (n : ℕ)
    (Φ : Submission.BoseGases.X n → ℝ) (u : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  ∑ i : Fin n,
    ∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
      (Work.UBBInputs8.boxQInd (mfV v μ u) (boxA v μ u) i Φ x) ^ 2
        * Submission.BoseGases.w1Fibre (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (boxW1 h μ u) (x i)

/-- The cross fibre line `Σ_i∫(Q_iΦ)(P_iΦ)·fib(x_i)`. -/
abbrev mfFibQP {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) (μ : ℝ) (n : ℕ)
    (Φ : Submission.BoseGases.X n → ℝ) (u : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  ∑ i : Fin n,
    ∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
      (Work.UBBInputs8.boxQInd (mfV v μ u) (boxA v μ u) i Φ x)
        * (Work.UBBInputs8.boxPInd (mfV v μ u) (boxA v μ u) i Φ x)
        * Submission.BoseGases.w1Fibre (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (boxW1 h μ u) (x i)

/-- FS's pairing word `A₂` at the box projections. -/
abbrev mfA2 {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) (μ : ℝ) (n : ℕ)
    (Φ : Submission.BoseGases.X n → ℝ) (u : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  boxA2 (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) (mfV v μ u) (boxA v μ u)
    (boxW1 h μ u) Φ

/-! ## 2. Two definitional identifications -/

/-- The excited count is the box `Q`-count. -/
theorem mfQ_eq_boxQCount {v : EuclideanSpace ℝ (Fin 3) → ℝ} (μ : ℝ) (n : ℕ)
    (Φ : Submission.BoseGases.X n → ℝ) (u : EuclideanSpace ℝ (Fin 3)) :
    mfQ v μ n Φ u
      = boxQCount (mfV v μ u) (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) (boxA v μ u)
          Φ := rfl

/-- The condensate count is the box flat count. -/
theorem mfS_eq_boxFlatCount {v : EuclideanSpace ℝ (Fin 3) → ℝ} (μ : ℝ) (n : ℕ)
    (Φ : Submission.BoseGases.X n → ℝ) (u : EuclideanSpace ℝ (Fin 3)) :
    mfS v μ n Φ u
      = boxFlatCount (mfV v μ u) (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) (boxA v μ u)
          Φ := rfl

/-! ## 3. The count split -/

/-- **The box count split**: `S + Q = n‖Φ‖²` for box-supported states.

Proof: `boxC1_add_cnPlus` (Parseval at the box projections,
`Σᵢ∫(P_iΦ)² + Σᵢ∫(Q_iΦ)² = Σᵢ∫1_A(x_i)Φ²`) combined with `boxSupport_count_eq`
(`Σᵢ∫1_A(x_i)Φ² = n‖Φ‖²` on the box-support set of the target). -/
theorem mfCountSplit {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ} {n : ℕ}
    {Φ : Submission.BoseGases.X n → ℝ} {u : EuclideanSpace ℝ (Fin 3)}
    (hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (hΦc : Continuous Φ) (hsupp : mfSupp v μ n Φ u) :
    mfS v μ n Φ u + mfQ v μ n Φ u = (n : ℝ) * mfI v μ n Φ := by
  have h1 := boxC1_add_cnPlus (N := n) (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (d := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) hℓ u hΦc
  have h2 := boxSupport_count_eq (v := v) (μ := μ) (n := n) (Φ := Φ) (u := u) hsupp
  rw [mfS_eq_boxFlatCount, mfQ_eq_boxQCount]
  simp only [boxFlatCount, boxQCount, boxA, mfV, Work.UBBInputs8.cnPlusBoxInd] at h1 ⊢
  rw [h1, h2]

end

end Work.BoseFixB1S
