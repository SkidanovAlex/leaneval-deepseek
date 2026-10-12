import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1.BoxA2
import Submission.Work.BoseFixR.PerBoxCrudeDefs
import Submission.Work.BoseFixR.SlabCountSplit
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixR

set_option linter.unusedVariables false

/-!
# `Work.BoseFixR.SlabCondensedHalf` — the condensed arm of the crude per-box bound

## The ledger (what this node still owes)

`Submission/Work/BoseFixR/FINDING_SlabCondensedHalf.md` (session 1) and
`..._SESSION2.md` (session 2) record the full analysis.  In brief, with
`ℓ = sideAt μ (a v)`, `V = boxMass ℓ d u`, `A = dlBox ℓ d u`, `M = mValue`,
`w = wSmallPair M ℓ d u v`, `w₁ = wSmall1Pair h M ℓ d u`, `w₂ = wSmallPair M ℓ d u (g₂ v h)`,
`ω = omC (choose h)`, and the box counts `S = boxFlatCount`, `nq = boxQCount`,
`Pc = boxPairCount`, `M₁ = boxM1 ℓ A w₁`, `M₂ = boxM2 V A w₂`, `J = normB`, `X = chiMass`:

* `Work.BoseFixR.BoxPotsplitSliding` (PROVED): `sbWord = sbKin + boxQSum` at the sliding kernels;
* `sbKin ≥ 0` (`Work.BoseFixB1.perBoxF_pieces.sbKin_ge_mu_av_cnPlus`, PROVED), and the
  *indefinite* `boxA2` (FS's `A₂`, linear in the excitation amplitude) is **paid separately** —
  that is rung 3, FS `lm:appbogolubov` / `Work.MGroupInput.SimpleA2Two`; it is *not* a step here;
* `Work.BoseFixR.SlabCountSplit` (PROVED): `S + nq = cnt`, so the node's hypothesis
  `(1/2)·cnt ≤ S` (the `boxPInd` count) gives `nq ≤ S`;
* the analytic input is FS `lm:appinteractionestimate` at the sliding box **in FS's own `A₀`
  form** (see below), i.e. `A₀ + A₂ − C a(v)(μ + S/V) nq ≤ boxQSum` with
  `A₀ = ½(M₂/V²)Pc − μ(M₁/V)S − ¼M₁(μ − (S−1)/V)²`
  (the draft's `(S+1)` is a typo — refuted at `n = 1`, see `_SESSION2.md` §0), and `boxA2` *must* be
  kept on the left (it sits inside `boxQSum` with a `+` sign);
* the *ledger* is then the pure-real arithmetic of `armBLedger_kernel` below: with
  `S ≤ N·J` (each `∫(PᵢΦ)² ≤ ∫Φ²`), `nq ≤ S`, `hcS2` (`Pc ≥ S² − S`) and the normalization
  `J = 1` (the statement is homogeneous of degree 2 in `Φ`), the box lower bound is a quadratic
  `A S² − B S` in `S` with `A = (2M₂ − M₁)/(4V²) − C a(v)/V`, and it stays above
  `−(C′)(μ² a(v)X + μ a(v))J` **iff** `C ≤ (2M₂ − M₁)/(4 a(v) V) ≈ 2πχ̄²(1+2ϖ)`.

**Do not use the `a0MainLocBox` form** (`boxQSum_ge_a0Main_add_A2R`, `boxCrossJoint`,
`boxCrossLower`): it spends the `pcb` slack `½(M₂/V²)Pc − ½(M₁/V²)(S²−S)` before handing over and
then the `S²`-condition is the much tighter `C ≤ M₁/(4a(v)V) ≈ 2πχ̄²`.  Likewise the `pcb`-free
strengthening `Sqp + L + credit ≥ 2μP + μQ` is **FALSE** (the reviewer's `N = 1`,
`Φ = 1 + kψ` counterexample, `_SESSION2.md` §2).

## Proved pieces this node can import (session 3) — and the import-graph constraint

* **`Work.BoseFixR.ArmBLedgerCrude`** (`…/ArmBLedgerCrude.lean`, **PROVED, axiom-clean**): Piece 1,
  `sbWord ≥ c'²μa(v)·nq − kav·μa(v)·occChi` with `c' ≥ 0` free, at the sliding data (from `Adm`,
  the gap régime, the FS geometry).  Its cone does **not** import this file, so it is importable
  here (unlike `Work.BoseFixB1B.sbCore`, the same statement, which sits in `perBoxCrudeLower.lean`
  — and that file imports *this* one, so it may not be imported here: see `_SESSION2.md` §11).
* **`Work.BoseFixR.ArmBLedgerArith`** (PROVED, axiom-clean): the pure-real ledger
  `½(M₂/V²)Pc − μ(M₁/V)S − ¼M₁(μ−(S−1)/V)² − C·aa(μ+S/V)nq ≥ −C′(μ²aaX + μaa)`
  under `μV ≥ 1`, `S²−S ≤ Pc`, `nq ≤ S`, `0 < (2M₂−M₁)/(4V²) − C·aa/V`.
* **`Work.BoseFixR.PIndFibreBilinearCollapse`** (PROVED, axiom-clean): the P-side sandwich collapse
  `Σᵢ∫f(xᵢ)(PᵢΨ)(PᵢΞ) = κ·Σⱼ∫(PⱼΨ)Ξ` (i.e. `Loss_P = κ⟨n₀(n₀+μV)⟩`).
* `armBLedger_kernel` / `armBLedger_kernel_add` below (`A S² − B S ≥ −B²/(4A)`, `A > 0`).
* **What is left is this file's own job** (it is equivalent to the node's conclusion given Piece 1
  and `SlabCountSplit`, hence not delegable): the supply that pays `kav·C_s·μa(v)·S` — the pair
  energy for the flat states (`nq ≪ S`; use the proved pair-manifold identities
  `boxPairManifestSumB1S`, `pairFive_add_swap`, `boxQ0_value`, `pairSqOmegaLowerB1`) together with
  the free `c'` for the "hole" states (`pairSum = 0`, `nq ≠ 0`).  See `_SESSION2.md` §10–§12.
* The refuted filings (`BoxCondensedArmQSum`, `BoxQSumA0FormBound`, `BoxQSumFsA0Pair`,
  `BoxQSumFsA0Occ`, `PairSumOccMeanField`, `PairSumOccJensen`) must **not** be re-filed in the same
  shape: `_SESSION2.md` §2, §5, §7, §9, §10 record the machine-checked witnesses against each.
* **`Work.BoseFixR.PIndFibreBilinearCollapse`** (`.../PIndFibreBilinearCollapse.lean`) — the P-side
  sandwich collapse `Σᵢ∫ f(xᵢ)(PᵢΨ)(PᵢΞ) = κ·Σⱼ∫(PⱼΨ)Ξ` (the bilinear form of the PROVED
  `boxPIndFibreMassB1`; it is the `Loss_P = κ⟨n₀(n₀+μV)⟩`-sandwich every route to the crux needs).
  Reviewer-verified correct; proof: `boxPInd_slotCollapse` + self-adjointness/idempotence of `Pᵢ`.
-/

/-- **The arm-B ledger kernel.**  For `A > 0` and every `S`, the quadratic `A S² − B S` is bounded
below by `−B²/(4A)`.  This is the pure-real step of the ledger: with `A` the `S²`-coefficient of
`½(M₂/V²)Pc − μ(M₁/V)S − ¼M₁(μ − (S−1)/V)² − C a(v)(μ + S/V)·S` (using `Pc ≥ S² − S`,
`nq ≤ S`) and `B` its `S`-coefficient, it pays every `μ`-power against
`C′(μ²a(v)X + μa(v))J` for a fixed `C′` (all constants free). -/
lemma armBLedger_kernel {A B S : ℝ} (hA : 0 < A) :
    -(B ^ 2 / (4 * A)) ≤ A * S ^ 2 - B * S := by
  have h4A : 0 < 4 * A := by linarith
  rw [← neg_div, div_le_iff₀ h4A]
  nlinarith [sq_nonneg (2 * A * S - B)]

/-- The same kernel in the form used by the ledger: `A S² − B S + K ≥ −(B²/(4A)) + K` is what the
assembly produces once the box estimate has been instantiated; recorded so that the arithmetic is
never redone. -/
lemma armBLedger_kernel_add {A B S K : ℝ} (hA : 0 < A) :
    -(B ^ 2 / (4 * A)) + K ≤ A * S ^ 2 - B * S + K := by
  linarith [armBLedger_kernel (A := A) (B := B) (S := S) hA]

/-- **The analytic input this node consumes** (FS `lm:appinteractionestimate` at the sliding box
`B(u)`, in FS's own `A₀` form, with the sliding kernels and the `Adm`-free geometry): there is
`C ≥ 0` such that for every admissible geometric datum and every continuous box state,

`½(M₂/V²)Pc − μ(M₁/V)S − ¼M₁(μ − (S−1)/V)² + boxA2 − C a(v)(μ + S/V)nq ≤ boxQSum`,

where `boxQSum` is the corpus's five-word sum at the sliding kernels.

Kept as a `Prop` so that the assembly below is machine-checked *now* and only this one analytic
statement is missing (it is strictly *stronger* than `Work.BoseFixB1S.boxCrossJoint` /
`Work.BoseFixB1.boxCrossLower`, which drop `pcb` and `M₁μ/V`; see `FINDING_...SESSION2.md` §1). -/
def BoxQSumA0FormInput (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ {ℓ d μ : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hμ : 0 < μ)
      (hR16 : R ≤ ℓ * d / 16) (hRχ : R ≤ ℓ * Submission.BoseGases.chiR0)
      (u : EuclideanSpace ℝ (Fin 3)) (hvol : 0 < Work.SmallBoxSliding.boxMass ℓ d u)
      (hμv : 1 ≤ μ * Work.SmallBoxSliding.boxMass ℓ d u)
      {N : ℕ} {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
      (hcS2 : Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                  (Submission.BoseGases.dlBox ℓ d u) Φ
                * Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                  (Submission.BoseGases.dlBox ℓ d u) Φ
              - Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                  (Submission.BoseGases.dlBox ℓ d u) Φ
            ≤ Work.BoseFixB1S.boxPairCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                (Submission.BoseGases.dlBox ℓ d u) Φ),
      (1 / 2) * (Work.BoseFixB1S.boxM2 (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u)
              (Submission.BoseGases.wSmallPair Work.BoseBox.mValue ℓ d u
                (Submission.BoseGases.g2 v h))
              / Work.SmallBoxSliding.boxMass ℓ d u ^ 2)
          * Work.BoseFixB1S.boxPairCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
              (Submission.BoseGases.dlBox ℓ d u) Φ
        - μ * (Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
                (Submission.BoseGases.wSmall1Pair h Work.BoseBox.mValue ℓ d u)
              / Work.SmallBoxSliding.boxMass ℓ d u)
            * Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                (Submission.BoseGases.dlBox ℓ d u) Φ
        - (1 / 4) * Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
            (Submission.BoseGases.wSmall1Pair h Work.BoseBox.mValue ℓ d u)
          * (μ - (Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                      (Submission.BoseGases.dlBox ℓ d u) Φ - 1)
                  / Work.SmallBoxSliding.boxMass ℓ d u) ^ 2
        + Work.BoseFixB1.boxA2 ℓ (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u)
            (Submission.BoseGases.wSmall1Pair h Work.BoseBox.mValue ℓ d u) Φ
        - C * (_root_.BoseGases.a v)
            * (μ + Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                  (Submission.BoseGases.dlBox ℓ d u) Φ
                / Work.SmallBoxSliding.boxMass ℓ d u)
            * Work.BoseFixB1S.boxQCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                (Submission.BoseGases.dlBox ℓ d u) Φ
      ≤ Work.BoseFixB1S.boxQSum (Work.SmallBoxSliding.boxMass ℓ d u) ℓ μ
          (Submission.BoseGases.dlBox ℓ d u)
          (Submission.BoseGases.wSmallPair Work.BoseBox.mValue ℓ d u v)
          (Submission.BoseGases.wSmall1Pair h Work.BoseBox.mValue ℓ d u)
          (Submission.BoseGases.wSmallPair Work.BoseBox.mValue ℓ d u
            (Submission.BoseGases.g2 v h))
          (Submission.BoseGases.omC (Classical.choose h)) Φ

theorem SlabCondensedHalf {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ K C : ℝ, 0 < ε₀ ∧ 0 < K ∧ 0 ≤ C ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
          (u : EuclideanSpace ℝ (Fin 3)),
          Work.BoseFixR.occChi (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
              (Φ : Submission.BoseGases.X n → ℝ)
            ≥ K * (μ * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u + 1)
              * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) →
          (1 / 2 : ℝ) * (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
              ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2 *
                (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u).indicator
                  (fun _ => (1 : ℝ)) (x i))
            ≤ (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
              (Work.UBBInputs8.boxPInd
                (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) i
                (Φ : Submission.BoseGases.X n → ℝ) x) ^ 2) →
          -(C * (μ ^ 2 * _root_.BoseGases.a v
                * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                    (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
              + μ * _root_.BoseGases.a v))
            * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
          ≤ Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ) := by sorry

end Work.BoseFixR
