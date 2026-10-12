import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1S.boxMuQP_le_sqrt
import Submission.Work.BoseFixB1S.boxPairManifestSumB1S
import Submission.Work.BoseFixB1S.fibManifestArith
import Submission.Work.BoseFixB1S.mfMuManifestPart
import Submission.Work.BoseFixB1S.mfPairManifestPart
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.fibSum_le_manifest` — the manifest fibre bound

The localised one-body fibre integral of the sliding box,
`fibSum = ∫_{abox n ℓ} Φ² · Σᵢ ∫_{acube ℓ} w_{1,B(u)}(xᵢ,y) dy`
(`Work.BoseFixB1.fibSum`), is dominated by the *manifest* flat term plus an `O(a)`-error
carried by the excited count `n₊ = cnPlusBoxInd ℓ B(u) |B(u)| Φ` and the flat count `S`:

    fibSum ≤ (M₁/|B(u)|)·S + C·(a v)·( √(n₊·(M₁/|B(u)|)·S) + n₊ ) ,

with `M₁ = ∫_{B(u)} fib` (`Work.BoseFixB1S.boxM1`) and `S = Σᵢ∫(PᵢΦ)²`
(`Work.BoseFixB1S.boxFlatCount`).

The proof is the exact square expansion of the slot decomposition `Φ = PᵢΦ + QᵢΦ`, which holds
on the support of the fibre (`fib` vanishes off the sliding box `B(u)`, since its kernel carries
the cutoff `chiSmallB` in both slots):

* `Work.BoseFixB1M.muPart_dlBox` at `μ = -1` gives the exact identity
  `fibSum = Σᵢ boxMuP + 2 Σᵢ boxMuQP + Σᵢ boxMuQ` in the box-projection fibre lines
  (`boxMuP`, `boxMuQP`, `boxMuQ` of `Work.BoseFixB1S.BoxPotDefs`);
* `Work.BoseFixB1.boxPIndFibreMassB1` collapses the `P`-line to `(M₁/|B(u)|)·S`;
* the Cauchy–Schwarz bound `Work.BoseFixB1S.boxMuQP_le_sqrt` on the cross line;
* `Work.BoseFixB1.boxQIndFibreCountB1` bounds the `Q`-line by `Kfib M · n₊ = KfibConst M · a v · n₊`;
* the pure arithmetic `Work.BoseFixB1S.fibManifestArith` converts
  `X + 2√(Y·X) + Y` with `Y ≤ κ·a·n₊` into `X + C·a·(√(n₊·X) + n₊)`.

The constant is `C = max (KfibConst M) (2√(KfibConst M)/√(a v))`, which may depend on `v` and `M`
but not on any box parameter.
-/

namespace Work.BoseFixB1S

open MeasureTheory
open scoped Real BigOperators ENNReal

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

theorem fibSum_le_manifest {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v)
    {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) {M : ℕ} (hM : 1 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {ℓ d μ : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
        (hR16 : R ≤ ℓ * d / 16) (hRχ : R ≤ ℓ * Submission.BoseGases.chiR0)
        (u : EuclideanSpace ℝ (Fin 3)) (hvol : 0 < Work.SmallBoxSliding.boxMass ℓ d u)
        {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ),
        Work.BoseFixB1.fibSum h M ℓ d u Φ
          ≤ (Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
                (Submission.BoseGases.wSmall1Pair h M ℓ d u)
              / Work.SmallBoxSliding.boxMass ℓ d u)
            * (Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                (Submission.BoseGases.dlBox ℓ d u) Φ)
          + C * (_root_.BoseGases.a v)
              * (Real.sqrt ((Work.UBBInputs8.cnPlusBoxInd ℓ (Submission.BoseGases.dlBox ℓ d u)
                    (Work.SmallBoxSliding.boxMass ℓ d u) Φ)
                  * ((Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
                        (Submission.BoseGases.wSmall1Pair h M ℓ d u)
                      / Work.SmallBoxSliding.boxMass ℓ d u)
                    * (Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                        (Submission.BoseGases.dlBox ℓ d u) Φ)))
                + Work.UBBInputs8.cnPlusBoxInd ℓ (Submission.BoseGases.dlBox ℓ d u)
                    (Work.SmallBoxSliding.boxMass ℓ d u) Φ) := by
  classical
  refine ⟨max (Work.BoseFixB1.KfibConst M)
      (2 * Real.sqrt (Work.BoseFixB1.KfibConst M) / Real.sqrt (_root_.BoseGases.a v)),
    le_trans (Work.BoseFixB1.KfibConst_nonneg M) (le_max_left _ _), ?_⟩
  intro ℓ d μ hℓ hd hR16 hRχ u hvol n Φ hΦc
  -- ### abbreviations
  set X : ℝ := (Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
                  (Submission.BoseGases.wSmall1Pair h M ℓ d u)
                / Work.SmallBoxSliding.boxMass ℓ d u)
              * (Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                  (Submission.BoseGases.dlBox ℓ d u) Φ) with hXdef
  set Y : ℝ := ∑ i : Fin n, boxMuQ (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
      (Submission.BoseGases.dlBox ℓ d u) (Submission.BoseGases.wSmall1Pair h M ℓ d u) Φ i with hYdef
  set Z : ℝ := ∑ i : Fin n, boxMuQP (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
      (Submission.BoseGases.dlBox ℓ d u) (Submission.BoseGases.wSmall1Pair h M ℓ d u) Φ i with hZdef
  set Qn : ℝ := Work.UBBInputs8.cnPlusBoxInd ℓ (Submission.BoseGases.dlBox ℓ d u)
      (Work.SmallBoxSliding.boxMass ℓ d u) Φ with hQdef
  -- ### the fibre is pointwise nonnegative
  have hfib0 : ∀ z : EuclideanSpace ℝ (Fin 3),
      0 ≤ Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) z :=
    fun z => boxFibLine_fibre_nonneg hR hv hvrad hv_supp h u z
  -- ### the decomposition of `fibSum` into the three box-projection fibre lines
  have hdecomp : Work.BoseFixB1.fibSum h M ℓ d u Φ
      = (∑ i : Fin n, boxMuP (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
            (Submission.BoseGases.dlBox ℓ d u) (Submission.BoseGases.wSmall1Pair h M ℓ d u) Φ i)
        + 2 * Z + Y := by
    have hmu := Work.BoseFixB1M.muPart_dlBox (v := v) (R0 := R) hv_supp hR hv hvrad hv1 h
      (M := M) hM (ℓ := ℓ) (d := d) (μ := -1) hℓ hd hR16 hRχ u hvol (N := n) hΦc
    rw [hZdef, hYdef]
    simp only [Work.BoseFixB1.fibSum, Submission.BoseGases.w1Fibre,
      Submission.BoseGases.wSmall1Pair, neg_neg, one_mul] at hmu ⊢
    exact hmu
  -- ### the `P`-line is exactly the manifest flat term
  have hP : (∑ i : Fin n, boxMuP (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
        (Submission.BoseGases.dlBox ℓ d u) (Submission.BoseGases.wSmall1Pair h M ℓ d u) Φ i) = X := by
    rw [hXdef]
    simpa only [boxMuP] using
      (Work.BoseFixB1.boxPIndFibreMassB1 (v := v) (R0 := R) hv_supp hR hv hvrad hv1 h
        (M := M) hM hℓ hd hR16 hRχ u hvol (N := n) hΦc)
  -- ### the `Q`-line is bounded by the excited count
  have hQ : Y ≤ Work.BoseFixB1.Kfib (v := v) M * Qn := by
    rw [hYdef, hQdef]
    simpa only [boxMuQ, boxQCount, Work.UBBInputs8.cnPlusBoxInd] using
      (Work.BoseFixB1.boxQIndFibreCountB1 (v := v) (R0 := R) hv_supp hR hv hvrad hv1 h
        (M := M) hM hℓ hd hR16 hRχ u hvol (N := n) hΦc)
  -- ### Cauchy–Schwarz on the cross line
  have hZle : Z ≤ Real.sqrt Y * Real.sqrt X := by
    have h0 : (∑ i : Fin n, boxMuQP (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
          (Submission.BoseGases.dlBox ℓ d u) (Submission.BoseGases.wSmall1Pair h M ℓ d u) Φ i)
        ≤ Real.sqrt (∑ i : Fin n, boxMuQ (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
              (Submission.BoseGases.dlBox ℓ d u) (Submission.BoseGases.wSmall1Pair h M ℓ d u) Φ i)
          * Real.sqrt (∑ i : Fin n, boxMuP (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
              (Submission.BoseGases.dlBox ℓ d u) (Submission.BoseGases.wSmall1Pair h M ℓ d u) Φ i) :=
      boxMuQP_le_sqrt (v := v) (R0 := R) hv_supp hR hv hvrad hv1 h
        (M := M) hM hℓ hd hR16 hRχ u hvol (N := n) hΦc
    rw [← hZdef, ← hYdef, hP] at h0
    exact h0
  -- ### nonnegativity
  have hY0 : 0 ≤ Y := by
    rw [hYdef]
    exact Finset.sum_nonneg (fun i _ => MeasureTheory.integral_nonneg_of_ae
      (Filter.Eventually.of_forall (fun x => mul_nonneg (sq_nonneg _) (hfib0 (x i)))))
  have hX0 : 0 ≤ X := by
    rw [hXdef]
    refine mul_nonneg (div_nonneg ?_ (le_of_lt hvol)) ?_
    · exact MeasureTheory.integral_nonneg_of_ae
        (Filter.Eventually.of_forall (fun z => hfib0 z))
    · exact Finset.sum_nonneg (fun i _ => MeasureTheory.integral_nonneg_of_ae
        (Filter.Eventually.of_forall (fun x => sq_nonneg _)))
  have hQn0 : 0 ≤ Qn := by
    rw [hQdef]
    exact Finset.sum_nonneg (fun i _ => MeasureTheory.integral_nonneg_of_ae
      (Filter.Eventually.of_forall (fun x => sq_nonneg _)))
  -- ### the `μ`-slack arithmetic
  have hYle : Y ≤ Work.BoseFixB1.KfibConst M * _root_.BoseGases.a v * Qn := by
    refine hQ.trans (le_of_eq ?_)
    rw [Work.BoseFixB1.Kfib_eq_KfibConst_mul_a]
  have harith := fibManifestArith (κ := Work.BoseFixB1.KfibConst M)
    (a := _root_.BoseGases.a v) (X := X) (Y := Y) (Q := Qn)
    (Work.BoseFixB1.KfibConst_nonneg M) hav hX0 hQn0 hY0 hYle
  have hstep : X + 2 * Z + Y ≤ X + 2 * Real.sqrt (Y * X) + Y := by
    have hZX : Z ≤ Real.sqrt (Y * X) := by
      rw [Real.sqrt_mul hY0 X]
      exact hZle
    linarith
  rw [hdecomp, hP]
  linarith

end Work.BoseFixB1S
