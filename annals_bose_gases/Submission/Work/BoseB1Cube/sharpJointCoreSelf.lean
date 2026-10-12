import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1S.boxJointCoreB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB1Cube.sharpJointCoreSelf` — the sharp joint core (self-contained copy)

`Work.BoseFixB1S.boxJointIneqSharpB1`: the corpus's `Work.BoseFixB1S.boxJointIneqSlidingB1`
(= FS `lm:appinteractionestimate`'s completion of squares) with the pair-condensate row
`½(M₂/V²)·Pc − ½(M₁/V²)(S²−S)` replaced by the **`M₁`-form** `½(M₁/V²)·Pc − ½(M₁/V²)(S²−S)`, i.e.
with the `pcb`-credit *not spent* on the square (the *pair-condensate surplus* row).

Why a copy is needed: the surplus row is **strictly stronger** than
`boxJointIneqSlidingB1`'s (its left-hand side is smaller), so it does not follow from it.  The
change is nevertheless exactly the substitution `M₂ := M₁` in the two internal calls of the
original proof:

* `boxJointLedgerB1 … (M2 := M1) (hM2 := le_refl M1) …` — legal because that ledger's `M₂` is a
  *free variable* and its `hb_pcb` step (`a·V·((α/2)Var) ≤ ½M₂Pc − ½M₁(S²−S)`) becomes the
  *identity* `a·V·((α/2)Var) = ½M₁·Var` at `M₂ = M₁`;
* the final `jointArithB1 … (M2 := M1) …`, whose `M₂`-row then reads `½(M₁/V²)·Pc − ½(M₁/V²)(S²−S)`.

Everything else is a verbatim transcription, and the chemical potential `μ` enters only through the
`let`-bound weights `gP r = √(r+1) + √(μV)`, `gM`, `Qm`, `Mt`, `Z0`, `Df`, `Z1`; hence the core is
usable at a **slot free of the box parameters**, which is what
`Submission/Work/BoseB1Cube/paySurplusSlotFree.lean` (and then
`Submission/Work/BoseB1Cube/sbWordSlot_ge_payPort.lean`) consumes.

(This module is self-contained on purpose: `Submission/Work/BoseB1Cube/sharpJointCore.lean` is a
*sibling* file of the same mathematical content written by another agent; the two do not clash.)
-/

noncomputable section
set_option maxHeartbeats 8000000
open MeasureTheory Metric Filter
open scoped Real Topology BigOperators ENNReal

namespace Work.BoseFixB1S

local notation "E3" => EuclideanSpace ℝ (Fin 3)

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox Work.SmallBoxSliding Work.BoseBoxFix
  Work.BoseFixB1

theorem boxJointIneqSharpB1 {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    (hav : 0 < _root_.BoseGases.a v) {M : ℕ} (hM : 1 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {ℓ d μ : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hμ : 0 < μ)
        (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
        (u : EuclideanSpace ℝ (Fin 3)) (hvol : 0 < Work.SmallBoxSliding.boxMass ℓ d u)
        (hμv : 1 ≤ μ * Work.SmallBoxSliding.boxMass ℓ d u)
        {N : ℕ} {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
        (hnorm : (∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2) = 1)
        (hsupp : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)),
          Φ x ≠ 0 → ∀ i : Fin N, x i ∈ Submission.BoseGases.dlBox ℓ d u)
        (hM1nn : 0 ≤ Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
            (Submission.BoseGases.wSmall1Pair h M ℓ d u))
        (hM2 : Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
              (Submission.BoseGases.wSmall1Pair h M ℓ d u)
            ≤ Work.BoseFixB1S.boxM2 (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u)
                (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h)))
        (hPcnn : 0 ≤ Work.BoseFixB1S.boxPairCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
            (Submission.BoseGases.dlBox ℓ d u) Φ)
        (hcS2 : Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                  (Submission.BoseGases.dlBox ℓ d u) Φ
                * Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                  (Submission.BoseGases.dlBox ℓ d u) Φ
                - Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                  (Submission.BoseGases.dlBox ℓ d u) Φ
              ≤ Work.BoseFixB1S.boxPairCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                  (Submission.BoseGases.dlBox ℓ d u) Φ),
        Work.BoseFixB1.boxSqPart (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
            (Submission.BoseGases.dlBox ℓ d u) (Submission.BoseGases.wSmallPair M ℓ d u v)
            (Submission.BoseGases.omC (Classical.choose h)) Φ
          + Work.BoseFixB1.boxCrossPart (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
              (Submission.BoseGases.dlBox ℓ d u) (Submission.BoseGases.wSmall1Pair h M ℓ d u) Φ
          + Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
              (Submission.BoseGases.wSmall1Pair h M ℓ d u)
            * ((1 / 4) * (Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                    (Submission.BoseGases.dlBox ℓ d u) Φ / Work.SmallBoxSliding.boxMass ℓ d u - μ) ^ 2
                + (Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                    (Submission.BoseGases.dlBox ℓ d u) Φ / Work.SmallBoxSliding.boxMass ℓ d u + μ)
                  / (2 * Work.SmallBoxSliding.boxMass ℓ d u)
                + 1 / (4 * Work.SmallBoxSliding.boxMass ℓ d u ^ 2))
          + (1 / 2) * (Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
                (Submission.BoseGases.wSmall1Pair h M ℓ d u)
              / (Work.SmallBoxSliding.boxMass ℓ d u) ^ 2)
              * Work.BoseFixB1S.boxPairCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                  (Submission.BoseGases.dlBox ℓ d u) Φ
          - (1 / 2) * (Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
                (Submission.BoseGases.wSmall1Pair h M ℓ d u)
              / (Work.SmallBoxSliding.boxMass ℓ d u) ^ 2)
              * (Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                    (Submission.BoseGases.dlBox ℓ d u) Φ ^ 2
                - Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                    (Submission.BoseGases.dlBox ℓ d u) Φ)
          + C * (_root_.BoseGases.a v)
              * (μ + Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                    (Submission.BoseGases.dlBox ℓ d u) Φ / Work.SmallBoxSliding.boxMass ℓ d u)
              * Work.BoseFixB1S.boxQCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                  (Submission.BoseGases.dlBox ℓ d u) Φ
        ≥ 2 * μ * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
              (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                  (Submission.BoseGases.dlBox ℓ d u) i Φ x)
                * (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                    (Submission.BoseGases.dlBox ℓ d u) i Φ x)
                * (Submission.BoseGases.w1Fibre ℓ
                    (Submission.BoseGases.wSmall1Pair h M ℓ d u) (x i)))
          + μ * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
              (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                  (Submission.BoseGases.dlBox ℓ d u) i Φ x) ^ 2
                * (Submission.BoseGases.w1Fibre ℓ
                    (Submission.BoseGases.wSmall1Pair h M ℓ d u) (x i))) := by
  classical
  -- ## the explicit fibre constant
  let Kc : ℝ := (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
      * ((2 * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
          / Work.SmallBoxSliding.smallConvLower M)
        * (8 * Real.pi * _root_.BoseGases.a v))
  have hKcdef : Kc = (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
      * ((2 * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
          / Work.SmallBoxSliding.smallConvLower M)
        * (8 * Real.pi * _root_.BoseGases.a v)) := rfl
  have hKc0 : 0 ≤ Kc := by
    rw [hKcdef]
    have h1 : 0 ≤ Submission.BoseGases.chiSupAbs := Submission.BoseGases.chiSupAbs_nonneg
    have h2 : 0 ≤ Submission.BoseGases.chiSmallDecay M :=
      Submission.BoseGases.chiSmallDecay_nonneg M
    have h3 : 0 < Work.SmallBoxSliding.smallConvLower M :=
      Work.SmallBoxSliding.smallConvLower_pos M
    have h4 : 0 ≤ _root_.BoseGases.a v := le_of_lt hav
    positivity
  refine ⟨2048 * (Kc / _root_.BoseGases.a v),
    mul_nonneg (by norm_num) (div_nonneg hKc0 (le_of_lt hav)), ?_⟩
  intro ℓ d μ hℓ hd hμ hR hRχ u hvol hμv N Φ hΦc hnorm hsupp hM1nn hM2 hPcnn hcS2
  -- ## the geometric data of the sliding box
  have hVpos : (0 : ℝ) < Work.SmallBoxSliding.boxMass ℓ d u := hvol
  have hAmeas : MeasurableSet (Submission.BoseGases.dlBox ℓ d u) :=
    Work.SmallBoxSliding.measurableSet_dlBox ℓ d u
  have hvolA : Work.SmallBoxSliding.boxMass ℓ d u
      = (MeasureTheory.volume (Submission.BoseGases.dlBox ℓ d u)).toReal := by
    rw [Work.SmallBoxSliding.boxMass_eq_measureReal, MeasureTheory.Measure.real_def]
  have hAc : Submission.BoseGases.dlBox ℓ d u ⊆ Submission.BoseGases.acube ℓ :=
    Work.SmallBoxSliding.dlBox_subset_acube ℓ d u
  have hμVnn : 0 ≤ μ * Work.SmallBoxSliding.boxMass ℓ d u := by linarith [hμv]
  -- ## the fibre: sign, size, measurability, integrability
  have hfibnn : ∀ z : E3,
      0 ≤ Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) z :=
    fun z => boxFibLine_fibre_nonneg hR0 hv hvrad hv_supp h u z
  have hfible : ∀ z : E3,
      Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) z ≤ Kc := by
    intro z
    rw [hKcdef]
    exact boxFibLine_fibre_le hv_supp hR0 hv hvrad h hM hℓ hd hR hRχ u z
  have hfibme : Measurable (fun z : E3 =>
      Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) z) :=
    Work.BoseFixB1.measurable_w1Fibre hv_supp hR0 hv hvrad hv1 h hM hℓ hd u
  have hfibint : MeasureTheory.IntegrableOn
      (fun z : E3 =>
        Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) z)
      (Submission.BoseGases.dlBox ℓ d u) :=
    Work.BoseFixB1S.Gen.integrableOn_w1Fibre_dlBox hv_supp hR0 hv hvrad hv1 h hM hℓ hd hR hRχ u
  have hfibsq := boxFibLine_fibre_sq_le hv_supp hR0 hv hvrad h hM hℓ hd hR hRχ u
  have hfibsqint : MeasureTheory.IntegrableOn
      (fun z : E3 =>
        (Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) z) ^ 2)
      (Submission.BoseGases.dlBox ℓ d u) := hfibsq.1
  have hfibabs : ∀ z ∈ Submission.BoseGases.acube ℓ,
      |Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) z| ≤ Kc :=
    fun z _ => by rw [abs_of_nonneg (hfibnn z)]; exact hfible z
  -- ## the atoms
  let V : ℝ := Work.SmallBoxSliding.boxMass ℓ d u
  let A : Set E3 := Submission.BoseGases.dlBox ℓ d u
  let w1 : E3 → E3 → ℝ := Submission.BoseGases.wSmall1Pair h M ℓ d u
  let fib : E3 → ℝ := Submission.BoseGases.w1Fibre ℓ w1
  let M1 : ℝ := Work.BoseFixB1S.boxM1 ℓ A w1
  let M2 : ℝ := Work.BoseFixB1S.boxM2 V A
      (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h))
  let Sq : ℝ := Work.BoseFixB1.boxSqPart V ℓ A
      (Submission.BoseGases.wSmallPair M ℓ d u v)
      (Submission.BoseGases.omC (Classical.choose h)) Φ
  let L : ℝ := Work.BoseFixB1.boxCrossPart V ℓ A w1 Φ
  let S : ℝ := Work.BoseFixB1S.boxFlatCount V ℓ A Φ
  let Pc : ℝ := Work.BoseFixB1S.boxPairCount V ℓ A Φ
  let nq : ℝ := Work.BoseFixB1S.boxQCount V ℓ A Φ
  let Q : ℝ := ∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
      (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2 * fib (x i)
  let Pm : ℝ := ∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
      (Work.UBBInputs8.boxQInd V A i Φ x) * fib (x i) * (Work.UBBInputs8.boxPInd V A i Φ x)
  let gP : ℝ → ℝ := fun r : ℝ => Real.sqrt (r + 1) + Real.sqrt (μ * V)
  let gM : ℝ → ℝ := fun r : ℝ => Real.sqrt (r + 1) - Real.sqrt (μ * V)
  let Qm : ℝ := ∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
      fib (x i) * (n0FunOp V A gP (Work.UBBInputs8.boxQInd V A i Φ)) x ^ 2
  let Mt : ℝ := ∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
      (n0FunOp V A gM (Work.UBBInputs8.boxPInd V A i Φ)) x ^ 2
  let Z0 : ℝ := ∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
      (n0FunOp V A gP (Work.UBBInputs8.boxQInd V A i Φ)) x * fib (x i)
        * (n0FunOp V A gM (Work.UBBInputs8.boxPInd V A i Φ)) x
  let Df : ℝ := ∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
      ((n0FunOp V A gP (fun y : Submission.BoseGases.X N =>
          fib (y i) * Work.UBBInputs8.boxQInd V A i Φ y)) x
        - fib (x i) * (n0FunOp V A gP (Work.UBBInputs8.boxQInd V A i Φ)) x)
        * (n0FunOp V A gM (Work.UBBInputs8.boxPInd V A i Φ)) x
  let Z1 : ℝ := ∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
      (Work.UBBInputs8.boxQInd V A i Φ x) * fib (x i)
        * (n0FunOp V A (fun r : ℝ => r + 1 - μ * V)
            (Work.UBBInputs8.boxPInd V A i Φ)) x
  let Cf : ℝ := Kc
  let Cosc : ℝ := Real.sqrt (Cf * (M1 / V))
  have hCf0 : 0 ≤ Cf := hKc0
  have hCosc0 : 0 ≤ Cosc := Real.sqrt_nonneg _
  have hCoscsq : Cosc ^ 2 = Cf * (M1 / V) := Real.sq_sqrt (by positivity)
  have hM1eq : M1 = ∫ z in A, fib z := rfl
  -- ## the `Z₁`-split and the two analytic bounds
  have hsplit : Z1 = Z0 + Df :=
    boxZpSplitB1 hℓ hVpos hAmeas hvolA hAc hμVnn hfibme hfibnn (Cf := Kc) hfibabs hΦc
  have hZ0 : -(4 / V) * Qm - (M1 / (4 * V ^ 2)) * Mt ≤ (2 / V) * Z0 :=
    boxSharpPairingAMGMB1 hℓ hVpos hAmeas hvolA hAc hμVnn hfibme hfibnn
      (Cf := Kc) (fun z _ => hfible z) hfibsqint hΦc
  have hfibvarb : (∫ z in A, (fib z - (∫ z in A, fib z) / V) ^ 2) ≤ Cf * (∫ z in A, fib z) :=
    boxFibVarLeCfM1B1 hℓ hVpos hAmeas hvolA hAc hfibme hfibnn (Cf := Cf)
      (fun z _ => hfible z) hfibint
  have hfibvarint : MeasureTheory.IntegrableOn
      (fun z : E3 => (fib z - (∫ z in A, fib z) / V) ^ 2) A :=
    integrableOn_fibSubMeanSqB1 hℓ hVpos hAmeas hvolA hAc hfibint (Cf := Kc) hfibabs
  have hosc : Cosc ^ 2 * V ≥ ∫ z in A, (fib z - (∫ z in A, fib z) / V) ^ 2 := by
    have h1 : Cf * (M1 / V) * V = Cf * (∫ z in A, fib z) := by
      have hVne : V ≠ 0 := ne_of_gt hVpos
      rw [hM1eq]
      field_simp
    rw [hCoscsq, h1]
    linarith [hfibvarb]
  have hDf' : |Df| ≤ 4 * Cosc * Real.sqrt (nq * Mt) :=
    commutatorPairingOscB1 hℓ hVpos hAmeas hvolA hAc hμVnn hΦc hfibme hfibvarint hCosc0 hosc
  have hDf : -(8 * Cosc / V) * Real.sqrt (nq * Mt) ≤ (2 / V) * Df := by
    have hlo := (abs_le.mp hDf').1
    have h2 : (0 : ℝ) ≤ 2 / V := by positivity
    have h3 := mul_le_mul_of_nonneg_left hlo h2
    have h4 : (2 / V) * (-(4 * Cosc * Real.sqrt (nq * Mt)))
        = -(8 * Cosc / V) * Real.sqrt (nq * Mt) := by ring
    linarith [h3, h4]
  have hZ : -(4 / V) * Qm - (M1 / (4 * V ^ 2)) * Mt - (8 * Cosc / V) * Real.sqrt (nq * Mt)
      ≤ (2 / V) * Z1 := by
    rw [hsplit]
    ring_nf at hZ0 hDf ⊢
    linarith [hZ0, hDf]
  -- ## the manifest square
  have hSq : 0 ≤ Sq :=
    Work.BoseFixB1.Clean.boxSqPart_nonneg hv (M := M) u
      (Submission.BoseGases.omC (Classical.choose h)) Φ
  -- ## the split of the cross part along the `μ`-line
  have hcross := Work.BoseFixB1S.boxCrossPartZsplitB1 (v := v) (R0 := R0) hv_supp hR0 hv hvrad
    hv1 h (M := M) hM (ℓ := ℓ) (d := d) (μ := μ) hℓ hd hR hRχ u hvol (Φ := Φ) hΦc
  have hL : L = 2 * μ * Pm + (2 / V) * (Z1 - 2 * Pm) := by linarith [hcross]
  -- ## the five scalar bounds of the ledger
  have hSnn : 0 ≤ S :=
    Finset.sum_nonneg (fun i _ => integral_nonneg (fun x => sq_nonneg _))
  have hnqnn : 0 ≤ nq :=
    Finset.sum_nonneg (fun i _ => integral_nonneg (fun x => sq_nonneg _))
  have hMt0 : 0 ≤ Mt :=
    Finset.sum_nonneg (fun i _ => integral_nonneg (fun x => sq_nonneg _))
  have hQ0 : 0 ≤ Q :=
    Finset.sum_nonneg (fun i _ => integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (hfibnn (x i))))
  have hQ : Q ≤ Cf * nq := by
    have h := boxQMassLeFibreB1 hℓ hVpos hAmeas hvolA hAc hfibme hfibnn hCf0 hfibabs hΦc
    simpa only [Q, Cf, nq, fib, V, A] using h
  have hP : Pm ^ 2 ≤ Q * (M1 / V) * S := by
    have h := boxPMassCsB1 hℓ hVpos hAmeas hvolA hAc hfibme hfibnn hfibint hΦc
    rw [mul_assoc]
    simpa only [Pm, Q, S, M1, boxM1, fib, V, A] using h
  have hQm : Qm ≤ 2 * Cf * (S * nq + (1 + μ * V) * nq) := by
    have h := boxQmassNeutralB1 hℓ hVpos hμVnn hAmeas hvolA hAc hfibme hfibnn
      (Cf := Kc) (fun z _ => hfible z) hΦc hnorm hsupp (by simpa only [sq] using hcS2)
    simpa only [Qm, S, nq, Cf, V, A, fib, gP] using h
  have hMt1 : Mt ≤ (Pc - (S ^ 2 - S)) + (S + 1 - μ * V) ^ 2 := by
    have h := (boxMtMomentBoundsB1 hℓ hVpos hμv hAmeas hvolA hAc hΦc hnorm).1
    simpa only [Mt, S, Pc, V, A, gM, sq] using h
  have hMt2 : Mt ≤ (Pc - (S ^ 2 - S)) + (S - μ * V - 1) ^ 2 + S := by
    have h := (boxMtMomentBoundsB1 hℓ hVpos hμv hAmeas hvolA hAc hΦc hnorm).2
    simpa only [Mt, S, Pc, V, A, gM, sq] using h
  have hMt3 : Mt ≤ 4 * (Pc - (S ^ 2 - S)) + 4 * S ^ 2 + 2 * (μ * V) * S := by
    have h := boxMtCrudeBoundB1 hℓ hVpos hμVnn hAmeas hvolA hAc hΦc hnorm
    simpa only [Mt, S, Pc, V, A, gM, sq] using h
  -- ## the ledger
  have hαeq : M1 = (M1 / (_root_.BoseGases.a v * V)) * (_root_.BoseGases.a v) * V := by
    rw [mul_assoc, div_mul_cancel₀ M1 (by positivity)]
  have hK0 : 0 ≤ Kc / _root_.BoseGases.a v := div_nonneg hKc0 (le_of_lt hav)
  have hCfK : Cf ≤ (Kc / _root_.BoseGases.a v) * _root_.BoseGases.a v := by
    rw [div_mul_cancel₀ _ (ne_of_gt hav)]
  have hled : 0 ≤ -(4 / V) * Qm - (M1 / (4 * V ^ 2)) * Mt
      - (8 * Cosc / V) * Real.sqrt (nq * Mt)
      - (4 / V) * |Pm| + M1 * ((1 / 4) * (S / V - μ) ^ 2 + (S / V + μ) / (2 * V)
          + 1 / (4 * V ^ 2))
      + ((1 / 2) * (M1 / V ^ 2) * Pc - (1 / 2) * (M1 / V ^ 2) * (S ^ 2 - S))
      + (2048 * (Kc / _root_.BoseGases.a v)) * (_root_.BoseGases.a v) * (μ + S / V) * nq
      - μ * Q := by
    have h := boxJointLedgerB1 (a := _root_.BoseGases.a v) (V := V) (μ := μ)
      (S := S) (Pc := Pc) (Var := Pc - (S ^ 2 - S)) (nq := nq) (Q := Q) (P := Pm)
      (Qm := Qm) (Mt := Mt) (Cosc := Cosc) (Cf := Cf) (M1 := M1) (M2 := M1)
      (K := Kc / _root_.BoseGases.a v) (K0 := Kc / _root_.BoseGases.a v)
      (C := 2048 * (Kc / _root_.BoseGases.a v)) (α := M1 / (_root_.BoseGases.a v * V))
      hav hVpos hμ hK0 hK0 (le_refl _) (le_refl _) hμv hCf0 hCfK hM1nn (le_refl M1) hαeq
      (div_nonneg hM1nn (by positivity)) hSnn hPcnn rfl (by simpa only [sq] using hcS2)
      hnqnn hMt0 hQ0 hQ hP hQm hMt1 hMt2 hMt3 hCoscsq.le hCosc0
    exact h
  -- ## the order of the `P`-sum in the goal
  have hPmOrd : (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) i Φ x)
          * (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) i Φ x)
          * (Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) (x i)))
      = Pm := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    ring
  rw [hPmOrd]
  refine jointArithB1 (V := V) (μ := μ) (M1 := M1) (M2 := M1) (S := S) (Pc := Pc) (nq := nq)
    (Q := Q) (Pm := Pm) (Sq := Sq) (L := L)
    (G := ((1 / 4) * (S / V - μ) ^ 2 + (S / V + μ) / (2 * V) + 1 / (4 * V ^ 2)))
    (C := 2048 * (Kc / _root_.BoseGases.a v)) (aa := _root_.BoseGases.a v)
    (Zpp := Z1) (Qm := Qm) (Mt := Mt) (Cosc := Cosc) hVpos hL hSq hZ hled


end Work.BoseFixB1S
