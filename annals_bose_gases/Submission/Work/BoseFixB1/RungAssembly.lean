import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseFixB1.RungPieces
import Submission.Work.BoseFixB1S.boxPQ_abs_bounds
import Submission.Work.BoseFixB1S.boxPairManifestSumB1S
import Submission.Work.BoseFixB1S.boxQSum_sub_boxA2_blockSum
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1.RungAssembly` — the (T′)-interface of the rung-4 target

The target `Work.BoseFixB1.boxA0A2Rung` is equivalent to the nonnegativity of its **slack**

    rungBracket C = boxQ1 + (boxQ2 − boxA2) + boxQ3 + boxQ4 + pcb + M₁·rungG + C·a(v)·rungRate·n₊

(`_rungAsm.target_of_bracket`, PROVED: the target ⟺ `0 ≤ rungBracket C`).  This module proves the
**machine-verified second form** of that slack,

    rungBracket C = rungPair − boxA2 − rungSlack + M₁·rungG + C·a(v)·rungRate·n₊
                      − 2μ·rungP − μ·rungQ ,                                                (S)

from the corpus's PROVED identities `boxQSum_sub_boxA2_blockSum` (R1) and
`boxPairManifestSumB1S` (`Sq + L = rungPair − boxA2 − ½(M₂/V²)Pc`) plus
`pcb = ½(M₂/V²)Pc − rungSlack`.  With (S) the (T′)-core

    (α) 2μ·rungP + μ·rungQ + rungSlack ≤ rungPair + M₁·rungG + C·a(v)·rungRate·n₊
    (β) boxA2 ≤ C'·a(v)·rungRate·n₊

implies the target (`target_of_bracket` with `C+C'`).  No new analysis: (S) is a linarith
consequence of proved corpus lemmas.
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators ENNReal

namespace Work.BoseFixB1

open _root_.BoseGases Submission.BoseGases

set_option autoImplicit false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **THE INTERFACE.**  At the localised kernels of the rung-4 target, the bracket of
`_rungAsm.rungBracket` equals the (T′)-core combination of `RungPieces`. -/
theorem rungBracket_eq_pairEnergyCore {v : E3 → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (h : Work.UBB.ScatSol v) {M : ℕ} (hM : 1 ≤ M) {ℓ d μ : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
    (u : E3) (hvol : 0 < Work.SmallBoxSliding.boxMass ℓ d u)
    {N : ℕ} {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) (C : ℝ) :
    Work.BoseFixB1S.boxQ1 (Work.SmallBoxSliding.boxMass ℓ d u) ℓ μ
        (Submission.BoseGases.dlBox ℓ d u)
        (Submission.BoseGases.wSmall1Pair h M ℓ d u)
        (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h)) Φ
      + (Work.BoseFixB1S.boxQ2 (Work.SmallBoxSliding.boxMass ℓ d u) ℓ μ
          (Submission.BoseGases.dlBox ℓ d u)
          (Submission.BoseGases.wSmall1Pair h M ℓ d u)
          (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h)) Φ
        - boxA2 ℓ (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.dlBox ℓ d u)
            (Submission.BoseGases.wSmall1Pair h M ℓ d u) Φ)
      + Work.BoseFixB1S.boxQ3 (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
          (Submission.BoseGases.dlBox ℓ d u)
          (Submission.BoseGases.wSmall1Pair h M ℓ d u) Φ
      + Work.BoseFixB1S.boxQ4 (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
          (Submission.BoseGases.dlBox ℓ d u)
          (Submission.BoseGases.wSmallPair M ℓ d u v)
          (Submission.BoseGases.omC (Classical.choose h)) Φ
      + ((1 / 2) * (Work.BoseFixB1S.boxM2 (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u)
              (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h))
            / (Work.SmallBoxSliding.boxMass ℓ d u) ^ 2)
          * Work.BoseFixB1S.boxPairCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
              (Submission.BoseGases.dlBox ℓ d u) Φ
        - Work.BoseFixB1.rungSlack (Work.SmallBoxSliding.boxMass ℓ d u)
            (Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
              (Submission.BoseGases.wSmall1Pair h M ℓ d u))
            (Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
              (Submission.BoseGases.dlBox ℓ d u) Φ))
      + Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
          (Submission.BoseGases.wSmall1Pair h M ℓ d u)
        * Work.BoseFixB1.rungG (Work.SmallBoxSliding.boxMass ℓ d u) μ
            (Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
              (Submission.BoseGases.dlBox ℓ d u) Φ)
      + C * (_root_.BoseGases.a v)
          * Work.BoseFixB1.rungRate (Work.SmallBoxSliding.boxMass ℓ d u) μ
              (Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                (Submission.BoseGases.dlBox ℓ d u) Φ)
          * Work.BoseFixB1S.boxQCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
              (Submission.BoseGases.dlBox ℓ d u) Φ
      = (1 / 2) * Work.BoseFixB1.rungPair ℓ (Submission.BoseGases.dlBox ℓ d u)
            (Submission.BoseGases.wSmallPair M ℓ d u v) Φ
          - boxA2 ℓ (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.dlBox ℓ d u)
              (Submission.BoseGases.wSmall1Pair h M ℓ d u) Φ
          - Work.BoseFixB1.rungSlack (Work.SmallBoxSliding.boxMass ℓ d u)
              (Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
                (Submission.BoseGases.wSmall1Pair h M ℓ d u))
              (Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                (Submission.BoseGases.dlBox ℓ d u) Φ)
          + Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
              (Submission.BoseGases.wSmall1Pair h M ℓ d u)
            * Work.BoseFixB1.rungG (Work.SmallBoxSliding.boxMass ℓ d u) μ
                (Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                  (Submission.BoseGases.dlBox ℓ d u) Φ)
          + C * (_root_.BoseGases.a v)
              * Work.BoseFixB1.rungRate (Work.SmallBoxSliding.boxMass ℓ d u) μ
                  (Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                    (Submission.BoseGases.dlBox ℓ d u) Φ)
              * Work.BoseFixB1S.boxQCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                  (Submission.BoseGases.dlBox ℓ d u) Φ
          - 2 * μ * Work.BoseFixB1.rungP (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
              (Submission.BoseGases.dlBox ℓ d u)
              (Submission.BoseGases.wSmall1Pair h M ℓ d u) Φ
          - μ * Work.BoseFixB1.rungQ (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
              (Submission.BoseGases.dlBox ℓ d u)
              (Submission.BoseGases.wSmall1Pair h M ℓ d u) Φ := by
  classical
  set V : ℝ := Work.SmallBoxSliding.boxMass ℓ d u with hVdef
  set A : Set E3 := Submission.BoseGases.dlBox ℓ d u with hAdef
  set w : E3 → E3 → ℝ := Submission.BoseGases.wSmallPair M ℓ d u v with hwdef
  set w₁ : E3 → E3 → ℝ := Submission.BoseGases.wSmall1Pair h M ℓ d u with hw₁def
  set w₂ : E3 → E3 → ℝ := Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h)
    with hw₂def
  set wom : E3 → E3 → ℝ := Submission.BoseGases.omC (Classical.choose h) with hwomdef
  have hVpos : 0 < V := hvol
  have hA : MeasurableSet A := Work.SmallBoxSliding.measurableSet_dlBox ℓ d u
  have hvolA : V = (MeasureTheory.volume A).toReal := by
    rw [hVdef, hAdef, Work.SmallBoxSliding.boxMass_eq_measureReal, MeasureTheory.Measure.real_def]
  have hAc : A ⊆ Submission.BoseGases.acube ℓ := Work.SmallBoxSliding.dlBox_subset_acube ℓ d u
  -- kernel identities
  have hw1 : ∀ x y : E3, w₁ x y = w x y * (1 - wom x y) := by
    intro x y
    rw [hw₁def, hwdef, hwomdef, Work.BoseFixB1.wSmall1Pair_eq_mul h u x y]
    simp only [Submission.BoseGases.omC]
  have hw2 : ∀ x y : E3, w₂ x y = w x y * (1 - wom x y ^ 2) := by
    intro x y
    rw [hw₂def, hwdef, hwomdef, Work.BoseFixB1.wSmallPair_g2_eq_mul h u x y,
      Work.BoseFixB1.wSmall1Pair_eq_mul h u x y]
    simp only [Submission.BoseGases.omC]
    ring
  have hwsym : ∀ x y : E3, w x y = w y x := by
    intro x y
    rw [hwdef]
    exact Submission.BoseGases.wSmallPair_symm hM u (radial_even hvrad) x y
  have homsym : ∀ x y : E3, wom x y = wom y x := by
    intro x y
    have hw0 : ∀ z : E3, Classical.choose h (-z) = Classical.choose h z :=
      radial_even (Classical.choose_spec h).1
    simp only [hwomdef, Submission.BoseGases.omC]
    rw [show y - x = -(x - y) from by abel, hw0]
  -- ## (R1): the sum-level reduction, plus the square/cross split
  obtain ⟨hint0, hint1, hint2, hint3, hint4, hint5⟩ :=
    Work.BoseFixB1.Clean.boxFragmentsIntegrable (v := v) (R0 := R0) hv_supp hR0 hv hvrad hv1 h
      hM hℓ hd hR hRχ u (Φ := Φ) hΦc
  obtain ⟨hBlk, hSqInt, hCrInt⟩ :=
    Work.BoseFixB1.boxPairBlockIntegrable (v := v) (R0 := R0) hv_supp hR0 hv hvrad hv1 h
      hM hℓ hd hR hRχ u (Φ := Φ) hΦc
  have hred := Work.BoseFixB1S.boxQSum_sub_boxA2_blockSum (N := N) (ℓ := ℓ) (volA := V)
    (μ := μ) (A := A) hℓ hVpos hA hvolA hAc (w := w) (w₁ := w₁) (w₂ := w₂) (om := wom)
    hw1 hw2 hwsym homsym hΦc hint0 hint1 hint2 hint3 hint4 hint5
  have hsplit := Work.BoseFixB1.boxSqPart_add_boxCrossPart_eq_blockSum (N := N) (ℓ := ℓ)
    (volA := V) (A := A) (w := w) (w₁ := w₁) (om := wom) (Φ := Φ)
    hSqInt hCrInt hBlk hw1
  have hid := Work.BoseFixB1S.boxPairManifestSumB1S (v := v) (R0 := R0) hv_supp hR0 hv hvrad
    hv1 h hM hℓ hd hR hRχ u hvol (Φ := Φ) hΦc
  have hsum : Work.BoseFixB1S.boxQ1 V ℓ μ A w₁ w₂ Φ
      + (Work.BoseFixB1S.boxQ2 V ℓ μ A w₁ w₂ Φ - boxA2 ℓ V A w₁ Φ)
      + Work.BoseFixB1S.boxQ3 V ℓ A w₁ Φ + Work.BoseFixB1S.boxQ4 V ℓ A w wom Φ
      + 2 * μ * Work.BoseFixB1.rungP V ℓ A w₁ Φ + μ * Work.BoseFixB1.rungQ V ℓ A w₁ Φ
      = Work.BoseFixB1.boxSqPart V ℓ A w wom Φ + Work.BoseFixB1.boxCrossPart V ℓ A w₁ Φ := by
    rw [Work.BoseFixB1S.boxQSum, Work.BoseFixB1S.boxQ0] at hred
    unfold Work.BoseFixB1.rungP Work.BoseFixB1.rungQ
    linarith [hred, hsplit]
  -- ## the pair identity, in the form needed
  have hpt : ∀ p : Fin N × Fin N, ∀ x : Submission.BoseGases.X N,
      ((A.indicator (fun _ => (1 : ℝ)) (x p.1)
          * (A.indicator (fun _ => (1 : ℝ)) (x p.2) * Φ x)) ^ 2)
        * (Submission.BoseGases.wSmallPair M ℓ d u v) (x p.1) (x p.2)
      = (A.indicator (fun _ => (1 : ℝ)) (x p.1)
          * A.indicator (fun _ => (1 : ℝ)) (x p.2)) * (Φ x) ^ 2
        * (Submission.BoseGases.wSmallPair M ℓ d u v) (x p.1) (x p.2) := by
    intro p x
    by_cases h1 : x p.1 ∈ A <;> by_cases h2 : x p.2 ∈ A <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, h1, h2] <;> ring
  have hsum_eq : (∑ p ∈ Submission.BoseGases.pairSet N,
        ∫ x in Submission.BoseGases.abox N ℓ,
          ((A.indicator (fun _ => (1 : ℝ)) (x p.1)
              * (A.indicator (fun _ => (1 : ℝ)) (x p.2) * Φ x)) ^ 2)
            * (Submission.BoseGases.wSmallPair M ℓ d u v) (x p.1) (x p.2))
      = (∑ p ∈ Submission.BoseGases.pairSet N,
        ∫ x in Submission.BoseGases.abox N ℓ,
          (A.indicator (fun _ => (1 : ℝ)) (x p.1)
              * A.indicator (fun _ => (1 : ℝ)) (x p.2)) * (Φ x) ^ 2
            * (Submission.BoseGases.wSmallPair M ℓ d u v) (x p.1) (x p.2)) := by
    refine Finset.sum_congr rfl fun p _ => ?_
    refine MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.abox_measurable N ℓ) ?_
    intro x _
    exact hpt p x
  have hpairW : (1 / 2) * (∑ p ∈ Submission.BoseGases.pairSet N,
        ∫ x in Submission.BoseGases.abox N ℓ,
          ((A.indicator (fun _ => (1 : ℝ)) (x p.1)
              * (A.indicator (fun _ => (1 : ℝ)) (x p.2) * Φ x)) ^ 2)
            * (Submission.BoseGases.wSmallPair M ℓ d u v) (x p.1) (x p.2))
      = (1 / 2) * Work.BoseFixB1.rungPair ℓ A (Submission.BoseGases.wSmallPair M ℓ d u v) Φ := by
    rw [hsum_eq, Work.BoseFixB1.rungPair]
  have hpairA2 : (∑ p ∈ Submission.BoseGases.pairSet N,
        ∫ x in Submission.BoseGases.abox N ℓ,
          (Work.UBBInputs8.boxPInd V A p.1 (Work.UBBInputs8.boxPInd V A p.2 Φ) x)
            * (Work.UBBInputs8.boxQInd V A p.2 (Work.UBBInputs8.boxQInd V A p.1 Φ) x)
            * w₁ (x p.1) (x p.2))
      = boxA2 ℓ V A w₁ Φ := by
    rw [boxA2]
  -- ## assemble
  have hpair : Work.BoseFixB1.boxSqPart V ℓ A w wom Φ + Work.BoseFixB1.boxCrossPart V ℓ A w₁ Φ
      = (1 / 2) * Work.BoseFixB1.rungPair ℓ A w Φ - boxA2 ℓ V A w₁ Φ
          - (1 / 2) * (Work.BoseFixB1S.boxM2 V A w₂ / V ^ 2)
              * Work.BoseFixB1S.boxPairCount V ℓ A Φ := by
    rw [hid]
    linarith [hpairW, hpairA2]
  unfold Work.BoseFixB1.rungSlack Work.BoseFixB1.rungG Work.BoseFixB1.rungRate
  linarith [hsum, hpair]

/-- **`½·rungPair` in terms of the square, the cross term, the pairing and the pair-condensate
count** — the ID form used by the assembly.  Consequence of `boxPairManifestSumB1S` (the two
`∑_p`-rewrites identifying the corpus's `½Σ_p∫σ_p²w` with `½·rungPair` and its pairing sum with
`boxA2`). -/
theorem halfRungPair_eq_sq_add_cross_add_A2 {v : E3 → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (h : Work.UBB.ScatSol v) {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
    (u : E3) (hvol : 0 < Work.SmallBoxSliding.boxMass ℓ d u)
    {N : ℕ} {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) :
    (1 / 2) * Work.BoseFixB1.rungPair ℓ (Submission.BoseGases.dlBox ℓ d u)
        (Submission.BoseGases.wSmallPair M ℓ d u v) Φ
      = Work.BoseFixB1.boxSqPart (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
            (Submission.BoseGases.dlBox ℓ d u) (Submission.BoseGases.wSmallPair M ℓ d u v)
            (Submission.BoseGases.omC (Classical.choose h)) Φ
        + Work.BoseFixB1.boxCrossPart (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
            (Submission.BoseGases.dlBox ℓ d u)
            (Submission.BoseGases.wSmall1Pair h M ℓ d u) Φ
        + boxA2 ℓ (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.dlBox ℓ d u)
            (Submission.BoseGases.wSmall1Pair h M ℓ d u) Φ
        + (1 / 2) * (Work.BoseFixB1S.boxM2 (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u)
              (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h))
            / (Work.SmallBoxSliding.boxMass ℓ d u) ^ 2)
            * Work.BoseFixB1S.boxPairCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                (Submission.BoseGases.dlBox ℓ d u) Φ := by
  classical
  set V : ℝ := Work.SmallBoxSliding.boxMass ℓ d u with hVdef
  set A : Set E3 := Submission.BoseGases.dlBox ℓ d u with hAdef
  have hid := Work.BoseFixB1S.boxPairManifestSumB1S (v := v) (R0 := R0) hv_supp hR0 hv hvrad
    hv1 h hM hℓ hd hR hRχ u hvol (Φ := Φ) hΦc
  -- the two sum-level identifications
  have hpt : ∀ p : Fin N × Fin N, ∀ x : Submission.BoseGases.X N,
      ((A.indicator (fun _ => (1 : ℝ)) (x p.1)
          * (A.indicator (fun _ => (1 : ℝ)) (x p.2) * Φ x)) ^ 2)
        * (Submission.BoseGases.wSmallPair M ℓ d u v) (x p.1) (x p.2)
      = (A.indicator (fun _ => (1 : ℝ)) (x p.1)
          * A.indicator (fun _ => (1 : ℝ)) (x p.2)) * (Φ x) ^ 2
        * (Submission.BoseGases.wSmallPair M ℓ d u v) (x p.1) (x p.2) := by
    intro p x
    by_cases h1 : x p.1 ∈ A <;> by_cases h2 : x p.2 ∈ A <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, h1, h2] <;> ring
  have hsum_eq : (∑ p ∈ Submission.BoseGases.pairSet N,
        ∫ x in Submission.BoseGases.abox N ℓ,
          ((A.indicator (fun _ => (1 : ℝ)) (x p.1)
              * (A.indicator (fun _ => (1 : ℝ)) (x p.2) * Φ x)) ^ 2)
            * (Submission.BoseGases.wSmallPair M ℓ d u v) (x p.1) (x p.2))
      = (∑ p ∈ Submission.BoseGases.pairSet N,
        ∫ x in Submission.BoseGases.abox N ℓ,
          (A.indicator (fun _ => (1 : ℝ)) (x p.1)
              * A.indicator (fun _ => (1 : ℝ)) (x p.2)) * (Φ x) ^ 2
            * (Submission.BoseGases.wSmallPair M ℓ d u v) (x p.1) (x p.2)) := by
    refine Finset.sum_congr rfl fun p _ => ?_
    refine MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.abox_measurable N ℓ) ?_
    intro x _
    exact hpt p x
  have hpairW : (1 / 2) * (∑ p ∈ Submission.BoseGases.pairSet N,
        ∫ x in Submission.BoseGases.abox N ℓ,
          ((A.indicator (fun _ => (1 : ℝ)) (x p.1)
              * (A.indicator (fun _ => (1 : ℝ)) (x p.2) * Φ x)) ^ 2)
            * (Submission.BoseGases.wSmallPair M ℓ d u v) (x p.1) (x p.2))
      = (1 / 2) * Work.BoseFixB1.rungPair ℓ A (Submission.BoseGases.wSmallPair M ℓ d u v) Φ := by
    rw [hsum_eq, Work.BoseFixB1.rungPair]
  have hpairA2 : (∑ p ∈ Submission.BoseGases.pairSet N,
        ∫ x in Submission.BoseGases.abox N ℓ,
          (Work.UBBInputs8.boxPInd V A p.1 (Work.UBBInputs8.boxPInd V A p.2 Φ) x)
            * (Work.UBBInputs8.boxQInd V A p.2 (Work.UBBInputs8.boxQInd V A p.1 Φ) x)
            * (Submission.BoseGases.wSmall1Pair h M ℓ d u) (x p.1) (x p.2))
      = boxA2 ℓ V A (Submission.BoseGases.wSmall1Pair h M ℓ d u) Φ := by
    rw [boxA2]
  rw [hid]
  linarith [hpairW, hpairA2]

/-! ## The assembly route (statement only; proved once the pieces land)

From the two halves of the μ-line chapter **Qi** and **Qii** (delegated as
`Work.BoseFixB1.boxMuLine_le_sq_add_cross` and `Work.BoseFixB1.boxSlack_le_sq_add_cross`),

    (Qi)  2μ·rungP + μ·rungQ ≤ boxSqPart + boxCrossPart + M₁·rungG + C₁·a(v)·rungRate·n₊
    (Qii) rungSlack          ≤ boxSqPart + boxCrossPart + M₁·rungG + C₂·a(v)·rungRate·n₊

one gets `2μ·rungP + μ·rungQ + rungSlack ≤ Sq + L + M₁·rungG + (C₁+C₂)·credit`; combined with
`pcb + rungSlack = ½(M₂/V²)·Pc ≥ 0` (definitional, from `hPcnn` and `M₂ ≥ 0`) and the proved
interface `rungBracket_eq_pairEnergyCore`, this is `0 ≤ rungBracket (C₁+C₂)`, hence the target.
The `(H-A)`/`(H-B)` split tried earlier is **insufficient** (its assembly needs
`−rungSlack ≤ pcb`, i.e. a *lower* bound on `rungSlack`, which `(H-B)` does not give), which is why
the route above is the one recorded.  The linarith assembly is short and will be written here as
soon as `Qi`,`Qii` are available. -/

/-- **`pcb ≥ 0`** (the pair-condensate block is a payer): with `0 ≤ M₁ ≤ M₂`, `0 ≤ Pc` and
`hcS2 : S²−S ≤ Pc`, `rungPCBlock = ½(M₂/V²)Pc − ½(M₁/V²)(S²−S) ≥ 0`.  This is the `pcb`-half of the
target's slack (cf. the corpus's `half_pc_slack_nonneg`). -/
theorem rungPCBlock_nonneg {V M2 M1 S Pc : ℝ} (hV : 0 < V) (hM1 : 0 ≤ M1) (hM2 : M1 ≤ M2)
    (hPc : 0 ≤ Pc) (hcS2 : S * S - S ≤ Pc) :
    0 ≤ Work.BoseFixB1.rungPCBlock V M2 M1 S Pc := by
  unfold Work.BoseFixB1.rungPCBlock Work.BoseFixB1.rungSlack
  have hV2 : 0 < V ^ 2 := by positivity
  have h1 : (1 / 2) * (M1 / V ^ 2) * (S * S - S) ≤ (1 / 2) * (M1 / V ^ 2) * Pc :=
    mul_le_mul_of_nonneg_left hcS2 (by positivity)
  have h2 : (1 / 2) * (M1 / V ^ 2) * Pc ≤ (1 / 2) * (M2 / V ^ 2) * Pc := by
    have : M1 / V ^ 2 ≤ M2 / V ^ 2 := div_le_div_of_nonneg_right hM2 hV2.le
    exact mul_le_mul_of_nonneg_right (by linarith) hPc
  linarith

/-- **THE ASSEMBLY (the μ-line route).**  `Qi` — the μ-line bounded by the manifest square, the
cross term, the `A₀`-defect and the credit — together with `pcb ≥ 0` gives the nonnegativity of the
bracket, hence the target (`target_of_bracket`).

Why `Qi` suffices: by `rungBracket_eq_pairEnergyCore` and `halfRungPair_eq_sq_add_cross_add_A2`,
the bracket equals `Sq + L + pcb + M₁·rungG + C·credit − (2μ·rungP + μ·rungQ)`, and `pcb ≥ 0`. -/
theorem rungBracket_nonneg_of_muLine {v : E3 → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (h : Work.UBB.ScatSol v) {M : ℕ} (hM : 1 ≤ M) {ℓ d μ : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
    (u : E3) (hvol : 0 < Work.SmallBoxSliding.boxMass ℓ d u)
    {N : ℕ} {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) {C₁ : ℝ}
    (hM1nn : 0 ≤ Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
        (Submission.BoseGases.wSmall1Pair h M ℓ d u))
    (hPc : 0 ≤ Work.BoseFixB1S.boxPairCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
        (Submission.BoseGases.dlBox ℓ d u) Φ)
    (hcS2 : Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
              (Submission.BoseGases.dlBox ℓ d u) Φ
            * Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
              (Submission.BoseGases.dlBox ℓ d u) Φ
            - Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
              (Submission.BoseGases.dlBox ℓ d u) Φ
          ≤ Work.BoseFixB1S.boxPairCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
              (Submission.BoseGases.dlBox ℓ d u) Φ)
    (hM2 : Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
              (Submission.BoseGases.wSmall1Pair h M ℓ d u)
            ≤ Work.BoseFixB1S.boxM2 (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u)
                (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h)))
    (hQi : 2 * μ * Work.BoseFixB1.rungP (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
              (Submission.BoseGases.dlBox ℓ d u)
              (Submission.BoseGases.wSmall1Pair h M ℓ d u) Φ
          + μ * Work.BoseFixB1.rungQ (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
              (Submission.BoseGases.dlBox ℓ d u)
              (Submission.BoseGases.wSmall1Pair h M ℓ d u) Φ
        ≤ Work.BoseFixB1.boxSqPart (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
              (Submission.BoseGases.dlBox ℓ d u) (Submission.BoseGases.wSmallPair M ℓ d u v)
              (Submission.BoseGases.omC (Classical.choose h)) Φ
          + Work.BoseFixB1.boxCrossPart (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
              (Submission.BoseGases.dlBox ℓ d u)
              (Submission.BoseGases.wSmall1Pair h M ℓ d u) Φ
          + Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
              (Submission.BoseGases.wSmall1Pair h M ℓ d u)
            * Work.BoseFixB1.rungG (Work.SmallBoxSliding.boxMass ℓ d u) μ
                (Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                  (Submission.BoseGases.dlBox ℓ d u) Φ)
          + C₁ * (_root_.BoseGases.a v)
              * Work.BoseFixB1.rungRate (Work.SmallBoxSliding.boxMass ℓ d u) μ
                  (Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                    (Submission.BoseGases.dlBox ℓ d u) Φ)
              * Work.BoseFixB1S.boxQCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                  (Submission.BoseGases.dlBox ℓ d u) Φ) :
    0 ≤ Work.BoseFixB1S.boxQ1 (Work.SmallBoxSliding.boxMass ℓ d u) ℓ μ
          (Submission.BoseGases.dlBox ℓ d u)
          (Submission.BoseGases.wSmall1Pair h M ℓ d u)
          (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h)) Φ
        + (Work.BoseFixB1S.boxQ2 (Work.SmallBoxSliding.boxMass ℓ d u) ℓ μ
            (Submission.BoseGases.dlBox ℓ d u)
            (Submission.BoseGases.wSmall1Pair h M ℓ d u)
            (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h)) Φ
          - boxA2 ℓ (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.dlBox ℓ d u)
              (Submission.BoseGases.wSmall1Pair h M ℓ d u) Φ)
        + Work.BoseFixB1S.boxQ3 (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
            (Submission.BoseGases.dlBox ℓ d u)
            (Submission.BoseGases.wSmall1Pair h M ℓ d u) Φ
        + Work.BoseFixB1S.boxQ4 (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
            (Submission.BoseGases.dlBox ℓ d u)
            (Submission.BoseGases.wSmallPair M ℓ d u v)
            (Submission.BoseGases.omC (Classical.choose h)) Φ
        + Work.BoseFixB1.rungPCBlock (Work.SmallBoxSliding.boxMass ℓ d u)
            (Work.BoseFixB1S.boxM2 (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u)
              (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h)))
            (Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
              (Submission.BoseGases.wSmall1Pair h M ℓ d u))
            (Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
              (Submission.BoseGases.dlBox ℓ d u) Φ)
            (Work.BoseFixB1S.boxPairCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
              (Submission.BoseGases.dlBox ℓ d u) Φ)
        + Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
            (Submission.BoseGases.wSmall1Pair h M ℓ d u)
          * Work.BoseFixB1.rungG (Work.SmallBoxSliding.boxMass ℓ d u) μ
              (Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                (Submission.BoseGases.dlBox ℓ d u) Φ)
        + C₁ * (_root_.BoseGases.a v)
            * Work.BoseFixB1.rungRate (Work.SmallBoxSliding.boxMass ℓ d u) μ
                (Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                  (Submission.BoseGases.dlBox ℓ d u) Φ)
            * Work.BoseFixB1S.boxQCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                (Submission.BoseGases.dlBox ℓ d u) Φ := by
  classical
  set V : ℝ := Work.SmallBoxSliding.boxMass ℓ d u with hVdef
  set A : Set E3 := Submission.BoseGases.dlBox ℓ d u with hAdef
  set w : E3 → E3 → ℝ := Submission.BoseGases.wSmallPair M ℓ d u v with hwdef
  set w₁ : E3 → E3 → ℝ := Submission.BoseGases.wSmall1Pair h M ℓ d u with hw₁def
  set w₂ : E3 → E3 → ℝ := Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h)
    with hw₂def
  set wom : E3 → E3 → ℝ := Submission.BoseGases.omC (Classical.choose h) with hwomdef
  have hpcb : 0 ≤ Work.BoseFixB1.rungPCBlock V
      (Work.BoseFixB1S.boxM2 V A w₂)
      (Work.BoseFixB1S.boxM1 ℓ A w₁) (Work.BoseFixB1S.boxFlatCount V ℓ A Φ)
      (Work.BoseFixB1S.boxPairCount V ℓ A Φ) := by
    exact rungPCBlock_nonneg hvol hM1nn hM2 hPc hcS2
  have hcore := rungBracket_eq_pairEnergyCore (v := v) (R0 := R0) hv_supp hR0 hv hvrad hv1 h hM
    (ℓ := ℓ) (d := d) (μ := μ) hℓ hd hR hRχ u hvol (Φ := Φ) hΦc C₁
  have hid2 := halfRungPair_eq_sq_add_cross_add_A2 (v := v) (R0 := R0) hv_supp hR0 hv hvrad hv1
    h hM hℓ hd hR hRχ u hvol (Φ := Φ) hΦc
  simp only [Work.BoseFixB1.rungPCBlock, Work.BoseFixB1.rungSlack, Work.BoseFixB1.rungG,
    Work.BoseFixB1.rungPair, Work.BoseFixB1.rungP, Work.BoseFixB1.rungQ, Work.BoseFixB1.rungRate]
    at *
  linarith [hQi, hcore, hid2, hpcb]

/-- **The `μ·rungQ` half of `Qi`** — the `Q`-side μ-line is paid by the credit *alone*, with no
help from the square or the cross term: `μ·Q ≤ C·a(v)·(μ + S/V)·n₊`.  Immediate from the second
conjunct of the corpus's PROVED `Work.BoseFixB1S.boxPQ_abs_bounds` (`rungQ ≤ C·a(v)·n₊`) and
`0 ≤ S`, `0 ≤ n₊`.

Together with the delegated `boxMuLineP_le_sq_add_cross` (the `2μ·rungP` half, which *does* need
`Sq + L`) this gives `Qi` with `C₁ = C_P + C_Q`, hence — via `rungBracket_nonneg_of_muLine` —
the target. -/
theorem muQ_le_credit {v : E3 → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (h : Work.UBB.ScatSol v) {M : ℕ} (hM : 1 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {ℓ d μ : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hμ : 0 < μ)
        (u : E3) (hμv : 1 ≤ μ * Work.SmallBoxSliding.boxMass ℓ d u)
        (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
        (hvol : 0 < Work.SmallBoxSliding.boxMass ℓ d u)
        {N : ℕ} {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ),
        μ * Work.BoseFixB1.rungQ (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
              (Submission.BoseGases.dlBox ℓ d u)
              (Submission.BoseGases.wSmall1Pair h M ℓ d u) Φ
          ≤ C * (_root_.BoseGases.a v)
              * Work.BoseFixB1.rungRate (Work.SmallBoxSliding.boxMass ℓ d u) μ
                  (Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                    (Submission.BoseGases.dlBox ℓ d u) Φ)
              * Work.BoseFixB1S.boxQCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                  (Submission.BoseGases.dlBox ℓ d u) Φ := by
  classical
  obtain ⟨C₀, hC₀, hbnd⟩ := Work.BoseFixB1S.boxPQ_abs_bounds (v := v) (R0 := R0) hv_supp hR0 hv
    hvrad hv1 h hM
  refine ⟨C₀, hC₀, ?_⟩
  intro ℓ d μ hℓ hd hμ u hμv hR hRχ hvol N Φ hΦc
  have hQ := (hbnd (ℓ := ℓ) (d := d) (μ := μ) hℓ hd hR hRχ u hvol (Φ := Φ) hΦc).2
  have ha : 0 ≤ _root_.BoseGases.a v :=
    (Submission.BoseGases.av_bounds_weak hR0 hv hvrad hv_supp h).1
  have hS : 0 ≤ Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
      (Submission.BoseGases.dlBox ℓ d u) Φ := by
    unfold Work.BoseFixB1S.boxFlatCount
    exact Finset.sum_nonneg fun i _ =>
      MeasureTheory.integral_nonneg fun x => by positivity
  have hV : 0 < Work.SmallBoxSliding.boxMass ℓ d u := hvol
  have hnq : 0 ≤ Work.BoseFixB1S.boxQCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
      (Submission.BoseGases.dlBox ℓ d u) Φ :=
    Work.BoseFixB1S.boxQCount_nonneg _ _ _ _
  have hrate : μ ≤ μ + Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
      (Submission.BoseGases.dlBox ℓ d u) Φ / Work.SmallBoxSliding.boxMass ℓ d u := by
    have : 0 ≤ Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
        (Submission.BoseGases.dlBox ℓ d u) Φ / Work.SmallBoxSliding.boxMass ℓ d u :=
      div_nonneg hS (le_of_lt hV)
    linarith
  unfold Work.BoseFixB1.rungQ Work.BoseFixB1.rungRate
  have hC0a : 0 ≤ C₀ * _root_.BoseGases.a v := mul_nonneg hC₀ ha
  have hC0anq : 0 ≤ C₀ * _root_.BoseGases.a v
      * Work.BoseFixB1S.boxQCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
          (Submission.BoseGases.dlBox ℓ d u) Φ := mul_nonneg hC0a hnq
  have h1 : μ * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
          (Submission.BoseGases.dlBox ℓ d u) i Φ x) ^ 2
          * Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) (x i))
      ≤ μ * (C₀ * _root_.BoseGases.a v
          * Work.BoseFixB1S.boxQCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
              (Submission.BoseGases.dlBox ℓ d u) Φ) :=
    mul_le_mul_of_nonneg_left hQ (le_of_lt hμ)
  have h2 : μ * (C₀ * _root_.BoseGases.a v
        * Work.BoseFixB1S.boxQCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
            (Submission.BoseGases.dlBox ℓ d u) Φ)
      ≤ (μ + Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
              (Submission.BoseGases.dlBox ℓ d u) Φ / Work.SmallBoxSliding.boxMass ℓ d u)
          * (C₀ * _root_.BoseGases.a v
            * Work.BoseFixB1S.boxQCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                (Submission.BoseGases.dlBox ℓ d u) Φ) :=
    mul_le_mul_of_nonneg_right hrate hC0anq
  have h3 : (μ + Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
              (Submission.BoseGases.dlBox ℓ d u) Φ / Work.SmallBoxSliding.boxMass ℓ d u)
          * (C₀ * _root_.BoseGases.a v
            * Work.BoseFixB1S.boxQCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                (Submission.BoseGases.dlBox ℓ d u) Φ)
      = C₀ * _root_.BoseGases.a v
          * (μ + Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
              (Submission.BoseGases.dlBox ℓ d u) Φ / Work.SmallBoxSliding.boxMass ℓ d u)
          * Work.BoseFixB1S.boxQCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
              (Submission.BoseGases.dlBox ℓ d u) Φ := by ring
  linarith [h1, h2, h3]

end Work.BoseFixB1
