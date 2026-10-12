import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.KernelFacts
import Submission.Work.BoseFixB1.perpair_peel_of_kernel
import Submission.Work.BoseFixB1.q1_pair_part_sandwich_of_peel
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1

open MeasureTheory
open scoped BigOperators
open Submission.BoseGases

/-! ## Supporting lemmas for the localised kernel `K := wSmallPair M ℓ d u f`

* `wSmallPair_fibre_eq` — the cube fibre of `K` equals `w1Fibre ℓ K` (kernel symmetry).
* `integrableOn_slot_pair_wSmallPair` — integrability of the peeled-pair slot integrand.
* `integrableOn_slot_fibre_wSmallPair` — integrability of the fibre slot integrand.
-/

/-- The cube fibre of the localised kernel equals its `w1Fibre`: for an even numerator
`f` the kernel is symmetric (`wSmall_symm`), so integrating the first slot is the same as
integrating the second. -/
lemma wSmallPair_fibre_eq {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (u : ℝ³) {f : ℝ³ → ℝ}
    (hfeven : ∀ z : ℝ³, f (-z) = f z) (z : ℝ³) :
    (∫ y in acube ℓ, wSmallPair M ℓ d u f y z) = w1Fibre ℓ (wSmallPair M ℓ d u f) z := by
  rw [w1Fibre]
  exact integral_congr_ae (Filter.Eventually.of_forall (fun y => wSmall_symm hM u hfeven y z))

/-- Integrability over the box of the peeled-pair slot integrand
`S x · T x · K (x a) (x b)` for continuous `S`, `T` and distinct slots `a ≠ b`. -/
lemma integrableOn_slot_pair_wSmallPair {N : ℕ} {ℓ d R0 : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    {f : ℝ³ → ℝ} (hf : Integrable f)
    (hfsupp : ∀ z : ℝ³, R0 ≤ ‖z‖ → f z = 0)
    {M : ℕ} (hM : 1 ≤ M) (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * chiR0)
    (u : ℝ³) {a b : Fin N} (hab : a ≠ b) {S T : Submission.BoseGases.X N → ℝ}
    (hS : Continuous S) (hT : Continuous T) :
    IntegrableOn (fun x : Submission.BoseGases.X N =>
        S x * T x * wSmallPair M ℓ d u f (x a) (x b))
      (abox N ℓ) volume := by
  have hST : Continuous (fun x : Submission.BoseGases.X N => S x * T x) := hS.mul hT
  have h := integrableOn_slot_wSmallPair_cont (N := N) (ℓ := ℓ) (d := d) (R := R0)
    hℓ hd hf hfsupp hM hR hRχ u hab hST
  simpa using h

/-- Integrability over the box of the fibre slot integrand
`S x · (w1Fibre ℓ K)(x i)` for continuous `S`. -/
lemma integrableOn_slot_fibre_wSmallPair {N : ℕ} {ℓ d R0 : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    {f : ℝ³ → ℝ} (hf : Integrable f)
    (hfsupp : ∀ z : ℝ³, R0 ≤ ‖z‖ → f z = 0)
    {M : ℕ} (hM : 1 ≤ M) (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * chiR0)
    (u : ℝ³) {i : Fin N} {S : X N → ℝ} (hS : Continuous S) :
    IntegrableOn (fun x : X N => S x * w1Fibre ℓ (wSmallPair M ℓ d u f) (x i))
      (abox N ℓ) volume := by
  have hfib_aem : AEStronglyMeasurable (w1Fibre ℓ (wSmallPair M ℓ d u f))
      (volume.restrict (acube ℓ)) :=
    aestronglyMeasurable_wSmallPairFibre M u hf.aemeasurable
  have hfib_bd : ∀ z ∈ acube ℓ, |w1Fibre ℓ (wSmallPair M ℓ d u f) z| ≤
      (chiSupAbs * chiSmallDecay M)
        * ((2 * (chiSupAbs * chiSmallDecay M) / Work.SmallBoxSliding.smallConvLower M)
            * (∫ w : ℝ³, |f w|)) := by
    intro z hz
    exact wSmallPair_fibre_abs_le_gen (M := M) hM hℓ hd hf hfsupp hR hRχ u z
  exact integrableOn_slot_fibre hℓ i hfib_aem hfib_bd hS

/-- **FS `eq:Q1n0` peel identity at an arbitrary LOCALISED kernel** (`Submission.BoseGases.wSmallPair`,
`Submission/Work/DLSmallKernels.lean`).

For an integrable, even numerator `f` supported in `ball 0 R0`, the localised kernel
`K := wSmallPair M ℓ d u f` is symmetric (`Work.BoseFixB1.wSmall_symm`), and the exact
`n₀`-collapse identity holds:

`2·Σ_{p∈pairSet N}∫_{abox N ℓ}(P_{p.1}Q_{p.2}Φ)·(P_{p.1}P_{p.2}Φ)·K(x_{p.1},x_{p.2})`
`  = 2·(ℓ³)⁻¹·Σ_i∫_{abox N ℓ}(P_iΦ)·(w1Fibre ℓ K (x_i))·(Q_i(Σ_{j≠i}P_jΦ))`.

It is the localised-kernel analogue of the PROVED corpus lemma
`Submission.BoseGases.q1_pair_part_sandwich_n0` (`Submission/Work/Q1Peel.lean`, import it), whose
chain is `q1_pair_peel_N` (= `q1_lhs_closed` + `q1_pair_replace`) + `pairSet_sum_swap_split` +
`q1_slot_collapse` + `q1_n0_collapse`; all of those are stated for the global kernel
`wPairC ℓ (g2 v h)` but their proofs only use: symmetry of the kernel, the slot-peel machinery
`Submission.BoseGases.abox_integral_peel` / `aP_const_in_coord` / `aP_fiber_const_one`, and
integrability.  For the localised kernel, integrability of the slot integrands is
`Work.BoseFixB1.integrableOn_slot_wSmallPair_cont`, and the pointwise fibre bound is
`Work.BoseFixB1.wSmallPair_fibre_abs_le_gen`. -/
theorem q1pair_peel_localised {f : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hf : MeasureTheory.Integrable f)
    {R0 : ℝ} (hR0 : 0 < R0) (hfsupp : ∀ z : EuclideanSpace ℝ (Fin 3), R0 ≤ ‖z‖ → f z = 0)
    (hfeven : ∀ z : EuclideanSpace ℝ (Fin 3), f (-z) = f z)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
    (u : EuclideanSpace ℝ (Fin 3)) {N : ℕ} {Φ : Submission.BoseGases.X N → ℝ}
    (hΦc : Continuous Φ) :
    2 * (∑ p ∈ Submission.BoseGases.pairSet N, ∫ x in Submission.BoseGases.abox N ℓ,
        (Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aQ ℓ p.2 Φ) x)
          * (Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aP ℓ p.2 Φ) x)
          * Submission.BoseGases.wSmallPair M ℓ d u f (x p.1) (x p.2))
      = 2 * (ℓ ^ 3)⁻¹ * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        (Submission.BoseGases.aP ℓ i Φ x)
          * (Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmallPair M ℓ d u f) (x i))
          * (Submission.BoseGases.aQ ℓ i (fun y : Submission.BoseGases.X N =>
              (∑ j : Fin N, if _hj : j ≠ i then Submission.BoseGases.aP ℓ j Φ y else 0)) x))
    := by
  classical
  have hsym : ∀ z : EuclideanSpace ℝ (Fin 3),
      (∫ y in Submission.BoseGases.acube ℓ, Submission.BoseGases.wSmallPair M ℓ d u f y z)
        = Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmallPair M ℓ d u f) z :=
    fun z => wSmallPair_fibre_eq hM u hfeven z
  have hfibbd : ∀ z ∈ Submission.BoseGases.acube ℓ,
      |Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmallPair M ℓ d u f) z| ≤
        (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
          * ((2 * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
              / Work.SmallBoxSliding.smallConvLower M)
            * (∫ w : EuclideanSpace ℝ (Fin 3), |f w|)) := by
    intro z _
    exact wSmallPair_fibre_abs_le_gen (M := M) hM hℓ hd hf hfsupp hR hRχ u z
  have hfibaem : AEStronglyMeasurable
      (Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmallPair M ℓ d u f))
      (volume.restrict (Submission.BoseGases.acube ℓ)) :=
    aestronglyMeasurable_wSmallPairFibre M u hf.aemeasurable
  have hInt1 : ∀ i j : Fin N, i ≠ j → IntegrableOn
      (fun x : Submission.BoseGases.X N =>
        (Submission.BoseGases.aP ℓ j (Submission.BoseGases.aQ ℓ i Φ) x)
          * (Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Φ) x)
          * Submission.BoseGases.wSmallPair M ℓ d u f (x j) (x i))
      (Submission.BoseGases.abox N ℓ) volume := by
    intro i j hij
    exact integrableOn_slot_pair_wSmallPair (a := j) (b := i) hℓ hd hf hfsupp hM hR hRχ u
      hij.symm
      (aP_continuous hℓ j (aQ_continuous hℓ i hΦc))
      (aP_continuous hℓ j (aP_continuous hℓ i hΦc))
  have hInt2 : ∀ i j : Fin N, i ≠ j → IntegrableOn
      (fun x : Submission.BoseGases.X N =>
        (Submission.BoseGases.aP ℓ j (Submission.BoseGases.aQ ℓ i Φ) x)
          * (Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Φ) x)
          * Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmallPair M ℓ d u f) (x i))
      (Submission.BoseGases.abox N ℓ) volume := by
    intro i j _
    have hS : Continuous (fun x : Submission.BoseGases.X N =>
        (Submission.BoseGases.aP ℓ j (Submission.BoseGases.aQ ℓ i Φ) x)
          * (Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Φ) x)) :=
      (aP_continuous hℓ j (aQ_continuous hℓ i hΦc)).mul
        (aP_continuous hℓ j (aP_continuous hℓ i hΦc))
    simpa using (integrableOn_slot_fibre_wSmallPair (N := N) hℓ hd hf hfsupp hM hR hRχ u
      (i := i) (S := fun x : Submission.BoseGases.X N =>
        (Submission.BoseGases.aP ℓ j (Submission.BoseGases.aQ ℓ i Φ) x)
          * (Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Φ) x)) hS)
  have hInt3 : ∀ i j : Fin N, i ≠ j → IntegrableOn
      (fun x : Submission.BoseGases.X N =>
        (Submission.BoseGases.aP ℓ j (Submission.BoseGases.aQ ℓ i Φ) x)
          * (Submission.BoseGases.aP ℓ i Φ x)
          * Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmallPair M ℓ d u f) (x i))
      (Submission.BoseGases.abox N ℓ) volume := by
    intro i j _
    have hS : Continuous (fun x : Submission.BoseGases.X N =>
        (Submission.BoseGases.aP ℓ j (Submission.BoseGases.aQ ℓ i Φ) x)
          * (Submission.BoseGases.aP ℓ i Φ x)) :=
      (aP_continuous hℓ j (aQ_continuous hℓ i hΦc)).mul (aP_continuous hℓ i hΦc)
    simpa using (integrableOn_slot_fibre_wSmallPair (N := N) hℓ hd hf hfsupp hM hR hRχ u
      (i := i) (S := fun x : Submission.BoseGases.X N =>
        (Submission.BoseGases.aP ℓ j (Submission.BoseGases.aQ ℓ i Φ) x)
          * (Submission.BoseGases.aP ℓ i Φ x)) hS)
  exact q1_pair_part_sandwich_of_peel (ℓ := ℓ) hℓ hΦc
    (perpair_peel_of_kernel (N := N) (ℓ := ℓ) hℓ hΦc hsym hfibaem hfibbd hInt1 hInt2 hInt3)
    hInt3

end Work.BoseFixB1
