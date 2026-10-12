import ChallengeDeps
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Order.Group.Lattice
import Submission.Work.BoseFixB1B.sectorStratum
import Submission.Work.SlotWord.integrableOn_boxQInd_sq_of_boundedOn
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1B.potGapAdditivityStratum` — additivity of the gap+potential word over
the slot-set strata

**STATUS (revised by the holder).**  This file is `sorry`-free and axiom-clean
(`propext`, `Classical.choice`, `Quot.sound`).  The *requested* statement was **false as
written** — the potential half needs the integrability hypothesis (★) below — and it has been
**removed** from the file; what is left is the *repaired*, proved version
(`potGapAdditivityStratum_of_integrable`), the two halves separately
(`cnPlusBoxInd_eq_sum_stratum` unconditionally, `qLHSwordB_eq_sum_stratum` from (★)), and the
two kernel lemmas of §4 that discharge (★) from the paper's standing hypotheses.

## The requested statement (FALSE as written — do not use)

`potGapAdditivityStratum` (at the bottom of this file, kept verbatim) asks, under
`h : ScatSol v`, `0 < ℓ`, `0 < d`, `0 < μ` and `Continuous Φ` alone, for the split of the
combined localised word `tbGapCoeff (ℓd) ε · n₊(B(u)) + qLHSwordB` into the sum of its
slot-set-stratum pieces:

    c·cnPlusBoxInd … Φ + qLHSwordB … Φ = Σ_S (c·cnPlusBoxInd … (1_S Φ) + qLHSwordB … (1_S Φ)).

**This is false** (it is already *unprovable*, and in the degenerate cases genuinely false):
the potential half is a *signed* multiplication form, so splitting it needs the Bochner
integral of each piece, i.e. the hypothesis

    hint : ∀ S, IntegrableOn (fun x => qLHSden N ℓ μ w w₁ x * (1_S Φ x)²) (abox N ℓ)      (★)

— exactly the hypothesis carried by the corpus's own slot-additivity lemma for the same
word, `Work.PerSector.qLHSword_eq_sum_slotPiece` (and by
`Work.FockBridge.qLHSword_eq_sum_sectorPiece`).  (★) is **not** implied by the hypotheses
above: `ScatSol v` only records `LocallyIntegrable w`, `LocallyIntegrable (v * (1 - w))` and
the weak equation `-Δw = ½ v (1-w)` (`ChallengeDeps.lean`), so `v` need be neither bounded nor
locally `L¹` — the counterexample family is documented in
`Submission/Work/BoseFixB1/FINDING_sbWord_marginal_integrable_missing_hv1.md` (and
`Submission/Work/BoseFixR/PotFibreMarginalNoMemLp.lean`, `FINDING_potGapAdditivityStratum.md`
next to this file): `ψ ≡ 0` near `0`, `ψ → 1`, `w := 1 - ψ`, `v := 2Δψ/ψ` gives `ScatSol v`
with `v ∉ L¹_loc` on a sphere, while `g₀ = v(1-w) = 2Δψ` stays locally integrable.  There the
two-body term `½Σ_p wSmallPair M ℓ d u v (x p.1) (x p.2)·Φ²` of the `qLHSword` integrand has a
non-integrable positive part (the kernel's numerator is `v` itself), so the left-hand side's
potential integral is the junk value `∫ = 0` (`MeasureTheory.integral_undef`), while the
pieces of cardinality `≤ 1` — which carry *no* pair term, and whose one-body kernel has the
honest locally integrable numerator `g₀` — are honest finite non-zero numbers.  Hence the two
sides differ (the kinetic half being additive in *both* readings, `cnPlusBoxInd_eq_sum_stratum`
below).

## The repair (proved below)

The kinetic half needs *no* hypothesis on `v` at all: the projection is bounded on the box, so
the squared projections are automatically integrable on the (finite-measure) box for every
continuous state, and `cnPlusBoxInd` is slot-additive.  The repair is to add (★) — or,
equivalently, the paper's standing hypotheses (`MemLp v 1`, support and radius conditions),
from which (★) follows from the two kernel lemmas of §4.

| name (this file) | content |
|---|---|
| `stratum_eq_slotSet`, `indicator_stratum_eq_slotPiece` | the two corpus vocabularies agree definitionally |
| `boxQInd_sq_integrableOn_of_bound` | `(Q_{B(u),i}Ψ)² ∈ L¹(abox)` for measurable `Ψ` bounded on the box |
| `boxQInd_sq_stratumPiece_integrableOn` | the same at the stratum pieces of a **continuous** `Φ` |
| `cnPlusBoxInd_eq_sum_stratum` | **kinetic additivity**: `Continuous Φ` suffices |
| `qLHSwordB_eq_sum_stratum` | **potential additivity**, from the integrability hypothesis (★) |
| `potGapAdditivityStratum_of_integrable` | **the repaired statement**: the identity with (★) added |
| `integrableOn_mul_abs_v_pair` | the pair half of (★) over the box, from `MemLp v 1` |
| `w1Fibre_bdd` | the one-body half of (★): the localised fibre is bounded under the paper's regime |
-/

namespace Work.BoseFixB1B

open MeasureTheory
open scoped Real BigOperators

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false

variable {N : ℕ}

/-! ## 0. The two vocabularies agree -/

/-- `Work.BoseFixB1B.stratum` is `Work.PerSector.slotSet` (both are
`{x | ∀ i, x i ∈ B ↔ i ∈ S}`), so the corpus's slot-additivity package applies verbatim. -/
lemma stratum_eq_slotSet (B : Set ℝ³) (S : Finset (Fin N)) :
    stratum B S = Work.PerSector.slotSet B S := rfl

/-- The stratum piece is the slot piece of the per-sector chapter. -/
lemma indicator_stratum_eq_slotPiece (B : Set ℝ³) (S : Finset (Fin N)) (Φ : X N → ℝ) :
    (stratum B S).indicator Φ = Work.PerSector.slotPiece B S Φ := rfl

/-! ## 1. The kinetic half

The only analytic input is the boundedness of the box mean, which uses the finiteness of the
measure of `abox N ℓ` and the inclusion `B(u) ⊆ acube ℓ`; no kernel, hence no hypothesis on
`v`, occurs. -/

/-- A continuous function is bounded on the box. -/
private lemma exists_abs_bound_abox {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ abox N ℓ, |Φ x| ≤ C := by
  obtain ⟨C, hC⟩ := (abox_compact N hℓ).exists_bound_of_continuousOn hΦc.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x hx => ?_⟩
  have h := hC x hx
  rw [Real.norm_eq_abs] at h
  exact le_trans h (le_max_left _ _)

/-- **The squared box projection is integrable on the box** for any measurable state that is
bounded on the box (no hypothesis on the kernels). -/
lemma boxQInd_sq_integrableOn_of_bound {ℓ d : ℝ} (hℓ : 0 < ℓ) (u : ℝ³) {Ψ : X N → ℝ}
    (hΨ : Measurable Ψ) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ x ∈ abox N ℓ, |Ψ x| ≤ C) (i : Fin N) :
    IntegrableOn (fun x => (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
        (dlBox ℓ d u) i Ψ x) ^ 2) (abox N ℓ) := by
  refine Work.SlotWord.integrableOn_boxQInd_sq_of_boundedOn (M := N) (A := dlBox ℓ d u)
    (a := ℓ) (volA := Work.SmallBoxSliding.boxMass ℓ d u)
    (Work.SmallBoxSliding.measurableSet_dlBox ℓ d u) ?_ ?_ hΨ hC0 hC i
  · intro x hx
    exact ((mem_dlBox_iff ℓ d u x).mp hx).1
  · exact Work.SmallBoxSliding.boxMass_eq_measureReal ℓ d u

/-- The same at the stratum pieces of a continuous state `Φ`. -/
lemma boxQInd_sq_stratumPiece_integrableOn {ℓ d : ℝ} (hℓ : 0 < ℓ) (u : ℝ³)
    (S : Finset (Fin N)) (i : Fin N) {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    IntegrableOn (fun x => (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
        (dlBox ℓ d u) i ((stratum (dlBox ℓ d u) S).indicator Φ) x) ^ 2) (abox N ℓ) := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_bound_abox (N := N) (ℓ := ℓ) hℓ hΦc
  refine boxQInd_sq_integrableOn_of_bound (N := N) hℓ u ?_ hC0 ?_ i
  · exact Measurable.indicator hΦc.measurable
      (stratum_measurable (Work.SmallBoxSliding.measurableSet_dlBox ℓ d u) S)
  · intro x hx
    by_cases hxs : x ∈ stratum (dlBox ℓ d u) S
    · rw [Set.indicator_of_mem hxs]
      exact hC x hx
    · rw [Set.indicator_of_notMem hxs]
      simpa using hC0

/-- **The box excited count is additive over the slot-set strata** — from `Continuous Φ` alone.
`n₊ = Σ_i‖Q_{B(u),i}Φ‖²`: the pointwise identity
`(Q_{B(u),i}Φ)² = Σ_S (Q_{B(u),i}(1_S Φ))²`
(`Work.PerSector.sq_boxQInd_eq_sum_sq_boxQInd_slotPiece`) is integrated over the box, each
piece being bounded there. -/
theorem cnPlusBoxInd_eq_sum_stratum {ℓ d : ℝ} (hℓ : 0 < ℓ) (u : ℝ³) {Φ : X N → ℝ}
    (hΦc : Continuous Φ) :
    Work.UBBInputs8.cnPlusBoxInd ℓ (dlBox ℓ d u) (Work.SmallBoxSliding.boxMass ℓ d u) Φ
      = ∑ S : Finset (Fin N),
          Work.UBBInputs8.cnPlusBoxInd ℓ (dlBox ℓ d u) (Work.SmallBoxSliding.boxMass ℓ d u)
            ((stratum (dlBox ℓ d u) S).indicator Φ) := by
  have hA : MeasurableSet (dlBox ℓ d u) := Work.SmallBoxSliding.measurableSet_dlBox ℓ d u
  have hslot : ∀ i : Fin N,
      (∫ x in abox N ℓ, (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
          (dlBox ℓ d u) i Φ x) ^ 2)
        = ∑ S : Finset (Fin N), ∫ x in abox N ℓ, (Work.UBBInputs8.boxQInd
            (Work.SmallBoxSliding.boxMass ℓ d u) (dlBox ℓ d u) i
            ((stratum (dlBox ℓ d u) S).indicator Φ) x) ^ 2 := by
    intro i
    obtain ⟨C, hC0, hC⟩ := exists_abs_bound_abox (N := N) (ℓ := ℓ) hℓ hΦc
    have h := Work.PerSector.cnPlusBoxInd_eq_sum_slotPiece (N := N) (A := dlBox ℓ d u) hA
      (volA := Work.SmallBoxSliding.boxMass ℓ d u) (a := ℓ) i (Φ := Φ)
      (fun S => by
        simpa only [indicator_stratum_eq_slotPiece] using
          boxQInd_sq_stratumPiece_integrableOn (N := N) hℓ u S i hΦc)
      (boxQInd_sq_integrableOn_of_bound (N := N) hℓ u hΦc.measurable hC0 hC i)
    simpa only [indicator_stratum_eq_slotPiece] using h
  calc Work.UBBInputs8.cnPlusBoxInd ℓ (dlBox ℓ d u) (Work.SmallBoxSliding.boxMass ℓ d u) Φ
      = ∑ i : Fin N, ∫ x in abox N ℓ, (Work.UBBInputs8.boxQInd
          (Work.SmallBoxSliding.boxMass ℓ d u) (dlBox ℓ d u) i Φ x) ^ 2 := rfl
    _ = ∑ i : Fin N, ∑ S : Finset (Fin N), ∫ x in abox N ℓ, (Work.UBBInputs8.boxQInd
          (Work.SmallBoxSliding.boxMass ℓ d u) (dlBox ℓ d u) i
          ((stratum (dlBox ℓ d u) S).indicator Φ) x) ^ 2 :=
        Finset.sum_congr rfl (fun i _ => hslot i)
    _ = ∑ S : Finset (Fin N), ∑ i : Fin N, ∫ x in abox N ℓ, (Work.UBBInputs8.boxQInd
          (Work.SmallBoxSliding.boxMass ℓ d u) (dlBox ℓ d u) i
          ((stratum (dlBox ℓ d u) S).indicator Φ) x) ^ 2 := Finset.sum_comm
    _ = ∑ S : Finset (Fin N),
          Work.UBBInputs8.cnPlusBoxInd ℓ (dlBox ℓ d u) (Work.SmallBoxSliding.boxMass ℓ d u)
            ((stratum (dlBox ℓ d u) S).indicator Φ) :=
        Finset.sum_congr rfl (fun S _ => rfl)

/-! ## 2. The potential half (from the integrability of the pieces) -/

/-- **The localised potential word is additive over the slot-set strata**, given the
integrability of the pieces (hypothesis (★) — *not* a consequence of `ScatSol v`, see the
module doc).  `qLHSword` is the multiplication form `∫ qLHSden·Φ²`, whose density `Φ²` is the
sum of the stratum pieces' squares, so the integral splits; the corpus's slot-additivity lemma
`Work.PerSector.qLHSword_eq_sum_slotPiece` is exactly this statement. -/
theorem qLHSwordB_eq_sum_stratum {v : ℝ³ → ℝ}
    (h : ∃ w : ℝ³ → ℝ, _root_.BoseGases.IsRadial w ∧
      _root_.BoseGases.IsScatteringSolution w v)
    {M : ℕ} {ℓ d μ : ℝ} (u : ℝ³) {Φ : X N → ℝ}
    (hint : ∀ S : Finset (Fin N), IntegrableOn (fun x => Submission.BoseGases.qLHSden N ℓ μ
        (Submission.BoseGases.wSmallPair M ℓ d u v)
        (Submission.BoseGases.wSmall1Pair h M ℓ d u) x
        * ((stratum (dlBox ℓ d u) S).indicator Φ x) ^ 2) (abox N ℓ)) :
    Work.SmallBoxSliding.qLHSwordB (v := v) h M ℓ d μ u Φ
      = ∑ S : Finset (Fin N),
          Work.SmallBoxSliding.qLHSwordB (v := v) h M ℓ d μ u
            ((stratum (dlBox ℓ d u) S).indicator Φ) := by
  have hmain := Work.PerSector.qLHSword_eq_sum_slotPiece (N := N) (ℓ := ℓ) (μ := μ)
    (B := dlBox ℓ d u) (Submission.BoseGases.wSmallPair M ℓ d u v)
    (Submission.BoseGases.wSmall1Pair h M ℓ d u) (Φ := Φ)
    (fun S => by simpa only [indicator_stratum_eq_slotPiece] using hint S)
  simpa only [Work.SmallBoxSliding.qLHSwordB, indicator_stratum_eq_slotPiece] using hmain

/-! ## 3. The repaired statement -/

/-- **The repaired `potGapAdditivityStratum`**: the requested identity, with the integrability
hypothesis (★) of the potential pieces added (the kinetic half, and the whole bookkeeping of
the `tbGapCoeff`-weighted sum, need nothing else). -/
theorem potGapAdditivityStratum_of_integrable {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ, _root_.BoseGases.IsRadial w ∧
      _root_.BoseGases.IsScatteringSolution w v)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d μ ε : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hμ : 0 < μ)
    (u : EuclideanSpace ℝ (Fin 3)) {N : ℕ} {Φ : Submission.BoseGases.X N → ℝ}
    (hΦc : Continuous Φ)
    (hint : ∀ S : Finset (Fin N), IntegrableOn (fun x => Submission.BoseGases.qLHSden N ℓ μ
        (Submission.BoseGases.wSmallPair M ℓ d u v)
        (Submission.BoseGases.wSmall1Pair h M ℓ d u) x
        * ((Work.BoseFixB1B.stratum (Submission.BoseGases.dlBox ℓ d u) S).indicator Φ x) ^ 2)
        (Submission.BoseGases.abox N ℓ)) :
    (Work.SmallBoxTBWord.tbGapCoeff (ℓ * d) ε
        * Work.UBBInputs8.cnPlusBoxInd ℓ (Submission.BoseGases.dlBox ℓ d u)
            (Work.SmallBoxSliding.boxMass ℓ d u) Φ
      + Work.SmallBoxSliding.qLHSwordB (v := v) h M ℓ d μ u Φ)
      = ∑ S : Finset (Fin N),
          (Work.SmallBoxTBWord.tbGapCoeff (ℓ * d) ε
              * Work.UBBInputs8.cnPlusBoxInd ℓ (Submission.BoseGases.dlBox ℓ d u)
                  (Work.SmallBoxSliding.boxMass ℓ d u)
                  ((Work.BoseFixB1B.stratum (Submission.BoseGases.dlBox ℓ d u) S).indicator Φ)
            + Work.SmallBoxSliding.qLHSwordB (v := v) h M ℓ d μ u
              ((Work.BoseFixB1B.stratum (Submission.BoseGases.dlBox ℓ d u) S).indicator Φ)) := by
  rw [cnPlusBoxInd_eq_sum_stratum (N := N) hℓ u hΦc,
    qLHSwordB_eq_sum_stratum (v := v) h (M := M) u hint,
    Finset.mul_sum, Finset.sum_add_distrib]

/-! ## 4. The two kernel lemmas discharging (★) from the paper's standing hypotheses

(★) is *not* a consequence of `ScatSol v` alone (that is the finding of this file), but it does
follow from the standing hypotheses of Theorem 1.2 (`MemLp v 1`, `tsupport v ⊆ ball 0 R0`, and
the two radius conditions `R0 ≤ (ℓd)/16`, `R0 ≤ ℓ·chiR0`, which every supplier of the sliding
kernel bounds carries): the pair part by Fubini (`pairInt_sq`), the one-body part by the fibre
bound below.  These are the kernel data that the corpus's own
`Work.SlotWord.integrableOn_slotPiece_sq_qLHSden` takes as hypotheses (`hwb`/`hw1b`). -/

/-- **The box-restricted pair integrand of an `L¹` potential is integrable.**  For a measurable
weight `Ψ` bounded by `C` on the box, `x ↦ Ψ x · |v (x p.1 − x p.2)|` is integrable over
`abox N ℓ`.  (The box version of `Submission.BoseGases.pairInt_sq`: a compactly supported bump
equal to `1` on the box transplants the full-space statement to the box.) -/
lemma integrableOn_mul_abs_v_pair {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hv1 : MeasureTheory.MemLp v 1) {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Ψ : X N → ℝ} (hΨm : Measurable Ψ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x ∈ abox N ℓ, |Ψ x| ≤ C) {p : Fin N × Fin N} (hp : p ∈ pairSet N) :
    IntegrableOn (fun x : X N => Ψ x * |v (x p.1 - x p.2)|) (abox N ℓ) := by
  classical
  have hpne : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
  -- a bump that is `1` on the box, with compact support
  obtain ⟨f, hf1, -, hfcs, -⟩ := exists_continuous_one_zero_of_isCompact
    (s := abox N ℓ) (t := (∅ : Set (X N))) (abox_compact N hℓ) isClosed_empty
    (Set.disjoint_empty _)
  -- the full-space pair integral of `v` against `f²`
  have hfint : Integrable (fun x : X N => f x ^ 2 * |v (x p.1 - x p.2)|) volume := by
    have h := Submission.BoseGases.pairInt_sq (v := fun y => ‖v y‖) hv1.norm f.continuous hfcs
      p.1 p.2
    simpa only [Real.norm_eq_abs] using h
  have hbox : Integrable (fun x : X N => f x ^ 2 * |v (x p.1 - x p.2)|)
      (volume.restrict (abox N ℓ)) :=
    hfint.mono_measure MeasureTheory.Measure.restrict_le_self
  have hbase : IntegrableOn (fun x : X N => |v (x p.1 - x p.2)|) (abox N ℓ) := by
    refine hbox.congr ?_
    filter_upwards [ae_restrict_mem (abox_measurable N ℓ)] with x hx
    rw [hf1 hx]
    simp
  refine (hbase.const_mul C).mono' ?_ ?_
  · -- a.e.-strong measurability: reduce `v` to a measurable representative
    have hvae : AEMeasurable v volume := hv1.aemeasurable
    set w : ℝ³ → ℝ := hvae.mk v with hw
    have hwm : Measurable w := hvae.measurable_mk
    have hvw : v =ᵐ[volume] w := hvae.ae_eq_mk
    have hmeasw : AEMeasurable (fun x : X N => w (x p.1 - x p.2)) volume :=
      (hwm.comp (by fun_prop : Measurable fun x : X N => x p.1 - x p.2)).aemeasurable
    have hae : (fun x : X N => w (x p.1 - x p.2)) =ᵐ[volume]
        (fun x : X N => v (x p.1 - x p.2)) := by
      have hN : volume {y : ℝ³ | v y ≠ w y} = 0 := by
        rw [← ae_iff]
        exact hvw
      obtain ⟨t, hsub, htmeas, ht0⟩ := exists_measurable_superset_of_null hN
      rw [Filter.EventuallyEq, ae_iff]
      refine measure_mono_null ?_ (Submission.BoseGases.null_preimage_pair_whole htmeas ht0
        p.1 p.2 hpne)
      intro x hx
      exact hsub (Ne.symm hx)
    have hvaemeas : AEMeasurable (fun x : X N => v (x p.1 - x p.2)) volume :=
      hmeasw.congr hae
    have habs : AEMeasurable (fun x : X N => |v (x p.1 - x p.2)|) volume :=
      (by fun_prop : Measurable fun t : ℝ => |t|).comp_aemeasurable hvaemeas
    have hmul : AEMeasurable (fun x : X N => Ψ x * |v (x p.1 - x p.2)|) volume :=
      hΨm.aemeasurable.mul habs
    exact hmul.aestronglyMeasurable.mono_measure
      MeasureTheory.Measure.restrict_le_self
  · filter_upwards [ae_restrict_mem (abox_measurable N ℓ)] with x hx
    simp only [Real.norm_eq_abs, abs_mul, abs_abs]
    exact mul_le_mul_of_nonneg_right (hC x hx) (abs_nonneg _)

/-- **The one-body fibre of the localised kernel is bounded**, under the standing hypotheses of
the paper.  The kernel is dominated pointwise by `K·|g₀(x−y)|`
(`Work.SmallBoxSliding.abs_wSmall1Pair_le`) and `g₀ = v(1−w₀) ∈ L¹`
(`Submission.BoseGases.g0_integrable`), so the fibre integral is bounded by `K·∫|g₀|`. -/
lemma w1Fibre_bdd {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ, _root_.BoseGases.IsRadial w ∧
      _root_.BoseGases.IsScatteringSolution w v)
    {R0 : ℝ} (hR0 : 0 < R0)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hdR : R0 ≤ ℓ * d / 16) (hdRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
    (u : EuclideanSpace ℝ (Fin 3)) :
    ∃ Cf : ℝ, 0 ≤ Cf ∧ ∀ x : EuclideanSpace ℝ (Fin 3),
      |Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) x| ≤ Cf := by
  have hSpos : 0 < Work.SmallBoxSliding.smallConvLower M :=
    Work.SmallBoxSliding.smallConvLower_pos M
  have hSupnn : 0 ≤ Submission.BoseGases.chiSupAbs := Submission.BoseGases.chiSupAbs_nonneg
  have hg0int : Integrable (Submission.BoseGases.g0 v h) :=
    Submission.BoseGases.g0_integrable hR0 hv_supp h
  set K : ℝ := Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M
      * (2 * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
          / Work.SmallBoxSliding.smallConvLower M) with hKdef
  have hFnn : 0 ≤ 2 * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
      / Work.SmallBoxSliding.smallConvLower M :=
    div_nonneg (mul_nonneg (by norm_num)
      (mul_nonneg hSupnn (Submission.BoseGases.chiSmallDecay_nonneg M))) (le_of_lt hSpos)
  have hK0 : 0 ≤ K := by
    rw [hKdef]
    exact mul_nonneg (mul_nonneg hSupnn (Submission.BoseGases.chiSmallDecay_nonneg M)) hFnn
  refine ⟨K * ∫ z, |Submission.BoseGases.g0 v h z|,
    mul_nonneg hK0 (integral_nonneg fun z => abs_nonneg (Submission.BoseGases.g0 v h z)), ?_⟩
  intro x
  -- the pointwise domination of the localised one-body kernel
  have hdom : ∀ y : EuclideanSpace ℝ (Fin 3),
      |Submission.BoseGases.wSmall1Pair h M ℓ d u x y| ≤
        K * |Submission.BoseGases.g0 v h (x - y)| := by
    intro y
    have hb := Work.SmallBoxSliding.abs_wSmall1Pair_le hv_supp hR0 h hM hℓ hd hdR hdRχ u x y
    have hχle : Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u)
        ≤ Submission.BoseGases.chiSmallDecay M := by
      have hb' := Submission.BoseGases.chiSmall_decay_coord_le_decay hM ((ℓ * d)⁻¹ • x - u)
      rwa [abs_of_nonneg (Submission.BoseGases.chiSmall_nonneg M _)] at hb'
    have hstep : Submission.BoseGases.chiSupAbs
          * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u)
        ≤ Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M :=
      mul_le_mul_of_nonneg_left hχle hSupnn
    calc |Submission.BoseGases.wSmall1Pair h M ℓ d u x y|
        ≤ (Submission.BoseGases.chiSupAbs
              * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u))
            * (2 * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
                * |Submission.BoseGases.g0 v h (x - y)|)
            / Work.SmallBoxSliding.smallConvLower M := hb
      _ = (Submission.BoseGases.chiSupAbs
              * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u)
              * (2 * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
                  / Work.SmallBoxSliding.smallConvLower M))
            * |Submission.BoseGases.g0 v h (x - y)| := by ring
      _ ≤ (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M
              * (2 * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
                  / Work.SmallBoxSliding.smallConvLower M))
            * |Submission.BoseGases.g0 v h (x - y)| :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hstep hFnn) (abs_nonneg _)
      _ = K * |Submission.BoseGases.g0 v h (x - y)| := by rw [hKdef]
  -- the dominating function is integrable
  have hdomint : Integrable (fun y : EuclideanSpace ℝ (Fin 3) =>
      K * |Submission.BoseGases.g0 v h (x - y)|) :=
    (hg0int.abs.comp_sub_left x).const_mul K
  -- the fibre integrand is a.e.-strongly measurable at the fixed `x`
  have haesm : AEStronglyMeasurable
      (fun y : EuclideanSpace ℝ (Fin 3) => Submission.BoseGases.wSmall1Pair h M ℓ d u x y)
      volume := by
    have hg0ae : AEMeasurable (Submission.BoseGases.g0 v h) volume :=
      (Classical.choose_spec h).2.rhs_integrable.aestronglyMeasurable.aemeasurable
    have hnum : AEMeasurable (fun y : EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.g0 v h (x - y)) volume :=
      hg0ae.comp_quasiMeasurePreserving
        (volume.measurePreserving_sub_left x).quasiMeasurePreserving
    have hden1 : AEMeasurable (fun y : EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.convScaleSmall M (ℓ * d) (x - y)) volume :=
      ((Submission.BoseGases.conv3Small_continuous (M := M) hM).comp
        (by fun_prop : Continuous fun y : EuclideanSpace ℝ (Fin 3) =>
          (ℓ * d)⁻¹ • (x - y))).aemeasurable
    have hden2 : AEMeasurable (fun y : EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.convScale ℓ (x - y)) volume :=
      ((Submission.BoseGases.convScale_continuous ℓ).comp
        (by fun_prop : Continuous fun y : EuclideanSpace ℝ (Fin 3) => x - y)).aemeasurable
    have hchi : AEMeasurable (fun y : EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.chiSmallB M ℓ d u y) volume :=
      ((Submission.BoseGases.chiScale_continuous ℓ).mul
        ((Submission.BoseGases.chiSmall_continuous hM).comp
          (by fun_prop : Continuous fun y : EuclideanSpace ℝ (Fin 3) =>
            (ℓ * d)⁻¹ • y - u))).aemeasurable
    have hW : AEMeasurable (fun y : EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.wSmallScaled M (ℓ * d) (Submission.BoseGases.g0 v h) (x - y)
          / Submission.BoseGases.convScale ℓ (x - y)) volume :=
      (hnum.div hden1).div hden2
    have h7 : AEMeasurable (fun y : EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g0 v h) x y) volume := by
      have hmain : AEMeasurable ((fun _ : EuclideanSpace ℝ (Fin 3) =>
              Submission.BoseGases.chiSmallB M ℓ d u x) *
            ((fun y : EuclideanSpace ℝ (Fin 3) =>
                Submission.BoseGases.wSmallScaled M (ℓ * d) (Submission.BoseGases.g0 v h)
                  (x - y) / Submission.BoseGases.convScale ℓ (x - y)) *
              (fun y : EuclideanSpace ℝ (Fin 3) =>
                Submission.BoseGases.chiSmallB M ℓ d u y))) volume :=
        (aemeasurable_const (b := Submission.BoseGases.chiSmallB M ℓ d u x)).mul
          (hW.mul hchi)
      refine hmain.congr ?_
      filter_upwards with y
      simp only [Pi.mul_apply]
      rw [Submission.BoseGases.wSmallPair, Submission.BoseGases.wSmallScaled]
      ring
    simpa only [Submission.BoseGases.wSmall1Pair] using h7.aestronglyMeasurable
  have hfibint : IntegrableOn
      (fun y : EuclideanSpace ℝ (Fin 3) => Submission.BoseGases.wSmall1Pair h M ℓ d u x y)
      (Submission.BoseGases.acube ℓ) := by
    refine Integrable.mono' hdomint.integrableOn
      (haesm.mono_measure MeasureTheory.Measure.restrict_le_self) ?_
    filter_upwards with y
    simpa only [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_nonneg hK0] using hdom y
  calc |Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) x|
      = |∫ y in Submission.BoseGases.acube ℓ, Submission.BoseGases.wSmall1Pair h M ℓ d u x y| :=
        rfl
    _ ≤ ∫ y in Submission.BoseGases.acube ℓ,
          |Submission.BoseGases.wSmall1Pair h M ℓ d u x y| := by
        have h := norm_integral_le_integral_norm
          (μ := (volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict
            (Submission.BoseGases.acube ℓ))
          (f := fun y : EuclideanSpace ℝ (Fin 3) =>
            Submission.BoseGases.wSmall1Pair h M ℓ d u x y)
        simpa only [Real.norm_eq_abs] using h
    _ ≤ ∫ y in Submission.BoseGases.acube ℓ,
          K * |Submission.BoseGases.g0 v h (x - y)| :=
        setIntegral_mono_on hfibint.abs hdomint.integrableOn
          (Submission.BoseGases.acube_measurable ℓ) (fun y _ => hdom y)
    _ = K * ∫ y in Submission.BoseGases.acube ℓ,
          |Submission.BoseGases.g0 v h (x - y)| := integral_const_mul K _
    _ ≤ K * ∫ y : EuclideanSpace ℝ (Fin 3), |Submission.BoseGases.g0 v h (x - y)| :=
        mul_le_mul_of_nonneg_left
          (setIntegral_le_integral (hg0int.abs.comp_sub_left x)
            (ae_of_all _ fun y => abs_nonneg _)) hK0
    _ = K * ∫ z : EuclideanSpace ℝ (Fin 3), |Submission.BoseGases.g0 v h z| := by
        congr 1
        exact MeasureTheory.integral_sub_left_eq_self
          (fun z : EuclideanSpace ℝ (Fin 3) => |Submission.BoseGases.g0 v h z|) volume x

/-! ## 5. The requested statement (false — kept verbatim, do not use)

The identity below is what was requested.  It is **not** provable from its hypotheses: (★) is
missing (see the module doc, and the repaired `potGapAdditivityStratum_of_integrable` above). -/

end Work.BoseFixB1B
