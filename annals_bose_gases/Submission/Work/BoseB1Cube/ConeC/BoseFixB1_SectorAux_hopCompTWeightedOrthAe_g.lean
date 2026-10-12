import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseB1Cube.ConeC.BoseFixB1S_a0A2QJointExpansionFib
import Submission.Work.BoseFixB1.SectorAux.weightedOrthMemSGood
import Submission.Work.BoseFixB1S.fibreAeTransfer
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1.SectorAux.hopCompTWeightedOrthAe_g`

The weighted orthogonality of the three-way box components for **measurable, box-bounded**
states `Φ`, `Ψ` and a weight `g` that is only **a.e. strongly measurable** (and bounded) on the
one-particle cube `acube ℓ`:

    ∫_{abox N ℓ} (boxCompT volA A S T Φ)(g(x i))(boxCompT volA A S' T' Ψ) = 0 ,

whenever the two disjoint pairs `(S,T)`, `(S',T')` have different slot types in a slot `j ≠ i`.

This is `Work.BoseFixB1S.hopSlotOrth` (proved for *continuous* `Φ`, `Ψ` and *measurable* `g`)
with both hypothesis families weakened to the level the corpus actually supplies:

* **states**: `GoodState ℓ Φ = Measurable Φ ∧ ∃ C, |Φ| ≤ C on abox N ℓ` is the exact interface
  the slot machinery consumes — the same weakening already carried out for the unweighted
  orthogonality in `SectorAux/boxCompTOrthMeas` (`boxCompTOrthMeas`, `orth_of_mem_S_good`,
  `boxPInd_boxCompT_good`);
* **weight**: the corpus only ever knows `w1Fibre ℓ (wSmall1Pair …)` to be a.e. strongly
  measurable and bounded on `acube ℓ`.  Replacing `g` by the clipped measurable representative
  of `Gen.exists_measurable_clip_ae_eq` (which agrees with `g` a.e. on `acube ℓ`) is legitimate
  because the a.e. equality pulls back along the slot projection
  (`Work.BoseFixB1S.fibreAeTransfer`, on the quasi-measure-preserving coordinate).

## Assembly

1. `hopSlotOrthGood` — the case analysis of `hopSlotOrth` at the `GoodState` level.  The two
   `P`-slot cases are `weightedOrthMemSGood` (the delegated `GoodState` version of
   `weighted_orth_of_mem_S`, using the eigenvector rule `boxPInd_boxCompT_good` and
   self-adjointness `boxPIndSelfAdjoint` together with `Gen.boxPInd_slotWeight`); the two
   `R`-slot cases vanish pointwise on the complementary half-spaces
   (`boxComponent_vanish_off` / `boxComponent_vanish_on` + `integral_mul_eq_zero_of_vanish`).
2. The target theorem: transfer `g` to its clipped measurable representative with
   `exists_measurable_clip_ae_eq` + `fibreAeTransfer`, then apply `hopSlotOrthGood`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseFixB1.SectorAux

open Submission.BoseGases

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## 1. The weighted slot orthogonality for `GoodState` states -/

/-- `Work.BoseFixB1S.hopSlotOrth` with the continuity of `Φ`, `Ψ` weakened to `GoodState`
(measurable and bounded on the analysis box): the case analysis of the weighted slot
orthogonality, the two `P`-slot cases being `weightedOrthMemSGood`. -/
theorem hopSlotOrthGood {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {g : EuclideanSpace ℝ (Fin 3) → ℝ} (hgm : Measurable g) {Bg : ℝ}
    (hgb : ∀ z ∈ Submission.BoseGases.acube ℓ, |g z| ≤ Bg)
    {i j : Fin N} (hij : j ≠ i)
    {S T S' T' : Finset (Fin N)} (hST : Disjoint S T) (hST' : Disjoint S' T')
    (hdif : Work.BoseFixB1S.orthSlotType S T j ≠ Work.BoseFixB1S.orthSlotType S' T' j)
    {Φ Ψ : Submission.BoseGases.X N → ℝ}
    (hΦ : Work.BoseFixB1S.GoodState ℓ Φ) (hΨ : Work.BoseFixB1S.GoodState ℓ Ψ) :
    (∫ x in Submission.BoseGases.abox N ℓ,
        Work.BoseFixB1S.boxCompT volA A S T Φ x * g (x i)
          * Work.BoseFixB1S.boxCompT volA A S' T' Ψ x) = 0 := by
  -- swap the two states, keeping the weight in its own slot `i`
  have hswap : (∫ x in Submission.BoseGases.abox N ℓ,
        Work.BoseFixB1S.boxCompT volA A S T Φ x * g (x i)
          * Work.BoseFixB1S.boxCompT volA A S' T' Ψ x)
      = ∫ x in Submission.BoseGases.abox N ℓ,
          Work.BoseFixB1S.boxCompT volA A S' T' Ψ x * g (x i)
            * Work.BoseFixB1S.boxCompT volA A S T Φ x := by
    apply MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.abox_measurable N ℓ)
    intro x hx
    ring
  by_cases hS : j ∈ S
  · by_cases hS' : j ∈ S'
    · -- `j` is a `P`-slot of both: the slot types agree, contradicting `hdif`
      exact absurd (by unfold Work.BoseFixB1S.orthSlotType; rw [if_pos hS, if_pos hS']) hdif
    · exact weightedOrthMemSGood hℓ hvol hA hvolA hAc hgm hgb hij hS hS' hΦ hΨ
  · by_cases hS' : j ∈ S'
    · rw [hswap]
      exact weightedOrthMemSGood hℓ hvol hA hvolA hAc hgm hgb hij hS' hS hΨ hΦ
    · by_cases hT : j ∈ T
      · -- `j` is a `Q`-slot of `(S,T)` but not of `(S',T')`: `R`-slot there, so the two
        -- components are supported on the complementary half-spaces
        have hT' : j ∉ T' := fun h =>
          hdif (by unfold Work.BoseFixB1S.orthSlotType; rw [if_neg hS, if_pos hT, if_neg hS', if_pos h])
        have hnot : j ∉ S' ∪ T' := by
          simp only [Finset.mem_union, not_or]
          exact ⟨hS', hT'⟩
        refine Work.BoseFixB1S.integral_mul_eq_zero_of_vanish (A := A) (j := j)
          (F := fun x => Work.BoseFixB1S.boxCompT volA A S T Φ x * g (x i))
          (G := Work.BoseFixB1S.boxCompT volA A S' T' Ψ) ?_ ?_
        · intro x hx
          rw [Work.BoseFixB1S.boxComponent_vanish_off volA A
            (Finset.mem_union_right S hT) Φ x hx, zero_mul]
        · exact Work.BoseFixB1S.boxComponent_vanish_on volA A hnot Ψ
      · have hT' : j ∈ T' := by
          by_contra h
          exact hdif (by unfold Work.BoseFixB1S.orthSlotType; rw [if_neg hS, if_neg hT, if_neg hS', if_neg h])
        have hnot : j ∉ S ∪ T := by
          simp only [Finset.mem_union, not_or]
          exact ⟨hS, hT⟩
        rw [hswap]
        refine Work.BoseFixB1S.integral_mul_eq_zero_of_vanish (A := A) (j := j)
          (F := fun x => Work.BoseFixB1S.boxCompT volA A S' T' Ψ x * g (x i))
          (G := Work.BoseFixB1S.boxCompT volA A S T Φ) ?_ ?_
        · intro x hx
          rw [Work.BoseFixB1S.boxComponent_vanish_off volA A
            (Finset.mem_union_right S' hT') Ψ x hx, zero_mul]
        · exact Work.BoseFixB1S.boxComponent_vanish_on volA A hnot Φ

/-! ## 2. The requested theorem -/

theorem hopCompTWeightedOrthAe_g {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {g : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hgm : MeasureTheory.AEStronglyMeasurable g
      (MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)))
    {Bg : ℝ} (hgb : ∀ z ∈ Submission.BoseGases.acube ℓ, |g z| ≤ Bg)
    {i j : Fin N} (hij : j ≠ i)
    {S T S' T' : Finset (Fin N)} (hST : Disjoint S T) (hST' : Disjoint S' T')
    (hdif : Work.BoseFixB1S.orthSlotType S T j ≠ Work.BoseFixB1S.orthSlotType S' T' j)
    {Φ Ψ : Submission.BoseGases.X N → ℝ}
    (hΦm : Measurable Φ) {CΦ : ℝ} (hΦb : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Φ x| ≤ CΦ)
    (hΨm : Measurable Ψ) {CΨ : ℝ} (hΨb : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Ψ x| ≤ CΨ) :
    (∫ x in Submission.BoseGases.abox N ℓ,
        Work.BoseFixB1S.boxCompT volA A S T Φ x * g (x i)
          * Work.BoseFixB1S.boxCompT volA A S' T' Ψ x) = 0 := by
  -- replace `g` by a measurable representative, equal to it a.e. on `acube ℓ`
  obtain ⟨f, hfm, hfbd, hgae⟩ :=
    Work.BoseFixB1S.Gen.exists_measurable_clip_ae_eq (ℓ := ℓ) (fib := g) (C := Bg) hgm hgb
  -- the a.e. equality pulls back along the slot projection, so the integrands agree a.e.
  have hge : (fun x : Submission.BoseGases.X N =>
        Work.BoseFixB1S.boxCompT volA A S T Φ x * g (x i)
          * Work.BoseFixB1S.boxCompT volA A S' T' Ψ x)
      =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)]
      (fun x : Submission.BoseGases.X N =>
        Work.BoseFixB1S.boxCompT volA A S T Φ x * f (x i)
          * Work.BoseFixB1S.boxCompT volA A S' T' Ψ x) := by
    filter_upwards [Work.BoseFixB1S.fibreAeTransfer hgae i] with x hx
    rw [hx]
  rw [integral_congr_ae hge]
  exact hopSlotOrthGood (g := f) hℓ hvol hA hvolA hAc hfm (Bg := max Bg 0)
    (fun z _ => hfbd z) hij hST hST' hdif ⟨hΦm, CΦ, hΦb⟩ ⟨hΨm, CΨ, hΨb⟩

end Work.BoseFixB1.SectorAux
