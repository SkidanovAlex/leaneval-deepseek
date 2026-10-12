import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.PQIdentAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1S.n0SumAqEqX`

The per-index sum of the `Q`-weighted `PQ` counts at the FS-faithful box projections equals the
`pairSet` sum of the pair squares:

    Σᵢ ∫_{abox N ℓ} (QᵢΦ)·(Σ_{j≠i} Pⱼ(QᵢΦ)) = Σ_{p ∈ pairSet N} ∫_{abox N ℓ} (P_{p.1}(Q_{p.2}Φ))² .

## Math

Both sides are the same object.  For a single ordered pair `i ≠ j` the FS box projection `Pⱼ` is
an orthogonal projection of `L²(abox N ℓ)`, hence

    ∫ (Pⱼ(QᵢΦ))² = ∫ (QᵢΦ)·Pⱼ(QᵢΦ)                                    (`n0Sum_pInd_sq_selfMul`),

and therefore

    Σᵢ ∫ QᵢΦ·(Σ_{j≠i} Pⱼ(QᵢΦ)) = Σᵢ Σ_{j≠i} ∫ (Pⱼ(QᵢΦ))²
                              = Σ_{p ∈ pairSet N} ∫ (P_{p.1}(Q_{p.2}Φ))² ,

the last step being the Finset reindexing `Σᵢ Σ_{j≠i} G j i = Σ_{p ∈ pairSet N} G p.1 p.2`
(the map `(i,j) ↦ (j,i)` is an involution of the ordered distinct-pair set).

The projection identity is `boxPIndSelfAdjoint` (`∫ PᵢΦ·Ψ = ∫ Φ·PᵢΨ`) followed by the pointwise
idempotence `boxPInd_idempotent` of `Pᵢ`; the finitely many sums are exchanged with the integral
via `MeasureTheory.integral_finset_sum`, all integrands being bounded measurable on the compact
box.
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators ENNReal

namespace Work.BoseFixB1S

open Submission.BoseGases

set_option maxHeartbeats 1500000
set_option linter.unusedVariables false

/-! ## 1. Combinatorial helpers -/

/-- The swap of the double sum over the pairs `i ≠ j`, in the orientation `(i,j) ↦ (j,i)`. -/
theorem n0Sum_sum_erase_comm {N : ℕ} (A : Fin N → Fin N → ℝ) :
    (∑ j : Fin N, ∑ i ∈ (Finset.univ : Finset (Fin N)).erase j, A i j)
      = ∑ i : Fin N, ∑ j ∈ (Finset.univ : Finset (Fin N)).erase i, A i j := by
  have h1 : ∀ j : Fin N, (∑ i ∈ (Finset.univ : Finset (Fin N)).erase j, A i j)
      = (∑ i : Fin N, A i j) - A j j := by
    intro j
    rw [← Finset.sum_erase_add (Finset.univ : Finset (Fin N)) (fun i => A i j)
      (Finset.mem_univ j)]
    ring
  have h2 : ∀ i : Fin N, (∑ j ∈ (Finset.univ : Finset (Fin N)).erase i, A i j)
      = (∑ j : Fin N, A i j) - A i i := by
    intro i
    rw [← Finset.sum_erase_add (Finset.univ : Finset (Fin N)) (fun j => A i j)
      (Finset.mem_univ i)]
    ring
  rw [Finset.sum_congr rfl (fun j _ => h1 j), Finset.sum_congr rfl (fun i _ => h2 i),
    Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_comm]

/-- The iterated `j ≠ i` sum is the `pairSet N` sum (`pairSet N` being the ordered pairs of
distinct indices, the sets `{i} × (univ.erase i)` partition it). -/
theorem n0Sum_erase_eq_pairSet {N : ℕ} (f : Fin N → Fin N → ℝ) :
    (∑ i : Fin N, ∑ j ∈ (Finset.univ : Finset (Fin N)).erase i, f i j)
      = ∑ p ∈ Submission.BoseGases.pairSet N, f p.1 p.2 := by
  rw [Submission.BoseGases.pairSet, Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.filter_ne' Finset.univ i, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  by_cases h : i = j
  · subst h; simp
  · simp [h, Ne.symm h]

/-- **The reindexing identity.**  For any `F`, the sum over the ordered distinct pairs `(a,b)` of
`F a b` equals the iterated sum `Σᵢ Σ_{j≠i} F j i`. -/
theorem n0Sum_pairSet_swap {N : ℕ} (F : Fin N → Fin N → ℝ) :
    (∑ p ∈ Submission.BoseGases.pairSet N, F p.1 p.2)
      = ∑ i : Fin N, ∑ j ∈ Finset.univ.erase i, F j i := by
  calc (∑ p ∈ Submission.BoseGases.pairSet N, F p.1 p.2)
      = ∑ i : Fin N, ∑ j ∈ (Finset.univ : Finset (Fin N)).erase i, F i j :=
        (n0Sum_erase_eq_pairSet (fun a b => F a b)).symm
    _ = ∑ j : Fin N, ∑ i ∈ (Finset.univ : Finset (Fin N)).erase j, F i j :=
        (n0Sum_sum_erase_comm (fun a b => F a b)).symm
    _ = ∑ i : Fin N, ∑ j ∈ Finset.univ.erase i, F j i := rfl

/-! ## 2. Measurability and boundedness of the FS box projections -/

/-- `QᵢΨ = 1_A(·ᵢ)·Ψ − PᵢΨ` is measurable for measurable `Ψ`. -/
theorem n0Sum_measurable_boxQInd {N : ℕ} (volA : ℝ)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A) (i : Fin N)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦ : Measurable Φ) :
    Measurable (Work.UBBInputs8.boxQInd volA A i Φ) := by
  have hσ : Measurable (fun x : Submission.BoseGases.X N =>
      A.indicator (fun _ => (1 : ℝ)) (x i)) :=
    (measurable_const.indicator hA).comp (measurable_pi_apply i)
  have hP : Measurable (Work.UBBInputs8.boxPInd volA A i Φ) :=
    measurable_boxPInd volA A hA i hΦ
  unfold Work.UBBInputs8.boxQInd
  exact (hσ.mul hΦ).sub hP

/-- `|QᵢΦ| ≤ 2C` on the box whenever `|Φ| ≤ C` there. -/
theorem n0Sum_abs_boxQInd_le {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) (i : Fin N)
    {Φ : Submission.BoseGases.X N → ℝ} {C : ℝ}
    (hC : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Φ x| ≤ C) :
    ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |Work.UBBInputs8.boxQInd volA A i Φ x| ≤ 2 * C := by
  intro x hx
  have hσ : |A.indicator (fun _ => (1 : ℝ)) (x i)| ≤ 1 := by
    by_cases h : x i ∈ A <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]
  have h1 : |A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x| ≤ C := by
    rw [abs_mul]
    calc |A.indicator (fun _ => (1 : ℝ)) (x i)| * |Φ x| ≤ 1 * C :=
          mul_le_mul hσ (hC x hx) (abs_nonneg _) zero_le_one
      _ = C := one_mul C
  have h2 : |Work.UBBInputs8.boxPInd volA A i Φ x| ≤ C :=
    abs_boxPInd_le hℓ hvol hA hvolA hAc i hC x hx
  have h3 : Work.UBBInputs8.boxQInd volA A i Φ x
      = A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x
        - Work.UBBInputs8.boxPInd volA A i Φ x := rfl
  rw [h3]
  calc |A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x
          - Work.UBBInputs8.boxPInd volA A i Φ x|
      ≤ |A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x|
          + |Work.UBBInputs8.boxPInd volA A i Φ x| := abs_sub _ _
    _ ≤ C + C := add_le_add h1 h2
    _ = 2 * C := by ring

/-! ## 3. The `L²` self-product of the box projection -/

/-- **`Pᵢ` is an orthogonal projection of `L²(abox N ℓ)`**: for measurable `Ψ` bounded on the box,

    ∫_{abox N ℓ} (PᵢΨ)² = ∫_{abox N ℓ} Ψ·(PᵢΨ) .

(`boxPIndSelfAdjoint` with the second argument `PᵢΨ`, followed by the pointwise idempotence
`boxPInd_idempotent`.) -/
theorem n0Sum_pInd_sq_selfMul {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) (i : Fin N)
    {Ψ : Submission.BoseGases.X N → ℝ} (hΨm : Measurable Ψ) {C : ℝ}
    (hΨb : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Ψ x| ≤ C) :
    (∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxPInd volA A i Ψ x) ^ 2)
      = ∫ x in Submission.BoseGases.abox N ℓ,
          Ψ x * Work.UBBInputs8.boxPInd volA A i Ψ x := by
  have hPm : Measurable (Work.UBBInputs8.boxPInd volA A i Ψ) :=
    measurable_boxPInd volA A hA i hΨm
  have hPb : ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |Work.UBBInputs8.boxPInd volA A i Ψ x| ≤ C :=
    abs_boxPInd_le hℓ hvol hA hvolA hAc i hΨb
  have hSA := boxPIndSelfAdjoint (N := N) (ℓ := ℓ) (volA := volA) hℓ hvol hA hvolA hAc i
    hΨm hΨb hPm hPb
  rw [show (fun x : Submission.BoseGases.X N => (Work.UBBInputs8.boxPInd volA A i Ψ x) ^ 2)
      = fun x : Submission.BoseGases.X N => Work.UBBInputs8.boxPInd volA A i Ψ x
          * Work.UBBInputs8.boxPInd volA A i Ψ x from funext (fun x => by ring)]
  rw [hSA]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  rw [boxPInd_idempotent hℓ hvol hA hvolA hAc i Ψ x]

/-! ## 4. The main identity -/

theorem n0SumAqEqX {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) :
    (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxQInd volA A i Φ x)
          * (∑ j ∈ Finset.univ.erase i,
              Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x))
      = ∑ p ∈ Submission.BoseGases.pairSet N, ∫ x in Submission.BoseGases.abox N ℓ,
          (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x) ^ 2 := by
  obtain ⟨C, _hC0, hCb⟩ := exists_abox_bound (N := N) hℓ hΦc
  have hQm : ∀ i : Fin N, Measurable (Work.UBBInputs8.boxQInd volA A i Φ) :=
    fun i => n0Sum_measurable_boxQInd volA hA i hΦc.measurable
  have hQb : ∀ i : Fin N, ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |Work.UBBInputs8.boxQInd volA A i Φ x| ≤ 2 * C :=
    fun i x hx => n0Sum_abs_boxQInd_le hℓ hvol hA hvolA hAc i hCb x hx
  -- step 1: pull the `j`-sum out of the integral and use the projection identity
  have hstep : ∀ i : Fin N,
      (∫ x in Submission.BoseGases.abox N ℓ,
          Work.UBBInputs8.boxQInd volA A i Φ x
            * (∑ j ∈ Finset.univ.erase i,
                Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x))
        = ∑ j ∈ Finset.univ.erase i,
            ∫ x in Submission.BoseGases.abox N ℓ,
              (Work.UBBInputs8.boxPInd volA A j
                (Work.UBBInputs8.boxQInd volA A i Φ) x) ^ 2 := by
    intro i
    have hpoint : (fun x : Submission.BoseGases.X N =>
          Work.UBBInputs8.boxQInd volA A i Φ x
            * (∑ j ∈ Finset.univ.erase i,
                Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x))
        = fun x : Submission.BoseGases.X N => ∑ j ∈ Finset.univ.erase i,
            Work.UBBInputs8.boxQInd volA A i Φ x
              * Work.UBBInputs8.boxPInd volA A j
                  (Work.UBBInputs8.boxQInd volA A i Φ) x := by
      funext x
      rw [Finset.mul_sum]
    have hInt : ∀ j ∈ Finset.univ.erase i,
        Integrable (fun x : Submission.BoseGases.X N =>
            Work.UBBInputs8.boxQInd volA A i Φ x
              * Work.UBBInputs8.boxPInd volA A j
                  (Work.UBBInputs8.boxQInd volA A i Φ) x)
          (MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)) := by
      intro j _
      exact integrableOn_mul_of_bound hℓ (hQm i)
        (measurable_boxPInd volA A hA j (hQm i)) (hQb i)
        (fun x hx => abs_boxPInd_le hℓ hvol hA hvolA hAc j (hQb i) x hx)
    rw [hpoint, MeasureTheory.integral_finsetSum _ hInt]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    exact (n0Sum_pInd_sq_selfMul (N := N) (ℓ := ℓ) (volA := volA) hℓ hvol hA hvolA hAc j
      (hQm i) (hQb i)).symm
  rw [Finset.sum_congr rfl (fun i _ => hstep i)]
  exact (n0Sum_pairSet_swap (N := N) (fun a b =>
    ∫ x in Submission.BoseGases.abox N ℓ,
      (Work.UBBInputs8.boxPInd volA A a (Work.UBBInputs8.boxQInd volA A b Φ) x) ^ 2)).symm

end Work.BoseFixB1S
