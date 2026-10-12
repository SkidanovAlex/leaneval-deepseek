import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1B.SliceVocab
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1B.cnPlusBoxInd_slice_split`

The FS-faithful excited-particle count `cnPlusBoxInd ℓ A V Ψ = Σᵢ ∫_{abox N ℓ} (Q_{A,i}Ψ)²`
(FS `eq:HBU`, `Work.UBBInputs8.boxQInd`) is a **sum of one-slot operators**, hence it splits
over the block decomposition `N = N₁ + N₂` of the particle number:

    cnPlusBoxInd ℓ A V Φ
      = ∫_{w ∈ abox N₂ ℓ} cnPlusBoxInd ℓ A V (fun u ↦ Φ (merge(u,w)))
      + ∫_{u ∈ abox N₁ ℓ} cnPlusBoxInd ℓ A V (fun w ↦ Φ (merge(u,w)))

for every continuous `Φ` on the box `X (N₁+N₂)` — with **no** hypothesis on the box side `ℓ`,
on the box `A` or on the reference volume `V`.  The target statement of this file is the case
`A = dlBox ℓ d u₀`.

## Proof

*For `0 < ℓ`* one proves the general statement `cns_split_gen` for an arbitrary measurable
`A ⊆ acube ℓ`:

* the box projection is a one-slot operator and `Function.update` commutes with the block
  concatenation (`mergeBlock_eq`, `firstBlock_update`, `lastBlock_update_first`, …), whence on a
  merged configuration `merge(u,w)` the projection in slot `Fin.castAdd N₂ j` of the *first*
  block equals the projection in slot `j` of the slice `u' ↦ Φ(merge(u',w))`
  (`cns_split_boxQInd_merge_castAdd`, and the `Fin.natAdd`-analogue for the second block);
* splitting the index set of the sum with `Fin.sum_univ_add` and pushing the sum through the
  integral (`integral_finsetSum`) turns the count into an integral over the full box of a sum of
  one-slot terms; Fubini for the measure-preserving block split (`aboxFubini`,
  `aboxFubini_swapped`) turns that into the iterated integral; finally the inner sum is pushed
  back through the inner integral and the two block integrals are recognised as the two slice
  counts (definitionally).
* The integrability inputs of the two Fubini/swap steps are supplied by the `L∞`-bound of the box
  projection `Work.SlotWord.abs_boxQInd_le_of_bound` (the state is bounded by `sup |Φ|` on the
  compact box, and the box mean is a mean of values of `Φ` inside the box), via
  `cns_split_integrableOn_boxQInd_sq_gen` and its slice versions.

*For `ℓ ≤ 0`* the analysis box `abox N ℓ` is null for `N ≥ 1` (`abox N ℓ ⊆ abox N 0` and
`volume (abox N 0) = 0`, since `0³ = 0`), so every slot integral — and with it the count — is
zero (`cns_split_cnPlusBoxInd_eq_zero_of_nonpos`); the same nullity kills the outer integrals of
the right-hand side, and the remaining corner case (`N₁ = 0` or `N₂ = 0`, where the box is a
point) has an identically vanishing integrand.
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators ENNReal

open Submission.BoseGases

namespace Work.BoseFixB1B

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1000000

/-! ## 1. The degenerate box `ℓ ≤ 0` -/

/-- For `ℓ ≤ 0` the analysis box `abox N ℓ` is null as soon as `N ≥ 1`: it is contained in
`abox N 0`, and `volume (abox N 0) = (0³)^N = 0`. -/
lemma cns_split_abox_volume_zero_of_nonpos {N : ℕ} {ℓ : ℝ} (hℓ : ℓ ≤ 0) (hN : 0 < N) :
    (volume : Measure (X N)) (abox N ℓ) = 0 := by
  have hsub : abox N ℓ ⊆ abox N 0 := by
    intro x hx
    simp only [mem_abox_iff, mem_acube_iff] at hx ⊢
    intro i m
    have hm := hx i m
    constructor <;> linarith [hm.1, hm.2]
  have h0 : (volume : Measure (X N)) (abox N 0) = 0 := by
    rw [abox_volume N 0 le_rfl]
    have : ((0 : ℝ) ^ 3) ^ N = 0 := by
      rw [zero_pow (by norm_num : (3 : ℕ) ≠ 0), zero_pow hN.ne']
    rw [this, ENNReal.ofReal_zero]
  exact measure_mono_null hsub h0

/-- On a degenerate box (`ℓ ≤ 0`) the box excited-particle count vanishes identically. -/
lemma cns_split_cnPlusBoxInd_eq_zero_of_nonpos {N : ℕ} {ℓ V : ℝ} (hℓ : ℓ ≤ 0) {A : Set E3}
    (Ψ : X N → ℝ) : Work.UBBInputs8.cnPlusBoxInd ℓ A V Ψ = 0 := by
  unfold Work.UBBInputs8.cnPlusBoxInd
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp
  · exact Finset.sum_eq_zero (fun i _ =>
      setIntegral_measure_zero _ (cns_split_abox_volume_zero_of_nonpos hℓ hN))

/-! ## 2. The box projection is a one-slot operator -/

/-- Updating slot `j` of the first block commutes with the block concatenation. -/
lemma cns_split_update_castAdd {N1 N2 : ℕ} (u : X N1) (w : X N2) (j : Fin N1) (z : E3) :
    Function.update (mergeBlock N1 N2 (u, w)) (Fin.castAdd N2 j) z
      = mergeBlock N1 N2 (Function.update u j z, w) := by
  rw [← mergeBlock_eq N1 N2 (Function.update (mergeBlock N1 N2 (u, w)) (Fin.castAdd N2 j) z)]
  simp [firstBlock_update, lastBlock_update_first, mergeBlock_first, mergeBlock_last]

/-- Updating slot `j` of the second block commutes with the block concatenation. -/
lemma cns_split_update_natAdd {N1 N2 : ℕ} (u : X N1) (w : X N2) (j : Fin N2) (z : E3) :
    Function.update (mergeBlock N1 N2 (u, w)) (Fin.natAdd N1 j) z
      = mergeBlock N1 N2 (u, Function.update w j z) := by
  rw [← mergeBlock_eq N1 N2 (Function.update (mergeBlock N1 N2 (u, w)) (Fin.natAdd N1 j) z)]
  simp [firstBlock_update_last, lastBlock_update_last, mergeBlock_first, mergeBlock_last]

/-- FS's `Q_{B,i}` is a one-slot operator: on a merged configuration the projection in slot
`Fin.castAdd N₂ j` of the first block is the projection in slot `j` of the `w`-slice. -/
lemma cns_split_boxQInd_merge_castAdd {N1 N2 : ℕ} {V : ℝ} {A : Set E3}
    (Φ : X (N1 + N2) → ℝ) (j : Fin N1) (u : X N1) (w : X N2) :
    Work.UBBInputs8.boxQInd V A (Fin.castAdd N2 j) Φ (mergeBlock N1 N2 (u, w))
      = Work.UBBInputs8.boxQInd V A j (fun u' => Φ (mergeBlock N1 N2 (u', w))) u := by
  have h1 : mergeBlock N1 N2 (u, w) (Fin.castAdd N2 j) = u j := by simp [mergeBlock]
  have h2 : (∫ z in A, Φ (Function.update (mergeBlock N1 N2 (u, w)) (Fin.castAdd N2 j) z))
      = ∫ z in A, (fun u' => Φ (mergeBlock N1 N2 (u', w))) (Function.update u j z) := by
    apply integral_congr_ae
    filter_upwards with z
    rw [cns_split_update_castAdd]
  simp only [Work.UBBInputs8.boxQInd, Work.UBBInputs8.boxPInd, h1, h2]

/-- The `Fin.natAdd`-analogue of `cns_split_boxQInd_merge_castAdd` for the second block. -/
lemma cns_split_boxQInd_merge_natAdd {N1 N2 : ℕ} {V : ℝ} {A : Set E3}
    (Φ : X (N1 + N2) → ℝ) (j : Fin N2) (u : X N1) (w : X N2) :
    Work.UBBInputs8.boxQInd V A (Fin.natAdd N1 j) Φ (mergeBlock N1 N2 (u, w))
      = Work.UBBInputs8.boxQInd V A j (fun w' => Φ (mergeBlock N1 N2 (u, w'))) w := by
  have h1 : mergeBlock N1 N2 (u, w) (Fin.natAdd N1 j) = w j := by simp [mergeBlock]
  have h2 : (∫ z in A, Φ (Function.update (mergeBlock N1 N2 (u, w)) (Fin.natAdd N1 j) z))
      = ∫ z in A, (fun w' => Φ (mergeBlock N1 N2 (u, w'))) (Function.update w j z) := by
    apply integral_congr_ae
    filter_upwards with z
    rw [cns_split_update_natAdd]
  simp only [Work.UBBInputs8.boxQInd, Work.UBBInputs8.boxPInd, h1, h2]

/-! ## 3. Merging, boxes and the small box `B(u) = dlBox ℓ d u₀` -/

/-- The block concatenation of two box configurations is a box configuration. -/
lemma cns_split_mergeBlock_mem_abox {N1 N2 : ℕ} {ℓ : ℝ} {u : X N1} {w : X N2}
    (hu : u ∈ abox N1 ℓ) (hw : w ∈ abox N2 ℓ) : mergeBlock N1 N2 (u, w) ∈ abox (N1 + N2) ℓ := by
  rw [mem_abox_split, mergeBlock_first, mergeBlock_last]
  exact ⟨hu, hw⟩

/-- Freezing the second block is continuous. -/
lemma cns_split_continuous_mergeBlock_fst {N1 N2 : ℕ} (w : X N2) :
    Continuous (fun u' : X N1 => mergeBlock N1 N2 (u', w)) := by
  rw [continuous_pi_iff]
  intro k
  rcases hk : finSplit N1 N2 k with i | j
  · simp only [mergeBlock, hk, Sum.elim_inl]
    exact continuous_apply i
  · simp only [mergeBlock, hk, Sum.elim_inr]
    exact continuous_const

/-- Freezing the first block is continuous. -/
lemma cns_split_continuous_mergeBlock_snd {N1 N2 : ℕ} (u : X N1) :
    Continuous (fun w' : X N2 => mergeBlock N1 N2 (u, w')) := by
  rw [continuous_pi_iff]
  intro k
  rcases hk : finSplit N1 N2 k with i | j
  · simp only [mergeBlock, hk, Sum.elim_inl]
    exact continuous_const
  · simp only [mergeBlock, hk, Sum.elim_inr]
    exact continuous_apply j

/-- The small box `B(u₀) = dlBox ℓ d u₀` is measurable. -/
lemma cns_split_dlBox_measurable (ℓ d : ℝ) (u₀ : E3) : MeasurableSet (dlBox ℓ d u₀) := by
  have h : dlBox ℓ d u₀ = acube ℓ ∩ (fun x : E3 => x - (ℓ * d) • u₀) ⁻¹' acube (ℓ * d) := by
    ext x
    rw [mem_dlBox_iff]
    trivial
  rw [h]
  exact (acube_measurable ℓ).inter ((acube_measurable (ℓ * d)).preimage (by fun_prop))

/-- The small box `dlBox ℓ d u₀` sits inside the analysis cube `acube ℓ`. -/
lemma cns_split_dlBox_subset (ℓ d : ℝ) (u₀ : E3) : dlBox ℓ d u₀ ⊆ acube ℓ :=
  fun _ hx => (mem_dlBox_iff ℓ d u₀ _).mp hx |>.1

/-! ## 4. Integrability of the squared box projections -/

/-- `IntegrableOn (abox N ℓ)` of `(Q_{A,i}Φ)²`, for `0 < ℓ`, a measurable box `A ⊆ acube ℓ`,
and a state that is measurable and bounded by `C` on the box. -/
lemma cns_split_integrableOn_boxQInd_sq_gen {N : ℕ} {ℓ V C : ℝ} (hℓ : 0 < ℓ) {A : Set E3}
    (hA : MeasurableSet A) (hAc : A ⊆ acube ℓ)
    {Φ : X N → ℝ} (hΦm : Measurable Φ) (hC0 : 0 ≤ C)
    (hCb : ∀ x ∈ abox N ℓ, |Φ x| ≤ C) (i : Fin N) :
    IntegrableOn (fun x => (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2) (abox N ℓ) := by
  have hfin : volume A < ⊤ := lt_of_le_of_lt (measure_mono hAc) (acube_lt_top ℓ hℓ.le)
  have hb : ∀ x : X N, (∀ j : Fin N, x j ∈ acube ℓ) →
      |Work.UBBInputs8.boxQInd V A i Φ x| ≤ C + |V|⁻¹ * (C * volume.real A) :=
    Work.SlotWord.abs_boxQInd_le_of_bound ℓ hAc hC0 hfin (fun x hx => hCb x hx) i
  set K : ℝ := C + |V|⁻¹ * (C * volume.real A) with hK
  have hK0 : 0 ≤ K := by
    rw [hK]
    have h1 : 0 ≤ (volume : Measure E3).real A := measureReal_nonneg
    have h2 : 0 ≤ |V|⁻¹ := inv_nonneg.mpr (abs_nonneg V)
    exact add_nonneg hC0 (mul_nonneg h2 (mul_nonneg hC0 h1))
  have haesm : AEStronglyMeasurable (fun x : X N => (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2)
      ((volume : Measure (X N)).restrict (abox N ℓ)) :=
    ((Work.SlotWord.measurable_boxQInd V A hA i hΦm).pow_const 2).aestronglyMeasurable
  refine IntegrableOn.of_bound (abox_lt_top N ℓ hℓ.le) haesm (K ^ 2) ?_
  filter_upwards [ae_restrict_mem (abox_measurable N ℓ)] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (hb x hx) 2

/-- Slice version of the integrability: the inner integrand of the first block is integrable
for every `w` in the second block's box. -/
lemma cns_split_sliceIntegrable_fst {N1 N2 : ℕ} {ℓ V C : ℝ} (hℓ : 0 < ℓ) {A : Set E3}
    (hA : MeasurableSet A) (hAc : A ⊆ acube ℓ) {Φ : X (N1 + N2) → ℝ} (hΦm : Measurable Φ)
    (hC0 : 0 ≤ C) (hCb : ∀ x ∈ abox (N1 + N2) ℓ, |Φ x| ≤ C) (w : X N2) (hw : w ∈ abox N2 ℓ)
    (j : Fin N1) :
    IntegrableOn (fun u : X N1 =>
      (Work.UBBInputs8.boxQInd V A j (fun u' => Φ (mergeBlock N1 N2 (u', w))) u) ^ 2)
      (abox N1 ℓ) :=
  cns_split_integrableOn_boxQInd_sq_gen (N := N1) hℓ hA hAc
    (hΦm.comp (cns_split_continuous_mergeBlock_fst (N1 := N1) (N2 := N2) w).measurable)
    hC0 (fun u hu => hCb (mergeBlock N1 N2 (u, w)) (cns_split_mergeBlock_mem_abox hu hw)) j

/-- Slice version of the integrability for the second block. -/
lemma cns_split_sliceIntegrable_snd {N1 N2 : ℕ} {ℓ V C : ℝ} (hℓ : 0 < ℓ) {A : Set E3}
    (hA : MeasurableSet A) (hAc : A ⊆ acube ℓ) {Φ : X (N1 + N2) → ℝ} (hΦm : Measurable Φ)
    (hC0 : 0 ≤ C) (hCb : ∀ x ∈ abox (N1 + N2) ℓ, |Φ x| ≤ C) (u : X N1) (hu : u ∈ abox N1 ℓ)
    (j : Fin N2) :
    IntegrableOn (fun w : X N2 =>
      (Work.UBBInputs8.boxQInd V A j (fun w' => Φ (mergeBlock N1 N2 (u, w'))) w) ^ 2)
      (abox N2 ℓ) :=
  cns_split_integrableOn_boxQInd_sq_gen (N := N2) hℓ hA hAc
    (hΦm.comp (cns_split_continuous_mergeBlock_snd (N1 := N1) (N2 := N2) u).measurable)
    hC0 (fun w hw => hCb (mergeBlock N1 N2 (u, w)) (cns_split_mergeBlock_mem_abox hu hw)) j

/-! ## 5. The block split of the box excited-particle count on a genuine box -/

theorem cns_split_gen {N1 N2 : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) {A : Set E3}
    (hA : MeasurableSet A) (hAc : A ⊆ acube ℓ)
    {Φ : X (N1 + N2) → ℝ} (hΦ : Continuous Φ) :
    Work.UBBInputs8.cnPlusBoxInd ℓ A V Φ
      = (∫ w in abox N2 ℓ, Work.UBBInputs8.cnPlusBoxInd ℓ A V
            (fun y => Φ (mergeBlock N1 N2 (y, w))))
        + (∫ y in abox N1 ℓ, Work.UBBInputs8.cnPlusBoxInd ℓ A V
            (fun w => Φ (mergeBlock N1 N2 (y, w)))) := by
  obtain ⟨C, hCb⟩ := (abox_compact (N1 + N2) hℓ).exists_bound_of_continuousOn
    (s := abox (N1 + N2) ℓ) (f := Φ) hΦ.continuousOn
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hCb _ (zero_mem_abox hℓ.le))
  have hCab : ∀ x ∈ abox (N1 + N2) ℓ, |Φ x| ≤ C := fun x hx => by
    simpa [Real.norm_eq_abs] using hCb x hx
  have hInt : ∀ i : Fin (N1 + N2), IntegrableOn
      (fun x => (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2) (abox (N1 + N2) ℓ) :=
    fun i => cns_split_integrableOn_boxQInd_sq_gen hℓ hA hAc hΦ.measurable hC0 hCab i
  have hA1 : (∑ j : Fin N1, ∫ x in abox (N1 + N2) ℓ,
        (Work.UBBInputs8.boxQInd V A (Fin.castAdd N2 j) Φ x) ^ 2)
      = ∫ w in abox N2 ℓ, Work.UBBInputs8.cnPlusBoxInd ℓ A V
          (fun y => Φ (mergeBlock N1 N2 (y, w))) := by
    have hsum : IntegrableOn (fun x : X (N1 + N2) =>
        ∑ j : Fin N1, (Work.UBBInputs8.boxQInd V A (Fin.castAdd N2 j) Φ x) ^ 2)
        (abox (N1 + N2) ℓ) :=
      integrable_finsetSum Finset.univ (fun j _ => hInt (Fin.castAdd N2 j))
    calc (∑ j : Fin N1, ∫ x in abox (N1 + N2) ℓ,
            (Work.UBBInputs8.boxQInd V A (Fin.castAdd N2 j) Φ x) ^ 2)
        = ∫ x in abox (N1 + N2) ℓ,
            ∑ j : Fin N1, (Work.UBBInputs8.boxQInd V A (Fin.castAdd N2 j) Φ x) ^ 2 :=
          (integral_finsetSum Finset.univ (f := fun j (x : X (N1 + N2)) =>
            (Work.UBBInputs8.boxQInd V A (Fin.castAdd N2 j) Φ x) ^ 2)
            (fun j _ => hInt (Fin.castAdd N2 j))).symm
      _ = ∫ w in abox N2 ℓ, ∫ u in abox N1 ℓ,
            ∑ j : Fin N1, (Work.UBBInputs8.boxQInd V A (Fin.castAdd N2 j) Φ
              (mergeBlock N1 N2 (u, w))) ^ 2 :=
          (aboxFubini_swapped ℓ _ hsum).symm
      _ = ∫ w in abox N2 ℓ, ∫ u in abox N1 ℓ,
            ∑ j : Fin N1, (Work.UBBInputs8.boxQInd V A j
              (fun u' => Φ (mergeBlock N1 N2 (u', w))) u) ^ 2 := by
          apply integral_congr_ae
          filter_upwards with w
          apply integral_congr_ae
          filter_upwards with u
          exact Finset.sum_congr rfl (fun j _ => by rw [cns_split_boxQInd_merge_castAdd])
      _ = ∫ w in abox N2 ℓ, ∑ j : Fin N1, ∫ u in abox N1 ℓ,
            (Work.UBBInputs8.boxQInd V A j
              (fun u' => Φ (mergeBlock N1 N2 (u', w))) u) ^ 2 := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem (abox_measurable N2 ℓ)] with w hw
          exact integral_finsetSum Finset.univ
            (f := fun j (u : X N1) => (Work.UBBInputs8.boxQInd V A j
              (fun u' => Φ (mergeBlock N1 N2 (u', w))) u) ^ 2)
            (fun j _ => cns_split_sliceIntegrable_fst hℓ hA hAc hΦ.measurable hC0 hCab w hw j)
      _ = ∫ w in abox N2 ℓ, Work.UBBInputs8.cnPlusBoxInd ℓ A V
            (fun y => Φ (mergeBlock N1 N2 (y, w))) := rfl
  have hA2 : (∑ j : Fin N2, ∫ x in abox (N1 + N2) ℓ,
        (Work.UBBInputs8.boxQInd V A (Fin.natAdd N1 j) Φ x) ^ 2)
      = ∫ y in abox N1 ℓ, Work.UBBInputs8.cnPlusBoxInd ℓ A V
          (fun w => Φ (mergeBlock N1 N2 (y, w))) := by
    have hsum : IntegrableOn (fun x : X (N1 + N2) =>
        ∑ j : Fin N2, (Work.UBBInputs8.boxQInd V A (Fin.natAdd N1 j) Φ x) ^ 2)
        (abox (N1 + N2) ℓ) :=
      integrable_finsetSum Finset.univ (fun j _ => hInt (Fin.natAdd N1 j))
    calc (∑ j : Fin N2, ∫ x in abox (N1 + N2) ℓ,
            (Work.UBBInputs8.boxQInd V A (Fin.natAdd N1 j) Φ x) ^ 2)
        = ∫ x in abox (N1 + N2) ℓ,
            ∑ j : Fin N2, (Work.UBBInputs8.boxQInd V A (Fin.natAdd N1 j) Φ x) ^ 2 :=
          (integral_finsetSum Finset.univ (f := fun j (x : X (N1 + N2)) =>
            (Work.UBBInputs8.boxQInd V A (Fin.natAdd N1 j) Φ x) ^ 2)
            (fun j _ => hInt (Fin.natAdd N1 j))).symm
      _ = ∫ y in abox N1 ℓ, ∫ w in abox N2 ℓ,
            ∑ j : Fin N2, (Work.UBBInputs8.boxQInd V A (Fin.natAdd N1 j) Φ
              (mergeBlock N1 N2 (y, w))) ^ 2 :=
          (aboxFubini ℓ _ hsum).symm
      _ = ∫ y in abox N1 ℓ, ∫ w in abox N2 ℓ,
            ∑ j : Fin N2, (Work.UBBInputs8.boxQInd V A j
              (fun w' => Φ (mergeBlock N1 N2 (y, w'))) w) ^ 2 := by
          apply integral_congr_ae
          filter_upwards with y
          apply integral_congr_ae
          filter_upwards with w
          exact Finset.sum_congr rfl (fun j _ => by rw [cns_split_boxQInd_merge_natAdd])
      _ = ∫ y in abox N1 ℓ, ∑ j : Fin N2, ∫ w in abox N2 ℓ,
            (Work.UBBInputs8.boxQInd V A j
              (fun w' => Φ (mergeBlock N1 N2 (y, w'))) w) ^ 2 := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem (abox_measurable N1 ℓ)] with y hy
          exact integral_finsetSum Finset.univ
            (f := fun j (w : X N2) => (Work.UBBInputs8.boxQInd V A j
              (fun w' => Φ (mergeBlock N1 N2 (y, w'))) w) ^ 2)
            (fun j _ => cns_split_sliceIntegrable_snd hℓ hA hAc hΦ.measurable hC0 hCab y hy j)
      _ = ∫ y in abox N1 ℓ, Work.UBBInputs8.cnPlusBoxInd ℓ A V
            (fun w => Φ (mergeBlock N1 N2 (y, w))) := rfl
  calc Work.UBBInputs8.cnPlusBoxInd ℓ A V Φ
      = ∑ i : Fin (N1 + N2), ∫ x in abox (N1 + N2) ℓ,
          (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2 := rfl
    _ = (∑ j : Fin N1, ∫ x in abox (N1 + N2) ℓ,
          (Work.UBBInputs8.boxQInd V A (Fin.castAdd N2 j) Φ x) ^ 2)
        + (∑ j : Fin N2, ∫ x in abox (N1 + N2) ℓ,
          (Work.UBBInputs8.boxQInd V A (Fin.natAdd N1 j) Φ x) ^ 2) := Fin.sum_univ_add _
    _ = _ + _ := by rw [hA1, hA2]

/-! ## 6. The target -/

theorem cnPlusBoxInd_slice_split {N1 N2 : ℕ} {ℓ d V : ℝ} (u₀ : EuclideanSpace ℝ (Fin 3))
    {Φ : Submission.BoseGases.X (N1 + N2) → ℝ} (hΦ : Continuous Φ) :
    Work.UBBInputs8.cnPlusBoxInd ℓ (Submission.BoseGases.dlBox ℓ d u₀) V Φ
      = (∫ w in Submission.BoseGases.abox N2 ℓ,
            Work.UBBInputs8.cnPlusBoxInd ℓ (Submission.BoseGases.dlBox ℓ d u₀) V
              (fun y => Φ (Submission.BoseGases.mergeBlock N1 N2 (y, w))))
        + (∫ y in Submission.BoseGases.abox N1 ℓ,
            Work.UBBInputs8.cnPlusBoxInd ℓ (Submission.BoseGases.dlBox ℓ d u₀) V
              (fun w => Φ (Submission.BoseGases.mergeBlock N1 N2 (y, w)))) := by
  by_cases hℓ : 0 < ℓ
  · exact cns_split_gen hℓ (cns_split_dlBox_measurable ℓ d u₀) (cns_split_dlBox_subset ℓ d u₀) hΦ
  · have hℓ0 : ℓ ≤ 0 := le_of_not_gt hℓ
    have hL : Work.UBBInputs8.cnPlusBoxInd ℓ (dlBox ℓ d u₀) V Φ = 0 :=
      cns_split_cnPlusBoxInd_eq_zero_of_nonpos hℓ0 Φ
    have hR1 : (∫ w in abox N2 ℓ, Work.UBBInputs8.cnPlusBoxInd ℓ (dlBox ℓ d u₀) V
        (fun y => Φ (mergeBlock N1 N2 (y, w)))) = 0 := by
      rcases Nat.eq_zero_or_pos N2 with hN2 | hN2
      · have h1 : (fun w : X N2 => Work.UBBInputs8.cnPlusBoxInd ℓ (dlBox ℓ d u₀) V
            (fun y => Φ (mergeBlock N1 N2 (y, w)))) = fun _ => (0 : ℝ) := by
          funext w
          exact cns_split_cnPlusBoxInd_eq_zero_of_nonpos hℓ0 _
        rw [h1, integral_zero]
      · exact setIntegral_measure_zero _ (cns_split_abox_volume_zero_of_nonpos hℓ0 hN2)
    have hR2 : (∫ y in abox N1 ℓ, Work.UBBInputs8.cnPlusBoxInd ℓ (dlBox ℓ d u₀) V
        (fun w => Φ (mergeBlock N1 N2 (y, w)))) = 0 := by
      rcases Nat.eq_zero_or_pos N1 with hN1 | hN1
      · have h1 : (fun y : X N1 => Work.UBBInputs8.cnPlusBoxInd ℓ (dlBox ℓ d u₀) V
            (fun w => Φ (mergeBlock N1 N2 (y, w)))) = fun _ => (0 : ℝ) := by
          funext y
          exact cns_split_cnPlusBoxInd_eq_zero_of_nonpos hℓ0 _
        rw [h1, integral_zero]
      · exact setIntegral_measure_zero _ (cns_split_abox_volume_zero_of_nonpos hℓ0 hN1)
    rw [hL, hR1, hR2, add_zero]

end Work.BoseFixB1B
