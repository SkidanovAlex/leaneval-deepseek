import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB1.integrable_sbKin
import Submission.Work.BoseFixB1.measurable_tBamp_boxQInd_pair
import Submission.Work.BoseFixB1.perSectorBoundG
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1

open MeasureTheory
open scoped BigOperators

set_option maxHeartbeats 1000000

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The pointwise Parseval identity (no integrability hypotheses)

`Work.FockBridge.sum_tBamp_normSq` carries the `Integrable` side conditions of the fibre kernels,
which are needed only for the *interchange* of the integral with the finite sum in its consumer.
The identity itself is pointwise, and it is the identity we need at *every* `p`, so it is reproved
here in the unconditional form. -/

/-- **The squared windowed amplitude of `Q_{A,i}Φ` is the sum of those of its sector pieces.**
Pointwise in `x`: the amplitude samples the state only on the slot-`i` fibre over `supp χ ⊆ A`, and
replacing slot `i` by a point of `A` shifts the `A`-occupancy to
`if x i ∈ A then n_A(x) else n_A(x)+1`, so exactly the corresponding sector piece survives. -/
private theorem sum_tBamp_normSq_sectorPiece {n : ℕ} {A : Set E3} (hA : MeasurableSet A)
    {χ : E3 → ℝ} (hχ : ∀ z : E3, χ z ≠ 0 → z ∈ A) {volA : ℝ} (i : Fin n)
    {Φ : Submission.BoseGases.X n → ℝ} (p : E3) (x : Submission.BoseGases.X n) :
    ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA A i Φ) i x‖ ^ 2
      = ∑ k ∈ Finset.range (n + 1),
          ‖Work.SmallBoxTBWord.tBamp χ p
            (Work.UBBInputs8.boxQInd volA A i
              (Work.FockBridge.sectorPiece A k Φ)) i x‖ ^ 2 := by
  classical
  set k0 : ℕ := (if x i ∈ A then Work.FockBridge.boxOccupancy A x
    else Work.FockBridge.boxOccupancy A x + 1) with hk0
  have hxk0 : x ∈ Work.FockBridge.ampSector A i k0 :=
    (Work.FockBridge.mem_ampSector_iff A i k0 x).mpr hk0.symm
  have hk0mem : k0 ∈ Finset.range (n + 1) :=
    Finset.mem_range.mpr
      (Nat.lt_succ_of_le (Work.FockBridge.ampShift_le A i hxk0))
  have hB : Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA A i Φ) i x
      = Work.SmallBoxTBWord.tBamp χ p
          (Work.UBBInputs8.boxQInd volA A i (Work.FockBridge.sectorPiece A k0 Φ)) i x := by
    refine Work.FockBridge.tBamp_congr_of_eqOn_fibre χ hχ p i (fun z hz => ?_)
    have hocc : Work.FockBridge.boxOccupancy A (Function.update x i z) = k0 :=
      (Work.FockBridge.boxOccupancy_update_of_mem A x i hz).trans hk0.symm
    exact Work.FockBridge.boxQInd_sectorPiece_eq_of_mem (A := A) (volA := volA) hA i
      ((Work.FockBridge.mem_sectorSet_iff A k0 (Function.update x i z)).mpr hocc)
  have hzero : ∀ k ∈ Finset.range (n + 1), k ≠ k0 →
      ‖Work.SmallBoxTBWord.tBamp χ p
        (Work.UBBInputs8.boxQInd volA A i (Work.FockBridge.sectorPiece A k Φ)) i x‖ ^ 2 = 0 := by
    intro k _ hne
    have hxnot : x ∉ Work.FockBridge.ampSector A i k := by
      intro hmem
      rw [Work.FockBridge.mem_ampSector_iff] at hmem
      exact hne (hmem.symm.trans hk0.symm)
    have h0 : Work.SmallBoxTBWord.tBamp χ p
        (Work.UBBInputs8.boxQInd volA A i (Work.FockBridge.sectorPiece A k Φ)) i x = 0 :=
      Work.FockBridge.tBamp_eq_zero_of_notMem_ampSector hχ p
        (fun y hy => Work.FockBridge.boxQInd_sectorPiece_eq_zero hA i hy) i hxnot
    rw [h0]
    simp
  rw [hB, Finset.sum_eq_single k0 hzero (fun hnot => absurd hk0mem hnot)]

/-! ## 2. Uniform rapid decay of the sector piece's amplitude -/

/-- **The windowed amplitude of the `Q_{B(u),i}`-projection of a count-sector piece decays
uniformly like `(1+‖p‖)⁻³`**, with the *same* constant as the decay
`Work.BoseFixB1.tBamp_chiB_boxQInd_decay` of the whole state.

The sector piece is dominated by the whole state through the pointwise Parseval identity of §1
(at most one summand survives and it equals the whole amplitude); for `k > n` the sector is empty
and the amplitude vanishes. -/
private lemma norm_tBamp_sectorPiece_le {n : ℕ} {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u : E3) {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ENat) Φ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (p : E3) (x : Submission.BoseGases.X n),
        x ∈ Submission.BoseGases.abox n ℓ → ∀ (i : Fin n) (k : ℕ),
        ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiB ℓ d u) p
          (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) i
            (Work.FockBridge.sectorPiece (Submission.BoseGases.dlBox ℓ d u) k Φ)) i x‖
          ≤ C / (1 + ‖p‖) ^ 3 := by
  obtain ⟨C, hC0, hdec⟩ := tBamp_chiB_boxQInd_decay (n := n) hℓ hd hΦ
  refine ⟨C, hC0, fun p x hx i k => ?_⟩
  have hA : MeasurableSet (Submission.BoseGases.dlBox ℓ d u) :=
    Work.SmallBoxSliding.measurableSet_dlBox ℓ d u
  have hχ : ∀ z : E3, Submission.BoseGases.chiB ℓ d u z ≠ 0 →
      z ∈ Submission.BoseGases.dlBox ℓ d u :=
    fun z hz => Work.UBBInputs9.A.tsupport_chiB_subset_dlBox hℓ hd u (subset_tsupport _ hz)
  by_cases hk : k ∈ Finset.range (n + 1)
  · -- the sector piece is one summand of the whole state's Parseval decomposition
    have hsum := sum_tBamp_normSq_sectorPiece (A := Submission.BoseGases.dlBox ℓ d u)
      (volA := Work.SmallBoxSliding.boxMass ℓ d u) (Φ := Φ) hA hχ i p x
    have h1 : ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiB ℓ d u) p
          (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) i
            (Work.FockBridge.sectorPiece (Submission.BoseGases.dlBox ℓ d u) k Φ)) i x‖ ^ 2
        ≤ ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiB ℓ d u) p
            (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) i Φ) i x‖ ^ 2 := by
      rw [hsum]
      refine Finset.single_le_sum (fun j _ => sq_nonneg (‖Work.SmallBoxTBWord.tBamp
        (Submission.BoseGases.chiB ℓ d u) p
        (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
          (Submission.BoseGases.dlBox ℓ d u) i
          (Work.FockBridge.sectorPiece (Submission.BoseGases.dlBox ℓ d u) j Φ)) i x‖)) hk
    have h2 : ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiB ℓ d u) p
        (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
          (Submission.BoseGases.dlBox ℓ d u) i Φ) i x‖ ≤ C / (1 + ‖p‖) ^ 3 := hdec u x hx i p
    have h3 : ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiB ℓ d u) p
          (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) i
            (Work.FockBridge.sectorPiece (Submission.BoseGases.dlBox ℓ d u) k Φ)) i x‖ ^ 2
        ≤ (C / (1 + ‖p‖) ^ 3) ^ 2 := le_trans h1 (pow_le_pow_left₀ (norm_nonneg _) h2 2)
    have hb : (0 : ℝ) ≤ C / (1 + ‖p‖) ^ 3 := div_nonneg hC0 (by positivity)
    have h4 := sq_le_sq.mp h3
    rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hb] at h4
  · -- an empty sector: the piece vanishes identically
    have hkn : n < k := by
      rw [Finset.mem_range, not_lt] at hk
      omega
    have hemp : Work.FockBridge.sectorPiece (Submission.BoseGases.dlBox ℓ d u) k Φ = 0 := by
      funext y
      simp only [Work.FockBridge.sectorPiece]
      rw [Work.FockBridge.sectorSet_eq_empty_of_lt (N := n)
        (Submission.BoseGases.dlBox ℓ d u) hkn]
      simp
    rw [hemp]
    have h0 : Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
        (Submission.BoseGases.dlBox ℓ d u) i (0 : Submission.BoseGases.X n → ℝ) = 0 := by
      funext y
      simp [Work.UBBInputs8.boxQInd, Work.UBBInputs8.boxPInd]
    rw [h0]
    have h1 : Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiB ℓ d u) p
        (0 : Submission.BoseGases.X n → ℝ) i x = 0 := by
      unfold Work.SmallBoxTBWord.tBamp
      simp
    rw [h1, norm_zero]
    exact div_nonneg hC0 (by positivity)

/-! ## 3. The target -/

theorem integrable_prod_ampEnergy_sectorPiece {n : ℕ} {ℓ d c : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u : EuclideanSpace ℝ (Fin 3)) {Φ : Submission.BoseGases.X n → ℝ}
    (hΦ : ContDiff ℝ (⊤ : ENat) Φ) (i : Fin n) (k : ℕ) :
    MeasureTheory.Integrable (fun q : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n =>
      Submission.BoseGases.fsKinCoeff c ‖q.1‖ * ((ℓ ^ 3)⁻¹ *
        ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiB ℓ d u) q.1
          (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) i
            (Work.FockBridge.sectorPiece (Submission.BoseGases.dlBox ℓ d u) k Φ)) i q.2‖ ^ 2))
      ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
        ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
          (Submission.BoseGases.abox n ℓ)))
    := by
  classical
  obtain ⟨C, hC0, hdec⟩ := norm_tBamp_sectorPiece_le hℓ hd u hΦ
  -- the second factor of the product is a *finite* measure (the box `abox n ℓ` is bounded)
  haveI hfin : IsFiniteMeasure
      ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
        (Submission.BoseGases.abox n ℓ)) := by
    rw [Submission.BoseGases.restrict_abox_eq_pi]
    infer_instance
  -- the dominating profile: constant in `x`, integrable in `p`
  have hg : MeasureTheory.Integrable
      (fun q : E3 × Submission.BoseGases.X n =>
        (ℓ ^ 3)⁻¹ * (Submission.BoseGases.fsKinCoeff c ‖q.1‖ * (C / (1 + ‖q.1‖) ^ 3) ^ 2))
      ((MeasureTheory.volume : MeasureTheory.Measure E3).prod
        ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
          (Submission.BoseGases.abox n ℓ))) :=
    ((Work.SlotWord.integrable_fsKinCoeff_decay c C).const_mul ((ℓ ^ 3)⁻¹)).comp_fst _
  refine hg.mono' ?_ ?_
  · -- joint measurability in the pair `(p, x)`
    have hmsq : Measurable (fun q : E3 × Submission.BoseGases.X n =>
        ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiB ℓ d u) q.1
          (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) i
            (Work.FockBridge.sectorPiece (Submission.BoseGases.dlBox ℓ d u) k Φ)) i q.2‖ ^ 2) :=
      Work.BoseFixB1.measurable_tBamp_boxQInd_pair
        (A := Submission.BoseGases.dlBox ℓ d u)
        (hA := Work.SmallBoxSliding.measurableSet_dlBox ℓ d u)
        (χ := Submission.BoseGases.chiB ℓ d u)
        (hχ := (Work.SmallBoxTBWord.contDiff_chiB hℓ hd u).continuous)
        (volA := Work.SmallBoxSliding.boxMass ℓ d u)
        (Ψ := Work.FockBridge.sectorPiece (Submission.BoseGases.dlBox ℓ d u) k Φ)
        (hΨ := hΦ.continuous.measurable.indicator
          (Work.FockBridge.sectorSet_measurable _
            (Work.SmallBoxSliding.measurableSet_dlBox ℓ d u) k))
        (i := i)
    have hcoef : Continuous (fun q : E3 × Submission.BoseGases.X n =>
        Submission.BoseGases.fsKinCoeff c ‖q.1‖) := by
      rw [show (fun q : E3 × Submission.BoseGases.X n =>
            Submission.BoseGases.fsKinCoeff c ‖q.1‖)
          = (fun r : ℝ => (max (r - c) 0) ^ 2) ∘
              (fun q : E3 × Submission.BoseGases.X n => ‖q.1‖) from rfl]
      exact (((continuous_id.sub continuous_const).max continuous_const).pow 2).comp
        (continuous_norm.comp continuous_fst)
    exact ((hcoef.measurable.mul (hmsq.const_mul _)).aestronglyMeasurable).mono_measure
      (MeasureTheory.Measure.prod_mono le_rfl MeasureTheory.Measure.restrict_le_self)
  · -- pointwise domination on the box, hence a.e. for the product measure
    have hprod : (MeasureTheory.volume : MeasureTheory.Measure E3).prod
        ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
          (Submission.BoseGases.abox n ℓ))
        = ((MeasureTheory.volume : MeasureTheory.Measure E3).prod
            (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n))).restrict
          (Set.univ ×ˢ Submission.BoseGases.abox n ℓ) := by
      rw [← MeasureTheory.Measure.prod_restrict (Set.univ : Set E3)
        (Submission.BoseGases.abox n ℓ), MeasureTheory.Measure.restrict_univ]
    rw [hprod, MeasureTheory.ae_restrict_iff'
      (MeasurableSet.univ.prod (Submission.BoseGases.abox_measurable n ℓ))]
    refine Filter.Eventually.of_forall (fun q hq => ?_)
    have hx : q.2 ∈ Submission.BoseGases.abox n ℓ := (Set.mem_prod.mp hq).2
    have hfs : 0 ≤ Submission.BoseGases.fsKinCoeff c ‖q.1‖ :=
      Submission.BoseGases.fsKinCoeff_nonneg c ‖q.1‖
    have hl3 : (0 : ℝ) < (ℓ ^ 3)⁻¹ := inv_pos.mpr (pow_pos hℓ 3)
    have hsq : ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiB ℓ d u) q.1
          (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) i
            (Work.FockBridge.sectorPiece (Submission.BoseGases.dlBox ℓ d u) k Φ)) i q.2‖ ^ 2
        ≤ (C / (1 + ‖q.1‖) ^ 3) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hdec q.1 q.2 hx i k) 2
    have hfnn : 0 ≤ Submission.BoseGases.fsKinCoeff c ‖q.1‖ *
        ((ℓ ^ 3)⁻¹ * ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiB ℓ d u) q.1
          (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) i
            (Work.FockBridge.sectorPiece (Submission.BoseGases.dlBox ℓ d u) k Φ)) i q.2‖ ^ 2) :=
      mul_nonneg hfs (mul_nonneg hl3.le (sq_nonneg _))
    rw [Real.norm_of_nonneg hfnn]
    calc Submission.BoseGases.fsKinCoeff c ‖q.1‖ *
          ((ℓ ^ 3)⁻¹ * ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiB ℓ d u) q.1
            (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) i
              (Work.FockBridge.sectorPiece (Submission.BoseGases.dlBox ℓ d u) k Φ)) i q.2‖ ^ 2)
        ≤ Submission.BoseGases.fsKinCoeff c ‖q.1‖ *
            ((ℓ ^ 3)⁻¹ * (C / (1 + ‖q.1‖) ^ 3) ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq hl3.le) hfs
      _ = (ℓ ^ 3)⁻¹ *
            (Submission.BoseGases.fsKinCoeff c ‖q.1‖ * (C / (1 + ‖q.1‖) ^ 3) ^ 2) := by ring

end Work.BoseFixB1
