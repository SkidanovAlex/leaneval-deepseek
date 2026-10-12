import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB1Cube.ConeC.BoseFixB1_SectorPiece_boxMuSum_sectorPiece
import Submission.Work.BoseB1Cube.ConeC.BoseFixB1_SectorPiece_fragIntegrable_sectorPiece
import Submission.Work.BoseB1Cube.ConeC.BoseFixB1_SectorPiece_pairFrags_sum_eq
import Submission.Work.BoseFixB1.BddSector.pairMixedBdd
import Submission.Work.BoseFixB1.BddSector.parsevalBdd
import Submission.Work.BoseFixB1.BddSector.regimeBdd
import Submission.Work.BoseFixB1.SectorPiece.pairInts_eq_integral_pairFrags
import Submission.Work.BoseFixB1S.sectorPassageB1Support
import Submission.Work.BoseFixR.qLHSwordSplitAe
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding Work.FockBridge

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-! ## 3. The `boxQ0` value at a sector piece -/

/-- **`Q₀`'s exact value at a sector piece.**  Both the two-slot peel
(`Work.BoseFixB1S.boxPairValue`, junk-tolerant but requiring the pair kernel to be integrable on
`B × B`) and the one-slot peel (`Work.BoseFixB1.oneValueAnyB1`, entirely unconditional) hold for
*arbitrary* states, so this needs no regularity of the sector piece at all. -/
theorem boxQ0_sectorPiece {N : ℕ} {ℓ d μ : ℝ} {v : ℝ³ → ℝ} (h : Work.UBB.ScatSol v)
    {M : ℕ} (hM : 1 ≤ M) (u : ℝ³) (k : ℕ) (Φ : Submission.BoseGases.X N → ℝ)
    (hℓ : 0 < ℓ) (hvol : 0 < boxMass ℓ d u)
    (hw2i : MeasureTheory.IntegrableOn
      (fun q : ℝ³ × ℝ³ => wSmallPair M ℓ d u (g2 v h) q.1 q.2)
      (dlBox ℓ d u ×ˢ dlBox ℓ d u)) :
    Work.BoseFixB1S.boxQ0 (boxMass ℓ d u) ℓ μ (dlBox ℓ d u) (wSmall1Pair h M ℓ d u)
        (wSmallPair M ℓ d u (g2 v h)) (sectorPiece (dlBox ℓ d u) k Φ)
      = (1 / 2) * (Work.BoseFixB1S.boxM2 (boxMass ℓ d u) (dlBox ℓ d u) (wSmallPair M ℓ d u (g2 v h))
            / (boxMass ℓ d u) ^ 2)
          * Work.BoseFixB1S.boxPairCount (boxMass ℓ d u) ℓ (dlBox ℓ d u) (sectorPiece (dlBox ℓ d u) k Φ)
        - μ * (Work.BoseFixB1S.boxM1 ℓ (dlBox ℓ d u) (wSmall1Pair h M ℓ d u) / boxMass ℓ d u)
            * Work.BoseFixB1S.boxFlatCount (boxMass ℓ d u) ℓ (dlBox ℓ d u) (sectorPiece (dlBox ℓ d u) k Φ) := by
  have hA : MeasurableSet (dlBox ℓ d u) := Work.SmallBoxSliding.measurableSet_dlBox ℓ d u
  have hvolA : boxMass ℓ d u = (MeasureTheory.volume (dlBox ℓ d u)).toReal := by
    rw [Work.SmallBoxSliding.boxMass_eq_measureReal, MeasureTheory.Measure.real_def]
  have hAc : dlBox ℓ d u ⊆ acube ℓ := Work.SmallBoxSliding.dlBox_subset_acube ℓ d u
  have hpair := Work.BoseFixB1S.boxPairValue (n := N) (ℓ := ℓ) (d := d) hℓ u
    (sectorPiece (dlBox ℓ d u) k Φ) hw2i
  have hone : ∀ i : Fin N,
      (∫ x in abox N ℓ,
          (Work.UBBInputs8.boxPInd (boxMass ℓ d u) (dlBox ℓ d u) i
            (sectorPiece (dlBox ℓ d u) k Φ) x) ^ 2
            * w1Fibre ℓ (wSmall1Pair h M ℓ d u) (x i))
        = (Work.BoseFixB1S.boxM1 ℓ (dlBox ℓ d u) (wSmall1Pair h M ℓ d u) / boxMass ℓ d u)
          * (∫ x in abox N ℓ,
              (Work.UBBInputs8.boxPInd (boxMass ℓ d u) (dlBox ℓ d u) i
                (sectorPiece (dlBox ℓ d u) k Φ) x) ^ 2) :=
    fun i => Work.BoseFixB1.oneValueAnyB1 (volA := boxMass ℓ d u) hℓ hvol hA hvolA hAc
  rw [Work.BoseFixB1S.boxQ0, Work.BoseFixB1S.boxPairCount, Work.BoseFixB1S.boxFlatCount,
    Work.BoseFixB1S.boxM2, hpair, Finset.sum_congr rfl (fun i _ => hone i), ← Finset.mul_sum]
  ring

/-! ## 4. Regularity of a sector piece, and the one-slot peel at bounded regularity -/

/-- A sector piece of a measurable state is measurable. -/
theorem sectorPiece_measurable {N : ℕ} {A : Set ℝ³} (hA : MeasurableSet A) (k : ℕ)
    {Φ : Submission.BoseGases.X N → ℝ} (hm : Measurable Φ) :
    Measurable (sectorPiece A k Φ) :=
  hm.indicator (Work.FockBridge.sectorSet_measurable A hA k)

/-- A sector piece inherits the box bound of the state. -/
theorem sectorPiece_bound {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {A : Set ℝ³} (k : ℕ)
    {Φ : Submission.BoseGases.X N → ℝ} {B : ℝ} (hb : ∀ x ∈ abox N ℓ, |Φ x| ≤ B) :
    ∀ x ∈ abox N ℓ, |sectorPiece A k Φ x| ≤ B := by
  have hB0 : 0 ≤ B := le_trans (abs_nonneg (Φ 0)) (hb 0 (zero_mem_abox hℓ.le))
  intro x hx
  rw [Work.FockBridge.sectorPiece]
  by_cases hxs : x ∈ Work.FockBridge.sectorSet A k
  · rw [Set.indicator_of_mem hxs]; exact hb x hx
  · rw [Set.indicator_of_notMem hxs]; simpa using hB0

/-- **The one-slot peel at measurable/bounded regularity**: `∫ Φ·PᵢΦ = ∫ (PᵢΦ)²`.  This is
`Work.BoseFixB1S.Q0C.one_self_N` with `Continuous Φ` replaced by `Measurable Φ` plus a bound on
the box; the proof is the corpus's (self-adjointness `boxPInd_adjoint_int` + idempotence
`boxPInd_self_idem`). -/
theorem oneSelfBdd {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set ℝ³} (hA : MeasurableSet A) (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) (i : Fin N)
    {Φ : Submission.BoseGases.X N → ℝ} (hm : Measurable Φ) {B : ℝ}
    (hb : ∀ x ∈ abox N ℓ, |Φ x| ≤ B) :
    (∫ x in abox N ℓ, Φ x * Work.UBBInputs8.boxPInd volA A i Φ x)
      = ∫ x in abox N ℓ, (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2 := by
  have hB0 : 0 ≤ B := le_trans (abs_nonneg (Φ 0)) (hb 0 (zero_mem_abox hℓ.le))
  have hPm : Measurable (Work.UBBInputs8.boxPInd volA A i Φ) :=
    Work.BoseFixB1S.measurable_boxPInd volA A hA i hm
  have hPb : ∀ x ∈ abox N ℓ, |Work.UBBInputs8.boxPInd volA A i Φ x| ≤ B :=
    Work.BoseFixB1S.abs_boxPInd_le hℓ hvol hA hvolA hAc i hb
  have hPint : IntegrableOn (Work.UBBInputs8.boxPInd volA A i Φ) (abox N ℓ) volume :=
    IntegrableOn.of_bound (abox_lt_top N ℓ hℓ.le) hPm.aestronglyMeasurable B
      ((ae_restrict_iff' (abox_measurable N ℓ)).mpr (Filter.Eventually.of_forall
        (fun x hx => by rw [Real.norm_eq_abs]; exact hPb x hx)))
  have hadj := Work.BoseFixB1.boxPInd_adjoint_int (N := N) (ℓ := ℓ) (V := volA) hℓ hvol
    (A := A) hA hvolA hAc i (f := Φ) (h := Work.UBBInputs8.boxPInd volA A i Φ)
    hm hB0 hb hPm hPint
  simp only [sq]
  rw [hadj]
  apply integral_congr_ae
  filter_upwards with x
  rw [Work.BoseFixB1.boxPInd_self_idem hvol hA hvolA i Φ]

/-! ## 5. The count identity `n₀ + n₊ = k·‖ψ‖²` at a sector piece -/

/-- **`n₀ + n₊ = k·‖ψ‖²` at a sector piece.**  The per-slot Parseval splitting
(`Work.BoseFixB1.BddSector.parsevalBdd`, proved at measurable/bounded regularity) summed over the
slots, and then the sector condition collapses `Σᵢ1_A(xᵢ)·ψ²` to `k·ψ²` (as in
`Work.BoseFixB1B.boxFlat_add_boxQ_eq_card`, whose `Continuous` hypothesis is replaced here by the
weaker measurable/bounded one). -/
theorem boxFlat_add_boxQCount_sectorPiece {N : ℕ} {ℓ : ℝ} {V : ℝ} {A : Set ℝ³}
    (hℓ : 0 < ℓ) (hvol : 0 < V) (hA : MeasurableSet A)
    (hvolA : V = (MeasureTheory.volume A).toReal) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {k : ℕ} {Φ : Submission.BoseGases.X N → ℝ} (hm : Measurable Φ) {B : ℝ}
    (hb : ∀ x ∈ abox N ℓ, |Φ x| ≤ B) :
    Work.BoseFixB1S.boxFlatCount V ℓ A (sectorPiece A k Φ)
      + Work.BoseFixB1S.boxQCount V ℓ A (sectorPiece A k Φ)
      = (k : ℝ) * ∫ x in abox N ℓ, (sectorPiece A k Φ x) ^ 2 := by
  have hB0 : 0 ≤ B := le_trans (abs_nonneg (Φ 0)) (hb 0 (zero_mem_abox hℓ.le))
  have hψm : Measurable (sectorPiece A k Φ) := sectorPiece_measurable hA k hm
  have hψb : ∀ x ∈ abox N ℓ, |sectorPiece A k Φ x| ≤ B := sectorPiece_bound hℓ k hb
  have hsum : Work.BoseFixB1S.boxFlatCount V ℓ A (sectorPiece A k Φ)
      + Work.BoseFixB1S.boxQCount V ℓ A (sectorPiece A k Φ)
      = ∑ i : Fin N, ∫ x in abox N ℓ,
          A.indicator (fun _ => (1 : ℝ)) (x i) * (sectorPiece A k Φ x) ^ 2 := by
    rw [Work.BoseFixB1S.boxFlatCount, Work.BoseFixB1S.boxQCount, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ =>
      Work.BoseFixB1.BddSector.parsevalBdd hℓ hvol hA hvolA hAc i hψm hψb)
  rw [hsum]
  have hint : ∀ i : Fin N, IntegrableOn (fun x : Submission.BoseGases.X N =>
      A.indicator (fun _ => (1 : ℝ)) (x i) * (sectorPiece A k Φ x) ^ 2) (abox N ℓ) volume := by
    intro i
    refine Work.BoseFixB1S.integrableOn_mul_of_bound (Cf := 1) (Cg := B ^ 2) hℓ
      ((measurable_const.indicator hA).comp (measurable_pi_apply i)) (hψm.pow_const 2)
      ?_ ?_
    · intro x hx
      by_cases h : x i ∈ A <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]
    · intro x hx
      have h1 : |sectorPiece A k Φ x| ^ 2 ≤ B ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) (hψb x hx) 2
      rwa [abs_of_nonneg (sq_nonneg _), ← sq_abs]
  rw [← MeasureTheory.integral_finsetSum Finset.univ (fun i _ => hint i)]
  have hpt : ∀ x : Submission.BoseGases.X N,
      (∑ i : Fin N, A.indicator (fun _ => (1 : ℝ)) (x i) * (sectorPiece A k Φ x) ^ 2)
        = (k : ℝ) * (sectorPiece A k Φ x) ^ 2 := by
    intro x
    rw [← Finset.sum_mul, ← Work.FockBridge.boxCount_eq_sum_indicator A x]
    by_cases hx : x ∈ Work.FockBridge.sectorSet A k
    · rw [Work.FockBridge.boxCount_eq_of_mem_sectorSet A hx]
    · have hz : sectorPiece A k Φ x = 0 := by
        rw [Work.FockBridge.sectorPiece]
        exact Set.indicator_of_notMem hx Φ
      rw [hz]; ring
  rw [show (fun x : Submission.BoseGases.X N =>
        ∑ i : Fin N, A.indicator (fun _ => (1 : ℝ)) (x i) * (sectorPiece A k Φ x) ^ 2)
      = fun x => (k : ℝ) * (sectorPiece A k Φ x) ^ 2 from funext hpt,
    MeasureTheory.integral_const_mul]

/-! ## 6. Jensen (the flat-count variance bound) at a sector piece -/

/-- **`S² − S·I ≤ I·T` at a sector piece** (FS's Jensen step at the box projections): the flat
count `S = boxFlatCount`, the mass `I = ‖ψ‖²` and the pair count `T = boxPairCount` satisfy the
Cauchy–Schwarz bound.  The proof is the corpus's (`Λ = ΣᵢPᵢψ`, `S = ∫ψΛψ`,
`∫(Λψ)² = S + T`, then Cauchy–Schwarz), at measurable/bounded regularity: `S = ∫ψ·Λψ` via the
one-slot peel and `∫(Λψ)² = S + T` via `Work.BoseFixB1.BddSector.pairMixedBdd`. -/
theorem boxFlatSqJensen_sectorPiece {N : ℕ} {ℓ : ℝ} {V : ℝ} {A : Set ℝ³}
    (hℓ : 0 < ℓ) (hvol : 0 < V) (hA : MeasurableSet A)
    (hvolA : V = (MeasureTheory.volume A).toReal) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {k : ℕ} {Φ : Submission.BoseGases.X N → ℝ} (hm : Measurable Φ) {B : ℝ}
    (hb : ∀ x ∈ abox N ℓ, |Φ x| ≤ B) :
    Work.BoseFixB1S.boxFlatCount V ℓ A (sectorPiece A k Φ) ^ 2
      - Work.BoseFixB1S.boxFlatCount V ℓ A (sectorPiece A k Φ)
        * (∫ x in abox N ℓ, (sectorPiece A k Φ x) ^ 2)
      ≤ (∫ x in abox N ℓ, (sectorPiece A k Φ x) ^ 2)
        * Work.BoseFixB1S.boxPairCount V ℓ A (sectorPiece A k Φ) := by
  classical
  haveI hfin : IsFiniteMeasure ((volume : Measure (Submission.BoseGases.X N)).restrict
      (abox N ℓ)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact abox_lt_top N ℓ hℓ.le⟩
  have hB0 : 0 ≤ B := le_trans (abs_nonneg (Φ 0)) (hb 0 (zero_mem_abox hℓ.le))
  have hψm : Measurable (sectorPiece A k Φ) := sectorPiece_measurable hA k hm
  have hψb : ∀ x ∈ abox N ℓ, |sectorPiece A k Φ x| ≤ B := sectorPiece_bound hℓ k hb
  have hPm : ∀ i : Fin N, Measurable (Work.UBBInputs8.boxPInd V A i (sectorPiece A k Φ)) :=
    fun i => Work.BoseFixB1S.measurable_boxPInd V A hA i hψm
  have hPb : ∀ i : Fin N, ∀ x ∈ abox N ℓ,
      |Work.UBBInputs8.boxPInd V A i (sectorPiece A k Φ) x| ≤ B :=
    fun i x hx => Work.BoseFixB1S.abs_boxPInd_le hℓ hvol hA hvolA hAc i hψb x hx
  -- the one-slot peel `∫ψ·Pᵢψ = ∫(Pᵢψ)²`
  have hbase : ∀ i : Fin N,
      (∫ x in abox N ℓ,
          (sectorPiece A k Φ) x * Work.UBBInputs8.boxPInd V A i (sectorPiece A k Φ) x)
        = ∫ x in abox N ℓ, (Work.UBBInputs8.boxPInd V A i (sectorPiece A k Φ) x) ^ 2 :=
    fun i => oneSelfBdd hℓ hvol hA hvolA hAc i hψm hψb
  -- the flat sum `Λψ = ΣᵢPᵢψ`
  set Λ : Submission.BoseGases.X N → ℝ :=
    fun x => ∑ i : Fin N, Work.UBBInputs8.boxPInd V A i (sectorPiece A k Φ) x with hΛ
  have hΛm : Measurable Λ := by
    rw [hΛ]; exact Finset.measurable_sum _ (fun i _ => hPm i)
  have hΛb : ∀ x ∈ abox N ℓ, |Λ x| ≤ (N : ℝ) * B := by
    intro x hx
    rw [hΛ]
    calc |∑ i : Fin N, Work.UBBInputs8.boxPInd V A i (sectorPiece A k Φ) x|
        ≤ ∑ i : Fin N, |Work.UBBInputs8.boxPInd V A i (sectorPiece A k Φ) x| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin N, B := Finset.sum_le_sum (fun i _ => hPb i x hx)
      _ = (N : ℝ) * B := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- `S = ∫ψ·Λψ`
  have hS : Work.BoseFixB1S.boxFlatCount V ℓ A (sectorPiece A k Φ)
      = ∫ x in abox N ℓ, (sectorPiece A k Φ) x * Λ x := by
    have h1 : Work.BoseFixB1S.boxFlatCount V ℓ A (sectorPiece A k Φ)
        = ∑ i : Fin N, ∫ x in abox N ℓ,
            (sectorPiece A k Φ) x * Work.UBBInputs8.boxPInd V A i (sectorPiece A k Φ) x := by
      rw [Work.BoseFixB1S.boxFlatCount]
      exact Finset.sum_congr rfl (fun i _ => (hbase i).symm)
    rw [h1, ← MeasureTheory.integral_finsetSum Finset.univ (fun i _ =>
      Work.BoseFixB1S.integrableOn_mul_of_bound hℓ hψm (hPm i) hψb (hPb i))]
    rw [hΛ]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    rw [← Finset.mul_sum]
  -- `∫(Λψ)² = S + T`
  have hΛsq : (∫ x in abox N ℓ, (Λ x) ^ 2)
      = Work.BoseFixB1S.boxFlatCount V ℓ A (sectorPiece A k Φ)
        + Work.BoseFixB1S.boxPairCount V ℓ A (sectorPiece A k Φ) := by
    have hint : ∀ i j : Fin N, IntegrableOn (fun x : Submission.BoseGases.X N =>
        Work.UBBInputs8.boxPInd V A i (sectorPiece A k Φ) x
          * Work.UBBInputs8.boxPInd V A j (sectorPiece A k Φ) x) (abox N ℓ) volume :=
      fun i j => Work.BoseFixB1S.integrableOn_mul_of_bound hℓ (hPm i) (hPm j) (hPb i) (hPb j)
    have step1 : (∫ x in abox N ℓ, (Λ x) ^ 2)
        = ∑ i : Fin N, ∑ j : Fin N, ∫ x in abox N ℓ,
            Work.UBBInputs8.boxPInd V A i (sectorPiece A k Φ) x
              * Work.UBBInputs8.boxPInd V A j (sectorPiece A k Φ) x := by
      rw [show (∫ x in abox N ℓ, (Λ x) ^ 2)
          = ∫ x in abox N ℓ, ∑ i : Fin N, ∑ j : Fin N,
              Work.UBBInputs8.boxPInd V A i (sectorPiece A k Φ) x
                * Work.UBBInputs8.boxPInd V A j (sectorPiece A k Φ) x from by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with x
        rw [hΛ, sq, Finset.sum_mul_sum]]
      rw [MeasureTheory.integral_finsetSum Finset.univ (fun i _ => ?_)]
      · exact Finset.sum_congr rfl (fun i _ =>
          MeasureTheory.integral_finsetSum Finset.univ (fun j _ => hint i j))
      · exact integrable_finsetSum _ (fun j _ => by simpa [IntegrableOn] using hint i j)
    have step2 : (∑ i : Fin N, ∑ j : Fin N, ∫ x in abox N ℓ,
            Work.UBBInputs8.boxPInd V A i (sectorPiece A k Φ) x
              * Work.UBBInputs8.boxPInd V A j (sectorPiece A k Φ) x)
        = (∑ i : Fin N, ∫ x in abox N ℓ,
              Work.UBBInputs8.boxPInd V A i (sectorPiece A k Φ) x
                * Work.UBBInputs8.boxPInd V A i (sectorPiece A k Φ) x)
          + ∑ p ∈ Submission.BoseGases.pairSet N, ∫ x in abox N ℓ,
              Work.UBBInputs8.boxPInd V A p.1 (sectorPiece A k Φ) x
                * Work.UBBInputs8.boxPInd V A p.2 (sectorPiece A k Φ) x :=
      Work.BoseFixB1S.Q0C.sum_univ_univ_eq _
    have step3 : (∑ i : Fin N, ∫ x in abox N ℓ,
            Work.UBBInputs8.boxPInd V A i (sectorPiece A k Φ) x
              * Work.UBBInputs8.boxPInd V A i (sectorPiece A k Φ) x)
        = Work.BoseFixB1S.boxFlatCount V ℓ A (sectorPiece A k Φ) := by
      rw [Work.BoseFixB1S.boxFlatCount]
      exact Finset.sum_congr rfl (fun i _ => by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with x
        rw [pow_two])
    have step4 : (∑ p ∈ Submission.BoseGases.pairSet N, ∫ x in abox N ℓ,
            Work.UBBInputs8.boxPInd V A p.1 (sectorPiece A k Φ) x
              * Work.UBBInputs8.boxPInd V A p.2 (sectorPiece A k Φ) x)
        = Work.BoseFixB1S.boxPairCount V ℓ A (sectorPiece A k Φ) := by
      rw [Work.BoseFixB1S.boxPairCount]
      refine Finset.sum_congr rfl (fun p hp => ?_)
      have hne : p.1 ≠ p.2 := by
        simpa only [Submission.BoseGases.pairSet, Finset.mem_filter, Finset.mem_univ,
          true_and] using hp
      rw [Work.BoseFixB1.BddSector.pairMixedBdd hℓ hvol hA hvolA hAc hne hψm hψb]
    rw [step1, step2, step3, step4]
  -- Cauchy–Schwarz
  have hCS := Work.BoseFixB1S.Q0C.integral_mul_sq_le
    (μ := (volume : Measure (Submission.BoseGases.X N)).restrict (abox N ℓ))
    hψm.aestronglyMeasurable hΛm.aestronglyMeasurable (Cf := B) (Cg := (N : ℝ) * B)
    ((ae_restrict_iff' (abox_measurable N ℓ)).mpr
      (Filter.Eventually.of_forall (fun x hx => hψb x hx)))
    ((ae_restrict_iff' (abox_measurable N ℓ)).mpr
      (Filter.Eventually.of_forall (fun x hx => hΛb x hx)))
  have hmain : Work.BoseFixB1S.boxFlatCount V ℓ A (sectorPiece A k Φ) ^ 2
      ≤ (∫ x in abox N ℓ, (sectorPiece A k Φ x) ^ 2)
        * (Work.BoseFixB1S.boxFlatCount V ℓ A (sectorPiece A k Φ)
            + Work.BoseFixB1S.boxPairCount V ℓ A (sectorPiece A k Φ)) := by
    rw [← hΛsq, hS]
    exact hCS
  linarith [hmain]

/-! ## 7. Kernel facts of the localised pair kernels (at the sliding box) -/

/-- The localised pair kernel vanishes unless both arguments lie in the sliding box. -/
theorem wSmallPair_support_dlBox' {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u : ℝ³) (f : ℝ³ → ℝ) {x y : ℝ³} (hxy : wSmallPair M ℓ d u f x y ≠ 0) :
    x ∈ dlBox ℓ d u ∧ y ∈ dlBox ℓ d u := by
  constructor
  · refine Work.BoseFixB1S.chiSmallB_mem_dlBox_B1S hM hℓ hd u x (fun h0 => hxy ?_)
    rw [wSmallPair, h0]; ring
  · refine Work.BoseFixB1S.chiSmallB_mem_dlBox_B1S hM hℓ hd u y (fun h0 => hxy ?_)
    rw [wSmallPair, h0]; ring

/-- The one-body kernel is the two-body kernel times `1 − ω`. -/
theorem wSmall1Pair_rel' {v : ℝ³ → ℝ} (h : Work.UBB.ScatSol v) {M : ℕ} {ℓ d : ℝ} (u : ℝ³) :
    ∀ x y : ℝ³, wSmall1Pair h M ℓ d u x y
      = wSmallPair M ℓ d u v x y * (1 - omC (Classical.choose h) x y) := by
  intro x y
  simp only [wSmall1Pair, wSmallPair, wSmallScaled, g0, omC]
  ring

/-- The `g₂`-kernel is the two-body kernel times `1 − ω²`. -/
theorem wSmall2_rel' {v : ℝ³ → ℝ} (h : Work.UBB.ScatSol v) {M : ℕ} {ℓ d : ℝ} (u : ℝ³) :
    ∀ x y : ℝ³, wSmallPair M ℓ d u (g2 v h) x y
      = wSmallPair M ℓ d u v x y * (1 - omC (Classical.choose h) x y ^ 2) := by
  intro x y
  simp only [wSmallPair, wSmallScaled, g2, omC]
  ring

/-- The localised two-body kernel is symmetric at a radial numerator. -/
theorem wSmallPair_symm' {v : ℝ³ → ℝ} (hvrad : _root_.BoseGases.IsRadial v) {M : ℕ}
    (hM : 1 ≤ M) {ℓ d : ℝ} (u : ℝ³) :
    ∀ x y : ℝ³, wSmallPair M ℓ d u v x y = wSmallPair M ℓ d u v y x :=
  fun x y => wSmallPair_symm hM u (fun z => radial_neg hvrad z) x y

/-- The chosen scattering solution is symmetric. -/
theorem omC_chosen_sym' {v : ℝ³ → ℝ} (h : Work.UBB.ScatSol v) :
    ∀ x y : ℝ³, omC (Classical.choose h) x y = omC (Classical.choose h) y x :=
  omC_chosen_sym h

/-! ## 8. The pair part of `boxQSum` at a sector piece -/

/-- **The pair part at a sector piece.**  The seven pair fragments of the sector piece are the
`1_{n_A=k}`-weighted fragments of the state (`Work.BoseFixB1.SectorPiece.pairFrags_sectorPiece`),
and their sum collapses pointwise to `½ψ²·Σ_p w(x_p, x_q)`
(`Work.BoseFixB1.SectorPiece.pairFrags_sum_eq`).  The integrability of the sector-piece fragments
is `Work.BoseFixB1.SectorPiece.fragIntegrable_sectorPiece`, and the folding of the seven fragment
integrals is `Work.BoseFixB1.SectorPiece.pairInts_eq_integral_pairFrags`. -/
theorem pairRaw_sectorPiece {v : ℝ³ → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (h : Work.UBB.ScatSol v) {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
    (u : ℝ³) (hvol : 0 < boxMass ℓ d u) {N : ℕ} (k : ℕ) {Φ : Submission.BoseGases.X N → ℝ}
    (hΦc : Continuous Φ) :
    Work.BoseFixB1S.pairRaw (boxMass ℓ d u) ℓ (dlBox ℓ d u) (wSmallPair M ℓ d u v)
        (wSmall1Pair h M ℓ d u) (wSmallPair M ℓ d u (g2 v h)) (omC (Classical.choose h))
        (sectorPiece (dlBox ℓ d u) k Φ)
      = (1 / 2) * ∑ p ∈ Submission.BoseGases.pairSet N,
          ∫ x in abox N ℓ, (sectorPiece (dlBox ℓ d u) k Φ x) ^ 2
            * wSmallPair M ℓ d u v (x p.1) (x p.2) := by
  classical
  have hA : MeasurableSet (dlBox ℓ d u) := Work.SmallBoxSliding.measurableSet_dlBox ℓ d u
  have hAc : dlBox ℓ d u ⊆ acube ℓ := Work.SmallBoxSliding.dlBox_subset_acube ℓ d u
  have hvolA : boxMass ℓ d u = (MeasureTheory.volume (dlBox ℓ d u)).toReal := by
    rw [Work.SmallBoxSliding.boxMass_eq_measureReal, MeasureTheory.Measure.real_def]
  set g : Submission.BoseGases.X N → ℝ :=
    (Work.FockBridge.sectorSet (dlBox ℓ d u) k).indicator (fun _ => (1 : ℝ)) with hg
  -- bounds of the state and of its sector piece
  obtain ⟨B, hB⟩ := (abox_compact N hℓ).exists_bound_of_continuousOn
    (s := abox N ℓ) (f := Φ) hΦc.continuousOn
  have hBb : ∀ x ∈ abox N ℓ, |Φ x| ≤ B := fun x hx => by
    simpa [Real.norm_eq_abs] using hB x hx
  have hψb : ∀ x ∈ abox N ℓ, |sectorPiece (dlBox ℓ d u) k Φ x| ≤ B :=
    sectorPiece_bound hℓ k hBb
  -- the seven fragments of the sector piece are integrable
  have hfrag : ∀ p ∈ Submission.BoseGases.pairSet N,
      (MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
        Work.BoseFixB1S.fg0 (boxMass ℓ d u) (dlBox ℓ d u) (wSmallPair M ℓ d u (g2 v h))
          (sectorPiece (dlBox ℓ d u) k Φ) p.1 p.2 x) (abox N ℓ) volume
      ∧ MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
        Work.BoseFixB1S.fg1 (boxMass ℓ d u) (dlBox ℓ d u) (wSmallPair M ℓ d u (g2 v h))
          (sectorPiece (dlBox ℓ d u) k Φ) p.1 p.2 x) (abox N ℓ) volume
      ∧ MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
        Work.BoseFixB1S.fg2a (boxMass ℓ d u) (dlBox ℓ d u) (wSmallPair M ℓ d u (g2 v h))
          (sectorPiece (dlBox ℓ d u) k Φ) p.1 p.2 x) (abox N ℓ) volume
      ∧ MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
        Work.BoseFixB1S.fg2b (boxMass ℓ d u) (dlBox ℓ d u) (wSmallPair M ℓ d u (g2 v h))
          (sectorPiece (dlBox ℓ d u) k Φ) p.1 p.2 x) (abox N ℓ) volume
      ∧ MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
        Work.BoseFixB1S.fg2c (boxMass ℓ d u) (dlBox ℓ d u) (wSmallPair M ℓ d u (g0 v h))
          (sectorPiece (dlBox ℓ d u) k Φ) p.1 p.2 x) (abox N ℓ) volume
      ∧ MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
        Work.BoseFixB1S.fg3 (boxMass ℓ d u) (dlBox ℓ d u) (wSmallPair M ℓ d u (g0 v h))
          (sectorPiece (dlBox ℓ d u) k Φ) p.1 p.2 x) (abox N ℓ) volume
      ∧ MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
        Work.BoseFixB1S.fg4 (boxMass ℓ d u) (dlBox ℓ d u) (wSmallPair M ℓ d u v)
          (omC (Classical.choose h))
          (sectorPiece (dlBox ℓ d u) k Φ) p.1 p.2 x) (abox N ℓ) volume) := by
    intro p hp
    have hne : p.1 ≠ p.2 := by
      simpa only [Submission.BoseGases.pairSet, Finset.mem_filter, Finset.mem_univ,
        true_and] using hp
    exact Work.BoseFixB1.SectorPiece.fragIntegrable_sectorPiece hR0 hv_supp hv hvrad hv1 h hM
      hℓ hd hR hRχ u k hΦc hne
  -- `pairRaw` is the sum of the per-pair fragment integrals
  have hpair1 : Work.BoseFixB1S.pairRaw (boxMass ℓ d u) ℓ (dlBox ℓ d u) (wSmallPair M ℓ d u v)
        (wSmall1Pair h M ℓ d u) (wSmallPair M ℓ d u (g2 v h)) (omC (Classical.choose h))
        (sectorPiece (dlBox ℓ d u) k Φ)
      = ∑ p ∈ Submission.BoseGases.pairSet N,
          ∫ x in abox N ℓ, Work.BoseFixB1S.pairFrags (boxMass ℓ d u) (dlBox ℓ d u)
            (wSmallPair M ℓ d u v) (wSmall1Pair h M ℓ d u) (wSmallPair M ℓ d u (g2 v h))
            (omC (Classical.choose h)) (sectorPiece (dlBox ℓ d u) k Φ) p.1 p.2 x := by
    rw [Work.BoseFixB1S.pairRaw_eq_sumPairInts]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    obtain ⟨h0, h1, h2a, h2b, h2c, h3, h4⟩ := hfrag p hp
    exact Work.BoseFixB1.SectorPiece.pairInts_eq_integral_pairFrags h0 h1 h2a h2b h2c h3 h4
  -- the fragments of the sector piece are the indicator-weighted fragments of the state
  have hpair2 : (∑ p ∈ Submission.BoseGases.pairSet N,
          ∫ x in abox N ℓ, Work.BoseFixB1S.pairFrags (boxMass ℓ d u) (dlBox ℓ d u)
            (wSmallPair M ℓ d u v) (wSmall1Pair h M ℓ d u) (wSmallPair M ℓ d u (g2 v h))
            (omC (Classical.choose h)) (sectorPiece (dlBox ℓ d u) k Φ) p.1 p.2 x)
      = ∑ p ∈ Submission.BoseGases.pairSet N,
          ∫ x in abox N ℓ, g x * Work.BoseFixB1S.pairFrags (boxMass ℓ d u) (dlBox ℓ d u)
            (wSmallPair M ℓ d u v) (wSmall1Pair h M ℓ d u) (wSmallPair M ℓ d u (g2 v h))
            (omC (Classical.choose h)) Φ p.1 p.2 x := by
    refine Finset.sum_congr rfl (fun p hp => ?_)
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    rw [Work.BoseFixB1.SectorPiece.pairFrags_sectorPiece (ℓ := ℓ)
      (volA := boxMass ℓ d u) hA k p.1 p.2 x, hg]
  -- fold the pair sum
  have hpair3 : (∑ p ∈ Submission.BoseGases.pairSet N,
          ∫ x in abox N ℓ, g x * Work.BoseFixB1S.pairFrags (boxMass ℓ d u) (dlBox ℓ d u)
            (wSmallPair M ℓ d u v) (wSmall1Pair h M ℓ d u) (wSmallPair M ℓ d u (g2 v h))
            (omC (Classical.choose h)) Φ p.1 p.2 x)
      = ∫ x in abox N ℓ, ∑ p ∈ Submission.BoseGases.pairSet N,
          g x * Work.BoseFixB1S.pairFrags (boxMass ℓ d u) (dlBox ℓ d u)
            (wSmallPair M ℓ d u v) (wSmall1Pair h M ℓ d u) (wSmallPair M ℓ d u (g2 v h))
            (omC (Classical.choose h)) Φ p.1 p.2 x := by
    rw [← MeasureTheory.integral_finsetSum (Submission.BoseGases.pairSet N)]
    intro p hp
    have hpw : (fun x : Submission.BoseGases.X N => g x * Work.BoseFixB1S.pairFrags
        (boxMass ℓ d u) (dlBox ℓ d u) (wSmallPair M ℓ d u v) (wSmall1Pair h M ℓ d u)
        (wSmallPair M ℓ d u (g2 v h)) (omC (Classical.choose h)) Φ p.1 p.2 x)
        = fun x => Work.BoseFixB1S.pairFrags (boxMass ℓ d u) (dlBox ℓ d u)
            (wSmallPair M ℓ d u v) (wSmall1Pair h M ℓ d u) (wSmallPair M ℓ d u (g2 v h))
            (omC (Classical.choose h)) (sectorPiece (dlBox ℓ d u) k Φ) p.1 p.2 x := by
      funext x
      rw [Work.BoseFixB1.SectorPiece.pairFrags_sectorPiece (ℓ := ℓ)
        (volA := boxMass ℓ d u) hA k p.1 p.2 x, hg]
    rw [hpw]
    obtain ⟨h0, h1, h2a, h2b, h2c, h3, h4⟩ := hfrag p hp
    simp only [Work.BoseFixB1S.pairFrags]
    exact (((((h0.add h1).add h2a).add h2b).add h2c).add h3).add h4
  -- pull the indicator out of the pair sum
  have hpair4 : (∫ x in abox N ℓ, ∑ p ∈ Submission.BoseGases.pairSet N,
          g x * Work.BoseFixB1S.pairFrags (boxMass ℓ d u) (dlBox ℓ d u)
            (wSmallPair M ℓ d u v) (wSmall1Pair h M ℓ d u) (wSmallPair M ℓ d u (g2 v h))
            (omC (Classical.choose h)) Φ p.1 p.2 x)
      = ∫ x in abox N ℓ, g x * ∑ p ∈ Submission.BoseGases.pairSet N,
          Work.BoseFixB1S.pairFrags (boxMass ℓ d u) (dlBox ℓ d u) (wSmallPair M ℓ d u v)
            (wSmall1Pair h M ℓ d u) (wSmallPair M ℓ d u (g2 v h)) (omC (Classical.choose h))
            Φ p.1 p.2 x := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    rw [Finset.mul_sum]
  -- the pointwise pair sum at the state
  have hpair5 : (∫ x in abox N ℓ, g x * ∑ p ∈ Submission.BoseGases.pairSet N,
          Work.BoseFixB1S.pairFrags (boxMass ℓ d u) (dlBox ℓ d u) (wSmallPair M ℓ d u v)
            (wSmall1Pair h M ℓ d u) (wSmallPair M ℓ d u (g2 v h)) (omC (Classical.choose h))
            Φ p.1 p.2 x)
      = ∫ x in abox N ℓ, g x * ((1 / 2) * (Φ x) ^ 2
          * ∑ p ∈ Submission.BoseGases.pairSet N, wSmallPair M ℓ d u v (x p.1) (x p.2)) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards [MeasureTheory.self_mem_ae_restrict (abox_measurable N ℓ)] with x hx
    rw [Work.BoseFixB1.SectorPiece.pairFrags_sum_eq hℓ hvol hA hvolA hAc
      (wSmallPair_symm' hvrad hM u) (omC_chosen_sym' h) (wSmall1Pair_rel' h u)
      (wSmall2_rel' h u)
      (fun a b hab => wSmallPair_support_dlBox' hM hℓ hd u v hab) hΦc hx]
  -- the final collapse to `½Σ_p ∫ ψ²w`
  have hpair6 : (∫ x in abox N ℓ, g x * ((1 / 2) * (Φ x) ^ 2
          * ∑ p ∈ Submission.BoseGases.pairSet N, wSmallPair M ℓ d u v (x p.1) (x p.2)))
      = (1 / 2) * ∑ p ∈ Submission.BoseGases.pairSet N,
          ∫ x in abox N ℓ, (sectorPiece (dlBox ℓ d u) k Φ x) ^ 2
            * wSmallPair M ℓ d u v (x p.1) (x p.2) := by
    have hpt : (fun x : Submission.BoseGases.X N => g x * ((1 / 2) * (Φ x) ^ 2
          * ∑ p ∈ Submission.BoseGases.pairSet N, wSmallPair M ℓ d u v (x p.1) (x p.2)))
        = fun x => (1 / 2) * ∑ p ∈ Submission.BoseGases.pairSet N,
            (sectorPiece (dlBox ℓ d u) k Φ x) ^ 2 * wSmallPair M ℓ d u v (x p.1) (x p.2) := by
      funext x
      have h1 : (sectorPiece (dlBox ℓ d u) k Φ x) ^ 2 = g x * (Φ x) ^ 2 := by
        rw [hg, Work.FockBridge.sectorPiece]
        by_cases hx : x ∈ Work.FockBridge.sectorSet (dlBox ℓ d u) k
        · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]; ring
        · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]; ring
      rw [h1]
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun p hp => ?_)
      ring
    rw [hpt, MeasureTheory.integral_const_mul,
      ← MeasureTheory.integral_finsetSum (Submission.BoseGases.pairSet N)]
    intro p hp
    have hne : p.1 ≠ p.2 := by
      simpa only [Submission.BoseGases.pairSet, Finset.mem_filter, Finset.mem_univ,
        true_and] using hp
    have hψm : Measurable (sectorPiece (dlBox ℓ d u) k Φ) :=
      sectorPiece_measurable hA k hΦc.measurable
    have hB0 : 0 ≤ B := le_trans (abs_nonneg (Φ 0)) (hBb 0 (zero_mem_abox hℓ.le))
    refine Work.BoseFixB1.integrableOn_slot_wSmallPair (N := N) hℓ hd
      (Submission.BoseGases.v_integrable hv1)
      (fun z hz => Submission.BoseGases.v_eq_zero_of_norm_ge hv_supp hz) hM hR hRχ u hne
      (hψm.pow_const 2).aestronglyMeasurable (sq_nonneg B) ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict (abox_measurable N ℓ)] with x hx
    rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hψb x hx) 2
  calc Work.BoseFixB1S.pairRaw (boxMass ℓ d u) ℓ (dlBox ℓ d u) (wSmallPair M ℓ d u v)
        (wSmall1Pair h M ℓ d u) (wSmallPair M ℓ d u (g2 v h)) (omC (Classical.choose h))
        (sectorPiece (dlBox ℓ d u) k Φ)
      = ∑ p ∈ Submission.BoseGases.pairSet N,
          ∫ x in abox N ℓ, Work.BoseFixB1S.pairFrags (boxMass ℓ d u) (dlBox ℓ d u)
            (wSmallPair M ℓ d u v) (wSmall1Pair h M ℓ d u) (wSmallPair M ℓ d u (g2 v h))
            (omC (Classical.choose h)) (sectorPiece (dlBox ℓ d u) k Φ) p.1 p.2 x := hpair1
    _ = _ := hpair2
    _ = _ := hpair3
    _ = _ := hpair4
    _ = _ := hpair5
    _ = _ := hpair6

/-! ## 9. The potential split (`potsplit`) at a sector piece -/

/-- **`Work.BoseFixB1.bqPotsplit` at a sector piece**: the localised potential word equals the
five-word box sum.  This is the first conjunct of `Work.BoseFixB1.SectorPieceStructure`.

The structural input is that the box projections *commute with the sector indicator*
(`Work.BoseFixB1.boxPInd_sectorPiece`, `Work.BoseFixB1.boxQInd_sectorPiece`): every pair fragment
of the sector piece is the `1_{n_A=k}`-weighted fragment of the state
(`Work.BoseFixB1.SectorPiece.pairFrags_sectorPiece`), whose sum collapses pointwise to
`½ψ²Σ_p w` (`Work.BoseFixB1.SectorPiece.pairFrags_sum_eq`).  The `μ`-part is the corpus's
`Work.BoseFixB1.SectorPiece.boxMuSum_sectorPiece`, the `qLHSword` split is the corpus's
`Work.BoseFixR.qLHSwordSplitAe`, and the two sides are glued by `Work.BoseFixB1S.boxQSum_eq`. -/
theorem bqPotsplit_sectorPiece {v : ℝ³ → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (h : Work.UBB.ScatSol v) {M : ℕ} (hM : 1 ≤ M) {ℓ d μ : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
    (u : ℝ³) (hvol : 0 < boxMass ℓ d u) {N : ℕ} (k : ℕ) {Φ : Submission.BoseGases.X N → ℝ}
    (hΦc : Continuous Φ) :
    Submission.BoseGases.qLHSword (N := N) ℓ μ (wSmallPair M ℓ d u v) (wSmall1Pair h M ℓ d u)
        (sectorPiece (dlBox ℓ d u) k Φ)
      = Work.BoseFixB1S.boxQSum (boxMass ℓ d u) ℓ μ (dlBox ℓ d u) (wSmallPair M ℓ d u v)
          (wSmall1Pair h M ℓ d u) (wSmallPair M ℓ d u (g2 v h)) (omC (Classical.choose h))
          (sectorPiece (dlBox ℓ d u) k Φ) := by
  classical
  have hA : MeasurableSet (dlBox ℓ d u) := Work.SmallBoxSliding.measurableSet_dlBox ℓ d u
  have hψm : Measurable (sectorPiece (dlBox ℓ d u) k Φ) :=
    sectorPiece_measurable hA k hΦc.measurable
  obtain ⟨B, hB⟩ := (abox_compact N hℓ).exists_bound_of_continuousOn
    (s := abox N ℓ) (f := Φ) hΦc.continuousOn
  have hBb : ∀ x ∈ abox N ℓ, |Φ x| ≤ B := fun x hx => by
    simpa [Real.norm_eq_abs] using hB x hx
  have hψb : ∀ x ∈ abox N ℓ, |sectorPiece (dlBox ℓ d u) k Φ x| ≤ B :=
    sectorPiece_bound hℓ k hBb
  have hB0 : 0 ≤ B := le_trans (abs_nonneg (Φ 0)) (hBb 0 (zero_mem_abox hℓ.le))
  -- the universal fibre constant of `Work.BoseFixB1.wSmall1Pair_fibre_abs_le`
  set Kfib : ℝ := (chiSupAbs * chiSmallDecay M)
        * ((2 * (chiSupAbs * chiSmallDecay M) / Work.SmallBoxSliding.smallConvLower M)
            * (8 * π * _root_.BoseGases.a v)) with hKfib
  -- integrability of the one-body slot summands
  have hfi : ∀ i : Fin N, IntegrableOn (fun x : Submission.BoseGases.X N =>
      (sectorPiece (dlBox ℓ d u) k Φ x) ^ 2
        * w1Fibre ℓ (wSmall1Pair h M ℓ d u) (x i)) (abox N ℓ) volume := by
    intro i
    have hfibb : ∀ z : ℝ³, |w1Fibre ℓ (wSmall1Pair h M ℓ d u) z| ≤ Kfib := fun z =>
      Work.BoseFixB1.wSmall1Pair_fibre_abs_le hv_supp hR0 hv hvrad h hM hℓ hd hR hRχ u z
    have hfibm : AEStronglyMeasurable
        (fun z : ℝ³ => w1Fibre ℓ (wSmall1Pair h M ℓ d u) z) (volume.restrict (acube ℓ)) :=
      Work.BoseFixB1.aestronglyMeasurable_wSmallPairFibre (ℓ := ℓ) (d := d) M u
        (Submission.BoseGases.g0_integrable hR0 hv_supp h).aemeasurable
    refine MeasureTheory.IntegrableOn.of_bound (abox_lt_top N ℓ hℓ.le)
      ((hψm.pow_const 2).aestronglyMeasurable.mul
        (Submission.BoseGases.aem_comp_coord' i hfibm)) (B ^ 2 * Kfib) ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict (abox_measurable N ℓ)] with x hx
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _), ← sq_abs]
    exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) (hψb x hx) 2) (hfibb (x i)) (abs_nonneg _)
      (sq_nonneg B)
  -- integrability of the pair summands
  have hWi : ∀ p ∈ Submission.BoseGases.pairSet N, IntegrableOn (fun x : Submission.BoseGases.X N =>
      (sectorPiece (dlBox ℓ d u) k Φ x) ^ 2 * wSmallPair M ℓ d u v (x p.1) (x p.2))
      (abox N ℓ) volume := by
    intro p hp
    have hne : p.1 ≠ p.2 := by
      simpa only [Submission.BoseGases.pairSet, Finset.mem_filter, Finset.mem_univ,
        true_and] using hp
    refine Work.BoseFixB1.integrableOn_slot_wSmallPair (N := N) hℓ hd
      (Submission.BoseGases.v_integrable hv1)
      (fun z hz => Submission.BoseGases.v_eq_zero_of_norm_ge hv_supp hz) hM hR hRχ u hne
      (hψm.pow_const 2).aestronglyMeasurable (sq_nonneg B) ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict (abox_measurable N ℓ)] with x hx
    rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hψb x hx) 2
  -- the corpus split of `qLHSword`
  have hL := Work.BoseFixR.qLHSwordSplitAe (N := N) (ℓ := ℓ) (μ := μ) hℓ hfi hWi
  -- the `μ`-part at the state
  have hmu' : (∑ i : Fin N, Work.BoseFixB1S.boxMuPhi (N := N) ℓ (wSmall1Pair h M ℓ d u)
        (sectorPiece (dlBox ℓ d u) k Φ) i)
      = ∫ x in abox N ℓ, (sectorPiece (dlBox ℓ d u) k Φ x) ^ 2
          * (∑ i : Fin N, w1Fibre ℓ (wSmall1Pair h M ℓ d u) (x i)) := by
    simp only [Work.BoseFixB1S.boxMuPhi]
    rw [← MeasureTheory.integral_finsetSum Finset.univ (fun i _ => by
      simpa [IntegrableOn] using hfi i)]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    rw [Finset.mul_sum]
  have hW := Work.BoseFixB1S.boxQSum_eq (boxMass ℓ d u) ℓ μ (dlBox ℓ d u) (wSmallPair M ℓ d u v)
    (wSmall1Pair h M ℓ d u) (wSmallPair M ℓ d u (g2 v h)) (omC (Classical.choose h))
    (sectorPiece (dlBox ℓ d u) k Φ)
  have hP := pairRaw_sectorPiece hv_supp hR0 hv hvrad hv1 h hM hℓ hd hR hRχ u hvol k hΦc
  have hMsum := Work.BoseFixB1.SectorPiece.boxMuSum_sectorPiece (v := v) (R0 := R0) hv_supp hR0
    hv hvrad h hM hℓ hd hR hRχ u k hΦc
  rw [hL, hmu', hW, hP, hMsum]
  ring

/-! ## 10. The `Q₀` value at a sector piece at FS's parameters -/

/-- **`Q₀`'s value at a sector piece** — the second conjunct of
`Work.BoseFixB1.SectorPieceStructure`, i.e. `Work.BoseFixB1.boxQ0_sectorPiece` with the
`B × B`-integrability of the pair kernel discharged from the dilute regime. -/
theorem boxQ0_sectorPiece_fs {v : ℝ³ → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (h : Work.UBB.ScatSol v)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d μ : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
    (u : ℝ³) (hvol : 0 < boxMass ℓ d u) {N : ℕ} (k : ℕ) {Φ : Submission.BoseGases.X N → ℝ}
    (hΦc : Continuous Φ) :
    Work.BoseFixB1S.boxQ0 (boxMass ℓ d u) ℓ μ (dlBox ℓ d u) (wSmall1Pair h M ℓ d u)
        (wSmallPair M ℓ d u (g2 v h)) (sectorPiece (dlBox ℓ d u) k Φ)
      = (1 / 2) * (Work.BoseFixB1S.boxM2 (boxMass ℓ d u) (dlBox ℓ d u)
            (wSmallPair M ℓ d u (g2 v h)) / (boxMass ℓ d u) ^ 2)
          * Work.BoseFixB1S.boxPairCount (boxMass ℓ d u) ℓ (dlBox ℓ d u)
              (sectorPiece (dlBox ℓ d u) k Φ)
        - μ * (Work.BoseFixB1S.boxM1 ℓ (dlBox ℓ d u) (wSmall1Pair h M ℓ d u)
              / boxMass ℓ d u)
            * Work.BoseFixB1S.boxFlatCount (boxMass ℓ d u) ℓ (dlBox ℓ d u)
                (sectorPiece (dlBox ℓ d u) k Φ) := by
  have hAc : dlBox ℓ d u ⊆ acube ℓ := Work.SmallBoxSliding.dlBox_subset_acube ℓ d u
  have hw2i : MeasureTheory.IntegrableOn
      (fun q : ℝ³ × ℝ³ => wSmallPair M ℓ d u (g2 v h) q.1 q.2)
      (dlBox ℓ d u ×ˢ dlBox ℓ d u) :=
    (Work.BoseFixB1.integrableOn_wSmallPair_cube
      (Submission.BoseGases.g2_integrable hR0 hv hvrad hv_supp h)
      (fun z hz => Submission.BoseGases.g2_support_of_norm_ge hv_supp hz h) hM hℓ hd hR hRχ
      u).mono_set (Set.prod_mono hAc hAc)
  exact boxQ0_sectorPiece h hM u k Φ hℓ hvol hw2i

end Work.BoseFixB1

namespace Work.BoseFixB1

/-- **The sector-piece structure bundle of `Work.BoseFixB1.CrossWordsDefs`.**  Choose the
admissibility threshold so that FS's parameter regime holds (so the localised kernels are
integrable and their peels apply) and then prove the four structural conjuncts at every admissible
`μ`:

* **(S1)** the potential split (`potsplit`) — `Work.BoseFixB1.bqPotsplit_sectorPiece`;
* **(S2)** the exact value of `Q₀` — `Work.BoseFixB1.boxQ0_sectorPiece_fs`;
* **(S3)** the flat-count Jensen inequality — `Work.BoseFixB1.boxFlatSqJensen_sectorPiece`;
* **(S4)** the count identity `n₀ + n₊ = k·‖ψ‖²` — `Work.BoseFixB1.boxFlat_add_boxQCount_sectorPiece`.

All four are proved at *measurable/bounded* regularity, which is exactly what a (non-continuous)
sector piece satisfies; the continuous-state corpus statements are used only for the *state* `Φ`. -/
theorem sectorPieceStructure {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ Work.BoseFixB1.SectorPieceStructure v h ε₀ := by
  classical
  obtain ⟨ε₀, hε₀pos, hε₀⟩ := Work.BoseFixB1.BddSector.regimeBdd (v := v) (R := R) hav hR
  refine ⟨ε₀, hε₀pos, ?_⟩
  intro μ hAdm n k Φ u hvolmass
  obtain ⟨hμpos, hdil, -⟩ := hAdm
  obtain ⟨hℓpos, hdpos, hM1, hR16, hRchi⟩ := hε₀ μ hμpos hdil
  dsimp only [Work.BoseFixB1B.PBB]
  have hΦc : Continuous (Φ : Submission.BoseGases.X n → ℝ) := Φ.contDiff.continuous
  obtain ⟨B, hB⟩ := (Submission.BoseGases.abox_compact n hℓpos).exists_bound_of_continuousOn
    (s := Submission.BoseGases.abox n (Work.BoseFixB1B.PBℓ v μ)) (f := Φ) hΦc.continuousOn
  have hBb : ∀ x ∈ Submission.BoseGases.abox n (Work.BoseFixB1B.PBℓ v μ), |Φ x| ≤ B :=
    fun x hx => by simpa [Real.norm_eq_abs] using hB x hx
  have hΦm : Measurable (Φ : Submission.BoseGases.X n → ℝ) := hΦc.measurable
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Work.SmallBoxSliding.qLHSwordB]
    exact bqPotsplit_sectorPiece (R0 := R) hv_supp hR hv hvrad hv1 h hM1 hℓpos hdpos hR16 hRchi
      u hvolmass k hΦc
  · exact boxQ0_sectorPiece_fs (R0 := R) hv_supp hR hv hvrad h hM1 hℓpos hdpos hR16 hRchi u
      hvolmass k hΦc
  · simpa only [pow_two] using boxFlatSqJensen_sectorPiece hℓpos hvolmass
      (Work.SmallBoxSliding.measurableSet_dlBox _ _ _)
      (by rw [Work.SmallBoxSliding.boxMass_eq_measureReal, MeasureTheory.Measure.real_def])
      (Work.SmallBoxSliding.dlBox_subset_acube _ _ _) hΦm hBb
  · exact boxFlat_add_boxQCount_sectorPiece hℓpos hvolmass
      (Work.SmallBoxSliding.measurableSet_dlBox _ _ _)
      (by rw [Work.SmallBoxSliding.boxMass_eq_measureReal, MeasureTheory.Measure.real_def])
      (Work.SmallBoxSliding.dlBox_subset_acube _ _ _) hΦm hBb

end Work.BoseFixB1

