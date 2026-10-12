import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.boxFlatCount_eq_sum_compT
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseFixB1.SectorAux

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-- **Resolution of the identity by the three-way joint components, pointwise.**  For every state
`Φ` and every configuration `x`, the disjoint pairs `(S,T)` (the `P`-slots and the `Q`-slots; `R`
outside) resolve `Φ`:

    Σ_{(S,T), S ⊥ T} boxCompT volA A S T Φ x = Φ x .

No hypothesis on `Φ` (not even measurability) is needed. -/
theorem boxCompT_sum_eq_pt {N : ℕ} (volA : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (Φ : Submission.BoseGases.X N → ℝ) (x : Submission.BoseGases.X N) :
    (∑ p ∈ Work.BoseFixB1S.disjPairs N,
        Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x) = Φ x := by
  have hsum : (∑ p ∈ Work.BoseFixB1S.disjPairs N,
        Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ) = Φ := by
    calc (∑ p ∈ Work.BoseFixB1S.disjPairs N,
            Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ)
        = ∑ p ∈ Work.BoseFixB1S.disjPairs N,
            (List.finRange N).foldl (fun g i => Work.BoseFixB1S.boxPatOp volA A i
              (if i ∈ p.1 then 0 else if i ∈ p.2 then 1 else 2) g) Φ :=
          Finset.sum_congr rfl (fun p _ => Work.BoseFixB1S.boxCompT_eq_foldl volA A p.1 p.2 Φ)
      _ = ∑ c : Fin N → Fin 3, (List.finRange N).foldl (fun g i =>
            Work.BoseFixB1S.boxPatOp volA A i (c i) g) Φ :=
          Work.BoseFixB1S.sumFilterDisjointFin3 (fun c => (List.finRange N).foldl (fun g i =>
            Work.BoseFixB1S.boxPatOp volA A i (c i) g) Φ)
      _ = Φ := Work.BoseFixB1S.sumFoldFinRangeTriple
          (fun i b g => Work.BoseFixB1S.boxPatOp volA A i b g)
          (fun i Ψ => Work.BoseFixB1S.boxPatOp_sum volA A i Ψ) Φ
  simpa [Finset.sum_apply] using congr_fun hsum x

/-- **The eigenvalue identity of `Pⱼ` on the joint component, for `GoodState`s.**  If `Φ` is
measurable and bounded on the box, then on the box

    Pⱼ (boxCompT volA A S T Φ) = if j ∈ S then boxCompT volA A S T Φ else 0 .

(The continuous version `Work.BoseFixB1S.boxPInd_boxCompT` uses continuity only to produce the
`GoodState` hypothesis of the fold induction `boxCompTAux_ind`.) -/
theorem boxPInd_boxCompT_goodState {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) (S T : Finset (Fin N))
    {Φ : Submission.BoseGases.X N → ℝ} (hΦg : Work.BoseFixB1S.GoodState ℓ Φ) (j : Fin N) :
    ∀ x ∈ Submission.BoseGases.abox N ℓ,
      Work.UBBInputs8.boxPInd volA A j (Work.BoseFixB1S.boxCompT volA A S T Φ) x
        = (if j ∈ S then Work.BoseFixB1S.boxCompT volA A S T Φ x else 0) := by
  intro x hx
  obtain ⟨hC, _⟩ := Work.BoseFixB1S.boxCompTAux_ind hℓ hvol hA hvolA hAc S T j
    (List.finRange N) (List.nodup_finRange N)
  have hres := hC (List.mem_finRange j) Φ hΦg x hx
  rw [Work.BoseFixB1S.boxCompT_eq_aux]
  exact hres

/-- **Slot-linearity of `Pⱼ` in the `GoodState` class** (the `Finset`-indexed form of
`BoxPotOper.boxPInd_add`, re-proved here because the sibling copy is `private`). -/
theorem boxPInd_finsetSum_good {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) {ι : Type*} (s : Finset ι)
    (F : ι → Submission.BoseGases.X N → ℝ)
    (hF : ∀ p ∈ s, Work.BoseFixB1S.GoodState ℓ (F p))
    (j : Fin N) {x : Submission.BoseGases.X N} (hx : x ∈ Submission.BoseGases.abox N ℓ) :
    Work.UBBInputs8.boxPInd volA A j (fun y => ∑ p ∈ s, F p y) x
      = ∑ p ∈ s, Work.UBBInputs8.boxPInd volA A j (F p) x := by
  have hInt : (∫ z in A, (∑ p ∈ s, F p (Function.update x j z)))
      = ∑ p ∈ s, ∫ z in A, F p (Function.update x j z) :=
    MeasureTheory.integral_finsetSum s (fun p hp => by
      obtain ⟨hm, C, hb⟩ := hF p hp
      exact Work.BoseFixB1S.slotInt_of_bound hℓ hA hAc j x hx hm hb)
  simp only [Work.UBBInputs8.boxPInd]
  rw [hInt, Finset.mul_sum, Finset.sum_mul]

/-- **The spectral decomposition of `PⱼΦ` for `GoodState`s**: on the box, `PⱼΦ` is the sum of the
joint components whose `P`-slots contain `j`. -/
theorem boxPInd_eq_sum_boxCompT_goodState {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) {Φ : Submission.BoseGases.X N → ℝ}
    (hΦg : Work.BoseFixB1S.GoodState ℓ Φ) (j : Fin N) :
    ∀ x ∈ Submission.BoseGases.abox N ℓ,
      Work.UBBInputs8.boxPInd volA A j Φ x
        = ∑ p ∈ (Work.BoseFixB1S.disjPairs N).filter (fun p => j ∈ p.1),
            Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x := by
  intro x hx
  classical
  have hdecomp : ∀ y ∈ Submission.BoseGases.abox N ℓ,
      Φ y = ∑ p ∈ Work.BoseFixB1S.disjPairs N,
        Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ y := by
    intro y hy
    exact (boxCompT_sum_eq_pt volA A Φ y).symm
  have hgood : ∀ p ∈ Work.BoseFixB1S.disjPairs N,
      Work.BoseFixB1S.GoodState ℓ (Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ) :=
    fun p _ => Work.BoseFixB1S.goodState_boxCompT hℓ hvol hA hvolA hAc p.1 p.2 hΦg
  calc Work.UBBInputs8.boxPInd volA A j Φ x
      = Work.UBBInputs8.boxPInd volA A j
          (fun y => ∑ p ∈ Work.BoseFixB1S.disjPairs N,
            Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ y) x :=
          Work.BoseFixB1S.agreeBox_boxPInd hA hAc j hdecomp x hx
    _ = ∑ p ∈ Work.BoseFixB1S.disjPairs N,
          Work.UBBInputs8.boxPInd volA A j (Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ) x :=
          boxPInd_finsetSum_good hℓ hA hAc (Work.BoseFixB1S.disjPairs N) _ hgood j hx
    _ = ∑ p ∈ Work.BoseFixB1S.disjPairs N,
          (if j ∈ p.1 then Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x else 0) :=
          Finset.sum_congr rfl (fun p _ =>
            boxPInd_boxCompT_goodState hℓ hvol hA hvolA hAc p.1 p.2 hΦg j x hx)
    _ = ∑ p ∈ (Work.BoseFixB1S.disjPairs N).filter (fun p => j ∈ p.1),
          Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x := by
          rw [Finset.sum_filter]

end Work.BoseFixB1.SectorAux
