import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseB1Cube.ConeC.BoseFixB1S_boxPairCount_eq_sum_compT
import Submission.Work.BoseFixB1.SectorAux.boxCompTOrthMeas
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseFixB1.SectorAux

open Submission.BoseGases
open Work.BoseFixB1S

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## 1. The resolution of unity at arbitrary states -/

/-- The three-way joint components resolve the identity on the analysis box:
`Σ_{(S,T), S ⊥ T} ψ_{S,T} = Φ`, pointwise, for an *arbitrary* state `Φ` (the continuity
hypothesis of `Work.BoseFixB1S.boxCompT_sum_eq` is unused in its proof). -/
theorem goodBoxCompT_sum_eq {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) {Φ : Submission.BoseGases.X N → ℝ} :
    ∀ x ∈ Submission.BoseGases.abox N ℓ,
      (∑ p ∈ Work.BoseFixB1S.disjPairs N,
        Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x) = Φ x := by
  intro x hx
  have hsum : (∑ p ∈ Work.BoseFixB1S.disjPairs N,
      Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ) = Φ := by
    calc (∑ p ∈ Work.BoseFixB1S.disjPairs N,
            Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ)
        = ∑ p ∈ Work.BoseFixB1S.disjPairs N,
            (List.finRange N).foldl (fun g i => boxPatOp volA A i
              (if i ∈ p.1 then 0 else if i ∈ p.2 then 1 else 2) g) Φ :=
          Finset.sum_congr rfl (fun p _ => boxCompT_eq_foldl volA A p.1 p.2 Φ)
      _ = ∑ c : Fin N → Fin 3, (List.finRange N).foldl (fun g i =>
            boxPatOp volA A i (c i) g) Φ :=
          sumFilterDisjointFin3 (fun c => (List.finRange N).foldl (fun g i =>
            boxPatOp volA A i (c i) g) Φ)
      _ = Φ := sumFoldFinRangeTriple (fun i b g => boxPatOp volA A i b g)
          (fun i Ψ => boxPatOp_sum volA A i Ψ) Φ
  simpa [Finset.sum_apply] using congr_fun hsum x

/-! ## 2. Parseval for the orthogonal components -/

/-- **Parseval for the three-way components** at `GoodState` states: for a family `s` of disjoint
pairs, the squared `L²`-norm of the sum of the components is the sum of the squared norms, since
the cross terms vanish by `boxCompT_orth_good`. -/
theorem goodParsevalCompT {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) {Φ : Submission.BoseGases.X N → ℝ}
    (hΦ : Work.BoseFixB1S.GoodState ℓ Φ)
    (s : Finset (Finset (Fin N) × Finset (Fin N))) (hs : ∀ p ∈ s, Disjoint p.1 p.2) :
    (∫ x in Submission.BoseGases.abox N ℓ,
        (∑ p ∈ s, Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x) ^ 2)
      = ∑ p ∈ s, ∫ x in Submission.BoseGases.abox N ℓ,
          (Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x) ^ 2 := by
  have hG : ∀ p : Finset (Fin N) × Finset (Fin N),
      Work.BoseFixB1S.GoodState ℓ (Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ) :=
    fun p => Work.BoseFixB1S.goodState_boxCompT hℓ hvol hA hvolA hAc p.1 p.2 hΦ
  -- the pairwise products of components are integrable on the box
  have hprod : ∀ p ∈ s, ∀ q ∈ s, IntegrableOn
      (fun x => Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x
        * Work.BoseFixB1S.boxCompT volA A q.1 q.2 Φ x)
      (Submission.BoseGases.abox N ℓ) volume := by
    intro p _ q _
    obtain ⟨Cf, hCf⟩ := (hG p).2
    obtain ⟨Cg, hCg⟩ := (hG q).2
    exact Work.BoseFixB1S.integrableOn_mul_of_bound hℓ (hG p).1 (hG q).1 hCf hCg
  -- the pointwise expansion of the square into the double sum
  have hpt : ∀ x : Submission.BoseGases.X N,
      (∑ p ∈ s, Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x) ^ 2
        = ∑ p ∈ s, ∑ q ∈ s,
            Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x
              * Work.BoseFixB1S.boxCompT volA A q.1 q.2 Φ x := by
    intro x
    rw [sq, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p _
    rw [Finset.mul_sum]
  calc (∫ x in Submission.BoseGases.abox N ℓ,
          (∑ p ∈ s, Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x) ^ 2)
      = ∫ x in Submission.BoseGases.abox N ℓ, ∑ p ∈ s, ∑ q ∈ s,
          Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x
            * Work.BoseFixB1S.boxCompT volA A q.1 q.2 Φ x :=
        setIntegral_congr_fun (Submission.BoseGases.abox_measurable N ℓ)
          (fun x _ => hpt x)
    _ = ∑ p ∈ s, ∫ x in Submission.BoseGases.abox N ℓ, ∑ q ∈ s,
          Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x
            * Work.BoseFixB1S.boxCompT volA A q.1 q.2 Φ x :=
        MeasureTheory.integral_finsetSum s
          (f := fun p x => ∑ q ∈ s,
            Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x
              * Work.BoseFixB1S.boxCompT volA A q.1 q.2 Φ x)
          (fun p hp => integrable_finsetSum
            (μ := (volume : Measure (Submission.BoseGases.X N)).restrict
              (Submission.BoseGases.abox N ℓ)) s
            (f := fun q x => Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x
              * Work.BoseFixB1S.boxCompT volA A q.1 q.2 Φ x)
            (fun q hq => hprod p hp q hq))
    _ = ∑ p ∈ s, ∑ q ∈ s,
          ∫ x in Submission.BoseGases.abox N ℓ,
            Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x
              * Work.BoseFixB1S.boxCompT volA A q.1 q.2 Φ x := by
        apply Finset.sum_congr rfl
        intro p hp
        exact MeasureTheory.integral_finsetSum s
          (f := fun q x => Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x
            * Work.BoseFixB1S.boxCompT volA A q.1 q.2 Φ x)
          (fun q hq => hprod p hp q hq)
    _ = ∑ p ∈ s, ∫ x in Submission.BoseGases.abox N ℓ,
          (Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x) ^ 2 := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [Finset.sum_eq_single p]
        · apply integral_congr_ae
          filter_upwards with x
          ring
        · intro q hq hqp
          refine boxCompT_orth_good hℓ hvol hA hvolA hAc (hs p hp) (hs q hq)
            (Work.BoseFixB1S.ne_fst_or_ne_snd hqp.symm) hΦ hΦ
        · intro hpn
          exact absurd hp hpn

/-! ## 3. The `P`-component decomposition and the per-pair spectral identity -/

/-- On the analysis box, `PⱼΦ` is the sum of the three-way joint components whose `P`-slot set
contains `j`, at `GoodState` states. -/
theorem goodBoxPInd_eq_sum_disjPairs {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) {Φ : Submission.BoseGases.X N → ℝ}
    (hΦ : Work.BoseFixB1S.GoodState ℓ Φ) (j : Fin N) :
    ∀ x ∈ Submission.BoseGases.abox N ℓ,
      Work.UBBInputs8.boxPInd volA A j Φ x
        = ∑ p ∈ (Work.BoseFixB1S.disjPairs N).filter (fun p => j ∈ p.1),
            Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x := by
  intro x hx
  have hG : ∀ p : Finset (Fin N) × Finset (Fin N),
      Work.BoseFixB1S.GoodState ℓ (Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ) :=
    fun p => Work.BoseFixB1S.goodState_boxCompT hℓ hvol hA hvolA hAc p.1 p.2 hΦ
  have hsum : ∀ y ∈ Submission.BoseGases.abox N ℓ, Φ y = ∑ p ∈ Work.BoseFixB1S.disjPairs N,
      Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ y :=
    fun y hy => (goodBoxCompT_sum_eq hℓ hvol hA hvolA hAc y hy).symm
  have h1 : Work.UBBInputs8.boxPInd volA A j Φ x
      = Work.UBBInputs8.boxPInd volA A j
          (fun y => ∑ p ∈ Work.BoseFixB1S.disjPairs N,
            Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ y) x :=
    Work.BoseFixB1S.agreeBox_boxPInd hA hAc j hsum x hx
  have h2 : Work.UBBInputs8.boxPInd volA A j
        (fun y => ∑ p ∈ Work.BoseFixB1S.disjPairs N,
          Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ y) x
      = ∑ p ∈ Work.BoseFixB1S.disjPairs N,
          Work.UBBInputs8.boxPInd volA A j (Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ) x :=
    Work.BoseFixB1S.boxPInd_finset_sum_gen volA A j x (Work.BoseFixB1S.disjPairs N)
      (fun p => Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ)
      (fun p _ => Work.BoseFixB1S.slotInt_of_bound hℓ hA hAc j x hx (hG p).1
        (hG p).2.choose_spec)
  have h3 : (∑ p ∈ Work.BoseFixB1S.disjPairs N,
        Work.UBBInputs8.boxPInd volA A j (Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ) x)
      = ∑ p ∈ (Work.BoseFixB1S.disjPairs N).filter (fun p => j ∈ p.1),
          Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x := by
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl (fun p _ =>
      boxPInd_boxCompT_good hℓ hvol hA hvolA hAc p.1 p.2 hΦ j x hx)
  rw [h1, h2, h3]

/-- **The per-ordered-pair spectral identity** at `GoodState` states: on the box,
`PᵢPⱼΦ = Σ_{p : i, j ∈ p.1} ψ_p`, and the components of distinct disjoint pairs are orthogonal
there, so the box `L²`-norm of `PᵢPⱼΦ` is the sum of the squared norms of those components. -/
theorem goodBoxPairCount_pident {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) {Φ : Submission.BoseGases.X N → ℝ}
    (hΦ : Work.BoseFixB1S.GoodState ℓ Φ) (i j : Fin N) :
    (∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x) ^ 2)
      = ∑ p ∈ (Work.BoseFixB1S.disjPairs N).filter (fun p => i ∈ p.1 ∧ j ∈ p.1),
          ∫ x in Submission.BoseGases.abox N ℓ,
            (Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x) ^ 2 := by
  have hG : ∀ p : Finset (Fin N) × Finset (Fin N),
      Work.BoseFixB1S.GoodState ℓ (Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ) :=
    fun p => Work.BoseFixB1S.goodState_boxCompT hℓ hvol hA hvolA hAc p.1 p.2 hΦ
  -- the pointwise component decomposition of `PᵢPⱼΦ` on the box
  have hpt : ∀ x ∈ Submission.BoseGases.abox N ℓ,
      Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x
        = ∑ p ∈ (Work.BoseFixB1S.disjPairs N).filter (fun p => i ∈ p.1 ∧ j ∈ p.1),
            Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x := by
    intro x hx
    have hPj := goodBoxPInd_eq_sum_disjPairs hℓ hvol hA hvolA hAc hΦ j
    calc Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x
        = Work.UBBInputs8.boxPInd volA A i
            (fun y => ∑ p ∈ (Work.BoseFixB1S.disjPairs N).filter (fun p => j ∈ p.1),
              Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ y) x :=
            Work.BoseFixB1S.agreeBox_boxPInd hA hAc i hPj x hx
      _ = ∑ p ∈ (Work.BoseFixB1S.disjPairs N).filter (fun p => j ∈ p.1),
            Work.UBBInputs8.boxPInd volA A i
              (Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ) x :=
            Work.BoseFixB1S.boxPInd_finset_sum_gen volA A i x
              ((Work.BoseFixB1S.disjPairs N).filter (fun p => j ∈ p.1))
              (fun p => Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ)
              (fun p _ => Work.BoseFixB1S.slotInt_of_bound hℓ hA hAc i x hx (hG p).1
                (hG p).2.choose_spec)
      _ = ∑ p ∈ (Work.BoseFixB1S.disjPairs N).filter (fun p => j ∈ p.1),
            (if i ∈ p.1 then Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x else 0) :=
            Finset.sum_congr rfl
              (fun p _ => boxPInd_boxCompT_good hℓ hvol hA hvolA hAc p.1 p.2 hΦ i x hx)
      _ = ∑ p ∈ (Work.BoseFixB1S.disjPairs N).filter (fun p => i ∈ p.1 ∧ j ∈ p.1),
            Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x := by
            conv_lhs => rw [Finset.sum_filter (s := Work.BoseFixB1S.disjPairs N)
              (p := fun p => j ∈ p.1)
              (f := fun p => if i ∈ p.1 then
                Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x else 0)]
            conv_rhs => rw [Finset.sum_filter (s := Work.BoseFixB1S.disjPairs N)
              (p := fun p => i ∈ p.1 ∧ j ∈ p.1)
              (f := fun p => Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x)]
            apply Finset.sum_congr rfl
            intro p _
            by_cases hi : i ∈ p.1 <;> by_cases hj : j ∈ p.1 <;> simp [hi, hj]
  calc (∫ x in Submission.BoseGases.abox N ℓ,
          (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x) ^ 2)
      = ∫ x in Submission.BoseGases.abox N ℓ,
          (∑ p ∈ (Work.BoseFixB1S.disjPairs N).filter (fun p => i ∈ p.1 ∧ j ∈ p.1),
            Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x) ^ 2 :=
          setIntegral_congr_fun (Submission.BoseGases.abox_measurable N ℓ)
            (fun x hx => by rw [hpt x hx])
    _ = ∑ p ∈ (Work.BoseFixB1S.disjPairs N).filter (fun p => i ∈ p.1 ∧ j ∈ p.1),
          ∫ x in Submission.BoseGases.abox N ℓ,
            (Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x) ^ 2 :=
          goodParsevalCompT hℓ hvol hA hvolA hAc hΦ _
            (fun p hp => Work.BoseFixB1S.mem_disjPairs.mp (Finset.mem_filter.mp hp).1)

/-! ## 4. The pair-condensate count -/

theorem goodBoxPairCount_eq_sum_compT {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) {Φ : Submission.BoseGases.X N → ℝ}
    (hΦg : Work.BoseFixB1S.GoodState ℓ Φ) :
    Work.BoseFixB1S.boxPairCount volA ℓ A Φ
      = ∑ p ∈ (Finset.univ : Finset (Finset (Fin N) × Finset (Fin N))).filter
            (fun p => Disjoint p.1 p.2),
          ((p.1.card : ℝ) * ((p.1.card : ℝ) - 1))
            * ∫ x in Submission.BoseGases.abox N ℓ,
                (Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x) ^ 2 := by
  show (∑ q ∈ Submission.BoseGases.pairSet N,
      ∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxPInd volA A q.1 (Work.UBBInputs8.boxPInd volA A q.2 Φ) x) ^ 2)
    = ∑ p ∈ Work.BoseFixB1S.disjPairs N,
          ((p.1.card : ℝ) * ((p.1.card : ℝ) - 1))
            * ∫ x in Submission.BoseGases.abox N ℓ,
                (Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x) ^ 2
  calc (∑ q ∈ Submission.BoseGases.pairSet N,
        ∫ x in Submission.BoseGases.abox N ℓ,
          (Work.UBBInputs8.boxPInd volA A q.1 (Work.UBBInputs8.boxPInd volA A q.2 Φ) x) ^ 2)
      = ∑ q ∈ Submission.BoseGases.pairSet N,
          ∑ p ∈ (Work.BoseFixB1S.disjPairs N).filter (fun p => q.1 ∈ p.1 ∧ q.2 ∈ p.1),
            ∫ x in Submission.BoseGases.abox N ℓ,
              (Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x) ^ 2 :=
        Finset.sum_congr rfl
          (fun q _ => goodBoxPairCount_pident hℓ hvol hA hvolA hAc hΦg q.1 q.2)
    _ = ∑ p ∈ Work.BoseFixB1S.disjPairs N,
          ((p.1.card : ℝ) * ((p.1.card : ℝ) - 1))
            * ∫ x in Submission.BoseGases.abox N ℓ,
                (Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x) ^ 2 :=
        Work.BoseFixB1S.sum_pairSet_filter_disjPairs
          (fun p => ∫ x in Submission.BoseGases.abox N ℓ,
              (Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x) ^ 2)

end Work.BoseFixB1.SectorAux
