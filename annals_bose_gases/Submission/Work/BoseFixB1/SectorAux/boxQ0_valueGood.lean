import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB1.SectorAux.oneValueGood
import Submission.Work.BoseFixB1S.PairValueAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory
open scoped Real BigOperators

namespace Work.BoseFixB1.SectorAux

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The unconditional two-slot peel -/

/-- **The two-slot slice** with an arbitrary two-slot kernel `h`: the box integral of
`(P_iP_jΦ)²·h(x_i,x_j)` factors as the `(acube ℓ × acube ℓ)`-integral of the
indicator-weighted kernel times the `A`-double-mean square marginal.  Exterior to the kernel
nothing is assumed about `Φ`. -/
theorem pairSlice {p : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) {A : Set E3} (hA : MeasurableSet A)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) (i : Fin (p + 2)) (j' : Fin (p + 1))
    {Φ : Submission.BoseGases.X (p + 2) → ℝ} {h : E3 → E3 → ℝ} :
    (∫ x in Submission.BoseGases.abox (p + 2) ℓ,
        (Work.UBBInputs8.boxPInd volA A i
          (Work.UBBInputs8.boxPInd volA A (i.succAbove j') Φ) x) ^ 2
          * h (x i) (x (i.succAbove j')))
      = (∫ q : E3 × E3,
            A.indicator (fun _ => (1 : ℝ)) q.1 * A.indicator (fun _ => (1 : ℝ)) q.2
              * h q.1 q.2
          ∂(((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)).prod
            ((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))))
        * (∫ r2 in Submission.BoseGases.abox p ℓ,
            (Work.BoseFixB1S.Q0C.pairRest volA A i j' Φ r2) ^ 2) := by
  rw [Work.BoseFixB1S.Q0C.abox_peel2_transport (p := p) (ℓ := ℓ) hℓ i j'
    (fun x => (Work.UBBInputs8.boxPInd volA A i
        (Work.UBBInputs8.boxPInd volA A (i.succAbove j') Φ) x) ^ 2
          * h (x i) (x (i.succAbove j')))]
  have hpt : ∀ q : (E3 × E3) × Submission.BoseGases.X p,
      (Work.UBBInputs8.boxPInd volA A i
          (Work.UBBInputs8.boxPInd volA A (i.succAbove j') Φ)
          (Submission.BoseGases.ins2 i j' q.1.1 q.1.2 q.2)) ^ 2
        * h ((Submission.BoseGases.ins2 i j' q.1.1 q.1.2 q.2) i)
            ((Submission.BoseGases.ins2 i j' q.1.1 q.1.2 q.2) (i.succAbove j'))
      = (A.indicator (fun _ => (1 : ℝ)) q.1.1 * A.indicator (fun _ => (1 : ℝ)) q.1.2
          * h q.1.1 q.1.2)
        * (Work.BoseFixB1S.Q0C.pairRest volA A i j' Φ q.2) ^ 2 := by
    intro q
    rcases q with ⟨⟨y, z⟩, r2⟩
    dsimp only
    rw [Submission.BoseGases.ins2_apply_i, Submission.BoseGases.ins2_apply_succ,
      Work.BoseFixB1S.Q0C.boxPInd_pair_ins2_sq]
    ring
  have hcongr :
      (∫ q : (E3 × E3) × Submission.BoseGases.X p,
          (Work.UBBInputs8.boxPInd volA A i
              (Work.UBBInputs8.boxPInd volA A (i.succAbove j') Φ)
              (Submission.BoseGases.ins2 i j' q.1.1 q.1.2 q.2)) ^ 2
            * h ((Submission.BoseGases.ins2 i j' q.1.1 q.1.2 q.2) i)
                ((Submission.BoseGases.ins2 i j' q.1.1 q.1.2 q.2) (i.succAbove j'))
          ∂((((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)).prod
              ((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))).prod
            ((volume : Measure (Submission.BoseGases.X p)).restrict
              (Submission.BoseGases.abox p ℓ))))
        = ∫ q : (E3 × E3) × Submission.BoseGases.X p,
            ((A.indicator (fun _ => (1 : ℝ)) q.1.1 * A.indicator (fun _ => (1 : ℝ)) q.1.2
                * h q.1.1 q.1.2)
              * (Work.BoseFixB1S.Q0C.pairRest volA A i j' Φ q.2) ^ 2)
          ∂((((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)).prod
              ((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))).prod
            ((volume : Measure (Submission.BoseGases.X p)).restrict
              (Submission.BoseGases.abox p ℓ))) :=
    integral_congr_ae (Filter.Eventually.of_forall hpt)
  rw [hcongr, MeasureTheory.integral_prod_mul
    (μ := ((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)).prod
      ((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)))
    (ν := (volume : Measure (Submission.BoseGases.X p)).restrict
      (Submission.BoseGases.abox p ℓ))
    (f := fun q : E3 × E3 =>
      A.indicator (fun _ => (1 : ℝ)) q.1 * A.indicator (fun _ => (1 : ℝ)) q.2 * h q.1 q.2)
    (g := fun r2 : Submission.BoseGases.X p =>
      (Work.BoseFixB1S.Q0C.pairRest volA A i j' Φ r2) ^ 2)]

/-! ## 2. The two-slot value identity, unconditional in the state -/

/-- **The two-slot value identity for an arbitrary state.**  For distinct slots `i ≠ j` and a
kernel `w₂` integrable on `A × A`,

    ∫_{abox N ℓ}(P_iP_jΦ)²·w₂(x_i,x_j) = (∬_{A×A}w₂/volA²)·∫_{abox N ℓ}(P_iP_jΦ)² .

No measurability or boundedness of `Φ` is needed: both sides are computed from the
unconditional two-slot peel `pairSlice` and the unconditional product-measure Fubini, the two
`A`-marginals being `boxM2` (`PairValueAux.pairCollapse`) resp. `volA²`
(`PairValueAux.flatCollapse`). -/
theorem pairValueGoodUncond {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {i j : Fin N} (hij : i ≠ j)
    {w2 : E3 → E3 → ℝ}
    (hw2 : MeasureTheory.Integrable (fun p : E3 × E3 => w2 p.1 p.2)
      ((MeasureTheory.volume : MeasureTheory.Measure (E3 × E3)).restrict (A ×ˢ A)))
    {Φ : Submission.BoseGases.X N → ℝ} :
    (∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x) ^ 2
          * w2 (x i) (x j))
      = (Work.BoseFixB1S.boxM2 volA A w2 / volA ^ 2)
        * (∫ x in Submission.BoseGases.abox N ℓ,
          (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x) ^ 2) := by
  cases N with
  | zero => exact absurd i.isLt (Nat.not_lt_zero _)
  | succ n =>
    cases n with
    | zero =>
      have h1 : i.1 = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ i.isLt)
      have h2 : j.1 = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ j.isLt)
      exact absurd (Fin.ext (h1.trans h2.symm)) hij
    | succ p =>
      rcases Fin.exists_succAbove_eq (x := j) (y := i) hij.symm with ⟨j', hj'⟩
      subst hj'
      have hw := pairSlice (p := p) (ℓ := ℓ) (volA := volA) hℓ hA hAc (i := i) (j' := j')
        (Φ := Φ) (h := w2)
      have hf := pairSlice (p := p) (ℓ := ℓ) (volA := volA) hℓ hA hAc (i := i) (j' := j')
        (Φ := Φ) (h := fun _ _ => (1 : ℝ))
      have hc2 : (∫ q : E3 × E3, A.indicator (fun _ => (1 : ℝ)) q.1
            * A.indicator (fun _ => (1 : ℝ)) q.2 * w2 q.1 q.2
          ∂(((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)).prod
            ((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))))
          = Work.BoseFixB1S.boxM2 volA A w2 := by
        rw [Work.BoseFixB1S.pairCollapse hA hAc w2, Work.BoseFixB1S.boxM2]
      have hc1 : (∫ q : E3 × E3, A.indicator (fun _ => (1 : ℝ)) q.1
            * A.indicator (fun _ => (1 : ℝ)) q.2 * (fun _ _ => (1 : ℝ)) q.1 q.2
          ∂(((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)).prod
            ((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))))
          = volA ^ 2 := by
        rw [Work.BoseFixB1S.pairCollapse hA hAc (fun _ _ => (1 : ℝ))]
        exact Work.BoseFixB1S.flatCollapse hvolA
      rw [hw, hc2]
      have hflat : (∫ x in Submission.BoseGases.abox (p + 2) ℓ,
            (Work.UBBInputs8.boxPInd volA A i
              (Work.UBBInputs8.boxPInd volA A (i.succAbove j') Φ) x) ^ 2)
          = volA ^ 2 * (∫ r2 in Submission.BoseGases.abox p ℓ,
              (Work.BoseFixB1S.Q0C.pairRest volA A i j' Φ r2) ^ 2) := by
        have h1 : (∫ x in Submission.BoseGases.abox (p + 2) ℓ,
              (Work.UBBInputs8.boxPInd volA A i
                (Work.UBBInputs8.boxPInd volA A (i.succAbove j') Φ) x) ^ 2)
            = ∫ x in Submission.BoseGases.abox (p + 2) ℓ,
                (Work.UBBInputs8.boxPInd volA A i
                  (Work.UBBInputs8.boxPInd volA A (i.succAbove j') Φ) x) ^ 2
                  * (fun _ _ => (1 : ℝ)) (x i) (x (i.succAbove j')) := by
          apply integral_congr_ae
          filter_upwards with x
          simp
        rw [h1, hf, hc1]
      rw [hflat]
      have hv : volA ≠ 0 := ne_of_gt hvol
      field_simp

/-! ## 3. The target: the summed value identity -/

theorem boxQ0_valueGood {N : ℕ} {ℓ volA μ : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {w1 w2 : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hw2i : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        w2 p.1 p.2) ((MeasureTheory.volume : MeasureTheory.Measure
          (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))).restrict (A ×ˢ A)))
    (hfib : MeasureTheory.IntegrableOn (fun z : EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.w1Fibre ℓ w1 z) A)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦg : Work.BoseFixB1S.GoodState ℓ Φ) :
    Work.BoseFixB1S.boxQ0 volA ℓ μ A w1 w2 Φ
      = (1 / 2) * (Work.BoseFixB1S.boxM2 volA A w2 / volA ^ 2)
          * Work.BoseFixB1S.boxPairCount volA ℓ A Φ
        - μ * (Work.BoseFixB1S.boxM1 ℓ A w1 / volA)
          * Work.BoseFixB1S.boxFlatCount volA ℓ A Φ := by
  have hpair : (∑ p ∈ Submission.BoseGases.pairSet N,
        ∫ x in Submission.BoseGases.abox N ℓ,
          (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxPInd volA A p.2 Φ) x) ^ 2
            * w2 (x p.1) (x p.2))
      = (Work.BoseFixB1S.boxM2 volA A w2 / volA ^ 2)
        * (∑ p ∈ Submission.BoseGases.pairSet N,
            ∫ x in Submission.BoseGases.abox N ℓ,
              (Work.UBBInputs8.boxPInd volA A p.1
                (Work.UBBInputs8.boxPInd volA A p.2 Φ) x) ^ 2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hne : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
    exact pairValueGoodUncond hℓ hvol hA hvolA hAc hne hw2i
  have hone : (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2
          * Submission.BoseGases.w1Fibre ℓ w1 (x i))
      = (Work.BoseFixB1S.boxM1 ℓ A w1 / volA)
        * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => oneValueGood hℓ hvol hA hvolA hAc i hfib hΦg
  rw [Work.BoseFixB1S.boxQ0, Work.BoseFixB1S.boxPairCount, Work.BoseFixB1S.boxFlatCount,
    hpair, hone]
  ring

end Work.BoseFixB1.SectorAux
