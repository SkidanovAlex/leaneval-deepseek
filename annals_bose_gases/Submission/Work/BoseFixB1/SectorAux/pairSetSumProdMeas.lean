import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.boxQInd_self_boxPInd
import Submission.Work.BoseFixB1S.PQIdentAux
import Submission.Work.BoseFixB1S.boxPInd_boxComp
import Submission.Work.BoseFixB1S.boxQIndSelfAdjoint
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.SectorAux.pairSetSumProdMeas`

For the FS box projections `Pᵢ = Work.UBBInputs8.boxPInd volA A i` and
`Qᵢ = Work.UBBInputs8.boxQInd volA A i = 1_A(·ᵢ)·Φ − PᵢΦ` (`A ⊆ acube ℓ`, `volA = |A|`), the
sum over the ordered *distinct* pairs of the squared `P Q`-components equals the integral of the
product of the two total counts:

  `∑_{p ∈ pairSet N} ∫_{abox N ℓ} (P_{p.1} Q_{p.2} Φ)² = ∫_{abox N ℓ} (∑ᵢ PᵢΦ)(∑ⱼ QⱼΦ)`,

for every state `Φ` that is measurable and bounded on the analysis box.

## Math

This is the `(P,Q)`-pair identity of FS's box projections, in its "summed" form.  The two
structural facts are

* `Pᵢ` and `Qⱼ` are **self-adjoint** on `L²(abox N ℓ)` (`boxPIndSelfAdjoint`,
  `boxQIndSelfAdjoint`), stated for measurable states bounded on the box;
* `Pᵢ` is **idempotent** (`boxPInd_idempotent`), `PⱼQⱼ = 0` (`boxPInd_boxQInd_self_zero`),
  and `PᵢQⱼ = QⱼPᵢ` for `i ≠ j` (`boxPInd_boxQInd_comm_good`); and `QⱼQⱼ = Qⱼ`
  (`boxQInd_idempotent_good` below, obtained from `PⱼQⱼ = 0` and the fact that `QⱼΦ` is
  supported in `{xⱼ ∈ A}`).

With these, each off-diagonal pair contributes (`i ≠ j`)

  `∫ (PᵢQⱼΦ)² = ⟨PᵢQⱼΦ, PᵢQⱼΦ⟩ = ⟨QⱼΦ, Pᵢ(PᵢQⱼΦ)⟩ = ⟨QⱼΦ, PᵢQⱼΦ⟩`
            `= ⟨QⱼΦ, QⱼPᵢΦ⟩ = ⟨QⱼQⱼΦ, PᵢΦ⟩ = ⟨QⱼΦ, PᵢΦ⟩ = ∫ (PᵢΦ)(QⱼΦ)`

(the penultimate step is self-adjointness of `Qⱼ`, the last one idempotence of `Qⱼ`), the
diagonal terms `∫(PᵢΦ)(QᵢΦ)` vanish, and `Q0C.sum_univ_univ_eq` splits the full double sum
`∑ᵢ∑ⱼ` into the diagonal plus the `pairSet` sum.  The remaining step is linearity of the
integral over the (finite) double sum (`integral_double_sum_eq`) together with the pointwise
identity `(∑ᵢ aᵢ)(∑ⱼ bⱼ) = ∑ᵢ∑ⱼ aᵢbⱼ`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseFixB1.SectorAux

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The mean-free box projection is idempotent

`Qⱼ = 1_A(·ⱼ) − Pⱼ` is the orthogonal projection onto the complement of the box condensate
inside the `A`-slot subspace.  The two ingredients are that `QⱼΨ` is already supported in
`{xⱼ ∈ A}` (so multiplying by the indicator changes nothing) and that `Pⱼ` annihilates `QⱼΨ`
(`boxPInd_boxQInd_self_zero`). -/
theorem boxQInd_idempotent_good {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) (j : Fin N)
    {Ψ : Submission.BoseGases.X N → ℝ} (hΨ : Work.BoseFixB1S.GoodState ℓ Ψ) :
    ∀ x ∈ Submission.BoseGases.abox N ℓ,
      Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxQInd volA A j Ψ) x
        = Work.UBBInputs8.boxQInd volA A j Ψ x := by
  intro x hx
  have hP0 : Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxQInd volA A j Ψ) x = 0 :=
    Work.BoseFixB1S.boxPInd_boxQInd_self_zero hℓ hvol hA hvolA hAc j hΨ x hx
  have hsig : Work.BoseFixB1S.Aind A (x j) * Work.UBBInputs8.boxQInd volA A j Ψ x
      = Work.UBBInputs8.boxQInd volA A j Ψ x := by
    rw [Work.BoseFixB1S.boxQInd_eq volA A j Ψ x, Work.BoseFixB1S.boxPInd_eq volA A j Ψ x]
    by_cases hxj : x j ∈ A
    · rw [show Work.BoseFixB1S.Aind A (x j) = 1 from Set.indicator_of_mem hxj _]
      ring
    · rw [show Work.BoseFixB1S.Aind A (x j) = 0 from Set.indicator_of_notMem hxj _]
      ring
  rw [Work.BoseFixB1S.boxQInd_eq volA A j (Work.UBBInputs8.boxQInd volA A j Ψ) x, hsig, hP0,
    sub_zero]

/-! ## 2. The off-diagonal pair identity at bounded measurable states -/
theorem boxPInd_boxQInd_integral_eq_good {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) {i j : Fin N} (hij : i ≠ j)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦ : Work.BoseFixB1S.GoodState ℓ Φ) :
    (∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x) ^ 2)
      = ∫ x in Submission.BoseGases.abox N ℓ,
          Work.UBBInputs8.boxPInd volA A i Φ x * Work.UBBInputs8.boxQInd volA A j Φ x := by
  have hΦm : Measurable Φ := hΦ.1
  obtain ⟨CΦ, hΦb⟩ := hΦ.2
  have hQ : Work.BoseFixB1S.GoodState ℓ (Work.UBBInputs8.boxQInd volA A j Φ) :=
    Work.BoseFixB1S.goodState_boxQInd hℓ hvol hA hvolA hAc j hΦ
  have hPQ : Work.BoseFixB1S.GoodState ℓ
      (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ)) :=
    Work.BoseFixB1S.goodState_boxPInd hℓ hvol hA hvolA hAc i hQ
  have hP : Work.BoseFixB1S.GoodState ℓ (Work.UBBInputs8.boxPInd volA A i Φ) :=
    Work.BoseFixB1S.goodState_boxPInd hℓ hvol hA hvolA hAc i hΦ
  have hQm : Measurable (Work.UBBInputs8.boxQInd volA A j Φ) := hQ.1
  obtain ⟨CQ, hQb⟩ := hQ.2
  have hPQm : Measurable
      (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ)) := hPQ.1
  obtain ⟨CPQ, hPQb⟩ := hPQ.2
  have hPm : Measurable (Work.UBBInputs8.boxPInd volA A i Φ) := hP.1
  obtain ⟨CP, hPb⟩ := hP.2
  -- `Qⱼ(PᵢQⱼΦ) = PᵢQⱼΦ`
  have hQPQ : ∀ y ∈ Submission.BoseGases.abox N ℓ,
      Work.UBBInputs8.boxQInd volA A j
          (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ)) y
        = Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) y := by
    intro y hy
    rw [← Work.BoseFixB1S.boxPInd_boxQInd_comm_good hℓ hvol hA hvolA hAc hij.symm hQ y hy]
    exact Work.BoseFixB1S.agreeBox_boxPInd hA hAc i
      (fun z hz => boxQInd_idempotent_good hℓ hvol hA hvolA hAc j hΦ z hz) y hy
  -- `PᵢQⱼΦ = Qⱼ(PᵢΦ)`
  have hcomm : ∀ y ∈ Submission.BoseGases.abox N ℓ,
      Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) y
        = Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) y :=
    Work.BoseFixB1S.boxPInd_boxQInd_comm_good hℓ hvol hA hvolA hAc hij.symm hΦ
  calc (∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x) ^ 2)
      = ∫ x in Submission.BoseGases.abox N ℓ,
          Work.UBBInputs8.boxQInd volA A j Φ x
            * Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x := by
        have hsa := Work.BoseFixB1S.boxPIndSelfAdjoint hℓ hvol hA hvolA hAc i hQm hQb hPQm hPQb
        rw [show (∫ x in Submission.BoseGases.abox N ℓ,
              (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x) ^ 2)
            = ∫ x in Submission.BoseGases.abox N ℓ,
                Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x
                  * Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x from by
            apply MeasureTheory.integral_congr_ae
            filter_upwards with x
            ring]
        rw [hsa]
        apply MeasureTheory.integral_congr_ae
        filter_upwards with x
        rw [Work.BoseFixB1S.boxPInd_idempotent hℓ hvol hA hvolA hAc i
          (Work.UBBInputs8.boxQInd volA A j Φ) x]
    _ = ∫ x in Submission.BoseGases.abox N ℓ,
          Φ x * Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x := by
        have hsa :=
          Work.BoseFixB1S.boxQIndSelfAdjoint hℓ hvol hA hvolA hAc j hΦm hΦb hPQm hPQb
        rw [hsa]
        apply MeasureTheory.integral_congr_ae
        filter_upwards [MeasureTheory.self_mem_ae_restrict
          (Submission.BoseGases.abox_measurable N ℓ)] with x hx
        rw [hQPQ x hx]
    _ = ∫ x in Submission.BoseGases.abox N ℓ,
          Work.UBBInputs8.boxPInd volA A i Φ x * Work.UBBInputs8.boxQInd volA A j Φ x := by
        have hsa := Work.BoseFixB1S.boxQIndSelfAdjoint hℓ hvol hA hvolA hAc j hΦm hΦb hPm hPb
        rw [show (∫ x in Submission.BoseGases.abox N ℓ,
              Φ x * Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x)
            = ∫ x in Submission.BoseGases.abox N ℓ,
                Φ x * Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x
              from by
            apply MeasureTheory.integral_congr_ae
            filter_upwards [MeasureTheory.self_mem_ae_restrict
              (Submission.BoseGases.abox_measurable N ℓ)] with x hx
            rw [hcomm x hx]]
        rw [← hsa]
        apply MeasureTheory.integral_congr_ae
        filter_upwards with x
        ring

/-! ## 3. The diagonal pairings vanish -/
theorem boxPInd_boxQInd_diag_eq_zero_good {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) (i : Fin N)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦ : Work.BoseFixB1S.GoodState ℓ Φ) :
    (∫ x in Submission.BoseGases.abox N ℓ,
        Work.UBBInputs8.boxPInd volA A i Φ x * Work.UBBInputs8.boxQInd volA A i Φ x) = 0 := by
  obtain ⟨hΦm, CΦ, hΦb⟩ := hΦ
  have hQ : Work.BoseFixB1S.GoodState ℓ (Work.UBBInputs8.boxQInd volA A i Φ) :=
    Work.BoseFixB1S.goodState_boxQInd hℓ hvol hA hvolA hAc i ⟨hΦm, CΦ, hΦb⟩
  obtain ⟨hQm, CQ, hQb⟩ := hQ
  have hsa := Work.BoseFixB1S.boxPIndSelfAdjoint hℓ hvol hA hvolA hAc i hΦm hΦb hQm hQb
  rw [hsa]
  rw [MeasureTheory.integral_congr_ae (show (fun x : Submission.BoseGases.X N =>
        Φ x * Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A i Φ) x)
      =ᵐ[(volume : Measure (Submission.BoseGases.X N)).restrict (Submission.BoseGases.abox N ℓ)]
        (0 : Submission.BoseGases.X N → ℝ) from by
    filter_upwards [MeasureTheory.self_mem_ae_restrict
      (Submission.BoseGases.abox_measurable N ℓ)] with x hx
    rw [Work.BoseFixB1S.boxPInd_boxQInd_self_zero hℓ hvol hA hvolA hAc i ⟨hΦm, CΦ, hΦb⟩ x hx,
      mul_zero]
    simp)]
  simp

/-! ## 4. Interchanging the integral with the finite double sum -/
theorem integral_double_sum_eq {N : ℕ} {ℓ : ℝ}
    {F : Fin N → Fin N → Submission.BoseGases.X N → ℝ}
    (hF : ∀ i j, MeasureTheory.IntegrableOn (F i j)
      (Submission.BoseGases.abox N ℓ) volume) :
    (∫ x in Submission.BoseGases.abox N ℓ, ∑ i : Fin N, ∑ j : Fin N, F i j x)
      = ∑ i : Fin N, ∑ j : Fin N,
          ∫ x in Submission.BoseGases.abox N ℓ, F i j x := by
  rw [MeasureTheory.integral_finsetSum Finset.univ
    (f := fun i : Fin N => fun x : Submission.BoseGases.X N => ∑ j : Fin N, F i j x)
    (fun i _ => MeasureTheory.integrable_finsetSum Finset.univ
      (f := fun j : Fin N => fun x : Submission.BoseGases.X N => F i j x)
      (fun j _ => hF i j))]
  exact Finset.sum_congr rfl (fun i _ => MeasureTheory.integral_finsetSum Finset.univ
    (f := fun j : Fin N => fun x : Submission.BoseGases.X N => F i j x)
    (fun j _ => hF i j))

/-! ## 5. The target -/
theorem pairSetSumProdMeas {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦm : Measurable Φ) {Cb : ℝ}
    (hΦb : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Φ x| ≤ Cb) :
    (∑ p ∈ Submission.BoseGases.pairSet N,
        ∫ x in Submission.BoseGases.abox N ℓ,
          (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x) ^ 2)
      = ∫ x in Submission.BoseGases.abox N ℓ,
          (∑ i : Fin N, Work.UBBInputs8.boxPInd volA A i Φ x)
            * (∑ j : Fin N, Work.UBBInputs8.boxQInd volA A j Φ x) := by
  have hΦ : Work.BoseFixB1S.GoodState ℓ Φ := ⟨hΦm, Cb, hΦb⟩
  have hpair : ∀ p ∈ Submission.BoseGases.pairSet N,
      (∫ x in Submission.BoseGases.abox N ℓ,
          (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x) ^ 2)
        = ∫ x in Submission.BoseGases.abox N ℓ,
            Work.UBBInputs8.boxPInd volA A p.1 Φ x
              * Work.UBBInputs8.boxQInd volA A p.2 Φ x := by
    intro p hp
    exact boxPInd_boxQInd_integral_eq_good hℓ hvol hA hvolA hAc
      (Finset.mem_filter.mp hp).2 hΦ
  have hdiag : ∀ i : Fin N,
      (∫ x in Submission.BoseGases.abox N ℓ,
          Work.UBBInputs8.boxPInd volA A i Φ x
            * Work.UBBInputs8.boxQInd volA A i Φ x) = 0 :=
    fun i => boxPInd_boxQInd_diag_eq_zero_good hℓ hvol hA hvolA hAc i hΦ
  have hIj : ∀ i j : Fin N,
      MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
          Work.UBBInputs8.boxPInd volA A i Φ x * Work.UBBInputs8.boxQInd volA A j Φ x)
        (Submission.BoseGases.abox N ℓ) volume := by
    intro i j
    obtain ⟨hQm, CQ, hQb⟩ := Work.BoseFixB1S.goodState_boxQInd hℓ hvol hA hvolA hAc j hΦ
    exact Work.BoseFixB1S.integrableOn_mul_of_bound hℓ
      (Work.BoseFixB1S.measurable_boxPInd volA A hA i hΦm)
      (Work.SlotWord.measurable_boxQInd volA A hA j hΦm)
      (Work.BoseFixB1S.abs_boxPInd_le hℓ hvol hA hvolA hAc i hΦb) hQb
  rw [Finset.sum_congr rfl hpair]
  rw [show (∫ x in Submission.BoseGases.abox N ℓ,
        (∑ i : Fin N, Work.UBBInputs8.boxPInd volA A i Φ x)
          * (∑ j : Fin N, Work.UBBInputs8.boxQInd volA A j Φ x))
      = ∫ x in Submission.BoseGases.abox N ℓ,
          ∑ i : Fin N, ∑ j : Fin N,
            Work.UBBInputs8.boxPInd volA A i Φ x
              * Work.UBBInputs8.boxQInd volA A j Φ x from by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    rw [Finset.sum_mul_sum]]
  rw [integral_double_sum_eq (N := N) (ℓ := ℓ)
    (F := fun i j x =>
      Work.UBBInputs8.boxPInd volA A i Φ x * Work.UBBInputs8.boxQInd volA A j Φ x)
    (fun i j => hIj i j)]
  rw [Work.BoseFixB1S.Q0C.sum_univ_univ_eq (G := fun i j : Fin N =>
    ∫ x in Submission.BoseGases.abox N ℓ,
      Work.UBBInputs8.boxPInd volA A i Φ x * Work.UBBInputs8.boxQInd volA A j Φ x)]
  rw [Finset.sum_eq_zero (fun i _ => hdiag i), zero_add]

end Work.BoseFixB1.SectorAux
