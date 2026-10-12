import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.N0Out.pIndDoubleSumEq
import Submission.Work.BoseFixB1S.boxPairQCount_eq
import Submission.Work.BoseFixB1S.boxSqSumExpandB1
import Submission.Work.BoseFixB1S.n0BoxPIndFinsetSum
import Submission.Work.BoseFixB1S.n0ProjOpPartitionEigen
import Submission.Work.BoseFixB1S.n0SectorOrthB1
import Submission.Work.BoseFixB1S.sum_card_mul_eq_sum_j
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Work.BoseFixB1S

open Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 0. The sector functions of a box-bounded state -/

/-- The subset idempotents `n0ProjOp volA A S` preserve the class of states that are measurable
and bounded on the box (`GoodState`, the class of `boxPInd_boxComp`). -/
theorem n0ProjOp_goodStateB1 {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ acube ℓ) {Φ : X N → ℝ} (hΦG : GoodState ℓ Φ) (S : Finset (Fin N)) :
    GoodState ℓ (n0ProjOp volA A S Φ) :=
  goodState_n0Iter hℓ hvol hA hvolA hAc (fun i => decide (i ∈ S))
    (List.ofFn (fun i : Fin N => i)) hΦG

/-- Pairwise products of sector functions are integrable on the analysis box. -/
theorem n0ProjOp_pairing_integrableB1 {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ acube ℓ) {Φ : X N → ℝ} (hΦG : GoodState ℓ Φ) (S T : Finset (Fin N)) :
    IntegrableOn (fun x : X N => n0ProjOp volA A S Φ x * n0ProjOp volA A T Φ x)
      (abox N ℓ) volume :=
  integrableOn_mul_of_bound hℓ (n0ProjOp_goodStateB1 hℓ hvol hA hvolA hAc hΦG S).1
    (n0ProjOp_goodStateB1 hℓ hvol hA hvolA hAc hΦG T).1
    (n0ProjOp_goodStateB1 hℓ hvol hA hvolA hAc hΦG S).2.choose_spec
    (n0ProjOp_goodStateB1 hℓ hvol hA hvolA hAc hΦG T).2.choose_spec

/-! ## 1. The elementary reindexing `Σ_j Σ_{S ∋ j} = Σ_S |S| ·` -/

/-- Double counting: summing over the slots `j` and then over the subsets `S` containing `j` is the
same as summing over `S` with multiplicity the cardinality of `S`. -/
theorem sum_filter_sum_eq_card_mul {N : ℕ} (a : Finset (Fin N) → ℝ) :
    (∑ j : Fin N, ∑ S ∈ (Finset.univ.filter (fun S : Finset (Fin N) => j ∈ S)), a S)
      = ∑ S : Finset (Fin N), (S.card : ℝ) * a S := by
  have h1 : ∀ j : Fin N,
      (∑ S ∈ (Finset.univ.filter (fun S : Finset (Fin N) => j ∈ S)), a S)
        = ∑ S : Finset (Fin N), (if j ∈ S then a S else 0) := by
    intro j
    rw [Finset.sum_filter]
  rw [Finset.sum_congr rfl (fun j _ => h1 j), Finset.sum_comm]
  refine Finset.sum_congr rfl fun S _ => ?_
  have hpt : ∀ j : Fin N,
      (if j ∈ S then a S else 0) = (if j ∈ S then (1 : ℝ) else 0) * a S := by
    intro j
    by_cases hj : j ∈ S <;> simp [hj]
  rw [Finset.sum_congr rfl (fun j _ => hpt j), ← Finset.sum_mul,
    Work.BoseFixB1S.card_cast_eq_sum_ite_mem S]

/-! ## 2. `P_j Φ` and `n₀Φ` in terms of the sector functions -/

/-- **The one-slot identity**: on the box, the box projection `P_j` of `Φ` is the sum of the sector
functions over the subsets `S` containing `j`.  (Resolution of the identity for `Φ`, linearity of
`P_j` over the finite sum, and the eigenvalue `[j ∈ S]` of `P_j` on `u S`.) -/
theorem n0ProjOp_pInd_sum_filter {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ acube ℓ) {Φ : X N → ℝ} (hΦG : GoodState ℓ Φ) (j : Fin N) :
    ∀ x ∈ abox N ℓ,
      Work.UBBInputs8.boxPInd volA A j Φ x
        = ∑ S ∈ (Finset.univ.filter (fun S : Finset (Fin N) => j ∈ S)),
            n0ProjOp volA A S Φ x := by
  intro x hx
  have hsplit := n0BoxPIndFinsetSum hℓ hvol hA hvolA hAc
    (Finset.univ : Finset (Finset (Fin N))) (fun S => n0ProjOp volA A S Φ)
    (fun S _ => n0ProjOp_goodStateB1 hℓ hvol hA hvolA hAc hΦG S) j hx
  calc Work.UBBInputs8.boxPInd volA A j Φ x
      = Work.UBBInputs8.boxPInd volA A j
          (∑ S : Finset (Fin N), n0ProjOp volA A S Φ) x := by
        conv_lhs => rw [← n0ProjOp_sum_eq volA A Φ]
    _ = ∑ S : Finset (Fin N), Work.UBBInputs8.boxPInd volA A j (n0ProjOp volA A S Φ) x :=
        hsplit
    _ = ∑ S : Finset (Fin N), (if j ∈ S then n0ProjOp volA A S Φ x else 0) :=
        Finset.sum_congr rfl fun S _ => n0IterEigen hℓ hvol hA hvolA hAc S hΦG j x hx
    _ = ∑ S ∈ (Finset.univ.filter (fun S : Finset (Fin N) => j ∈ S)),
          n0ProjOp volA A S Φ x := by
        rw [Finset.sum_filter]

/-- **The `n₀` identity**: on the box, `n₀Φ = Σ_S |S| · u S`, i.e. the sector function `u S` is an
eigenfunction of `n₀ = Σ_j P_j` with eigenvalue the cardinality of `S`. -/
theorem n0Op_eq_sum_card_mul {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ acube ℓ) {Φ : X N → ℝ} (hΦG : GoodState ℓ Φ) :
    ∀ x ∈ abox N ℓ,
      n0Op volA A Φ x = ∑ S : Finset (Fin N), (S.card : ℝ) * n0ProjOp volA A S Φ x := by
  intro x hx
  have h0 : n0Op volA A Φ x = ∑ j : Fin N, Work.UBBInputs8.boxPInd volA A j Φ x := rfl
  have h1 : (∑ j : Fin N, Work.UBBInputs8.boxPInd volA A j Φ x)
      = ∑ j : Fin N, ∑ S ∈ (Finset.univ.filter (fun S : Finset (Fin N) => j ∈ S)),
          n0ProjOp volA A S Φ x :=
    Finset.sum_congr rfl fun j _ => n0ProjOp_pInd_sum_filter hℓ hvol hA hvolA hAc hΦG j x hx
  rw [h0, h1, sum_filter_sum_eq_card_mul (fun S => n0ProjOp volA A S Φ x)]

/-! ## 3. Parseval with weights for an orthogonal family on the box -/

/-- **Weighted Parseval**: for a pairwise orthogonal family `(f p)` on the box and real weights
`c`, the squared `L²`-norm of `Σ_p c p · f p` is the weighted sum of the squared norms.  This is
`boxSqSumExpandB1` followed by the collapse of the double sum along the diagonal. -/
theorem boxSqSumWeightedOrthB1_self {N : ℕ} {ℓ : ℝ} {ι : Type*} {s : Finset ι}
    {f : ι → X N → ℝ} {c : ι → ℝ}
    (hprod : ∀ p ∈ s, ∀ q ∈ s,
      IntegrableOn (fun x : X N => f p x * f q x) (abox N ℓ) volume)
    (horth : ∀ p ∈ s, ∀ q ∈ s, p ≠ q →
      (∫ x in abox N ℓ, f p x * f q x) = 0) :
    (∫ x in abox N ℓ, (∑ p ∈ s, c p * f p x) ^ 2)
      = ∑ p ∈ s, (c p) ^ 2 * (∫ x in abox N ℓ, (f p x) ^ 2) := by
  have hprod' : ∀ p ∈ s, ∀ q ∈ s,
      IntegrableOn (fun x : X N => (c p * f p x) * (c q * f q x)) (abox N ℓ) volume := by
    intro p hp q hq
    have h := (hprod p hp q hq).const_mul (c p * c q)
    refine h.congr ?_
    filter_upwards with x
    ring
  have horth' : ∀ p ∈ s, ∀ q ∈ s, p ≠ q →
      (∫ x in abox N ℓ, (c p * f p x) * (c q * f q x)) = 0 := by
    intro p hp q hq hpq
    have h1 : (fun x : X N => (c p * f p x) * (c q * f q x))
        = fun x : X N => (c p * c q) * (f p x * f q x) := by
      funext x
      ring
    rw [h1, integral_const_mul, horth p hp q hq hpq, mul_zero]
  rw [boxSqSumExpandB1 (s := s) (f := fun p x => c p * f p x) hprod']
  refine Finset.sum_congr rfl (fun p hp => ?_)
  rw [Finset.sum_eq_single p]
  · have h1 : (fun x : X N => (c p * f p x) * (c p * f p x))
        = fun x : X N => (c p * c p) * (f p x * f p x) := by
      funext x
      ring
    have h2 : (fun x : X N => f p x * f p x) = fun x : X N => (f p x) ^ 2 := by
      funext x
      ring
    rw [h1, integral_const_mul, h2]
    ring
  · intro q hq hqp
    exact horth' p hp q hq hqp.symm
  · intro hpn
    exact absurd hp hpn

/-! ## 4. The three moments -/

/-- **Zeroth moment**: the subset idempotents resolve the identity in `L²(abox N ℓ)`. -/
theorem n0Moments_oneB1 {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ acube ℓ) {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    (∑ S : Finset (Fin N), ∫ x in abox N ℓ, (n0ProjOp volA A S Φ x) ^ 2)
      = ∫ x in abox N ℓ, (Φ x) ^ 2 := by
  obtain ⟨C, _hC0, hCb⟩ := exists_abox_bound hℓ hΦc
  have hΦG : GoodState ℓ Φ := ⟨hΦc.measurable, C, hCb⟩
  have hpy := integral_sq_sum_of_orth (s := (Finset.univ : Finset (Finset (Fin N))))
    (f := fun S : Finset (Fin N) => n0ProjOp volA A S Φ)
    (fun p _ q _ => n0ProjOp_pairing_integrableB1 hℓ hvol hA hvolA hAc hΦG p q)
    (fun p _ q _ hpq => n0SectorOrthB1 hℓ hvol hA hvolA hAc hΦc hpq)
  refine hpy.symm.trans ?_
  apply integral_congr_ae
  filter_upwards with x
  rw [show (∑ S : Finset (Fin N), n0ProjOp volA A S Φ x) = Φ x from by
    rw [← Finset.sum_apply]
    exact congrFun (n0ProjOp_sum_eq volA A Φ) x]

/-- **First moment**: `Σ_S |S| ‖u S‖²` is the localised condensate count. -/
theorem n0Moments_twoB1 {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ acube ℓ) {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    (∑ S : Finset (Fin N), (S.card : ℝ) * ∫ x in abox N ℓ, (n0ProjOp volA A S Φ x) ^ 2)
      = boxFlatCount volA ℓ A Φ := by
  obtain ⟨C, _hC0, hCb⟩ := exists_abox_bound hℓ hΦc
  have hΦG : GoodState ℓ Φ := ⟨hΦc.measurable, C, hCb⟩
  have hper : ∀ j : Fin N,
      (∫ x in abox N ℓ, (Work.UBBInputs8.boxPInd volA A j Φ x) ^ 2)
        = ∑ S ∈ (Finset.univ.filter (fun S : Finset (Fin N) => j ∈ S)),
            ∫ x in abox N ℓ, (n0ProjOp volA A S Φ x) ^ 2 := by
    intro j
    have hpy := integral_sq_sum_of_orth
      (s := Finset.univ.filter (fun S : Finset (Fin N) => j ∈ S))
      (f := fun S : Finset (Fin N) => n0ProjOp volA A S Φ)
      (fun p _ q _ => n0ProjOp_pairing_integrableB1 hℓ hvol hA hvolA hAc hΦG p q)
      (fun p _ q _ hpq => n0SectorOrthB1 hℓ hvol hA hvolA hAc hΦc hpq)
    rw [← hpy]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (abox_measurable N ℓ)] with x hx
    rw [n0ProjOp_pInd_sum_filter hℓ hvol hA hvolA hAc hΦG j x hx]
  rw [boxFlatCount]
  rw [Finset.sum_congr rfl (fun j _ => hper j)]
  exact (sum_filter_sum_eq_card_mul
    (fun S => ∫ x in abox N ℓ, (n0ProjOp volA A S Φ x) ^ 2)).symm

/-- **The squared norm of `n₀Φ`**: `∫ (Σ_S |S| u S)² = boxFlatCount + boxPairCount`. -/
theorem n0Op_sq_integral_eq_cardB1 {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ acube ℓ) {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    (∫ x in abox N ℓ,
        (∑ S : Finset (Fin N), (S.card : ℝ) * n0ProjOp volA A S Φ x) ^ 2)
      = boxFlatCount volA ℓ A Φ + boxPairCount volA ℓ A Φ := by
  obtain ⟨C, _hC0, hCb⟩ := exists_abox_bound hℓ hΦc
  have hΦG : GoodState ℓ Φ := ⟨hΦc.measurable, C, hCb⟩
  have hPG : ∀ i : Fin N, GoodState ℓ (Work.UBBInputs8.boxPInd volA A i Φ) :=
    fun i => goodState_boxPInd hℓ hvol hA hvolA hAc i hΦG
  have hE := boxSqSumExpandB1 (s := (Finset.univ : Finset (Fin N)))
    (f := fun i : Fin N => Work.UBBInputs8.boxPInd volA A i Φ)
    (fun p _ q _ => integrableOn_mul_of_bound hℓ (hPG p).1 (hPG q).1
      (hPG p).2.choose_spec (hPG q).2.choose_spec)
  calc (∫ x in abox N ℓ,
        (∑ S : Finset (Fin N), (S.card : ℝ) * n0ProjOp volA A S Φ x) ^ 2)
      = ∫ x in abox N ℓ, (n0Op volA A Φ x) ^ 2 := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem (abox_measurable N ℓ)] with x hx
        rw [n0Op_eq_sum_card_mul hℓ hvol hA hvolA hAc hΦG x hx]
    _ = ∫ x in abox N ℓ, (∑ i : Fin N, Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2 := rfl
    _ = ∑ i : Fin N, ∑ j : Fin N,
          ∫ x in abox N ℓ,
            Work.UBBInputs8.boxPInd volA A i Φ x * Work.UBBInputs8.boxPInd volA A j Φ x := hE
    _ = boxFlatCount volA ℓ A Φ + boxPairCount volA ℓ A Φ :=
        N0Out.pIndDoubleSumEq hℓ hvol hA hvolA hAc hΦc

/-- **Second moment**, in the form of the target statement: `Σ_S |S|² ‖u S‖²` is the flat plus the
pair count. -/
theorem n0Moments_threeB1 {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ acube ℓ) {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    (∑ S : Finset (Fin N), ((S.card : ℝ) ^ 2) * ∫ x in abox N ℓ, (n0ProjOp volA A S Φ x) ^ 2)
      = boxFlatCount volA ℓ A Φ + boxPairCount volA ℓ A Φ := by
  obtain ⟨C, _hC0, hCb⟩ := exists_abox_bound hℓ hΦc
  have hΦG : GoodState ℓ Φ := ⟨hΦc.measurable, C, hCb⟩
  have hW := boxSqSumWeightedOrthB1_self (s := (Finset.univ : Finset (Finset (Fin N))))
    (f := fun S : Finset (Fin N) => n0ProjOp volA A S Φ)
    (c := fun S : Finset (Fin N) => (S.card : ℝ))
    (fun p _ q _ => n0ProjOp_pairing_integrableB1 hℓ hvol hA hvolA hAc hΦG p q)
    (fun p _ q _ hpq => n0SectorOrthB1 hℓ hvol hA hvolA hAc hΦc hpq)
  exact hW.symm.trans (n0Op_sq_integral_eq_cardB1 hℓ hvol hA hvolA hAc hΦc)

/-! ## 4. The target -/

theorem n0SpectralMomentsB1 {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) :
    (∑ S : Finset (Fin N), ∫ x in Submission.BoseGases.abox N ℓ,
        (Work.BoseFixB1S.n0ProjOp volA A S Φ x) ^ 2)
        = ∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2
    ∧ (∑ S : Finset (Fin N), (S.card : ℝ) * ∫ x in Submission.BoseGases.abox N ℓ,
        (Work.BoseFixB1S.n0ProjOp volA A S Φ x) ^ 2)
        = Work.BoseFixB1S.boxFlatCount volA ℓ A Φ
    ∧ (∑ S : Finset (Fin N), ((S.card : ℝ) ^ 2) * ∫ x in Submission.BoseGases.abox N ℓ,
        (Work.BoseFixB1S.n0ProjOp volA A S Φ x) ^ 2)
        = Work.BoseFixB1S.boxFlatCount volA ℓ A Φ
          + Work.BoseFixB1S.boxPairCount volA ℓ A Φ :=
  ⟨n0Moments_oneB1 hℓ hvol hA hvolA hAc hΦc,
    n0Moments_twoB1 hℓ hvol hA hvolA hAc hΦc,
    n0Moments_threeB1 hℓ hvol hA hvolA hAc hΦc⟩

end Work.BoseFixB1S
