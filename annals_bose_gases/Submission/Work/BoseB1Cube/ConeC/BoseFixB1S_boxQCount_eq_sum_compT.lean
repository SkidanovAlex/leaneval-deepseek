import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.boxCompT_orth
import Submission.Work.BoseFixB1S.boxCompT_sum_eq
import Submission.Work.BoseFixB1S.boxQInd_boxCompT
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.boxQCount_eq_sum_compT` — the spectral form of the mean-free box count

The mean-free (excited) box count

    boxQCount volA ℓ A Φ = Σᵢ ∫_{abox N ℓ} (QᵢΦ)² ,   Qᵢ = UBBInputs8.boxQInd volA A i

is the diagonal of the second-quantised number operator `n₊ = Σᵢ Qᵢ`.  The commuting family of
FS box projections `(Pᵢ, Qᵢ, Rᵢ)ᵢ` (`Rᵢ = boxOut A i = 1 − 1_A(xᵢ)`) has the three-way joint
components

    ψ_{S,T} = boxCompT volA A S T Φ ,   S ⊥ T

(`BoxSpectralDefs`), which resolve the identity on the analysis box (`boxCompT_sum_eq`) and are
pairwise orthogonal there (`boxCompT_orth`).  On the range of `boxCompT volA A S T` the operator
`n₊ = Σⱼ Qⱼ` acts by `|T|` (`boxQInd_boxCompT`), so the count is the `|T|`-weighted sum of the
squared norms of the components:

    Σᵢ ∫_{abox} (QᵢΦ)² = Σ_{(S,T), S ⊥ T} |T| · ∫_{abox} (ψ_{S,T})² .

## Proof

Everything is spectral bookkeeping around three already-delivered facts.

* **The component decomposition of `QᵢΦ`.**  Since `Φ = Σ_p ψ_p` pointwise on `abox`
  (`boxCompT_sum_eq`) and `Qᵢ` only reads the box values of its argument (`agreeBox_boxQInd`),
  the finite-sum additivity of `Qᵢ` (`boxQInd_finset_sum`, from `boxQInd_add`) and the eigenvalue
  rule `Qᵢψ_p = [i ∈ p.2]·ψ_p` (`boxQInd_boxCompT`) give the pointwise identity on the box

      QᵢΦ = Σ_{p : i ∈ p.2} ψ_p .

* **Pythagoras.**  Expanding the square of that finite sum and splitting the integral
  (`integral_finsetSum`), the cross terms `∫ ψ_p ψ_q` (`p ≠ q`) vanish by `boxCompT_orth`, leaving
  `∫ (Σ_{p : i∈p.2} ψ_p)² = Σ_{p : i∈p.2} ∫ (ψ_p)²` (`integral_sum_compT_sq`).

* **Counting.**  Summing over `i : Fin N` and exchanging the two finite sums turns the indicator
  `[i ∈ p.2]` into the cardinality `|p.2|`: `Σᵢ Σ_{p : i∈p.2} f p = Σ_p |p.2|·f p`
  (`sum_i_sum_filter_card_mul`).

The integrability side conditions are met because every component `ψ_p` is a `GoodState`
(`goodState_boxCompT`: measurable and bounded on the compact box) and `A ⊆ acube ℓ` has finite
measure, so the slot integrals of `boxQInd_add` are integrable (`slotInt_of_bound`) and every
product of two components is integrable on `abox` (`integrableOn_mul_of_bound`).
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseFixB1S

open Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## 1. The index set of the three-way decomposition -/

/-- The finset of ordered pairs `(S,T)` of **disjoint** subsets of `Fin N`: the index set of the
three-way joint decomposition of the commuting box projections. -/
def qPairSet (N : ℕ) : Finset (Finset (Fin N) × Finset (Fin N)) :=
  (Finset.univ : Finset (Finset (Fin N) × Finset (Fin N))).filter (fun p => Disjoint p.1 p.2)

/-- Membership in `qPairSet`. -/
theorem mem_qPairSet {N : ℕ} {p : Finset (Fin N) × Finset (Fin N)} :
    p ∈ qPairSet N ↔ Disjoint p.1 p.2 := by
  rw [qPairSet, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ p, h⟩⟩

/-- Two distinct pairs of slot sets differ in one of their two components. -/
theorem ne_fst_or_ne_snd {N : ℕ} {p q : Finset (Fin N) × Finset (Fin N)} (h : p ≠ q) :
    p.1 ≠ q.1 ∨ p.2 ≠ q.2 := by
  by_contra hcon
  push Not at hcon
  exact h (Prod.ext hcon.1 hcon.2)

/-! ## 2. `GoodState` is closed under finite sums -/

/-- A finite sum of `GoodState`s (measurable, bounded on the analysis box) is a `GoodState`. -/
theorem goodState_finset_sum_coneC {ι : Type*} {N : ℕ} {ℓ : ℝ} (s : Finset ι)
    {F : ι → X N → ℝ} (hF : ∀ p ∈ s, GoodState ℓ (F p)) :
    GoodState ℓ (fun y => ∑ p ∈ s, F p y) := by
  classical
  have hex : ∀ p : ι, ∃ C : ℝ,
      ∀ x ∈ abox N ℓ, |(if p ∈ s then F p x else 0)| ≤ C := by
    intro p
    by_cases hp : p ∈ s
    · obtain ⟨C, hC⟩ := (hF p hp).2
      exact ⟨C, fun x hx => by rw [if_pos hp]; exact hC x hx⟩
    · exact ⟨0, fun x hx => by rw [if_neg hp]; simp⟩
  choose C hC using hex
  refine ⟨Finset.measurable_sum s (fun p hp => (hF p hp).1), ∑ p ∈ s, C p, ?_⟩
  intro x hx
  calc |∑ p ∈ s, F p x| = |∑ p ∈ s, (if p ∈ s then F p x else 0)| := by
        congr 1
        apply Finset.sum_congr rfl
        intro p hp
        rw [if_pos hp]
    _ ≤ ∑ p ∈ s, |(if p ∈ s then F p x else 0)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ s, C p := Finset.sum_le_sum (fun p hp => hC p x hx)

/-! ## 3. Additivity of `Qᵢ` over a finite sum -/

/-- `Qᵢ` is additive over a finite sum of states, as soon as each slot function is integrable
over `A` at `x`.  (Generalisation of `Work.BoseFixB1S.boxQInd_finset_sum` to an arbitrary index
type, by the induction on the finset with `boxQInd_add`.) -/
theorem boxQInd_finset_sum_gen {ι : Type*} {N : ℕ} (volA : ℝ) (A : Set E3) (i : Fin N)
    (x : X N) (s : Finset ι) (f : ι → X N → ℝ)
    (h : ∀ j ∈ s, IntegrableOn (fun z => f j (Function.update x i z)) A volume) :
    UBBInputs8.boxQInd volA A i (fun y => ∑ j ∈ s, f j y) x
      = ∑ j ∈ s, UBBInputs8.boxQInd volA A i (f j) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [UBBInputs8.boxQInd, UBBInputs8.boxPInd]
  | insert a s ha ih =>
    have hfs : (fun y : X N => ∑ j ∈ insert a s, f j y)
        = (fun y => f a y) + (fun y => ∑ j ∈ s, f j y) := by
      funext y; rw [Finset.sum_insert ha]; rfl
    rw [hfs, boxQInd_add volA A i x (h a (Finset.mem_insert_self a s)) ?_,
      ih (fun j hj => h j (Finset.mem_insert_of_mem hj)), Finset.sum_insert ha]
    exact integrable_finsetSum (μ := (volume : Measure E3).restrict A) s
      (f := fun j => fun z : E3 => f j (Function.update x i z))
      (fun j hj => h j (Finset.mem_insert_of_mem hj))

/-! ## 4. The card counting -/

/-- Summing the inner filtered sums over `i : Fin N` and exchanging the two sums replaces the
membership indicator `[i ∈ p.2]` by the cardinality `|p.2|`. -/
theorem sum_i_sum_filter_card_mul {N : ℕ}
    (I : Finset (Finset (Fin N) × Finset (Fin N))) (f : Finset (Fin N) × Finset (Fin N) → ℝ) :
    (∑ i : Fin N, ∑ p ∈ I.filter (fun p => i ∈ p.2), f p)
      = ∑ p ∈ I, (p.2.card : ℝ) * f p := by
  classical
  calc (∑ i : Fin N, ∑ p ∈ I.filter (fun p => i ∈ p.2), f p)
      = ∑ i : Fin N, ∑ p ∈ I, (if i ∈ p.2 then f p else 0) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_filter]
    _ = ∑ p ∈ I, ∑ i : Fin N, (if i ∈ p.2 then f p else 0) := Finset.sum_comm
    _ = ∑ p ∈ I, ∑ i ∈ p.2, f p := by
        apply Finset.sum_congr rfl
        intro p _
        rw [Finset.sum_ite_mem, Finset.univ_inter]
    _ = ∑ p ∈ I, (p.2.card : ℝ) * f p := by
        apply Finset.sum_congr rfl
        intro p _
        rw [Finset.sum_const, nsmul_eq_mul]

/-! ## 5. Pythagoras for the orthogonal components -/

/-- **Parseval for the three-way components.**  For a family `s` of disjoint pairs, the squared
`L²`-norm of the sum of the components is the sum of the squared norms: the cross terms vanish by
`boxCompT_orth`. -/
theorem integral_sum_compT_sq {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (volume A).toReal)
    (hAc : A ⊆ acube ℓ) {Φ : X N → ℝ} (hΦc : Continuous Φ)
    (s : Finset (Finset (Fin N) × Finset (Fin N))) (hs : ∀ p ∈ s, Disjoint p.1 p.2) :
    (∫ x in abox N ℓ, (∑ p ∈ s, boxCompT volA A p.1 p.2 Φ x) ^ 2)
      = ∑ p ∈ s, ∫ x in abox N ℓ, (boxCompT volA A p.1 p.2 Φ x) ^ 2 := by
  have hΦG : GoodState ℓ Φ := goodState_of_continuous hℓ hΦc
  have hG : ∀ p : Finset (Fin N) × Finset (Fin N),
      GoodState ℓ (boxCompT volA A p.1 p.2 Φ) :=
    fun p => goodState_boxCompT hℓ hvol hA hvolA hAc p.1 p.2 hΦG
  -- the pairwise products of components are integrable on the box
  have hprod : ∀ p ∈ s, ∀ q ∈ s, IntegrableOn
      (fun x => boxCompT volA A p.1 p.2 Φ x * boxCompT volA A q.1 q.2 Φ x)
      (abox N ℓ) volume := by
    intro p _ q _
    obtain ⟨Cf, hCf⟩ := (hG p).2
    obtain ⟨Cg, hCg⟩ := (hG q).2
    exact integrableOn_mul_of_bound hℓ (hG p).1 (hG q).1 hCf hCg
  -- the pointwise expansion of the square into the double sum
  have hpt : ∀ x : X N,
      (∑ p ∈ s, boxCompT volA A p.1 p.2 Φ x) ^ 2
        = ∑ p ∈ s, ∑ q ∈ s,
            boxCompT volA A p.1 p.2 Φ x * boxCompT volA A q.1 q.2 Φ x := by
    intro x
    rw [sq, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p _
    rw [Finset.mul_sum]
  calc (∫ x in abox N ℓ, (∑ p ∈ s, boxCompT volA A p.1 p.2 Φ x) ^ 2)
      = ∫ x in abox N ℓ, ∑ p ∈ s, ∑ q ∈ s,
          boxCompT volA A p.1 p.2 Φ x * boxCompT volA A q.1 q.2 Φ x :=
        setIntegral_congr_fun (abox_measurable N ℓ) (fun x _ => hpt x)
    _ = ∑ p ∈ s, ∫ x in abox N ℓ, ∑ q ∈ s,
          boxCompT volA A p.1 p.2 Φ x * boxCompT volA A q.1 q.2 Φ x :=
        MeasureTheory.integral_finsetSum s
          (f := fun p x => ∑ q ∈ s,
            boxCompT volA A p.1 p.2 Φ x * boxCompT volA A q.1 q.2 Φ x)
          (fun p hp => integrable_finsetSum
            (μ := (volume : Measure (X N)).restrict (abox N ℓ)) s
            (f := fun q x => boxCompT volA A p.1 p.2 Φ x * boxCompT volA A q.1 q.2 Φ x)
            (fun q hq => hprod p hp q hq))
    _ = ∑ p ∈ s, ∑ q ∈ s,
          ∫ x in abox N ℓ, boxCompT volA A p.1 p.2 Φ x * boxCompT volA A q.1 q.2 Φ x := by
        apply Finset.sum_congr rfl
        intro p hp
        exact MeasureTheory.integral_finsetSum s
          (f := fun q x => boxCompT volA A p.1 p.2 Φ x * boxCompT volA A q.1 q.2 Φ x)
          (fun q hq => hprod p hp q hq)
    _ = ∑ p ∈ s, ∫ x in abox N ℓ, (boxCompT volA A p.1 p.2 Φ x) ^ 2 := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [Finset.sum_eq_single p]
        · apply integral_congr_ae
          filter_upwards with x
          ring
        · intro q hq hqp
          refine boxCompT_orth hℓ hvol hA hvolA hAc (hs p hp) (hs q hq)
            (ne_fst_or_ne_snd hqp.symm) hΦc hΦc
        · intro hpn
          exact absurd hp hpn

/-! ## 6. The spectral form of the count -/

theorem boxQCount_eq_sum_compT {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) {Φ : Submission.BoseGases.X N → ℝ}
    (hΦc : Continuous Φ) :
    Work.BoseFixB1S.boxQCount volA ℓ A Φ
      = ∑ p ∈ (Finset.univ : Finset (Finset (Fin N) × Finset (Fin N))).filter
            (fun p => Disjoint p.1 p.2),
          (p.2.card : ℝ)
            * ∫ x in Submission.BoseGases.abox N ℓ,
                (Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x) ^ 2 := by
  have hΦG : GoodState ℓ Φ := goodState_of_continuous hℓ hΦc
  have hG : ∀ p : Finset (Fin N) × Finset (Fin N),
      GoodState ℓ (boxCompT volA A p.1 p.2 Φ) :=
    fun p => goodState_boxCompT hℓ hvol hA hvolA hAc p.1 p.2 hΦG
  -- the master identity, stated with the local abbreviation `qPairSet`
  have master : boxQCount volA ℓ A Φ
      = ∑ p ∈ qPairSet N, (p.2.card : ℝ)
          * ∫ x in abox N ℓ, (boxCompT volA A p.1 p.2 Φ x) ^ 2 := by
    -- the pointwise component decomposition of `QᵢΦ` on the box
    have hQdecomp : ∀ i : Fin N, ∀ x ∈ abox N ℓ,
        UBBInputs8.boxQInd volA A i Φ x
          = ∑ p ∈ (qPairSet N).filter (fun p => i ∈ p.2),
              boxCompT volA A p.1 p.2 Φ x := by
      intro i x hx
      have hsum : ∀ y ∈ abox N ℓ,
          Φ y = ∑ p ∈ qPairSet N, boxCompT volA A p.1 p.2 Φ y :=
        fun y hy => (boxCompT_sum_eq hℓ hvol hA hvolA hAc hΦc y hy).symm
      have h1 : UBBInputs8.boxQInd volA A i Φ x
          = UBBInputs8.boxQInd volA A i
              (fun y => ∑ p ∈ qPairSet N, boxCompT volA A p.1 p.2 Φ y) x :=
        agreeBox_boxQInd hA hAc i hsum x hx
      have h2 : UBBInputs8.boxQInd volA A i
            (fun y => ∑ p ∈ qPairSet N, boxCompT volA A p.1 p.2 Φ y) x
          = ∑ p ∈ qPairSet N,
              UBBInputs8.boxQInd volA A i (boxCompT volA A p.1 p.2 Φ) x :=
        boxQInd_finset_sum_gen volA A i x (qPairSet N)
          (fun p => boxCompT volA A p.1 p.2 Φ)
          (fun p _ => slotInt_of_bound hℓ hA hAc i x hx (hG p).1 (hG p).2.choose_spec)
      have h3 : (∑ p ∈ qPairSet N,
            UBBInputs8.boxQInd volA A i (boxCompT volA A p.1 p.2 Φ) x)
          = ∑ p ∈ (qPairSet N).filter (fun p => i ∈ p.2),
              boxCompT volA A p.1 p.2 Φ x := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro p hp
        exact boxQInd_boxCompT hℓ hvol hA hvolA hAc (mem_qPairSet.mp hp) hΦc i x hx
      rw [h1, h2, h3]
    -- Pythagoras for each slot
    have hstep : ∀ i : Fin N,
        (∫ x in abox N ℓ, (UBBInputs8.boxQInd volA A i Φ x) ^ 2)
          = ∑ p ∈ (qPairSet N).filter (fun p => i ∈ p.2),
              ∫ x in abox N ℓ, (boxCompT volA A p.1 p.2 Φ x) ^ 2 := by
      intro i
      calc (∫ x in abox N ℓ, (UBBInputs8.boxQInd volA A i Φ x) ^ 2)
          = ∫ x in abox N ℓ,
              (∑ p ∈ (qPairSet N).filter (fun p => i ∈ p.2),
                boxCompT volA A p.1 p.2 Φ x) ^ 2 :=
            setIntegral_congr_fun (abox_measurable N ℓ) (fun x hx => by rw [hQdecomp i x hx])
        _ = ∑ p ∈ (qPairSet N).filter (fun p => i ∈ p.2),
              ∫ x in abox N ℓ, (boxCompT volA A p.1 p.2 Φ x) ^ 2 :=
            integral_sum_compT_sq hℓ hvol hA hvolA hAc hΦc _
              (fun p hp => mem_qPairSet.mp (Finset.mem_filter.mp hp).1)
    rw [boxQCount]
    calc (∑ i : Fin N, ∫ x in abox N ℓ, (UBBInputs8.boxQInd volA A i Φ x) ^ 2)
        = ∑ i : Fin N, ∑ p ∈ (qPairSet N).filter (fun p => i ∈ p.2),
            ∫ x in abox N ℓ, (boxCompT volA A p.1 p.2 Φ x) ^ 2 :=
          Finset.sum_congr rfl (fun i _ => hstep i)
      _ = ∑ p ∈ qPairSet N, (p.2.card : ℝ)
            * ∫ x in abox N ℓ, (boxCompT volA A p.1 p.2 Φ x) ^ 2 :=
          sum_i_sum_filter_card_mul (qPairSet N)
            (fun p => ∫ x in abox N ℓ, (boxCompT volA A p.1 p.2 Φ x) ^ 2)
  simpa only [qPairSet] using master

end Work.BoseFixB1S
