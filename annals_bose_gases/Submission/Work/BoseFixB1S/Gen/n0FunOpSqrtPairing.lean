import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.n0ProjOpOrthB1
import Submission.Work.BoseFixB1S.n0SpectralMomentsB1
import Submission.Work.BoseFixB1S.n0Sqrt_quadformB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.Gen.n0FunOpSqrtPairing` — the polarised (bilinear) `√`-quadratic form of `n₀`

The corpus's `n0Sqrt_quadformB1` proves the *quadratic* form identity
`∫ (√(n₀+1)Ψ)² = ∫ Ψ·(n₀Ψ) + ∫ Ψ²` for a single state `Ψ`.  The present file proves the
**polarised** (bilinear) form, which is what the FS completion-of-squares assembly needs when the
two factors are *different* states `u`, `v`:

    ∫_{abox N ℓ} (√(n₀+1)u)·(√(n₀+1)v) = ∫_{abox N ℓ} ((n₀u) + u)·v .

## Route

`n₀ = ΣᵢP_{B,i}` (`n0Op`) is a finite sum of *commuting orthogonal projections*, so its functional
calculus is polynomial: with the subset idempotents `P_S := n0ProjOp volA A S` one has
`g(n₀) = Σ_S g(|S|)P_S` (`n0FunOp_eq_sum_card`), `Σ_S P_S = id` (`n0ProjOp_sum_eq`),
`P_S(P_SΨ) = P_SΨ` on the box (`n0ProjOp_idem`), `P_S(P_TΨ) = 0` on the box for `S ≠ T`
(`n0ProjOp_orth`) and `P_S` self-adjoint on the box (`n0Iter_selfAdjoint`, all three packaged in
`Work.BoseFixB1S.n0ProjOpOrthB1`).

Hence the mixed pairings of the idempotents are those of an orthogonal projection family:

* `n0ProjOp_pairing_diag_mixed`: `∫ (P_S u)·v = ∫ (P_S u)·(P_S v)` (self-adjointness + idempotence);
* `n0ProjOp_pairing_zero_mixed`: `∫ (P_S u)·(P_T v) = 0` for `S ≠ T` (self-adjointness +
  orthogonality).

Expanding both factors of the left-hand side with `n0FunOp_eq_sum_card` and integrating the product
of the two finite sums (`abox_integral_mul_pair_finset_sum`), the double sum collapses onto its
diagonal, and `√(|S|+1)·√(|S|+1) = |S|+1` turns the left-hand side into `Σ_S (|S|+1)∫(P_S u)(P_S v)`.
On the right-hand side, `Σ_S P_S = id` gives `∫ u·v = Σ_S ∫(P_S u)(P_S v)` and the pointwise
spectral expansion `n₀u = Σ_S |S|P_S u` (`n0Op_eq_sum_card_mul`) gives
`∫ (n₀u)·v = Σ_S |S|∫(P_S u)(P_S v)`; adding the two sums gives the same expression.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Work.BoseFixB1S.Gen

open Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1600000

/-! ## 1. The bilinear expansion of the box integral of a product of two finite sums -/

/-- **Bilinear Parseval/expansion.**  The box integral of the product of two finite linear
combinations expands into the double sum of the coefficient-weighted pairings.  This is the
two-family (bilinear) companion of `Work.BoseFixB1S.abox_integral_sq_finset_sum`; the hypothesis is
exactly the pairwise integrability of the products `f i · g j`. -/
theorem abox_integral_mul_pair_finset_sum {N : ℕ} {ℓ : ℝ} {ι : Type*} (s : Finset ι)
    (c d : ι → ℝ) (f g : ι → X N → ℝ)
    (hint : ∀ i ∈ s, ∀ j ∈ s, IntegrableOn (fun x => f i x * g j x) (abox N ℓ) volume) :
    (∫ x in abox N ℓ, (∑ i ∈ s, c i * f i x) * (∑ j ∈ s, d j * g j x))
      = ∑ i ∈ s, ∑ j ∈ s, c i * d j * (∫ x in abox N ℓ, f i x * g j x) := by
  have hint' : ∀ i ∈ s, ∀ j ∈ s,
      Integrable (fun x : X N => c i * d j * (f i x * g j x))
        ((volume : Measure (X N)).restrict (abox N ℓ)) :=
    fun i hi j hj => (hint i hi j hj).const_mul (c i * d j)
  have hpt : (fun x : X N => (∑ i ∈ s, c i * f i x) * (∑ j ∈ s, d j * g j x))
      = fun x => ∑ i ∈ s, ∑ j ∈ s, c i * d j * (f i x * g j x) := by
    funext x
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [hpt]
  rw [MeasureTheory.integral_finsetSum _
    (fun i hi => MeasureTheory.integrable_finsetSum _ (fun j hj => hint' i hi j hj))]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [MeasureTheory.integral_finsetSum _ (fun j hj => hint' i hi j hj)]
  exact Finset.sum_congr rfl fun j hj => by rw [MeasureTheory.integral_const_mul]

/-! ## 2. The mixed pairings of the `n₀` subset idempotents -/

/-- **Diagonal mixed pairing**: `∫ (P_S u)·v = ∫ (P_S u)·(P_S v)`.  Self-adjointness moves `P_S`
onto `v`, idempotence collapses `P_S(P_S v)` back to `P_S v`, and self-adjointness again returns
`P_S` to the left factor. -/
theorem n0ProjOp_pairing_diag_mixed {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (volume : Measure E3).real A)
    (hAc : A ⊆ acube ℓ)
    {u v : X N → ℝ} (hu : Work.BoseFixB1S.GoodState ℓ u)
    (hv : Work.BoseFixB1S.GoodState ℓ v) (S : Finset (Fin N)) :
    (∫ x in abox N ℓ, Work.BoseFixB1S.n0ProjOp volA A S u x * v x)
      = ∫ x in abox N ℓ,
          Work.BoseFixB1S.n0ProjOp volA A S u x
            * Work.BoseFixB1S.n0ProjOp volA A S v x := by
  have hSv : Work.BoseFixB1S.GoodState ℓ (Work.BoseFixB1S.n0ProjOp volA A S v) :=
    Work.BoseFixB1S.n0ProjOp_goodStateB1 hℓ hvol hA hvolA hAc hv S
  -- self-adjointness: `∫ (P_S u)·v = ∫ u·(P_S v)`
  have h1 : (∫ x in abox N ℓ, Work.BoseFixB1S.n0ProjOp volA A S u x * v x)
      = ∫ x in abox N ℓ, u x * Work.BoseFixB1S.n0ProjOp volA A S v x :=
    (Work.BoseFixB1S.n0ProjOpOrthB1 hℓ hvol hA hvolA hAc hu).2.2 S hu hv
  -- idempotence on the box: `P_S(P_S v) = P_S v`
  have h2 : (∫ x in abox N ℓ, u x * Work.BoseFixB1S.n0ProjOp volA A S v x)
      = ∫ x in abox N ℓ, u x
          * Work.BoseFixB1S.n0ProjOp volA A S (Work.BoseFixB1S.n0ProjOp volA A S v) x := by
    apply integral_congr_ae
    filter_upwards [self_mem_ae_restrict (abox_measurable N ℓ)] with x hx
    rw [Work.BoseFixB1S.n0ProjOp_idem hℓ hvol hA hvolA hAc S hv x hx]
  -- self-adjointness again: `∫ (P_S u)·(P_S v) = ∫ u·(P_S(P_S v))`
  have h3 : (∫ x in abox N ℓ,
        Work.BoseFixB1S.n0ProjOp volA A S u x * Work.BoseFixB1S.n0ProjOp volA A S v x)
      = ∫ x in abox N ℓ, u x
          * Work.BoseFixB1S.n0ProjOp volA A S (Work.BoseFixB1S.n0ProjOp volA A S v) x :=
    (Work.BoseFixB1S.n0ProjOpOrthB1 hℓ hvol hA hvolA hAc hu).2.2 S hu hSv
  exact h1.trans (h2.trans h3.symm)

/-- **Off-diagonal mixed pairing**: `∫ (P_S u)·(P_T v) = 0` for `S ≠ T`.  Self-adjointness moves
`P_S` onto `P_T v`, and orthogonality of the ranges (`n0ProjOp_orth`) kills `P_S(P_T v)` on the
box. -/
theorem n0ProjOp_pairing_zero_mixed {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (volume : Measure E3).real A)
    (hAc : A ⊆ acube ℓ)
    {u v : X N → ℝ} (hu : Work.BoseFixB1S.GoodState ℓ u)
    (hv : Work.BoseFixB1S.GoodState ℓ v) {S T : Finset (Fin N)} (hST : S ≠ T) :
    (∫ x in abox N ℓ,
        Work.BoseFixB1S.n0ProjOp volA A S u x
          * Work.BoseFixB1S.n0ProjOp volA A T v x) = 0 := by
  have hTv : Work.BoseFixB1S.GoodState ℓ (Work.BoseFixB1S.n0ProjOp volA A T v) :=
    Work.BoseFixB1S.n0ProjOp_goodStateB1 hℓ hvol hA hvolA hAc hv T
  have h1 : (∫ x in abox N ℓ,
        Work.BoseFixB1S.n0ProjOp volA A S u x * Work.BoseFixB1S.n0ProjOp volA A T v x)
      = ∫ x in abox N ℓ,
          u x * Work.BoseFixB1S.n0ProjOp volA A S (Work.BoseFixB1S.n0ProjOp volA A T v) x :=
    (Work.BoseFixB1S.n0ProjOpOrthB1 hℓ hvol hA hvolA hAc hu).2.2 S hu hTv
  have h0 : (∫ x in abox N ℓ,
        u x * Work.BoseFixB1S.n0ProjOp volA A S (Work.BoseFixB1S.n0ProjOp volA A T v) x)
      = ∫ x in abox N ℓ, (0 : ℝ) := by
    apply integral_congr_ae
    filter_upwards [self_mem_ae_restrict (abox_measurable N ℓ)] with x hx
    rw [Work.BoseFixB1S.n0ProjOp_orth hℓ hvol hA hvolA hAc S T hST hv x hx, mul_zero]
  rw [h1, h0]
  simp

/-! ## 3. The target -/

theorem n0FunOpSqrtPairing {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {u v : Submission.BoseGases.X N → ℝ} (huc : Continuous u) (hvc : Continuous v) :
    (∫ x in Submission.BoseGases.abox N ℓ,
        Work.BoseFixB1S.n0FunOp volA A (fun r => Real.sqrt (r + 1)) u x
          * Work.BoseFixB1S.n0FunOp volA A (fun r => Real.sqrt (r + 1)) v x)
      = ∫ x in Submission.BoseGases.abox N ℓ,
          (Work.BoseFixB1S.n0Op volA A u x + u x) * v x := by
  classical
  have huG : Work.BoseFixB1S.GoodState ℓ u := Work.BoseFixB1S.BoxNice.of_continuous hℓ huc
  have hvG : Work.BoseFixB1S.GoodState ℓ v := Work.BoseFixB1S.BoxNice.of_continuous hℓ hvc
  have hPhG : ∀ S : Finset (Fin N),
      Work.BoseFixB1S.GoodState ℓ (Work.BoseFixB1S.n0ProjOp volA A S u) :=
    fun S => Work.BoseFixB1S.n0ProjOp_goodStateB1 hℓ hvol hA hvolA hAc huG S
  have hPsG : ∀ S : Finset (Fin N),
      Work.BoseFixB1S.GoodState ℓ (Work.BoseFixB1S.n0ProjOp volA A S v) :=
    fun S => Work.BoseFixB1S.n0ProjOp_goodStateB1 hℓ hvol hA hvolA hAc hvG S
  -- integrability of the mixed products
  have hint : ∀ S T : Finset (Fin N), IntegrableOn (fun x : X N =>
      Work.BoseFixB1S.n0ProjOp volA A S u x * Work.BoseFixB1S.n0ProjOp volA A T v x)
      (abox N ℓ) volume := fun S T =>
    integrableOn_mul_of_bound hℓ (hPhG S).1 (hPsG T).1 (hPhG S).2.choose_spec (hPsG T).2.choose_spec
  have hintv : ∀ S : Finset (Fin N), IntegrableOn (fun x : X N =>
      Work.BoseFixB1S.n0ProjOp volA A S u x * v x) (abox N ℓ) volume := fun S =>
    integrableOn_mul_of_bound hℓ (hPhG S).1 hvG.1 (hPhG S).2.choose_spec hvG.2.choose_spec
  have hintuv : IntegrableOn (fun x : X N => u x * v x) (abox N ℓ) volume :=
    integrableOn_mul_of_bound hℓ huG.1 hvG.1 huG.2.choose_spec hvG.2.choose_spec
  -- `n₀u` is measurable and bounded on the box
  have hOpG : Work.BoseFixB1S.GoodState ℓ (Work.BoseFixB1S.n0Op volA A u) := by
    obtain ⟨C, hC⟩ := huG.2
    refine ⟨?_, (N : ℝ) * C, ?_⟩
    · exact Finset.measurable_sum _ (fun i _ => measurable_boxPInd volA A hA i huG.1)
    · intro x hx
      have hsum : Work.BoseFixB1S.n0Op volA A u x
          = ∑ i : Fin N, Work.UBBInputs8.boxPInd volA A i u x := rfl
      rw [hsum]
      calc |∑ i : Fin N, Work.UBBInputs8.boxPInd volA A i u x|
          ≤ ∑ i : Fin N, |Work.UBBInputs8.boxPInd volA A i u x| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin N, C :=
            Finset.sum_le_sum (fun i _ => abs_boxPInd_le hℓ hvol hA hvolA hAc i hC x hx)
        _ = (N : ℝ) * C := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hintOp : IntegrableOn (fun x : X N => Work.BoseFixB1S.n0Op volA A u x * v x)
      (abox N ℓ) volume :=
    integrableOn_mul_of_bound hℓ hOpG.1 hvG.1 hOpG.2.choose_spec hvG.2.choose_spec
  -- the functional calculus, expanded over the subset idempotents
  have hFunU : ∀ x : X N,
      Work.BoseFixB1S.n0FunOp volA A (fun r : ℝ => Real.sqrt (r + 1)) u x
        = ∑ S : Finset (Fin N),
            Real.sqrt ((S.card : ℝ) + 1) * Work.BoseFixB1S.n0ProjOp volA A S u x := fun x =>
    congrFun (Work.BoseFixB1S.n0FunOp_eq_sum_card volA A (fun r : ℝ => Real.sqrt (r + 1)) u) x
  have hFunV : ∀ x : X N,
      Work.BoseFixB1S.n0FunOp volA A (fun r : ℝ => Real.sqrt (r + 1)) v x
        = ∑ T : Finset (Fin N),
            Real.sqrt ((T.card : ℝ) + 1) * Work.BoseFixB1S.n0ProjOp volA A T v x := fun x =>
    congrFun (Work.BoseFixB1S.n0FunOp_eq_sum_card volA A (fun r : ℝ => Real.sqrt (r + 1)) v) x
  -- the pointwise spectral expansion of `n₀` and the resolution of the identity
  have hOpEq : ∀ x ∈ abox N ℓ, Work.BoseFixB1S.n0Op volA A u x
      = ∑ S : Finset (Fin N), (S.card : ℝ) * Work.BoseFixB1S.n0ProjOp volA A S u x :=
    Work.BoseFixB1S.n0Op_eq_sum_card_mul hℓ hvol hA hvolA hAc huG
  have hSumEq : ∀ x : X N, (∑ S : Finset (Fin N), Work.BoseFixB1S.n0ProjOp volA A S u x)
      = u x := fun x => by
    have h := congrFun (Work.BoseFixB1S.n0ProjOp_sum_eq volA A u) x
    simpa [Finset.sum_apply] using h
  -- ## The left-hand side
  have hLHS : (∫ x in abox N ℓ,
        Work.BoseFixB1S.n0FunOp volA A (fun r : ℝ => Real.sqrt (r + 1)) u x
          * Work.BoseFixB1S.n0FunOp volA A (fun r : ℝ => Real.sqrt (r + 1)) v x)
      = ∑ S : Finset (Fin N), ((S.card : ℝ) + 1)
          * ∫ x in abox N ℓ,
              Work.BoseFixB1S.n0ProjOp volA A S u x
                * Work.BoseFixB1S.n0ProjOp volA A S v x := by
    rw [show (fun x : X N =>
          Work.BoseFixB1S.n0FunOp volA A (fun r : ℝ => Real.sqrt (r + 1)) u x
            * Work.BoseFixB1S.n0FunOp volA A (fun r : ℝ => Real.sqrt (r + 1)) v x)
        = fun x => (∑ S : Finset (Fin N),
              Real.sqrt ((S.card : ℝ) + 1) * Work.BoseFixB1S.n0ProjOp volA A S u x)
            * (∑ T : Finset (Fin N),
              Real.sqrt ((T.card : ℝ) + 1) * Work.BoseFixB1S.n0ProjOp volA A T v x) from by
      funext x
      rw [hFunU x, hFunV x]]
    rw [abox_integral_mul_pair_finset_sum Finset.univ
      (fun S : Finset (Fin N) => Real.sqrt ((S.card : ℝ) + 1))
      (fun T : Finset (Fin N) => Real.sqrt ((T.card : ℝ) + 1))
      (fun S : Finset (Fin N) => Work.BoseFixB1S.n0ProjOp volA A S u)
      (fun T : Finset (Fin N) => Work.BoseFixB1S.n0ProjOp volA A T v)
      (fun i _ j _ => hint i j)]
    refine Finset.sum_congr rfl (fun S _ => ?_)
    rw [Finset.sum_eq_single S]
    · have hsq : Real.sqrt ((S.card : ℝ) + 1) * Real.sqrt ((S.card : ℝ) + 1)
          = (S.card : ℝ) + 1 := by
        rw [← sq, Real.sq_sqrt (by positivity)]
      rw [hsq]
    · intro T _ hTS
      rw [n0ProjOp_pairing_zero_mixed hℓ hvol hA hvolA hAc huG hvG hTS.symm, mul_zero]
    · intro hS
      exact absurd (Finset.mem_univ S) hS
  -- ## The right-hand side
  have hOpInt : (∫ x in abox N ℓ, Work.BoseFixB1S.n0Op volA A u x * v x)
      = ∑ S : Finset (Fin N), (S.card : ℝ)
          * ∫ x in abox N ℓ,
              Work.BoseFixB1S.n0ProjOp volA A S u x
                * Work.BoseFixB1S.n0ProjOp volA A S v x := by
    have h1 : (∫ x in abox N ℓ, Work.BoseFixB1S.n0Op volA A u x * v x)
        = ∫ x in abox N ℓ,
            (∑ S : Finset (Fin N),
              (S.card : ℝ) * Work.BoseFixB1S.n0ProjOp volA A S u x) * v x := by
      apply integral_congr_ae
      filter_upwards [self_mem_ae_restrict (abox_measurable N ℓ)] with x hx
      rw [hOpEq x hx]
    rw [h1]
    have h2 : (∫ x in abox N ℓ,
            (∑ S : Finset (Fin N),
              (S.card : ℝ) * Work.BoseFixB1S.n0ProjOp volA A S u x) * v x)
        = ∑ S : Finset (Fin N), (S.card : ℝ)
            * ∫ x in abox N ℓ, Work.BoseFixB1S.n0ProjOp volA A S u x * v x := by
      rw [show (fun x : X N =>
            (∑ S : Finset (Fin N),
              (S.card : ℝ) * Work.BoseFixB1S.n0ProjOp volA A S u x) * v x)
          = fun x => ∑ S : Finset (Fin N),
              (S.card : ℝ) * (Work.BoseFixB1S.n0ProjOp volA A S u x * v x) from by
        funext x
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl (fun S _ => by ring)]
      rw [MeasureTheory.integral_finsetSum]
      · exact Finset.sum_congr rfl (fun S _ => by rw [MeasureTheory.integral_const_mul])
      · intro S _
        exact (hintv S).const_mul _
    rw [h2]
    exact Finset.sum_congr rfl
      (fun S _ => by rw [n0ProjOp_pairing_diag_mixed hℓ hvol hA hvolA hAc huG hvG S])
  have huInt : (∫ x in abox N ℓ, u x * v x)
      = ∑ S : Finset (Fin N),
          ∫ x in abox N ℓ,
            Work.BoseFixB1S.n0ProjOp volA A S u x
              * Work.BoseFixB1S.n0ProjOp volA A S v x := by
    have h1 : (∫ x in abox N ℓ, u x * v x)
        = ∫ x in abox N ℓ,
            (∑ S : Finset (Fin N), Work.BoseFixB1S.n0ProjOp volA A S u x) * v x := by
      apply integral_congr_ae
      filter_upwards with x
      rw [hSumEq x]
    rw [h1]
    have h2 : (∫ x in abox N ℓ,
            (∑ S : Finset (Fin N), Work.BoseFixB1S.n0ProjOp volA A S u x) * v x)
        = ∑ S : Finset (Fin N),
            ∫ x in abox N ℓ, Work.BoseFixB1S.n0ProjOp volA A S u x * v x := by
      rw [show (fun x : X N =>
            (∑ S : Finset (Fin N), Work.BoseFixB1S.n0ProjOp volA A S u x) * v x)
          = fun x => ∑ S : Finset (Fin N),
              Work.BoseFixB1S.n0ProjOp volA A S u x * v x from by
        funext x
        rw [Finset.sum_mul]]
      exact integral_finsetSum Finset.univ (fun S _ => hintv S)
    rw [h2]
    exact Finset.sum_congr rfl
      (fun S _ => by rw [n0ProjOp_pairing_diag_mixed hℓ hvol hA hvolA hAc huG hvG S])
  -- split the right-hand side into the `n₀` part and the `u` part
  have hRHS : (∫ x in abox N ℓ, (Work.BoseFixB1S.n0Op volA A u x + u x) * v x)
      = (∫ x in abox N ℓ, Work.BoseFixB1S.n0Op volA A u x * v x)
        + ∫ x in abox N ℓ, u x * v x := by
    rw [show (fun x : X N => (Work.BoseFixB1S.n0Op volA A u x + u x) * v x)
        = fun x => Work.BoseFixB1S.n0Op volA A u x * v x + u x * v x from by
      funext x
      ring]
    exact MeasureTheory.integral_add hintOp hintuv
  rw [hLHS, hRHS, hOpInt, huInt]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun S _ => by ring)

end Work.BoseFixB1S.Gen
