import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.BoxOpA
import Submission.Work.BoseFixB1S.BoxPIndFlat
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1.boxOpG_one_one_flatCount`

The `(f,h) = (1,1)` specialisation of the box-generic one-slot operator `boxOpG A f h`:

  `∫_{abox (N+1) a} Ψ·boxOpG A 1 1 Ψ = volA · S`,  `S = boxFlatCount volA a A Ψ`.

The proof is a short observation.  Unfolding,

  `boxOpG A 1 1 Ψ x = Σᵢ 1_A(xᵢ)·∫_{z∈A} Ψ(x|i↦z) dz`,

and the box projection of the corpus is

  `(PᵢΨ)(x) = boxPInd volA A i Ψ x = (1/volA)·(∫_{z∈A} Ψ(x|i↦z) dz)·1_A(xᵢ)`,

so *pointwise* `1_A(xᵢ)·∫_{z∈A} Ψ(x|i↦z) dz = volA · (PᵢΨ)(x)`.  Hence the left-hand side is
`volA · Σᵢ ∫ Ψ·(PᵢΨ)`, and the two peel identities of `Work.BoseFixB1S.BoxQIndCore`

* `Work.BoseFixB1S.Q0C.one_self : ∫ Ψ·(PᵢΨ) = volA · ∫_{abox N a} (oneRest)²`,
* `Work.BoseFixB1S.Q0C.one_flat : ∫ (PᵢΨ)² = volA · ∫_{abox N a} (oneRest)²`,

give, on both sides, `Σᵢ volA² · ∫_{abox N a}(oneRest)²` — the flat count is the sum of the
squares of the box projections, which carry the same one-slot mean `oneRest` *without* the
indicator.
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators ENNReal

namespace Work.BoseFixB1

open Submission.BoseGases

set_option maxHeartbeats 800000

theorem boxOpG_one_one_flatCount {N : ℕ} {a volA : ℝ} (ha : 0 < a)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hAm : MeasurableSet A)
    (hAc : A ⊆ Submission.BoseGases.acube a)
    (hvol : volA = (MeasureTheory.volume A).toReal) (hvolpos : 0 < volA)
    {Ψ : Submission.BoseGases.X (N + 1) → ℝ} (hΨ : Continuous Ψ) :
    ∫ x in Submission.BoseGases.abox (N + 1) a,
        Ψ x * Work.BoseFixB1.boxOpG A (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) Ψ x
      = volA * Work.BoseFixB1S.boxFlatCount volA a A Ψ := by
  have hvolA : volA = (volume : Measure (EuclideanSpace ℝ (Fin 3))).real A := hvol
  have hΨm : Measurable Ψ := hΨ.measurable
  -- a bound for `Ψ` on the compact box and for the box projections
  obtain ⟨C, hC⟩ := (abox_compact (N + 1) ha).exists_bound_of_continuousOn
    (s := abox (N + 1) a) (f := Ψ) hΨ.continuousOn
  have hC0 : 0 ≤ C := le_trans (norm_nonneg (Ψ 0)) (hC 0 (zero_mem_abox (N := N + 1) ha.le))
  have hbΨ : ∀ x ∈ abox (N + 1) a, |Ψ x| ≤ C := fun x hx => by
    simpa [Real.norm_eq_abs] using hC x hx
  have hm : ∀ i : Fin (N + 1), Measurable (UBBInputs8.boxPInd volA A i Ψ) :=
    fun i => Work.BoseFixB1S.measurable_boxPInd volA A hAm i hΨm
  have hb : ∀ i : Fin (N + 1), ∀ x ∈ abox (N + 1) a,
      |UBBInputs8.boxPInd volA A i Ψ x| ≤ C :=
    fun i => Work.BoseFixB1S.abs_boxPInd_le (N := N + 1) ha hvolpos hAm hvol hAc i hbΨ
  have hint : ∀ i : Fin (N + 1),
      IntegrableOn (fun x : X (N + 1) => Ψ x * UBBInputs8.boxPInd volA A i Ψ x)
        (abox (N + 1) a) volume :=
    fun i => Work.BoseFixB1S.integrableOn_mul_of_bound ha hΨm (hm i) hbΨ (hb i)
  -- the pointwise collapse of `boxOpG A 1 1` onto the sum of the box projections
  have hne : volA ≠ 0 := ne_of_gt hvolpos
  have hpt : ∀ x : X (N + 1),
      boxOpG A (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) Ψ x
        = volA * ∑ i : Fin (N + 1), UBBInputs8.boxPInd volA A i Ψ x := by
    intro x
    rw [boxOpG, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [UBBInputs8.boxPInd]
    have hi : (∫ z in A, (1 : ℝ) * Ψ (Function.update x i z))
        = ∫ z in A, Ψ (Function.update x i z) := by
      rw [MeasureTheory.integral_const_mul]
      simp
    rw [hi]
    field_simp
  have hpt2 : ∀ x : X (N + 1),
      Ψ x * boxOpG A (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) Ψ x
        = volA * ∑ i : Fin (N + 1), (Ψ x * UBBInputs8.boxPInd volA A i Ψ x) := by
    intro x
    rw [hpt x, ← Finset.mul_sum]
    ring
  -- the left-hand side, computed as `volA · Σᵢ ∫ Ψ·PᵢΨ`
  have hL : (∫ x in abox (N + 1) a,
        Ψ x * boxOpG A (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) Ψ x)
      = volA * ∑ i : Fin (N + 1),
          (volA * ∫ r in abox N a, (Work.BoseFixB1S.Q0C.oneRest volA A i Ψ r) ^ 2) := by
    calc (∫ x in abox (N + 1) a,
            Ψ x * boxOpG A (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) Ψ x)
        = ∫ x in abox (N + 1) a,
            volA * ∑ i : Fin (N + 1), (Ψ x * UBBInputs8.boxPInd volA A i Ψ x) := by
          apply integral_congr_ae
          filter_upwards with x
          exact hpt2 x
      _ = volA * ∫ x in abox (N + 1) a,
            ∑ i : Fin (N + 1), (Ψ x * UBBInputs8.boxPInd volA A i Ψ x) := by
          rw [MeasureTheory.integral_const_mul]
      _ = volA * ∑ i : Fin (N + 1),
            ∫ x in abox (N + 1) a, (Ψ x * UBBInputs8.boxPInd volA A i Ψ x) := by
          congr 1
          rw [MeasureTheory.integral_finsetSum]
          intro i _
          exact hint i
      _ = volA * ∑ i : Fin (N + 1),
            (volA * ∫ r in abox N a, (Work.BoseFixB1S.Q0C.oneRest volA A i Ψ r) ^ 2) := by
          congr 1
          exact Finset.sum_congr rfl
            (fun i _ => Work.BoseFixB1S.Q0C.one_self ha hvolpos hAm hAc hvolA i hΨ)
  -- the right-hand side, the same sum of the same slot means
  have hR : volA * Work.BoseFixB1S.boxFlatCount volA a A Ψ
      = volA * ∑ i : Fin (N + 1),
          (volA * ∫ r in abox N a, (Work.BoseFixB1S.Q0C.oneRest volA A i Ψ r) ^ 2) := by
    congr 1
    rw [Work.BoseFixB1S.boxFlatCount]
    exact Finset.sum_congr rfl
      (fun i _ => Work.BoseFixB1S.Q0C.one_flat ha hvolpos hAm hAc hvolA i hΨ)
  exact hL.trans hR.symm

end Work.BoseFixB1
