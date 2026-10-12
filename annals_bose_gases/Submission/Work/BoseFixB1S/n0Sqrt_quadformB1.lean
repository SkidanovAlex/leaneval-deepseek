import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.abox_integral_mul_finset_sum
import Submission.Work.BoseFixB1S.abox_integral_sq_finset_sum
import Submission.Work.BoseFixB1S.n0FunOp_eq_sum_card
import Submission.Work.BoseFixB1S.n0OpEqSpectral
import Submission.Work.BoseFixB1S.n0ProjOp_pairing_sum
import Submission.Work.BoseFixB1S.n0ProjOp_pairing_zero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1S.n0Sqrt_quadformB1`

The **`√`-quadratic form of the `n₀` functional calculus** on the analysis box: for a continuous
state `Ψ` and the FS box projections `P_{B,i} = UBBInputs8.boxPInd volA A i`,

    ∫_{abox N ℓ} (√(n₀+1)Ψ)² = ∫_{abox N ℓ} Ψ·(n₀Ψ) + ∫_{abox N ℓ} Ψ² ,

i.e. the operator identity `(√(n₀+1))² = n₀ + 1` read as a quadratic form.  This is the `√`-input
consumed by the sharp completion of squares of FS `lm:appinteractionestimate`
(`FINDING_perBoxFWeightB1.md` §7.7, `fsP_creditDefs.lean`).

## Route

Write `Φ_S := n0ProjOp volA A S Ψ` for the subset idempotents.  Then

* `∑_S Φ_S = Ψ` pointwise (`n0ProjOp_sum_eq`), and
* `∫ Φ_S Φ_T = 0` for `S ≠ T` (`n0ProjOp_pairing_zero`), because a slot `j ∈ S∖T` makes
  `Φ_S = P_jΦ_S` and `P_jΦ_T = 0` on the box, and `P_j` is self-adjoint (`boxPIndSelfAdjoint`).

Hence `Φ_S` is an orthogonal family, `∫ ΨΦ_S = ∫ Φ_S²` (`n0ProjOp_pairing_sum` plus orthogonality),
and both

* `∫ Ψ·(n₀Ψ) = ∑_S (card S)·∫Φ_S²` (`n0OpEqSpectral` regrouped by subsets), and
* `∫ Ψ² = ∑_S ∫Φ_S²`

come out.  `n0FunOp_eq_sum_card` turns the functional calculus into `∑_S g(card S)·Φ_S`, so the
left side is `∑_S (card S + 1)·∫Φ_S² = ∑_S card S·∫Φ_S² + ∑_S ∫Φ_S²`.

The finite-sum/integration bookkeeping is delegated to `abox_integral_sq_finset_sum` and
`abox_integral_mul_finset_sum`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Work.BoseFixB1S

open Submission.BoseGases

set_option maxHeartbeats 1200000

/-- **Diagonal extraction from a double sum with vanishing off-diagonal terms.** -/
theorem sum_sum_eq_diag {ι : Type*} [DecidableEq ι] (s : Finset ι) (w : ι → ι → ℝ)
    (h : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → w i j = 0) :
    (∑ i ∈ s, ∑ j ∈ s, w i j) = ∑ i ∈ s, w i i := by
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_eq_single i (fun j hj hji => h i hi j hj hji.symm) (fun hi' => absurd hi hi')]

theorem n0Sqrt_quadformB1 {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {Ψ : Submission.BoseGases.X N → ℝ} (hΨc : Continuous Ψ) :
    (∫ x in Submission.BoseGases.abox N ℓ,
        (Work.BoseFixB1S.n0FunOp volA A (fun r => Real.sqrt (r + 1)) Ψ x) ^ 2)
      = (∫ x in Submission.BoseGases.abox N ℓ,
            Ψ x * (Work.BoseFixB1S.n0Op volA A Ψ x))
        + ∫ x in Submission.BoseGases.abox N ℓ, (Ψ x) ^ 2 := by
  have hΨG : GoodState ℓ Ψ := BoxNice.of_continuous hℓ hΨc
  have hΦG : ∀ S : Finset (Fin N), GoodState ℓ (n0ProjOp volA A S Ψ) := by
    intro S
    obtain ⟨hm, C, hb⟩ := BoxNice.iter hℓ hvol hA hvolA hAc (fun i : Fin N => decide (i ∈ S))
      hΨG (List.ofFn (fun i : Fin N => i))
    exact ⟨hm, C, hb⟩
  have hInt : ∀ S T : Finset (Fin N),
      IntegrableOn (fun x : X N => n0ProjOp volA A S Ψ x * n0ProjOp volA A T Ψ x)
        (abox N ℓ) volume := by
    intro S T
    obtain ⟨CS, hCS⟩ := (hΦG S).2
    obtain ⟨CT, hCT⟩ := (hΦG T).2
    exact integrableOn_mul_of_bound hℓ (hΦG S).1 (hΦG T).1 hCS hCT
  have hIntΨ : ∀ S : Finset (Fin N),
      IntegrableOn (fun x : X N => Ψ x * n0ProjOp volA A S Ψ x) (abox N ℓ) volume := by
    intro S
    obtain ⟨C, hC⟩ := hΨG.2
    obtain ⟨CS, hCS⟩ := (hΦG S).2
    exact integrableOn_mul_of_bound hℓ hΨG.1 (hΦG S).1 hC hCS
  -- ## The diagonal pairings
  have hdiag : ∀ S : Finset (Fin N),
      (∫ x in abox N ℓ, Ψ x * n0ProjOp volA A S Ψ x)
        = ∫ x in abox N ℓ, n0ProjOp volA A S Ψ x * n0ProjOp volA A S Ψ x := by
    intro S
    have hsum := n0ProjOp_pairing_sum hℓ hvol hA hvolA hAc hΨc S
    have hsingle : (∑ T : Finset (Fin N), ∫ x in abox N ℓ,
          n0ProjOp volA A T Ψ x * n0ProjOp volA A S Ψ x)
        = ∫ x in abox N ℓ, n0ProjOp volA A S Ψ x * n0ProjOp volA A S Ψ x :=
      Finset.sum_eq_single S
        (fun T _ hTS => n0ProjOp_pairing_zero hℓ hvol hA hvolA hAc hΨc hTS)
        (fun hS => absurd (Finset.mem_univ S) hS)
    rw [hsum, hsingle]
  -- ## `n₀` regrouped by subsets
  have hOpfun : (fun x : X N => ∑ k ∈ Finset.range (N + 1),
        (k : ℝ) * n0LagrangeOp volA A k Ψ x)
      = fun x => ∑ S : Finset (Fin N), (S.card : ℝ) * n0ProjOp volA A S Ψ x := by
    funext x
    have hx := congrFun (n0FunOp_eq_sum_card volA A (fun r : ℝ => r) Ψ) x
    simpa only [n0FunOp] using hx
  have hOp : (fun x : X N => n0Op volA A Ψ x) =ᵐ[volume.restrict (abox N ℓ)]
      fun x => ∑ S : Finset (Fin N), (S.card : ℝ) * n0ProjOp volA A S Ψ x :=
    (n0OpEqSpectral hℓ hvol hA hvolA hAc hΨc).trans (Filter.EventuallyEq.of_eq hOpfun)
  -- ## `∫ Ψ·(n₀Ψ)`
  have hX : (∫ x in abox N ℓ, Ψ x * n0Op volA A Ψ x)
      = ∑ S : Finset (Fin N),
          (S.card : ℝ) * ∫ x in abox N ℓ, n0ProjOp volA A S Ψ x * n0ProjOp volA A S Ψ x := by
    have hOpΨ : (fun x : X N => Ψ x * n0Op volA A Ψ x) =ᵐ[volume.restrict (abox N ℓ)]
        fun x => Ψ x * (∑ S : Finset (Fin N), (S.card : ℝ) * n0ProjOp volA A S Ψ x) := by
      filter_upwards [hOp] with x hx
      rw [hx]
    rw [integral_congr_ae hOpΨ]
    rw [abox_integral_mul_finset_sum Finset.univ Ψ (fun S : Finset (Fin N) => (S.card : ℝ))
      (fun S => n0ProjOp volA A S Ψ) (fun S _ => hIntΨ S)]
    simp_rw [hdiag]
  -- ## `∫ Ψ²`
  have hsumpt : ∀ x : X N, Ψ x = ∑ S : Finset (Fin N), n0ProjOp volA A S Ψ x := by
    intro x
    simpa only [Finset.sum_apply] using (congrFun (n0ProjOp_sum_eq volA A Ψ) x).symm
  have hPsi2 : (∫ x in abox N ℓ, (Ψ x) ^ 2)
      = ∑ S : Finset (Fin N),
          ∫ x in abox N ℓ, n0ProjOp volA A S Ψ x * n0ProjOp volA A S Ψ x := by
    have h1 : (∫ x in abox N ℓ, (Ψ x) ^ 2)
        = ∫ x in abox N ℓ,
            Ψ x * (∑ S : Finset (Fin N), (1 : ℝ) * n0ProjOp volA A S Ψ x) := by
      apply integral_congr_ae
      filter_upwards with x
      have h1x : (∑ S : Finset (Fin N), (1 : ℝ) * n0ProjOp volA A S Ψ x) = Ψ x := by
        rw [hsumpt x]
        simp only [one_mul]
      rw [h1x, pow_two]
    rw [h1]
    rw [abox_integral_mul_finset_sum Finset.univ Ψ (fun _ : Finset (Fin N) => (1 : ℝ))
      (fun S => n0ProjOp volA A S Ψ) (fun S _ => hIntΨ S)]
    simp only [one_mul]
    simp_rw [hdiag]
  -- ## `∫ (√(n₀+1)Ψ)²`
  have hexpand : ∀ x : X N, n0FunOp volA A (fun r : ℝ => Real.sqrt (r + 1)) Ψ x
      = ∑ S : Finset (Fin N),
          Real.sqrt ((S.card : ℝ) + 1) * (n0ProjOp volA A S Ψ x) := fun x => by
    have h := congrFun (n0FunOp_eq_sum_card volA A (fun r : ℝ => Real.sqrt (r + 1)) Ψ) x
    simpa using h
  have hLHS : (∫ x in abox N ℓ, (n0FunOp volA A (fun r : ℝ => Real.sqrt (r + 1)) Ψ x) ^ 2)
      = ∑ S : Finset (Fin N),
          ((S.card : ℝ) + 1) * ∫ x in abox N ℓ,
            n0ProjOp volA A S Ψ x * n0ProjOp volA A S Ψ x := by
    simp_rw [hexpand]
    rw [abox_integral_sq_finset_sum Finset.univ
      (fun S : Finset (Fin N) => Real.sqrt ((S.card : ℝ) + 1))
      (fun S => n0ProjOp volA A S Ψ) (fun i _ j _ => hInt i j)]
    rw [sum_sum_eq_diag Finset.univ
      (fun i j : Finset (Fin N) =>
        Real.sqrt ((i.card : ℝ) + 1) * Real.sqrt ((j.card : ℝ) + 1)
          * ∫ x in abox N ℓ, n0ProjOp volA A i Ψ x * n0ProjOp volA A j Ψ x)
      (fun i _ j _ hij => by
        rw [n0ProjOp_pairing_zero hℓ hvol hA hvolA hAc hΨc hij, mul_zero])]
    apply Finset.sum_congr rfl
    intro S _
    have hsq : Real.sqrt ((S.card : ℝ) + 1) * Real.sqrt ((S.card : ℝ) + 1)
        = (S.card : ℝ) + 1 := by
      rw [← sq, Real.sq_sqrt (by positivity)]
    rw [hsq]
  -- ## Assemble
  rw [hLHS, hX, hPsi2]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro S _
  ring

end Work.BoseFixB1S
