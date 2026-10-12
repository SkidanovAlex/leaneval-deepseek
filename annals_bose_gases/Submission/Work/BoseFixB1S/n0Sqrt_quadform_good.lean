import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.Gen.n0FunOpSqrtPairing
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1S.n0Sqrt_quadform_good`

The **`√`-quadratic form of the `n₀` functional calculus** on the analysis box, in the form needed
by the FS completion of squares: for a state `Ψ` that is only assumed to be *measurable and bounded
on the box* (`GoodState ℓ Ψ`, the class of `boxPInd_boxComp`) and the FS box projections
`P_{B,i} = UBBInputs8.boxPInd volA A i`,

    ∫_{abox N ℓ} (√(n₀+1)Ψ)² = ∫_{abox N ℓ} Ψ·(n₀Ψ) + ∫_{abox N ℓ} Ψ² ,

i.e. the operator identity `(√(n₀+1))² = n₀ + 1` read as a quadratic form.

This is the `GoodState`-hypothesis strengthening of `Work.BoseFixB1S.n0Sqrt_quadformB1`, whose
statement assumes `Continuous Ψ`.  The continuity hypothesis in that proof enters **only** through
the supply of a box bound (`BoxNice.of_continuous`, and `GoodState`/`BoxNice` are the *same*
definition), so the whole argument runs verbatim on the class `GoodState`:

* `n0ProjOp_goodStateB1` — the subset idempotents `P_S := n0ProjOp volA A S` preserve `GoodState`;
* `Gen.n0ProjOp_pairing_diag_mixed` — `∫ (P_S u)·v = ∫ (P_S u)·(P_S v)` for box-bounded `u`, `v`
  (self-adjointness of `P_S`, `n0ProjOpOrthB1`, plus idempotence), which yields the diagonal
  pairing `∫ Ψ·(P_S Ψ) = ∫ (P_S Ψ)²`;  the off-diagonal pairings vanish by
  `Gen.n0ProjOp_pairing_zero_mixed` (only needed for the polarised form);
* `n0Op_eq_sum_card_mul` — the pointwise spectral expansion `n₀Ψ = Σ_S |S|·(P_S Ψ)` on the box;
* `n0ProjOp_sum_eq` (unconditional) — the resolution of the identity `Σ_S P_S Ψ = Ψ`, hence
  `∫ Ψ² = Σ_S ∫ (P_S Ψ)²`;
* `n0FunOp_eq_sum_card` (unconditional) — `√(n₀+1)Ψ = Σ_S √(|S|+1)·(P_S Ψ)`, so by the squared-sum
  expansion `abox_integral_sq_finset_sum` plus orthogonality the left-hand side is
  `Σ_S (|S|+1)·∫(P_S Ψ)²`.

Adding the two right-hand sums gives the identity term by term with `√(k+1)² = k+1`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Work.BoseFixB1S

open Submission.BoseGases

set_option maxHeartbeats 1200000

theorem n0Sqrt_quadform_good {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {Ψ : Submission.BoseGases.X N → ℝ} (hΨ : Work.BoseFixB1S.GoodState ℓ Ψ) :
    (∫ x in Submission.BoseGases.abox N ℓ,
        (Work.BoseFixB1S.n0FunOp volA A (fun r => Real.sqrt (r + 1)) Ψ x) ^ 2)
      = (∫ x in Submission.BoseGases.abox N ℓ, Ψ x * (Work.BoseFixB1S.n0Op volA A Ψ x))
        + ∫ x in Submission.BoseGases.abox N ℓ, (Ψ x) ^ 2 := by
  have hΨG : GoodState ℓ Ψ := hΨ
  have hΦG : ∀ S : Finset (Fin N), GoodState ℓ (n0ProjOp volA A S Ψ) := fun S =>
    n0ProjOp_goodStateB1 hℓ hvol hA hvolA hAc hΨ S
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
    have h := Gen.n0ProjOp_pairing_diag_mixed hℓ hvol hA hvolA hAc hΨG hΨG S
    have hcomm : (∫ x in abox N ℓ, Ψ x * n0ProjOp volA A S Ψ x)
        = ∫ x in abox N ℓ, n0ProjOp volA A S Ψ x * Ψ x := by
      apply integral_congr_ae
      filter_upwards with x
      ring
    rw [hcomm, h]
  -- ## `n₀` regrouped by subsets
  have hOppt : ∀ x ∈ abox N ℓ,
      n0Op volA A Ψ x = ∑ S : Finset (Fin N), (S.card : ℝ) * n0ProjOp volA A S Ψ x :=
    n0Op_eq_sum_card_mul hℓ hvol hA hvolA hAc hΨG
  have hOp : (fun x : X N => n0Op volA A Ψ x) =ᵐ[volume.restrict (abox N ℓ)]
      fun x => ∑ S : Finset (Fin N), (S.card : ℝ) * n0ProjOp volA A S Ψ x := by
    filter_upwards [self_mem_ae_restrict (abox_measurable N ℓ)] with x hx
    exact hOppt x hx
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
        rw [Gen.n0ProjOp_pairing_zero_mixed hℓ hvol hA hvolA hAc hΨG hΨG hij, mul_zero])]
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
