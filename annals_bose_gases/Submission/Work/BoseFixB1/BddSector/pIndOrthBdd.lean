import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.boxPInd_adjoint_int
import Submission.Work.BoseFixB1.boxPInd_self_idem
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.BddSector.pIndOrthBdd`

The **orthogonality of the FS box projection with its complement**, in the
*measurable/bounded-on-the-box* regularity the downstream sector argument needs.  The corpus
form `Work.BoseSplit.pIndOrth` assumes `Φ` continuous on the whole configuration space; here
`Φ` is only measurable and bounded on the box, which is exactly the hypothesis under which the
rest of the bounded-sector argument (`pairMixedBdd`, `parsevalBdd`) is run.

With `Pᵢ = Work.UBBInputs8.boxPInd volA A i` (FS `eq:HBU`:
`P_{B,i}ψ = |B|⁻¹⟨1_B,ψ⟩1_B` in slot `i`, i.e. the box indicator in slot `i` times the mean
over `A` in that slot) and `1_A(· i)Φ − PᵢΦ` the complementary piece of the decomposition
`1_A(· i)Φ = (1_A(· i)Φ − PᵢΦ) + PᵢΦ`, the claim is

  `∫_{abox N ℓ} PᵢΦ · (1_A(· i)Φ − PᵢΦ) = 0`,

the `L²`-orthogonality of that decomposition.

## Proof

* **Pointwise.**  Since `PᵢΦ` carries the box indicator in slot `i` and `1_A(x i)² = 1_A(x i)`,
  the integrand equals `Φ·PᵢΦ − (PᵢΦ)²` (`pIndOrthBdd_integrand_eq`).
* **Self-adjointness.**  `Work.BoseFixB1.boxPInd_adjoint_int` (self-adjointness of `Pᵢ` on the
  ambient box, at `L¹`-regularity in the *second* argument) applied with `f := Φ` and
  `h := PᵢΦ` gives `∫ (PᵢΦ)² = ∫ Φ·Pᵢ(PᵢΦ)`, and idempotence
  `Work.BoseFixB1.boxPInd_self_idem` turns the right-hand side into `∫ Φ·PᵢΦ`.  This is the
  `BddSector` replacement for the continuous-case `Work.BoseFixB1S.Q0C.one_self_N`.
* **Integrability.**  `Φ` is bounded on the box and `PᵢΦ` inherits that bound
  (`Work.BoseFixB1S.abs_boxPInd_le`), so `Φ·PᵢΦ` and `(PᵢΦ)²` are integrable on the box
  (`Work.BoseFixB1S.integrableOn_mul_of_bound`, `integrableOn_sq_of_bound`, the box having
  finite measure), and `integral_sub` applies.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseFixB1.BddSector

/-- **Pointwise form of the integrand.**  Because the box projection carries the box indicator
in slot `i` (`(1 − 1_A(· i))·PᵢΦ = 0`) and `1_A(x i)² = 1_A(x i)`, the integrand of
`pIndOrthBdd` equals `Φ·PᵢΦ − (PᵢΦ)²` pointwise. -/
theorem pIndOrthBdd_integrand_eq {N : ℕ} (volA : ℝ)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (i : Fin N)
    (Φ : Submission.BoseGases.X N → ℝ) (x : Submission.BoseGases.X N) :
    (Work.UBBInputs8.boxPInd volA A i Φ x)
        * ((A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x)
            - Work.UBBInputs8.boxPInd volA A i Φ x)
      = Φ x * Work.UBBInputs8.boxPInd volA A i Φ x
        - (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2 := by
  simp only [Work.UBBInputs8.boxPInd]
  by_cases h : x i ∈ A <;>
    simp [Set.indicator_of_mem, Set.indicator_of_notMem, h] <;> ring

theorem pIndOrthBdd {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) (i : Fin N)
    {Φ : Submission.BoseGases.X N → ℝ} (hm : Measurable Φ) {B : ℝ}
    (hb : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Φ x| ≤ B) :
    (∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxPInd volA A i Φ x)
          * ((A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x)
              - Work.UBBInputs8.boxPInd volA A i Φ x)) = 0 := by
  -- a nonnegative bound for `Φ` on the box
  set C : ℝ := max B 0 with hC
  have hC0 : 0 ≤ C := le_max_right _ _
  have hbc : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Φ x| ≤ C :=
    fun x hx => le_trans (hb x hx) (le_max_left _ _)
  -- measurability and box-boundedness of the projection
  have hmPi : Measurable (Work.UBBInputs8.boxPInd volA A i Φ) :=
    Work.BoseFixB1S.measurable_boxPInd volA A hA i hm
  have hbPi : ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |Work.UBBInputs8.boxPInd volA A i Φ x| ≤ C :=
    Work.BoseFixB1S.abs_boxPInd_le hℓ hvol hA hvolA hAc i hbc
  -- integrability of the two pieces on the box
  have hIntΦ : IntegrableOn (fun x : Submission.BoseGases.X N =>
      Φ x * Work.UBBInputs8.boxPInd volA A i Φ x) (Submission.BoseGases.abox N ℓ) volume :=
    Work.BoseFixB1S.integrableOn_mul_of_bound (N := N) hℓ hm hmPi hbc hbPi
  have hIntP2 : IntegrableOn (fun x : Submission.BoseGases.X N =>
      (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2) (Submission.BoseGases.abox N ℓ) volume :=
    Work.BoseFixB1S.integrableOn_sq_of_bound (N := N) hℓ hmPi hbPi
  have hIntPi : IntegrableOn (Work.UBBInputs8.boxPInd volA A i Φ)
      (Submission.BoseGases.abox N ℓ) volume := by
    refine IntegrableOn.of_bound (Submission.BoseGases.abox_lt_top N ℓ hℓ.le)
      hmPi.aestronglyMeasurable C ?_
    rw [ae_restrict_iff' (Submission.BoseGases.abox_measurable N ℓ)]
    exact ae_of_all _ (fun x hx => by rw [Real.norm_eq_abs]; exact hbPi x hx)
  -- the self-adjointness/one-slot identity `∫ Φ·PᵢΦ = ∫ (PᵢΦ)²`
  have hself : (∫ x in Submission.BoseGases.abox N ℓ,
        Φ x * Work.UBBInputs8.boxPInd volA A i Φ x)
      = ∫ x in Submission.BoseGases.abox N ℓ,
          (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2 := by
    have h := Work.BoseFixB1.boxPInd_adjoint_int (V := volA) hℓ hvol hA hvolA hAc i
      hm hC0 hbc hmPi hIntPi
    rw [Work.BoseFixB1.boxPInd_self_idem hvol hA hvolA i Φ] at h
    -- `h : ∫ (PᵢΦ)·(PᵢΦ) = ∫ Φ·(PᵢΦ)`
    rw [← h]
    refine integral_congr_ae ?_
    filter_upwards with x
    ring
  -- the pointwise rewriting of the integrand
  have hEq : (∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxPInd volA A i Φ x)
          * ((A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x)
              - Work.UBBInputs8.boxPInd volA A i Φ x))
      = ∫ x in Submission.BoseGases.abox N ℓ,
          (Φ x * Work.UBBInputs8.boxPInd volA A i Φ x
            - (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2) := by
    apply integral_congr_ae
    filter_upwards with x
    exact pIndOrthBdd_integrand_eq volA i Φ x
  rw [hEq, integral_sub hIntΦ hIntP2, hself]
  ring

end Work.BoseFixB1.BddSector
