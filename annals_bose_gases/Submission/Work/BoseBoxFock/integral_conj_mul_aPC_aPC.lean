import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.aPCPairAlg
import Submission.Work.BoseBoxFock.integrableOn_aPC_aPC
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.integral_conj_mul_aPC_aPC`

The **pair-slot projection identity** on the box: for a state `Θ` that is `L^∞` on the
configuration space (and supported in the box), the double slot mean `P_i P_j Θ`
(`P_i = aPC ℓ i`) satisfies

  `∫_{abox d ℓ} conj Θ · P_i P_j Θ = ‖P_i P_j Θ‖²`-mass `= ↑(∫_{abox d ℓ} ‖P_i P_j Θ‖²)`,

together with the integrability of the left-hand integrand.  This is the per-pair row of the
box-side dictionary `⟨Θ, (Σ_i uSlot_i)(Σ_j uSlot_j) Θ⟩ = cS1C + cS2C` and the input of the
box ↔ model comparison for the pair-excitation count.

## The mathematics

`P_i` is idempotent (`aPC_idem`) and symmetric on the box (`aPC_sym_box`), hence an
orthogonal projection onto the functions constant in the `i`-th slot.  Let

  `Ξ := P_j Θ`,   `Π := P_i Ξ = P_i P_j Θ`.

* `Π` is invariant in the `j`-th coordinate (`aPC_aPC_invariant`), so `P_j Π = Π`
  (`aPC_of_invariant`);  `P_i Π = Π` is `aPC_idem`.
* Symmetry of `P_j` (`setIntegral_conj_aPC_mul_eq` below, with `P_j (conj Θ) = conj (P_j Θ)`):
  `∫ conj Θ · Π = ∫ conj Θ · P_j Π = ∫ P_j (conj Θ) · Π = ∫ conj Ξ · Π`.
* Symmetry of `P_i` (same helper): `∫ conj Ξ · Π = ∫ conj Ξ · P_i Π = ∫ P_i (conj Ξ) · Π
  = ∫ conj Π · Π`.
* Finally `conj Π · Π = ↑‖Π‖²` pointwise (`Complex.conj_mul'`) and `integral_ofReal`.

All the integrability bookkeeping (`L^∞` state, `aPC` of an a.e. bounded strongly measurable
state stays a.e. bounded and a.e. strongly measurable) is `L^1`-bookkeeping on a finite measure
box: `integrableOn_aPC_mul_of_bound` for the two pairings entering the symmetry, and
`integrableOn_conj_mul_aPC_aPC_of_bound` for the statement's own integrand.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock

open Work.BoseDict

set_option linter.unusedVariables false

/-! ## 1. Symmetry of the slot mean on the box, in `L^∞` form

`aPC_sym_box` is stated with the two pairings as explicit integrability hypotheses; here we
discharge them from global a.e. bounds, which is the form in which the pair identity consumes
the symmetry (twice, once for `j` and once for `i`). -/

theorem setIntegral_conj_aPC_mul_eq {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Φ Ψ : Xn N → ℂ} {C₁ C₂ : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hΦm : AEStronglyMeasurable Φ (volume : Measure (Xn N)))
    (hΦb : ∀ᵐ x ∂(volume : Measure (Xn N)), ‖Φ x‖ ≤ C₁)
    (hΨm : AEStronglyMeasurable Ψ (volume : Measure (Xn N)))
    (hΨb : ∀ᵐ x ∂(volume : Measure (Xn N)), ‖Ψ x‖ ≤ C₂) (i : Fin N) :
    IntegrableOn (fun x => (starRingEnd ℂ) (aPC ℓ i Φ x) * Ψ x)
        (Submission.BoseGases.abox N ℓ) volume
      ∧ IntegrableOn (fun x => (starRingEnd ℂ) (Φ x) * aPC ℓ i Ψ x)
        (Submission.BoseGases.abox N ℓ) volume
      ∧ (∫ x in Submission.BoseGases.abox N ℓ, (starRingEnd ℂ) (aPC ℓ i Φ x) * Ψ x)
        = ∫ x in Submission.BoseGases.abox N ℓ, (starRingEnd ℂ) (Φ x) * aPC ℓ i Ψ x := by
  have hΦb' : ∀ᵐ x ∂(volume : Measure (Xn N)), ‖(starRingEnd ℂ) (Φ x)‖ ≤ C₁ := by
    filter_upwards [hΦb] with x hx
    simpa using hx
  obtain ⟨hI1, hI2⟩ := integrableOn_aPC_mul_of_bound (Φ := fun x => (starRingEnd ℂ) (Φ x))
    (Ψ := Ψ) hℓ hC₁ hC₂ hΦm.star hΦb' hΨm hΨb i
  have hI1' : IntegrableOn (fun x => (starRingEnd ℂ) (aPC ℓ i Φ x) * Ψ x)
      (Submission.BoseGases.abox N ℓ) volume :=
    hI1.congr_fun (fun x _ => by rw [aPC_conj]) (Submission.BoseGases.abox_measurable N ℓ)
  have hsym : (∫ x in Submission.BoseGases.abox N ℓ,
        aPC ℓ i (fun x => (starRingEnd ℂ) (Φ x)) x * Ψ x)
      = ∫ x in Submission.BoseGases.abox N ℓ, (starRingEnd ℂ) (Φ x) * aPC ℓ i Ψ x :=
    aPC_sym_box i hI1 hI2
  exact ⟨hI1', hI2, by
    calc ∫ x in Submission.BoseGases.abox N ℓ, (starRingEnd ℂ) (aPC ℓ i Φ x) * Ψ x
        = ∫ x in Submission.BoseGases.abox N ℓ,
            aPC ℓ i (fun x => (starRingEnd ℂ) (Φ x)) x * Ψ x := by
          apply setIntegral_congr_fun (Submission.BoseGases.abox_measurable N ℓ)
          intro x _
          rw [aPC_conj]
      _ = ∫ x in Submission.BoseGases.abox N ℓ, (starRingEnd ℂ) (Φ x) * aPC ℓ i Ψ x := hsym⟩

/-! ## 2. The pair identity from an a.e. bound -/

theorem integral_conj_mul_aPC_aPC_of_aesm_bound {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Θ : Xn N → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hΘm : AEStronglyMeasurable Θ (volume : Measure (Xn N)))
    (hΘb : ∀ᵐ x ∂(volume : Measure (Xn N)), ‖Θ x‖ ≤ C) (i j : Fin N) :
    IntegrableOn (fun x => (starRingEnd ℂ) (Θ x) * aPC ℓ i (aPC ℓ j Θ) x)
        (Submission.BoseGases.abox N ℓ) volume
      ∧ (∫ x in Submission.BoseGases.abox N ℓ,
          (starRingEnd ℂ) (Θ x) * aPC ℓ i (aPC ℓ j Θ) x)
        = ((∫ x in Submission.BoseGases.abox N ℓ,
            ‖aPC ℓ i (aPC ℓ j Θ) x‖ ^ 2 : ℝ) : ℂ) := by
  have hSm : AEStronglyMeasurable (aPC ℓ j Θ) (volume : Measure (Xn N)) :=
    aPC_aesm_full ℓ j hΘm
  have hSb : ∀ᵐ x ∂(volume : Measure (Xn N)), ‖aPC ℓ j Θ x‖ ≤ C :=
    aPC_ae_bound_full ℓ hℓ j hC hΘb
  have hPm : AEStronglyMeasurable (aPC ℓ i (aPC ℓ j Θ)) (volume : Measure (Xn N)) :=
    aPC_aesm_full ℓ i hSm
  have hPb : ∀ᵐ x ∂(volume : Measure (Xn N)), ‖aPC ℓ i (aPC ℓ j Θ) x‖ ≤ C :=
    aPC_ae_bound_full ℓ hℓ i hC hSb
  -- the two invariance facts: `P_j Π = Π` and `P_i Π = Π` for `Π = P_i P_j Θ`
  have hPjP : aPC ℓ j (aPC ℓ i (aPC ℓ j Θ)) = aPC ℓ i (aPC ℓ j Θ) :=
    aPC_of_invariant hℓ j (fun x w => aPC_aPC_invariant hℓ i j x w)
  have hPiP : aPC ℓ i (aPC ℓ i (aPC ℓ j Θ)) = aPC ℓ i (aPC ℓ j Θ) := aPC_idem hℓ i
  -- symmetry of `P_j`, then of `P_i`
  obtain ⟨hI1, hI2, hEq1⟩ := setIntegral_conj_aPC_mul_eq hℓ hC hC hΘm hΘb hPm hPb j
  obtain ⟨hJ1, hJ2, hEq2⟩ := setIntegral_conj_aPC_mul_eq (Φ := aPC ℓ j Θ)
    (Ψ := aPC ℓ i (aPC ℓ j Θ)) hℓ hC hC hSm hSb hPm hPb i
  have hAB : (∫ x in Submission.BoseGases.abox N ℓ,
        (starRingEnd ℂ) (Θ x) * aPC ℓ i (aPC ℓ j Θ) x)
      = ∫ x in Submission.BoseGases.abox N ℓ, (starRingEnd ℂ) (aPC ℓ j Θ x)
        * aPC ℓ i (aPC ℓ j Θ) x := by
    simpa only [hPjP] using hEq1.symm
  have hBC : (∫ x in Submission.BoseGases.abox N ℓ, (starRingEnd ℂ) (aPC ℓ j Θ x)
        * aPC ℓ i (aPC ℓ j Θ) x)
      = ∫ x in Submission.BoseGases.abox N ℓ, (starRingEnd ℂ) (aPC ℓ i (aPC ℓ j Θ) x)
        * aPC ℓ i (aPC ℓ j Θ) x := by
    simpa only [hPiP] using hEq2.symm
  refine ⟨?_, ?_⟩
  · simpa only [hPjP] using hI2
  · calc ∫ x in Submission.BoseGases.abox N ℓ, (starRingEnd ℂ) (Θ x) * aPC ℓ i (aPC ℓ j Θ) x
        = ∫ x in Submission.BoseGases.abox N ℓ, (starRingEnd ℂ) (aPC ℓ j Θ x)
            * aPC ℓ i (aPC ℓ j Θ) x := hAB
      _ = ∫ x in Submission.BoseGases.abox N ℓ, (starRingEnd ℂ) (aPC ℓ i (aPC ℓ j Θ) x)
            * aPC ℓ i (aPC ℓ j Θ) x := hBC
      _ = ((∫ x in Submission.BoseGases.abox N ℓ, ‖aPC ℓ i (aPC ℓ j Θ) x‖ ^ 2 : ℝ) : ℂ) := by
        have h1 : (∫ x in Submission.BoseGases.abox N ℓ,
              (starRingEnd ℂ) (aPC ℓ i (aPC ℓ j Θ) x) * aPC ℓ i (aPC ℓ j Θ) x)
            = ∫ x in Submission.BoseGases.abox N ℓ,
                ((‖aPC ℓ i (aPC ℓ j Θ) x‖ ^ 2 : ℝ) : ℂ) :=
          setIntegral_congr_fun (Submission.BoseGases.abox_measurable N ℓ)
            (fun x _ => by rw [Complex.conj_mul', ← Complex.ofReal_pow])
        exact h1.trans integral_ofReal

/-! ## 3. The requested statement -/

theorem integral_conj_mul_aPC_aPC {d : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Θ : Work.BoseDict.Xn d → ℂ}
    (hΘm : MeasureTheory.MemLp Θ (⊤ : ENNReal)
      (MeasureTheory.volume : MeasureTheory.Measure (Work.BoseDict.Xn d)))
    (hΘs : Function.support Θ ⊆ Submission.BoseGases.abox d ℓ) (i j : Fin d) :
    MeasureTheory.IntegrableOn
        (fun x => (starRingEnd ℂ) (Θ x)
          * Work.BoseBoxFock.aPC ℓ i (Work.BoseBoxFock.aPC ℓ j Θ) x)
        (Submission.BoseGases.abox d ℓ) MeasureTheory.volume
      ∧ (∫ x in Submission.BoseGases.abox d ℓ,
          (starRingEnd ℂ) (Θ x) * Work.BoseBoxFock.aPC ℓ i (Work.BoseBoxFock.aPC ℓ j Θ) x)
        = ((∫ x in Submission.BoseGases.abox d ℓ,
            ‖Work.BoseBoxFock.aPC ℓ i (Work.BoseBoxFock.aPC ℓ j Θ) x‖ ^ 2 : ℝ) : ℂ) := by
  obtain ⟨C, hCnn, hCb⟩ := exists_ae_bound_of_memLp_top_gen hΘm
  exact integral_conj_mul_aPC_aPC_of_aesm_bound hℓ hCnn hΘm.aestronglyMeasurable hCb i j

end Work.BoseBoxFock
