import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.UBBInputs8.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `setIntegral_abox_mul_prod_indicator`

The box integral of `f` multiplied by the product over the particles of the
indicator of a set `A ⊆ Λ(ℓ)` equals the integral of `f` over the *product* set
`Aᴺ = Set.univ.pi (fun _ : Fin N => A)`.

The route is purely measure-theoretic and needs no product-measure theory:

* pointwise, `∏ i, 1_A (x i) = 1_{Aᴺ} (x)` (a product of `0/1`-valued factors is
  `1` exactly when all factors are `1`);
* hence the integrand `f x * ∏ i, 1_A (x i)` is the pointwise indicator
  `1_{Aᴺ} (x) * f x`;
* `MeasureTheory.setIntegral_indicator` turns the integral of an indicator over
  `abox N ℓ` into the integral over `abox N ℓ ∩ Aᴺ`;
* `A ⊆ Λ(ℓ)` gives `Aᴺ ⊆ abox N ℓ`, so `abox N ℓ ∩ Aᴺ = Aᴺ`.
-/

namespace Work.BoseFixB1B

open MeasureTheory

/-- A product of `0/1`-valued indicators over the particles is the indicator of
the product set. -/
lemma prod_indicator_eq_pi_indicator {N : ℕ} {A : Set (EuclideanSpace ℝ (Fin 3))}
    (x : Submission.BoseGases.X N) :
    (∏ i : Fin N, A.indicator (fun _ => (1 : ℝ)) (x i))
      = (Set.univ.pi (fun _ : Fin N => A)).indicator (fun _ => (1 : ℝ)) x := by
  by_cases h : x ∈ Set.univ.pi (fun _ : Fin N => A)
  · rw [Set.indicator_of_mem h]
    refine Finset.prod_eq_one (fun i _ => ?_)
    rw [Set.indicator_of_mem ((Set.mem_univ_pi.mp h) i)]
  · rw [Set.indicator_of_notMem h]
    obtain ⟨i, hi⟩ := not_forall.mp (fun hall => h (Set.mem_univ_pi.mpr hall))
    exact Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)

/-- Multiplying by the indicator of the product set is the same as applying the
indicator to `f`. -/
lemma mul_indicator_eq_pi_indicator {N : ℕ} {A : Set (EuclideanSpace ℝ (Fin 3))}
    (f : Submission.BoseGases.X N → ℝ) (x : Submission.BoseGases.X N) :
    f x * (Set.univ.pi (fun _ : Fin N => A)).indicator (fun _ => (1 : ℝ)) x
      = (Set.univ.pi (fun _ : Fin N => A)).indicator f x := by
  by_cases h : x ∈ Set.univ.pi (fun _ : Fin N => A)
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, mul_one]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, mul_zero]

lemma setIntegral_abox_mul_prod_indicator {N : ℕ} {ℓ : ℝ} {A : Set (EuclideanSpace ℝ (Fin 3))}
    (hA : MeasurableSet A) (hAc : A ⊆ Submission.BoseGases.acube ℓ) (f : Submission.BoseGases.X N → ℝ) :
    ∫ x in Submission.BoseGases.abox N ℓ,
        f x * ∏ i : Fin N, A.indicator (fun _ => (1 : ℝ)) (x i)
      = ∫ x in Set.univ.pi (fun _ : Fin N => A), f x := by
  have hmeasA : MeasurableSet (Set.univ.pi (fun _ : Fin N => A)) :=
    MeasurableSet.pi (s := Set.univ) (t := fun _ : Fin N => A) Set.countable_univ (fun i _ => hA)
  have hsub : Set.univ.pi (fun _ : Fin N => A) ⊆ Submission.BoseGases.abox N ℓ := by
    intro x hx i
    exact hAc (Set.mem_univ_pi.mp hx i)
  calc ∫ x in Submission.BoseGases.abox N ℓ,
          f x * ∏ i : Fin N, A.indicator (fun _ => (1 : ℝ)) (x i)
      = ∫ x in Submission.BoseGases.abox N ℓ,
          (Set.univ.pi (fun _ : Fin N => A)).indicator f x := by
        apply setIntegral_congr_fun (Submission.BoseGases.abox_measurable N ℓ)
        intro x _
        change f x * (∏ i : Fin N, A.indicator (fun _ => (1 : ℝ)) (x i))
          = (Set.univ.pi (fun _ : Fin N => A)).indicator f x
        rw [prod_indicator_eq_pi_indicator x, mul_indicator_eq_pi_indicator f x]
    _ = ∫ x in Submission.BoseGases.abox N ℓ ∩ Set.univ.pi (fun _ : Fin N => A), f x := by
        rw [setIntegral_indicator hmeasA]
    _ = ∫ x in Set.univ.pi (fun _ : Fin N => A), f x := by
        rw [Set.inter_eq_self_of_subset_right hsub]

end Work.BoseFixB1B
