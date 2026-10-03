import Mathlib
import Submission.Work.FIArea7.KStarDefs
import Submission.Work.FIArea7.KStarDivs.PrimDefs

set_option autoImplicit false

namespace Work.FIArea7.KStarDivs

open Classical
attribute [local instance] Classical.propDecidable

noncomputable section

open Finset
open scoped BigOperators

/-- The generating-function identity `∑_{t ⊆ s} ∏_{i ∈ t} f i = ∏_{i ∈ s} (1 + f i)`. -/
lemma sum_powerset_prod {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℂ) :
    (∑ t ∈ s.powerset, ∏ i ∈ t, f i) = ∏ i ∈ s, (1 + f i) := by
  have h : ∏ i ∈ s, (f i + 1) = ∑ t ∈ s.powerset, ∏ i ∈ t, f i := by
    have h := Finset.prod_add f (fun _ => (1 : ℂ)) s
    simpa only [Finset.prod_const_one, mul_one] using h
  rw [← h]
  exact Finset.prod_congr rfl (fun i _ => add_comm (f i) 1)

/-- The indicator of `∏_{p ∈ S} p ∣ z` factors over `S`. -/
lemma ind_dvd_prod {w : GaussianInt} {S : Finset GaussianInt} {z : GaussianInt}
    (hS : S ⊆ primPrimes w) :
    ((if (∏ p ∈ S, p) ∣ z then (1 : ℂ) else 0))
      = ∏ p ∈ S, (if p ∣ z then (1 : ℂ) else 0) := by
  by_cases h : (∏ p ∈ S, p) ∣ z
  · rw [if_pos h]
    rw [show (∏ p ∈ S, (if p ∣ z then (1 : ℂ) else 0)) = ∏ p ∈ S, (1 : ℂ) from
      Finset.prod_congr rfl (fun p hp => if_pos ((dvd_prod_primPrimes_iff hS).mp h p hp))]
    simp
  · rw [if_neg h]
    obtain ⟨p0, hp0, hp0z⟩ : ∃ p ∈ S, ¬ p ∣ z := by
      by_contra hc
      push_neg at hc
      exact h ((dvd_prod_primPrimes_iff hS).mpr hc)
    exact (Finset.prod_eq_zero hp0 (if_neg hp0z)).symm

/-- A product of `0`-`1` factors; it is `1` exactly when every factor is. -/
lemma prod_ite_zero_one {ι : Type*} (P : Finset ι) (q : ι → Prop) [DecidablePred q] :
    (∏ p ∈ P, (if q p then (0 : ℂ) else 1)) = if (∀ p ∈ P, ¬ q p) then 1 else 0 := by
  rw [← Finset.prod_boole (s := P) (p := fun p => ¬ q p)]
  exact Finset.prod_congr rfl (fun p _ => by by_cases h : q p <;> simp [h])

end

end Work.FIArea7.KStarDivs
