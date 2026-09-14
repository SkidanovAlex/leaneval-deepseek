import Mathlib
import Submission.Commons.NumberTheory.Height.MvPolynomial.polyHeight_mul_le

namespace Commons.NumberTheory.Height.MvPolynomial

open scoped BigOperators

variable {σ : Type*} [Fintype σ]

/-- On `ℚ`, every archimedean absolute value sends an integer to its absolute value
(viewed in `ℝ`). -/
lemma archAbsVal_apply_intCast {a : AbsoluteValue ℚ ℝ}
    (ha : a ∈ Height.AdmissibleAbsValues.archAbsVal (K := ℚ)) (z : ℤ) :
    a ((z : ℚ)) = ((z.natAbs : ℕ) : ℝ) := by
  obtain ⟨w, hw⟩ :=
    NumberField.isInfinitePlace_iff a |>.mp (NumberField.mem_multisetInfinitePlace.mp ha)
  rw [← hw]
  rw [← NumberField.InfinitePlace.coe_apply]
  rw [NumberField.InfinitePlace.map_intCast]
  rw [Int.norm_eq_abs, ← Int.cast_abs, Int.abs_eq_natAbs]
  norm_num

theorem logHeight_gP_int_le {σ : Type*} [Fintype σ] (P : MvPolynomial σ ℤ) (B : ℝ) (hB : 1 ≤ B) (h : ∀ m : σ →₀ ℕ, ((((MvPolynomial.coeff m P).natAbs : ℕ) : ℝ)) ≤ B) : Height.logHeight (Commons.NumberTheory.Height.MvPolynomial.gP (P.map (Int.castRingHom ℚ))) ≤ Real.log B := by
  classical
  let Q : MvPolynomial σ ℚ := P.map (Int.castRingHom ℚ)
  have hcoeff : ∀ m : σ →₀ ℕ, MvPolynomial.coeff m Q = ((MvPolynomial.coeff m P : ℤ) : ℚ) := by
    intro m
    simp only [Q, MvPolynomial.coeff_map, Int.coe_castRingHom]
  -- the nonarchimedean part is trivial because all coefficients are integers
  have hnonarch : (∏ᶠ v : Height.AdmissibleAbsValues.nonarchAbsVal (K := ℚ),
      (⨆ i : tP Q, v.val (gP Q i))) = 1 := by
    refine finprod_eq_one_of_forall_eq_one (fun v => ?_)
    rw [iSup_gP_eq v.val Q]
    have hle : coeffSup v.val Q ≤ 1 := by
      refine ciSup_le (fun m => ?_)
      rw [hcoeff m]
      exact IsNonarchimedean.apply_intCast_le_one
        (Height.AdmissibleAbsValues.isNonarchimedean v.val v.prop)
    rw [max_eq_left hle]
  -- the archimedean part is bounded by `B`
  have hcard : (Height.AdmissibleAbsValues.archAbsVal (K := ℚ)).card = 1 := by
    rw [← Height.totalWeight, NumberField.totalWeight_eq_finrank]
    simp [Module.finrank_self]
  obtain ⟨a, ha⟩ := Multiset.card_eq_one.mp hcard
  have hamem : a ∈ Height.AdmissibleAbsValues.archAbsVal (K := ℚ) := by
    rw [ha]; exact Multiset.mem_singleton_self a
  have harch : ((Height.AdmissibleAbsValues.archAbsVal (K := ℚ)).map
      (fun v => max 1 (coeffSup v Q))).prod ≤ B := by
    rw [ha]
    simp only [Multiset.map_singleton, Multiset.prod_singleton]
    refine max_le hB ?_
    refine ciSup_le (fun m => ?_)
    rw [hcoeff m, archAbsVal_apply_intCast hamem]
    exact h m
  -- combine both parts
  have hmain : Height.mulHeight (gP Q) ≤ B := by
    rw [mulHeight_gP_eq_prod Q, hnonarch, mul_one]
    exact harch
  have hpos : 0 < Height.mulHeight (gP Q) := by
    rw [mulHeight_gP_eq_prod Q, hnonarch, mul_one]
    exact lt_of_lt_of_le zero_lt_one
      (Multiset.one_le_prod_map (fun v _ => le_max_left _ _))
  change Height.logHeight (gP Q) ≤ Real.log B
  rw [Height.logHeight_eq_log_mulHeight]
  exact Real.log_le_log hpos hmain

end Commons.NumberTheory.Height.MvPolynomial
