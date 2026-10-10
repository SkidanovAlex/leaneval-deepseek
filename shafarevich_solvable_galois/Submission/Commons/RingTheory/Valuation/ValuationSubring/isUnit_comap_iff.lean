import Mathlib.RingTheory.Valuation.ValuationSubring
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.RingTheory.Valuation.ValuationSubring

/-- For a subring `S` of a field `K`, an element `x : S` is a unit if and only if its image
`(x : K)` is nonzero and the inverse `(x : K)⁻¹` taken in `K` again belongs to `S`. -/
lemma isUnit_subring_coe_iff {K : Type*} [Field K] (S : Subring K) (x : S) :
    IsUnit x ↔ (x : K) ≠ 0 ∧ (x : K)⁻¹ ∈ S := by
  constructor
  · intro hx
    obtain ⟨b, hxb, hbx⟩ := isUnit_iff_exists.mp hx
    have hb : (x : K) * (b : K) = 1 := by
      have := congrArg (Subtype.val : S → K) hxb
      simpa using this
    have hb' : (b : K) * (x : K) = 1 := by
      have := congrArg (Subtype.val : S → K) hbx
      simpa using this
    refine ⟨?_, ?_⟩
    · rintro h0; rw [h0, mul_zero] at hb'; exact zero_ne_one hb'
    · rw [inv_eq_of_mul_eq_one_right hb]; exact b.2
  · rintro ⟨hx0, hinv⟩
    refine isUnit_iff_exists.mpr ⟨⟨(x : K)⁻¹, hinv⟩, ?_, ?_⟩
    · apply Subtype.ext
      simp only [Subring.coe_mul, Subring.coe_one]
      exact mul_inv_cancel₀ hx0
    · apply Subtype.ext
      simp only [Subring.coe_mul, Subring.coe_one]
      exact inv_mul_cancel₀ hx0

theorem isUnit_comap_iff {K E : Type*} [Field K] [Field E] [Algebra K E] (A : ValuationSubring E)
    (x : A.comap (algebraMap K E)) :
    IsUnit x ↔
      IsUnit (⟨algebraMap K E (x : K), (ValuationSubring.mem_comap).mp x.2⟩ : A) := by
  have hL : IsUnit x ↔ (x : K) ≠ 0 ∧ (x : K)⁻¹ ∈ A.comap (algebraMap K E) :=
    isUnit_subring_coe_iff _ x
  have hR : IsUnit (⟨algebraMap K E (x : K), (ValuationSubring.mem_comap).mp x.2⟩ : A) ↔
      (algebraMap K E (x : K)) ≠ 0 ∧ (algebraMap K E (x : K))⁻¹ ∈ A.toSubring :=
    isUnit_subring_coe_iff _ _
  rw [hL, hR]
  simp only [ValuationSubring.mem_comap]
  constructor
  · rintro ⟨h0, h1⟩
    refine ⟨?_, ?_⟩
    · intro hf0
      exact h0 ((algebraMap K E).injective (by simpa using hf0))
    · rw [← map_inv₀ (algebraMap K E) (x : K)]
      exact h1
  · rintro ⟨h0, h1⟩
    refine ⟨?_, ?_⟩
    · intro hx0; exact h0 (by rw [hx0, map_zero])
    · rw [map_inv₀ (algebraMap K E) (x : K)]
      exact h1

end Commons.RingTheory.Valuation.ValuationSubring