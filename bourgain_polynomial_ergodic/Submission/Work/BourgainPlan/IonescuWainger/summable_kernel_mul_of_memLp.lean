import Mathlib

namespace Work.BourgainPlan.IonescuWainger

/-- Hölder/Young: if `K ∈ ℓ^q` (`q = p/(p-1)`, `1 < p`) and `h ∈ ℓ^p`, then the pointwise
product `i ↦ K (k-i) * h i` is summable. -/
theorem summable_kernel_mul_of_memLp {p : ℝ} (hp : 1 < p) {K : ℤ → ℂ}
    (hK : Summable (fun j : ℤ => ‖K j‖ ^ (p / (p - 1)))) {h : ℤ → ℂ}
    (hh : Memℓp h (ENNReal.ofReal p)) (k : ℤ) :
    Summable (fun i : ℤ => K (k - i) * h i) := by
  have hp_pos : 0 < p := zero_lt_one.trans hp
  have hpq : p.HolderConjugate (p / (p - 1)) := Real.HolderConjugate.conjExponent hp
  -- `‖h‖ ∈ ℓ^p`, extracted from the `Memℓp` hypothesis.
  have hh' : Summable (fun i : ℤ => ‖h i‖ ^ p) := by
    have h0 : 0 < (ENNReal.ofReal p).toReal := by
      rw [ENNReal.toReal_ofReal (le_of_lt hp_pos)]; exact hp_pos
    have h1 := (memℓp_gen_iff (p := ENNReal.ofReal p) h0).mp hh
    rwa [ENNReal.toReal_ofReal (le_of_lt hp_pos)] at h1
  -- Reindex `j ↦ k - j` is injective on `ℤ`, so `‖K (k - ·)‖ ∈ ℓ^q`.
  have hK' : Summable (fun i : ℤ => ‖K (k - i)‖ ^ (p / (p - 1))) :=
    hK.comp_injective (fun a b hab => by linarith)
  -- Young's inequality dominates the norms of the products by a summable sequence.
  have hprod : Summable (fun i : ℤ => ‖K (k - i)‖ * ‖h i‖) := by
    apply Summable.of_nonneg_of_le
      (f := fun i : ℤ => ‖K (k - i)‖ ^ (p / (p - 1)) / (p / (p - 1)) + ‖h i‖ ^ p / p)
    · intro i; positivity
    · intro i
      exact Real.young_inequality_of_nonneg (a := ‖K (k - i)‖) (b := ‖h i‖)
        (norm_nonneg _) (norm_nonneg _) hpq.symm
    · exact (hK'.div_const _).add (hh'.div_const _)
  refine Summable.of_norm ?_
  simpa only [norm_mul] using hprod

end Work.BourgainPlan.IonescuWainger
