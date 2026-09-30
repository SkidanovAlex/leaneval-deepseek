import Mathlib
import Submission.Work.BW.Defs
import Submission.Work.BW.logHeight_prod_zpow_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

set_option linter.unusedVariables false

/-- The natural absolute value of an integer, coerced to `ℝ`, is its real absolute value. -/
lemma natAbs_cast_eq_abs (z : ℤ) : ((z.natAbs : ℝ)) = |(z : ℝ)| := by
  rw [← Int.cast_abs, Int.abs_eq_natAbs]
  norm_num

/-- `hmod` is subadditive over a product of powers: if `hmod (η_a) (ℓ_a) ≤ σ_a` for all `a` and
`M ≠ 0`, then `hmod (∏_a η_a^{M_a}) (∑_a M_a ℓ_a) ≤ ∑_a |M_a| σ_a`.

*Proof:* `hmod β ℓ = max (h(β)/d) (max (‖ℓ‖/d) (1/d))` with `d = Module.finrank ℚ K`. Bound the
height term via `logHeight_prod_zpow_le` (`h(∏ η_a^{M_a}) ≤ ∑ |M_a| h(η_a)`, and
`h(η_a)/d ≤ hmod (η_a) (ℓ_a) ≤ σ_a`), the log term by the triangle inequality (and
`‖ℓ_a‖/d ≤ σ_a`), and the constant `1/d` by `σ_a ≥ hmod (η_a) (ℓ_a) ≥ 1/d` together with
`|M_a| ≥ 1` for some `a` (from `M ≠ 0`). -/
theorem hmod_prod_zpow_le {K : Type*} [Field K] [NumberField K] {r : ℕ} (η : Fin r → K)
    (hη : ∀ a, η a ≠ 0) (ℓ : Fin r → ℂ) (σ : Fin r → ℝ) (M : Fin r → ℤ) (hM : M ≠ 0)
    (hσ : ∀ a, hmod (η a) (ℓ a) ≤ σ a) :
    hmod (∏ a, η a ^ M a) (∑ a, (M a : ℂ) * ℓ a) ≤ ∑ a, |(M a : ℝ)| * σ a := by
  -- some coefficient is nonzero
  obtain ⟨k, hk⟩ : ∃ a, M a ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hM (funext h)
  set D : ℝ := (Module.finrank ℚ K : ℝ) with hD
  have hDnn : 0 ≤ D := by rw [hD]; exact Nat.cast_nonneg _
  -- componentwise consequences of `hmod (η a) (ℓ a) ≤ σ a`
  have hheight : ∀ a, Height.logHeight₁ (η a) / D ≤ σ a :=
    fun a => le_trans (le_max_left _ _) (hσ a)
  have hlog : ∀ a, ‖ℓ a‖ / D ≤ σ a :=
    fun a => le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (hσ a)
  have hconst : ∀ a, 1 / D ≤ σ a :=
    fun a => le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (hσ a)
  have hσnn : ∀ a, 0 ≤ σ a := fun a => le_trans (one_div_nonneg.mpr hDnn) (hconst a)
  rw [hmod, max_le_iff]
  refine ⟨?_, ?_⟩
  · -- height term
    calc Height.logHeight₁ (∏ a, η a ^ M a) / D
        ≤ (∑ a, ((M a).natAbs : ℝ) * Height.logHeight₁ (η a)) / D :=
          div_le_div_of_nonneg_right (logHeight_prod_zpow_le η M) hDnn
      _ = ∑ a, ((M a).natAbs : ℝ) * (Height.logHeight₁ (η a) / D) := by
          rw [Finset.sum_div]
          exact Finset.sum_congr rfl fun a _ => by ring
      _ ≤ ∑ a, ((M a).natAbs : ℝ) * σ a :=
          Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hheight a) (Nat.cast_nonneg _)
      _ = ∑ a, |(M a : ℝ)| * σ a :=
          Finset.sum_congr rfl fun a _ => by rw [natAbs_cast_eq_abs]
  · rw [max_le_iff]
    refine ⟨?_, ?_⟩
    · -- logarithmic term
      calc ‖∑ a, (M a : ℂ) * ℓ a‖ / D
          ≤ (∑ a, ‖(M a : ℂ) * ℓ a‖) / D :=
            div_le_div_of_nonneg_right (norm_sum_le _ _) hDnn
        _ = (∑ a, |(M a : ℝ)| * ‖ℓ a‖) / D := by
            congr 1
            exact Finset.sum_congr rfl fun a _ => by rw [norm_mul, Complex.norm_intCast]
        _ = ∑ a, |(M a : ℝ)| * (‖ℓ a‖ / D) := by
            rw [Finset.sum_div]
            exact Finset.sum_congr rfl fun a _ => by ring
        _ ≤ ∑ a, |(M a : ℝ)| * σ a :=
            Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hlog a) (abs_nonneg _)
    · -- constant term
      have hone : 1 ≤ |(M k : ℝ)| := by
        have h1 : 1 ≤ (M k).natAbs := by have := Int.natAbs_pos.mpr hk; omega
        calc (1 : ℝ) ≤ ((M k).natAbs : ℝ) := by exact_mod_cast h1
          _ = |(M k : ℝ)| := natAbs_cast_eq_abs _
      have hsingle : |(M k : ℝ)| * σ k ≤ ∑ a, |(M a : ℝ)| * σ a :=
        Finset.single_le_sum (f := fun a => |(M a : ℝ)| * σ a)
          (fun a _ => mul_nonneg (abs_nonneg _) (hσnn a)) (Finset.mem_univ k)
      calc 1 / D ≤ σ k := hconst k
        _ ≤ |(M k : ℝ)| * σ k := le_mul_of_one_le_left (hσnn k) hone
        _ ≤ ∑ a, |(M a : ℝ)| * σ a := hsingle

end Work.BW
