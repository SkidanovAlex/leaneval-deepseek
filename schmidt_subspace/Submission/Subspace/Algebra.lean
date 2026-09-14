import Mathlib
import Submission.Commons.Data.Rat.exists_common_denominator

/-!
# Linear algebra frame for the subspace theorem

Statements here are the algebraic interface layer between the classical
(subspace/hyperplane) formulation of Schmidt's subspace theorem and the
challenge statement over `σ → ℤ`:

* every ℚ-linear form on `σ → ℚ` is a dot product with a rational tuple;
* every proper ℚ-subspace of `σ → ℚ` is contained in the hyperplane of a
  nonzero *integer* tuple `c` (`∑ cᵢ vᵢ = 0`), `c ≠ 0`.
-/

open scoped BigOperators

namespace Submission.Subspace

section Fintype

variable {σ : Type*} [Fintype σ]

/-- Every `ℚ`-linear form on `σ → ℚ` is a dot product with a rational tuple. -/
theorem linearForm_eq_dot (f : (σ → ℚ) →ₗ[ℚ] ℚ) :
    ∃ a : σ → ℚ, ∀ v : σ → ℚ, f v = ∑ i, a i * v i := by
  classical
  let e (i : σ) : σ → ℚ := Pi.single i 1
  refine ⟨fun i => f (e i), ?_⟩
  intro v
  have hv : v = ∑ i, v i • e i := by
    ext j
    simp [e, Pi.single_apply]
  rw [hv, map_sum]
  simp [e, Pi.single_apply, mul_comm]

/-- A proper `ℚ`-subspace of `σ → ℚ` is contained in the kernel of a nonzero
rational linear form, i.e. in a hyperplane `{v | ∑ aᵢ vᵢ = 0}` with `a ≠ 0`. -/
theorem exists_rat_normal_of_proper (V : Submodule ℚ (σ → ℚ)) (hV : V ≠ ⊤) :
    ∃ a : σ → ℚ, a ≠ 0 ∧ ∀ v : σ → ℚ, v ∈ V → (∑ i, a i * v i) = 0 := by
  classical
  have hp : V < ⊤ := lt_top_iff_ne_top.mpr hV
  obtain ⟨f, hf, hfV⟩ := V.exists_dual_map_eq_bot_of_lt_top hp inferInstance
  obtain ⟨a, ha_form⟩ := linearForm_eq_dot f
  refine ⟨a, ?_, ?_⟩
  · intro ha0
    apply hf
    apply LinearMap.ext
    intro v
    rw [ha_form, ha0]
    simp
  · intro v hv
    have hm : f v ∈ V.map f := ⟨v, hv, rfl⟩
    have hm' : f v ∈ (⊥ : Submodule ℚ ℚ) := by
      rw [← hfV]
      exact ⟨v, hv, rfl⟩
    have hz : f v = 0 := (Submodule.mem_bot (R := ℚ) (M := ℚ)).mp hm'
    rw [← ha_form v]
    exact hz

/-- Every proper `ℚ`-subspace of `σ → ℚ` is contained in the kernel of a
nonzero *integer* tuple. -/
theorem exists_int_normal_of_proper (V : Submodule ℚ (σ → ℚ)) (hV : V ≠ ⊤) :
    ∃ c : σ → ℤ, c ≠ 0 ∧ ∀ v : σ → ℚ, v ∈ V → (∑ i, (c i : ℚ) * v i) = 0 := by
  classical
  obtain ⟨a, ha, haV⟩ := exists_rat_normal_of_proper V hV
  obtain ⟨D, hDpos, hD⟩ := Commons.Data.Rat.exists_common_denominator σ a
  let c : σ → ℤ := fun i => Classical.choose (hD i)
  have hw (i : σ) : ((Classical.choose (hD i) : ℤ) : ℚ) = (D : ℚ) * a i := by
    have hqi := Classical.choose_spec (hD i)  -- a i = (c i : ℚ) / D
    have hDc : (D : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hDpos)
    conv_rhs => rw [hqi]
    rw [mul_comm, div_mul_cancel₀ _ hDc]
  have hcD (i : σ) : (c i : ℚ) = (D : ℚ) * a i := by
    simpa [c] using hw i
  refine ⟨c, ?_, ?_⟩
  · intro hc0
    apply ha
    funext i
    have hci : (c i : ℚ) = 0 := by rw [hc0]; simp
    have hDi : (D : ℚ) * a i = 0 := by rw [← hcD i, hci]
    exact (mul_eq_zero.mp hDi).resolve_left (by exact_mod_cast (ne_of_gt hDpos))
  · intro v hv
    calc
      (∑ i, (c i : ℚ) * v i) = ∑ i, ((D : ℚ) * a i) * v i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hcD i]
      _ = (D : ℚ) * (∑ i, a i * v i) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = 0 := by rw [haV v hv]; ring

/-- At `x = 0` the strict hypothesis of the subspace theorem is contradictory:
the left hand side is `‖0‖ = 0` and `‖0‖ ^ (-ε) = 0`. -/
theorem zero_not_small (L : σ → σ → ℂ) (ε : ℝ) (hε : 0 < ε) :
    ¬ ‖(∏ i : σ, ∑ j : σ, L i j * (0 : ℤ) : ℂ)‖ < ‖(0 : σ → ℤ)‖ ^ (-ε) := by
  intro h
  have hR : ‖(0 : σ → ℤ)‖ ^ (-ε) = 0 := by
    rw [Real.rpow_def_of_nonneg (show (0 : ℝ) ≤ ‖(0 : σ → ℤ)‖ by simp)]
    have hne : -ε ≠ 0 := by linarith
    simp [hne]
  have hnonneg : (0 : ℝ) ≤ ‖(∏ i : σ, ∑ j : σ, L i j * (0 : ℤ) : ℂ)‖ := by positivity
  linarith
end Fintype

end Submission.Subspace
