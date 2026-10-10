import Mathlib
import Submission.Work.MotAS.ASResidual

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotAS.ASRulV2

theorem zias_shift_reduce (K : Type*) [Field K]
    (Z : Ideal (MvPolynomial (Fin 3) K))
    (h : Ideal.map (MvPolynomial.aeval (fun i : Fin 3 =>
        (![MvPolynomial.X 0, MvPolynomial.X 1, (1 : MvPolynomial (Fin 2) K)] : Fin 3 → MvPolynomial (Fin 2) K) i)) Z ≠ ⊤) :
    Z ⊔ Ideal.span {(MvPolynomial.X 2 - 1 : MvPolynomial (Fin 3) K)} ≠ ⊤ := by
  -- `φ` is the `K`-algebra map `K[X₀,X₁,X₂] → K[Y₀,Y₁]` with `X₀ ↦ Y₀`, `X₁ ↦ Y₁`, `X₂ ↦ 1`.
  set φ : MvPolynomial (Fin 3) K →ₐ[K] MvPolynomial (Fin 2) K :=
    MvPolynomial.aeval (fun i : Fin 3 =>
        (![MvPolynomial.X 0, MvPolynomial.X 1, (1 : MvPolynomial (Fin 2) K)] : Fin 3 → MvPolynomial (Fin 2) K) i)
    with hφ
  -- Its value on the generator `X₂ - 1` of the second ideal is zero.
  have hX2 : φ (MvPolynomial.X 2 - 1 : MvPolynomial (Fin 3) K) = 0 := by
    rw [map_sub, map_one, MvPolynomial.aeval_X]
    simp
  intro h2
  apply h
  rw [Ideal.eq_top_iff_one]
  -- `1 ∈ Z ⊔ (X₂ - 1)`; split it as `z + y` with `z ∈ Z` and `y ∈ (X₂ - 1)`.
  have h1 : (1 : MvPolynomial (Fin 3) K) ∈
      Z ⊔ Ideal.span {(MvPolynomial.X 2 - 1 : MvPolynomial (Fin 3) K)} := by
    rw [h2]; exact Submodule.mem_top
  rw [Submodule.mem_sup] at h1
  obtain ⟨z, hz, y, hy, hzy⟩ := h1
  have hy0 : φ y = 0 := by
    have hdiv : (MvPolynomial.X 2 - 1 : MvPolynomial (Fin 3) K) ∣ y :=
      Ideal.mem_span_singleton.mp hy
    obtain ⟨c, rfl⟩ := hdiv
    rw [map_mul, hX2, zero_mul]
  -- Applying `φ` to `z + y = 1` gives `φ z = 1`.
  have hz1 : φ z = 1 := by
    have hh := congrArg φ hzy
    rw [map_add, hy0, add_zero, map_one] at hh
    exact hh
  rw [← hz1]
  exact Ideal.mem_map_of_mem _ hz

end Work.MotAS.ASRulV2
