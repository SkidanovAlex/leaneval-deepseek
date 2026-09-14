import Mathlib.NumberTheory.Height.NumberField

/-!
# The multiplicative height of an integer vector over `ℚ` is bounded by its sup norm

For a nonzero integer vector `x : ι → ℤ`, the multiplicative height of `x`, viewed as a tuple of
rational numbers, is at most the sup norm `‖x‖`.

We split the height formula over `ℚ` (from `NumberField.mulHeight_eq`) into its archimedean and
nonarchimedean parts:

* the archimedean part is `∏ v, (⨆ i, v (x i)) ^ v.mult`, and each factor `⨆ i, v (x i)` is
  bounded by `‖x‖`; since `totalWeight ℚ = 1`, the whole archimedean part is at most `‖x‖`;
* the nonarchimedean part is a `finprod` of terms `⨆ i, v (x i) ≤ 1` (as `x i ∈ ℤ`), all of them
  nonnegative, and it has finite multiplicative support, so it is at most `1`.
-/

open scoped BigOperators

namespace Commons.NumberTheory.Height.Rat

section aux

variable {ι : Type*} [Fintype ι]

/-- For a nonzero integer vector `x`, the nonarchimedean (finite place) part of the multiplicative
height of `x` viewed in `ℚ^ι` is at most `1`. -/
theorem finitePlace_finprod_iSup_le_one (x : ι → ℤ) (hx : x ≠ 0) :
    (∏ᶠ v : NumberField.FinitePlace ℚ, ⨆ i, v ((x i : ℚ))) ≤ 1 := by
  classical
  -- a nonzero coordinate, used to show that the multiplicative support is finite
  obtain ⟨j₀, hj₀⟩ : ∃ j, x j ≠ 0 := by
    by_contra h
    apply hx
    funext i
    by_contra hi
    exact h ⟨i, hi⟩
  have hxqj₀ : ((x j₀ : ℚ)) ≠ 0 := fun h ↦ hj₀ (Int.cast_injective h)
  have hne : Nonempty ι := ⟨j₀⟩
  -- each term of the product is at most `1`, since `v (n : ℚ) ≤ 1` for integers `n`
  have hle1 : ∀ v : NumberField.FinitePlace ℚ, (⨆ i, v ((x i : ℚ))) ≤ 1 := by
    intro v
    apply ciSup_le
    intro i
    have hv : IsNonarchimedean (v ·) := NumberField.FinitePlace.add_le v
    exact IsNonarchimedean.apply_intCast_le_one hv
  -- each term is nonnegative
  have hnonneg : ∀ v : NumberField.FinitePlace ℚ, 0 ≤ (⨆ i, v ((x i : ℚ))) := by
    intro v
    apply Real.iSup_nonneg'
    exact ⟨j₀, NonnegHomClass.apply_nonneg v _⟩
  -- the multiplicative support of the `sup` is contained in that of the `j₀`-th coordinate,
  -- which is finite
  have hsubset : Function.mulSupport (fun v : NumberField.FinitePlace ℚ ↦ ⨆ i, v ((x i : ℚ)))
      ⊆ Function.mulSupport (fun v : NumberField.FinitePlace ℚ ↦ v ((x j₀ : ℚ))) := by
    intro v hv
    rw [Function.mem_mulSupport] at hv ⊢
    intro hvj₀
    apply hv
    have hbdd : BddAbove (Set.range (fun i : ι ↦ v ((x i : ℚ)))) := Finite.bddAbove_range _
    apply le_antisymm (hle1 v)
    calc (1 : ℝ) = v ((x j₀ : ℚ)) := hvj₀.symm
      _ ≤ ⨆ i, v ((x i : ℚ)) := le_ciSup hbdd j₀
  have hfin : (fun v : NumberField.FinitePlace ℚ ↦ ⨆ i, v ((x i : ℚ))).HasFiniteMulSupport :=
    (NumberField.FinitePlace.hasFiniteMulSupport hxqj₀).subset hsubset
  calc ∏ᶠ v : NumberField.FinitePlace ℚ, (⨆ i, v ((x i : ℚ)))
      ≤ ∏ᶠ v : NumberField.FinitePlace ℚ, (1 : ℝ) :=
        finprod_le_finprod hfin hnonneg Function.hasFiniteMulSupport_fun_one hle1
    _ = 1 := finprod_one

/-- For an integer vector `x`, the archimedean (infinite place) part of the multiplicative height
of `x` viewed in `ℚ^ι` is at most the sup norm `‖x‖`. -/
theorem archPart_le_norm [Nonempty ι] (x : ι → ℤ) :
    (∏ v : NumberField.InfinitePlace ℚ, (⨆ i, v ((x i : ℚ))) ^ v.mult) ≤ ‖x‖ := by
  classical
  obtain ⟨j₀⟩ := (inferInstance : Nonempty ι)
  -- each factor `⨆ i, v (x i)` is at most `‖x‖`
  have hinf : ∀ v : NumberField.InfinitePlace ℚ, (⨆ i, v ((x i : ℚ))) ≤ ‖x‖ := by
    intro v
    apply ciSup_le
    intro i
    rw [NumberField.InfinitePlace.map_intCast]
    exact norm_le_pi_norm x i
  have hnonneg : ∀ v : NumberField.InfinitePlace ℚ, 0 ≤ (⨆ i, v ((x i : ℚ))) := by
    intro v
    apply Real.iSup_nonneg'
    exact ⟨j₀, NonnegHomClass.apply_nonneg v _⟩
  calc (∏ v : NumberField.InfinitePlace ℚ, (⨆ i, v ((x i : ℚ))) ^ v.mult)
      ≤ ∏ v : NumberField.InfinitePlace ℚ, ‖x‖ ^ v.mult := by
        apply Finset.prod_le_prod
        · intro v _
          exact pow_nonneg (hnonneg v) _
        · intro v _
          exact pow_le_pow_left₀ (hnonneg v) (hinf v) _
    _ = ‖x‖ ^ (∑ v : NumberField.InfinitePlace ℚ, v.mult) :=
        Finset.prod_pow_eq_pow_sum (Finset.univ : Finset (NumberField.InfinitePlace ℚ))
          (fun v ↦ v.mult) ‖x‖
    _ = ‖x‖ ^ Height.totalWeight ℚ := by rw [← NumberField.totalWeight_eq_sum_mult]
    _ = ‖x‖ ^ 1 := by rw [NumberField.totalWeight_eq_finrank, Module.finrank_self]
    _ = ‖x‖ := pow_one _

end aux

theorem mulHeight_int_le_norm {ι : Type*} [Fintype ι] (x : ι → ℤ) (hx : x ≠ 0) :
    Height.mulHeight (fun i : ι => (x i : ℚ)) ≤ ‖x‖ := by
  classical
  have hne : Nonempty ι := by
    by_contra h
    apply hx
    funext i
    exact False.elim (h ⟨i⟩)
  have hxq : (fun i : ι => (x i : ℚ)) ≠ 0 := by
    intro h
    apply hx
    funext i
    exact Int.cast_injective (congrFun h i)
  have hAnonneg : 0 ≤ (∏ v : NumberField.InfinitePlace ℚ, (⨆ i, v ((x i : ℚ))) ^ v.mult) := by
    apply Finset.prod_nonneg
    intro v _
    apply pow_nonneg
    apply Real.iSup_nonneg'
    exact ⟨Classical.arbitrary ι, NonnegHomClass.apply_nonneg v _⟩
  have hBnonneg : 0 ≤ (∏ᶠ v : NumberField.FinitePlace ℚ, ⨆ i, v ((x i : ℚ))) :=
    finprod_nonneg fun v ↦ by
      apply Real.iSup_nonneg'
      exact ⟨Classical.arbitrary ι, NonnegHomClass.apply_nonneg v _⟩
  calc Height.mulHeight (fun i : ι => (x i : ℚ))
      = (∏ v : NumberField.InfinitePlace ℚ, (⨆ i, v ((x i : ℚ))) ^ v.mult) *
        (∏ᶠ v : NumberField.FinitePlace ℚ, ⨆ i, v ((x i : ℚ))) :=
        NumberField.mulHeight_eq hxq
    _ ≤ ‖x‖ * 1 :=
        mul_le_mul (archPart_le_norm x) (finitePlace_finprod_iSup_le_one x hx) hBnonneg
          (norm_nonneg x)
    _ = ‖x‖ := mul_one _

end Commons.NumberTheory.Height.Rat