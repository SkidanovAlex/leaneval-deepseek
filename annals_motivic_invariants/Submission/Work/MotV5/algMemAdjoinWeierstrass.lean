import Mathlib
import Submission.Work.MotV5.mem_bot_of_mem_adjoin_simple_of_isAlgebraic
import Submission.Work.MotV5.not_mem_adjoin_simple_of_no_rat_root
import Submission.Work.MotV5.finrank_adjoin_le_two_of_quadratic
import Submission.Work.MotV5.two_le_finrank_adjoin_of_notMem_bot
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The algebraic part of `L(x,y)` for a Weierstrass equation is `L`

Let `K ⊆ L ⊆ Ω` be fields with `L / K` algebraic, `x ∈ Ω` transcendental over `K`, and
`y ∈ Ω` a solution of the (inhomogeneous) Weierstrass equation

`y ^ 2 + (a₁ x + a₃) y = x ^ 3 + a₂ x ^ 2 + a₄ x + a₆`.

If `z ∈ L⟮x, y⟯` is algebraic over `L`, and if `L⟮z⟯` has no point of the curve "with
`x`-coordinate the transcendental variable" (the hypothesis `hno`), then `z` already lies in `L`.

The proof is a degree count.  Put `A := L⟮x⟯`, `A' := A⟮z⟯` and `B := A⟮y⟯`.

* `dim_A B ≤ 2`, since `y` is a root of the monic quadratic `T ^ 2 + (a₁ x + a₃) T - f(x)` over `A`.
* `hno` forces `y ∉ A' = L⟮x, z⟯ = L⟮z⟯⟮x⟯`: otherwise `y` would be a rational function of `x`
  over `L⟮z⟯`, contradicting the absence of a root of the homogenised equation.
* If `z ∉ L`, then `z ∉ A` (the base field is algebraically closed in `A = L⟮x⟯`, since `x` is
  transcendental over `L`), so `dim_A A' ≥ 2`.
* Finally `A' ≤ B`, and `dim_A A' ∣ dim_A B ≤ 2` gives `dim_A A' = 2`, i.e. `A' = B`, contradicting
  `y ∉ A'`.
-/

set_option linter.style.haveILetI false

namespace Work.MotV5

/-- The algebraic part of the function field of a Weierstrass curve `y ^ 2 + (a₁x + a₃)y =
x ^ 3 + a₂x ^ 2 + a₄x + a₆`, for `x` transcendental, is the base field. -/
theorem algMemAdjoinWeierstrass {K L Ω : Type*} [Field K] [Field L] [Field Ω]
    [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω]
    (hLalg : Algebra.IsAlgebraic K L)
    (x y z : Ω) (a₁ a₂ a₃ a₄ a₆ : K)
    (hW : y ^ 2 + (algebraMap K Ω a₁ * x + algebraMap K Ω a₃) * y
        = x ^ 3 + algebraMap K Ω a₂ * x ^ 2 + algebraMap K Ω a₄ * x + algebraMap K Ω a₆)
    (hxt : Transcendental K x)
    (hz : IsAlgebraic L z)
    (hzm : z ∈ IntermediateField.adjoin L ({x, y} : Set Ω))
    (hno : ∀ r s : Polynomial ↥(IntermediateField.adjoin L ({z} : Set Ω)), s ≠ 0 →
        r ^ 2 + (Polynomial.C (algebraMap K (↥(IntermediateField.adjoin L ({z} : Set Ω))) a₁)
            * Polynomial.X + Polynomial.C (algebraMap K _ a₃)) * r * s
          - (Polynomial.X ^ 3 + Polynomial.C (algebraMap K _ a₂) * Polynomial.X ^ 2
              + Polynomial.C (algebraMap K _ a₄) * Polynomial.X + Polynomial.C (algebraMap K _ a₆))
            * s ^ 2 ≠ 0) :
    ∃ c : L, z = algebraMap L Ω c := by
  -- `x` is transcendental over `L` (and, below, over `L⟮z⟯`).
  have hxtL : Transcendental L x := fun h => hxt ((Algebra.IsAlgebraic.isAlgebraic_iff K L).mpr h)
  -- The fields `A = L⟮x⟯` and `F = L⟮z⟯`.
  set A : IntermediateField L Ω := IntermediateField.adjoin L ({x} : Set Ω) with hA
  set F : IntermediateField L Ω := IntermediateField.adjoin L ({z} : Set Ω) with hF
  -- Coefficients of `hno`, transported to the ambient field.
  have keyF : ∀ a : K, algebraMap ↥F Ω (algebraMap K ↥F a) = algebraMap K Ω a := by
    intro a
    rw [IsScalarTower.algebraMap_apply K L ↥F, ← IsScalarTower.algebraMap_apply L ↥F Ω,
      ← IsScalarTower.algebraMap_apply K L Ω]
  have hLF : Algebra.IsAlgebraic L ↥F := by
    rw [hF]
    exact IntermediateField.isAlgebraic_adjoin (S := ({z} : Set Ω)) (fun w hw => by
      rw [Set.mem_singleton_iff] at hw
      subst hw
      exact hz.isIntegral)
  have hxtF : Transcendental ↥F x := fun h =>
    hxt ((Algebra.IsAlgebraic.isAlgebraic_iff K L).mpr
      ((Algebra.IsAlgebraic.isAlgebraic_iff L ↥F).mpr h))
  by_contra hcon
  -- `z ∉ L` in terms of intermediate fields.
  have hzbot : z ∉ (⊥ : IntermediateField L Ω) := by
    intro h
    obtain ⟨c, hc⟩ := IntermediateField.mem_bot.mp h
    exact hcon ⟨c, hc.symm⟩
  -- `z ∉ L⟮x⟯`: `L` is algebraically closed in the purely transcendental extension `L⟮x⟯`.
  have hzA' : z ∉ ((IntermediateField.adjoin L ({x} : Set Ω)) : Set Ω) :=
    fun h => hzbot (mem_bot_of_mem_adjoin_simple_of_isAlgebraic hxtL hz h)
  have hzA : z ∉ (A : Set Ω) := by rwa [hA]
  have hxA : x ∈ (A : Set Ω) := by
    rw [hA]
    exact IntermediateField.subset_adjoin L ({x} : Set Ω) (Set.mem_singleton x)
  have hzAalg : IsAlgebraic ↥A z := by
    obtain ⟨p, hp, hpz⟩ := hz
    exact ⟨p.map (algebraMap L ↥A),
      (by
        have h := (Polynomial.map_injective (algebraMap L ↥A) (algebraMap L ↥A).injective).ne hp
        rwa [Polynomial.map_zero] at h),
      (by simpa only [Polynomial.aeval_map_algebraMap] using hpz)⟩
  -- The intermediate fields `A' = A⟮z⟯` and `B = A⟮y⟯` over `A`.
  set A' : IntermediateField ↥A Ω := IntermediateField.adjoin ↥A ({z} : Set Ω) with hA'
  set B : IntermediateField ↥A Ω := IntermediateField.adjoin ↥A ({y} : Set Ω) with hB
  have hBset : (B : Set Ω) = (IntermediateField.adjoin L ({x, y} : Set Ω) : Set Ω) := by
    have h1 : (IntermediateField.restrictScalars L B : IntermediateField L Ω) =
        IntermediateField.adjoin L ({x} ∪ {y}) := by
      rw [hB, hA, IntermediateField.adjoin_adjoin_left L ({x} : Set Ω) ({y} : Set Ω)]
    have h1' : (B : Set Ω) = (IntermediateField.adjoin L ({x} ∪ {y}) : Set Ω) := by
      rw [← IntermediateField.coe_restrictScalars L (E := B), h1]
    have h2 : ({x} ∪ {y} : Set Ω) = {x, y} := by
      rw [Set.singleton_union]
    rw [h1', h2]
  have hA'set : (A' : Set Ω) = (IntermediateField.adjoin ↥F ({x} : Set Ω) : Set Ω) := by
    have h1 : (IntermediateField.restrictScalars L A' : IntermediateField L Ω) =
        IntermediateField.adjoin L ({x} ∪ {z}) := by
      rw [hA', hA, IntermediateField.adjoin_adjoin_left L ({x} : Set Ω) ({z} : Set Ω)]
    have h1' : (A' : Set Ω) = (IntermediateField.adjoin L ({x} ∪ {z}) : Set Ω) := by
      rw [← IntermediateField.coe_restrictScalars L (E := A'), h1]
    have h2 : (IntermediateField.restrictScalars L (IntermediateField.adjoin ↥F ({x} : Set Ω)) :
        IntermediateField L Ω) = IntermediateField.adjoin L ({z} ∪ {x}) := by
      rw [hF, IntermediateField.adjoin_adjoin_left L ({z} : Set Ω) ({x} : Set Ω)]
    have h2' : (IntermediateField.adjoin ↥F ({x} : Set Ω) : Set Ω) =
        (IntermediateField.adjoin L ({z} ∪ {x}) : Set Ω) := by
      rw [← IntermediateField.coe_restrictScalars L
        (E := IntermediateField.adjoin ↥F ({x} : Set Ω)), h2]
    rw [h1', h2', Set.union_comm]
  -- `hno` forces `y ∉ A' = L⟮z⟯⟮x⟯`.
  have hyA' : y ∉ (A' : Set Ω) := by
    rw [hA'set]
    refine not_mem_adjoin_simple_of_no_rat_root x y (algebraMap K ↥F a₁) (algebraMap K ↥F a₂)
      (algebraMap K ↥F a₃) (algebraMap K ↥F a₄) (algebraMap K ↥F a₆) hxtF ?_ ?_
    · rw [keyF a₁, keyF a₂, keyF a₃, keyF a₄, keyF a₆]
      exact hW
    · simpa only [hF] using hno
  -- `A' ⊆ B`.
  have hA'B : A' ≤ B := by
    rw [hA', IntermediateField.adjoin_le_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    rw [hBset]
    exact hzm
  -- `z ∉ A`, i.e. `A'` is a proper extension of `A`, hence `2 ≤ dim_A A'`.
  have hzbotA : z ∉ (⊥ : IntermediateField ↥A Ω) := by
    rw [IntermediateField.mem_bot]
    rintro ⟨w, hw⟩
    rw [IntermediateField.algebraMap_apply] at hw
    exact hzA (hw ▸ w.2)
  have hA'fin : 2 ≤ Module.finrank ↥A ↥A' := by
    rw [hA']
    exact two_le_finrank_adjoin_of_notMem_bot hzAalg hzbotA
  -- `y` is a root of a monic quadratic over `A`, so `B` has degree `≤ 2` over `A`.
  have hquad : ∃ α β : ↥A, y ^ 2 + algebraMap ↥A Ω α * y + algebraMap ↥A Ω β = 0 := by
    refine ⟨algebraMap L ↥A (algebraMap K L a₁) * ⟨x, hxA⟩ + algebraMap L ↥A (algebraMap K L a₃),
      -(⟨x, hxA⟩ ^ 3 + algebraMap L ↥A (algebraMap K L a₂) * ⟨x, hxA⟩ ^ 2
        + algebraMap L ↥A (algebraMap K L a₄) * ⟨x, hxA⟩ + algebraMap L ↥A (algebraMap K L a₆)), ?_⟩
    simp only [map_add, map_mul, map_pow, map_neg, IntermediateField.algebraMap_apply,
      SubalgebraClass.coe_algebraMap, ← IsScalarTower.algebraMap_apply K L Ω]
    linear_combination (norm := first | refl_ring1 | ring1) hW
  obtain ⟨α, β, hαβ⟩ := hquad
  have hyint : IsIntegral ↥A y := by
    refine ⟨Polynomial.X ^ 2 + Polynomial.C α * Polynomial.X + Polynomial.C β, ?_, ?_⟩
    · monicity!
    · simpa only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
        Polynomial.eval₂_X, Polynomial.eval₂_C] using hαβ
  haveI hBfd : FiniteDimensional ↥A B := by
    rw [hB]
    exact IntermediateField.finiteDimensional_adjoin (S := ({y} : Set Ω)) (fun w hw => by
      rw [Set.mem_singleton_iff] at hw; subst hw; exact hyint)
  have hBfin : Module.finrank ↥A ↥B ≤ 2 := by
    rw [hB]
    exact finrank_adjoin_le_two_of_quadratic y α β hαβ
  -- Degree count: `2 ≤ dim_A A' ≤ dim_A B ≤ 2`, hence `A' = B`.
  have hfinle : Module.finrank ↥A ↥A' ≤ Module.finrank ↥A ↥B :=
    IntermediateField.finrank_le_of_le_right hA'B
  have heq : Module.finrank ↥A ↥A' = Module.finrank ↥A ↥B :=
    le_antisymm hfinle (le_trans hBfin hA'fin)
  have hA'eqB : A' = B := IntermediateField.eq_of_le_of_finrank_eq hA'B heq
  have hyB : y ∈ (B : Set Ω) := by
    rw [hB]
    exact IntermediateField.subset_adjoin ↥A ({y} : Set Ω) (Set.mem_singleton y)
  exact hyA' (hA'eqB.symm ▸ hyB)

end Work.MotV5
