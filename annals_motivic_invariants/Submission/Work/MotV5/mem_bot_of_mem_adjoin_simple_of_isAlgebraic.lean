import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotV5

theorem mem_bot_of_mem_adjoin_simple_of_isAlgebraic {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    {x z : Ω} (hx : Transcendental K x) (hz : IsAlgebraic K z)
    (hzx : z ∈ (IntermediateField.adjoin K ({x} : Set Ω) : Set Ω)) :
    z ∈ (⊥ : IntermediateField K Ω) := by
  -- `z` is a rational function in `x` over `K`.
  obtain ⟨r, s, hrs⟩ := (IntermediateField.mem_adjoin_simple_iff (F := K) (α := x) z).mp hzx
  by_cases hsx : Polynomial.aeval x s = 0
  · -- degenerate representation: `z = r(x)/0 = 0`
    rw [IntermediateField.mem_bot]
    refine ⟨0, ?_⟩
    rw [map_zero, hrs, hsx, div_zero]
  · -- in lowest terms: `z * s(x) = r(x)`
    have hs0 : s ≠ 0 := fun h => hsx (by rw [h, map_zero])
    have hz_mul : z * Polynomial.aeval x s = Polynomial.aeval x r := by
      rw [hrs, div_mul_cancel₀ _ hsx]
    -- `E = K(z)`; it is algebraic over `K` since `z` is.
    let E : IntermediateField K Ω := IntermediateField.adjoin K ({z} : Set Ω)
    have halgE : Algebra.IsAlgebraic K E :=
      IntermediateField.isAlgebraic_adjoin_simple hz.isIntegral
    let z' : E := IntermediateField.AdjoinSimple.gen K z
    have hz'coe : (z' : Ω) = z := IntermediateField.AdjoinSimple.coe_gen K z
    -- the polynomial `z * s(T) - r(T)` over `K(z)` kills `x`
    let p : Polynomial E := Polynomial.C z' * s.map (algebraMap K E) - r.map (algebraMap K E)
    have hp : Polynomial.aeval x p = 0 := by
      have h1 : Polynomial.aeval x (Polynomial.C z') = z := by
        rw [Polynomial.aeval_C]
        exact IntermediateField.AdjoinSimple.algebraMap_gen K z
      have h2 : Polynomial.aeval x (s.map (algebraMap K E)) = Polynomial.aeval x s :=
        Polynomial.aeval_map_algebraMap E x s
      have h3 : Polynomial.aeval x (r.map (algebraMap K E)) = Polynomial.aeval x r :=
        Polynomial.aeval_map_algebraMap E x r
      dsimp only [p]
      rw [Polynomial.aeval_sub, Polynomial.aeval_mul, h1, h2, h3, hz_mul, sub_self]
    by_cases hp0 : p = 0
    · -- `p = 0`: comparing top coefficients of `z * s = r` exhibits `z` as an
      -- element of `K`
      have hcoeff : z' * (algebraMap K E) (s.coeff s.natDegree) =
          (algebraMap K E) (r.coeff s.natDegree) := by
        have h := congrArg (fun q : Polynomial E => q.coeff s.natDegree) hp0
        simp only [p, Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_map,
          Polynomial.coeff_zero] at h
        exact sub_eq_zero.mp h
      have hsd : s.coeff s.natDegree ≠ 0 := by
        rw [Polynomial.coeff_natDegree]
        exact Polynomial.leadingCoeff_ne_zero.mpr hs0
      have hfsd : (algebraMap K E) (s.coeff s.natDegree) ≠ 0 := fun h =>
        hsd (FaithfulSMul.algebraMap_injective K E (by simpa using h))
      have hz' : z' = (algebraMap K E) (r.coeff s.natDegree / s.coeff s.natDegree) := by
        rw [map_div₀, eq_div_iff hfsd]
        exact hcoeff
      rw [IntermediateField.mem_bot]
      refine ⟨r.coeff s.natDegree / s.coeff s.natDegree, ?_⟩
      rw [IsScalarTower.algebraMap_apply K E Ω, ← hz', IntermediateField.algebraMap_apply]
      exact hz'coe
    · -- `p ≠ 0`: `x` is algebraic over `K(z)`, hence over `K`, contradiction
      have : IsAlgebraic K x :=
        (Algebra.IsAlgebraic.isAlgebraic_iff K E).mpr ⟨p, hp0, hp⟩
      exact absurd this hx

end Work.MotV5
