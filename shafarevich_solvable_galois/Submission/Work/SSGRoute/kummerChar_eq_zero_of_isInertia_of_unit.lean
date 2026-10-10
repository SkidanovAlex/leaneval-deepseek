import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.Algebra.Order.Ring.Star
import Submission.Work.SSGRoute.ZConstruction.localKummerDictionary
import Submission.Work.SSGRoute.grunwald_surjective_two
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

set_option linter.unusedVariables false

/-- **The Kummer character of a local unit kills the inertia.**  If `A ∤ 2` and `a ∈ Kˣ` is a unit
at `A`, then the global Kummer character of `a` vanishes on the inertia group of `A` over `K`: the
local Kummer extension is unramified. -/
theorem kummerChar_eq_zero_of_isInertia_of_unit
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ 2)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) (h2 : ¬ A.valuation (2 : Ω) < 1)
    (a : (↥K)ˣ) (ha : A.valuation (algebraMap ↥K Ω (a : ↥K)) = 1)
    (σ : Ω ≃ₐ[↥K] Ω) (hσ : SSGRoute.IsInertia (k := ↥K) A σ) :
    Work.SSGRoute.kummerChar (Ω := Ω) ζ hζ a σ = 0 := by
  -- A square root `γ` of the unit `a`; it is again a unit at `A`.
  set γ : Ω := kummerSqrtVal (K := ↥K) (Ω := Ω) a with hγdef
  have hγsq : γ ^ 2 = algebraMap ↥K Ω (a : ↥K) := kummerSqrtVal_pow (K := ↥K) (Ω := Ω) a
  -- `a` is integral at `A` (it is a unit), whence so is its square root `γ`.
  have hmem_a : algebraMap ↥K Ω (a : ↥K) ∈ A := by
    rw [← ValuationSubring.valuation_le_one_iff]; exact le_of_eq ha
  have hγA : γ ∈ A := by
    have hIC : IsIntegrallyClosedIn ↥A.toSubring Ω :=
      Subring.isIntegrallyClosedIn_iff.mpr fun z hz =>
        LocalSubring.mem_of_isMax_of_isIntegral A.isMax_toLocalSubring hz
    have hint : IsIntegral ↥A.toSubring γ := by
      refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
      rw [hγsq]
      exact isIntegral_algebraMap (x := (⟨algebraMap ↥K Ω (a : ↥K), hmem_a⟩ : ↥A.toSubring))
    exact (Subring.isIntegrallyClosedIn_iff.mp hIC) hint
  -- `2` is a unit at `A`, since `A ∤ 2`.
  have h2A : (2 : Ω) ∈ A := by
    have hh : (2 : Ω) = 1 + 1 := by norm_num
    rw [hh]; exact A.add_mem 1 1 A.one_mem A.one_mem
  have hval2_le : A.valuation (2 : Ω) ≤ 1 := (ValuationSubring.valuation_le_one_iff A _).mpr h2A
  have hval2 : A.valuation (2 : Ω) = 1 := le_antisymm hval2_le (not_lt.mp h2)
  -- `σ` fixes `a`, so `σ γ` is a square root of `a` as well.
  have hsq : (σ γ) ^ 2 = γ ^ 2 := by
    rw [← map_pow σ γ 2, hγsq]
    exact AlgEquiv.commutes σ (a : ↥K)
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
  · -- `σ γ = γ`: the Kummer character vanishes.
    refine kummerIdx_eq_zero_of_apply_eq 2 hζ a (kummerSqrt (Ω := Ω) a)
      (kummerSqrt_pow (Ω := Ω) a) σ ?_
    simpa only [kummerSqrt, Units.val_mk0] using h
  · -- `σ γ = -γ`: the inertia condition would force `γ` to be non-integral, impossible.
    exfalso
    have hlt := hσ.2 γ hγA
    have hneg : σ γ - γ = -((2 : Ω) * γ) := by rw [h]; ring
    rw [hneg, Valuation.map_neg, Valuation.map_mul, hval2, one_mul] at hlt
    have heq : A.valuation γ * A.valuation γ = 1 := by
      rw [← Valuation.map_mul, ← pow_two, hγsq, ha]
    have hγpos : 0 < A.valuation γ := by
      rw [pos_iff_ne_zero]
      intro hz
      rw [hz] at heq
      simp only [zero_mul] at heq
      exact one_ne_zero heq.symm
    have hlt2 : A.valuation γ * A.valuation γ < 1 :=
      calc A.valuation γ * A.valuation γ < 1 * A.valuation γ :=
            mul_lt_mul_of_pos_right hlt hγpos
        _ = A.valuation γ := one_mul _
        _ < 1 := hlt
    rw [heq] at hlt2
    exact lt_irrefl 1 hlt2

end Work.SSGRoute
