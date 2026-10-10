import Mathlib
import Submission.Work.MotA.Spread

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Injectivity of the spreading-out map `Work.MotA.spreadMap`

`Work.MotA.spreadMap 𝕜 n : 𝕜[t, x₁,…,xₙ] →ₐ[𝕜] MvPolynomial (Fin n) (RatFunc 𝕜)` sends
`t ↦ RatFunc.X` and `x_j ↦ X_j`.  The target is the polynomial ring in `x₁,…,xₙ` whose coefficient
ring is the rational function field `K = RatFunc 𝕜`.  Factoring

`𝕜[t, x₁,…,xₙ] ≃ₐ[𝕜] 𝕜[x₁,…,xₙ][t]`  (`spreadRatFuncEquiv`, currying the variable `t` into a
coefficient) followed by the *coefficient* map `𝕜[t] → K`, which is injective (a fraction ring of a
domain is a domain, so `IsFractionRing.injective` applies, and `MvPolynomial.map` preserves
injectivity), exhibits `spreadMap 𝕜 n` as a composite of two injective maps.  This is the route taken
below.
-/

noncomputable section

namespace Work.MotA

open MvPolynomial

/-- Currying the variable `t = x₀` into the coefficient ring:
`𝕜[t, x₁,…,xₙ] ≃ₐ[𝕜] 𝕜[x₁,…,xₙ][t]`, sending `t` to the polynomial variable and `x_j` to `x_j`. -/
noncomputable def spreadRatFuncEquiv (𝕜 : Type) [CommSemiring 𝕜] (n : ℕ) :
    MvPolynomial (Fin (n + 1)) 𝕜 ≃ₐ[𝕜] MvPolynomial (Fin n) (Polynomial 𝕜) :=
  (MvPolynomial.renameEquiv 𝕜 (_root_.finSuccEquiv n)).trans
    (MvPolynomial.optionEquivRight 𝕜 (Fin n))

@[simp]
theorem spreadRatFuncEquiv_X_zero (𝕜 : Type) [CommSemiring 𝕜] (n : ℕ) :
    spreadRatFuncEquiv 𝕜 n (MvPolynomial.X 0) =
      MvPolynomial.C (Polynomial.X : Polynomial 𝕜) := by
  simp [spreadRatFuncEquiv, _root_.finSuccEquiv_zero]

@[simp]
theorem spreadRatFuncEquiv_X_succ (𝕜 : Type) [CommSemiring 𝕜] (n : ℕ) (j : Fin n) :
    spreadRatFuncEquiv 𝕜 n (MvPolynomial.X j.succ) = MvPolynomial.X j := by
  simp [spreadRatFuncEquiv, _root_.finSuccEquiv_succ]

@[simp]
theorem spreadRatFuncEquiv_C (𝕜 : Type) [CommSemiring 𝕜] (n : ℕ) (r : 𝕜) :
    spreadRatFuncEquiv 𝕜 n (MvPolynomial.C r) = MvPolynomial.C (Polynomial.C r) := by
  simp [spreadRatFuncEquiv]

/-- The coefficient map `𝕜[x₁,…,xₙ][t] →ₐ[𝕜] 𝕜[x₁,…,xₙ](t)`, i.e. `MvPolynomial.map` along the
inclusion `𝕜[t] ↪ K = RatFunc 𝕜` of the polynomial ring into its fraction field. -/
noncomputable def spreadCoeffMap (𝕜 : Type) [Field 𝕜] (n : ℕ) :
    MvPolynomial (Fin n) (Polynomial 𝕜) →ₐ[𝕜] MvPolynomial (Fin n) (RatFunc 𝕜) :=
  (MvPolynomial.mapAlgHom (Algebra.ofId (Polynomial 𝕜) (RatFunc 𝕜))).restrictScalars 𝕜

@[simp]
theorem spreadCoeffMap_C (𝕜 : Type) [Field 𝕜] (n : ℕ) (a : Polynomial 𝕜) :
    spreadCoeffMap 𝕜 n (MvPolynomial.C a) =
      MvPolynomial.C (algebraMap (Polynomial 𝕜) (RatFunc 𝕜) a) := by
  simp [spreadCoeffMap]

@[simp]
theorem spreadCoeffMap_X (𝕜 : Type) [Field 𝕜] (n : ℕ) (j : Fin n) :
    spreadCoeffMap 𝕜 n (MvPolynomial.X j) = MvPolynomial.X j := by
  simp [spreadCoeffMap]

/-- **The factorisation of `spreadMap`.**  Sending `t` to `RatFunc.X` and the `x_j` to themselves is
the same as first currying `t` into the coefficient ring and then applying the coefficient map
`𝕜[t] → RatFunc 𝕜`. -/
theorem spreadMap_eq_spreadCoeffMap_comp (𝕜 : Type) [Field 𝕜] (n : ℕ) :
    Work.MotA.spreadMap 𝕜 n =
      (spreadCoeffMap 𝕜 n).comp (spreadRatFuncEquiv 𝕜 n).toAlgHom := by
  apply MvPolynomial.algHom_ext
  intro i
  induction i using Fin.cases with
  | zero => simp [AlgHom.comp_apply]
  | succ j => simp [AlgHom.comp_apply]

/-- `spreadMap 𝕜 n` is injective: it is the composite of the algebra equivalence
`spreadRatFuncEquiv 𝕜 n` with the coefficient map `spreadCoeffMap 𝕜 n`, which is injective because
`𝕜[t] → RatFunc 𝕜` is injective. -/
theorem spreadMap_injective (𝕜 : Type) [Field 𝕜] (n : ℕ) :
    Function.Injective (Work.MotA.spreadMap 𝕜 n) := by
  have hmap : Function.Injective (spreadCoeffMap 𝕜 n) := by
    intro a b hab
    exact MvPolynomial.map_injective (algebraMap (Polynomial 𝕜) (RatFunc 𝕜))
      (IsFractionRing.injective (Polynomial 𝕜) (RatFunc 𝕜)) hab
  rw [spreadMap_eq_spreadCoeffMap_comp 𝕜 n]
  intro a b h
  simp only [AlgHom.comp_apply] at h
  exact (spreadRatFuncEquiv 𝕜 n).injective (hmap h)

end Work.MotA
