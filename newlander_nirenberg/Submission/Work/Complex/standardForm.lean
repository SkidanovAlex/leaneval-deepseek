import Mathlib
import Submission.Work.Core.Defs

set_option linter.style.haveILetI false

namespace Work.Complex

open LeanEval.Geometry.NewlanderNirenberg
open Submission

/-- Every real-linear complex structure `J` (`J ∘ J = -1`) on `E n = ℝ^{2n}` is linearly
isomorphic to the standard complex structure on `ℂⁿ = F n`: there is a real-linear
isomorphism `T` with `T (J v) = i • T v`. -/
theorem standardForm {n : ℕ} (J : E n →L[ℝ] E n) (hJ : ∀ v, J (J v) = -v) :
    ∃ T : E n ≃L[ℝ] F n, ∀ v, T (J v) = Complex.I • T v := by
  -- `J` as an element of the endomorphism ring, with `J * J = -1`.
  have hJJ : (J.toLinearMap : Module.End ℝ (E n)) * J.toLinearMap = -1 := by
    ext v; simp [hJ]
  -- The `ℝ`-algebra map `ℂ →ₐ[ℝ] End_ℝ(E n)` sending `i` to `J`.
  let φ : ℂ →ₐ[ℝ] Module.End ℝ (E n) := Complex.liftAux J.toLinearMap hJJ
  -- The complex vector space structure on `E n` induced by `J`.
  letI : Module ℂ (E n) := Module.compHom (E n) φ.toRingHom
  haveI htower : IsScalarTower ℝ ℂ (E n) := by
    refine ⟨fun r c v => ?_⟩
    show φ (r • c) v = r • (φ c v)
    rw [Algebra.smul_def, map_mul]
    show (φ (algebraMap ℝ ℂ r)) ((φ c) v) = r • (φ c v)
    rw [show φ (algebraMap ℝ ℂ r) = algebraMap ℝ (Module.End ℝ (E n)) r from φ.commutes r]
    rfl
  -- Multiplication by `i` in this structure is `J`.
  have hI : ∀ v : E n, (Complex.I : ℂ) • v = J v := by
    intro v
    show φ Complex.I v = J v
    rw [Complex.liftAux_apply_I]
    rfl
  -- `E n` is a finite-dimensional complex vector space (of dimension `n`).
  haveI : Module.Finite ℂ (E n) := Module.Finite.of_restrictScalars_finite ℝ ℂ (E n)
  have hfr : Module.finrank ℂ (E n) = n := by
    have h := Module.finrank_mul_finrank ℝ ℂ (E n)
    rw [Complex.finrank_real_complex, finrank_euclideanSpace, Fintype.card_fin] at h
    exact Nat.mul_left_cancel (by norm_num) h
  have hfrF : Module.finrank ℂ (F n) = n := by
    rw [finrank_euclideanSpace, Fintype.card_fin]
  -- Identify the two `n`-dimensional complex vector spaces.
  have e : E n ≃ₗ[ℂ] F n := LinearEquiv.ofFinrankEq (E n) (F n) (by rw [hfr, hfrF])
  -- Forget the complex structure and make it continuous over `ℝ`.
  refine ⟨(e.restrictScalars ℝ).toContinuousLinearEquiv, ?_⟩
  intro v
  rw [← hI v]
  show ((e.restrictScalars ℝ).toContinuousLinearEquiv) (Complex.I • v)
      = Complex.I • ((e.restrictScalars ℝ).toContinuousLinearEquiv) v
  exact e.map_smul Complex.I v

end Work.Complex
