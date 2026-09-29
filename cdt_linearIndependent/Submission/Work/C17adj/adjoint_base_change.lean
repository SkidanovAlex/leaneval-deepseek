import Mathlib
import Submission.Work.C17.adjoint_defs

/-!
# Base change `ℚ(x) → ℂ(x)` for the adjoint certificate

`Work.C17.toC : RatFunc ℚ → RatFunc ℂ` is the base change along `ℚ → ℂ`.  Here we show that it
is a ring homomorphism (`T` below), that it commutes with the rational-function derivation
`Submission.CDT.dRat`, and that it sends the `ℚ`-data (`P2Q`, `P1Q`, `P0Q`, `yQ`, `dyQ`) to the
`ℂ`-data (`Pac`, `Pbc`, `Pcc`, `yQc`, `dyQc`).  Consequently a relation in `ℚ(x)` between the
`y`-integrands transfers to `ℂ(x)` (`adjoint_base_change`).
-/

namespace Work.C17adj

open Polynomial

noncomputable section

/-- `Polynomial.map` along `ℚ → ℂ`, as an algebra homomorphism. -/
theorem baseChange_map_injective : Function.Injective (Polynomial.mapRingHom (algebraMap ℚ ℂ)) := by
  rw [Polynomial.coe_mapRingHom]
  exact Polynomial.map_injective _ (algebraMap ℚ ℂ).injective

/-- The non-zero-divisor condition for `RatFunc.map`. -/
theorem baseChange_nzd :
    nonZeroDivisors ℚ[X] ≤ Submonoid.comap (Polynomial.mapRingHom (algebraMap ℚ ℂ))
      (nonZeroDivisors ℂ[X]) :=
  nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
    (by rw [Polynomial.coe_mapRingHom]
        exact Polynomial.map_injective _ (algebraMap ℚ ℂ).injective)

/-- The base change `ℚ(x) → ℂ(x)` as a ring homomorphism. -/
noncomputable def T : RatFunc ℚ →+* RatFunc ℂ :=
  RatFunc.mapRingHom (Polynomial.mapRingHom (algebraMap ℚ ℂ)) baseChange_nzd

/-- `T` maps a polynomial to the image polynomial. -/
theorem T_algebraMap (p : Polynomial ℚ) :
    T (algebraMap (Polynomial ℚ) (RatFunc ℚ) p)
      = algebraMap (Polynomial ℂ) (RatFunc ℂ) (p.map (algebraMap ℚ ℂ)) := by
  rw [show algebraMap (Polynomial ℚ) (RatFunc ℚ) p
        = algebraMap (Polynomial ℚ) (RatFunc ℚ) p
          / algebraMap (Polynomial ℚ) (RatFunc ℚ) (1 : Polynomial ℚ) by simp]
  unfold T
  rw [RatFunc.coe_mapRingHom_eq_coe_map, RatFunc.map_apply_div]
  simp [Polynomial.coe_mapRingHom]

/-- `T` agrees with `Work.C17.toC`. -/
theorem T_eq_toC (β : RatFunc ℚ) : T β = Work.C17.toC β := by
  unfold T Work.C17.toC
  rw [RatFunc.coe_mapRingHom_eq_coe_map, RatFunc.map_apply]
  rfl

/-- `T` sends rational constants to rational constants. -/
theorem T_rat (r : ℚ) : T (algebraMap ℚ (RatFunc ℚ) r) = algebraMap ℂ (RatFunc ℂ) r := by
  rw [IsScalarTower.algebraMap_apply ℚ (Polynomial ℚ) (RatFunc ℚ), T_algebraMap]
  rw [show (algebraMap ℚ ℚ[X]) r = Polynomial.C r from (Polynomial.C_eq_algebraMap r).symm]
  rw [Polynomial.map_C, Polynomial.C_eq_algebraMap]
  rw [← IsScalarTower.algebraMap_apply ℂ (Polynomial ℂ) (RatFunc ℂ)]
  simp

/-- `T` sends rational constants (as casts) to rational constants. -/
theorem T_ratcast (r : ℚ) : T (r : RatFunc ℚ) = algebraMap ℂ (RatFunc ℂ) r := by
  simpa using T_rat r

/-! ## Commutation with `dRat` -/

theorem T_dRatF (p q : Polynomial ℚ) :
    T (Submission.CDT.dRatF p q)
      = Submission.CDT.dRatF (p.map (algebraMap ℚ ℂ)) (q.map (algebraMap ℚ ℂ)) := by
  rw [Submission.CDT.dRatF, Submission.CDT.dRatF]
  rw [map_div₀, map_pow, T_algebraMap, T_algebraMap]
  congr 1
  rw [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_mul]
  rw [← Polynomial.derivative_map (p := p), ← Polynomial.derivative_map (p := q)]

/-- `T` commutes with the derivation `dRat`. -/
theorem T_dRat (f : RatFunc ℚ) : T (Submission.CDT.dRat f) = Submission.CDT.dRat (T f) := by
  have hTf : T f = algebraMap (Polynomial ℂ) (RatFunc ℂ) (f.num.map (algebraMap ℚ ℂ))
      / algebraMap (Polynomial ℂ) (RatFunc ℂ) (f.denom.map (algebraMap ℚ ℂ)) := by
    conv_lhs => rw [Submission.CDT.num_denom_eq f]
    rw [map_div₀, T_algebraMap, T_algebraMap]
  rw [Submission.CDT.dRat_eq_dRatF f, hTf, T_dRatF, Submission.CDT.dRat_div]
  rfl

/-! ## The images of the `ℚ`-data -/

theorem T_X : T (RatFunc.X : RatFunc ℚ)
    = algebraMap (Polynomial ℂ) (RatFunc ℂ) Polynomial.X := by
  unfold RatFunc.X
  rw [T_algebraMap, Polynomial.map_X]

theorem T_yQ : T Work.C17.yQ = Work.C17.yQc := by
  unfold Work.C17.yQ Work.C17.yQc Work.C17.xQ
  simp only [map_div₀, map_pow, map_sub, map_one, T_X]

theorem T_dyQ : T Work.C17.dyQ = Work.C17.dyQc := by
  unfold Work.C17.dyQ Work.C17.dyQc Work.C17.xQ
  simp only [map_div₀, map_pow, map_sub, map_mul, map_ofNat, map_one, T_X]

theorem T_P2Q (a b : ℚ) : T (Work.C17.P2Q a b) = Work.C17.Pac a b := by
  unfold Work.C17.P2Q Work.C17.Pac Work.C17.P2Cc
  rw [T_algebraMap]

theorem T_P1Q (a b : ℚ) : T (Work.C17.P1Q a b) = Work.C17.Pbc a b := by
  unfold Work.C17.P1Q Work.C17.Pbc Work.C17.P1Cc
  rw [T_algebraMap]

theorem T_P0Q (a b : ℚ) : T (Work.C17.P0Q a b) = Work.C17.Pcc a b := by
  unfold Work.C17.P0Q Work.C17.Pcc Work.C17.P0Cc
  rw [T_algebraMap]

/-- **Base change of the adjoint relation.**  A relation in `ℚ(x)` between the `y`-integrands
base-changes to the same relation in `ℂ(x)`. -/
theorem adjoint_base_change (a b : ℚ) (β : RatFunc ℚ) (c : Fin 6 → ℚ)
    (h : Submission.CDT.dRat (Submission.CDT.dRat (Work.C17.P2Q a b * β))
        - Submission.CDT.dRat (Work.C17.P1Q a b * β) + Work.C17.P0Q a b * β
      = ∑ i : Fin 6, (c i : RatFunc ℚ) * Work.C17.yQ ^ ((i : ℤ) - 4) * Work.C17.dyQ) :
    Submission.CDT.dRat (Submission.CDT.dRat (Work.C17.Pac a b * Work.C17.toC β))
        - Submission.CDT.dRat (Work.C17.Pbc a b * Work.C17.toC β) + Work.C17.Pcc a b * Work.C17.toC β
      = ∑ i : Fin 6, algebraMap ℂ (RatFunc ℂ) (c i) * Work.C17.yQc ^ ((i : ℤ) - 4) * Work.C17.dyQc := by
  have key := congrArg T h
  simp only [map_sub, map_add, map_mul, map_sum, map_zpow₀, T_dRat] at key
  rw [T_P2Q a b, T_P1Q a b, T_P0Q a b, T_eq_toC β, T_yQ, T_dyQ] at key
  simp only [T_ratcast] at key
  exact key

end

end Work.C17adj
