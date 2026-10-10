import Mathlib
import Submission.Work.MotT.T4Setup
import Submission.Work.MotV.Defs
import Submission.Work.MotC2.FuncExt
import Submission.Work.MotC2.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotT

open WeierstrassCurve WeierstrassCurve.Affine

/-- **An `L`-algebra automorphism of the function field `L(E)` fixing every Klein ratio `κᵢ/κ₀`
is the identity.**

Let `D` be a good Klein datum over `K` and `L` a `K`-field.  By `KleinData.Good.spans`, every
element of the basis `1, x, y, x², xy` of `L(5·O)` is an `L`-linear combination of the Klein
coordinates `κᵢ`.  The case `m = 0` of `spans` reads `1 = ∑ᵢ eᵢ κᵢ` with `eᵢ ∈ K`, i.e. (using
`κᵢ = κ₀·(κᵢ/κ₀)` and `κ₀ ≠ 0`, which is `KleinData.Good.coord0_ne`)

  `κ₀⁻¹ = ∑ᵢ eᵢ (κᵢ/κ₀) ∈ L(κᵢ/κ₀)`,

whence `κ₀ ∈ L(κᵢ/κ₀)`; the cases `m = 1, 2` then give `x, y ∈ L(κᵢ/κ₀)`.  Since
`L(x, y) = L(E)`, the Klein ratios generate the function field over `L`, so an `L`-algebra
automorphism fixing all of them is the identity. -/
theorem algEquiv_eq_one_of_kleinCoord_ratio_gen {K : Type} [Field K] (D : Work.MotV.KleinData K)
    (hD : D.Good) (L : Type) [Field L] [Algebra K L]
    (σ : Affine.FunctionField (D.E.baseChange L) ≃ₐ[L] Affine.FunctionField (D.E.baseChange L))
    (hσ : ∀ i : Fin 5, σ (Work.MotV.kleinCoord D L i / Work.MotV.kleinCoord D L 0) =
      Work.MotV.kleinCoord D L i / Work.MotV.kleinCoord D L 0) :
    σ = 1 := by
  obtain ⟨e, he⟩ := hD.spans
  have hκ0 : Work.MotV.kleinCoord D L 0 ≠ 0 := hD.coord0_ne L
  -- `kleinBas m = κ₀ · ∑ᵢ e_{mi} (κᵢ/κ₀)`
  have hsplit : ∀ m : Fin 5,
      Work.MotV.kleinBas D L m =
        Work.MotV.kleinCoord D L 0 *
          ∑ i : Fin 5, algebraMap L _ (algebraMap K L (e m i)) *
            (Work.MotV.kleinCoord D L i / Work.MotV.kleinCoord D L 0) := by
    intro m
    rw [he L m, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_div_assoc, mul_div_cancel₀ _ hκ0]
  -- the case `m = 0`: `∑ᵢ e_{0i} (κᵢ/κ₀) = κ₀⁻¹`
  have hS0 : (∑ i : Fin 5, algebraMap L _ (algebraMap K L (e 0 i)) *
            (Work.MotV.kleinCoord D L i / Work.MotV.kleinCoord D L 0))
        = (Work.MotV.kleinCoord D L 0)⁻¹ := by
    have h := hsplit 0
    rw [show Work.MotV.kleinBas D L 0 =
        (1 : Affine.FunctionField (D.E.baseChange L)) from rfl] at h
    exact eq_inv_of_mul_eq_one_right h.symm
  -- `σ` fixes each sum `∑ᵢ e_{mi} (κᵢ/κ₀)`
  have hSfix : ∀ m : Fin 5, σ (∑ i : Fin 5, algebraMap L _ (algebraMap K L (e m i)) *
            (Work.MotV.kleinCoord D L i / Work.MotV.kleinCoord D L 0)) =
          (∑ i : Fin 5, algebraMap L _ (algebraMap K L (e m i)) *
            (Work.MotV.kleinCoord D L i / Work.MotV.kleinCoord D L 0)) := by
    intro m
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, hσ i, σ.commutes]
  -- hence `σ` fixes `κ₀`
  have hκ0fix : σ (Work.MotV.kleinCoord D L 0) = Work.MotV.kleinCoord D L 0 := by
    have hκ : Work.MotV.kleinCoord D L 0 =
        (∑ i : Fin 5, algebraMap L _ (algebraMap K L (e 0 i)) *
          (Work.MotV.kleinCoord D L i / Work.MotV.kleinCoord D L 0))⁻¹ := by
      rw [hS0, inv_inv]
    rw [hκ, map_inv₀, hSfix 0, hκ]
  -- and therefore every element of the basis `1, x, y, x², xy`
  have hbasefix : ∀ m : Fin 5, σ (Work.MotV.kleinBas D L m) = Work.MotV.kleinBas D L m := by
    intro m
    rw [hsplit m, map_mul, hκ0fix, hSfix m]
  -- so `σ` fixes `x` and `y`, which generate `L(E)` over `L`
  refine Work.MotC2.funcAlgEquiv_ext_genX_genY (D.E.baseChange L) σ 1 ?_ ?_
  · rw [AlgEquiv.one_apply]; exact hbasefix 1
  · rw [AlgEquiv.one_apply]; exact hbasefix 2

theorem algEquiv_eq_one_of_kleinCoord_ratio {K : Type} [Field K] (D : Work.MotV.KleinData K)
    (hD : D.Good) (h₁ h₂ : K) (hk : ringChar K ≠ 5)
    (σ : ML2 D h₁ h₂ hk ≃ₐ[↥(KummerField2 K h₁ h₂ hk)] ML2 D h₁ h₂ hk)
    (hσ : ∀ i : Fin 5, σ (Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) i /
        Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) 0) =
      Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) i /
        Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) 0) :
    σ = 1 :=
  algEquiv_eq_one_of_kleinCoord_ratio_gen D hD ↥(KummerField2 K h₁ h₂ hk) σ hσ

end Work.MotT
