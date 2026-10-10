import Mathlib
import Submission.Work.MotV.Defs
import Submission.Work.MotC.adjoin_genX_genY_eq_top

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The coefficient action of `Aut_𝕜(L)` on the function field `L(W)`

For a Weierstrass curve `W` over a field `𝕜`, a field `L` with a `𝕜`-algebra structure and a
`𝕜`-algebra automorphism `γ : L ≃ₐ[𝕜] L`, the function field of the base changed curve
`L(W) = FunctionField (W.baseChange L)` carries a `𝕜`-algebra automorphism acting on the constants
`L` by `γ` and fixing the generic point `x, y`.

The construction is the coefficient change `γ` on the affine coordinate ring
`CoordinateRing (W.baseChange L) = L[X, Y]/(W)`:  the polynomial `(W.baseChange L).polynomial` has
coefficients in the image of `𝕜`, whence `γ` (which fixes that image) leaves it unchanged; hence
`AdjoinRoot.lift` produces an endomorphism `coeffRingHom γ` of the coordinate ring, sending `X` to
`X`, `Y` to `Y` and the coefficient `a` to `γ a`.  The same construction with `γ.symm` is a two-sided
inverse (both are ring maps out of an `AdjoinRoot`, so `AdjoinRoot.ringHom_ext` applies), and it is
`𝕜`-linear, so it upgrades to an `AlgEquiv` of the coordinate ring.  Localizing at the nonzero
divisors (`IsFractionRing.liftAlgHom`, the target is a field) and comparing the composites once
more via `IsLocalization.algHom_ext` yields the desired automorphism of `L(W)`.
-/

open WeierstrassCurve WeierstrassCurve.Affine Polynomial

namespace Work.MotT

noncomputable section

variable {𝕜 : Type} [Field 𝕜] {W : WeierstrassCurve 𝕜} {L : Type} [Field L] [Algebra 𝕜 L]

/-! ## §1 The polynomial of the base change is fixed by a coefficient automorphism -/

/-- `γ` fixes the polynomial of `W.baseChange L`, because the latter has coefficients in the image
of `𝕜` and `γ` is a `𝕜`-algebra map. -/
theorem baseChange_polynomial_map (γ : L ≃ₐ[𝕜] L) :
    (WeierstrassCurve.Affine.polynomial (W.baseChange L)).map (mapRingHom (γ : L →+* L))
      = WeierstrassCurve.Affine.polynomial (W.baseChange L) := by
  rw [← WeierstrassCurve.Affine.map_polynomial]
  congr 1
  exact WeierstrassCurve.map_baseChange (W := W) (S := 𝕜) (A := L) (B := L) γ.toAlgHom

/-! ## §2 The induced endomorphism of the affine coordinate ring -/

/-- The coefficient change `γ` as a ring endomorphism of `CoordinateRing (W.baseChange L)`. -/
noncomputable def coeffRingHom (γ : L ≃ₐ[𝕜] L) :
    CoordinateRing (W.baseChange L) →+* CoordinateRing (W.baseChange L) :=
  AdjoinRoot.lift ((AdjoinRoot.of (WeierstrassCurve.Affine.polynomial (W.baseChange L))).comp
      (mapRingHom (γ : L →+* L))) (AdjoinRoot.root _) (by
    rw [← Polynomial.eval₂_map, baseChange_polynomial_map]
    exact AdjoinRoot.eval₂_root _)

lemma coeffRingHom_of (γ : L ≃ₐ[𝕜] L) (r : Polynomial L) :
    coeffRingHom (W := W) γ (AdjoinRoot.of (WeierstrassCurve.Affine.polynomial (W.baseChange L)) r)
      = AdjoinRoot.of _ (mapRingHom (γ : L →+* L) r) := by
  simp only [coeffRingHom]
  exact AdjoinRoot.lift_of _

lemma coeffRingHom_root (γ : L ≃ₐ[𝕜] L) :
    coeffRingHom (W := W) γ (AdjoinRoot.root (WeierstrassCurve.Affine.polynomial (W.baseChange L)))
      = AdjoinRoot.root _ := by
  simp only [coeffRingHom]
  exact AdjoinRoot.lift_root _

/-- `γ.symm` undoes the coefficient change on polynomials. -/
lemma mapRingHom_symm_comp_mapRingHom (γ : L ≃ₐ[𝕜] L) :
    (mapRingHom (γ.symm : L →+* L)).comp (mapRingHom (γ : L →+* L)) = RingHom.id (Polynomial L) := by
  rw [mapRingHom_comp]
  have h : ((γ.symm : L ≃ₐ[𝕜] L) : L →+* L).comp (γ : L →+* L) = RingHom.id L :=
    RingHom.ext (fun x => γ.symm_apply_apply x)
  rw [h, mapRingHom_id]

/-- `γ` undoes the coefficient change of `γ.symm` on polynomials. -/
lemma mapRingHom_comp_symm_mapRingHom (γ : L ≃ₐ[𝕜] L) :
    (mapRingHom (γ : L →+* L)).comp (mapRingHom (γ.symm : L →+* L)) = RingHom.id (Polynomial L) := by
  rw [mapRingHom_comp]
  have h : ((γ : L ≃ₐ[𝕜] L) : L →+* L).comp (γ.symm : L →+* L) = RingHom.id L :=
    RingHom.ext (fun x => γ.apply_symm_apply x)
  rw [h, mapRingHom_id]

lemma coeffRingHom_symm_comp (γ : L ≃ₐ[𝕜] L) :
    (coeffRingHom (W := W) γ.symm).comp (coeffRingHom (W := W) γ) = RingHom.id _ := by
  apply AdjoinRoot.ringHom_ext
  · apply RingHom.ext
    intro r
    show coeffRingHom (W := W) γ.symm (coeffRingHom (W := W) γ (AdjoinRoot.of _ r)) = AdjoinRoot.of _ r
    rw [coeffRingHom_of, coeffRingHom_of]
    exact congrArg (AdjoinRoot.of _) (congrArg (fun f : Polynomial L →+* Polynomial L => f r)
      (mapRingHom_symm_comp_mapRingHom γ))
  · show coeffRingHom (W := W) γ.symm (coeffRingHom (W := W) γ (AdjoinRoot.root _)) = AdjoinRoot.root _
    rw [coeffRingHom_root, coeffRingHom_root]

lemma coeffRingHom_comp_symm (γ : L ≃ₐ[𝕜] L) :
    (coeffRingHom (W := W) γ).comp (coeffRingHom (W := W) γ.symm) = RingHom.id _ := by
  apply AdjoinRoot.ringHom_ext
  · apply RingHom.ext
    intro r
    show coeffRingHom (W := W) γ (coeffRingHom (W := W) γ.symm (AdjoinRoot.of _ r)) = AdjoinRoot.of _ r
    rw [coeffRingHom_of, coeffRingHom_of]
    exact congrArg (AdjoinRoot.of _) (congrArg (fun f : Polynomial L →+* Polynomial L => f r)
      (mapRingHom_comp_symm_mapRingHom γ))
  · show coeffRingHom (W := W) γ (coeffRingHom (W := W) γ.symm (AdjoinRoot.root _)) = AdjoinRoot.root _
    rw [coeffRingHom_root, coeffRingHom_root]

lemma coeffRingHom_symm_apply (γ : L ≃ₐ[𝕜] L) (x) :
    coeffRingHom (W := W) γ.symm (coeffRingHom (W := W) γ x) = x :=
  congrArg (fun f : CoordinateRing (W.baseChange L) →+* CoordinateRing (W.baseChange L) => f x)
    (coeffRingHom_symm_comp γ)

lemma coeffRingHom_apply_symm (γ : L ≃ₐ[𝕜] L) (x) :
    coeffRingHom (W := W) γ (coeffRingHom (W := W) γ.symm x) = x :=
  congrArg (fun f : CoordinateRing (W.baseChange L) →+* CoordinateRing (W.baseChange L) => f x)
    (coeffRingHom_comp_symm γ)

lemma coeffRingHom_injective (γ : L ≃ₐ[𝕜] L) : Function.Injective (coeffRingHom (W := W) γ) := by
  intro x y h
  have h2 := congrArg (coeffRingHom (W := W) γ.symm) h
  rwa [coeffRingHom_symm_apply, coeffRingHom_symm_apply] at h2

/-! ## §3 The action on the constants -/

lemma algMap_eq_C (l : L) :
    algebraMap L (CoordinateRing (W.baseChange L)) l
      = AdjoinRoot.of (WeierstrassCurve.Affine.polynomial (W.baseChange L)) (Polynomial.C l) := by
  rw [IsScalarTower.algebraMap_apply L (Polynomial L) (CoordinateRing (W.baseChange L)),
      AdjoinRoot.algebraMap_eq]
  rfl

lemma coeffRingHom_algebraMapL (γ : L ≃ₐ[𝕜] L) (l : L) :
    coeffRingHom (W := W) γ (algebraMap L (CoordinateRing (W.baseChange L)) l)
      = algebraMap L (CoordinateRing (W.baseChange L)) (γ l) := by
  rw [algMap_eq_C, algMap_eq_C, coeffRingHom_of]
  simp only [Polynomial.coe_mapRingHom, Polynomial.map_C]
  rfl

lemma coeffRingHom_algebraMap (γ : L ≃ₐ[𝕜] L) (c : 𝕜) :
    coeffRingHom (W := W) γ (algebraMap 𝕜 (CoordinateRing (W.baseChange L)) c)
      = algebraMap 𝕜 (CoordinateRing (W.baseChange L)) c := by
  rw [IsScalarTower.algebraMap_apply 𝕜 L (CoordinateRing (W.baseChange L)),
      coeffRingHom_algebraMapL]
  exact congrArg (algebraMap L (CoordinateRing (W.baseChange L))) (γ.commutes c)

/-! ## §4 From the coordinate ring to the function field -/

/-- The coefficient change as a `𝕜`-algebra endomorphism of the affine coordinate ring. -/
noncomputable def coeffAlgHomCR (γ : L ≃ₐ[𝕜] L) :
    CoordinateRing (W.baseChange L) →ₐ[𝕜] CoordinateRing (W.baseChange L) :=
  AlgHom.mk (coeffRingHom γ) (fun c => coeffRingHom_algebraMap γ c)

/-- The coefficient change followed by the structure map into the function field. -/
noncomputable def coeffAlgHomField (γ : L ≃ₐ[𝕜] L) :
    CoordinateRing (W.baseChange L) →ₐ[𝕜] FunctionField (W.baseChange L) :=
  AlgHom.mk ((algebraMap (CoordinateRing (W.baseChange L)) (FunctionField (W.baseChange L))).comp
      (coeffRingHom γ)) (fun c => by
    show algebraMap (CoordinateRing (W.baseChange L)) (FunctionField (W.baseChange L))
        (coeffRingHom γ (algebraMap 𝕜 (CoordinateRing (W.baseChange L)) c))
      = algebraMap 𝕜 (FunctionField (W.baseChange L)) c
    rw [coeffRingHom_algebraMap]
    exact (IsScalarTower.algebraMap_apply 𝕜 (CoordinateRing (W.baseChange L))
      (FunctionField (W.baseChange L)) c).symm)

lemma coeffAlgHomField_apply (γ : L ≃ₐ[𝕜] L) (x : CoordinateRing (W.baseChange L)) :
    coeffAlgHomField (W := W) γ x
      = algebraMap (CoordinateRing (W.baseChange L)) (FunctionField (W.baseChange L))
          (coeffRingHom γ x) := rfl

lemma coeffAlgHomField_injective (γ : L ≃ₐ[𝕜] L) :
    Function.Injective (coeffAlgHomField (W := W) γ) := by
  intro x y h
  rw [coeffAlgHomField_apply, coeffAlgHomField_apply] at h
  exact coeffRingHom_injective γ (IsFractionRing.injective _ _ h)

/-- The coefficient change as a `𝕜`-algebra endomorphism of the function field `L(W)`. -/
noncomputable def coeffFieldHom (γ : L ≃ₐ[𝕜] L) :
    FunctionField (W.baseChange L) →ₐ[𝕜] FunctionField (W.baseChange L) :=
  IsFractionRing.liftAlgHom (coeffAlgHomField_injective γ)

lemma coeffFieldHom_algebraMap (γ : L ≃ₐ[𝕜] L) (x : CoordinateRing (W.baseChange L)) :
    coeffFieldHom (W := W) γ
        (algebraMap (CoordinateRing (W.baseChange L)) (FunctionField (W.baseChange L)) x)
      = algebraMap (CoordinateRing (W.baseChange L)) (FunctionField (W.baseChange L))
          (coeffRingHom γ x) := by
  simp only [coeffFieldHom, IsFractionRing.coe_liftAlgHom, IsFractionRing.lift_algebraMap]
  exact coeffAlgHomField_apply γ x

lemma coeffFieldHom_comp_symm (γ : L ≃ₐ[𝕜] L) :
    (coeffFieldHom (W := W) γ).comp (coeffFieldHom (W := W) γ.symm) = AlgHom.id 𝕜 _ := by
  apply IsLocalization.algHom_ext (nonZeroDivisors (CoordinateRing (W.baseChange L)))
  apply AlgHom.ext
  intro x
  show coeffFieldHom (W := W) γ (coeffFieldHom (W := W) γ.symm
      ((IsScalarTower.toAlgHom 𝕜 (CoordinateRing (W.baseChange L))
        (FunctionField (W.baseChange L))) x))
    = (IsScalarTower.toAlgHom 𝕜 (CoordinateRing (W.baseChange L))
        (FunctionField (W.baseChange L))) x
  rw [IsScalarTower.toAlgHom_apply, coeffFieldHom_algebraMap, coeffFieldHom_algebraMap,
    coeffRingHom_apply_symm]

lemma coeffFieldHom_symm_comp (γ : L ≃ₐ[𝕜] L) :
    (coeffFieldHom (W := W) γ.symm).comp (coeffFieldHom (W := W) γ) = AlgHom.id 𝕜 _ := by
  apply IsLocalization.algHom_ext (nonZeroDivisors (CoordinateRing (W.baseChange L)))
  apply AlgHom.ext
  intro x
  show coeffFieldHom (W := W) γ.symm (coeffFieldHom (W := W) γ
      ((IsScalarTower.toAlgHom 𝕜 (CoordinateRing (W.baseChange L))
        (FunctionField (W.baseChange L))) x))
    = (IsScalarTower.toAlgHom 𝕜 (CoordinateRing (W.baseChange L))
        (FunctionField (W.baseChange L))) x
  rw [IsScalarTower.toAlgHom_apply, coeffFieldHom_algebraMap, coeffFieldHom_algebraMap,
    coeffRingHom_symm_apply]

/-- The coefficient action of `Aut_𝕜(L)` on the function field `L(W)`. -/
noncomputable def coeffAlgEquivAux (γ : L ≃ₐ[𝕜] L) :
    FunctionField (W.baseChange L) ≃ₐ[𝕜] FunctionField (W.baseChange L) :=
  AlgEquiv.ofAlgHom (coeffFieldHom γ) (coeffFieldHom γ.symm)
    (coeffFieldHom_comp_symm γ) (coeffFieldHom_symm_comp γ)

lemma coeffAlgEquivAux_algebraMap (γ : L ≃ₐ[𝕜] L) (l : L) :
    coeffAlgEquivAux (W := W) γ (algebraMap L (FunctionField (W.baseChange L)) l)
      = algebraMap L (FunctionField (W.baseChange L)) (γ l) := by
  show coeffFieldHom (W := W) γ (algebraMap L (FunctionField (W.baseChange L)) l)
      = algebraMap L (FunctionField (W.baseChange L)) (γ l)
  rw [IsScalarTower.algebraMap_apply L (CoordinateRing (W.baseChange L))
    (FunctionField (W.baseChange L))]
  rw [coeffFieldHom_algebraMap, coeffRingHom_algebraMapL]
  rw [← IsScalarTower.algebraMap_apply L (CoordinateRing (W.baseChange L))
    (FunctionField (W.baseChange L))]

/-! ## §5 The generic point -/

lemma genX_bridge : Work.MotV.genX (W.baseChange L)
    = algebraMap (CoordinateRing (W.baseChange L)) (FunctionField (W.baseChange L))
        (AdjoinRoot.of (WeierstrassCurve.Affine.polynomial (W.baseChange L)) Polynomial.X) := by
  simp only [Work.MotV.genX, WeierstrassCurve.Affine.CoordinateRing.mk, AdjoinRoot.mk_C]

lemma genY_bridge : Work.MotV.genY (W.baseChange L)
    = algebraMap (CoordinateRing (W.baseChange L)) (FunctionField (W.baseChange L))
        (AdjoinRoot.root (WeierstrassCurve.Affine.polynomial (W.baseChange L))) := by
  simp only [Work.MotV.genY, WeierstrassCurve.Affine.CoordinateRing.mk, AdjoinRoot.mk_X]

lemma coeffAlgEquivAux_genX (γ : L ≃ₐ[𝕜] L) :
    coeffAlgEquivAux (W := W) γ (Work.MotV.genX (W.baseChange L))
      = Work.MotV.genX (W.baseChange L) := by
  show coeffFieldHom (W := W) γ (Work.MotV.genX (W.baseChange L))
      = Work.MotV.genX (W.baseChange L)
  rw [genX_bridge, coeffFieldHom_algebraMap, coeffRingHom_of]
  simp only [Polynomial.coe_mapRingHom, Polynomial.map_X]

lemma coeffAlgEquivAux_genY (γ : L ≃ₐ[𝕜] L) :
    coeffAlgEquivAux (W := W) γ (Work.MotV.genY (W.baseChange L))
      = Work.MotV.genY (W.baseChange L) := by
  show coeffFieldHom (W := W) γ (Work.MotV.genY (W.baseChange L))
      = Work.MotV.genY (W.baseChange L)
  rw [genY_bridge, coeffFieldHom_algebraMap]
  exact congrArg _ (coeffRingHom_root γ)

end

/-- **The coefficient action of `Aut_𝕜(L)` on `L(W)`.**  For a field `L` with a `𝕜`-algebra
structure and a `𝕜`-algebra automorphism `γ : L ≃ₐ[𝕜] L`, the function field
`L(W) = FunctionField (W.baseChange L)` of the base-changed curve carries a `𝕜`-algebra
automorphism `g` acting on the constants `L` by `γ` and fixing the generic point `x, y` (so `g` is
unique, since `L(x, y) = L(W)`).  Declare it in namespace `Work.MotT`.

Route.  `W.baseChange L = W.map (algebraMap 𝕜 L)`, so `(W.baseChange L).map γ.toRingHom` is
`W.map (γ ∘ algebraMap 𝕜 L) = W.map (algebraMap 𝕜 L) = W.baseChange L` because `γ` fixes the image
of `𝕜`.  `WeierstrassCurve.Affine.CoordinateRing.map (γ : L →+* L)` therefore gives an endomorphism
of `CoordinateRing (W.baseChange L)` whose effect on `mk (C a)` is `mk (C (γ a))` and which fixes
`mk (C X)` and `mk Y` (`CoordinateRing.map_mk`); extend it to `FunctionField` using
`IsLocalization.liftAlgHom` (the target is a field) and use the case `γ⁻¹` to see it is an
`AlgEquiv` (the two composites agree on `L`, `x`, `y`, which generate `L(W)` over `𝕜` by
`Work.MotC.adjoin_genX_genY_eq_top` together with the `L`-structure). -/
theorem coeffAlgEquiv (𝕜 : Type) [Field 𝕜] (W : WeierstrassCurve 𝕜) (L : Type) [Field L]
    [Algebra 𝕜 L] (γ : L ≃ₐ[𝕜] L) :
    ∃ g : WeierstrassCurve.Affine.FunctionField (W.baseChange L) ≃ₐ[𝕜] WeierstrassCurve.Affine.FunctionField (W.baseChange L),
      (∀ l : L, g (algebraMap L _ l) = algebraMap L _ (γ l)) ∧
      g (Work.MotV.genX (W.baseChange L)) = Work.MotV.genX (W.baseChange L) ∧
      g (Work.MotV.genY (W.baseChange L)) = Work.MotV.genY (W.baseChange L) :=
  ⟨coeffAlgEquivAux γ, coeffAlgEquivAux_algebraMap γ, coeffAlgEquivAux_genX γ,
    coeffAlgEquivAux_genY γ⟩

end Work.MotT
