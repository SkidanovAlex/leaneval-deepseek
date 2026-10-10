import Mathlib
import Submission.Work.MotV.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open WeierstrassCurve WeierstrassCurve.Affine

namespace Work.MotT

section BaseChange

variable (𝕜 : Type) [Field 𝕜] (W : WeierstrassCurve 𝕜)
  (L L' : Type) [Field L] [Field L'] [Algebra 𝕜 L] [Algebra 𝕜 L'] (f : L →ₐ[𝕜] L')

/-- The ring homomorphism `CoordinateRing.map` induced by `f` is compatible with the structure
maps of the base fields: it sends `algebraMap L _ l` to `algebraMap L' _ (f l)`. -/
private lemma coordinateRing_map_algebraMap (l : L) :
    CoordinateRing.map (W.baseChange L) f.toRingHom
        (algebraMap L (CoordinateRing (W.baseChange L)) l)
      = algebraMap L' (CoordinateRing ((W.baseChange L).map f.toRingHom)) (f l) := by
  rw [show algebraMap L (CoordinateRing (W.baseChange L)) l
      = CoordinateRing.mk (W.baseChange L) (Polynomial.C (Polynomial.C l)) from rfl]
  rw [CoordinateRing.map_mk]
  rw [show algebraMap L' (CoordinateRing ((W.baseChange L).map f.toRingHom)) (f l)
      = CoordinateRing.mk ((W.baseChange L).map f.toRingHom) (Polynomial.C (Polynomial.C (f l)))
      from rfl]
  simp

/-- The ring homomorphism `CoordinateRing.map` induced by `f` fixes the coordinate `x`. -/
private lemma coordinateRing_map_mk_C_X :
    CoordinateRing.map (W.baseChange L) f.toRingHom
        (CoordinateRing.mk (W.baseChange L) (Polynomial.C Polynomial.X))
      = CoordinateRing.mk ((W.baseChange L).map f.toRingHom) (Polynomial.C Polynomial.X) := by
  rw [CoordinateRing.map_mk]
  simp

/-- The ring homomorphism `CoordinateRing.map` induced by `f` fixes the coordinate `y`. -/
private lemma coordinateRing_map_mk_Y :
    CoordinateRing.map (W.baseChange L) f.toRingHom
        (CoordinateRing.mk (W.baseChange L) Polynomial.X)
      = CoordinateRing.mk ((W.baseChange L).map f.toRingHom) Polynomial.X := by
  rw [CoordinateRing.map_mk]
  simp

end BaseChange

/-- **Base-change functoriality of the function field of a Weierstrass curve.**  An
`𝕜`-algebra homomorphism `f : L →ₐ[𝕜] L'` induces a `𝕜`-algebra homomorphism
`L(W) →ₐ[𝕜] L'(W)` of the function fields of the base-changed curves, sending `algebraMap L _ l` to
`algebraMap L' _ (f l)`, the generic point `x` to `x` and `y` to `y`; it is injective when `f` is.
Declare it in namespace `Work.MotT`.

Route.  `W.baseChange L = W.map (algebraMap 𝕜 L)`, and `f` composed with `algebraMap 𝕜 L` is
`algebraMap 𝕜 L'`, so the curves match.  On affine coordinate rings use
`WeierstrassCurve.Affine.CoordinateRing.map` (with `map_mk`, `map_X`, `map_injective`), and then
extend to the fraction fields with `IsFractionRing`/`IsLocalization.liftAlgHom` (the target is a
field).  The `x`/`y` values are `CoordinateRing.mk _ (C X)` and `CoordinateRing.mk _ Y`, on which
`map` acts by `Polynomial.map`, which fixes `C X` and `Y`. -/
theorem functionField_baseChange_map (𝕜 : Type) [Field 𝕜] (W : WeierstrassCurve 𝕜)
    (L L' : Type) [Field L] [Field L'] [Algebra 𝕜 L] [Algebra 𝕜 L'] (f : L →ₐ[𝕜] L') :
    ∃ φ : WeierstrassCurve.Affine.FunctionField (W.baseChange L) →ₐ[𝕜]
        WeierstrassCurve.Affine.FunctionField (W.baseChange L'),
      (∀ l : L, φ (algebraMap L _ l) = algebraMap L' _ (f l)) ∧
      φ (Work.MotV.genX (W.baseChange L)) = Work.MotV.genX (W.baseChange L') ∧
      φ (Work.MotV.genY (W.baseChange L)) = Work.MotV.genY (W.baseChange L') ∧
      (Function.Injective f → Function.Injective φ) := by
  -- The two base-changed curves agree, since `f` commutes with the structure maps of `𝕜`.
  have hcurve : (W.baseChange L).map f.toRingHom = W.baseChange L' := by
    show (W.map (algebraMap 𝕜 L)).map f.toRingHom = W.map (algebraMap 𝕜 L')
    rw [WeierstrassCurve.map_map]
    congr 1
    ext x
    exact f.commutes x
  -- Replace the target curve by `(W.baseChange L).map f.toRingHom`, so that the coordinate-ring
  -- compatibility lemmas apply without any rewriting of types.
  rw [← hcurve]
  have hmap_algMap : ∀ l : L,
      CoordinateRing.map (W.baseChange L) f.toRingHom
          (algebraMap L (CoordinateRing (W.baseChange L)) l)
        = algebraMap L' (CoordinateRing ((W.baseChange L).map f.toRingHom)) (f l) :=
    fun l => coordinateRing_map_algebraMap 𝕜 W L L' f l
  -- The induced map on coordinate rings, viewed as a `𝕜`-algebra homomorphism.
  let gA : CoordinateRing (W.baseChange L) →ₐ[𝕜]
      CoordinateRing ((W.baseChange L).map f.toRingHom) :=
    { CoordinateRing.map (W.baseChange L) f.toRingHom with
      commutes' := fun c => by
        change CoordinateRing.map (W.baseChange L) f.toRingHom
            (algebraMap L (CoordinateRing (W.baseChange L)) (algebraMap 𝕜 L c))
          = algebraMap 𝕜 (CoordinateRing ((W.baseChange L).map f.toRingHom)) c
        rw [hmap_algMap,
          IsScalarTower.algebraMap_apply 𝕜 L' (CoordinateRing ((W.baseChange L).map f.toRingHom)),
          f.commutes c] }
  -- Its composite with the structure map into the fraction field.
  let g : CoordinateRing (W.baseChange L) →ₐ[𝕜]
      FunctionField ((W.baseChange L).map f.toRingHom) :=
    (IsScalarTower.toAlgHom 𝕜 (CoordinateRing ((W.baseChange L).map f.toRingHom))
      (FunctionField ((W.baseChange L).map f.toRingHom))).comp gA
  have hgA : Function.Injective gA :=
    fun x y h => CoordinateRing.map_injective (f := f.toRingHom) f.injective h
  have hg : Function.Injective g := by
    rw [show ⇑g = ⇑(algebraMap (CoordinateRing ((W.baseChange L).map f.toRingHom))
      (FunctionField ((W.baseChange L).map f.toRingHom))) ∘ ⇑gA from rfl]
    exact (IsFractionRing.injective _ _).comp hgA
  refine ⟨IsFractionRing.liftAlgHom (R := 𝕜) hg, ?_, ?_, ?_, ?_⟩
  · -- The structure maps of the base fields are respected.
    intro l
    rw [IsScalarTower.algebraMap_apply L (CoordinateRing (W.baseChange L))
      (FunctionField (W.baseChange L))]
    rw [IsFractionRing.liftAlgHom_apply, IsFractionRing.lift_algebraMap]
    change g (algebraMap L (CoordinateRing (W.baseChange L)) l)
      = algebraMap L' (FunctionField ((W.baseChange L).map f.toRingHom)) (f l)
    rw [show g (algebraMap L (CoordinateRing (W.baseChange L)) l)
        = algebraMap (CoordinateRing ((W.baseChange L).map f.toRingHom))
            (FunctionField ((W.baseChange L).map f.toRingHom))
            (gA (algebraMap L (CoordinateRing (W.baseChange L)) l)) from rfl]
    rw [show gA (algebraMap L (CoordinateRing (W.baseChange L)) l)
        = algebraMap L' (CoordinateRing ((W.baseChange L).map f.toRingHom)) (f l)
        from hmap_algMap l]
    rw [← IsScalarTower.algebraMap_apply L' (CoordinateRing ((W.baseChange L).map f.toRingHom))
      (FunctionField ((W.baseChange L).map f.toRingHom)) (f l)]
  · -- The coordinate `x` is preserved.
    rw [Work.MotV.genX, Work.MotV.genX]
    rw [IsFractionRing.liftAlgHom_apply, IsFractionRing.lift_algebraMap]
    change g (CoordinateRing.mk (W.baseChange L) (Polynomial.C Polynomial.X))
      = algebraMap (CoordinateRing ((W.baseChange L).map f.toRingHom))
          (FunctionField ((W.baseChange L).map f.toRingHom))
          (CoordinateRing.mk ((W.baseChange L).map f.toRingHom) (Polynomial.C Polynomial.X))
    rw [show g (CoordinateRing.mk (W.baseChange L) (Polynomial.C Polynomial.X))
        = algebraMap (CoordinateRing ((W.baseChange L).map f.toRingHom))
            (FunctionField ((W.baseChange L).map f.toRingHom))
            (gA (CoordinateRing.mk (W.baseChange L) (Polynomial.C Polynomial.X))) from rfl]
    rw [show gA (CoordinateRing.mk (W.baseChange L) (Polynomial.C Polynomial.X))
        = CoordinateRing.mk ((W.baseChange L).map f.toRingHom) (Polynomial.C Polynomial.X) from by
      change CoordinateRing.map (W.baseChange L) f.toRingHom
        (CoordinateRing.mk (W.baseChange L) (Polynomial.C Polynomial.X)) = _
      rw [CoordinateRing.map_mk]; simp]
  · -- The coordinate `y` is preserved.
    rw [Work.MotV.genY, Work.MotV.genY]
    rw [IsFractionRing.liftAlgHom_apply, IsFractionRing.lift_algebraMap]
    change g (CoordinateRing.mk (W.baseChange L) Polynomial.X)
      = algebraMap (CoordinateRing ((W.baseChange L).map f.toRingHom))
          (FunctionField ((W.baseChange L).map f.toRingHom))
          (CoordinateRing.mk ((W.baseChange L).map f.toRingHom) Polynomial.X)
    rw [show g (CoordinateRing.mk (W.baseChange L) Polynomial.X)
        = algebraMap (CoordinateRing ((W.baseChange L).map f.toRingHom))
            (FunctionField ((W.baseChange L).map f.toRingHom))
            (gA (CoordinateRing.mk (W.baseChange L) Polynomial.X)) from rfl]
    rw [show gA (CoordinateRing.mk (W.baseChange L) Polynomial.X)
        = CoordinateRing.mk ((W.baseChange L).map f.toRingHom) Polynomial.X from by
      change CoordinateRing.map (W.baseChange L) f.toRingHom
        (CoordinateRing.mk (W.baseChange L) Polynomial.X) = _
      rw [CoordinateRing.map_mk]; simp]
  · -- A homomorphism of fields is injective.
    intro _
    exact RingHom.injective _

end Work.MotT
