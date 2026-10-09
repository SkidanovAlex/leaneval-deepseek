import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.GlobalCFT.Galois

/-- The map `K_v → L_w` induced by `algebraMap K L` (when `w` lies over `v`) is an isometry.

This is because `completionMap` is the composite of the isometry
`WithAbs v.1 → WithAbs w.1` (the algebra map `K → L`, which is norm preserving), the
`Completion.equiv` transferring between `v.Completion` and the underlying uniform completion of
`WithAbs v.1` on the source side, and the inverse of the corresponding equivalence on the target
side.  Each of the three is an isometry. -/
theorem completionMap_isometry {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] {v : NumberField.InfinitePlace K} {w : NumberField.InfinitePlace L} [w.LiesOver v] :
    Isometry (NumberField.LiesOver.completionMap (v := v) (w := w)) := by
  have hC : Isometry ⇑(NumberField.InfinitePlace.Completion.equiv v).toRingHom :=
    NumberField.InfinitePlace.Completion.isometry_toCompletion v
  have hB : Isometry ⇑((NumberField.InfinitePlace.LiesOver.isometry_algebraMap w v).mapRingHom) :=
    Isometry.isometry_mapRingHom _
  have hA : Isometry ⇑(NumberField.InfinitePlace.Completion.equiv w).symm.toRingHom :=
    (NumberField.InfinitePlace.Completion.isometryEquivCompletion w).symm.isometry_toFun
  rw [NumberField.LiesOver.completionMap]
  simp only [RingHom.coe_comp]
  exact hA.comp (hB.comp hC)

end NK.GlobalCFT.Galois
