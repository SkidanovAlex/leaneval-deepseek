/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Homology of complexes commutes with additive functors which preserve homology.
-/
import Mathlib

set_option autoImplicit false

open CategoryTheory Limits

namespace Work.ORHomAlg.Bridge

/-- The homology of a homological complex commutes with an additive functor which preserves
homology: the homology in degree `n` of `F` applied to a complex `K` is `F` applied to the
homology of `K` in degree `n`. -/
theorem homology_mapHomologicalComplex {C D : Type*} [Category* C] [Category* D]
    [Abelian C] [Abelian D] {ι : Type*} {c : ComplexShape ι}
    (F : C ⥤ D) [F.Additive] [F.PreservesHomology]
    (K : HomologicalComplex C c) (n : ι) :
    Nonempty (F.obj (K.homology n) ≅ ((F.mapHomologicalComplex c).obj K).homology n) :=
  ⟨(ShortComplex.mapHomologyIso (K.sc n) F).symm⟩

end Work.ORHomAlg.Bridge
