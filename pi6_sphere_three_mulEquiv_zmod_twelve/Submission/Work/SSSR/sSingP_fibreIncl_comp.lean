import Mathlib
import Submission.Work.SSSR.serreE1Defs
import Submission.Work.SSSR.StemsB.Fibrations
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

namespace Work.SSSR

open CategoryTheory Simplicial Opposite
/-- The composite of the simplicial maps induced by the inclusion of the fibre of `p` over `b` and
by `p` itself is the constant simplicial map at the `0`-simplex `b`.  Equivalently,
`Sing(fibreIncl p b) ≫ Sing p = const (b)`, which encodes `p ∘ i = const b` on the level of
singular simplicial sets. -/
theorem sSingP_fibreIncl_comp {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (b : B) :
    CategoryTheory.CategoryStruct.comp (Work.SSSR.sSingP (Work.SSSR.StemsB.fibreIncl p b))
      (Work.SSSR.sSingP p) = SSet.const (TopCat.toSSetObj₀Equiv.symm b) := by
  -- `sSingP` is `TopCat.toSSet.map`, hence it is functorial; the composite of the two induced maps
  -- is the map induced by the composite continuous map `p.comp (fibreIncl p b)`, which is the
  -- constant map at `b` because `p` restricted to the fibre over `b` is constantly `b`.
  have h : (TopCat.ofHom (Work.SSSR.StemsB.fibreIncl p b) ≫ TopCat.ofHom p :
      TopCat.of (Work.SSSR.StemsB.fibre p b) ⟶ TopCat.of B) = TopCat.const b := by
    ext x
    rw [TopCat.const_apply]
    exact x.2
  simp only [Work.SSSR.sSingP]
  rw [← Functor.map_comp, h, TopCat.toSSet_map_const]

end Work.SSSR
