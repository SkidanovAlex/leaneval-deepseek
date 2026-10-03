import Mathlib
import Submission.Work.ORDunwoody.Dunwoody.Source
import Submission.Work.ORDunwoody.finite_orbits_vertex

namespace Work.ORDunwoody

universe u

/-- **Finiteness of the orbits of the old vertices of `Λ''`.**  `BaseV D = G × BaseV₀ D` and `G`
acts by left multiplication on the first factor (`Dunwoody.instMulActionBaseV`), so every orbit
contains a vertex `(1, x)` with `x : BaseV₀ D`; since `BaseV₀ D` is finite the orbit quotient is
finite (it can also be obtained from `Work.ORDunwoody.finite_orbits_vertex` along the equivariant
injection `BaseV D → Vertex D`, `Sum.inl`). -/
theorem finite_orbits_baseV {G : Type u} [Group G] {V : Type u} [MulAction G V] [DecidableEq V]
    {T : Work.ORDunwoody.GTree G V} {t₀ : V} {P : Work.ORDunwoody.FinPresentation G}
    {D : Work.ORDunwoody.Cayley.GeoData T t₀ P} :
    Finite (MulAction.orbitRel.Quotient G (Work.ORDunwoody.Dunwoody.BaseV D)) := by
  -- Every orbit of an old vertex `(g, x)` contains the vertex `(1, x)` with `x : BaseV₀ D`,
  -- so the orbit quotient is a quotient of the finite type `BaseV₀ D`.
  refine Finite.of_surjective
    (fun x : Work.ORDunwoody.Dunwoody.BaseV₀ D =>
      (Quotient.mk (MulAction.orbitRel G (Work.ORDunwoody.Dunwoody.BaseV D))
        ((1 : G), x) :
        MulAction.orbitRel.Quotient G (Work.ORDunwoody.Dunwoody.BaseV D))) ?_
  intro q
  refine Quotient.inductionOn q (fun p => ?_)
  refine ⟨p.2, ?_⟩
  apply Quotient.sound
  show (MulAction.orbitRel G (Work.ORDunwoody.Dunwoody.BaseV D)) ((1 : G), p.2) p
  rw [MulAction.orbitRel_apply]
  refine MulAction.mem_orbit_iff.mpr ⟨p.1⁻¹, ?_⟩
  rw [Work.ORDunwoody.Dunwoody.baseV_smul]
  simp

end Work.ORDunwoody
