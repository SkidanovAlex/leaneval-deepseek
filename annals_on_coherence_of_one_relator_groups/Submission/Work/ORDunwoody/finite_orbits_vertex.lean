import Mathlib
import Submission.Work.ORDunwoody.Dunwoody.Source

/-!
# Finiteness of the vertex orbits of `Λ''` (node N13 of the ORDunwoody subproject)

The vertices of the subdivided Cayley complex `Λ''` of the Dunwoody construction are

* the *old* vertices `BaseV D = G × BaseV₀ D`, where `BaseV₀ D = Unit ⊕ Σ j, Fin (L (j,true) - 1)`
  consists of the base point together with the interior points of the generator edges, and
* the *pattern points* `MidV D = G × MidIdx D`, where
  `MidIdx D = {j : Fin P.n, k : Fin (L (j,true))}` indexes the cells of `Λ'`.

In both cases the group acts by left multiplication on the first factor, so the orbit of `(g, x)`
is exactly the fibre over `x`: the orbit quotient is a quotient of the *finite* type
`BaseV₀ D ⊕ MidIdx D` (which already classifies the orbits).  Hence the orbit quotient is finite,
i.e. the action of `G` on the vertices of `Λ''` is cocompact.
-/

set_option autoImplicit false

universe u

namespace Work.ORDunwoody

open Work.ORDunwoody.Dunwoody

/-- The orbits of vertices of `Λ''`.  The action of `G` on `Vertex D` is by left multiplication on
the first factor, so the orbit of a vertex is determined by its second coordinate; accordingly the
orbit quotient is a quotient of the finite type
`BaseV₀ D ⊕ (Σ j : Fin P.n, Fin (D.L (j, true)))`, which is the type `BaseV₀ D ⊕ MidIdx D`
together with its definitional `Fintype` structure. -/
theorem finite_orbits_vertex {G : Type u} [Group G] {V : Type u} [MulAction G V] {T : Work.ORDunwoody.GTree G V} {t₀ : V} {P : Work.ORDunwoody.FinPresentation G} {D : Work.ORDunwoody.Cayley.GeoData T t₀ P} : Finite (MulAction.orbitRel.Quotient G (Work.ORDunwoody.Dunwoody.Vertex D)) := by
  -- The finite type that classifies the orbits: the "old" coordinates `BaseV₀ D` (the base point
  -- and the interior points of the generator edges) together with the cell indices `MidIdx D`.
  refine Finite.of_surjective
    (fun v : BaseV₀ D ⊕ (Σ j : Fin P.n, Fin (D.L (j, true))) =>
      (Quotient.mk (MulAction.orbitRel G (Vertex D))
        (Sum.map (fun x : BaseV₀ D => ((1 : G), x))
          (fun m : Σ j : Fin P.n, Fin (D.L (j, true)) =>
            ((1 : G), (⟨m.1, m.2⟩ : MidIdx D))) v) :
        MulAction.orbitRel.Quotient G (Vertex D))) ?_
  intro q
  refine Quotient.inductionOn q (fun p => ?_)
  cases p with
  | inl p =>
      -- An old vertex `(g, x)` lies in the orbit of `(1, x)`.
      refine ⟨Sum.inl p.2, ?_⟩
      apply Quotient.sound
      show (MulAction.orbitRel G (Vertex D)) (Sum.inl ((1 : G), p.2)) (Sum.inl p)
      rw [MulAction.orbitRel_apply]
      refine MulAction.mem_orbit_iff.mpr ⟨p.1⁻¹, ?_⟩
      rw [vertex_smul_inl, baseV_smul]
      simp
  | inr p =>
      -- A pattern point `(g, m)` lies in the orbit of `(1, m)`.
      refine ⟨Sum.inr ⟨p.2.j, p.2.k⟩, ?_⟩
      apply Quotient.sound
      show (MulAction.orbitRel G (Vertex D))
        (Sum.inr ((1 : G), (⟨p.2.j, p.2.k⟩ : MidIdx D))) (Sum.inr p)
      rw [MulAction.orbitRel_apply]
      refine MulAction.mem_orbit_iff.mpr ⟨p.1⁻¹, ?_⟩
      rw [vertex_smul_inr, midV_smul]
      simp

end Work.ORDunwoody
