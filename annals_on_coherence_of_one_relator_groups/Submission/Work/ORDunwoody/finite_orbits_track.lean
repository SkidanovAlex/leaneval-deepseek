import Mathlib
import Submission.Work.ORDunwoody.Dunwoody.TrackWall
import Submission.Work.ORDunwoody.finite_orbits_vertex

/-!
# Finiteness of the orbits of the tracks of the Dunwoody pattern (node N13 of the ORDunwoody
subproject)

The tracks are the connected components of the chord graph on the pattern points `MidV D`:

    Track D = (chordGraph D).ConnectedComponent,   trackOf : MidV D → Track D.

Since `MidV D = G × MidIdx D` and the action of `G` on `MidV D` is by left translation on the
first factor (`Dunwoody/Source.lean`), the orbit quotient of `MidV D` is a quotient of the
*finite* index type `MidIdx D`.  The canonical projection `trackOf` is `G`-equivariant
(`trackOf_smul`), so it descends to a surjection of orbit quotients; hence the orbit quotient of
the tracks is finite as well, i.e. the action of `G` on the tracks is cocompact.

The two steps are isolated below:

* `finite_orbits_midV` — the orbit quotient of the pattern points is finite;
* `finite_orbits_of_surjective` — finiteness of the orbit quotient descends along a surjective
  equivariant map.
-/

set_option autoImplicit false

universe u

namespace Work.ORDunwoody

open Work.ORDunwoody.Dunwoody

/-- **Finiteness of the orbit quotient descends along a surjective equivariant map.**  If `G`
acts on `X` and `Y`, if the orbit quotient of `X` is finite and if `f : X → Y` is surjective and
`G`-equivariant, then the orbit quotient of `Y` is finite: `f` descends to a surjection of the
orbit quotients. -/
theorem finite_orbits_of_surjective {G : Type u} [Group G] {X Y : Type u} [MulAction G X]
    [MulAction G Y] (hX : Finite (MulAction.orbitRel.Quotient G X)) (f : X → Y)
    (hf : Function.Surjective f) (heq : ∀ (g : G) (x : X), f (g • x) = g • f x) :
    Finite (MulAction.orbitRel.Quotient G Y) := by
  classical
  -- The relation is preserved: two elements of one orbit of `X` map into one orbit of `Y`.
  have hmap : ∀ a b : X, (MulAction.orbitRel G X) a b →
      (MulAction.orbitRel G Y) (f a) (f b) := by
    intro a b hab
    rw [MulAction.orbitRel_apply] at hab ⊢
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hab
    exact MulAction.mem_orbit_iff.mpr ⟨g, by rw [← heq g b, hg]⟩
  refine Finite.of_surjective (α := MulAction.orbitRel.Quotient G X)
    (Quotient.map (sa := MulAction.orbitRel G X) (sb := MulAction.orbitRel G Y) f hmap) ?_
  intro q
  refine Quotient.inductionOn q (fun y => ?_)
  obtain ⟨x, rfl⟩ := hf y
  exact ⟨Quotient.mk _ x, rfl⟩

/-- **The orbits of the pattern points.**  The action of `G` on `MidV D = G × MidIdx D` is by
left translation on the first factor, so `(g, m)` lies in the orbit of `(1, m)`; hence the orbit
quotient is a quotient of the finite index type
`Σ j : Fin P.n, Fin (D.L (j, true))`, which is the underlying type of `MidIdx D`. -/
theorem finite_orbits_midV {G : Type u} [Group G] {V : Type u} [MulAction G V] [DecidableEq V]
    {T : Work.ORDunwoody.GTree G V} {t₀ : V} {P : Work.ORDunwoody.FinPresentation G}
    {D : Work.ORDunwoody.Cayley.GeoData T t₀ P} :
    Finite (MulAction.orbitRel.Quotient G (Work.ORDunwoody.Dunwoody.MidV D)) := by
  classical
  refine Finite.of_surjective
    (fun x : Σ j : Fin P.n, Fin (D.L (j, true)) =>
      (Quotient.mk (MulAction.orbitRel G (Work.ORDunwoody.Dunwoody.MidV D))
        ((1 : G), (⟨x.1, x.2⟩ : Work.ORDunwoody.Dunwoody.MidIdx D)) :
        MulAction.orbitRel.Quotient G (Work.ORDunwoody.Dunwoody.MidV D))) ?_
  intro q
  refine Quotient.inductionOn q (fun p => ?_)
  refine ⟨⟨p.2.j, p.2.k⟩, ?_⟩
  apply Quotient.sound
  show (MulAction.orbitRel G (Work.ORDunwoody.Dunwoody.MidV D))
    ((1 : G), (⟨p.2.j, p.2.k⟩ : Work.ORDunwoody.Dunwoody.MidIdx D)) p
  rw [MulAction.orbitRel_apply]
  refine MulAction.mem_orbit_iff.mpr ⟨p.1⁻¹, ?_⟩
  rw [Work.ORDunwoody.Dunwoody.midV_smul]
  simp

/-- **The orbits of the tracks of the Dunwoody pattern are finite.**  The tracks are the connected
components of the chord graph on the pattern points, so `trackOf : MidV D → Track D` is
surjective, and it is `G`-equivariant (`trackOf_smul`).  Finiteness of the orbit quotient of the
pattern points (`finite_orbits_midV`) therefore descends to the tracks
(`finite_orbits_of_surjective`). -/
theorem finite_orbits_track {G : Type u} [Group G] {V : Type u} [MulAction G V] [DecidableEq V]
    {T : Work.ORDunwoody.GTree G V} {t₀ : V} {P : Work.ORDunwoody.FinPresentation G}
    {D : Work.ORDunwoody.Cayley.GeoData T t₀ P} :
    Finite (MulAction.orbitRel.Quotient G (Work.ORDunwoody.Dunwoody.Track D)) := by
  classical
  refine finite_orbits_of_surjective (X := MidV D) (Y := Track D)
    (finite_orbits_midV (D := D)) (fun m : MidV D => trackOf m) ?_ ?_
  · -- Every track contains a pattern point.
    intro τ
    exact Quotient.mk_surjective
      (s := SimpleGraph.reachableSetoid (Work.ORDunwoody.Dunwoody.chordGraph D)) τ
  · -- The projection to the tracks is equivariant.
    intro g m
    exact Work.ORDunwoody.Dunwoody.trackOf_smul g m

end Work.ORDunwoody
