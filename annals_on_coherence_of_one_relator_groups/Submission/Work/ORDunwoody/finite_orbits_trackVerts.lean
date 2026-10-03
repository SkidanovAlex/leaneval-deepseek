import Mathlib
import Submission.Work.ORDunwoody.Dunwoody.TrackGraph
import Submission.Work.ORDunwoody.finite_orbits_track

/-!
Copyright: work of the ORDunwoody subproject (node N13 of the
`annals_on_coherence_of_one_relator_groups` project).

# Cocompactness of the action of the stabiliser of a track on the track

`Dunwoody/TrackGraph.lean` defines, for a track `τ` of the Dunwoody pattern,

* `trackVerts τ` — the pattern points of `τ`, i.e. the vertices of the connected component `τ` of
  the chord graph on the pattern points `MidV D`;
* the action of `H = MulAction.stabilizer G τ` on `trackVerts τ`.

This file proves that this action is **cocompact**, i.e. that the orbit space is finite:

    Finite (MulAction.orbitRel.Quotient (MulAction.stabilizer G τ) (trackVerts τ))

Together with the freeness of the action (`trackVerts_smul_eq_self`) and the local finiteness of
`trackGraph τ` this is the hypothesis of `Work.WallSystem.fg_of_free_cocompact_graph` that makes
the stabiliser of a track finitely generated (node N13).

## The argument

The pattern points form the set `MidV D = G × MidIdx D` with `G` acting by left translation on the
first factor (`midV_smul`), and the projection to the tracks is `G`-equivariant (`trackOf_smul`).
Hence for a pattern point `m = (g, j)` of a track `τ` we have

    τ = trackOf m = g • trackOf (1, j),

so that *any* two pattern points of `τ` with the same index `j` differ by an element of
`H = MulAction.stabilizer G τ` (`same_orbit_of_snd_eq`, the key lemma below): if `m = (g, j)` and
`m' = (g', j)` then `τ = g • τ_j = g' • τ_j`, whence `g * g'⁻¹ ∈ H` and `(g * g'⁻¹) • m' = m`.

Consequently the orbit of a pattern point only depends on its index, and the (finite) index type
`MidIdx D = {j : Fin P.n, k : Fin (L (j,true))}` surjects onto the orbit space of `H` on
`trackVerts τ`.
-/

set_option autoImplicit false

universe u

namespace Work.ORDunwoody

open Work.ORDunwoody.Dunwoody

/-- **Two pattern points of a track with the same index lie in one orbit of the stabiliser of the
track.**  Writing the pattern points `m = (g, j)` and `m' = (g', j)` of the track `τ`
(`MidV D = G × MidIdx D`), equivariance of the projection to the tracks gives
`τ = trackOf m = g • trackOf (1, j)` and `τ = trackOf m' = g' • trackOf (1, j)`; hence
`g * g'⁻¹` fixes `τ`, i.e. it lies in `MulAction.stabilizer G τ`, and it moves `m'` to `m`. -/
theorem same_orbit_of_snd_eq {G : Type u} [Group G] {V : Type u} [MulAction G V] [DecidableEq V]
    {T : Work.ORDunwoody.GTree G V} {t₀ : V} {P : Work.ORDunwoody.FinPresentation G}
    {D : Work.ORDunwoody.Cayley.GeoData T t₀ P} {τ : Track D} {m m' : trackVerts τ}
    (h : (m : MidV D).2 = (m' : MidV D).2) :
    MulAction.orbitRel (MulAction.stabilizer G τ) (trackVerts τ) m m' := by
  -- Each pattern point is its first coordinate translated onto the base point of its index.
  have hm : (m : MidV D) = (m : MidV D).1 • (((1 : G), (m : MidV D).2) : MidV D) := by
    rw [midV_smul, mul_one]
  have hm' : (m' : MidV D) = (m' : MidV D).1 • (((1 : G), (m' : MidV D).2) : MidV D) := by
    rw [midV_smul, mul_one]
  -- The track of `m` and of `m'`, expressed through the base pattern point `(1, (m).2)`.
  have h1 : τ = (m : MidV D).1 • trackOf (((1 : G), (m : MidV D).2) : MidV D) := by
    calc τ = trackOf ((m : MidV D)) := m.2.symm
      _ = trackOf ((m : MidV D).1 • (((1 : G), (m : MidV D).2) : MidV D)) := congrArg trackOf hm
      _ = (m : MidV D).1 • trackOf (((1 : G), (m : MidV D).2) : MidV D) := by rw [trackOf_smul]
  have h2 : τ = (m' : MidV D).1 • trackOf (((1 : G), (m : MidV D).2) : MidV D) := by
    calc τ = trackOf ((m' : MidV D)) := m'.2.symm
      _ = trackOf ((m' : MidV D).1 • (((1 : G), (m' : MidV D).2) : MidV D)) :=
          congrArg trackOf hm'
      _ = (m' : MidV D).1 • trackOf (((1 : G), (m' : MidV D).2) : MidV D) := by rw [trackOf_smul]
      _ = (m' : MidV D).1 • trackOf (((1 : G), (m : MidV D).2) : MidV D) := by rw [h]
  -- `g * g'⁻¹` fixes the track, because `τ = g • τ_j = g' • τ_j`.
  have hmem : ((m : MidV D).1 * (m' : MidV D).1⁻¹) ∈ MulAction.stabilizer G τ := by
    rw [MulAction.mem_stabilizer_iff]
    calc ((m : MidV D).1 * (m' : MidV D).1⁻¹) • τ
        = ((m : MidV D).1 * (m' : MidV D).1⁻¹) •
            ((m' : MidV D).1 • trackOf (((1 : G), (m : MidV D).2) : MidV D)) :=
          congrArg (fun s => ((m : MidV D).1 * (m' : MidV D).1⁻¹) • s) h2
      _ = (((m : MidV D).1 * (m' : MidV D).1⁻¹) * (m' : MidV D).1) •
            trackOf (((1 : G), (m : MidV D).2) : MidV D) :=
          smul_smul ((m : MidV D).1 * (m' : MidV D).1⁻¹) (m' : MidV D).1
            (trackOf (((1 : G), (m : MidV D).2) : MidV D))
      _ = (m : MidV D).1 • trackOf (((1 : G), (m : MidV D).2) : MidV D) := by
          congr 1
          rw [mul_assoc, inv_mul_cancel, mul_one]
      _ = τ := h1.symm
  -- That element moves `m'` to `m`.
  rw [MulAction.orbitRel_apply]
  refine MulAction.mem_orbit_iff.mpr ⟨⟨(m : MidV D).1 * (m' : MidV D).1⁻¹, hmem⟩, ?_⟩
  refine Subtype.ext ?_
  show ((m : MidV D).1 * (m' : MidV D).1⁻¹) • (m' : MidV D) = (m : MidV D)
  rw [midV_smul]
  refine Prod.ext ?_ ?_
  · rw [mul_assoc, inv_mul_cancel, mul_one]
  · exact h.symm

/-- **The action of the stabiliser of a track on the pattern points of the track is cocompact.**
The orbit of a pattern point `(g, j)` of `τ` is determined by its index `j`
(`same_orbit_of_snd_eq`), so the finite index type `MidIdx D` (realised as
`Σ j : Fin P.n, Fin (L (j,true))`) surjects onto the orbit space. -/
theorem finite_orbits_trackVerts {G : Type u} [Group G] {V : Type u} [MulAction G V]
    [DecidableEq V]
    {T : Work.ORDunwoody.GTree G V} {t₀ : V} {P : Work.ORDunwoody.FinPresentation G}
    {D : Work.ORDunwoody.Cayley.GeoData T t₀ P} (τ : Work.ORDunwoody.Dunwoody.Track D) :
    Finite (MulAction.orbitRel.Quotient (MulAction.stabilizer G τ)
      (Work.ORDunwoody.trackVerts τ)) := by
  classical
  obtain ⟨m₀⟩ := trackVerts_nonempty τ
  -- Send an index to the orbit of some pattern point of the track with that index, if there is
  -- one; the choice is irrelevant by `same_orbit_of_snd_eq`.
  let φ : MidIdx D → MulAction.orbitRel.Quotient (MulAction.stabilizer G τ)
      (trackVerts τ) :=
    fun j => if h : ∃ m : trackVerts τ, (m : MidV D).2 = j then Quotient.mk _ h.choose
      else Quotient.mk _ m₀
  refine Finite.of_surjective
    (fun x : Σ j : Fin P.n, Fin (D.L (j, true)) => φ ⟨x.1, x.2⟩) ?_
  intro q
  refine Quotient.inductionOn q (fun m => ?_)
  refine ⟨⟨(m : MidV D).2.j, (m : MidV D).2.k⟩, ?_⟩
  show φ ⟨(m : MidV D).2.j, (m : MidV D).2.k⟩ = Quotient.mk _ m
  have hex : ∃ m' : trackVerts τ,
      (m' : MidV D).2 = (⟨(m : MidV D).2.j, (m : MidV D).2.k⟩ : MidIdx D) := ⟨m, rfl⟩
  rw [show φ ⟨(m : MidV D).2.j, (m : MidV D).2.k⟩ =
      Quotient.mk _ (Classical.choose hex) from dif_pos hex]
  exact Quotient.sound (same_orbit_of_snd_eq (Classical.choose_spec hex))

end Work.ORDunwoody
