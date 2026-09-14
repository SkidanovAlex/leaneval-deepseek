import Mathlib
import Submission.FundBody
import Submission.Cvp
import Submission.Transport
import Submission.CellTransport
import Submission.VoronoiMeasure

open Module Real MeasureTheory
open scoped Real BigOperators InnerProductSpace RealInnerProductSpace Pointwise
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

/-!
# Intrinsic (in-span) Voronoi-cell translate disjointness

The boundary case of `gamma_stable_of_two_le` needs the Voronoi cells of the *factor*
lattices of the ambient host `ℒ` to be "fundamental bodies in their own spans": no point
of the (subspace-)interior of the in-span cell lies in a translate by a nonzero lattice
point.  This module records:

* `voronoi_congr` — equal submodules have equal Voronoi cells;
* `voronoi_interior_disjoint_ambient` — for a discrete lattice `ℒ` in a standard space
  `EuclideanSpace ℝ (Fin n)`: `Disjoint (interior (voronoi ℒ)) ((y : E) +ᵥ voronoi ℒ)`
  for every nonzero `y : ℒ` (interior points satisfy the cell constraints strictly, so
  `x ∈ y + V` forces `‖x − y‖ ≤ ‖x‖` while interiority gives `‖x‖ < ‖x − y‖`);
* `translate_disjoint_congr` — the property is invariant under replacing the lattice by
  an equal submodule (same translate VALUES and equal Voronoi cells);
* `isometry_translate_disjoint` — a (linear) isometry carries such a translate-disjointness
  property between a lattice and its image (`CellTransport.latticeMap`);
* `inSpan_voronoi_interior_disjoint` — via the transported lattice `transLattice ℒ` in
  `EuclideanSpace ℝ (Fin (finrank ℤ ℒ))` and `Transport.realSpanIso ℒ`, the intrinsic
  disjointness of the in-span cell `voronoi (latticeInSpan ℒ)` inside `realSpan ℒ`;
* `inSpan_voronoi_disjoint_of_ambient_mem` — the same disjointness for translates by
  in-span vectors whose ambient value is a lattice point (the form needed when the
  quotient-lattice cell is translated by the projected component of a host point).
-/

namespace Submission.Intrinsic

noncomputable section

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "VC" => Submission.Voronoi.voronoi

/-- The Voronoi cell of equal submodules is the same set. -/
lemma voronoi_congr {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    (Λ₁ Λ₂ : Submodule ℤ Y) (h : Λ₁ = Λ₂) :
    VC (ℒ := Λ₁) = VC (ℒ := Λ₂) := by
  ext x
  rw [Submission.Voronoi.mem_voronoi, Submission.Voronoi.mem_voronoi]
  constructor
  · intro hx y₂
    have hy : (y₂ : Y) ∈ Λ₁ := by
      change (y₂ : Y) ∈ (Λ₁ : Set Y)
      rw [h]
      exact y₂.2
    simpa using (hx ⟨(y₂ : Y), hy⟩)
  · intro hx y₁
    have hy : (y₁ : Y) ∈ Λ₂ := by
      change (y₁ : Y) ∈ (Λ₂ : Set Y)
      rw [← h]
      exact y₁.2
    simpa using (hx ⟨(y₁ : Y), hy⟩)

/-- The (ambient) Voronoi cell of a discrete lattice: no point of its interior lies in a
translate by a nonzero lattice point. -/
theorem voronoi_interior_disjoint_ambient {ℒ : Submodule ℤ E} [DiscreteTopology ℒ] :
    ∀ y : ℒ, y ≠ 0 → Disjoint (interior (VC ℒ)) (((y : E) +ᵥ (VC ℒ))) := by
  intro y hy0
  rw [Set.disjoint_left]
  intro x hxInt hxTr
  have hxmem : x - (y : E) ∈ VC ℒ := (Submission.VoronoiMeasure.mem_cell_iff (ℒ := ℒ) y x).mp hxTr
  have hstrict : ⟪x, (y : E)⟫_ℝ < ‖(y : E)‖ ^ 2 / 2 := by
    exact (Submission.Cvp.mem_interior_voronoi_iff (ℒ := ℒ) x).mp hxInt y hy0
  have hnorm1 : ‖x - (y : E)‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    have hV := (Submission.VoronoiMeasure.mem_voronoi_iff_norm (ℒ := ℒ) (x - (y : E))).mp hxmem (-y)
    have hsim : (x - (y : E)) - (-(y : E)) = x := by abel
    simpa [hsim] using hV
  have hnorm2 : ‖x‖ ^ 2 < ‖x - (y : E)‖ ^ 2 := by
    have hsq : ‖x - (y : E)‖ ^ 2 = ‖x‖ ^ 2 + ‖(y : E)‖ ^ 2 - 2 * ⟪x, (y : E)⟫_ℝ := by
      rw [norm_sub_sq_real]
      ring
    rw [hsq]
    nlinarith
  exact (not_lt_of_ge hnorm1) hnorm2

/-- The translate-disjointness property only depends on the translate values and on the
Voronoi cell as a set, so replacing the lattice by an equal submodule is harmless. -/
lemma translate_disjoint_congr {Y : Type*} [NormedAddCommGroup Y]
    [InnerProductSpace ℝ Y] (Λ₁ Λ₂ : Submodule ℤ Y) (hΛ : Λ₁ = Λ₂)
    (h₁ : ∀ w : Λ₁, w ≠ 0 → Disjoint (interior (VC (ℒ := Λ₁))) (((w : Y) +ᵥ (VC (ℒ := Λ₁))))) :
    ∀ w : Λ₂, w ≠ 0 → Disjoint (interior (VC (ℒ := Λ₂))) (((w : Y) +ᵥ (VC (ℒ := Λ₂)))) := by
  intro w hw0
  have hwcar : (w : Y) ∈ Λ₁ := by
    change (w : Y) ∈ (Λ₁ : Set Y)
    rw [hΛ]
    exact w.2
  let w₁ : Λ₁ := ⟨(w : Y), hwcar⟩
  have hw₁0 : w₁ ≠ 0 := by
    intro hz
    apply hw0
    have hval : (w : Y) = 0 := congrArg (fun z : Λ₁ => (z : Y)) hz
    simpa using hval
  have h := h₁ w₁ hw₁0
  have hset : VC (ℒ := Λ₁) = VC (ℒ := Λ₂) := voronoi_congr Λ₁ Λ₂ hΛ
  have hval : (w₁ : Y) = (w : Y) := rfl
  rwa [hset, hval] at h

/-- Translate-disjointness transfers along a (linear) isometry from the image lattice back
to the source lattice. -/
lemma isometry_translate_disjoint {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    (e : X ≃ₗᵢ[ℝ] Y) (L : Submodule ℤ X)
    (h : ∀ w : Submission.CellTransport.latticeMap e L, w ≠ 0 → Disjoint
      (interior (VC (ℒ := (Submission.CellTransport.latticeMap e L))))
      (((w : Y) +ᵥ (VC (ℒ := (Submission.CellTransport.latticeMap e L)))))) :
    ∀ w : L, w ≠ 0 → Disjoint (interior (VC (ℒ := L))) (((w : X) +ᵥ (VC (ℒ := L)))) := by
  intro w hw0
  rw [Set.disjoint_left]
  intro x hxInt hxTr
  let W : Submodule ℤ Y := Submission.CellTransport.latticeMap e L
  have hxInt' : (e x) ∈ interior (VC (ℒ := W)) := by
    have himg : (e '' interior (VC (ℒ := L))) = interior ((e '' (VC (ℒ := L)))) := by
      exact (Homeomorph.image_interior (e.toHomeomorph) (VC (ℒ := L)))
    have hmem : e x ∈ e '' interior (VC (ℒ := L)) := ⟨x, hxInt, rfl⟩
    rw [himg] at hmem
    have heq : e '' (VC (ℒ := L)) = VC (ℒ := W) := (Submission.CellTransport.voronoi_map e L).symm
    rw [heq] at hmem
    exact hmem
  have hxTr' : e x ∈ ((e w : Y) +ᵥ (VC (ℒ := W))) := by
    rw [Set.mem_vadd_set]
    rcases (Set.mem_vadd_set.mp hxTr) with ⟨v, hv, hxwv⟩
    refine ⟨e v, ?_, ?_⟩
    · change e v ∈ VC (ℒ := (Submission.CellTransport.latticeMap e L))
      rw [Submission.CellTransport.voronoi_map e L]
      exact ⟨v, hv, rfl⟩
    · change (e (w : X) : Y) + (e v : Y) = e x
      rw [← e.map_add]
      exact congrArg (fun z : X => (e : X → Y) z) hxwv
  have hw' : (e w : Y) ∈ W := by
    rw [Submission.CellTransport.mem_latticeMap]
    exact ⟨w, w.2, rfl⟩
  let w' : W := ⟨(e w : Y), hw'⟩
  have hw'0 : w' ≠ 0 := by
    intro hz
    apply hw0
    apply Subtype.ext
    exact e.map_eq_zero_iff.mp (congrArg (fun z : W => (z : Y)) hz)
  exact (Set.disjoint_left.mp (h w' hw'0)) hxInt' hxTr'

/-- Intrinsic (in-span) translate disjointness of the Voronoi cell of a discrete lattice
inside its own real span: `voronoi (latticeInSpan ℒ)` (a set inside `realSpan ℒ`) has
interior disjoint from its translates by nonzero `latticeInSpan ℒ`-points. -/
theorem inSpan_voronoi_interior_disjoint {ℒ : Submodule ℤ E} [DiscreteTopology ℒ] :
    ∀ w : Submission.FundBody.latticeInSpan ℒ, w ≠ 0 → Disjoint
      (interior (VC (ℒ := (Submission.FundBody.latticeInSpan ℒ))))
      (((w : ↥(Submission.QuotientLattice.realSpan ℒ)) +ᵥ
        (VC (ℒ := (Submission.FundBody.latticeInSpan ℒ))))) := by
  classical
  let e : ↥(Submission.QuotientLattice.realSpan ℒ) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin (Module.finrank ℤ ℒ)) :=
    Submission.Transport.realSpanIso ℒ
  have h1 : ∀ w' : Submission.Transport.transLattice ℒ, w' ≠ 0 → Disjoint
      (interior (VC (ℒ := (Submission.Transport.transLattice ℒ))))
      (((w' : EuclideanSpace ℝ (Fin (Module.finrank ℤ ℒ))) +ᵥ
        (VC (ℒ := (Submission.Transport.transLattice ℒ))))) := by
    intro w' hw'0
    haveI : DiscreteTopology (Submission.Transport.transLattice ℒ) :=
      Submission.Transport.transLattice_discrete ℒ
    exact voronoi_interior_disjoint_ambient (n := Module.finrank ℤ ℒ)
      (ℒ := (Submission.Transport.transLattice ℒ)) w' hw'0
  have h1' : ∀ w : Submission.CellTransport.latticeMap e (Submission.FundBody.latticeInSpan ℒ),
      w ≠ 0 → Disjoint
      (interior (VC (ℒ := (Submission.CellTransport.latticeMap e
        (Submission.FundBody.latticeInSpan ℒ)))))
      (((w : EuclideanSpace ℝ (Fin (Module.finrank ℤ ℒ))) +ᵥ
        (VC (ℒ := (Submission.CellTransport.latticeMap e
          (Submission.FundBody.latticeInSpan ℒ)))))) := by
    have hΛ : Submission.Transport.transLattice ℒ =
        Submission.CellTransport.latticeMap e (Submission.FundBody.latticeInSpan ℒ) := by
      simpa [e] using (Submission.FundBody.transLattice_eq_latticeMap ℒ)
    exact translate_disjoint_congr (Λ₁ := (Submission.Transport.transLattice ℒ))
      (Λ₂ := (Submission.CellTransport.latticeMap e (Submission.FundBody.latticeInSpan ℒ))) hΛ h1
  exact isometry_translate_disjoint e (Submission.FundBody.latticeInSpan ℒ) h1'

/-- The translate-disjointness of the in-span cell against translates by lattice points
(given as in-span vectors whose ambient value is a lattice point).  This is the form used
when the quotient-lattice cell is translated by the projected component of a host-lattice
point. -/
theorem inSpan_voronoi_disjoint_of_ambient_mem {ℒ : Submodule ℤ E} [DiscreteTopology ℒ] :
    ∀ w : ↥(Submission.QuotientLattice.realSpan ℒ), w ≠ 0 → (w : E) ∈ ℒ → Disjoint
      (interior {v : ↥(Submission.QuotientLattice.realSpan ℒ) | (v : E) ∈ VC (ℒ := ℒ)})
      (((w : ↥(Submission.QuotientLattice.realSpan ℒ)) +ᵥ
        {v : ↥(Submission.QuotientLattice.realSpan ℒ) | (v : E) ∈ VC (ℒ := ℒ)})) := by
  classical
  intro w hw0 hwmem
  -- the in-span cell equals voronoi (latticeInSpan ℒ) as a set
  have hC : {v : ↥(Submission.QuotientLattice.realSpan ℒ) | (v : E) ∈ VC (ℒ := ℒ)} =
      VC (ℒ := (Submission.FundBody.latticeInSpan ℒ)) := by
    ext v
    constructor
    · intro hv
      exact (Submission.FundBody.mem_voronoi_inSpan_iff ℒ v).mpr hv
    · intro hv
      exact (Submission.FundBody.mem_voronoi_inSpan_iff ℒ v).mp hv
  let y : ℒ := ⟨(w : E), hwmem⟩
  have hin : Submission.FundBody.inSpanMap ℒ y = w := by
    simpa [Submission.FundBody.inSpanMap, y]
  let w' : Submission.FundBody.latticeInSpan ℒ :=
    ⟨Submission.FundBody.inSpanMap ℒ y,
      (Submission.FundBody.mem_latticeInSpan_iff ℒ (Submission.FundBody.inSpanMap ℒ y)).2 ⟨y, rfl⟩⟩
  have hw'0 : w' ≠ 0 := by
    intro hz
    apply hw0
    have hval : (w' : ↥(Submission.QuotientLattice.realSpan ℒ)) = 0 :=
      congrArg (fun z : Submission.FundBody.latticeInSpan ℒ =>
        (z : ↥(Submission.QuotientLattice.realSpan ℒ))) hz
    simpa [w', hin] using hval
  have h := inSpan_voronoi_interior_disjoint (ℒ := ℒ) w' hw'0
  dsimp [w'] at h
  rw [← hC] at h
  rw [hin] at h
  exact h

end

end Submission.Intrinsic
