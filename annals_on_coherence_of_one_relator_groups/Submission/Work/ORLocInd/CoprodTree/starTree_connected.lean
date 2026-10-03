import Mathlib
import Submission.Work.ORLocInd.CoprodTree.StarTreeDefs

set_option autoImplicit false

universe u

namespace Work.ORLocInd.CoprodTree

open Quiver
open Work.ORBassSerre

section

variable {ι : Type u} {M : ι → Type u} [∀ i, Group (M i)]

/-! ## Elementary arrows of the star tree

The star tree has central vertices `vtx none g` and coset vertices `vtx (some i) g`.  The
elementary moves are:

* `arrowOut i g`  : `vtx none g ⟶ vtx (some i) g`
* `arrowBack i g` : `vtx (some i) g ⟶ vtx none g`
* `arrowMul i m g`: `vtx (some i) g ⟶ vtx none (g * of m)`

The last one is the key step: it multiplies the label of a central vertex on the *right* by an
element of a factor.  -/

/-- The arrow going from a central vertex to the coset vertex with the same label. -/
def arrowOut (i : ι) (g : Monoid.CoprodI M) :
    vtx (none : Option ι) g ⟶ vtx (some i) g :=
  ⟨(i, g), Or.inl ⟨rfl, rfl⟩⟩

/-- The arrow going from a coset vertex back to the central vertex with the same label. -/
def arrowBack (i : ι) (g : Monoid.CoprodI M) :
    vtx (some i) g ⟶ vtx (none : Option ι) g :=
  ⟨(i, g), Or.inr ⟨rfl, rfl⟩⟩

/-- The second half of the move multiplying the label of a central vertex on the right by an
element of a factor: this arrow goes from the coset vertex `vtx (some i) g` to the central
vertex `vtx none (g * of m)`, which is the same coset. -/
def arrowMul (i : ι) (m : M i) (g : Monoid.CoprodI M) :
    vtx (some i) g ⟶ vtx (none : Option ι) (g * Monoid.CoprodI.of m) :=
  ⟨(i, g * Monoid.CoprodI.of m), Or.inr ⟨by
    rw [vtx_some_eq_vtx_some, ← mul_assoc, inv_mul_cancel, one_mul]
    exact mem_factor.mpr ⟨m, rfl⟩, rfl⟩⟩

/-- **The right-multiplication move.**  There is a path from the central vertex `vtx none g` to
the central vertex `vtx none (g * of m)`. -/
theorem path_mul_of (i : ι) (m : M i) (g : Monoid.CoprodI M) :
    Nonempty (Quiver.Path (vtx (none : Option ι) g) (vtx none (g * Monoid.CoprodI.of m))) :=
  ⟨((Quiver.Path.nil : Quiver.Path (vtx (none : Option ι) g) (vtx none g)).cons
      (arrowOut i g)).cons (arrowMul i m g)⟩

/-! ## Reduction to paths between central vertices -/

/-- Induction principle for the free product in which the generator is multiplied on the
**right** (deduced from `Monoid.CoprodI.induction_left` applied to the inverse). -/
theorem induction_right {motive : Monoid.CoprodI M → Prop} (one : motive 1)
    (mul : ∀ {i : ι} (m : M i) (x : Monoid.CoprodI M),
      motive x → motive (x * Monoid.CoprodI.of m))
    (g : Monoid.CoprodI M) : motive g := by
  have key : motive (g⁻¹)⁻¹ :=
    Monoid.CoprodI.induction_left (motive := fun x => motive x⁻¹) g⁻¹
      (by simpa using one)
      (fun {i} mm x hx => by
        have hgoal : (Monoid.CoprodI.of mm * x)⁻¹ = x⁻¹ * Monoid.CoprodI.of (mm⁻¹) := by
          rw [mul_inv_rev, map_inv]
        rw [hgoal]
        exact mul (m := mm⁻¹) x⁻¹ hx)
  simpa using key

/-- There is a path from the central vertex of the identity to any central vertex. -/
theorem root_path (g : Monoid.CoprodI M) :
    Nonempty (Quiver.Path (vtx (none : Option ι) 1) (vtx none g)) := by
  refine induction_right (M := M)
    (motive := fun g => Nonempty (Quiver.Path (vtx (none : Option ι) 1) (vtx none g)))
    ⟨Quiver.Path.nil⟩ ?_ g
  intro i m x ih
  obtain ⟨p⟩ := ih
  exact ⟨p.comp (path_mul_of i m x).some⟩

/-- Any two central vertices are joined by a path. -/
theorem conn_none (g h : Monoid.CoprodI M) :
    Nonempty (Quiver.Path (vtx (none : Option ι) g) (vtx none h)) := by
  obtain ⟨p⟩ := root_path (M := M) (g⁻¹ * h)
  refine ⟨(smulPath g p).cast ?_ ?_⟩
  · rw [smul_vtx_none, mul_one]
  · rw [smul_vtx_none, ← mul_assoc, mul_inv_cancel, one_mul]

/-- A path from a central vertex to a coset vertex. -/
theorem conn_to_coset (i : ι) (g h : Monoid.CoprodI M) :
    Nonempty (Quiver.Path (vtx (none : Option ι) g) (vtx (some i) h)) :=
  ⟨(conn_none g h).some.comp (arrowOut i h).toPath⟩

/-- A path from a coset vertex to a central vertex. -/
theorem conn_from_coset (i : ι) (g h : Monoid.CoprodI M) :
    Nonempty (Quiver.Path (vtx (some i) g) (vtx (none : Option ι) h)) :=
  ⟨((Quiver.Path.nil : Quiver.Path (vtx (some i) g) (vtx (some i) g)).cons
      (arrowBack i g)).comp (conn_none g h).some⟩

/-- A path between two coset vertices. -/
theorem conn_coset_coset (i j : ι) (g h : Monoid.CoprodI M) :
    Nonempty (Quiver.Path (vtx (some i) g) (vtx (some j) h)) :=
  ⟨(((Quiver.Path.nil : Quiver.Path (vtx (some i) g) (vtx (some i) g)).cons
      (arrowBack i g)).comp (conn_none g h).some).comp (arrowOut j h).toPath⟩

end

theorem starTree_connected {ι : Type u} {M : ι → Type u} [∀ i, Group (M i)]
    (x y : Work.ORLocInd.CoprodTree.Vertex M) : Nonempty (Quiver.Path x y) := by
  obtain ⟨kx, gx, rfl⟩ := exists_vtx x
  obtain ⟨ky, gy, rfl⟩ := exists_vtx y
  rcases kx with _ | i
  · rcases ky with _ | j
    · exact conn_none gx gy
    · exact conn_to_coset j gx gy
  · rcases ky with _ | j
    · exact conn_from_coset i gx gy
    · exact conn_coset_coset i j gx gy

end Work.ORLocInd.CoprodTree
