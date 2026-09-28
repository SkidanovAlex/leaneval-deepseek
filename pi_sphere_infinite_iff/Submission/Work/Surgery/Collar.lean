import Submission.Work.Surgery.Boundary

/-!
# Collars of manifolds with boundary

For a smooth manifold `M` with boundary, modelled on the half-space `EuclideanHalfSpace (n+1)`, a
**collar** of `M` is an open embedding of `∂M × [0,∞)` into `M` whose restriction to `∂M × {0}` is
the inclusion of the boundary:

`c : ∂M × [0,∞) ↪ M`,  `c x 0 = x`.

Its image is an open neighbourhood of `∂M` in `M` (`Collar.isOpen_range`, and
`Collar.range_mem_nhds`), which is what makes it possible to *glue* two manifolds with boundary
along a diffeomorphism of their boundaries (`Gluing.lean`), and to describe attaching maps of
handles (`Handle.lean`).

The **collar neighbourhood theorem** — every smooth manifold with boundary admits a collar — is
not in Mathlib and is not proved here; it is isolated as the named proposition

`Work.Surgery.HasCollar n M : Prop := Nonempty (Collar n M)`

so that every statement depending on it records the input once.  The theorem is *proved* for
manifolds with empty boundary (`hasCollar_of_boundary_eq_empty`), where the empty map is a collar.

## Main definitions

* `Work.Surgery.Collar n M` — collars of `M` (an open embedding `∂M × ℝ≥0 ↪ M`);
* `Work.Surgery.Collar.range`, `Collar.isOpen_range`, `Collar.mem_range`,
  `Collar.range_mem_nhds`, `Collar.toHomeomorph` — the collar is a homeomorphism onto an open
  neighbourhood of the boundary;
* `Work.Surgery.HasCollar n M` — the collar neighbourhood theorem as a hypothesis, with
  `hasCollar_of_boundary_eq_empty`;
* `Work.Surgery.Collar.restr` — the collar restricted to `∂M × [0,ε]`.
-/

open scoped Manifold Topology ContDiff
open Function

namespace Work.Surgery

noncomputable section

variable {n : ℕ}

/-- The half-line `[0,∞)` of collar parameters. -/
abbrev HalfLine : Type := {t : ℝ // 0 ≤ t}

/-- **A collar of a manifold with boundary**: an open embedding `∂M × [0,∞) ↪ M` whose
restriction to `∂M × {0}` is the inclusion of the boundary. -/
structure Collar (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] where
  /-- the collar map -/
  toFun : (𝓡∂ (n + 1)).boundary M × HalfLine → M
  /-- the collar map is an open embedding -/
  isOpenEmbedding : Topology.IsOpenEmbedding toFun
  /-- the collar map is the identity on `∂M × {0}` -/
  toFun_zero : ∀ x : (𝓡∂ (n + 1)).boundary M, toFun (x, ⟨0, le_refl 0⟩) = x.1

namespace Collar

variable {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M]

/-- The **image of the collar**: an open neighbourhood of the boundary. -/
def range (c : Collar n M) : Set M := Set.range c.toFun

theorem continuous_toFun (c : Collar n M) : Continuous c.toFun :=
  c.isOpenEmbedding.continuous

theorem injective_toFun (c : Collar n M) : Injective c.toFun :=
  c.isOpenEmbedding.toIsEmbedding.injective

theorem isOpen_range (c : Collar n M) : IsOpen c.range :=
  c.isOpenEmbedding.isOpen_range

/-- The boundary is contained in the collar's image. -/
theorem mem_range (c : Collar n M) (x : (𝓡∂ (n + 1)).boundary M) : x.1 ∈ c.range :=
  ⟨(x, ⟨0, le_refl 0⟩), c.toFun_zero x⟩

/-- The collar's image is a neighbourhood of each boundary point. -/
theorem range_mem_nhds (c : Collar n M) (x : (𝓡∂ (n + 1)).boundary M) : c.range ∈ 𝓝 x.1 :=
  c.isOpen_range.mem_nhds (c.mem_range x)

/-- The collar map as a homeomorphism onto its range. -/
def toHomeomorph (c : Collar n M) :
    ((𝓡∂ (n + 1)).boundary M × HalfLine) ≃ₜ c.range :=
  c.isOpenEmbedding.toIsEmbedding.toHomeomorph

theorem toHomeomorph_apply (c : Collar n M) (p : (𝓡∂ (n + 1)).boundary M × HalfLine) :
    (c.toHomeomorph p : M) = c.toFun p := rfl

/-- The inverse of the collar, as a map from its range. -/
def invFun (c : Collar n M) (y : c.range) : (𝓡∂ (n + 1)).boundary M × HalfLine :=
  c.toHomeomorph.symm y

theorem toFun_invFun (c : Collar n M) (y : c.range) : c.toFun (c.invFun y) = y.1 :=
  congrArg Subtype.val (c.toHomeomorph.apply_symm_apply y)

theorem invFun_toFun (c : Collar n M) (p : (𝓡∂ (n + 1)).boundary M × HalfLine) :
    c.invFun ⟨c.toFun p, ⟨p, rfl⟩⟩ = p := by
  change c.toHomeomorph.symm (c.toHomeomorph p) = p
  exact c.toHomeomorph.symm_apply_apply p

/-- The first component of the inverse of the collar: the boundary point underlying a point of the
collar's image.  This is the retraction of the collar onto the boundary. -/
def retract (c : Collar n M) (y : c.range) : (𝓡∂ (n + 1)).boundary M := (c.invFun y).1

/-- The second component of the inverse of the collar: the collar coordinate. -/
def coord (c : Collar n M) (y : c.range) : HalfLine := (c.invFun y).2

theorem toFun_invFun_eq (c : Collar n M) (y : c.range) :
    c.toFun ((c.invFun y).1, (c.invFun y).2) = y.1 := c.toFun_invFun y

@[simp] theorem retract_toFun (c : Collar n M)
    (p : (𝓡∂ (n + 1)).boundary M × HalfLine) :
    c.retract ⟨c.toFun p, ⟨p, rfl⟩⟩ = p.1 := by
  rw [retract, c.invFun_toFun p]

@[simp] theorem coord_toFun (c : Collar n M) (p : (𝓡∂ (n + 1)).boundary M × HalfLine) :
    c.coord ⟨c.toFun p, ⟨p, rfl⟩⟩ = p.2 := by
  rw [coord, c.invFun_toFun p]

@[simp] theorem coord_boundary (c : Collar n M) (x : (𝓡∂ (n + 1)).boundary M) :
    c.coord ⟨x.1, c.mem_range x⟩ = ⟨0, le_refl 0⟩ := by
  have h : (⟨x.1, c.mem_range x⟩ : c.range)
      = ⟨c.toFun (x, ⟨0, le_refl 0⟩), ⟨(x, ⟨0, le_refl 0⟩), rfl⟩⟩ :=
    Subtype.ext (c.toFun_zero x).symm
  rw [h, c.coord_toFun]

end Collar

/-- **The collar neighbourhood theorem**, as a named hypothesis: every smooth manifold with
boundary admits a collar.  Proved in this library only for manifolds with empty boundary
(`hasCollar_of_boundary_eq_empty`). -/
def HasCollar (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] : Prop := Nonempty (Collar n M)

/-- **A manifold with empty boundary has a collar**: the empty map. -/
theorem hasCollar_of_boundary_eq_empty {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    (h : (𝓡∂ (n + 1)).boundary M = ∅) : HasCollar n M := by
  haveI : IsEmpty ((𝓡∂ (n + 1)).boundary M) := by
    rw [h]; infer_instance
  haveI : IsEmpty ((𝓡∂ (n + 1)).boundary M × HalfLine) := inferInstance
  exact ⟨{ toFun := fun p => (IsEmpty.false p.1).elim,
           isOpenEmbedding := Topology.IsOpenEmbedding.of_isEmpty _,
           toFun_zero := fun x => (IsEmpty.false x).elim }⟩

end

end Work.Surgery
