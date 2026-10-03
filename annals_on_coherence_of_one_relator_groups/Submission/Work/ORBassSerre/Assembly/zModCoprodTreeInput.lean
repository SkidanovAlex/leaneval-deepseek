/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Bass--Serre tree of `ℤ/n ∗ F(γ)` (node N12)

This file discharges `Work.ORAssembly.ZModCoprodTreeInput`: the free product `ℤ/n ∗ F(γ)` acts on
the Bass--Serre tree whose vertices are the cosets of the two factors, with vertex stabilizers the
conjugates of the images of the factors.

The tree is the quiver `Work.ORBassSerre.CoprodTree.Vertex` of
`Submission/Work/ORBassSerre/CoprodTree/`; it is a `Work.ORBassSerre.IsTree`
(`Work.ORBassSerre.CoprodTree.isTree_vertex`) on which the free product acts compatibly
(`Work.ORBassSerre.CoprodTree.instGraphAction`), so
`Work.ORDunwoody.Lemmas.ofQuiverTree` turns it into a `Work.ORDunwoody.GTree`.  The vertex
stabilizers are computed in `Work.ORBassSerre.CoprodTree.vertexStab_vA` and
`Work.ORBassSerre.CoprodTree.vertexStab_vB`.
-/
import Mathlib
import Submission.Work.ORAssembly.Defs
import Submission.Work.ORDunwoody.Hypotheses
import Submission.Work.ORBassSerre.Interface
import Submission.Work.ORDunwoody.Lemmas.ofQuiverTree
import Submission.Work.ORBassSerre.CoprodTree.Tree
import Submission.Work.ORBassSerre.CoprodTree.vertexStab_vA
import Submission.Work.ORBassSerre.CoprodTree.vertexStab_vB

namespace Work.ORBassSerre.Assembly

open Work.ORBassSerre.CoprodTree

universe u

/-- Node N12 discharging `Work.ORAssembly.ZModCoprodTreeInput`: the Bass--Serre tree of the free
product `ℤ/n ∗ F(γ)`, a tree on which it acts with vertex stabilizers conjugate to one of the two
factors.  Suggested model: vertices are the cosets of the two factors in the free product, with
adjacency given by the obvious edges; use the normal form of `Monoid.Coprod` to prove that the
resulting graph is a tree. -/
theorem zModCoprodTreeInput : Work.ORAssembly.ZModCoprodTreeInput.{u} := by
  intro γ n
  haveI : Nonempty (Vertex (Multiplicative (ZMod n)) (FreeGroup γ)) := ⟨vA 1⟩
  obtain ⟨T, -, -⟩ := Work.ORDunwoody.Lemmas.ofQuiverTree
    (G := Monoid.Coprod (Multiplicative (ZMod n)) (FreeGroup γ))
    (V := Vertex (Multiplicative (ZMod n)) (FreeGroup γ))
    (isTree_vertex (A := Multiplicative (ZMod n)) (B := FreeGroup γ))
  refine ⟨Vertex (Multiplicative (ZMod n)) (FreeGroup γ), inferInstance, T, ?_⟩
  intro v
  rcases v with c | c
  · obtain ⟨g, rfl⟩ := Quotient.exists_rep c
    exact Or.inl ⟨g, vertexStab_vA (A := Multiplicative (ZMod n)) (B := FreeGroup γ) g⟩
  · obtain ⟨g, rfl⟩ := Quotient.exists_rep c
    exact Or.inr ⟨g, vertexStab_vB (A := Multiplicative (ZMod n)) (B := FreeGroup γ) g⟩

end Work.ORBassSerre.Assembly
