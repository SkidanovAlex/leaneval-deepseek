import Submission.Work.PTGeometric.SourceNull
import Submission.Work.PTGeometric.SourceBlocks

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# PTGEOMETRIC: the explicit `0`-end of the null-homotopy of a family

The `0`-end of the null-homotopy of the genuine collapse class `∏ i, tubeAlpha (G.rep i)` of a finite
family is the explicit concatenation of `m` copies of the pieces' collapse loops.  For the source
construction (`SOURCE_PLAN.md` §1.4) the *blocks* of the concatenation must be indexed by
`Fin m × ι`: each block carries one copy of one piece's collapse loop, and the preimage of the core in
a block is exactly the piece (up to the block reparametrisation of the cube), so that the intersection
of the null-bordism with the boundary is the disjoint union of the pieces.

To make that indexing canonical, the concatenation is organised in **two levels**:

* the *outer* concatenation is along the first coordinate `0` of the cube, over `m` copies of one
  loop (so a block of it is selected by a `Fin m`);
* the *inner* loop is the concatenation along the second coordinate `1` of the cube, over the pieces
  enumerated by `Fintype.equivFin ι` (so a block of it is selected by a `Fin (Fintype.card ι)`).

Hence a block of the whole concatenation is indexed by `Fin m × Fin (Fintype.card ι) ≃ Fin m × ι`.

## Main definitions and results

* `Work.PTGeometric.blockLoop`, `Work.PTGeometric.blockInner`, `Work.PTGeometric.alphaFamily`
* `Work.PTGeometric.alphaFamily_class`
* `Work.PTGeometric.FamilySource`, `Work.PTGeometric.familySource`
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open scoped Manifold ContDiff Topology unitInterval
open Function Set Topology Manifold Filter

namespace Work.PTGeometric

noncomputable section

open Work.ThomBordism
open Work.ThomBordism.PontryaginThom

variable {k : ℕ} {D : ThomTarget k} {ι : Type} [Fintype ι] {Fam : ι → Man8}

/-- **The `j`-th piece's collapse loop**, read along the canonical enumeration `Fintype.equivFin ι`. -/
def blockLoop (G : GenuineTubeGeometry k D ι Fam) (j : Fin (Fintype.card ι)) :
    GenLoop (Fin (k + 8)) D.T D.t₀ :=
  (G.rep ((Fintype.equivFin ι).symm j)).collapse

/-- **The inner concatenation**: the pieces' collapse loops concatenated along the second coordinate of
the cube.  Its blocks are indexed by `Fin (Fintype.card ι)`. -/
def blockInner (G : GenuineTubeGeometry k D ι Fam) : GenLoop (Fin (k + 8)) D.T D.t₀ :=
  genLoopListConcat ⟨1, by omega⟩ (List.ofFn (blockLoop (D := D) (Fam := Fam) G))

/-- **The `0`-end of the null-homotopy of a family**: `m` copies of the inner concatenation,
concatenated along the first coordinate of the cube.  Its blocks are indexed by
`Fin m × Fin (Fintype.card ι) ≃ Fin m × ι`. -/
def alphaFamily (G : GenuineTubeGeometry k D ι Fam) (m : ℕ) : GenLoop (Fin (k + 8)) D.T D.t₀ :=
  genLoopListConcat ⟨0, by omega⟩ (List.ofFn (fun _ : Fin m => blockInner G))

@[simp] theorem blockLoop_apply (G : GenuineTubeGeometry k D ι Fam) (j : Fin (Fintype.card ι)) :
    blockLoop (D := D) (Fam := Fam) G j
      = (G.rep ((Fintype.equivFin ι).symm j)).collapse := rfl

/-- **The class of the explicit `0`-end is the `m`-th power of the product of the pieces'
classes.** -/
theorem alphaFamily_class (G : GenuineTubeGeometry k D ι Fam) (m : ℕ) :
    letI : CommGroup (Quotient (GenLoop.Homotopic.setoid (Fin (k + 8)) D.t₀)) :=
      inferInstanceAs (CommGroup (HomotopyGroup (Fin (k + 8)) D.T D.t₀))
    (Quotient.mk _ (alphaFamily (D := D) (Fam := Fam) G m) :
        HomotopyGroup (Fin (k + 8)) D.T D.t₀) = (∏ i, tubeAlpha (G.rep i)) ^ m := by
  letI : CommGroup (Quotient (GenLoop.Homotopic.setoid (Fin (k + 8)) D.t₀)) :=
    inferInstanceAs (CommGroup (HomotopyGroup (Fin (k + 8)) D.T D.t₀))
  haveI : Nonempty (Fin (k + 8)) := ⟨⟨0, by omega⟩⟩
  haveI : Nontrivial (Fin (k + 8)) := ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp⟩
  have hinner : (Quotient.mk _ (blockInner G) : HomotopyGroup (Fin (k + 8)) D.T D.t₀)
      = ∏ j : Fin (Fintype.card ι),
          (Quotient.mk _ (blockLoop (D := D) (Fam := Fam) G j) :
            HomotopyGroup (Fin (k + 8)) D.T D.t₀) := by
    rw [blockInner, genLoopListConcat_class, List.map_ofFn, List.prod_ofFn]
    exact Finset.prod_congr rfl fun i _ => rfl
  have houter : (Quotient.mk _ (alphaFamily (D := D) (Fam := Fam) G m) :
        HomotopyGroup (Fin (k + 8)) D.T D.t₀)
      = ∏ _ : Fin m, (Quotient.mk _ (blockInner G) : HomotopyGroup (Fin (k + 8)) D.T D.t₀) := by
    rw [alphaFamily, genLoopListConcat_class, List.map_ofFn, List.prod_ofFn]
    exact Finset.prod_congr rfl fun i _ => rfl
  rw [houter, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hinner]
  congr 1
  exact Fintype.prod_equiv (Fintype.equivFin ι).symm
    (fun j : Fin (Fintype.card ι) =>
      (Quotient.mk _ (blockLoop (D := D) (Fam := Fam) G j) :
        HomotopyGroup (Fin (k + 8)) D.T D.t₀))
    (fun i : ι => tubeAlpha (G.rep i)) (fun j => rfl)

/-- **The null-homotopy data of a family's collapse class**: the collapsing quotient map, the
null-homotopy of the explicit `0`-end `alphaFamily`, and the three properties the source construction
consumes (the collar identity, the basepoint at the far end, and the basepoint on the collapsed
boundary of the cube). -/
structure FamilySource (G : GenuineTubeGeometry k D ι Fam) (m : ℕ) where
  φ : C(Fin (k + 8) → Set.Icc (0 : ℝ) 1,
    Metric.sphere (0 : EuclideanSpace ℝ (Fin ((k + 8) + 1))) 1)
  H : C(SourceModel (k + 8), D.T)
  collar : ∀ (y : Fin (k + 8) → Set.Icc (0 : ℝ) 1) (τ : Set.Icc (1 : ℝ) 2),
    (τ : ℝ) ≤ 3 / 2 → H (φ y, τ) = alphaFamily (D := D) (Fam := Fam) G m y
  far : ∀ s : Metric.sphere (0 : EuclideanSpace ℝ (Fin ((k + 8) + 1))) 1,
    H (s, ⟨2, by norm_num⟩) = D.t₀
  bdry : ∀ (y : Fin (k + 8) → Set.Icc (0 : ℝ) 1), y ∈ _root_.Cube.boundary (Fin (k + 8)) →
    ∀ τ : Set.Icc (1 : ℝ) 2, H (φ y, τ) = D.t₀
  /-- the collapsing map collapses the boundary of the cube to a point -/
  bdry_eq : ∀ y ∈ _root_.Cube.boundary (Fin (k + 8)), φ y = φ 0

/-- **The source homotopy of a family exists** as soon as the `m`-th power of the product of the
pieces' collapse classes is trivial. -/
theorem familySource_exists (G : GenuineTubeGeometry k D ι Fam) (m : ℕ)
    (hpow : (∏ i, tubeAlpha (G.rep i)) ^ m = 1) :
    Nonempty (FamilySource (D := D) (Fam := Fam) G m) := by
  haveI : Nonempty (Fin (k + 8)) := ⟨⟨0, by omega⟩⟩
  haveI : Nontrivial (Fin (k + 8)) := ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp⟩
  letI : CommGroup (Quotient (GenLoop.Homotopic.setoid (Fin (k + 8)) D.t₀)) :=
    inferInstanceAs (CommGroup (HomotopyGroup (Fin (k + 8)) D.T D.t₀))
  have hclass : (Quotient.mk _ (alphaFamily (D := D) (Fam := Fam) G m) :
      HomotopyGroup (Fin (k + 8)) D.T D.t₀) = (1 : HomotopyGroup (Fin (k + 8)) D.T D.t₀) :=
    (alphaFamily_class G m).trans hpow
  obtain ⟨φ, H, h1, h2, h3, h4⟩ := exists_sourceHomotopy_boundary D (alphaFamily G m) hclass
  exact ⟨{ φ := φ, H := H, collar := h1, far := h2, bdry := h3, bdry_eq := h4 }⟩

/-- The chosen source homotopy data of a family. -/
noncomputable def familySource (G : GenuineTubeGeometry k D ι Fam) (m : ℕ)
    (hpow : (∏ i, tubeAlpha (G.rep i)) ^ m = 1) :
    FamilySource (D := D) (Fam := Fam) G m :=
  Classical.choice (familySource_exists G m hpow)

end

end Work.PTGeometric
