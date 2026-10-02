import Mathlib
import Submission.Work.PTGeometric.SourceFamily
import Submission.Work.PTGeometric.genLoopListConcat_eq_get
import Submission.Work.PTGeometric.cubeToEuc_mem_openCube
import Submission.Work.PTGeometric.genLoopListConcat_preimage_homeo
import Submission.Work.PTGeometric.collapse_corePreimage_homeo

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# PTGEOMETRIC: the preimage of the core of the `0`-end `alphaFamily` is the pieces

The main statement of this file, `Work.PTGeometric.alphaFamily_corePreimage_homeo`, is the
statement that the `0`-end of the null-homotopy of a family — the explicit two-level concatenation
`alphaFamily G m` of the pieces' collapse loops — has, as the preimage of the core of the universal
Thom space, exactly `m` disjoint copies of the family's pieces:

`{z | alphaFamily G m z ∈ G.core} ≃ₜ Σ a : Fin m × ι, (Fam a.2).pt`.

The proof is the *block decomposition* of an iterated concatenation, applied twice:

* `genLoopListConcat_preimage_homeo` (proved in `genLoopListConcat_preimage_homeo.lean`)
  decomposes the preimage of `A` under `genLoopListConcat i l` as the disjoint union of the
  preimages under the elements of `l`, one per dyadic block of the `i`-th coordinate.  This is the
  formal counterpart of the fact that a concatenation reads its `k`-th factor on the `k`-th block of
  the `i`-th coordinate, and that each block misses the boundary of the cube (because the pieces are
  loops and the core does not contain the base point);
* applied to the outer concatenation along the coordinate `0` (the `m` copies of `blockInner`) and
  then to the inner concatenation along the coordinate `1` (the pieces) it gives the decomposition
  of the preimage into `m × card ι` blocks;
* `collapse_corePreimage_homeo` (proved in `collapse_corePreimage_homeo.lean`) identifies each
  block — the preimage of the core under the Pontryagin–Thom representative's collapse — with the
  corresponding piece `(Fam i).pt`, via `G.isGeom`, `G.zero`, the cube homeomorphism `cubeToEuc`
  and the closed embedding `Fam i ↪ ℝ^{8+k}`.

The remaining bookkeeping (reindexing the sigmas of the two block decompositions, and
reassociating the sigma over `Fin m × ι`) is done here.

## Main results

* `Work.PTGeometric.nonempty_sigma_congr`, `Work.PTGeometric.nonempty_sigma_prod`
* `Work.PTGeometric.alphaFamily_corePreimage_homeo`
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

open scoped Topology unitInterval
open Function Set

namespace Work.PTGeometric

noncomputable section

open Work.ThomBordism
open Work.ThomBordism.PontryaginThom

variable {k : ℕ} {D : ThomTarget k} {ι : Type} [Fintype ι] {Fam : ι → Man8}

/-! ## Two generic reindexings of sigma types -/

/-- **Reindexing a sigma type along a bijection, with homeomorphic fibres.**  If `e : ι ≃ κ` and
each fibre `X i` is homeomorphic to `Y (e i)`, then `Σ i, X i` is homeomorphic to `Σ j, Y j`. -/
theorem nonempty_sigma_congr {ι κ : Type*} {X : ι → Type*} {Y : κ → Type*}
    [∀ i, TopologicalSpace (X i)] [∀ j, TopologicalSpace (Y j)]
    (e : ι ≃ κ) (h : ∀ i, Nonempty (X i ≃ₜ Y (e i))) :
    Nonempty ((Σ i, X i) ≃ₜ (Σ j, Y j)) := by
  have G : ∀ i, X i ≃ₜ Y (e i) := fun i => Classical.choice (h i)
  exact ⟨(IsHomeomorph.sigmaMap (f := ⇑e) e.bijective (g := fun i => ⇑(G i))
    (fun i => (G i).isHomeomorph)).homeomorph⟩

/-- **The sigma type over a product is the iterated sigma.**  `Σ _ : Fin m, Σ a : ι, Z a` is
homeomorphic to `Σ p : Fin m × ι, Z p.2`. -/
theorem nonempty_sigma_prod {m : ℕ} {ι : Type} {Z : ι → Type*} [∀ a, TopologicalSpace (Z a)] :
    Nonempty ((Σ _k : Fin m, Σ a : ι, Z a) ≃ₜ (Σ p : Fin m × ι, Z p.2)) := by
  have hf : Continuous (fun x : (Σ _k : Fin m, Σ a : ι, Z a) =>
      (⟨(x.1, x.2.1), x.2.2⟩ : (Σ p : Fin m × ι, Z p.2))) := by
    apply continuous_sigma
    intro k
    apply continuous_sigma
    intro a
    exact @continuous_sigmaMk (Fin m × ι) (fun p => Z p.2) _ (k, a)
  have hg : Continuous (fun x : (Σ p : Fin m × ι, Z p.2) =>
      (⟨x.1.1, ⟨x.1.2, x.2⟩⟩ : (Σ _k : Fin m, Σ a : ι, Z a))) := by
    apply continuous_sigma
    intro p
    exact (@continuous_sigmaMk (Fin m) (fun k => Sigma fun a : ι => Z a) _ p.1).comp
      (@continuous_sigmaMk ι (fun a => Z a) _ p.2)
  refine ⟨{ toFun := fun x => ⟨(x.1, x.2.1), x.2.2⟩
            invFun := fun x => ⟨x.1.1, ⟨x.1.2, x.2⟩⟩
            left_inv := fun x => by cases x with | mk a y => cases y with | mk b z => rfl
            right_inv := fun x => by cases x with | mk p z => rfl
            continuous_toFun := hf
            continuous_invFun := hg }⟩

/-! ## The assembly -/

/-- **The main theorem, given the two block-decomposition inputs.** -/
private theorem corePreimage_of
    (hPre : ∀ {N : Type} [DecidableEq N] {X : Type} [TopologicalSpace X] {x : X} (i : N)
      (l : List (GenLoop N X x)) {A : Set X}, IsClosed A → x ∉ A →
      Nonempty (((genLoopListConcat i l) ⁻¹' A) ≃ₜ (Σ k : Fin l.length, ((l.get k) ⁻¹' A))))
    (hCol : ∀ {k' : ℕ} {D' : ThomTarget k'} {ι' : Type} [Fintype ι'] {Fam' : ι' → Man8}
      (G : GenuineTubeGeometry k' D' ι' Fam') (i : ι'),
      Nonempty (((G.rep i).collapse ⁻¹' G.core) ≃ₜ (Fam' i).pt))
    (G : GenuineTubeGeometry k D ι Fam) (m : ℕ) :
    Nonempty (↥{z : Fin (k + 8) → Set.Icc (0 : ℝ) 1 |
        alphaFamily (D := D) (Fam := Fam) G m z ∈ G.core} ≃ₜ
      (Σ a : Fin m × ι, (Fam a.2).pt)) := by
  classical
  -- the outer block decomposition, along the coordinate `0`
  obtain ⟨h1⟩ := hPre (N := Fin (k + 8)) (X := D.T) (x := D.t₀) (A := G.core)
    (⟨0, by omega⟩ : Fin (k + 8)) (List.ofFn (fun _ : Fin m => blockInner G))
    G.isClosed_core G.t0_notMem_core
  obtain ⟨h2⟩ := nonempty_sigma_congr (ι := Fin (List.ofFn (fun _ : Fin m => blockInner G)).length)
    (κ := Fin m)
    (X := fun kk => ↥((List.ofFn (fun _ : Fin m => blockInner G)).get kk ⁻¹' G.core))
    (Y := fun _kk => ↥(blockInner G ⁻¹' G.core))
    (finCongr List.length_ofFn) (fun kk => ⟨Homeomorph.setCongr (by rw [List.get_ofFn])⟩)
  -- the inner block decomposition, along the coordinate `1`
  have step2 : ∀ _kk : Fin m, Nonempty (↥(blockInner G ⁻¹' G.core) ≃ₜ
      (Σ j : Fin (Fintype.card ι), ↥(blockLoop G j ⁻¹' G.core))) := by
    intro kk
    obtain ⟨h1'⟩ := hPre (N := Fin (k + 8)) (X := D.T) (x := D.t₀) (A := G.core)
      (⟨1, by omega⟩ : Fin (k + 8)) (List.ofFn (blockLoop G)) G.isClosed_core G.t0_notMem_core
    obtain ⟨h2'⟩ := nonempty_sigma_congr
      (ι := Fin (List.ofFn (blockLoop G)).length) (κ := Fin (Fintype.card ι))
      (X := fun j => ↥((List.ofFn (blockLoop G)).get j ⁻¹' G.core))
      (Y := fun j => ↥(blockLoop G j ⁻¹' G.core))
      (finCongr List.length_ofFn)
      (fun j => ⟨Homeomorph.setCongr (by rw [List.get_ofFn]; simp [finCongr])⟩)
    exact ⟨h1'.trans h2'⟩
  -- each block is the corresponding piece
  have step3 : ∀ j : Fin (Fintype.card ι),
      Nonempty (↥(blockLoop G j ⁻¹' G.core) ≃ₜ (Fam ((Fintype.equivFin ι).symm j)).pt) :=
    fun j => hCol G ((Fintype.equivFin ι).symm j)
  obtain ⟨hInner⟩ := nonempty_sigma_congr (ι := Fin m) (κ := Fin m)
    (X := fun _kk => ↥(blockInner G ⁻¹' G.core))
    (Y := fun _kk => (Σ j : Fin (Fintype.card ι), ↥(blockLoop G j ⁻¹' G.core)))
    (Equiv.refl (Fin m)) step2
  obtain ⟨hPiece⟩ := nonempty_sigma_congr (ι := Fin m) (κ := Fin m)
    (X := fun _kk => (Σ j : Fin (Fintype.card ι), ↥(blockLoop G j ⁻¹' G.core)))
    (Y := fun _kk => (Σ j : Fin (Fintype.card ι), (Fam ((Fintype.equivFin ι).symm j)).pt))
    (Equiv.refl (Fin m))
    (fun _kk => nonempty_sigma_congr (ι := Fin (Fintype.card ι)) (κ := Fin (Fintype.card ι))
      (X := fun j => ↥(blockLoop G j ⁻¹' G.core))
      (Y := fun j => (Fam ((Fintype.equivFin ι).symm j)).pt) (Equiv.refl _) step3)
  obtain ⟨hIdx⟩ := nonempty_sigma_congr (ι := Fin m) (κ := Fin m)
    (X := fun _kk => (Σ j : Fin (Fintype.card ι), (Fam ((Fintype.equivFin ι).symm j)).pt))
    (Y := fun _kk => (Σ a : ι, (Fam a).pt)) (Equiv.refl (Fin m))
    (fun _kk => nonempty_sigma_congr (ι := Fin (Fintype.card ι)) (κ := ι)
      (X := fun j => (Fam ((Fintype.equivFin ι).symm j)).pt)
      (Y := fun a => (Fam a).pt) ((Fintype.equivFin ι).symm) (fun j => ⟨Homeomorph.refl _⟩))
  obtain ⟨hProd⟩ := nonempty_sigma_prod (m := m) (ι := ι) (Z := fun a => (Fam a).pt)
  exact ⟨h1.trans h2 |>.trans hInner |>.trans hPiece |>.trans hIdx |>.trans hProd⟩

/-- **The preimage of the core of the `0`-end is the disjoint union of the pieces.**

The `0`-end `alphaFamily G m` of the null-homotopy of the family is the explicit two-level
concatenation of `m` copies of the pieces' collapse loops.  Its preimage of the core of the
universal Thom space is the union of the `m · card ι` dyadic blocks of the cube, and the block of
the pair `(s, j)` — read at the piece `(Fintype.equivFin ι).symm j` — is exactly that piece's
preimage of the core, hence homeomorphic to the piece by `collapse_corePreimage_homeo`. -/
theorem alphaFamily_corePreimage_homeo {k : ℕ} {D : Work.ThomBordism.PontryaginThom.ThomTarget k}
    {ι : Type} [Fintype ι] {Fam : ι → Work.ThomBordism.Man8}
    (G : Work.PTGeometric.GenuineTubeGeometry k D ι Fam) (m : ℕ) :
    Nonempty (↥{z : Fin (k + 8) → Set.Icc (0 : ℝ) 1 |
        Work.PTGeometric.alphaFamily (D := D) (Fam := Fam) G m z ∈ G.core} ≃ₜ
      (Σ a : Fin m × ι, (Fam a.2).pt)) := by
  exact corePreimage_of genLoopListConcat_preimage_homeo collapse_corePreimage_homeo G m


end

end Work.PTGeometric
