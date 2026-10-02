import Submission.Work.PTGeometric.SourceModelHomotopy
import Submission.Work.PTGeometric.exists_annulusStationaryHomotopy
import Submission.Work.PTGeometric.ConcatLoop

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# PTGEOMETRIC: the source homotopy on the annulus, with a *prescribed* `0`-end

The last mile's source is the annulus `Work.PTGeometric.SourceModel (k+8) = S^{k+8} × [1,2]`, and the
null-homotopy on it must have a `0`-end whose core preimage is the disjoint union of the pieces: this
is what forces the `0`-end to be the **explicit concatenation** of the pieces' collapse maps
(README §20.4), rather than an arbitrary representative of the same class.

This file performs the reduction, starting from a cube loop `α` whose class is trivial:

* `Quotient.exact` turns `⟦α⟧ = 1` into a based homotopy `α ≃ const`, i.e. a cube homotopy
  `F : I × I^{k+8} → T` with `F (0,·) = α`, constant on the lateral boundary and at the `1`-end
  (exactly the shape of `Work.PTGeometric.exists_nullHomotopy`);
* `Work.PTGeometric.exists_annulusStationaryHomotopy` descends it to `S^{k+8} × I` (it produces the
  collapsing quotient map `φ` itself, so no choice of `φ` has to be made here), making it stationary
  on the first half of the interval;
* `Work.PTGeometric.exists_sourceModelHomotopy` transports it to the annulus,
  `(s,τ) ↦ (s,τ-1)`.

The output is a continuous `H : SourceModel (k+8) → T` with `H (φ y, τ) = α y` on the whole collar
`τ ≤ 3/2` (so that the ambient data of `H` near the `0`-end are those of the collapse map, TUBULAR's
`tube_ambient_data`) and `H = D.t₀` at the far end `τ = 2`.

## Main results

* `Work.PTGeometric.exists_sourceHomotopy`
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open scoped Manifold ContDiff Topology unitInterval
open Function Set Topology Manifold Filter

namespace Work.PTGeometric

noncomputable section

open Work.ThomBordism
open Work.ThomBordism.PontryaginThom

/-- **The source homotopy on the annulus with prescribed `0`-end.**  From a cube loop `α` of trivial
class in `π_{k+8}(D.T, D.t₀)` there are the collapsing quotient map `φ : I^{k+8} → S^{k+8}` and a
continuous `H : SourceModel (k+8) → D.T` which is `α` (read along `φ`) on the whole collar
`1 ≤ τ ≤ 3/2` of the annulus and the basepoint at `τ = 2`. -/
theorem exists_sourceHomotopy {k : ℕ} (D : ThomTarget k)
    (α : GenLoop (Fin (k + 8)) D.T D.t₀)
    (hα : (Quotient.mk _ α : HomotopyGroup (Fin (k + 8)) D.T D.t₀)
      = (1 : HomotopyGroup (Fin (k + 8)) D.T D.t₀)) :
    ∃ (φ : C(Fin (k + 8) → Set.Icc (0 : ℝ) 1,
        Metric.sphere (0 : EuclideanSpace ℝ (Fin ((k + 8) + 1))) 1))
      (H : C(SourceModel (k + 8), D.T)),
      (∀ (y : Fin (k + 8) → Set.Icc (0 : ℝ) 1) (τ : Set.Icc (1 : ℝ) 2),
        (τ : ℝ) ≤ 3 / 2 → H (φ y, τ) = α y) ∧
      (∀ s : Metric.sphere (0 : EuclideanSpace ℝ (Fin ((k + 8) + 1))) 1,
        H (s, ⟨2, by norm_num⟩) = D.t₀) := by
  have hn : 1 ≤ k + 8 := by omega
  -- the based homotopy of `α` with the constant loop
  have hone : (Quotient.mk _ (GenLoop.const : GenLoop (Fin (k + 8)) D.T D.t₀)
      : HomotopyGroup (Fin (k + 8)) D.T D.t₀)
      = (1 : HomotopyGroup (Fin (k + 8)) D.T D.t₀) := HomotopyGroup.one_def.symm
  have hHom : GenLoop.Homotopic α (GenLoop.const : GenLoop (Fin (k + 8)) D.T D.t₀) :=
    Quotient.exact (hα.trans hone)
  obtain ⟨F⟩ := hHom
  -- the cube homotopy, constant on the lateral boundary
  have hH : ∀ (t : Set.Icc (0 : ℝ) 1) (y : Fin (k + 8) → Set.Icc (0 : ℝ) 1),
      y ∈ Cube.boundary (Fin (k + 8)) → F.toHomotopy.toContinuousMap (t, y) = D.t₀ := by
    intro t y hy
    exact (F.prop' t y hy).trans (α.2 y hy)
  have hH1 : ∀ y : Fin (k + 8) → Set.Icc (0 : ℝ) 1,
      F.toHomotopy.toContinuousMap (1, y) = D.t₀ := fun y => F.map_one_left y
  obtain ⟨φ, Hbar, hHbar0, hstat, h1⟩ :=
    exists_annulusStationaryHomotopy (n := k + 8) hn F.toHomotopy.toContinuousMap hH hH1
  obtain ⟨H', hH'⟩ := exists_sourceModelHomotopy Hbar hstat h1
  refine ⟨φ, H', ?_, hH'.2⟩
  intro y τ hτ
  rw [hH'.1 (φ y) τ hτ, hHbar0 y (φ y) rfl]
  exact F.map_zero_left y


/-- **The source homotopy with the `m`-fold concatenation of a list of loops as `0`-end.**

Given loops `l` (the pieces' collapse maps) whose classes' product has trivial `m`-th power, the
explicit concatenation `α` of `m` copies of each of them (flattening the `m`-fold repetition of the
list) has trivial class, so `Work.PTGeometric.exists_sourceHomotopy` applies to it: the annulus
carries a homotopy whose `0`-collar is *that* explicit loop and whose far end is the basepoint.  This
is the `0`-end input of the source construction (README §20.4 and §21.2): the core preimage of `α` is
the disjoint union of the pieces, by the block formula
(`Work.PTGeometric.genLoop_transAt_preimage`). -/
theorem exists_sourceHomotopy_of_list {k : ℕ} (D : ThomTarget k) (m : ℕ)
    (l : List (GenLoop (Fin (k + 8)) D.T D.t₀)) :
    letI : CommGroup (Quotient (GenLoop.Homotopic.setoid (Fin (k + 8)) D.t₀)) :=
      inferInstanceAs (CommGroup (HomotopyGroup (Fin (k + 8)) D.T D.t₀))
    (((l.map (fun g => (Quotient.mk _ g :
        HomotopyGroup (Fin (k + 8)) D.T D.t₀))).prod) ^ m
      = (1 : HomotopyGroup (Fin (k + 8)) D.T D.t₀)) →
    ∃ (φ : C(Fin (k + 8) → Set.Icc (0 : ℝ) 1,
        Metric.sphere (0 : EuclideanSpace ℝ (Fin ((k + 8) + 1))) 1))
      (H : C(SourceModel (k + 8), D.T)),
      (∀ (y : Fin (k + 8) → Set.Icc (0 : ℝ) 1) (τ : Set.Icc (1 : ℝ) 2),
        (τ : ℝ) ≤ 3 / 2 →
          H (φ y, τ) = genLoopListConcat ⟨0, by omega⟩
            (List.flatten (List.replicate m l)) y) ∧
      (∀ s : Metric.sphere (0 : EuclideanSpace ℝ (Fin ((k + 8) + 1))) 1,
        H (s, ⟨2, by norm_num⟩) = D.t₀) := by
  haveI : Nonempty (Fin (k + 8)) := ⟨⟨0, by omega⟩⟩
  haveI : Nontrivial (Fin (k + 8)) := ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp⟩
  letI : CommGroup (Quotient (GenLoop.Homotopic.setoid (Fin (k + 8)) D.t₀)) :=
    inferInstanceAs (CommGroup (HomotopyGroup (Fin (k + 8)) D.T D.t₀))
  intro hpow
  have hclass : (Quotient.mk _ (genLoopListConcat ⟨0, by omega⟩
        (List.flatten (List.replicate m l))) : HomotopyGroup (Fin (k + 8)) D.T D.t₀)
      = (((l.map (fun g => (Quotient.mk _ g :
          HomotopyGroup (Fin (k + 8)) D.T D.t₀))).prod) ^ m) :=
    genLoop_listConcat_flatten_class (X := D.T) (x := D.t₀) ⟨0, by omega⟩ m l
  exact exists_sourceHomotopy D _ (hclass.trans hpow)



/-- The product of the classes of a finite family, read along any enumeration of the index type
(`Finset.univ.val.map f` as a list), is the `Finset`-product. -/
theorem finset_prod_eq_toList_prod {M : Type*} [CommMonoid M] {ι : Type*} [Fintype ι]
    (f : ι → M) :
    (((Finset.univ.val.map f)).toList).prod = ∏ i, f i := by
  rw [Multiset.prod_toList, ← Finset.prod_eq_multiset_prod]

/-- **The source homotopy from the family's power condition.**

For a finite family of loops `r` (the pieces' genuine collapse maps, whose classes' product is the
Pontryagin–Thom class of the disjoint union of the pieces) and a multiplicity `m` with the `m`-th
power of the product of their classes trivial, the annulus carries a homotopy whose `0`-collar is the
explicit `m`-fold concatenation of the loops (read along the enumeration
`(Finset.univ.val.map r).toList`) and whose far end is the basepoint.  This is the input of the source
construction.

The hypothesis is stated through the enumeration so that it is *syntactically* the class of the
explicit concatenation; `Work.PTGeometric.finset_prod_eq_toList_prod` converts the usual
`Finset`-product form `(∏ i, ⟦r i⟧)^m = 1` into it. -/
theorem exists_sourceHomotopy_of_family {k : ℕ} (D : ThomTarget k) {ι : Type} [Fintype ι]
    (r : ι → GenLoop (Fin (k + 8)) D.T D.t₀) (m : ℕ) :
    letI : CommGroup (Quotient (GenLoop.Homotopic.setoid (Fin (k + 8)) D.t₀)) :=
      inferInstanceAs (CommGroup (HomotopyGroup (Fin (k + 8)) D.T D.t₀))
    ((((((Finset.univ.val.map r)).toList).map
        (fun g => (Quotient.mk _ g : HomotopyGroup (Fin (k + 8)) D.T D.t₀))).prod) ^ m
      = (1 : HomotopyGroup (Fin (k + 8)) D.T D.t₀)) →
    ∃ (φ : C(Fin (k + 8) → Set.Icc (0 : ℝ) 1,
        Metric.sphere (0 : EuclideanSpace ℝ (Fin ((k + 8) + 1))) 1))
      (H : C(SourceModel (k + 8), D.T)),
      (∀ (y : Fin (k + 8) → Set.Icc (0 : ℝ) 1) (τ : Set.Icc (1 : ℝ) 2),
        (τ : ℝ) ≤ 3 / 2 →
          H (φ y, τ) = genLoopListConcat ⟨0, by omega⟩
            (List.flatten (List.replicate m ((Finset.univ.val.map r)).toList)) y) ∧
      (∀ s : Metric.sphere (0 : EuclideanSpace ℝ (Fin ((k + 8) + 1))) 1,
        H (s, ⟨2, by norm_num⟩) = D.t₀) := by
  letI : CommGroup (Quotient (GenLoop.Homotopic.setoid (Fin (k + 8)) D.t₀)) :=
    inferInstanceAs (CommGroup (HomotopyGroup (Fin (k + 8)) D.T D.t₀))
  intro hpow
  exact exists_sourceHomotopy_of_list D m ((Finset.univ.val.map r)).toList hpow


/-- **The cube null-homotopy of the explicit concatenation.**

For a list of loops `l` whose classes' `m`-th power product is trivial, there is a *cube* homotopy
`F : I × I^{k+8} → D.T` with `F (0,·)` equal to the explicit `m`-fold concatenation of `l`, constant
on the lateral boundary and equal to the basepoint at the `1`-end.  Unlike
`Work.PTGeometric.exists_sourceHomotopy_of_list` this stays on the cube: the source construction of
README §25 composes it with a *smooth* map of its source into the cube, so that the collapse map is
never descended along the (non-smooth) quotient map `Work.Stems.exists_collapsingMap`. -/
theorem exists_cubeSourceHomotopy {k : ℕ} (D : ThomTarget k) (m : ℕ)
    (l : List (GenLoop (Fin (k + 8)) D.T D.t₀)) :
    letI : CommGroup (Quotient (GenLoop.Homotopic.setoid (Fin (k + 8)) D.t₀)) :=
      inferInstanceAs (CommGroup (HomotopyGroup (Fin (k + 8)) D.T D.t₀))
    (((l.map (fun g => (Quotient.mk _ g :
        HomotopyGroup (Fin (k + 8)) D.T D.t₀))).prod) ^ m
      = (1 : HomotopyGroup (Fin (k + 8)) D.T D.t₀)) →
    ∃ F : C(Set.Icc (0 : ℝ) 1 × (Fin (k + 8) → Set.Icc (0 : ℝ) 1), D.T),
      (∀ y : Fin (k + 8) → Set.Icc (0 : ℝ) 1,
        F (0, y) = genLoopListConcat ⟨0, by omega⟩ (List.flatten (List.replicate m l)) y) ∧
      (∀ (t : Set.Icc (0 : ℝ) 1) (y : Fin (k + 8) → Set.Icc (0 : ℝ) 1),
        y ∈ Cube.boundary (Fin (k + 8)) → F (t, y) = D.t₀) ∧
      (∀ y : Fin (k + 8) → Set.Icc (0 : ℝ) 1, F (1, y) = D.t₀) := by
  haveI : Nonempty (Fin (k + 8)) := ⟨⟨0, by omega⟩⟩
  haveI : Nontrivial (Fin (k + 8)) := ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp⟩
  letI : CommGroup (Quotient (GenLoop.Homotopic.setoid (Fin (k + 8)) D.t₀)) :=
    inferInstanceAs (CommGroup (HomotopyGroup (Fin (k + 8)) D.T D.t₀))
  intro hpow
  set α := genLoopListConcat (X := D.T) (x := D.t₀) ⟨0, by omega⟩
    (List.flatten (List.replicate m l)) with hα
  have hclass : (Quotient.mk _ α : HomotopyGroup (Fin (k + 8)) D.T D.t₀)
      = (((l.map (fun g => (Quotient.mk _ g :
          HomotopyGroup (Fin (k + 8)) D.T D.t₀))).prod) ^ m) :=
    genLoop_listConcat_flatten_class (X := D.T) (x := D.t₀) ⟨0, by omega⟩ m l
  have hone : (Quotient.mk _ (GenLoop.const : GenLoop (Fin (k + 8)) D.T D.t₀)
      : HomotopyGroup (Fin (k + 8)) D.T D.t₀)
      = (1 : HomotopyGroup (Fin (k + 8)) D.T D.t₀) := HomotopyGroup.one_def.symm
  have hHom : GenLoop.Homotopic α (GenLoop.const : GenLoop (Fin (k + 8)) D.T D.t₀) :=
    Quotient.exact ((hclass.trans hpow).trans hone)
  obtain ⟨F⟩ := hHom
  exact ⟨F.toHomotopy.toContinuousMap,
    fun y => F.map_zero_left y,
    fun t y hy => (F.prop' t y hy).trans (α.2 y hy),
    fun y => F.map_one_left y⟩

end

end Work.PTGeometric
