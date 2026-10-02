import Submission.Work.PTGeometric.ConcreteCollapse
import Submission.Work.PTGeometric.FlatSource
import Submission.Work.PTGeometric.exists_sourceHomotopy_boundary

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# PTGEOMETRIC: the flat source of a family — the null-homotopy and its zero set

Step 1 of `SOURCE_PLAN.md` §7: from a family's genuine collapse data (`GenuineTubeGeometry`) and a
multiplicity `m` with trivial `m`-th power of the product of the pieces' collapse classes, build

* the explicit concatenation `α` of `m` copies of the pieces' collapse loops;
* the collapsing quotient map `φ` and the annulus null-homotopy `H` of
  `Work.PTGeometric.exists_sourceHomotopy_boundary`, which is `α` on the collar and the basepoint on
  the collapsed boundary `φ (∂I^{k+8})`;
* the **flat source homotopy** `x ↦ H (φ (cubeCoord (tail (srcCast x))), srcTime (srcCast x))` on the
  half-space `EuclideanHalfSpace ((8+k)+1)`, whose zero set (the preimage of the core) is the
  null-bordism.

The map `srcCast` is the only bridge between the manifold model of `AmbientCollapseEnd` (whose ambient
dimension is `(8+k)+1`) and the cube model of the source homotopy (`k+8`); it is the identity on
coordinates.

## Main definitions and results

* `Work.PTGeometric.srcCast`
* `Work.PTGeometric.exists_sourceHomotopy_boundary_of_family`
* `Work.PTGeometric.flatSourceHomotopy8`, `…_eq_collapse`, `…_eq_basepoint_of_one_le`
-/

set_option autoImplicit false
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

/-- **The reindexing of the ambient Euclidean space**: `EuclideanSpace ℝ (Fin ((8+k)+1)) →
EuclideanSpace ℝ (Fin ((k+8)+1))`, the identity on coordinates.  It is the bridge between the manifold
model of `AmbientCollapseEnd` and the cube model of the source homotopy (`k+8`). -/
def srcCast (k : ℕ) :
    EuclideanSpace ℝ (Fin ((8 + k) + 1)) →L[ℝ] EuclideanSpace ℝ (Fin ((k + 8) + 1)) :=
  (piToEucl ((k + 8) + 1)).toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i : Fin ((k + 8) + 1) =>
      (ContinuousLinearMap.proj
        (Fin.cast (show (k + 8) + 1 = (8 + k) + 1 by omega) i)).comp
        (euclToPi ((8 + k) + 1)).toContinuousLinearMap))

theorem srcCast_apply (k : ℕ) (x : EuclideanSpace ℝ (Fin ((8 + k) + 1)))
    (i : Fin ((k + 8) + 1)) :
    srcCast k x i = x (Fin.cast (show (k + 8) + 1 = (8 + k) + 1 by omega) i) := by
  simp [srcCast, euclToPi, piToEucl]

theorem continuous_srcCast (k : ℕ) : Continuous (srcCast k) := (srcCast k).continuous

theorem head_srcCast (k : ℕ) (x : EuclideanSpace ℝ (Fin ((8 + k) + 1))) :
    head (k + 8) (srcCast k x) = x 0 := by
  show srcCast k x 0 = x 0
  rw [srcCast_apply, Fin.cast_zero]

/-- **The inverse reindexing** of `srcCast`. -/
def srcCastInv (k : ℕ) :
    EuclideanSpace ℝ (Fin ((k + 8) + 1)) →L[ℝ] EuclideanSpace ℝ (Fin ((8 + k) + 1)) :=
  (piToEucl ((8 + k) + 1)).toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i : Fin ((8 + k) + 1) =>
      (ContinuousLinearMap.proj
        (Fin.cast (show (8 + k) + 1 = (k + 8) + 1 by omega) i)).comp
        (euclToPi ((k + 8) + 1)).toContinuousLinearMap))

theorem srcCastInv_apply (k : ℕ) (x : EuclideanSpace ℝ (Fin ((k + 8) + 1)))
    (i : Fin ((8 + k) + 1)) :
    srcCastInv k x i = x (Fin.cast (show (8 + k) + 1 = (k + 8) + 1 by omega) i) := by
  simp [srcCastInv, euclToPi, piToEucl]

theorem srcCastInv_srcCast (k : ℕ) (y : EuclideanSpace ℝ (Fin ((8 + k) + 1))) :
    srcCastInv k (srcCast k y) = y := by
  ext i
  rw [srcCastInv_apply, srcCast_apply, Fin.cast_cast]
  exact congrArg (fun j : Fin ((8 + k) + 1) => y.ofLp j) (Fin.ext (by simp [Fin.cast]))

theorem continuous_coord0 (k : ℕ) :
    Continuous (fun y : EuclideanSpace ℝ (Fin ((8 + k) + 1)) => y 0) :=
  (continuous_apply 0).comp (euclToPi ((8 + k) + 1)).continuous

theorem srcTime_srcCast (k : ℕ) (x : EuclideanSpace ℝ (Fin ((8 + k) + 1))) :
    ((srcTime (k + 8) (srcCast k x) : Set.Icc (1 : ℝ) 2) : ℝ) = 1 + clamp (x 0) := by
  rw [srcTime_coe]
  show 1 + clamp (head (k + 8) (srcCast k x)) = 1 + clamp (x 0)
  rw [head_srcCast]

/-- **The source homotopy of a family, with the values on the collapsed boundary.**

For a finite family of cube loops `r` (the pieces' genuine collapse maps) and a multiplicity `m` with
trivial `m`-th power of the product of their classes, there are the collapsing quotient map `φ` and a
continuous `H : S^{k+8} × [1,2] → D.T` which is the **explicit concatenation** of `m` copies of the
loops (read along the enumeration `(Finset.univ.val.map r).toList`) on the collar `τ ≤ 3/2`, the
basepoint at `τ = 2`, and **constantly** the basepoint over the collapsed boundary `φ (∂I^{k+8})`. -/
theorem exists_sourceHomotopy_boundary_of_family {k : ℕ} (D : ThomTarget k) {ι : Type} [Fintype ι]
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
        H (s, ⟨2, by norm_num⟩) = D.t₀) ∧
      (∀ (y : Fin (k + 8) → Set.Icc (0 : ℝ) 1), y ∈ _root_.Cube.boundary (Fin (k + 8)) →
        ∀ τ : Set.Icc (1 : ℝ) 2, H (φ y, τ) = D.t₀) ∧
      (∀ y ∈ _root_.Cube.boundary (Fin (k + 8)), φ y = φ 0) := by
  haveI : Nonempty (Fin (k + 8)) := ⟨⟨0, by omega⟩⟩
  haveI : Nontrivial (Fin (k + 8)) := ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp⟩
  letI : CommGroup (Quotient (GenLoop.Homotopic.setoid (Fin (k + 8)) D.t₀)) :=
    inferInstanceAs (CommGroup (HomotopyGroup (Fin (k + 8)) D.T D.t₀))
  intro hpow
  have hclass : (Quotient.mk _ (genLoopListConcat ⟨0, by omega⟩
        (List.flatten (List.replicate m ((Finset.univ.val.map r)).toList))) :
        HomotopyGroup (Fin (k + 8)) D.T D.t₀)
      = (((((Finset.univ.val.map r)).toList).map (fun g => (Quotient.mk _ g :
          HomotopyGroup (Fin (k + 8)) D.T D.t₀))).prod) ^ m :=
    genLoop_listConcat_flatten_class (X := D.T) (x := D.t₀) (⟨0, by omega⟩ : Fin (k + 8)) m _
  exact exists_sourceHomotopy_boundary D _ (hclass.trans hpow)

/-- **The flat source homotopy of a family**: the null-homotopy `H` read at the cube coordinates
`cubeCoord (tail (srcCast x))` of the source and the time `srcTime (srcCast x)`, i.e. the map whose
zero set is the null-bordism of the pieces. -/
def flatSourceHomotopy8 (k : ℕ) {D : ThomTarget k} (H : C(SourceModel (k + 8), D.T))
    (φ : C(Fin (k + 8) → Set.Icc (0 : ℝ) 1,
      Metric.sphere (0 : EuclideanSpace ℝ (Fin ((k + 8) + 1))) 1)) :
    EuclideanSpace ℝ (Fin ((8 + k) + 1)) → D.T :=
  fun x => flatSourceHomotopy (k := k) (k + 8) H φ (srcCast k x)

theorem continuous_flatSourceHomotopy8 (k : ℕ) {D : ThomTarget k}
    (H : C(SourceModel (k + 8), D.T))
    (φ : C(Fin (k + 8) → Set.Icc (0 : ℝ) 1,
      Metric.sphere (0 : EuclideanSpace ℝ (Fin ((k + 8) + 1))) 1)) :
    Continuous (flatSourceHomotopy8 (k := k) H φ) :=
  (continuous_flatSourceHomotopy (k := k) (k + 8) H φ).comp (continuous_srcCast k)

/-- **The collar identity of the flat source homotopy of a family.** -/
theorem flatSourceHomotopy8_eq_collapse (k : ℕ) {D : ThomTarget k}
    (H : C(SourceModel (k + 8), D.T))
    (φ : C(Fin (k + 8) → Set.Icc (0 : ℝ) 1,
      Metric.sphere (0 : EuclideanSpace ℝ (Fin ((k + 8) + 1))) 1))
    (α : GenLoop (Fin (k + 8)) D.T D.t₀)
    (hH : ∀ (y : Fin (k + 8) → Set.Icc (0 : ℝ) 1) (τ : Set.Icc (1 : ℝ) 2),
      (τ : ℝ) ≤ 3 / 2 → H (φ y, τ) = α y)
    {x : EuclideanSpace ℝ (Fin ((8 + k) + 1))} (hx : x 0 ≤ 1 / 2) :
    flatSourceHomotopy8 (k := k) H φ x
      = α (cubeCoord (k + 8) (tail (k + 8) (srcCast k x))) :=
  flatSourceHomotopy_eq_collapse (k := k) (n := k + 8) H φ α hH
    (by rw [head_srcCast]; exact hx)

/-- **The flat source homotopy of a family is the basepoint at the far time end.** -/
theorem flatSourceHomotopy8_eq_basepoint_of_one_le (k : ℕ) {D : ThomTarget k}
    (H : C(SourceModel (k + 8), D.T))
    (φ : C(Fin (k + 8) → Set.Icc (0 : ℝ) 1,
      Metric.sphere (0 : EuclideanSpace ℝ (Fin ((k + 8) + 1))) 1))
    (hH2 : ∀ s : Metric.sphere (0 : EuclideanSpace ℝ (Fin ((k + 8) + 1))) 1,
      H (s, ⟨2, by norm_num⟩) = D.t₀)
    {x : EuclideanSpace ℝ (Fin ((8 + k) + 1))} (hx : 1 ≤ x 0) :
    flatSourceHomotopy8 (k := k) H φ x = D.t₀ := by
  show flatSourceHomotopy (k := k) (k + 8) H φ (srcCast k x) = D.t₀
  have hcl : clamp (head (k + 8) (srcCast k x)) = 1 := by
    rw [head_srcCast]
    exact clamp_eq_one_of_one_le hx
  have hst : srcTime (k + 8) (srcCast k x) = ⟨2, by norm_num⟩ := by
    apply Subtype.ext
    rw [srcTime_coe, hcl]
    norm_num
  rw [flatSourceHomotopy, hst]
  exact hH2 _

end

end Work.PTGeometric
