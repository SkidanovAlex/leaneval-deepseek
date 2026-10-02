import Mathlib
import Submission.Work.PTGeometric.RegionManifoldNC
import Submission.Work.PTGeometric.SourceHomotopy
import Submission.Work.PTGeometric.FlatSource

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# PTGEOMETRIC: the source homotopy on the annulus, constant on the collapsed boundary

`Work.PTGeometric.exists_sourceHomotopy` produces, from a cube loop `α` of trivial class in
`π_{k+8}(D.T, D.t₀)`, the collapsing map `φ : I^{k+8} → S^{k+8}` and a homotopy
`H : SourceModel (k+8) → D.T` on the annulus `S^{k+8} × [1,2]` which is `α` (read along `φ`) on the
collar `τ ≤ 3/2` and the basepoint at `τ = 2`.

The construction of `exists_sourceHomotopy` *descends* the cube homotopy along `φ` and then
reparametrises the time variable (`Work.PTGeometric.exists_stationary_reparam`); the resulting
statement records the values of the descended homotopy only on the collar and at the far end, so it
loses the fact — true by construction, and needed by the source construction of
`SOURCE_PLAN.md` §1.3 — that the homotopy is *constantly* `D.t₀` over the collapsed boundary
`φ (∂I^{k+8})`, i.e. over the whole ray `{basepoint} × [1,2]`.

This file proves that strengthening.  The only thing that has to be re-done is the time
reparametrisation: the descended homotopy `Hbar` of `Work.PTGeometric.exists_sphereHomotopy`
satisfies `Hbar (φ y, t) = H (t, y)` for **all** `t` (this is exactly its statement), hence is
constantly `D.t₀` over `φ 0`, and the reparametrisation
`τ ↦ min 1 (max 0 (4 (τ - 1) - 2))` reads it only at points of `[0,1]`, so the constancy survives
for every `τ ∈ [1,2]`.

## Main results

* `Work.PTGeometric.exists_sourceHomotopy_boundary`
-/

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open scoped Manifold ContDiff Topology unitInterval
open Function Set Topology Manifold Filter

namespace Work.PTGeometric

noncomputable section

open Work.ThomBordism
open Work.ThomBordism.PontryaginThom

/-- The time reparametrisation `x ↦ min 1 (max 0 (4x - 2))` of the real line: it is `0` for
`x ≤ 1/2` and `1` for `3/4 ≤ x`, and continuous in between.  It is the reparametrisation which makes
the descended homotopy stationary on the collar `[1, 3/2]` of the source and equal to its far end on
`[7/4, 2]`. -/
def ptRho (x : ℝ) : ℝ := min 1 (max 0 (4 * x - 2))

theorem continuous_ptRho : Continuous ptRho := by
  show Continuous fun x : ℝ => min 1 (max 0 (4 * x - 2))
  fun_prop

theorem ptRho_mem (x : ℝ) : ptRho x ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨le_min (by norm_num) (le_max_left _ _), min_le_left _ _⟩

theorem ptRho_eq_zero_of_le {x : ℝ} (hx : x ≤ 1 / 2) : ptRho x = 0 := by
  have hz : 4 * x - 2 ≤ 0 := by linarith
  show min 1 (max 0 (4 * x - 2)) = 0
  rw [max_eq_left hz, min_eq_right (by norm_num : (0 : ℝ) ≤ 1)]

theorem ptRho_eq_one_of_ge {x : ℝ} (hx : 3 / 4 ≤ x) : ptRho x = 1 := by
  have hz : (0 : ℝ) ≤ 4 * x - 2 := by linarith
  have h1 : (1 : ℝ) ≤ 4 * x - 2 := by linarith
  show min 1 (max 0 (4 * x - 2)) = 1
  rw [max_eq_right hz, min_eq_left h1]

/-- The reparametrisation `[1,2] → [0,1]` of the second coordinate of the source, `τ ↦ ptRho (τ-1)`;
it is `0` on the collar `τ ≤ 3/2` and `1` at the far end `τ = 2`. -/
def srcRho (τ : Set.Icc (1 : ℝ) 2) : Set.Icc (0 : ℝ) 1 :=
  ⟨ptRho ((τ : ℝ) - 1), ptRho_mem _⟩

theorem srcRho_coe (τ : Set.Icc (1 : ℝ) 2) :
    ((srcRho τ : Set.Icc (0 : ℝ) 1) : ℝ) = ptRho ((τ : ℝ) - 1) := rfl

theorem continuous_srcRho : Continuous srcRho :=
  (continuous_ptRho.comp (continuous_subtype_val.sub continuous_const)).subtype_mk
    (fun τ => ptRho_mem _)

theorem srcRho_eq_zero {τ : Set.Icc (1 : ℝ) 2} (hτ : (τ : ℝ) ≤ 3 / 2) : srcRho τ = 0 := by
  apply Subtype.ext
  rw [srcRho_coe]
  exact ptRho_eq_zero_of_le (by linarith)

theorem srcRho_eq_one : srcRho (⟨2, by norm_num⟩ : Set.Icc (1 : ℝ) 2) = 1 := by
  apply Subtype.ext
  rw [srcRho_coe]
  exact ptRho_eq_one_of_ge (by norm_num)

/-- **The source homotopy on the annulus, constant on the collapsed boundary.**  From a cube loop `α`
of trivial class in `π_{k+8}(D.T, D.t₀)` there are the collapsing quotient map
`φ : I^{k+8} → S^{k+8}` and a continuous `H : SourceModel (k+8) → D.T` which is `α` (read along
`φ`) on the whole collar `1 ≤ τ ≤ 3/2` of the annulus, the basepoint at `τ = 2`, and — the content of
this file — **constantly** the basepoint on the ray `φ (∂I^{k+8}) × [1,2]` over the collapsed
boundary of the cube. -/
theorem exists_sourceHomotopy_boundary {k : ℕ} (D : Work.ThomBordism.PontryaginThom.ThomTarget k) (α : GenLoop (Fin (k + 8)) D.T D.t₀) (hα : (Quotient.mk _ α : HomotopyGroup (Fin (k + 8)) D.T D.t₀) = (1 : HomotopyGroup (Fin (k + 8)) D.T D.t₀)) : ∃ (φ : C(Fin (k + 8) → Set.Icc (0 : ℝ) 1, Metric.sphere (0 : EuclideanSpace ℝ (Fin ((k + 8) + 1))) 1)) (H : C(Work.PTGeometric.SourceModel (k + 8), D.T)), (∀ (y : Fin (k + 8) → Set.Icc (0 : ℝ) 1) (τ : Set.Icc (1 : ℝ) 2), (τ : ℝ) ≤ 3 / 2 → H (φ y, τ) = α y) ∧ (∀ s : Metric.sphere (0 : EuclideanSpace ℝ (Fin ((k + 8) + 1))) 1, H (s, ⟨2, by norm_num⟩) = D.t₀) ∧ (∀ (y : Fin (k + 8) → Set.Icc (0 : ℝ) 1), y ∈ _root_.Cube.boundary (Fin (k + 8)) → ∀ τ : Set.Icc (1 : ℝ) 2, H (φ y, τ) = D.t₀) ∧ (∀ y ∈ _root_.Cube.boundary (Fin (k + 8)), φ y = φ 0) := by
  have hn : 1 ≤ k + 8 := by omega
  -- the based homotopy of `α` with the constant loop
  have hone : (Quotient.mk _ (GenLoop.const : GenLoop (Fin (k + 8)) D.T D.t₀)
      : HomotopyGroup (Fin (k + 8)) D.T D.t₀)
      = (1 : HomotopyGroup (Fin (k + 8)) D.T D.t₀) := HomotopyGroup.one_def.symm
  have hHom : GenLoop.Homotopic α (GenLoop.const : GenLoop (Fin (k + 8)) D.T D.t₀) :=
    Quotient.exact (hα.trans hone)
  obtain ⟨F⟩ := hHom
  -- the cube homotopy, constant on the lateral boundary
  have hcube : ∀ (t : Set.Icc (0 : ℝ) 1) (y : Fin (k + 8) → Set.Icc (0 : ℝ) 1),
      y ∈ Cube.boundary (Fin (k + 8)) → F.toHomotopy.toContinuousMap (t, y) = D.t₀ := by
    intro t y hy
    exact (F.prop' t y hy).trans (α.2 y hy)
  have hcube1 : ∀ y : Fin (k + 8) → Set.Icc (0 : ℝ) 1,
      F.toHomotopy.toContinuousMap (1, y) = D.t₀ := fun y => F.map_one_left y
  -- the collapse of the cube boundary to a point
  obtain ⟨φ, hφ, hφbd, hφfib⟩ := Work.Stems.exists_collapsingMap (k + 8) hn
  -- descend it to the sphere: `Hbar (φ y, t) = F (t, y)` for **all** `t`
  obtain ⟨Hbar, hHbar, hHbar1⟩ :=
    exists_sphereHomotopy hn φ hφ hφfib F.toHomotopy.toContinuousMap hcube hcube1
  -- a boundary point of the cube: over its image `Hbar` is constantly the basepoint
  have hmem0 : (0 : Fin (k + 8) → Set.Icc (0 : ℝ) 1) ∈ Cube.boundary (Fin (k + 8)) :=
    ⟨⟨0, hn⟩, Or.inl rfl⟩
  have hbase : ∀ t : Set.Icc (0 : ℝ) 1, Hbar (φ 0, t) = D.t₀ := fun t =>
    (hHbar 0 t).trans (hcube t 0 hmem0)
  -- transport to the annulus `S^{k+8} × [1,2]` by the time reparametrisation
  refine ⟨φ, ⟨fun x => Hbar (x.1, srcRho x.2), Hbar.continuous.comp
    (Continuous.prodMk continuous_fst (continuous_srcRho.comp continuous_snd))⟩, ?_, ?_, ?_, hφbd⟩
  · intro y τ hτ
    show Hbar (φ y, srcRho τ) = α y
    rw [srcRho_eq_zero hτ, hHbar y 0]
    exact F.map_zero_left y
  · intro s
    show Hbar (s, srcRho ⟨2, by norm_num⟩) = D.t₀
    rw [srcRho_eq_one, hHbar1]
  · intro y hy τ
    show Hbar (φ y, srcRho τ) = D.t₀
    rw [hφbd y hy]
    exact hbase (srcRho τ)

end

end Work.PTGeometric
