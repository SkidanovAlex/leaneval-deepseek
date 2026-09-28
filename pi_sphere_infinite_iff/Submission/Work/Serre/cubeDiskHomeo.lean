import Mathlib
import Submission.Work.Serre.cubePairDefs

set_option synthInstance.maxHeartbeats 400000

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

namespace Work.Serre

noncomputable section

open Metric Set

/-!
# The cube `I^n` is homeomorphic to the closed unit disk `D^n`

This file proves `Work.Serre.cubeDiskHomeo`: the cube `I^n = [0,1]^n` is homeomorphic to the
closed unit ball of `ℝ^n`, with the boundary of the cube corresponding to the unit sphere.

The route is the "gauge rescale" homeomorphism of `Mathlib.Analysis.Convex.GaugeRescale`
(`exists_homeomorph_image_interior_closure_frontier_eq_unitBall`), applied to the cube
`[0,1]^n ⊆ ℝ^n` (which is convex, closed, bounded, with nonempty interior): it produces a
homeomorphism `h` of the ambient space carrying the cube onto the closed unit ball, its
interior onto the open ball and its **frontier onto the unit sphere**.  The frontier of the
cube is exactly the set of points with some coordinate equal to `0` or `1`, which is the
boundary of the cube.
-/

/-- The Euclidean space `ℝ^n` in which the closed unit disk lives. -/
abbrev DiskVec (n : ℕ) : Type := EuclideanSpace ℝ (Fin n)

/-- The cube `[0,1]^n`, as a subset of `ℝ^n` with the Euclidean metric. -/
def cubeSet (n : ℕ) : Set (DiskVec n) := {y | ∀ i, y.ofLp i ∈ Set.Icc (0 : ℝ) 1}

/-- The open cube `(0,1)^n`. -/
def openCubeSet (n : ℕ) : Set (DiskVec n) := {y | ∀ i, y.ofLp i ∈ Set.Ioo (0 : ℝ) 1}

theorem mem_cubeSet {n : ℕ} {y : DiskVec n} :
    y ∈ cubeSet n ↔ ∀ i, y.ofLp i ∈ Set.Icc (0 : ℝ) 1 := Iff.rfl

@[simp] theorem piLpHomeomorph_apply (n : ℕ) (y : DiskVec n) :
    (PiLp.homeomorph 2 (fun _ : Fin n => ℝ)) y = y.ofLp := rfl

theorem cubeSet_eq_preimage (n : ℕ) :
    cubeSet n = (PiLp.homeomorph 2 (fun _ : Fin n => ℝ)) ⁻¹'
      Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1) := by
  ext y; constructor
  · intro hy i _; exact hy i
  · intro hy i; exact hy i (Set.mem_univ i)

theorem isClosed_cubeSet (n : ℕ) : IsClosed (cubeSet n) := by
  rw [cubeSet_eq_preimage]
  exact (isClosed_set_pi (fun i _ => isClosed_Icc)).preimage
    (PiLp.homeomorph 2 (fun _ : Fin n => ℝ)).continuous

theorem convex_cubeSet (n : ℕ) : Convex ℝ (cubeSet n) := by
  have h : Convex ℝ (Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1)) :=
    convex_pi (fun i _ => convex_Icc 0 1)
  have h2 : Convex ℝ ((WithLp.linearEquiv 2 ℝ (Fin n → ℝ)) ⁻¹'
      Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1)) :=
    h.linear_preimage (WithLp.linearEquiv 2 ℝ (Fin n → ℝ) : DiskVec n →ₗ[ℝ] (Fin n → ℝ))
  have heq : (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)) ⁻¹'
      Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1) = cubeSet n := by
    ext y; constructor
    · intro hy i; exact hy i (Set.mem_univ i)
    · intro hy i _; exact hy i
  rwa [heq] at h2

/-- The coordinate map `I^n → ℝ^n`, sending the cube to `[0,1]^n`. -/
def cubeCoordFun (n : ℕ) : Work.Stems.Cubical.IC n → DiskVec n :=
  fun t => WithLp.toLp 2 (fun i => (t i : ℝ))

@[simp] theorem cubeCoordFun_ofLp (n : ℕ) (t : Work.Stems.Cubical.IC n) (i : Fin n) :
    (cubeCoordFun n t).ofLp i = (t i : ℝ) := rfl

theorem cubeCoordFun_mem (n : ℕ) (t : Work.Stems.Cubical.IC n) :
    cubeCoordFun n t ∈ cubeSet n := fun i => (t i).2

theorem continuous_cubeCoordFun (n : ℕ) : Continuous (cubeCoordFun n) :=
  (PiLp.homeomorph 2 (fun _ : Fin n => ℝ)).symm.continuous.comp
    (continuous_pi (fun i => continuous_subtype_val.comp (continuous_apply i)))

theorem cubeSet_eq_range (n : ℕ) : cubeSet n = Set.range (cubeCoordFun n) := by
  ext y; constructor
  · intro hy
    refine ⟨fun i => ⟨y.ofLp i, hy i⟩, ?_⟩
    apply (WithLp.ext_iff 2).mpr
    ext i
    rfl
  · rintro ⟨t, rfl⟩ i
    exact (t i).2

theorem isBounded_cubeSet (n : ℕ) : Bornology.IsBounded (cubeSet n) := by
  rw [cubeSet_eq_range]
  exact (isCompact_range (continuous_cubeCoordFun n)).isBounded

/-- The inverse of the coordinate map: an element of the cube gives a point of `I^n`. -/
def cubeInvFun (n : ℕ) : cubeSet n → Work.Stems.Cubical.IC n :=
  fun y i => ⟨(y : DiskVec n).ofLp i, (y.2 i)⟩

@[simp] theorem cubeInvFun_apply (n : ℕ) (y : cubeSet n) (i : Fin n) :
    ((cubeInvFun n y i : unitInterval) : ℝ) = (y : DiskVec n).ofLp i := rfl

theorem continuous_cubeInvFun (n : ℕ) : Continuous (cubeInvFun n) := by
  apply continuous_pi
  intro i
  change Continuous fun y : cubeSet n => (⟨(y : DiskVec n).ofLp i, (y.2 i)⟩ : unitInterval)
  exact Continuous.subtype_mk
    (((continuous_apply i).comp (PiLp.continuous_ofLp 2 (fun _ : Fin n => ℝ))).comp
      continuous_subtype_val)
    (fun y : cubeSet n => y.2 i)

/-- The cube `I^n` is homeomorphic to `[0,1]^n ⊆ ℝ^n`. -/
def cubeHomeo (n : ℕ) : Work.Stems.Cubical.IC n ≃ₜ cubeSet n where
  toFun t := ⟨cubeCoordFun n t, cubeCoordFun_mem n t⟩
  invFun := cubeInvFun n
  left_inv t := by
    funext i
    apply Subtype.ext
    rfl
  right_inv y := by
    apply Subtype.ext
    apply (WithLp.ext_iff 2).mpr
    ext i
    rfl
  continuous_toFun := Continuous.subtype_mk (continuous_cubeCoordFun n) fun t => cubeCoordFun_mem n t
  continuous_invFun := continuous_cubeInvFun n

@[simp] theorem cubeHomeo_apply_coe (n : ℕ) (t : Work.Stems.Cubical.IC n) :
    ((cubeHomeo n t : cubeSet n) : DiskVec n) = cubeCoordFun n t := rfl

/-! ### The interior and frontier of the cube -/

theorem interior_cubeSet (n : ℕ) : interior (cubeSet n) = openCubeSet n := by
  rw [cubeSet_eq_preimage, ← (PiLp.homeomorph 2 (fun _ : Fin n => ℝ)).preimage_interior,
    interior_pi_set Set.finite_univ]
  ext y; constructor
  · intro hy i
    have h := hy i (Set.mem_univ i)
    rw [interior_Icc] at h
    simpa [piLpHomeomorph_apply] using h
  · intro hy i _
    rw [interior_Icc]
    simpa [piLpHomeomorph_apply] using hy i

theorem nonempty_interior_cubeSet (n : ℕ) : (interior (cubeSet n)).Nonempty := by
  refine ⟨cubeCoordFun n (fun _ => ⟨1 / 2, by constructor <;> norm_num⟩), ?_⟩
  rw [interior_cubeSet, openCubeSet]
  intro i
  rw [cubeCoordFun_ofLp]
  exact ⟨by norm_num, by norm_num⟩

theorem frontier_cubeSet (n : ℕ) :
    frontier (cubeSet n) = {y : DiskVec n | (∀ i, y.ofLp i ∈ Set.Icc (0 : ℝ) 1) ∧
      ¬ (∀ i, y.ofLp i ∈ Set.Ioo (0 : ℝ) 1)} := by
  rw [(isClosed_cubeSet n).frontier_eq, interior_cubeSet n, openCubeSet]
  rfl

/-- The boundary of the cube `I^n`, expressed with the coordinates of `ℝ^n`. -/
theorem mem_boundary_iff_not_Ioo (n : ℕ) (x : Work.Stems.Cubical.IC n) :
    x ∈ Cube.boundary (Fin n) ↔ ¬ (∀ i, (x i : ℝ) ∈ Set.Ioo (0 : ℝ) 1) := by
  rw [Cube.boundary, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨i, hi | hi⟩ h
    · have h1 : (x i : ℝ) = 0 := by rw [hi]; rfl
      exact absurd (h i).1 (by rw [h1]; exact lt_irrefl 0)
    · have h1 : (x i : ℝ) = 1 := by rw [hi]; rfl
      exact absurd (h i).2 (by rw [h1]; exact lt_irrefl 1)
  · intro h
    by_contra hc
    apply h
    intro i
    have hI := (x i).2
    refine ⟨?_, ?_⟩
    · rcases lt_or_eq_of_le hI.1 with hlt | heq
      · exact hlt
      · exact absurd ⟨i, Or.inl (Subtype.ext heq.symm)⟩ hc
    · rcases lt_or_eq_of_le hI.2 with hlt | heq
      · exact hlt
      · exact absurd ⟨i, Or.inr (Subtype.ext heq)⟩ hc

theorem cubeCoordFun_mem_frontier_iff (n : ℕ) (x : Work.Stems.Cubical.IC n) :
    cubeCoordFun n x ∈ frontier (cubeSet n) ↔ x ∈ Cube.boundary (Fin n) := by
  rw [frontier_cubeSet, Set.mem_ofPred_eq, mem_boundary_iff_not_Ioo n x]
  constructor
  · rintro ⟨-, h2⟩; exact h2
  · intro h2; exact ⟨fun i => (x i).2, h2⟩

/-- If two subsets of a topological space are equal, they are homeomorphic. -/
def homeoOfSetEq {X : Type*} [TopologicalSpace X] {s t : Set X} (h : s = t) : s ≃ₜ t where
  toFun x := ⟨x.1, h ▸ x.2⟩
  invFun x := ⟨x.1, h.symm ▸ x.2⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  continuous_toFun := Continuous.subtype_mk continuous_subtype_val fun x => h ▸ x.2
  continuous_invFun := Continuous.subtype_mk continuous_subtype_val fun x => h.symm ▸ x.2

/-- **The cube `I^n` is homeomorphic to the closed unit disk `D^n`, with the boundary of the cube
corresponding to the boundary sphere.**  (The radial/gauge construction: `x ↦ (γ(x)/‖x‖) • x` for
`x ≠ 0`, where `γ` is the gauge function of the cube, with the evident inverse; the cube's boundary
`γ = 1` goes to the sphere `‖·‖ = 1`.) -/
theorem cubeDiskHomeo (n : ℕ) :
    ∃ e : Work.Stems.Cubical.IC n ≃ₜ
        ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1),
      (∀ x : Work.Stems.Cubical.IC n, x ∈ Cube.boundary (Fin n) ↔
        (e x : EuclideanSpace ℝ (Fin n)) ∈ Metric.sphere 0 1) := by
  obtain ⟨h, -, h_clo, h_fro⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall
      (E := DiskVec n) (s := cubeSet n) (convex_cubeSet n) (nonempty_interior_cubeSet n)
      (isBounded_cubeSet n)
  have h_clo' : h '' cubeSet n = Metric.closedBall (0 : DiskVec n) 1 := by
    rw [← (isClosed_cubeSet n).closure_eq]
    exact h_clo
  let e : Work.Stems.Cubical.IC n ≃ₜ ↥(Metric.closedBall (0 : DiskVec n) 1) :=
    (cubeHomeo n).trans ((Homeomorph.image h (cubeSet n)).trans (homeoOfSetEq h_clo'))
  refine ⟨e, ?_⟩
  intro x
  have hx : (e x : DiskVec n) = h (cubeCoordFun n x) := rfl
  have hsphere : h (cubeCoordFun n x) ∈ Metric.sphere (0 : DiskVec n) 1 ↔
      cubeCoordFun n x ∈ frontier (cubeSet n) := by
    rw [← h_fro, Set.mem_image]
    exact ⟨fun ⟨z, hz, hzy⟩ => by rwa [h.injective hzy] at hz,
      fun hx => ⟨_, hx, rfl⟩⟩
  rw [hx, hsphere, cubeCoordFun_mem_frontier_iff n x]

end

end Work.Serre
