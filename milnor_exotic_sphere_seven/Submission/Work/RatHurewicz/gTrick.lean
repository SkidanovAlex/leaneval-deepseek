import Mathlib
import Submission.Work.RatHurewicz.Triad.kTrick

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The `G`-trick (the mirror of tom Dieck 6.9.1)

The `K`-trick (`Triad/kTrick.lean`) pushes towards `0`; the `G`-trick pushes towards `1`. It is the
`K`-trick for the map precomposed with the reflection `ρ u i = 1 - u i` of the cube, which preserves
the boundary and converts `1/2 < v` into `v < 1/2`.
-/

open scoped Topology unitInterval

namespace Work.RatHurewicz

noncomputable section

/-- The reflection of the cube, `u i ↦ 1 - u i`. -/
def cubeReflect {d : ℕ} (u : ICube d) : ICube d :=
  fun i => ⟨1 - (u i : ℝ), by
    have h := (u i).2
    exact ⟨by linarith [h.2], by linarith [h.1]⟩⟩

@[simp] theorem cubeReflect_apply {d : ℕ} (u : ICube d) (i : Fin d) :
    ((cubeReflect u i : unitInterval) : ℝ) = 1 - (u i : ℝ) := rfl

theorem cubeReflect_involutive {d : ℕ} : Function.Involutive (@cubeReflect d) := by
  intro u
  funext i
  apply Subtype.ext
  simp only [cubeReflect_apply]
  ring

theorem continuous_cubeReflect {d : ℕ} : Continuous (@cubeReflect d) := by
  refine continuous_pi fun i => Continuous.subtype_mk ?_ _
  exact continuous_const.sub (continuous_subtype_val.comp (continuous_apply i))

theorem cubeReflect_mem_boundary {d : ℕ} {u : ICube d} (hu : u ∈ Cube.boundary (Fin d)) :
    cubeReflect u ∈ Cube.boundary (Fin d) := by
  obtain ⟨i, hi⟩ := hu
  refine ⟨i, ?_⟩
  rcases hi with h | h
  · right
    apply Subtype.ext
    simp [cubeReflect_apply, h]
  · left
    apply Subtype.ext
    simp [cubeReflect_apply, h]

/-- **The `G`-trick**: the mirror of `kTrick`, pushing towards `1`. -/
theorem gTrick {Y : Type} [TopologicalSpace Y] {d : ℕ} (P : ℕ) (hP : P ≤ d)
    (f : C(ICube d, Y)) (A : Set Y)
    (h : ∀ u : ICube d, u ∈ Cube.boundary (Fin d) → f u ∈ A →
      ∃ L : Finset (Fin d), P ≤ L.card ∧ ∀ i ∈ L, 1 / 2 < (u i : ℝ)) :
    ∃ G : C(ICube d × I, Y),
      (∀ u, G (u, 0) = f u) ∧
      (∀ (u : ICube d) (hu : u ∈ Cube.boundary (Fin d)) (t : I), G (u, t) = f u) ∧
      (∀ u, G (u, 1) ∈ A →
        ∃ L : Finset (Fin d), P ≤ L.card ∧ ∀ i ∈ L, 1 / 2 < (u i : ℝ)) := by
  classical
  set ρ : C(ICube d, ICube d) := ⟨cubeReflect, continuous_cubeReflect⟩ with hρ
  have hρval : ∀ u, ρ u = cubeReflect u := fun u => rfl
  have h' : ∀ u : ICube d, u ∈ Cube.boundary (Fin d) → (f.comp ρ) u ∈ A →
      ∃ L : Finset (Fin d), P ≤ L.card ∧ ∀ i ∈ L, (u i : ℝ) < 1 / 2 := by
    intro u hu hA
    have hA' : f (cubeReflect u) ∈ A := by
      simpa [hρval, ContinuousMap.comp_apply] using hA
    obtain ⟨L, hL, hLi⟩ := h (cubeReflect u) (cubeReflect_mem_boundary hu) hA'
    refine ⟨L, hL, fun i hi => ?_⟩
    have := hLi i hi
    rw [cubeReflect_apply] at this
    linarith
  obtain ⟨G', hG'0, hG'bd, hG'1⟩ :=
    Work.RatHurewicz.Triad.kTrick P hP (f.comp ρ) A h'
  refine ⟨⟨fun p => G' (cubeReflect p.1, p.2), ?_⟩, ?_, ?_, ?_⟩
  · exact G'.continuous.comp
      (Continuous.prodMk (continuous_cubeReflect.comp continuous_fst) continuous_snd)
  · intro u
    show G' (cubeReflect u, (0 : I)) = f u
    rw [hG'0, ContinuousMap.comp_apply, hρval (cubeReflect u), cubeReflect_involutive u]
  · intro u hu t
    show G' (cubeReflect u, t) = f u
    rw [hG'bd (cubeReflect u) (cubeReflect_mem_boundary hu) t,
      ContinuousMap.comp_apply, hρval (cubeReflect u), cubeReflect_involutive u]
  · intro u hA
    have hA' : G' (cubeReflect u, (1 : I)) ∈ A := by
      simpa using hA
    obtain ⟨L, hL, hLi⟩ := hG'1 (cubeReflect u) hA'
    refine ⟨L, hL, fun i hi => ?_⟩
    have := hLi i hi
    rw [cubeReflect_apply] at this
    linarith

end

end Work.RatHurewicz
