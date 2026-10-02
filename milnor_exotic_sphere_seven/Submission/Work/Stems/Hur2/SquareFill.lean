import Submission.Work.Stems.Hur2.Loop

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Filling a loop inside the square

The three paths `γ₀ : x₀ → a`, `e : a → b`, `γ₁ : x₀ → b` form the loop `γ₀ · e · γ₁⁻¹` in the
quarter parametrisation of the square's boundary.  Since `X` is simply connected that loop is
null-homotopic, and the null-homotopy descends along the quotient map `coneMap` to a map
`K : I² → X` with `K (bd t) = L t` on the boundary.
-/

open scoped unitInterval Topology

namespace Work.Stems.Hur2

open Work.Stems.Cubical

noncomputable section

/-- **The square filling the loop `γ₀ · e · γ₁⁻¹`.** -/
theorem exists_square_of_loop {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X] (x₀ : X)
    (γ₀ e γ₁ : C(unitInterval, X)) (hγ₀ : γ₀ 0 = x₀) (he₀ : e 0 = γ₀ 1) (he₁ : e 1 = γ₁ 1)
    (hγ₁ : γ₁ 0 = x₀) :
    ∃ K : C(IC 2, X), ∀ t : unitInterval,
      K (bd t) = loopPath
        { toFun := ⇑γ₀, continuous_toFun := γ₀.continuous, source' := hγ₀, target' := rfl }
        { toFun := ⇑e, continuous_toFun := e.continuous, source' := he₀, target' := he₁ }
        { toFun := ⇑γ₁, continuous_toFun := γ₁.continuous, source' := hγ₁, target' := rfl }
        t := by
  let p₀ : Path x₀ (γ₀ 1) :=
    { toFun := ⇑γ₀, continuous_toFun := γ₀.continuous, source' := hγ₀, target' := rfl }
  let pe : Path (γ₀ 1) (γ₁ 1) :=
    { toFun := ⇑e, continuous_toFun := e.continuous, source' := he₀, target' := he₁ }
  let p₁ : Path x₀ (γ₁ 1) :=
    { toFun := ⇑γ₁, continuous_toFun := γ₁.continuous, source' := hγ₁, target' := rfl }
  let L : Path x₀ x₀ := loopPath p₀ pe p₁
  obtain ⟨H⟩ := SimplyConnectedSpace.paths_homotopic L (Path.refl x₀)
  have hwrap : ∀ s : unitInterval,
      H.toHomotopy.toContinuousMap (s, 0) = H.toHomotopy.toContinuousMap (s, 1) := by
    intro s
    show H (s, 0) = H (s, 1)
    simp
  have hcentre : ∀ t : unitInterval,
      H.toHomotopy.toContinuousMap (1, t) = H.toHomotopy.toContinuousMap (1, 0) := by
    intro t
    show H (1, t) = H (1, 0)
    simp [ContinuousMap.Homotopy.map_one_left]
  obtain ⟨K, hK⟩ := exists_lift_coneMap H.toHomotopy.toContinuousMap hwrap hcentre
  refine ⟨K, fun t => ?_⟩
  have h0 : coneMap ((fun _ : Fin 1 => (0 : unitInterval)), (fun _ : Fin 1 => t)) = bd t := by
    funext j
    fin_cases j <;> apply Subtype.ext <;> simp [coneMap, coneCoord] <;> ring
  rw [← h0, hK]
  show H (0, t) = L t
  simpa using H.toHomotopy.map_zero_left t

end

end Work.Stems.Hur2
