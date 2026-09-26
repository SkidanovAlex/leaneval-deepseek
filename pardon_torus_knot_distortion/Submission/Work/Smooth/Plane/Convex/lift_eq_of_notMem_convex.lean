import Mathlib
import Submission.Work.Smooth.Plane.Jordan
import Submission.Work.CoreTopology.All

namespace Work.Smooth.Plane.Convex

open scoped unitInterval
open Work.CoreTopology

/-- **The winding (degree) of a loop lying in a convex set around a point outside it is zero.**

Let `D ⊆ ℂ` be convex, `x ∉ D`, and let `c : ℝ → ℂ` be a continuous `2π`-periodic loop whose trace
lies in `D`.  Let `Λ : ℝ → ℝ` be a continuous lift of the *normalised* loop
`t ↦ (c t - x) / ‖c t - x‖` to the universal cover of the unit circle, i.e.
`Circle.exp (Λ t) = (c t - x)/‖c t - x‖` for all `t`.  Then `Λ (2π) = Λ 0`: the loop winds zero
times around `x`.

This is the winding-number/degree formulation of the geometric fact that a convex set is simply
connected, and it is the statement the planar chapter's item 1 would be proved from by the covering
space route (the elementary route — the straight-line homotopy
`Work.Smooth.Plane.nullHomotopicAvoiding_of_convex` — is what the chapter actually uses).

Proof sketch (a homotopy-of-loops version of `Work.CoreTopology.circle_lift_eq_of_extends_disk`,
which is `Work.CoreTopology`'s monodromy statement for the covering `Circle.exp`).  Since
`hmem` and `hx` give `c t ≠ x` for all `t`, the normalised loop
`g u := (c (2π u) - x)/‖c (2π u) - x‖` is a well defined continuous loop in `Circle`, based at
`g 0 = g 1` (by `hper`), and `Λ` restricted to the parameter range gives the lift of `g` starting
at `Λ 0`.  By convexity, the straight-line homotopy
`K (s, u) := (1 - s) • c (2π u) + s • c 0` takes values in `D`, hence never equals `x`, and
`K (s, 0) = c 0 = K (s, 1)` for all `s` (using `c 0 = c (2π)`), so normalising gives a homotopy of
loops *relative to the endpoints* from `g` to the constant loop at `g 0`.  Applying
`IsCoveringMap.liftPath_apply_one_eq_of_homotopicRel` for the covering map
`Circle.isCoveringMap_exp`, with the two lifts of the two ends of the homotopy, gives
`Λ (2π) = Λ 0`.  (Equivalently one may build the extension over the disc used in
`Work.CoreTopology.circle_lift_eq_of_extends_disk`.) -/
theorem lift_eq_of_notMem_convex {D : Set ℂ} (hD : Convex ℝ D) {x : ℂ} (hx : x ∉ D)
    {c : ℝ → ℂ} (hc : Continuous c) (hper : ∀ t : ℝ, c (t + 2 * Real.pi) = c t)
    (hmem : ∀ t : ℝ, c t ∈ D) {Λ : ℝ → ℝ} (hΛ : Continuous Λ)
    (hlift : ∀ t : ℝ, Circle.exp (Λ t) = (c t - x) / ‖c t - x‖) :
    Λ (2 * Real.pi) = Λ 0 := by
  have hne : ∀ t : ℝ, c t - x ≠ 0 :=
    fun t => sub_ne_zero.mpr (fun h => hx (h ▸ hmem t))
  have h2pi : c (2 * Real.pi) = c 0 := by simpa using hper 0
  -- **The straight-line homotopy**, normalised: it never hits `x` because it stays in `D`.
  have hmem' : ∀ p : I × I,
      (1 - (p.1 : ℝ)) • c (2 * Real.pi * (p.2 : ℝ)) + (p.1 : ℝ) • c 0 ∈ D := by
    intro p
    refine hD (hmem _) (hmem 0) ?_ ?_ ?_
    · exact sub_nonneg.mpr p.1.2.2
    · exact p.1.2.1
    · ring
  have hne' : ∀ p : I × I,
      (1 - (p.1 : ℝ)) • c (2 * Real.pi * (p.2 : ℝ)) + (p.1 : ℝ) • c 0 - x ≠ 0 :=
    fun p => sub_ne_zero.mpr (fun h => hx (h ▸ hmem' p))
  -- The normalised loop `g`, the constant loop at `g 0`, and the homotopy of loops.
  let γ₀ : C(I, Circle) :=
    ⟨fun s : I => normCircle (c (2 * Real.pi * (s : ℝ)) - x) (hne _),
      continuous_normCircle _ (by fun_prop) fun s => hne _⟩
  let γ₁ : C(I, Circle) := ContinuousMap.const I (Circle.exp (Λ 0))
  let H : C(I × I, Circle) :=
    ⟨fun p : I × I =>
        normCircle ((1 - (p.1 : ℝ)) • c (2 * Real.pi * (p.2 : ℝ)) + (p.1 : ℝ) • c 0 - x)
          (hne' p),
      continuous_normCircle _ (by fun_prop) fun p => hne' p⟩
  -- The lift `s ↦ Λ (2π s)` of `γ₀` starting at `Λ 0`.
  let Γ : C(I, ℝ) := ⟨fun s : I => Λ (2 * Real.pi * (s : ℝ)), hΛ.comp (by fun_prop)⟩
  -- The homotopy starts at `γ₀` ...
  have hH0 : ∀ s : I, H (0, s) = γ₀ s := by
    intro s
    show normCircle ((1 - ((0 : I) : ℝ)) • c (2 * Real.pi * (s : ℝ)) + ((0 : I) : ℝ) • c 0 - x)
        (hne' (0, s)) = normCircle (c (2 * Real.pi * (s : ℝ)) - x) (hne _)
    apply Subtype.ext
    rw [normCircle_coe, normCircle_coe]
    simp
  -- ... and ends at the constant loop at `g 0` (the eventual value of `c` is `c 0`).
  have hH1 : ∀ s : I, H (1, s) = γ₁ s := by
    intro s
    show normCircle ((1 - ((1 : I) : ℝ)) • c (2 * Real.pi * (s : ℝ)) + ((1 : I) : ℝ) • c 0 - x)
        (hne' (1, s)) = Circle.exp (Λ 0)
    apply Subtype.ext
    rw [normCircle_coe]
    simpa using (hlift 0).symm
  -- The homotopy is constant, at `γ₀`, on the endpoints `{0, 1}` of the source interval:
  -- for `y = 0` the combination is `c 0`, and for `y = 1` it is `c (2π) = c 0` by periodicity.
  have hprop : ∀ t : I, ∀ y ∈ ({0, 1} : Set I), H (t, y) = γ₀ y := by
    intro t y hy
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · show normCircle ((1 - (t : ℝ)) • c (2 * Real.pi * ((0 : I) : ℝ)) + (t : ℝ) • c 0 - x)
          (hne' (t, 0)) = normCircle (c (2 * Real.pi * ((0 : I) : ℝ)) - x) (hne _)
      apply Subtype.ext
      rw [normCircle_coe, normCircle_coe]
      have h0 : 2 * Real.pi * ((0 : I) : ℝ) = 0 := by simp
      rw [h0]
      rw [← add_smul, sub_add_cancel, one_smul]
    · show normCircle ((1 - (t : ℝ)) • c (2 * Real.pi * ((1 : I) : ℝ)) + (t : ℝ) • c 0 - x)
          (hne' (t, 1)) = normCircle (c (2 * Real.pi * ((1 : I) : ℝ)) - x) (hne _)
      apply Subtype.ext
      rw [normCircle_coe, normCircle_coe]
      have h1 : 2 * Real.pi * ((1 : I) : ℝ) = 2 * Real.pi := by simp
      rw [h1, h2pi]
      rw [← add_smul, sub_add_cancel, one_smul]
  have hrel : γ₀.HomotopicRel γ₁ {0, 1} :=
    ⟨{ toContinuousMap := H
       map_zero_left := hH0
       map_one_left := hH1
       prop' := hprop }⟩
  -- Both loops start at `Circle.exp (Λ 0)`, the base point of the monodromy argument.
  have hγ₀0 : γ₀ 0 = Circle.exp (Λ 0) := by
    show normCircle (c (2 * Real.pi * ((0 : I) : ℝ)) - x) (hne _) = Circle.exp (Λ 0)
    apply Subtype.ext
    rw [normCircle_coe]
    simpa using (hlift 0).symm
  have hγ₁0 : γ₁ 0 = Circle.exp (Λ 0) := rfl
  have key := IsCoveringMap.liftPath_apply_one_eq_of_homotopicRel
    Circle.isCoveringMap_exp hrel (Λ 0) hγ₀0 hγ₁0
  -- The lift of `γ₀` starting at `Λ 0` is `s ↦ Λ (2π s)`: ...
  have hA : Γ = Circle.isCoveringMap_exp.liftPath γ₀ (Λ 0) hγ₀0 := by
    rw [IsCoveringMap.eq_liftPath_iff']
    refine ⟨?_, ?_⟩
    · funext s
      show Circle.exp (Λ (2 * Real.pi * (s : ℝ))) = γ₀ s
      show Circle.exp (Λ (2 * Real.pi * (s : ℝ)))
        = normCircle (c (2 * Real.pi * (s : ℝ)) - x) (hne _)
      apply Subtype.ext
      rw [normCircle_coe]
      exact hlift (2 * Real.pi * (s : ℝ))
    · show (fun s => Λ (2 * Real.pi * (s : ℝ))) 0 = Λ 0
      simp
  -- ... and the lift of the constant loop is the constant path at `Λ 0`.
  have hB : (ContinuousMap.const I (Λ 0) : C(I, ℝ)) =
      Circle.isCoveringMap_exp.liftPath γ₁ (Λ 0) hγ₁0 := by
    rw [IsCoveringMap.eq_liftPath_iff']
    refine ⟨?_, ?_⟩
    · ext s
      rfl
    · simp
  have hB1 := congrArg (fun F : C(I, ℝ) => F 1) hB
  simp only [ContinuousMap.const_apply] at hB1
  have h1 : Λ (2 * Real.pi) = (Circle.isCoveringMap_exp.liftPath γ₀ (Λ 0) hγ₀0) 1 := by
    rw [← congrArg (fun F : C(I, ℝ) => F 1) hA]
    show Λ (2 * Real.pi) = Λ (2 * Real.pi * ((1 : I) : ℝ))
    simp
  exact h1.trans (key.trans hB1.symm)

end Work.Smooth.Plane.Convex
