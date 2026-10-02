import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# A continuous logarithm of a path in `ℂ \ {0}`

We prove that a continuous map `q : ℝ → ℂ` which is nowhere zero on `[0, ∞)`
admits a continuous logarithm on `[0, ∞)`.

The argument is the standard one: `Complex.exp` is a covering map on `{0}ᶜ`
(`Complex.isCoveringMapOn_exp`) and `[0, ∞)` is convex, hence contractible, hence
simply connected and locally path connected; so the lifting criterion for covering
maps (`IsCoveringMapOn.existsUnique_continuousMap_lifts`) applies.

This is the same argument as `Complex.exists_continuousOn_eqOn_exp_comp`, but the
domain `[0, ∞)` is not open, so we run the lifting argument directly.
-/

namespace Work.LandLeaves.Snail

/-- A continuous, nowhere zero function on `[0, ∞)` has a continuous logarithm. -/
theorem exists_continuous_log_of_path {q : ℝ → ℂ}
    (hq : ContinuousOn q (Set.Ici 0)) (hqne : ∀ t ∈ Set.Ici (0 : ℝ), q t ≠ 0) :
    ∃ L : ℝ → ℂ, ContinuousOn L (Set.Ici 0) ∧ ∀ t ∈ Set.Ici (0 : ℝ), Complex.exp (L t) = q t := by
  classical
  have hU₀ : (0 : ℂ) ∉ q '' Set.Ici (0 : ℝ) := by
    rintro ⟨t, ht, hqt⟩
    exact hqne t ht hqt
  -- `[0, ∞)` is convex, hence contractible, hence simply connected and locally path connected.
  have : ContractibleSpace (Set.Ici (0 : ℝ)) :=
    (convex_Ici 0).contractibleSpace Set.nonempty_Ici
  have : SimplyConnectedSpace (Set.Ici (0 : ℝ)) := SimplyConnectedSpace.ofContractible _
  have : LocallyPathConnectedSpace (Set.Ici (0 : ℝ)) :=
    (convex_Ici 0).locallyPathConnectedSpace
  -- Choose a base point `x₀ ∈ [0, ∞)`.
  obtain ⟨x₀, hx₀U⟩ : (Set.Ici (0 : ℝ)).Nonempty := Set.nonempty_Ici
  have hx₀ : q x₀ ≠ 0 := ne_of_mem_of_not_mem (Set.mem_image_of_mem q hx₀U) hU₀
  lift x₀ to Set.Ici (0 : ℝ) using hx₀U
  -- Lift the map `q : [0, ∞) → ℂ \ {0}` through the covering map `Complex.exp`.
  rcases IsCoveringMapOn.existsUnique_continuousMap_lifts Complex.isCoveringMapOn_exp
      (f := ⟨(Set.Ici (0 : ℝ)).domRestrict q, continuousOn_iff_continuous_domRestrict.mp hq⟩)
      (a₀ := x₀) (e₀ := Complex.log (q x₀)) (Complex.exp_log hx₀)
      (fun a => by simpa using hqne a.1 a.2) with ⟨F, ⟨hF0, hF⟩, -⟩
  -- Extend `F` by `0` off `[0, ∞)`.
  refine ⟨fun t => if ht : t ∈ Set.Ici (0 : ℝ) then F ⟨t, ht⟩ else 0, ?_, ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    have h_eq : (Set.Ici (0 : ℝ)).domRestrict
        (fun t => if ht : t ∈ Set.Ici (0 : ℝ) then F ⟨t, ht⟩ else 0) = ⇑F := by
      ext z
      rw [Set.domRestrict_apply]
      simp
      try rfl
    rw [h_eq]
    exact F.continuous
  · intro t ht
    have hFt := congr_fun hF ⟨t, ht⟩
    simpa [Set.domRestrict_apply, ht] using hFt

end Work.LandLeaves.Snail
