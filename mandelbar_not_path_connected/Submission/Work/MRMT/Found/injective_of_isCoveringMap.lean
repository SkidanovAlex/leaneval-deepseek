import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Found

/-- A covering map `F : ℂ → ℂ` is injective (the total space `ℂ` is connected and the base `ℂ` is
simply connected, so the covering is trivial).

Proof sketch.  Lift the *identity* of the base.  Let `a₀ := F a` and `e₀ := a`
(so `F e₀ = a₀` holds by rfl).  Since `SimplyConnectedSpace ℂ` and `LocallyPathConnectedSpace ℂ`
are instances, `IsCoveringMapOn.existsUnique_continuousMap_lifts`
(`hcov.isCoveringMapOn`, applied to the identity map `C(ℂ,ℂ)`, with `∀ x, x ∈ Set.univ`) gives
`s : C(ℂ, ℂ)` with `s (F a) = a` and `F ∘ s = id`.

Now apply `IsCoveringMap.eq_of_comp_eq` (`cov := hcov`, domain `ℂ`, which is preconnected) to the
two maps `fun z => s (F z)` and `id`:
* their compositions with `F` agree because `F (s (F z)) = F z` (from `F ∘ s = id`);
* they agree at the point `a` because `s (F a) = a`.
Hence `s ∘ F = id`, and if `F a = F b` then `b = s (F b) = s (F a) = a`. -/
theorem injective_of_isCoveringMap {F : ℂ → ℂ} (hcov : IsCoveringMap F) :
    Function.Injective F := by
  intro a b hab
  -- Lift the identity of the base `ℂ` through the covering `F`, sending `F a` back to `a`.
  obtain ⟨s, ⟨hs0, hscomp⟩, -⟩ :=
    hcov.isCoveringMapOn.existsUnique_continuousMap_lifts (ContinuousMap.id ℂ)
      (a₀ := F a) (e₀ := a) rfl (fun _ => Set.mem_univ _)
  -- `hs0 : s (F a) = a` and `hscomp : F ∘ s = id`.
  -- Uniqueness of lifts along the preconnected space `ℂ` forces `s ∘ F = id`.
  have hkey : (fun z => s (F z)) = id := by
    refine hcov.eq_of_comp_eq (s.continuous.comp hcov.continuous) continuous_id ?_ a ?_
    · funext z
      have h := congr_fun hscomp (F z)
      simpa [ContinuousMap.coe_comp, Function.comp_def] using h
    · simpa using hs0
  have h1 : s (F b) = b := by simpa using congr_fun hkey b
  rw [← hab] at h1
  rw [← hs0]
  exact h1

end Work.MRMT.Found
