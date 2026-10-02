import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedDyn

/-- **A far point with a unique preimage.**

Let `U ⊆ ℂ`, `f : ℂ → ℂ` be such that

* `f` maps `U` strictly outside the unit disc (`hmaps`);
* `f` is bounded on every bounded piece of `U` (`hbdd`);
* the complement of some disc is contained in `U` and `f` is injective there (`hR`);
* the preimage under `f` of every bounded set is bounded in `U` (`hgrow`).

Then `U` contains a point `z₀` whose only preimage in `U` is `z₀` itself.

**Proof.**  Let `R` be the radius of `hR`, `M` the bound of `hbdd` on `{z ∈ U | ‖z‖ ≤ R}`,
and `R'` the radius of `hgrow` for that `M`.  Take `z₀ ∈ U` far out, `‖z₀‖ ≥ max R (R' + 1)`:
then `R ≤ ‖z₀‖` so `z₀ ∈ U` and `f` is injective on the far region through `z₀`, while
`R' < ‖z₀‖` together with `hgrow` gives `M < ‖f z₀‖`.  Now if `z ∈ U` has `f z = f z₀`, then
`‖f z‖ > M`; were `‖z‖ ≤ R`, the bound `hbdd` would give `‖f z‖ ≤ M`, a contradiction.  So
`‖z‖ > R` as well, and injectivity of `f` on the far region yields `z = z₀`.  The converse
implication is trivial.

The argument uses only the boundedness/properness data `hbdd`, `hR`, `hgrow`; the coercivity
input `hmaps` is recorded at `z₀` (`f z₀ ≠ 0`) but the conclusion does not need it. -/
theorem exists_unique_preimage_of_far {U : Set ℂ} {f : ℂ → ℂ}
    (hmaps : ∀ z ∈ U, 1 < ‖f z‖)
    (hbdd : ∀ R : ℝ, ∃ M : ℝ, ∀ z ∈ U, ‖z‖ ≤ R → ‖f z‖ ≤ M)
    (hR : ∃ R : ℝ, {z : ℂ | R ≤ ‖z‖} ⊆ U ∧ Set.InjOn f {z : ℂ | R ≤ ‖z‖})
    (hgrow : ∀ M : ℝ, ∃ R' : ℝ, ∀ z ∈ U, ‖f z‖ ≤ M → ‖z‖ ≤ R') :
    ∃ z₀ ∈ U, ∀ z ∈ U, (f z = f z₀ ↔ z = z₀) := by
  obtain ⟨R, hRU, hinj⟩ := hR
  obtain ⟨M, hM⟩ := hbdd R
  obtain ⟨R', hR'⟩ := hgrow M
  -- a far-out point `z₀ = s` with `s ≥ max R (R' + 1) ≥ 0`
  set s : ℝ := max R (max (R' + 1) 0) with hs
  have hs0 : 0 ≤ s := by
    rw [hs]; exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hsR : R ≤ s := by rw [hs]; exact le_max_left _ _
  have hsR' : R' + 1 ≤ s := by
    rw [hs]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  set z₀ : ℂ := (s : ℂ) with hz₀
  have hznorm : ‖z₀‖ = s := by
    rw [hz₀]; simp [abs_of_nonneg hs0]
  have hz₀geR : R ≤ ‖z₀‖ := le_trans hsR hznorm.ge
  have hz₀U : z₀ ∈ U := hRU hz₀geR
  have hz₀gtR' : R' < ‖z₀‖ := by rw [hznorm]; linarith
  -- `hmaps` is not needed for the conclusion; record that it holds at `z₀` anyway
  have hfz₀pos : 0 < ‖f z₀‖ := lt_trans one_pos (hmaps z₀ hz₀U)
  -- `f z₀` is outside the ball of radius `M`
  have hfz₀ : M < ‖f z₀‖ := by
    by_contra hcon
    push Not at hcon
    have := hR' z₀ hz₀U hcon
    linarith
  refine ⟨z₀, hz₀U, ?_⟩
  intro z hz
  constructor
  · intro hfz
    -- `z` cannot be in the near region `{‖z‖ ≤ R}`
    have hzfar : R ≤ ‖z‖ := by
      by_contra hcon
      have hb := hM z hz (le_of_lt (not_le.mp hcon))
      rw [hfz] at hb
      linarith
    exact hinj hzfar hz₀geR hfz
  · intro h
    rw [h]

end Work.SeedDyn
