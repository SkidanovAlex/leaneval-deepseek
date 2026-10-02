import Mathlib
import Submission.Work.FatouCoord.Exist.exists_eq_of_deriv_close

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FlowerGlue2

/-- Banach fixed-point (contraction mapping) argument, in the "shifted" form needed for
gluing flowers: if the perturbation `x ↦ V x - x` is `κ`-Lipschitz on the closed ball of
radius `ρ` around `v₀` with `κ < 1`, and `V v₀` is within `(1 - κ) ρ` of `w`, then `w` has a
preimage under `V` inside that closed ball. -/
theorem exists_preimage_of_lipschitz {V : ℂ → ℂ} {v₀ w : ℂ} {ρ κ : ℝ} (hρ : 0 < ρ)
    (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
    (hlip : ∀ x y : ℂ, dist x v₀ ≤ ρ → dist y v₀ ≤ ρ →
      ‖(V x - x) - (V y - y)‖ ≤ κ * ‖x - y‖)
    (hclose : ‖V v₀ - w‖ ≤ (1 - κ) * ρ) : ∃ v : ℂ, dist v v₀ ≤ ρ ∧ V v = w := by
  -- The closed ball of radius `ρ` around `v₀`, and the auxilliary map `g z = w - (V z - z)`.
  set s : Set ℂ := Metric.closedBall v₀ ρ with hs
  let g : ℂ → ℂ := fun z => w - (V z - z)
  have hmem : ∀ z : ℂ, z ∈ s ↔ dist z v₀ ≤ ρ := by
    intro z; rw [hs, Metric.mem_closedBall]
  have hv0 : v₀ ∈ s := by rw [hmem]; simpa using hρ.le
  -- `g` is `κ`-Lipschitz on the ball: it is `V x - x` up to reflection.
  have hg_lip : ∀ x y : ℂ, x ∈ s → y ∈ s → dist (g x) (g y) ≤ κ * dist x y := by
    intro x y hx hy
    have hx' : dist x v₀ ≤ ρ := (hmem x).mp hx
    have hy' : dist y v₀ ≤ ρ := (hmem y).mp hy
    have h := hlip x y hx' hy'
    have hsub : g x - g y = -((V x - x) - (V y - y)) := by
      simp only [g]; ring
    rw [dist_eq_norm, dist_eq_norm, hsub, norm_neg]
    exact h
  -- `g` maps the ball into itself.
  have hg_maps : Set.MapsTo g s s := by
    intro z hz
    rw [hmem] at hz ⊢
    have h1 : dist (g z) (g v₀) ≤ κ * dist z v₀ := hg_lip z v₀ hz hv0
    have h2 : ‖w - V v₀‖ ≤ (1 - κ) * ρ := by
      rw [norm_sub_rev]; exact hclose
    have hgv0 : dist (g v₀) v₀ = ‖w - V v₀‖ := by
      rw [dist_eq_norm]
      congr 1
      simp only [g]; ring
    calc dist (g z) v₀ ≤ dist (g z) (g v₀) + dist (g v₀) v₀ := dist_triangle _ _ _
      _ ≤ κ * ρ + (1 - κ) * ρ :=
            add_le_add (h1.trans (mul_le_mul_of_nonneg_left hz hκ0)) (hgv0.trans_le h2)
      _ = ρ := by ring
  -- Hence the restriction of `g` to the (complete) ball is a contraction.
  have hcont : ContractingWith ⟨κ, hκ0⟩ (Set.MapsTo.restrict g s s hg_maps) := by
    refine ⟨?_, LipschitzWith.of_dist_le_mul ?_⟩
    · exact_mod_cast hκ1
    · intro x y
      show dist (g x.1) (g y.1) ≤ (κ : ℝ) * dist x.1 y.1
      exact hg_lip x.1 y.1 x.2 y.2
  obtain ⟨y, hy_mem, hy_fix, _⟩ := hcont.exists_fixedPoint'
    (by rw [hs]; exact Metric.isClosed_closedBall.isComplete) hg_maps hv0 (edist_ne_top _ _)
  refine ⟨y, (hmem y).mp hy_mem, ?_⟩
  have hyfix : g y = y := hy_fix
  simp only [g] at hyfix
  have : V y = w := by linear_combination -hyfix
  exact this

end Work.FlowerGlue2
