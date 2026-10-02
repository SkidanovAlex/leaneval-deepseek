import Mathlib
import Submission.Work.NAKANE.Defs
import Submission.Work.NAKANE.GreenJoint.continuous_jointGreen

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.NAKANE.GreenJoint

/-- **PARIMPL (I2), abstract form.**  If the Green function is bounded below by a positive constant
`s` on a compact set `K` at the parameter `c₀`, then for all parameters `c` sufficiently close to
`c₀` the Green function is positive on a whole neighbourhood of `K`.

This is the general form of the statement PARIMPL needs (`NOTES_LEAD_mandelbar_residuals.md` §1.4,
(I2)): with `K = Ψ(closedBall (x* - j₀) r₀)` compact and `G_{c₀} ≥ s₀ > 0` on it, a point `y` close
to `K` satisfies `G_c y > 0` for `c` near `c₀`, i.e. `y` is outside the filled Julia set `K_c`
(use `Work.ParamRays.greenFun_pos_iff_escaping` after the bridge with `Work.Escape.green`).

Route: `K × {c₀}` is compact and `jointGreen ≥ s > 0` on it, so joint continuity of
`Work.NAKANE.jointGreen` (`Work.NAKANE.GreenJoint.continuous_jointGreen`, already proved: import
`Submission.Work.NAKANE.GreenJoint.continuous_jointGreen`) gives an open neighbourhood of
`K × {c₀}` on which `jointGreen > s/2`; taking `ρ` below the distance from `K × {c₀}` to the
complement of that neighbourhood gives the conclusion (the case `K = ∅` is trivial). -/
theorem exists_green_pos_near {c₀ : ℂ} {K : Set ℂ} (hK : IsCompact K) {s : ℝ} (hs : 0 < s)
    (hKs : ∀ z ∈ K, s ≤ Work.NAKANE.jointGreen (c₀, z)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ c : ℂ, ‖c - c₀‖ < ρ → ∀ z : ℂ,
      (∃ k ∈ K, ‖z - k‖ < ρ) → 0 < Work.NAKANE.jointGreen (c, z) := by
  -- The compact slice `A = {c₀} × K` on which `jointGreen` is bounded below by `s > 0`.
  set A : Set (ℂ × ℂ) := ({c₀} : Set ℂ) ×ˢ K with hA
  have hAcompact : IsCompact A := by
    rw [hA]
    exact isCompact_singleton.prod hK
  -- The open set where `jointGreen` is `> s/2`; it contains `A`.
  have hUopen : IsOpen {p : ℂ × ℂ | s / 2 < Work.NAKANE.jointGreen p} :=
    isOpen_lt continuous_const continuous_jointGreen
  have hAU : A ⊆ {p : ℂ × ℂ | s / 2 < Work.NAKANE.jointGreen p} := by
    rw [hA]
    rintro ⟨a, b⟩ ⟨ha, hb⟩
    simp only [Set.mem_singleton_iff] at ha
    subst ha
    have hb' := hKs b hb
    simp only [Set.mem_ofPred_eq]
    linarith
  -- A whole cthickening of `A` therefore sits inside that open set.
  obtain ⟨δ, hδpos, hδ⟩ := hAcompact.exists_cthickening_subset_open hUopen hAU
  refine ⟨δ / 2, by linarith, ?_⟩
  intro c hc z hz
  obtain ⟨k, hkK, hzk⟩ := hz
  -- `(c₀, k) ∈ A`, and `(c, z)` is within `δ` of it.
  have hmemA : (c₀, k) ∈ A := by
    rw [hA]
    exact Set.mem_prod.mpr ⟨rfl, hkK⟩
  have hd : dist (c, z) (c₀, k) < δ := by
    rw [Prod.dist_eq, dist_eq_norm, dist_eq_norm]
    exact max_lt (hc.trans_le (by linarith)) (hzk.trans_le (by linarith))
  have hcth : (c, z) ∈ Metric.cthickening δ A :=
    Metric.mem_cthickening_of_dist_le (c, z) (c₀, k) δ A hmemA (le_of_lt hd)
  exact lt_trans (by linarith : (0 : ℝ) < s / 2) (hδ hcth)

end Work.NAKANE.GreenJoint
