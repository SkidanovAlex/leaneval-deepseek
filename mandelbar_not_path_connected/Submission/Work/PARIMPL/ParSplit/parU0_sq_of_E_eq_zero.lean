import Mathlib
import Submission.Work.PARIMPL.ParSplit.ParWall
import Submission.Work.PARIMPL.ParSplit.parChart_algebra
import Submission.Work.PARIMPL.ParSplit.parLam_eq
import Submission.Work.PARIMPL.ParSplit.parGerm_conj
import Submission.Work.PARIMPL.ParSplit.Hp_double_root_count
import Submission.Work.PARIMPL.ParSplit.g_mem_of_split
import Submission.Work.PARIMPL.ParSplit.deriv_star_comp_sq
import Submission.Work.PARIMPL.ParSplit.parRho_ne_zero
import Submission.Work.PARIMPL.ParSplit.parU0_eq_one_of_wall
import Submission.Work.PARIMPL.ParSplit.exists_uniform_bounds

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.PARIMPL.ParSplit

/-- **The value of the germ at `0` on the collision locus.**  If `E c = 0` (the two split fixed
points have merged) and `c` is close to `c₀`, then `parU0 S c ^ 2 = 1`; i.e. the rotation
`parHgerm S c 0` of the normal form is exactly `1` there.  Consequently the two possible values
of `parU0 S c` are `±1`, and the principal-branch condition `Re (Complex.sqrt z) ≥ 0` selects `1`;
this is what makes the clause `‖h 0 - 1‖ ≤ 1/2` of `ParBounds` available on the whole ball
(including the collision curve, where the phase estimate `phase_of_split` — which requires
`E c ≠ 0` — cannot be applied).

Sketch of the proof (all but the last algebra step is already in the workspace):
* `E c = 0` gives `Gc c = 0`, and `Qpoly_eval_shift_local` gives `Q_c(m c + w) = w² Rfun(c,w)`;
  in particular `F c (m c) = m c` and `(Q_c)'(m c) = 0` (`Hp_double_root_count`), i.e. `m c` is a
  parabolic fixed point of `F c`, and `gtc c (m c) = m c` (from `g_mem_of_split` + `SplitData.unique`).
* `parRho S c = psi S c 0 = phi S c 2 = (F c)''(m c)/2` (`two_mul_coeff_comp_X_add_C`,
  `iteratedDeriv_two_poly`).
* With `α := deriv (fun u => (Gpoly c).eval u) (m c)` one has `parH S c = α`
  (`parH_eq_gam_one_of_E_eq_zero`, `gam_one_eq_deriv`), `parLam S c = conj α`, and
  `F c = f ∘ G` with `G := fun u => (Gpoly c).eval u`, `f := fun x => star (G (star x))`
  (`eval_Gpoly_eq_star_gtc`, `Ft_eq_g_comp`).
* `deriv (F c) (m c) = α * conj α = 1` (`deriv_star_comp_sq`), so `|α| = 1`.
* `(F c)''(m c) = conj (G''(m c)) * α^2 + conj α * G''(m c)` (`iteratedDeriv_two_comp` applied to
  `f ∘ G`, plus `deriv (fun x => star (h (star x))) w = star (deriv h (star w))`).
* Hence `parLam * parRho = conj α * (conj (G'') α^2 + conj α G'')/2 = (conj (G'') α + conj α^2 G'')/2
  = conj (parRho)` using `α * conj α = 1`.
* Finally `parU0^2 = parLam * parRho^2 / ‖parRho‖^2 = (parLam * parRho) * parRho / ‖parRho‖^2
  = conj(parRho) * parRho / ‖parRho‖^2 = 1`. -/
theorem parU0_sq_of_E_eq_zero {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    (S : Work.PARIMPL.ParSplit.SplitData d) :
    ∃ ρ' > 0, ρ' ≤ S.ρ ∧ ∀ c ∈ Metric.ball c₀ ρ',
      S.E c = 0 → Work.PARIMPL.ParSplit.parU0 S c ^ 2 = 1 := by
  obtain ⟨ρ₁, hρ₁, hρ₁ρ, hwall⟩ := parU0_eq_one_of_wall S
  obtain ⟨ρ₂, hρ₂, hρ₂ρ, hdr⟩ := Hp_double_root_count S
  refine ⟨min ρ₁ ρ₂, lt_min hρ₁ hρ₂, le_trans (min_le_left _ _) hρ₁ρ, ?_⟩
  intro c hc hE
  have hc₁ : c ∈ Metric.ball c₀ ρ₁ := Metric.ball_subset_ball (min_le_left _ _) hc
  have hc₂ : c ∈ Metric.ball c₀ ρ₂ := Metric.ball_subset_ball (min_le_right _ _) hc
  rw [hwall c hc₁ hE (hdr c hc₂ hE), one_pow]

end Work.PARIMPL.ParSplit
