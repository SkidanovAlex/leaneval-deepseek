/-
# `Work.PARIMPL.ParSplit.parH_ne_zero`

`parH S c` is the symmetric difference quotient of the holomorphic partner
`G_c = \overline{(T_c)^5}` of the antiholomorphic square root at the midpoint `S.m c` of the two
split fixed points,

    parH S c = (G_c (m + Δ) - G_c (m - Δ)) / (2Δ),      Δ = S.E c / 2,

of `ParWall`'s `parH` (finite sum form; the identity with the difference quotient is
`parLam_eq.eval_sub_eval_neg_Gam`).  This module shows that it does not vanish near `c₀`.

**Structure of the argument.**  `parH` is *continuous* (`ParWall.continuousOn_parH`), so it
suffices to show `parH S c₀ ≠ 0`; nonvanishing then propagates to a whole ball around `c₀`.

At `c₀` the two split fixed points collide (`S.E c₀ = 0`), so the defining sum of `parH`
collapses to its `l = 1` term,

    parH S c₀ = gam S c₀ 1 = G_{c₀}'(z₁),

and it remains to see that the derivative of `G_{c₀}` at the parabolic point `z₁` does not vanish.
This is where the parabolic structure enters: `g = (T_{c₀})^5` is the antiholomorphic square root
of `F = (T_{c₀})^{10} = g ∘ g`, `G_{c₀} = \overline{g}` is its holomorphic partner, `g z₁ = z₁`
(`RootParabolic.per_half`) and `F'(z₁) = 1` (`RootParabolic.mult`, a *simple* parabolic point).
Differentiating the identity

    \overline{G_{c₀} (\overline{G_{c₀}} u)} = (g ∘ g) u = F u

(`deriv_star_comp_sq`: the chain rule for `\overline{h ∘ \overline{h}}`) at `u = z₁`, where
`\overline{G_{c₀} z₁} = g z₁ = z₁`, gives

    G_{c₀}'(z₁) · \overline{G_{c₀}'(z₁)} = F'(z₁) = 1,

so `G_{c₀}'(z₁)` is a unit complex number, in particular nonzero.  Thus `parH S c₀ ≠ 0`, and
continuity finishes.
-/
import Mathlib
import Submission.Work.PARIMPL.ParSplit.ParWall
import Submission.Work.PARIMPL.ParSplit.parLam_eq
import Submission.Work.PARIMPL.ParSplit.deriv_star_comp_sq

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedVariables false

open Classical Filter Set Metric
open scoped Topology

noncomputable section

namespace Work.PARIMPL.ParSplit

open Polynomial

variable {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}

/-! ## The value of `parH` at a collision parameter -/

/-- At a parameter `c` where the two split fixed points collide (`S.E c = 0`) all the terms of
the defining sum of `parH` except the first (`l = 1`) vanish, so
`parH S c = gam S c 1`. -/
theorem parH_eq_gam_one_of_E_eq_zero (S : SplitData d) {c : ℂ} (hE : S.E c = 0) :
    parH S c = gam S c 1 := by
  unfold parH
  rw [Finset.sum_eq_single 1]
  · rw [ite_eq_left (by norm_num : 1 % 2 = 1), pow_zero, mul_one]
  · intro l _ hne
    by_cases hodd : l % 2 = 1
    · rw [ite_eq_left hodd]
      obtain ⟨k, hk⟩ := Nat.odd_iff.mpr hodd
      have hk0 : k ≠ 0 := by
        intro hkz
        exact hne (by simp [hk, hkz])
      have hpow : (S.E c / 2) ^ (l - 1) = 0 := by
        rw [hk, hE]
        have : (2 * k + 1) - 1 = 2 * k := by omega
        rw [this, zero_div, zero_pow (by positivity)]
      rw [hpow, mul_zero]
    · rw [ite_eq_right hodd]
  · intro h1
    exact absurd (Finset.mem_range.mpr (by norm_num [wallN])) h1

/-! ## `gam S c 1` is a derivative -/

/-- The linear coefficient of `G_c (S.m c + ·)` is the derivative of `G_c` at the midpoint. -/
theorem gam_one_eq_deriv (S : SplitData d) (c : ℂ) :
    gam S c 1 = deriv (fun u => (Gpoly c).eval u) (S.m c) := by
  have h1 : gam S c 1 = ((taylor (S.m c)) (Gpoly c)).coeff 1 := by
    unfold gam Gam
    rw [Polynomial.taylor_apply]
  rw [h1, Polynomial.taylor_coeff, Polynomial.hasseDeriv_one]
  exact (Polynomial.deriv (Gpoly c)).symm

/-! ## The derivative of the holomorphic partner at the parabolic point -/

/-- The holomorphic partner `G_{c₀}` of the antiholomorphic square root has a **unit** derivative
at the parabolic point `z₁ = S.m c₀`:

    G_{c₀}'(z₁) · conj (G_{c₀}'(z₁)) = F'(z₁) = 1.

Indeed `\overline{G_{c₀}} = g = (T_{c₀})^5` squares to `F = (T_{c₀})^{10}`, and
`\overline{G_{c₀} z₁} = g z₁ = z₁`, so differentiating
`\overline{G_{c₀}(\overline{G_{c₀}} u)} = F u` at `u = z₁` gives the claim with `F'(z₁) = 1`
(`RootParabolic.mult`). -/
theorem deriv_Gpoly_mul_star_self (S : SplitData d) :
    deriv (fun u => (Gpoly c₀).eval u) (S.m c₀)
      * star (deriv (fun u => (Gpoly c₀).eval u) (S.m c₀)) = 1 := by
  rw [S.m₀]
  have hdiff : Differentiable ℂ (fun u => (Gpoly c₀).eval u) := Polynomial.differentiable _
  have hsq := deriv_star_comp_sq hdiff d.z₁
  -- the function `u ↦ conj (G_{c₀} (conj (G_{c₀} u)))` is `g ∘ g = F`
  have hfun : (fun x => star ((fun u => (Gpoly c₀).eval u)
      (star ((fun u => (Gpoly c₀).eval u) x)))) = Ft c₀ := by
    funext x
    show star ((Gpoly c₀).eval (star ((Gpoly c₀).eval x))) = Ft c₀ x
    rw [eval_Gpoly_eq_star_gtc c₀ x, star_star, eval_Gpoly_eq_star_gtc c₀ (gtc c₀ x),
      gtc_comp_apply, star_star]
  rw [hfun] at hsq
  have hF' : deriv (Ft c₀) d.z₁ = 1 := by
    simpa only [Ft, Work.EL.F, Work.Landing.multiplier2] using d.mult
  have hφz : star ((Gpoly c₀).eval d.z₁) = d.z₁ := by
    rw [eval_Gpoly_eq_star_gtc c₀ d.z₁, star_star]
    exact d.per_half
  rw [hF', hφz] at hsq
  exact hsq.symm

/-! ## Nonvanishing -/

/-- `parH` does not vanish at the root-parabolic parameter `c₀`: there `parH S c₀ = G_{c₀}'(z₁)`
is a unit complex number. -/
theorem parH_at_root_ne_zero (S : SplitData d) : parH S c₀ ≠ 0 := by
  have hval : parH S c₀ = deriv (fun u => (Gpoly c₀).eval u) (S.m c₀) := by
    rw [parH_eq_gam_one_of_E_eq_zero S S.E₀, gam_one_eq_deriv]
  have hunit := deriv_Gpoly_mul_star_self S
  have hne : deriv (fun u => (Gpoly c₀).eval u) (S.m c₀) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hunit
    exact one_ne_zero hunit.symm
  rw [hval]
  exact hne

theorem parH_ne_zero {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    (S : Work.PARIMPL.ParSplit.SplitData d) :
    ∃ ρ' > 0, ρ' ≤ S.ρ ∧ ∀ c ∈ Metric.ball c₀ ρ',
      Work.PARIMPL.ParSplit.parH S c ≠ 0 := by
  have h0 : parH S c₀ ≠ 0 := parH_at_root_ne_zero S
  have hcont : ContinuousOn (parH S) (ball c₀ S.ρ) := continuousOn_parH S le_rfl
  have hmem : c₀ ∈ ball c₀ S.ρ := Metric.mem_ball_self S.hρ
  have hca : ContinuousAt (parH S) c₀ :=
    hcont.continuousAt (Metric.isOpen_ball.mem_nhds hmem)
  have hnhds : {c : ℂ | parH S c ≠ 0} ∈ nhds c₀ :=
    hca.preimage_mem_nhds (isOpen_ne.mem_nhds h0)
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hnhds
  refine ⟨min δ (S.ρ / 2), lt_min hδ (by linarith [S.hρ]),
    le_trans (min_le_right _ _) (by linarith [S.hρ]), ?_⟩
  intro c hc
  exact hδsub (Metric.ball_subset_ball (min_le_left _ _) hc)

end Work.PARIMPL.ParSplit
