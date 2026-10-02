/-
# Vanishing of the lift change of the normalised-factor path at a level `s`

**Generalisation of `Work.Bottcher.Contraction.liftChange_normFactorPath_eq_zero`** (which is
the case `s = 0`, `c ∈ M*`).

Let `s ≥ green c 0` be a level such that the sublevel set `K = {z | green c z ≤ s}` is
preconnected.  Let `γ` be a closed path on which `green c` exceeds `s` (so `γ` avoids `K`,
hence avoids `0` and the four roots of `p_c`, which satisfy `green c ≤ s`).  Then the
normalised-factor path `t ↦ p_c (γ t)/(γ t)^4` admits a *closed* lift through the exponential
covering: its lift change vanishes.

Proof: as in the case `s = 0`, write `p_c z = ∏_j (z - root_j c)` and

`p_c (γ t)/(γ t)^4 = ∏_j (γ t - root_j c) / (γ t)^4`,

so that, by additivity of the lift change under products and powers,

`liftChange (η ∘ γ) + 4·liftChange γ = Σ_j liftChange (γ - root_j c)`.

All the points `0, root_1 c, …, root_4 c` lie in `K`:
`green c 0 ≤ s` is the hypothesis, and `green c (root_j c) = green c 0 / 4 ≤ green c 0 ≤ s`
because `p_c (root_j c) = 0` and `G_c(p_c z) = 4 G_c z`
(`Work.Bottcher.CritBasic.green_pMap_four`, `Work.Bottcher.Green.green_nonneg`).
By `liftChange_pathSub_eq_of_green_le` (with `p = 0`) the five lift changes on the right are
therefore all equal to `liftChange γ`, and the identity gives `liftChange (η ∘ γ) = 0`.
-/
import Mathlib
import Submission.Work.Bottcher.Defs
import Submission.Work.Bottcher.CritBasic
import Submission.Work.Bottcher.Contraction.LiftCoreDefs
import Submission.Work.Bottcher.Contraction.NormFactorRoots
import Submission.Work.Bottcher.Contraction.liftChange_mul
import Submission.Work.Bottcher.Contraction.liftChange_normFactorPath_eq_zero
import Submission.Work.Bottcher.Contraction.liftChange_pathSub_eq_of_green_le
import Submission.Work.Bottcher.Inverse.green_eq_log_of_inverseBottcher

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Bottcher.Contraction

noncomputable section

open Filter Function
open scoped Topology

/-- **Green value of a root of `pMap c`.**  If `pMap c z = 0` then `green c z = green c 0 / 4`,
because `green c (pMap c z) = 4 * green c z`. -/
theorem green_eq_div_four_of_pMap_eq_zero (c z : ℂ) (hz : Work.Bottcher.pMap c z = 0) :
    Work.Bottcher.green c z = Work.Bottcher.green c 0 / 4 := by
  have h := Work.Bottcher.CritBasic.green_pMap_four c z
  rw [hz] at h
  linarith

theorem liftChange_normFactorPath_eq_zero_of_preconnected (c : ℂ) (s : ℝ)
    (hK : IsPreconnected {z : ℂ | Work.Bottcher.green c z ≤ s})
    (hg0 : Work.Bottcher.green c 0 ≤ s)
    (γ : C(unitInterval, ℂ)) (hloop : γ 1 = γ 0)
    (hγ : ∀ t, s < Work.Bottcher.green c (γ t)) (hγne : ∀ t, γ t ≠ 0)
    (h : ∀ t, Work.Bottcher.Contraction.normFactorPath c γ hγne t ≠ 0) :
    Work.Bottcher.Contraction.liftChange
      (Work.Bottcher.Contraction.normFactorPath c γ hγne) h = 0 := by
  -- The four roots of `p_c` have Green value `green c 0 / 4 ≤ green c 0 ≤ s`.
  have h0nn : 0 ≤ Work.Bottcher.green c 0 := Work.Bottcher.Green.green_nonneg c 0
  have hr1 : Work.Bottcher.green c (root1 c) ≤ s := by
    rw [green_eq_div_four_of_pMap_eq_zero c (root1 c) (pMap_root1 c)]; linarith
  have hr2 : Work.Bottcher.green c (root2 c) ≤ s := by
    rw [green_eq_div_four_of_pMap_eq_zero c (root2 c) (pMap_root2 c)]; linarith
  have hr3 : Work.Bottcher.green c (root3 c) ≤ s := by
    rw [green_eq_div_four_of_pMap_eq_zero c (root3 c) (pMap_root3 c)]; linarith
  have hr4 : Work.Bottcher.green c (root4 c) ≤ s := by
    rw [green_eq_div_four_of_pMap_eq_zero c (root4 c) (pMap_root4 c)]; linarith
  -- The loop lies in the escape set, hence avoids the sublevel set `K`.
  have hsub_ne : ∀ p : ℂ, Work.Bottcher.green c p ≤ s → ∀ t, pathSub γ p t ≠ 0 := by
    intro p hp t
    rw [pathSub_apply, sub_ne_zero]
    intro htp
    have hle : Work.Bottcher.green c (γ t) ≤ s := by rw [htp]; exact hp
    linarith [hγ t]
  have hd0 : ∀ t, pathSub γ 0 t ≠ 0 := hsub_ne 0 hg0
  have hd1 : ∀ t, pathSub γ (root1 c) t ≠ 0 := hsub_ne (root1 c) hr1
  have hd2 : ∀ t, pathSub γ (root2 c) t ≠ 0 := hsub_ne (root2 c) hr2
  have hd3 : ∀ t, pathSub γ (root3 c) t ≠ 0 := hsub_ne (root3 c) hr3
  have hd4 : ∀ t, pathSub γ (root4 c) t ≠ 0 := hsub_ne (root4 c) hr4
  -- Non-vanishing of `γ^4`.
  have hG4 : ∀ t, (γ ^ 4) t ≠ 0 := by
    intro t
    rw [ContinuousMap.pow_apply]
    exact pow_ne_zero 4 (hγne t)
  -- Non-vanishing of the product of the four translated loops.
  have hP4 : ∀ t, (pathSub γ (root1 c) * pathSub γ (root2 c) * pathSub γ (root3 c)
      * pathSub γ (root4 c)) t ≠ 0 := by
    intro t
    simp only [ContinuousMap.mul_apply]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (hd1 t) (hd2 t)) (hd3 t)) (hd4 t)
  -- `η ∘ γ` times `γ^4` is the product of the four translated loops.
  have hDGeq : normFactorPath c γ hγne * γ ^ 4
      = pathSub γ (root1 c) * pathSub γ (root2 c) * pathSub γ (root3 c)
        * pathSub γ (root4 c) := by
    ext t
    simp only [ContinuousMap.mul_apply, ContinuousMap.pow_apply, normFactorPath_apply,
      pathSub_apply]
    rw [pMap_eq_prod_roots c (γ t), div_mul_cancel₀ _ (pow_ne_zero 4 (hγne t))]
  have hDG : ∀ t, (normFactorPath c γ hγne * γ ^ 4) t ≠ 0 := by
    intro t
    rw [congrArg (fun f : C(unitInterval, ℂ) => f t) hDGeq]
    exact hP4 t
  have hmul := liftChange_mul (normFactorPath c γ hγne) (γ ^ 4) h hG4 hDG
  have hcop : liftChange (normFactorPath c γ hγne * γ ^ 4) hDG
      = liftChange (pathSub γ (root1 c) * pathSub γ (root2 c) * pathSub γ (root3 c)
          * pathSub γ (root4 c)) hP4 := liftChange_congr hDGeq hDG hP4
  have hpow : liftChange (γ ^ 4) hG4 = (4 : ℂ) * liftChange γ hγne :=
    liftChange_pow γ hγne 4 hG4
  have hfour : liftChange (pathSub γ (root1 c) * pathSub γ (root2 c) * pathSub γ (root3 c)
      * pathSub γ (root4 c)) hP4
      = liftChange (pathSub γ (root1 c)) hd1 + liftChange (pathSub γ (root2 c)) hd2
        + liftChange (pathSub γ (root3 c)) hd3 + liftChange (pathSub γ (root4 c)) hd4 :=
    liftChange_mul_four _ _ _ _ hd1 hd2 hd3 hd4 hP4
  -- The four roots lie in the preconnected sublevel set, so the winding about each of them
  -- equals the winding about `0`.
  have e1 : liftChange (pathSub γ (root1 c)) hd1 = liftChange (pathSub γ 0) hd0 :=
    liftChange_pathSub_eq_of_green_le c s hK γ hloop hγ hr1 hg0 hd1 hd0
  have e2 : liftChange (pathSub γ (root2 c)) hd2 = liftChange (pathSub γ 0) hd0 :=
    liftChange_pathSub_eq_of_green_le c s hK γ hloop hγ hr2 hg0 hd2 hd0
  have e3 : liftChange (pathSub γ (root3 c)) hd3 = liftChange (pathSub γ 0) hd0 :=
    liftChange_pathSub_eq_of_green_le c s hK γ hloop hγ hr3 hg0 hd3 hd0
  have e4 : liftChange (pathSub γ (root4 c)) hd4 = liftChange (pathSub γ 0) hd0 :=
    liftChange_pathSub_eq_of_green_le c s hK γ hloop hγ hr4 hg0 hd4 hd0
  have hpath0 : pathSub γ 0 = γ := by
    ext t
    simp [pathSub_apply]
  have e0 : liftChange (pathSub γ 0) hd0 = liftChange γ hγne :=
    liftChange_congr hpath0 hd0 hγne
  have hsub : liftChange (normFactorPath c γ hγne) h
      = liftChange (normFactorPath c γ hγne * γ ^ 4) hDG - liftChange (γ ^ 4) hG4 := by
    rw [hmul]
    ring
  rw [hsub, hcop, hfour, e1, e2, e3, e4, e0, hpow]
  ring

end

end Work.Bottcher.Contraction
