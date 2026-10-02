import Mathlib
import Submission.Work.Bottcher.Defs
import Submission.Work.Bottcher.Contraction.LiftCoreDefs
import Submission.Work.Bottcher.Contraction.NormFactorRoots
import Submission.Work.Bottcher.Contraction.liftChange_mul
import Submission.Work.Bottcher.Contraction.liftChange_pathSub_eq_of_segment
import Submission.Work.Bottcher.Contraction.liftChange_pathSub_eq_of_green_eq_zero

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Vanishing of the lift change of the normalised-factor path

For `c` in the mandelbar the holomorphic quartic `p_c = T_c ∘ T_c` factors through its four
roots, `p_c z = ∏_{j} (z - root_j)`, and those roots together with the critical point `0` all
lie in the filled Julia set `K = {G_c = 0}`.  If `K` is preconnected, the winding number of a
closed loop `γ` avoiding `K` about every point of `K` is the same, so the winding numbers of
the four translated loops `γ - root_j` coincide with that of `γ` itself.  Since

`η(z) = p_c z / z^4 = (∏_j (z - root_j)) · z^{-4}`,

the winding number of `t ↦ η (γ t)` is `4 - 4 = 0`: the winding of `p_c ∘ γ` is the sum of the
four equal windings, and the winding of `γ^4` is `4` times the winding of `γ`.  Hence the lift
change of `t ↦ η (γ t)` through the exponential covering vanishes.

The winding invariance about the points of `K` is `liftChange_pathSub_eq_of_green_eq_zero`; the
rest is multiplicativity of the lift change (products and powers), which turns the winding
computation into the formal identity `liftChange (η ∘ γ) = 4 · liftChange γ - 4 · liftChange γ`.
-/

open Filter Function
open scoped Topology

namespace Work.Bottcher.Contraction

/-- **A lift change computed from any lift.**  If `Γ` is a continuous lift of the nowhere-zero
path `δ` through the exponential, then the lift change of `δ` is `Γ 1 - Γ 0`. -/
theorem liftChange_eq_sub_of_lifts {δ : C(unitInterval, ℂ)} (hδ : ∀ t, δ t ≠ 0)
    {Γ : unitInterval → ℂ} (hcont : Continuous Γ) (hlift : ∀ t, Complex.exp (Γ t) = δ t) :
    liftChange δ hδ = Γ 1 - Γ 0 :=
  liftChange_eq_of_lift (δ := δ) (e := Γ 0) hδ (hlift 0) hcont hlift rfl

/-- **Lift changes depend only on the underlying path.** -/
theorem liftChange_congr {δ δ' : C(unitInterval, ℂ)} (h : δ = δ')
    (hδ : ∀ t, δ t ≠ 0) (hδ' : ∀ t, δ' t ≠ 0) :
    liftChange δ hδ = liftChange δ' hδ' := by
  let L : C(unitInterval, ℂ) := liftOf δ hδ (Complex.log (δ 0)) (Complex.exp_log (hδ 0))
  have hlift : ∀ t, Complex.exp (L t) = δ t := fun t => exp_liftOf δ hδ _ _ t
  have hlift' : ∀ t, Complex.exp (L t) = δ' t := fun t => by
    rw [hlift t]
    exact congrArg (fun f : C(unitInterval, ℂ) => f t) h
  rw [liftChange_eq_sub_of_lifts (δ := δ) hδ L.continuous hlift,
    liftChange_eq_sub_of_lifts (δ := δ') hδ' L.continuous hlift']

/-- **The lift change of the constant path `1` is zero.** -/
theorem liftChange_one (h : ∀ t : unitInterval, (1 : C(unitInterval, ℂ)) t ≠ 0) :
    liftChange (1 : C(unitInterval, ℂ)) h = 0 := by
  have key := liftChange_eq_sub_of_lifts (δ := (1 : C(unitInterval, ℂ))) h
    (Γ := fun _ : unitInterval => (0 : ℂ)) continuous_const
    (fun t => by rw [Complex.exp_zero, ContinuousMap.one_apply])
  rw [key]
  simp

/-- **The lift change is additive in powers**: `liftChange (δ^n) = n · liftChange δ`. -/
theorem liftChange_pow (δ : C(unitInterval, ℂ)) (hδ : ∀ t, δ t ≠ 0) (n : ℕ) :
    ∀ (h : ∀ t, (δ ^ n) t ≠ 0), liftChange (δ ^ n) h = (n : ℂ) * liftChange δ hδ := by
  induction n with
  | zero =>
      intro h
      have h1 : ∀ t : unitInterval, (1 : C(unitInterval, ℂ)) t ≠ 0 := fun _ => one_ne_zero
      rw [liftChange_congr (pow_zero δ) h h1, liftChange_one h1]
      simp
  | succ n ih =>
      intro h
      have hδn : ∀ t, (δ ^ n) t ≠ 0 := by
        intro t ht
        exact h t (by simp [pow_succ, ContinuousMap.mul_apply, ht])
      have hprod : ∀ t, (δ ^ n * δ) t ≠ 0 := by
        intro t
        rw [ContinuousMap.mul_apply]
        exact mul_ne_zero (hδn t) (hδ t)
      rw [liftChange_congr (pow_succ δ n) h hprod,
        liftChange_mul (δ ^ n) δ hδn hδ hprod, ih hδn]
      push_cast
      ring

/-- **Lift change of a product of four nowhere-zero paths.** -/
theorem liftChange_mul_four (a b c d : C(unitInterval, ℂ))
    (ha : ∀ t, a t ≠ 0) (hb : ∀ t, b t ≠ 0) (hc : ∀ t, c t ≠ 0) (hd : ∀ t, d t ≠ 0)
    (h : ∀ t, (a * b * c * d) t ≠ 0) :
    liftChange (a * b * c * d) h =
      liftChange a ha + liftChange b hb + liftChange c hc + liftChange d hd := by
  have hab : ∀ t, (a * b) t ≠ 0 := by
    intro t
    rw [ContinuousMap.mul_apply]
    exact mul_ne_zero (ha t) (hb t)
  have habc : ∀ t, (a * b * c) t ≠ 0 := by
    intro t
    rw [ContinuousMap.mul_apply]
    exact mul_ne_zero (hab t) (hc t)
  rw [liftChange_mul (a * b * c) d habc hd h, liftChange_mul (a * b) c hab hc habc,
    liftChange_mul a b ha hb hab]

theorem liftChange_normFactorPath_eq_zero (c : ℂ) (hc : c ∈ LeanEval.ComplexAnalysis.Mandelbar)
    (hK : IsPreconnected {z : ℂ | Work.Bottcher.green c z = 0})
    (γ : C(unitInterval, ℂ)) (hloop : γ 1 = γ 0) (hγ : ∀ t, 0 < Work.Bottcher.green c (γ t))
    (hγne : ∀ t, γ t ≠ 0)
    (h : ∀ t, Work.Bottcher.Contraction.normFactorPath c γ hγne t ≠ 0) :
    Work.Bottcher.Contraction.liftChange (Work.Bottcher.Contraction.normFactorPath c γ hγne) h = 0 := by
  -- The critical point `0` and the four roots of `p_c` lie in the filled Julia set.
  have hg0 : Work.Bottcher.green c 0 = 0 := green_zero_of_mem_mandelbar c hc
  have hg1 : Work.Bottcher.green c (root1 c) = 0 := green_root1_of_mem_mandelbar c hc
  have hg2 : Work.Bottcher.green c (root2 c) = 0 := green_root2_of_mem_mandelbar c hc
  have hg3 : Work.Bottcher.green c (root3 c) = 0 := green_root3_of_mem_mandelbar c hc
  have hg4 : Work.Bottcher.green c (root4 c) = 0 := green_root4_of_mem_mandelbar c hc
  -- The loop lies in the escape set, hence avoids the filled Julia set.
  have hsub_ne : ∀ p : ℂ, Work.Bottcher.green c p = 0 → ∀ t, pathSub γ p t ≠ 0 := by
    intro p hp t
    rw [pathSub_apply, sub_ne_zero]
    intro htp
    have hzero : Work.Bottcher.green c (γ t) = 0 := by rw [htp]; exact hp
    linarith [hγ t]
  have hd0 : ∀ t, pathSub γ 0 t ≠ 0 := hsub_ne 0 hg0
  have hd1 : ∀ t, pathSub γ (root1 c) t ≠ 0 := hsub_ne (root1 c) hg1
  have hd2 : ∀ t, pathSub γ (root2 c) t ≠ 0 := hsub_ne (root2 c) hg2
  have hd3 : ∀ t, pathSub γ (root3 c) t ≠ 0 := hsub_ne (root3 c) hg3
  have hd4 : ∀ t, pathSub γ (root4 c) t ≠ 0 := hsub_ne (root4 c) hg4
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
  -- The four roots lie in the preconnected filled Julia set, so the winding about each of them
  -- equals the winding about `0`.
  have e1 : liftChange (pathSub γ (root1 c)) hd1 = liftChange (pathSub γ 0) hd0 :=
    liftChange_pathSub_eq_of_green_eq_zero c hK γ hloop hγ hg1 hg0 hd1 hd0
  have e2 : liftChange (pathSub γ (root2 c)) hd2 = liftChange (pathSub γ 0) hd0 :=
    liftChange_pathSub_eq_of_green_eq_zero c hK γ hloop hγ hg2 hg0 hd2 hd0
  have e3 : liftChange (pathSub γ (root3 c)) hd3 = liftChange (pathSub γ 0) hd0 :=
    liftChange_pathSub_eq_of_green_eq_zero c hK γ hloop hγ hg3 hg0 hd3 hd0
  have e4 : liftChange (pathSub γ (root4 c)) hd4 = liftChange (pathSub γ 0) hd0 :=
    liftChange_pathSub_eq_of_green_eq_zero c hK γ hloop hγ hg4 hg0 hd4 hd0
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

end Work.Bottcher.Contraction
