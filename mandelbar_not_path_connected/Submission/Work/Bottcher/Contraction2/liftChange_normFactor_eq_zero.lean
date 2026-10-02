import Mathlib
import Submission.Work.Bottcher.Defs
import Submission.Work.Bottcher.Contraction.LiftCoreDefs
import Submission.Work.Bottcher.Contraction.liftChange_mul
import Submission.Work.Bottcher.Contraction.liftChange_pathSub_eq_of_segment
import Submission.Work.Bottcher.Contraction.NormFactorRoots
import Submission.Work.Bottcher.Contraction.liftChange_pathSub_eq_of_green_eq_zero
import Submission.Work.Bottcher.Green.green_nonneg
import Submission.Work.Bottcher.Green.greenParam_pos_iff

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Winding numbers of the normalised factor along loops in the escape set

For `c` in the mandelbar the holomorphic quartic `p_c = T_c ∘ T_c` factors through its four
roots, `p_c z = ∏_j (z - root_j)`, and those roots, together with the critical point `0`, all
lie in the filled Julia set `K = {G_c = 0}`.  If `K` is connected (`hK`), the winding number
of a closed loop `γ` avoiding `K` about every point of `K` is the same, so the winding numbers
of the four translated loops `t ↦ γ t - root_j` coincide with that of `γ` itself.  Since

`η(z) = p_c z / z^4 = (∏_j (z - root_j)) · z^{-4}`,

the winding number of `t ↦ η (γ t)` is `4 - 4 = 0`: the winding of `p_c ∘ γ` is the sum of the
four equal windings, and the winding of `z ↦ z^{-4}` along `γ` is `-4` times the winding of
`γ`.  Equivalently, the lift change of `t ↦ η (γ t)` through the exponential covering vanishes.

The winding invariance about the points of `K` is `liftChange_pathSub_eq_of_green_eq_zero`; the
remaining content of this file is the multiplicativity of the lift change (products and
powers of nowhere-zero paths), which turns the winding computation into the formal identity
`liftChange (η ∘ γ) = 4 · liftChange γ - 4 · liftChange γ`.
-/

open Filter Function
open scoped Topology

namespace Work.Bottcher.Contraction2

open Work.Bottcher.Contraction

/-- **Lift changes depend only on the underlying path.**  Two equal continuous maps have equal
lift changes, whatever witnesses of non-vanishing are used. -/
theorem liftChange_congr {δ δ' : C(unitInterval, ℂ)} (h : δ = δ')
    (hδ : ∀ t, δ t ≠ 0) (hδ' : ∀ t, δ' t ≠ 0) :
    liftChange δ hδ = liftChange δ' hδ' := by
  subst h
  rw [Subsingleton.elim hδ hδ']

/-- **The lift change of the constant path `1` is zero.** -/
theorem liftChange_one (h : ∀ t : unitInterval, (1 : C(unitInterval, ℂ)) t ≠ 0) :
    liftChange (1 : C(unitInterval, ℂ)) h = 0 := by
  have he : Complex.exp (0 : ℂ) = (1 : C(unitInterval, ℂ)) 0 := Complex.exp_zero.trans rfl
  have hlift : ∀ t : unitInterval,
      Complex.exp ((fun _ : unitInterval => (0 : ℂ)) t) = (1 : C(unitInterval, ℂ)) t :=
    fun t => Complex.exp_zero.trans rfl
  have h0 : (fun _ : unitInterval => (0 : ℂ)) 0 = (0 : ℂ) := rfl
  rw [liftChange_eq_of_lift (δ := 1) h he continuous_const hlift h0]
  simp

/-- The pointwise inverse of a nowhere-zero continuous path `δ : C(I, ℂ)`.  (The bundled
inverse of `ContinuousMap` is not available for `ℂ`, where `z ↦ z⁻¹` is not continuous at
`0`, so we build it by hand from the pointwise inverse and `Continuous.inv₀`.) -/
noncomputable def invPath (δ : C(unitInterval, ℂ)) (hδ : ∀ t, δ t ≠ 0) : C(unitInterval, ℂ) :=
  ⟨fun t => (δ t)⁻¹, δ.continuous.inv₀ hδ⟩

@[simp] theorem invPath_apply (δ : C(unitInterval, ℂ)) (hδ : ∀ t, δ t ≠ 0) (t : unitInterval) :
    invPath δ hδ t = (δ t)⁻¹ := rfl

/-- The path `t ↦ (δ t)^{-4}`, the fourth power of the pointwise inverse of `δ`. -/
noncomputable def invFourPath (δ : C(unitInterval, ℂ)) (hδ : ∀ t, δ t ≠ 0) : C(unitInterval, ℂ) :=
  invPath δ hδ ^ 4

@[simp] theorem invFourPath_apply (δ : C(unitInterval, ℂ)) (hδ : ∀ t, δ t ≠ 0)
    (t : unitInterval) : invFourPath δ hδ t = ((δ t)⁻¹) ^ 4 := by
  simp only [invFourPath, ContinuousMap.pow_apply, invPath_apply]

/-- **Lift change of the pointwise inverse.**  The lift of `1/δ` is the negative of the lift
of `δ`, so `liftChange δ⁻¹ = - liftChange δ`. -/
theorem liftChange_invPath (δ : C(unitInterval, ℂ)) (hδ : ∀ t, δ t ≠ 0)
    (h : ∀ t, invPath δ hδ t ≠ 0) : liftChange (invPath δ hδ) h = - liftChange δ hδ := by
  have hprod : ∀ t, (δ * invPath δ hδ) t ≠ 0 := by
    intro t
    simp only [ContinuousMap.mul_apply, invPath_apply]
    exact mul_ne_zero (hδ t) (inv_ne_zero (hδ t))
  have hone : liftChange (δ * invPath δ hδ) hprod = 0 := by
    have hpath : δ * invPath δ hδ = (1 : C(unitInterval, ℂ)) := by
      ext t
      simp only [ContinuousMap.mul_apply, invPath_apply]
      exact mul_inv_cancel₀ (hδ t)
    rw [liftChange_congr hpath hprod (fun _ => one_ne_zero)]
    exact liftChange_one (fun _ => one_ne_zero)
  have hmul := liftChange_mul δ (invPath δ hδ) hδ h hprod
  rw [hone] at hmul
  exact eq_neg_of_add_eq_zero_right hmul.symm

/-- **The lift change is additive in powers**: `liftChange (δ^n) = n · liftChange δ`. -/
theorem liftChange_pow (δ : C(unitInterval, ℂ)) (hδ : ∀ t, δ t ≠ 0) (n : ℕ) :
    ∀ (h : ∀ t, (δ ^ n) t ≠ 0), liftChange (δ ^ n) h = (n : ℂ) * liftChange δ hδ := by
  induction n with
  | zero =>
      intro h
      have h1 : ∀ t, (1 : C(unitInterval, ℂ)) t ≠ 0 := fun _ => one_ne_zero
      rw [liftChange_congr (pow_zero δ) h h1, liftChange_one h1]
      ring
  | succ n ih =>
      intro h
      have hδn : ∀ t, (δ ^ n) t ≠ 0 := by
        intro t ht
        refine h t ?_
        rw [pow_succ, ContinuousMap.mul_apply, ht, zero_mul]
      have h' : ∀ t, (δ ^ n * δ) t ≠ 0 := fun t => mul_ne_zero (hδn t) (hδ t)
      rw [liftChange_congr (pow_succ δ n) h h', liftChange_mul (δ ^ n) δ hδn hδ h', ih hδn]
      push_cast
      ring

/-- **Lift change of a product of four nowhere-zero paths.** -/
theorem liftChange_mul_four (a b c d : C(unitInterval, ℂ))
    (ha : ∀ t, a t ≠ 0) (hb : ∀ t, b t ≠ 0) (hc : ∀ t, c t ≠ 0) (hd : ∀ t, d t ≠ 0)
    (h : ∀ t, (a * b * c * d) t ≠ 0) :
    liftChange (a * b * c * d) h =
      liftChange a ha + liftChange b hb + liftChange c hc + liftChange d hd := by
  have hab : ∀ t, (a * b) t ≠ 0 := fun t => mul_ne_zero (ha t) (hb t)
  have habc : ∀ t, (a * b * c) t ≠ 0 := fun t => mul_ne_zero (hab t) (hc t)
  rw [liftChange_mul (a * b * c) d habc hd h, liftChange_mul (a * b) c hab hc habc,
    liftChange_mul a b ha hb hab]

/-- **The normalised factor of a loop in the escape set has zero winding.**  For `c` in the
mandelbar, `K = {G_c = 0}` connected, and `γ` a closed loop on which `G_c` is positive, the
lift change of `t ↦ η (γ t)`, `η z = p_c z / z^4`, vanishes. -/
theorem liftChange_normFactor_eq_zero (c : ℂ)
    (hc : c ∈ LeanEval.ComplexAnalysis.Mandelbar)
    (hK : IsConnected {z : ℂ | Work.Bottcher.green c z = 0})
    (γ : C(unitInterval, ℂ)) (hγ : ∀ t, 0 < Work.Bottcher.green c (γ t)) (hloop : γ 0 = γ 1)
    (hcont : Continuous fun t => Work.Bottcher.normFactor c (γ t))
    (hne : ∀ t, Work.Bottcher.normFactor c (γ t) ≠ 0) :
    Work.Bottcher.Contraction.liftChange
      ⟨fun t => Work.Bottcher.normFactor c (γ t), hcont⟩ hne = 0 := by
  -- The critical point `0` and the four roots of `p_c` lie in the filled Julia set `K`.
  have hg0 : Work.Bottcher.green c 0 = 0 := green_zero_of_mem_mandelbar c hc
  have hg1 : Work.Bottcher.green c (root1 c) = 0 := green_root1_of_mem_mandelbar c hc
  have hg2 : Work.Bottcher.green c (root2 c) = 0 := green_root2_of_mem_mandelbar c hc
  have hg3 : Work.Bottcher.green c (root3 c) = 0 := green_root3_of_mem_mandelbar c hc
  have hg4 : Work.Bottcher.green c (root4 c) = 0 := green_root4_of_mem_mandelbar c hc
  -- The loop lies in the escape set, hence avoids `K`.
  have hsub_ne : ∀ p : ℂ, Work.Bottcher.green c p = 0 → ∀ t, pathSub γ p t ≠ 0 := by
    intro p hp t
    rw [pathSub_apply, sub_ne_zero]
    intro htp
    have : Work.Bottcher.green c (γ t) = 0 := by rw [htp, hp]
    linarith [hγ t]
  have hd0 : ∀ t, pathSub γ 0 t ≠ 0 := hsub_ne 0 hg0
  have hd1 : ∀ t, pathSub γ (root1 c) t ≠ 0 := hsub_ne _ hg1
  have hd2 : ∀ t, pathSub γ (root2 c) t ≠ 0 := hsub_ne _ hg2
  have hd3 : ∀ t, pathSub γ (root3 c) t ≠ 0 := hsub_ne _ hg3
  have hd4 : ∀ t, pathSub γ (root4 c) t ≠ 0 := hsub_ne _ hg4
  have hinv : ∀ t, invPath (pathSub γ 0) hd0 t ≠ 0 := by
    intro t; rw [invPath_apply]; exact inv_ne_zero (hd0 t)
  have hB : ∀ t, invFourPath (pathSub γ 0) hd0 t ≠ 0 := by
    intro t; rw [invFourPath_apply]; exact pow_ne_zero 4 (inv_ne_zero (hd0 t))
  have hA : ∀ t, (pathSub γ (root1 c) * pathSub γ (root2 c) * pathSub γ (root3 c)
      * pathSub γ (root4 c)) t ≠ 0 := fun t =>
    mul_ne_zero (mul_ne_zero (mul_ne_zero (hd1 t) (hd2 t)) (hd3 t)) (hd4 t)
  -- `η ∘ γ` is the product of the four translated loops with `(γ - 0)^{-4}`.
  have hmap : (⟨fun t => Work.Bottcher.normFactor c (γ t), hcont⟩ : C(unitInterval, ℂ))
      = pathSub γ (root1 c) * pathSub γ (root2 c) * pathSub γ (root3 c) * pathSub γ (root4 c)
          * invFourPath (pathSub γ 0) hd0 := by
    ext t
    change Work.Bottcher.normFactor c (γ t)
      = (pathSub γ (root1 c) * pathSub γ (root2 c) * pathSub γ (root3 c) * pathSub γ (root4 c)
          * invFourPath (pathSub γ 0) hd0) t
    simp only [ContinuousMap.mul_apply, invFourPath_apply, pathSub_apply, sub_zero,
      Work.Bottcher.normFactor, pMap_eq_prod_roots c (γ t), inv_pow, div_eq_mul_inv]
  have hne' : ∀ t, (pathSub γ (root1 c) * pathSub γ (root2 c) * pathSub γ (root3 c)
      * pathSub γ (root4 c) * invFourPath (pathSub γ 0) hd0) t ≠ 0 :=
    fun t => mul_ne_zero (hA t) (hB t)
  rw [liftChange_congr hmap hne hne']
  -- Multiplicativity of the lift change along the product decomposition.
  have hAB : liftChange (pathSub γ (root1 c) * pathSub γ (root2 c) * pathSub γ (root3 c)
      * pathSub γ (root4 c) * invFourPath (pathSub γ 0) hd0) hne'
      = liftChange (pathSub γ (root1 c) * pathSub γ (root2 c) * pathSub γ (root3 c)
          * pathSub γ (root4 c)) hA
        + liftChange (invFourPath (pathSub γ 0) hd0) hB :=
    liftChange_mul _ _ hA hB hne'
  have hfour : liftChange (pathSub γ (root1 c) * pathSub γ (root2 c) * pathSub γ (root3 c)
      * pathSub γ (root4 c)) hA
      = liftChange (pathSub γ (root1 c)) hd1 + liftChange (pathSub γ (root2 c)) hd2
        + liftChange (pathSub γ (root3 c)) hd3 + liftChange (pathSub γ (root4 c)) hd4 :=
    liftChange_mul_four _ _ _ _ hd1 hd2 hd3 hd4 hA
  have hpow : liftChange (invFourPath (pathSub γ 0) hd0) hB
      = (4 : ℂ) * liftChange (invPath (pathSub γ 0) hd0) hinv :=
    liftChange_pow (invPath (pathSub γ 0) hd0) hinv 4 hB
  have hinvc : liftChange (invPath (pathSub γ 0) hd0) hinv = - liftChange (pathSub γ 0) hd0 :=
    liftChange_invPath (pathSub γ 0) hd0 hinv
  -- The four roots lie in the connected filled Julia set, so the winding about each of them
  -- equals the winding about `0`.
  have e1 : liftChange (pathSub γ (root1 c)) hd1 = liftChange (pathSub γ 0) hd0 :=
    liftChange_pathSub_eq_of_green_eq_zero c hK.isPreconnected γ hloop.symm hγ hg1 hg0 hd1 hd0
  have e2 : liftChange (pathSub γ (root2 c)) hd2 = liftChange (pathSub γ 0) hd0 :=
    liftChange_pathSub_eq_of_green_eq_zero c hK.isPreconnected γ hloop.symm hγ hg2 hg0 hd2 hd0
  have e3 : liftChange (pathSub γ (root3 c)) hd3 = liftChange (pathSub γ 0) hd0 :=
    liftChange_pathSub_eq_of_green_eq_zero c hK.isPreconnected γ hloop.symm hγ hg3 hg0 hd3 hd0
  have e4 : liftChange (pathSub γ (root4 c)) hd4 = liftChange (pathSub γ 0) hd0 :=
    liftChange_pathSub_eq_of_green_eq_zero c hK.isPreconnected γ hloop.symm hγ hg4 hg0 hd4 hd0
  rw [hAB, hfour, e1, e2, e3, e4, hpow, hinvc]
  ring

end Work.Bottcher.Contraction2
