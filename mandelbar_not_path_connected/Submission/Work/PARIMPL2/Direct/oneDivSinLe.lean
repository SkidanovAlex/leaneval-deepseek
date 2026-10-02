import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.PARIMPL2.Direct

open Set

/-- Auxiliary function for the proof of `oneDivSinLe`: `π * sin x + x ^ 2 - π * x`.
It equals `π * sin x - x * (π - x)`, which we show is nonnegative on `[0, π]`. -/
private noncomputable def mbarAux (x : ℝ) : ℝ := Real.pi * Real.sin x + x ^ 2 - Real.pi * x

theorem oneDivSinLe (t : ℝ) (h0 : 0 < t) (hpi : t < Real.pi) :
    1 / Real.sin t ≤ 1 / t + 1 / (Real.pi - t) := by
  -- The auxiliary function is `π sin x - x (π - x)`; we prove it is `≥ 0` on `[0, π]`,
  -- which yields `sin t ≥ t (π - t) / π`, and hence the desired reciprocal inequality.
  have hderiv : ∀ x, HasDerivAt mbarAux (Real.pi * Real.cos x + 2 * x - Real.pi) x := by
    intro x
    unfold mbarAux
    have h1 : HasDerivAt (fun x : ℝ => Real.pi * Real.sin x) (Real.pi * Real.cos x) x :=
      (Real.hasDerivAt_sin x).const_mul Real.pi
    have h2 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * x) x := by
      simpa using hasDerivAt_pow 2 x
    have h3 : HasDerivAt (fun x : ℝ => Real.pi * x) Real.pi x := by
      simpa using (hasDerivAt_id x).const_mul Real.pi
    exact (h1.add h2).sub h3
  have hcont : Continuous mbarAux := by unfold mbarAux; fun_prop
  have hdiff : Differentiable ℝ mbarAux := by unfold mbarAux; fun_prop
  -- On `[0, π/2]` the derivative is nonnegative, using Jordan's inequality for `cos`.
  have hA : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 ≤ deriv mbarAux x := by
    intro x hx
    rw [(hderiv x).deriv]
    have hx0 : 0 ≤ x := le_of_lt hx.1
    have hx2 : x ≤ Real.pi / 2 := le_of_lt hx.2
    have hcos := Real.one_sub_mul_le_cos hx0 hx2
    have hcos' : Real.pi - 2 * x ≤ Real.pi * Real.cos x := by
      calc Real.pi - 2 * x = Real.pi * (1 - 2 / Real.pi * x) := by field_simp
        _ ≤ Real.pi * Real.cos x := by
              apply mul_le_mul_of_nonneg_left hcos Real.pi_pos.le
    linarith
  -- On `[π/2, π]` the derivative is nonpositive, using Jordan's inequality for `sin`.
  have hB : ∀ x ∈ Set.Ioo (Real.pi / 2) Real.pi, deriv mbarAux x ≤ 0 := by
    intro x hx
    rw [(hderiv x).deriv]
    set s := x - Real.pi / 2 with hs
    have hs0 : 0 < s := by linarith [hx.1]
    have hs2 : s ≤ Real.pi / 2 := by linarith [hx.2]
    have hcos : Real.cos x = - Real.sin s := by
      have : x = s + Real.pi / 2 := by linarith
      rw [this, Real.cos_add_pi_div_two]
    rw [hcos]
    have hsine := Real.mul_le_sin hs0.le hs2
    have h2s : 2 * s ≤ Real.pi * Real.sin s := by
      have := mul_le_mul_of_nonneg_left hsine Real.pi_pos.le
      rwa [show Real.pi * (2 / Real.pi * s) = 2 * s by field_simp] at this
    linarith
  have hmono : MonotoneOn mbarAux (Set.Icc 0 (Real.pi / 2)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 (Real.pi / 2)) hcont.continuousOn
      hdiff.differentiableOn
    intro x hx
    rw [interior_Icc] at hx
    exact hA x hx
  have hanti : AntitoneOn mbarAux (Set.Icc (Real.pi / 2) Real.pi) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc (Real.pi / 2) Real.pi) hcont.continuousOn
      hdiff.differentiableOn
    intro x hx
    rw [interior_Icc] at hx
    exact hB x hx
  have hf0 : mbarAux 0 = 0 := by unfold mbarAux; rw [Real.sin_zero]; ring
  have hfpi : mbarAux Real.pi = 0 := by unfold mbarAux; rw [Real.sin_pi]; ring
  have hfnonneg : 0 ≤ mbarAux t := by
    rcases le_or_gt t (Real.pi / 2) with hle | hgt
    · have hmem0 : (0 : ℝ) ∈ Set.Icc 0 (Real.pi / 2) :=
        ⟨le_rfl, by linarith [Real.pi_pos]⟩
      have hmemt : t ∈ Set.Icc 0 (Real.pi / 2) := ⟨le_of_lt h0, hle⟩
      have h := hmono hmem0 hmemt (le_of_lt h0)
      rwa [hf0] at h
    · have hmemt : t ∈ Set.Icc (Real.pi / 2) Real.pi := ⟨le_of_lt hgt, le_of_lt hpi⟩
      have hmempi : Real.pi ∈ Set.Icc (Real.pi / 2) Real.pi :=
        ⟨by linarith [Real.pi_pos], le_rfl⟩
      have h := hanti hmemt hmempi (le_of_lt hpi)
      rwa [hfpi] at h
  -- `π * sin t ≥ t * (π - t)`
  have hkey : t * (Real.pi - t) ≤ Real.pi * Real.sin t := by
    have := hfnonneg
    unfold mbarAux at this
    nlinarith
  have hApos : 0 < t * (Real.pi - t) / Real.pi :=
    div_pos (mul_pos h0 (by linarith)) Real.pi_pos
  have hsin : t * (Real.pi - t) / Real.pi ≤ Real.sin t := by
    rw [div_le_iff₀ Real.pi_pos]
    linarith
  refine (one_div_le_one_div_of_le hApos hsin).trans_eq ?_
  have hpt : Real.pi - t ≠ 0 := by linarith
  field_simp
  ring

end Work.PARIMPL2.Direct
