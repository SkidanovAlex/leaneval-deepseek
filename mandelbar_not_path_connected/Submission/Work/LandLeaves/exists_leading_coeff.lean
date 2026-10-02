import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LandLeaves

open Filter Asymptotics Set
open scoped Topology
/-- Leading nonlinear term of an analytic germ: if `F` is analytic at `0` with `F 0 = 0` and
`deriv F 0 = lam`, and is not equal to `lam * w` on a neighbourhood of `0`, then the first
nonlinear term of `F` is `c * w ^ (n+1)` with `n ≥ 1` and `c ≠ 0`.
Hint: use `analyticOrderAt` / `AnalyticAt.analyticOrderAt_ne_top` (Mathlib,
`Analysis/Analytic/Order.lean`) on `fun w => F w - lam * w`. -/
theorem exists_leading_coeff {F : ℂ → ℂ} {lam : ℂ} (hF : AnalyticAt ℂ F 0) (h0 : F 0 = 0)
    (hlam : deriv F 0 = lam) (hlin : ¬ (F =ᶠ[𝓝 0] fun w => lam * w)) :
    ∃ (n : ℕ) (c : ℂ), 1 ≤ n ∧ c ≠ 0 ∧
      Asymptotics.IsLittleO (𝓝 0) (fun w : ℂ => F w - lam * w - c * w ^ (n + 1)) (fun w : ℂ => w ^ (n + 1)) := by
  -- `G` is the nonlinear part `F - lam * id`.
  set G : ℂ → ℂ := fun w => F w - lam * w with hGdef
  have hG : AnalyticAt ℂ G 0 := by
    rw [hGdef]
    exact hF.sub (by fun_prop)
  have hG0 : G 0 = 0 := by
    rw [hGdef]; simp [h0]
  have hderivG : deriv G 0 = 0 := by
    have h1 : deriv (fun w : ℂ => F w - lam * w) 0 = deriv F 0 - lam :=
      ((hF.differentiableAt.hasDerivAt).sub (hasDerivAt_const_mul (x := 0) lam)).deriv
    rw [hGdef, h1, hlam]
    simp
  have hGne : ¬ ∀ᶠ w in 𝓝 (0:ℂ), G w = 0 := by
    intro h
    apply hlin
    filter_upwards [h] with w hw
    rw [hGdef] at hw
    exact sub_eq_zero.mp hw
  have htop : analyticOrderAt G 0 ≠ ⊤ := by
    intro h
    exact hGne ((analyticOrderAt_eq_top).mp h)
  -- the order of vanishing of the nonlinear part is at least `2`
  have hkge : 2 ≤ analyticOrderNatAt G 0 := by
    have h2 : (2 : ℕ∞) ≤ analyticOrderAt G 0 :=
      (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hG).mpr (by
        intro i hi
        interval_cases i
        · simp [iteratedDeriv_zero, hG0]
        · simp [iteratedDeriv_one, hderivG])
    rw [← Nat.cast_analyticOrderNatAt htop] at h2
    exact_mod_cast h2
  obtain ⟨g, hga, hg0ne, hgeq⟩ := (AnalyticAt.analyticOrderAt_ne_top hG).mp htop
  have key : IsLittleO (𝓝 0) (fun w : ℂ => G w - g 0 * w ^ (analyticOrderNatAt G 0))
      (fun w : ℂ => w ^ (analyticOrderNatAt G 0)) := by
    have hgtend : Tendsto (fun w : ℂ => g w - g 0) (𝓝 0) (𝓝 0) := by
      simpa using hga.continuousAt.tendsto.sub_const (g 0)
    have hsmall : (fun w : ℂ => g w - g 0) =o[𝓝 0] (fun _ : ℂ => (1:ℂ)) :=
      (isLittleO_one_iff ℂ).mpr hgtend
    have hmul :=
      (isBigO_refl (fun w : ℂ => w ^ (analyticOrderNatAt G 0)) (𝓝 0)).mul_isLittleO hsmall
    have hmain : (fun w : ℂ => w ^ (analyticOrderNatAt G 0) * (g w - g 0)) =o[𝓝 0]
        (fun w : ℂ => w ^ (analyticOrderNatAt G 0)) := by
      simpa using hmul
    have heq : (fun w : ℂ => w ^ (analyticOrderNatAt G 0) * (g w - g 0)) =ᶠ[𝓝 0]
        (fun w : ℂ => G w - g 0 * w ^ (analyticOrderNatAt G 0)) := by
      filter_upwards [hgeq] with w hw
      rw [hw]
      simp only [sub_zero, smul_eq_mul]
      ring
    exact hmain.congr' heq (EventuallyEq.refl _ _)
  refine ⟨analyticOrderNatAt G 0 - 1, g 0, by omega, hg0ne, ?_⟩
  have hk1 : analyticOrderNatAt G 0 - 1 + 1 = analyticOrderNatAt G 0 :=
    Nat.sub_add_cancel (by omega)
  rw [hk1]
  simpa [hGdef] using key

end Work.LandLeaves
