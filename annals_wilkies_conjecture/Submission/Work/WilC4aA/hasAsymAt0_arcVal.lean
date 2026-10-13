import Mathlib
import Submission.Work.WilC4aA.Defs

set_option linter.unusedVariables false

open Classical Topology Filter Set

namespace Work.WilC4aA

/-- **One-sided asymptotics of an analytic function of one real variable.**

If `g` is analytic at `0`, then either `g` vanishes identically on a right-neighbourhood of `0`,
or `g s / s ^ k` tends to a nonzero limit for some integer `k`.

Indeed, if `g` does not vanish identically near `0` then, writing `n` for its order of vanishing
and `g s = s ^ n * u s` with `u` analytic and `u 0 ≠ 0`
(`AnalyticAt.analyticOrderAt_ne_top`), one gets the limit `u 0` for the exponent `k = n`. -/
private theorem hasAsymAt0_of_analyticAt {g : ℝ → ℝ} (hg : AnalyticAt ℝ g 0) :
    HasAsymAt0 g := by
  rcases eq_or_ne (analyticOrderAt g 0) ⊤ with htop | htop
  · -- `g` vanishes identically near `0`, hence also along `0⁺`.
    left
    rw [analyticOrderAt_eq_top] at htop
    filter_upwards [htop.filter_mono nhdsWithin_le_nhds] with s hs
    exact hs
  · right
    obtain ⟨u, hu, hu0, hgu⟩ := (hg.analyticOrderAt_ne_top).mp htop
    refine ⟨(analyticOrderNatAt g 0 : ℤ), u 0, hu0, ?_⟩
    have hEq : (fun s : ℝ => g s / s ^ ((analyticOrderNatAt g 0 : ℤ) : ℝ))
        =ᶠ[𝓝[>] (0:ℝ)] u := by
      filter_upwards [self_mem_nhdsWithin, hgu.filter_mono nhdsWithin_le_nhds] with s hs hs2
      have hs0 : s ≠ 0 := ne_of_gt hs
      rw [hs2, sub_zero, Real.rpow_intCast, zpow_natCast]
      exact mul_div_cancel_left₀ (u s) (pow_ne_zero _ hs0)
    exact (hu.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' hEq.symm

/-- **One-sided asymptotics of the reciprocal of an analytic function of one real variable.**

If `g` is analytic at `0`, then either `g⁻¹` vanishes identically on a right-neighbourhood of `0`,
or `g s⁻¹ / s ^ k` tends to a nonzero limit for some integer `k`. The relevant exponent is
`-n`, where `n` is the order of vanishing of `g` at `0`. -/
private theorem hasAsymAt0_inv_of_analyticAt {g : ℝ → ℝ} (hg : AnalyticAt ℝ g 0) :
    HasAsymAt0 (fun s => (g s)⁻¹) := by
  rcases eq_or_ne (analyticOrderAt g 0) ⊤ with htop | htop
  · -- `g` vanishes identically near `0`, hence so does `g⁻¹`.
    left
    rw [analyticOrderAt_eq_top] at htop
    filter_upwards [htop.filter_mono nhdsWithin_le_nhds] with s hs
    simp [hs]
  · right
    obtain ⟨u, hu, hu0, hgu⟩ := (hg.analyticOrderAt_ne_top).mp htop
    refine ⟨-(analyticOrderNatAt g 0 : ℤ), (u 0)⁻¹, inv_ne_zero hu0, ?_⟩
    have hEq : (fun s : ℝ => (g s)⁻¹ / s ^ (((-(analyticOrderNatAt g 0 : ℤ) : ℤ) : ℝ)))
        =ᶠ[𝓝[>] (0:ℝ)] fun s => (u s)⁻¹ := by
      filter_upwards [self_mem_nhdsWithin, hgu.filter_mono nhdsWithin_le_nhds] with s hs hs2
      have hs0 : s ≠ 0 := ne_of_gt hs
      rw [hs2, sub_zero, Real.rpow_intCast, zpow_neg, zpow_natCast, div_inv_eq_mul]
      rw [smul_eq_mul, mul_inv_rev, mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hs0), mul_one]
    exact ((hu.continuousAt.inv₀ hu0).tendsto.mono_left nhdsWithin_le_nhds).congr' hEq.symm

/-- **The analytic asymptotics step of `C4a`.**  Along an analytic arc `γ` whose values lie in a
piece `P`, the value `arcVal P γ s` represented by `γ s` has one-sided asymptotics at `0⁺`.

Only the analyticity of `γ` is used: the component `s ↦ (γ s) 1` is analytic at `0` (it is a
continuous linear functional composed with `γ`), and an analytic function of one variable either
vanishes eventually at `0⁺` or behaves like `b s ^ k` with `b ≠ 0` and `k : ℤ`; taking the
reciprocal when `P.inv` is `true` merely negates the exponent. -/
theorem hasAsymAt0_arcVal {P : WilkiesDesign.CG.C4a.LiftPiece} (hP : P.Good)
    {γ : ℝ → Fin (P.m + 2) → ℝ} (hγan : AnalyticAt ℝ γ 0)
    (hγmem : ∀ᶠ s in nhdsWithin (0 : ℝ) (Set.Ioi 0), γ s ∈ P.set) :
    Work.WilC4aA.HasAsymAt0 (Work.WilC4aA.arcVal P γ) := by
  -- The `y`-coordinate of the arc is analytic at `0`.
  have hg : AnalyticAt ℝ (fun s => (γ s) 1) 0 :=
    ((ContinuousLinearMap.proj (1 : Fin (P.m + 2)) :
      (Fin (P.m + 2) → ℝ) →L[ℝ] ℝ).analyticAt (γ 0)).comp hγan
  rcases hb : P.inv with _ | _
  · -- Non-inverted piece: `arcVal P γ s = (γ s) 1`.
    rw [arcVal_of_false hb]
    exact hasAsymAt0_of_analyticAt hg
  · -- Inverted piece: `arcVal P γ s = ((γ s) 1)⁻¹`.
    rw [arcVal_of_true hb]
    exact hasAsymAt0_inv_of_analyticAt hg

end Work.WilC4aA
