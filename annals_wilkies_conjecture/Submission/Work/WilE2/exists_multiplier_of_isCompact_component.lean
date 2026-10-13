import Mathlib

open Set Filter
open scoped Topology

namespace Work.WilE2

/-- **Lagrange multipliers on a compact component of a regular level set.**

Let `F : ℝ^m → ℝ` be `C¹`, `Γ` a nonempty compact subset of the zero set `{F = 0}` which
coincides with the zero set locally around each of its points (i.e. `Γ` is a union of connected
components of `{F = 0}`), and suppose the gradient of `F` never vanishes on the zero set.

Then some point `z ∈ Γ` has `∇F(z)` proportional to any prescribed direction `u`.

**Proof.** Maximise the linear functional `x ↦ ⟨u, x⟩` on the compact set `Γ`; let `z` be a
maximiser. Because `Γ` agrees with the zero set in a neighbourhood of `z`, `z` is a local
maximum of `⟨u, ·⟩` on the whole level set `{F = F z}`. Lagrange multipliers (Mathlib:
`IsLocalExtrOn.exists_multipliers_of_hasStrictFDerivAt_1d`) then give `a • dF_z + b • φ' = 0`
with `(a, b) ≠ 0`, where `φ'` is the (strict) derivative of the linear functional. Since
`dF_z ≠ 0`, necessarily `b ≠ 0`, and reading off values gives `⟨u, v⟩ = (-a/b) · dF_z v`. -/
theorem exists_multiplier_of_isCompact_component {m : ℕ} (F : (Fin m → ℝ) → ℝ) (u : Fin m → ℝ) (hF : ContDiff ℝ 1 F) (Γ : Set (Fin m → ℝ)) (hne : Γ.Nonempty) (hcomp : IsCompact Γ) (hsub : Γ ⊆ {x | F x = 0}) (hopen : ∀ z ∈ Γ, ∃ ε : ℝ, 0 < ε ∧ ∀ y : Fin m → ℝ, dist y z < ε → F y = 0 → y ∈ Γ) (hgrad : ∀ x, F x = 0 → fderiv ℝ F x ≠ 0) : ∃ z ∈ Γ, ∃ c : ℝ, ∀ v : Fin m → ℝ, dotProduct u v = c * fderiv ℝ F z v := by
  -- `φ` is the linear functional `x ↦ ⟨u, x⟩`, and `φ'` its (continuous linear) derivative.
  let φ : (Fin m → ℝ) → ℝ := fun x => dotProduct u x
  let φ' : (Fin m → ℝ) →L[ℝ] ℝ := ∑ i, u i • ContinuousLinearMap.proj i
  have hφ'apply : ∀ x : Fin m → ℝ, φ' x = dotProduct u x := by
    intro x
    simp [φ', dotProduct, ContinuousLinearMap.proj_apply, smul_eq_mul]
  have hφcont : Continuous φ := by
    have : φ = ⇑φ' := funext fun x => (hφ'apply x).symm
    rw [this]; exact φ'.continuous
  -- Maximise `φ` on the compact set `Γ`.
  obtain ⟨z, hzΓ, hzmax⟩ := hcomp.exists_isMaxOn hne hφcont.continuousOn
  have hzF : F z = 0 := hsub hzΓ
  -- `z` is a local maximum of `φ` on the level set `{F = F z}`.
  have hlocalmax : IsLocalMaxOn φ {x | F x = F z} z := by
    rw [IsLocalMaxOn]
    change ∀ᶠ x in nhdsWithin z {x | F x = F z}, φ x ≤ φ z
    rw [eventually_nhdsWithin_iff]
    obtain ⟨ε, hεpos, hε⟩ := hopen z hzΓ
    filter_upwards [Metric.ball_mem_nhds z hεpos] with x hx
    intro hxF
    exact hzmax (hε x (by simpa [Metric.mem_ball] using hx) (by rw [hxF, hzF]))
  have hextr : IsLocalExtrOn φ {x | F x = F z} z := Or.inr hlocalmax
  have hFstrict : HasStrictFDerivAt F (fderiv ℝ F z) z := hF.hasStrictFDerivAt (by norm_num)
  have hφ'strict : HasStrictFDerivAt φ φ' z := by
    have h : HasStrictFDerivAt (⇑φ') φ' z := φ'.hasStrictFDerivAt
    rwa [show (⇑φ') = φ from funext fun x => hφ'apply x] at h
  -- Lagrange multipliers.
  obtain ⟨a, b, hab, hlin⟩ := hextr.exists_multipliers_of_hasStrictFDerivAt_1d hFstrict hφ'strict
  have hbne : b ≠ 0 := by
    intro hb
    have hzero : a • fderiv ℝ F z = 0 := by simpa [hb] using hlin
    have ha : a ≠ 0 := by intro ha; exact hab (by simp [ha, hb])
    exact hgrad z hzF ((smul_eq_zero.mp hzero).resolve_left ha)
  refine ⟨z, hzΓ, -a/b, ?_⟩
  intro v
  have hv : a * (fderiv ℝ F z v) + b * (φ' v) = 0 := by
    have := congrArg (fun (L : (Fin m → ℝ) →L[ℝ] ℝ) => L v) hlin
    simpa using this
  have hkey : φ' v = (-a/b) * (fderiv ℝ F z v) := by
    have h1 : b * (φ' v) = -a * (fderiv ℝ F z v) := by linarith
    field_simp
    linarith
  rw [show dotProduct u v = φ' v from (hφ'apply v).symm, hkey]

end Work.WilE2
