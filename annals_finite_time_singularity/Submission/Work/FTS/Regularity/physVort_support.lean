import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.FTS.Regularity.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set

namespace Work.FTS.Regularity

/-! ## Compact support of the physical vorticity

The physical vorticity of the route is

  `physVort α A B g x τ = A(τ)⁻¹ · F(ρ(x)^{3α}/B(τ), θ(x), τ) · e_θ(x)`,

so it vanishes wherever the *profile* `F = F_* + g` does.  The interface `RegPkg` supplies the
compact support of the full profile in the self-similar variable `z`, uniformly on the strip
(`hsupp`), and the two-sided bound `B τ ≤ b₁` (`hBb`).  Hence the physical vorticity is supported
in a ball whose radius is controlled by `L · b₁` and the profile exponent `3α`.

The only two ingredients are (i) the dictionary between the profile of a `τ`-slice
(`ConstructionInstance.profile`) and the full profile `profFull`, and (ii) the elementary
observation that `t ^ s ≤ c` with `t ≥ 0`, `s > 0`, `c ≥ 0` forces `t ≤ max 1 (c ^ s⁻¹)`. -/

/-- The profile of a `τ`-slice agrees with the full profile `profFull` on the physical half plane
`0 ≤ θ`. -/
private lemma profile_gSlice_eq_profFull (α : ℝ) (g : ℝ → ℝ → ℝ → ℝ) (τ z θ : ℝ)
    (hθ : 0 ≤ θ) :
    Work.ConstructionInstance.profile (pExp α) (gSlice g τ) z θ = profFull α g z θ τ := by
  rw [Work.ConstructionInstance.profile_of_nonneg hθ]
  rfl

/-- Off the physical half plane `θ ≥ 0` the profile of a `τ`-slice is the odd extension of the
full profile. -/
private lemma profile_gSlice_eq_neg_profFull (α : ℝ) (g : ℝ → ℝ → ℝ → ℝ) (τ z θ : ℝ)
    (hθ : ¬ 0 ≤ θ) :
    Work.ConstructionInstance.profile (pExp α) (gSlice g τ) z θ
      = - profFull α g z (-θ) τ := by
  rw [Work.ConstructionInstance.profile_of_neg hθ]
  rfl

/-- If `t ≥ 0` and `t ^ s ≤ c` with `s > 0` and `c ≥ 0`, then `t ≤ max 1 (c ^ s⁻¹)`. -/
private lemma le_max_one_rpow_inv {s c t : ℝ} (hs : 0 < s) (_hc : 0 ≤ c) (ht : 0 ≤ t)
    (h : t ^ s ≤ c) : t ≤ max 1 (c ^ (1 / s)) := by
  rcases le_or_gt t 1 with h1 | h1
  · exact le_trans h1 (le_max_left _ _)
  · refine le_trans ?_ (le_max_right _ _)
    calc t = (t ^ s) ^ (1 / s) := by
          rw [← Real.rpow_mul ht s (1 / s), mul_one_div_cancel (ne_of_gt hs), Real.rpow_one]
      _ ≤ c ^ (1 / s) := Real.rpow_le_rpow (Real.rpow_nonneg ht s) h (by positivity)

/-- **The physical vorticity of a `RegPkg` profile is compactly supported, uniformly on the
strip `[0,S]`.**  The radius is `max 1 ((L · b₁) ^ (3α)⁻¹)`, where `L` bounds the support of the
full profile in `z` and `b₁` bounds the clock `B` above. -/
theorem physVort_support {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (h : Work.FTS.Regularity.RegPkg α S A B g) :
    ∃ R : ℝ, 0 < R ∧ ∀ τ ∈ Set.Icc 0 S, ∀ y : Work.FTS.Regularity.R3,
      Work.FTS.Regularity.physVort α A B g y τ ≠ 0 → y ∈ Metric.closedBall 0 R := by
  obtain ⟨L, hLpos, hL⟩ := h.hsupp
  obtain ⟨b₀, b₁, hb₀pos, hBb⟩ := h.hBb
  have h0 : (0 : ℝ) ∈ Set.Icc 0 S := ⟨le_rfl, h.hS.le⟩
  have hb₁pos : 0 < b₁ := lt_of_lt_of_le hb₀pos (le_trans (hBb 0 h0).1 (hBb 0 h0).2)
  refine ⟨max 1 ((L * b₁) ^ (1 / pExp α)), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro τ hτ y hy
  simp only [Metric.mem_closedBall, dist_eq_norm, sub_zero]
  -- the profile at the rescaled self-similar variable must be non-zero
  have hpne : Work.ConstructionInstance.profile (pExp α) (gSlice g τ)
      (Work.Cyl.rho y ^ pExp α / B τ) (Work.Cyl.theta y) ≠ 0 := by
    intro hz
    refine hy ?_
    rw [physVort_apply, Work.ConstructionInstance.omegaSz_apply, hz]
    simp
  -- hence the self-similar variable lies below the support radius `L`
  have hzL : Work.Cyl.rho y ^ pExp α / B τ ≤ L := by
    rcases le_or_gt 0 (Work.Cyl.theta y) with hθ | hθ
    · rw [profile_gSlice_eq_profFull α g τ _ _ hθ] at hpne
      by_contra hc
      exact hpne (hL τ hτ _ (Work.Cyl.theta y) (not_le.mp hc).le)
    · rw [profile_gSlice_eq_neg_profFull α g τ _ _ (not_le.mpr hθ), neg_ne_zero] at hpne
      by_contra hc
      exact hpne (hL τ hτ _ (-(Work.Cyl.theta y)) (not_le.mp hc).le)
  -- convert it into a bound on `ρ(y)`, using `B τ ≤ b₁`
  have hBτ : 0 < B τ := lt_of_lt_of_le hb₀pos (hBb τ hτ).1
  have hle : Work.Cyl.rho y ^ pExp α ≤ L * b₁ :=
    ((div_le_iff₀ hBτ).mp hzL).trans (mul_le_mul_of_nonneg_left (hBb τ hτ).2 hLpos.le)
  rw [← Work.Cyl.rho_eq_norm y]
  exact le_max_one_rpow_inv (pExp_pos h.hα) (mul_nonneg hLpos.le hb₁pos.le)
    (Work.Cyl.rho_nonneg y) hle

end Work.FTS.Regularity
