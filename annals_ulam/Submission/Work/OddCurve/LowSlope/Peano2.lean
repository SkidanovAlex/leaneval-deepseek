import Mathlib

/-!
# Second-order (Peano) expansions at a point

For `f : ℝ → ℝ` and real numbers `x₀ c₁ c₂`, the predicate `Peano2 f x₀ c₁ c₂` records the
*pointwise* second-order Taylor expansion (Peano form) of `f` at `x₀`:

  `f (x₀ + h) = f x₀ + c₁ * h + c₂ / 2 * h ^ 2 + o (h ^ 2)`   as `h → 0`.

This is the notion of "twice differentiable at the point `x₀`" that is stable under composition and
that does not require differentiability of `f` on a *neighbourhood* of `x₀`.  It is the right tool
when one only knows `HasDerivAt f c₁ x₀` and `HasDerivAt (deriv f) c₂ x₀` at a single point.

Main results (in the files `Peano2Mul`, `Peano2Comp`, `Peano2OfHasDerivAtDeriv`, `Peano2Sqrt`):

* `peano2_unique`  — the coefficients are determined by `f` and `x₀`;
* `peano2_congr`   — `Peano2` is invariant under eventual equality at `x₀`;
* `peano2_mul`     — product rule for Peano expansions;
* `peano2_comp`    — chain rule for Peano expansions;
* `peano2_of_hasDerivAt_deriv` — `HasDerivAt f c₁ x₀` plus `HasDerivAt (deriv f) c₂ x₀` give the
  Peano expansion, as soon as `(c₁, c₂) ≠ (0, 0)`;
* `peano2_sqrt_one_sub_sq` — the expansion of `v ↦ √(1 - v²)`.
-/

namespace Work.OddCurve.LowSlope

noncomputable section

open Filter Asymptotics
open scoped Topology

/-- `Peano2 f x₀ c₁ c₂` is the Peano (pointwise) second-order expansion of `f` at `x₀`:
`f (x₀ + h) = f x₀ + c₁ * h + c₂ / 2 * h ^ 2 + o (h ^ 2)`. -/
def Peano2 (f : ℝ → ℝ) (x₀ c₁ c₂ : ℝ) : Prop :=
  (fun h : ℝ => f (x₀ + h) - f x₀ - c₁ * h - c₂ / 2 * h ^ 2) =o[𝓝 0] fun h : ℝ => h ^ 2

theorem peano2_id (x₀ : ℝ) : Peano2 id x₀ 1 0 := by
  unfold Peano2
  have h : (fun h : ℝ => id (x₀ + h) - id x₀ - 1 * h - 0 / 2 * h ^ 2) = fun _ : ℝ => 0 := by
    funext h
    simp only [id_eq]
    ring
  rw [h]
  exact isLittleO_zero _ _

theorem peano2_const (x₀ c : ℝ) : Peano2 (fun _ : ℝ => c) x₀ 0 0 := by
  unfold Peano2
  have h : (fun h : ℝ =>
      (fun _ : ℝ => c) (x₀ + h) - (fun _ : ℝ => c) x₀ - 0 * h - 0 / 2 * h ^ 2)
      = fun _ : ℝ => 0 := by
    funext h
    simp
  rw [h]
  exact isLittleO_zero _ _

/-- `Peano2` is invariant under eventual equality at the base point. -/
theorem peano2_congr {f g : ℝ → ℝ} {x₀ c₁ c₂ : ℝ}
    (hfg : f =ᶠ[𝓝 x₀] g) (h : Peano2 f x₀ c₁ c₂) : Peano2 g x₀ c₁ c₂ := by
  have hx : f x₀ = g x₀ := Filter.EventuallyEq.eq_of_nhds hfg
  unfold Peano2 at h ⊢
  refine h.congr' ?_ EventuallyEq.rfl
  have ht : Tendsto (fun h : ℝ => x₀ + h) (𝓝 0) (𝓝 x₀) := by
    have h1 : Tendsto (fun _ : ℝ => x₀) (𝓝 0) (𝓝 x₀) := tendsto_const_nhds
    have h2 : Tendsto (fun h : ℝ => h) (𝓝 0) (𝓝 0) := tendsto_id'.2 le_rfl
    simpa using h1.add h2
  filter_upwards [ht.eventually hfg] with h hh
  rw [hh, hx]

/-- The coefficients of a Peano expansion are determined: uniqueness. -/
theorem peano2_unique {f : ℝ → ℝ} {x₀ c₁ c₂ c₁' c₂' : ℝ}
    (h : Peano2 f x₀ c₁ c₂) (h' : Peano2 f x₀ c₁' c₂') : c₁ = c₁' ∧ c₂ = c₂' := by
  unfold Peano2 at h h'
  -- the difference of the two error terms is `o (h ^ 2)`
  have hsub : (fun h : ℝ => (c₁ - c₁') * h + (c₂ - c₂') / 2 * h ^ 2) =o[𝓝 0]
      fun h : ℝ => h ^ 2 := by
    refine (h'.sub h).congr' ?_ EventuallyEq.rfl
    filter_upwards with h
    ring
  -- first coefficient: divide the relation by `h`
  have hb : ∀ᶠ h in 𝓝[≠] (0 : ℝ), |(c₁ - c₁') + (c₂ - c₂') / 2 * h| ≤ |h| := by
    have h1 : ∀ᶠ h in 𝓝 (0 : ℝ),
        ‖(c₁ - c₁') * h + (c₂ - c₂') / 2 * h ^ 2‖ ≤ 1 * ‖h ^ 2‖ := hsub.def one_pos
    have h1' : ∀ᶠ h in 𝓝[≠] (0 : ℝ),
        ‖(c₁ - c₁') * h + (c₂ - c₂') / 2 * h ^ 2‖ ≤ 1 * ‖h ^ 2‖ :=
      nhdsWithin_le_nhds h1
    filter_upwards [h1', self_mem_nhdsWithin] with h hh hne
    rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_pow] at hh
    have hfac : (c₁ - c₁') * h + (c₂ - c₂') / 2 * h ^ 2
        = h * ((c₁ - c₁') + (c₂ - c₂') / 2 * h) := by ring
    rw [hfac, abs_mul] at hh
    have hpos : 0 < |h| := abs_pos.mpr hne
    have hs : |h| ^ 2 = |h| * |h| := by ring
    rw [hs] at hh
    exact le_of_mul_le_mul_left hh hpos
  have hid : Tendsto (fun h : ℝ => h) (𝓝[≠] (0 : ℝ)) (𝓝 0) :=
    tendsto_id'.2 nhdsWithin_le_nhds
  have hlim1 : Tendsto (fun h : ℝ => |(c₁ - c₁') + (c₂ - c₂') / 2 * h|) (𝓝[≠] (0 : ℝ))
      (𝓝 |c₁ - c₁'|) := by
    have ht : Tendsto (fun h : ℝ => (c₁ - c₁') + (c₂ - c₂') / 2 * h) (𝓝[≠] (0 : ℝ))
        (𝓝 (c₁ - c₁')) := by
      have hc : Tendsto (fun h : ℝ => (c₂ - c₂') / 2 * h) (𝓝[≠] (0 : ℝ))
          (𝓝 ((c₂ - c₂') / 2 * 0)) := tendsto_const_nhds.mul hid
      simpa using tendsto_const_nhds.add hc
    exact (continuous_abs.tendsto (c₁ - c₁')).comp ht
  have hlim2 : Tendsto (fun h : ℝ => |h|) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    simpa only [Function.comp_def, abs_zero] using (continuous_abs.tendsto (0 : ℝ)).comp hid
  have hle : |c₁ - c₁'| ≤ 0 := le_of_tendsto_of_tendsto hlim1 hlim2 hb
  have hc1 : c₁ - c₁' = 0 := abs_eq_zero.mp (le_antisymm hle (abs_nonneg _))
  have hc1' : c₁ = c₁' := by linarith
  -- second coefficient
  have hsub2 : (fun h : ℝ => (c₂ - c₂') / 2 * h ^ 2) =o[𝓝 0] fun h : ℝ => h ^ 2 := by
    refine hsub.congr' ?_ EventuallyEq.rfl
    filter_upwards with h
    rw [hc1']
    ring
  have h1 : (fun h : ℝ => ((c₂ - c₂') / 2 * h ^ 2) * (h ^ 2)⁻¹) =o[𝓝[≠] (0 : ℝ)]
      fun h : ℝ => h ^ 2 * (h ^ 2)⁻¹ :=
    (hsub2.mono nhdsWithin_le_nhds).mul_isBigO (isBigO_refl (fun h : ℝ => (h ^ 2)⁻¹) _)
  have h2 : (fun _ : ℝ => (c₂ - c₂') / 2) =o[𝓝[≠] (0 : ℝ)] fun _ : ℝ => (1 : ℝ) := by
    refine h1.congr' ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with h hne
      have h2ne : h ^ 2 ≠ 0 := pow_ne_zero 2 hne
      rw [mul_assoc, mul_inv_cancel₀ h2ne, mul_one]
    · filter_upwards [self_mem_nhdsWithin] with h hne
      have h2ne : h ^ 2 ≠ 0 := pow_ne_zero 2 hne
      rw [mul_inv_cancel₀ h2ne]
  have hlim3 : Tendsto (fun _ : ℝ => (c₂ - c₂') / 2) (𝓝[≠] (0 : ℝ)) (𝓝 0) :=
    (isLittleO_one_iff ℝ).1 h2
  have hlim3' : Tendsto (fun _ : ℝ => (c₂ - c₂') / 2) (𝓝[≠] (0 : ℝ)) (𝓝 ((c₂ - c₂') / 2)) :=
    tendsto_const_nhds
  have hc2 : (c₂ - c₂') / 2 = 0 := tendsto_nhds_unique hlim3' hlim3
  exact ⟨hc1', by linarith⟩

end

end Work.OddCurve.LowSlope
