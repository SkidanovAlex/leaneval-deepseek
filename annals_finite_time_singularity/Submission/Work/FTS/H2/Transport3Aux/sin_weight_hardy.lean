import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Submission.Work.FTS.H2.STBasic
import Submission.Work.FTS.H2.Transport3Aux.power_hardy_boundary

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.Transport3Aux

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# The `sin(2θ)`-weighted Hardy inequality on `[0,π/2]`

For `0 < β ≤ 1` and `φ` of class `C¹` on `[0,π/2]`,

* `∫_0^{π/2} φ² sin(2θ)^{β-1} ≤ (400/β²)(∫_0^{π/2} (φ')² sin(2θ)^{1-β} + φ(π/4)²)`,
* `∫_0^{π/2} φ² sin(2θ)^{β} ≤ 400 (∫_0^{π/2} (φ')² sin(2θ)^{1-β} + φ(π/4)²)`.

The two weights `sin(2θ)^{β-1}` and `sin(2θ)^{1-β}` are reciprocal, so the first inequality is the
weighted Hardy inequality with a boundary term at the *interior* point `θ = π/4`; the second is
its `L²`-counterpart with the (bounded) weight `sin(2θ)^β`.

The proof splits `(0,π/2)` at `π/4` and on each half uses the *power* weighted Hardy inequality
`power_hardy_boundary` together with Jordan's inequality `(4/π)θ ≤ sin(2θ) ≤ 1` on `[0,π/4]`
(and its mirror image on `[π/4,π/2]`, via `θ ↦ π/2 - θ`, under which `sin 2θ` is invariant).
-/

/-! ## Elementary pointwise facts on `[0,π/4]` -/

theorem four_div_pi_mul_le_sin_two (θ : ℝ) (hθ : θ ∈ Set.Icc 0 (Real.pi / 4)) :
    (4 / Real.pi) * θ ≤ Real.sin (2 * θ) := by
  have h2 : (2 / Real.pi) * (2 * θ) ≤ Real.sin (2 * θ) :=
    Real.mul_le_sin (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hc : (4 / Real.pi) * θ = (2 / Real.pi) * (2 * θ) := by ring
  rwa [hc]

theorem theta_le_quarter_sin_two (θ : ℝ) (hθ : θ ∈ Set.Icc 0 (Real.pi / 4)) :
    θ ≤ Real.pi / 4 * Real.sin (2 * θ) := by
  have h2 : (2 / Real.pi) * (2 * θ) ≤ Real.sin (2 * θ) :=
    Real.mul_le_sin (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hc : (Real.pi / 4) * ((2 / Real.pi) * (2 * θ)) = θ := by
    field_simp
    ring
  calc θ = (Real.pi / 4) * ((2 / Real.pi) * (2 * θ)) := hc.symm
    _ ≤ (Real.pi / 4) * Real.sin (2 * θ) := mul_le_mul_of_nonneg_left h2 (by positivity)

theorem sin_two_pos_of_quarter {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 4)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- `sin(2θ)^{β-1} ≤ (4/π)^{β-1} θ^{β-1}` on `(0,π/4]` for `β ≤ 1`. -/
theorem sin_rpow_sub_le_theta {β θ : ℝ} (hβ1 : β ≤ 1) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 4)) :
    (Real.sin (2 * θ)) ^ (β - 1) ≤ (4 / Real.pi) ^ (β - 1) * θ ^ (β - 1) := by
  have hJ : (4 / Real.pi) * θ ≤ Real.sin (2 * θ) :=
    four_div_pi_mul_le_sin_two θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hpos : 0 < (4 / Real.pi) * θ := by
    have h0 := hθ.1
    positivity
  have h1 : (Real.sin (2 * θ)) ^ (β - 1) ≤ ((4 / Real.pi) * θ) ^ (β - 1) :=
    Real.rpow_le_rpow_of_nonpos hpos hJ (by linarith)
  rwa [Real.mul_rpow (by positivity) (le_of_lt hθ.1)] at h1

/-- `θ^{β+1} ≤ (π/4)^{β+1} sin(2θ)^{1-β}` on `(0,π/4]` for `0 ≤ β`. -/
theorem theta_rpow_le_sin_rpow {β θ : ℝ} (hβ : 0 ≤ β) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 4)) :
    θ ^ (β + 1) ≤ (Real.pi / 4) ^ (β + 1) * (Real.sin (2 * θ)) ^ (1 - β) := by
  have hle := theta_le_quarter_sin_two θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hsin_pos : 0 < Real.sin (2 * θ) := sin_two_pos_of_quarter hθ
  have h1 : θ ^ (β + 1) ≤ (Real.pi / 4 * Real.sin (2 * θ)) ^ (β + 1) :=
    Real.rpow_le_rpow (le_of_lt hθ.1) hle (by linarith)
  rw [Real.mul_rpow (by positivity) (le_of_lt hsin_pos)] at h1
  have h2 : (Real.sin (2 * θ)) ^ (β + 1) ≤ (Real.sin (2 * θ)) ^ (1 - β) :=
    Real.rpow_le_rpow_of_exponent_ge hsin_pos (Real.sin_le_one _) (by linarith)
  calc θ ^ (β + 1) ≤ (Real.pi / 4) ^ (β + 1) * (Real.sin (2 * θ)) ^ (β + 1) := h1
    _ ≤ (Real.pi / 4) ^ (β + 1) * (Real.sin (2 * θ)) ^ (1 - β) :=
        mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg (by positivity) _)

/-- `sin(2θ)^β ≤ 1` on `(0,π/4]` for `0 ≤ β`. -/
theorem sin_rpow_le_one' {β θ : ℝ} (hβ : 0 ≤ β) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 4)) :
    (Real.sin (2 * θ)) ^ β ≤ 1 :=
  Real.rpow_le_one (le_of_lt (sin_two_pos_of_quarter hθ)) (Real.sin_le_one _) hβ

/-- `θ² ≤ (π/4)² sin(2θ)^{1-β}` on `(0,π/4]` for `-1 ≤ β`. -/
theorem theta_sq_le_quarter_sq_sin_rpow {β θ : ℝ} (hβ : -1 ≤ β)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 4)) :
    θ ^ 2 ≤ (Real.pi / 4) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β) := by
  have hle := theta_le_quarter_sin_two θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hsin_pos : 0 < Real.sin (2 * θ) := sin_two_pos_of_quarter hθ
  have h1 : θ ^ 2 ≤ (Real.pi / 4 * Real.sin (2 * θ)) ^ 2 := pow_le_pow_left₀ hθ.1.le hle 2
  rw [mul_pow] at h1
  have h2 : (Real.sin (2 * θ)) ^ 2 ≤ (Real.sin (2 * θ)) ^ (1 - β) := by
    rw [← Real.rpow_two]
    exact Real.rpow_le_rpow_of_exponent_ge hsin_pos (Real.sin_le_one _) (by linarith)
  calc θ ^ 2 ≤ (Real.pi / 4) ^ 2 * (Real.sin (2 * θ)) ^ 2 := h1
    _ ≤ (Real.pi / 4) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)

/-! ## Integrability helpers -/

/-- `sin(2θ)^p` is interval integrable on `[a,b] ⊆ [0,π/2]` for `p > -1`. -/
theorem II_sin_rpow_interval {p a b : ℝ} (hp : -1 < p) (hab : a ≤ b) (ha : 0 ≤ a)
    (hb : b ≤ Real.pi / 2) :
    IntervalIntegrable (fun θ : ℝ => (Real.sin (2 * θ)) ^ p) volume a b :=
  (Work.FTS.H2.intervalIntegrable_sin_rpow p hp).mono_set (by
    rw [Set.uIcc_of_le hab, Set.uIcc_of_le (by linarith [Real.pi_pos] : (0:ℝ) ≤ Real.pi / 2)]
    exact fun x hx => ⟨ha.trans hx.1, hx.2.trans hb⟩)

/-- A bounded continuous function times an interval integrable weight is interval integrable. -/
theorem II_mul_cont {a b : ℝ} {w u : ℝ → ℝ} (hw : IntervalIntegrable w volume a b)
    (hu : ContinuousOn u (Set.uIcc a b)) :
    IntervalIntegrable (fun θ : ℝ => u θ * w θ) volume a b :=
  IntervalIntegrable.congr (fun x _ => mul_comm (w x) (u x)) (hw.mul_continuousOn hu)

/-- On `[a,b] ⊆ [0,π/2]`, `deriv f` agrees a.e. with the continuous function
`derivWithin f [0,π/2]`; only the endpoint `π/2` is exceptional. -/
theorem deriv_ae_eq_derivWithin {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (ha : 0 ≤ a)
    (hb : b ≤ Real.pi / 2) :
    (fun x : ℝ => deriv f x)
      =ᵐ[volume.restrict (Set.uIoc a b)]
        (fun x : ℝ => derivWithin f (Set.Icc 0 (Real.pi / 2)) x) := by
  show ∀ᵐ x ∂(volume.restrict (Set.uIoc a b)),
    deriv f x = derivWithin f (Set.Icc 0 (Real.pi / 2)) x
  rw [MeasureTheory.ae_restrict_iff' measurableSet_uIoc, MeasureTheory.ae_iff]
  refine MeasureTheory.measure_mono_null ?_
    (Set.Finite.measure_zero (Set.finite_singleton (Real.pi / 2)) volume)
  intro x hx
  simp only [Set.mem_setOf_eq, not_imp, Set.mem_singleton_iff] at hx
  obtain ⟨hxin, hne⟩ := hx
  by_contra hxne
  rw [Set.uIoc_of_le hab, Set.mem_Ioc] at hxin
  have hxI : x ∈ Set.Ioo (0:ℝ) (Real.pi / 2) :=
    ⟨lt_of_le_of_lt ha hxin.1, lt_of_le_of_ne (le_trans hxin.2 hb) hxne⟩
  exact hne (derivWithin_of_mem_nhds
    (mem_of_superset (Ioo_mem_nhds hxI.1 hxI.2) Set.Ioo_subset_Icc_self)).symm

/-- The `deriv`-squared integrand against any interval integrable weight is interval integrable
on any `[a,b] ⊆ [0,π/2]`. -/
theorem II_deriv_sq_mul {a b : ℝ} (hab : a ≤ b) (ha : 0 ≤ a) (hb : b ≤ Real.pi / 2)
    {f w : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Icc 0 (Real.pi / 2)))
    (hw : IntervalIntegrable w volume a b) :
    IntervalIntegrable (fun θ : ℝ => (deriv f θ) ^ 2 * w θ) volume a b := by
  have hg : ContinuousOn (fun θ : ℝ => (derivWithin f (Set.Icc 0 (Real.pi / 2)) θ) ^ 2)
      (Set.uIcc a b) := by
    have hc := hf.continuousOn_derivWithin
      (uniqueDiffOn_Icc (by positivity : (0:ℝ) < Real.pi / 2)) le_rfl
    have hsub : Set.uIcc a b ⊆ Set.Icc 0 (Real.pi / 2) := by
      rw [Set.uIcc_of_le hab]
      exact fun x hx => ⟨ha.trans hx.1, hx.2.trans hb⟩
    exact (hc.mono hsub).pow 2
  have h1 : IntervalIntegrable
      (fun θ : ℝ => (derivWithin f (Set.Icc 0 (Real.pi / 2)) θ) ^ 2 * w θ) volume a b :=
    II_mul_cont hw hg
  refine h1.congr_ae ?_
  filter_upwards [deriv_ae_eq_derivWithin (f := f) hab ha hb] with x hx
  rw [hx]

/-- The `deriv`-squared integrand against a `sin(2θ)^p` weight is interval integrable on any
`[a,b] ⊆ [0,π/2]`. -/
theorem II_deriv_sq_mul_sin {a b p : ℝ} (hab : a ≤ b) (ha : 0 ≤ a) (hb : b ≤ Real.pi / 2)
    {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Icc 0 (Real.pi / 2))) (hp : -1 < p) :
    IntervalIntegrable (fun θ : ℝ => (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ p) volume a b :=
  II_deriv_sq_mul hab ha hb hf (II_sin_rpow_interval hp hab ha hb)

/-- Interval integrals do not see the endpoints: `F = G` on `Ioo a b` suffices. -/
theorem integral_congr_Ioo {a b : ℝ} (hab : a ≤ b) {F G : ℝ → ℝ}
    (h : ∀ x ∈ Set.Ioo a b, F x = G x) :
    (∫ x in a..b, F x) = ∫ x in a..b, G x := by
  refine intervalIntegral.integral_congr_ae ?_
  rw [MeasureTheory.ae_iff]
  refine MeasureTheory.measure_mono_null ?_ (Set.Finite.measure_zero (Set.finite_singleton b) volume)
  intro x hx
  simp only [Set.mem_setOf_eq, not_imp] at hx
  obtain ⟨hxin, hne⟩ := hx
  rw [Set.uIoc_of_le hab, Set.mem_Ioc] at hxin
  by_contra hxb
  have hxb' : x ≠ b := by simpa using hxb
  exact hne (h x ⟨hxin.1, lt_of_le_of_ne hxin.2 hxb'⟩)

/-! ## The mirror `θ ↦ π/2 - θ` -/

/-- The mirror substitution. -/
theorem integral_mirror_sub (g : ℝ → ℝ) :
    (∫ u in (0:ℝ)..(Real.pi / 4), g (Real.pi / 2 - u))
      = ∫ θ in (Real.pi / 4)..(Real.pi / 2), g θ := by
  have h := intervalIntegral.integral_comp_sub_left (a := (0:ℝ)) (b := Real.pi / 4) g
    (Real.pi / 2)
  rw [show (Real.pi / 2 - Real.pi / 4 : ℝ) = Real.pi / 4 by ring,
    show (Real.pi / 2 - 0 : ℝ) = Real.pi / 2 by ring] at h
  exact h

/-- The mirror of a `C¹` function on the closed quadrant. -/
theorem contDiffOn_mirror {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Icc 0 (Real.pi / 2))) :
    ContDiffOn ℝ 1 (fun u : ℝ => f (Real.pi / 2 - u)) (Set.Icc 0 (Real.pi / 2)) := by
  have h1 : ContDiffOn ℝ 1 (fun u : ℝ => Real.pi / 2 - u) (Set.Icc 0 (Real.pi / 2)) :=
    (contDiffOn_const (c := Real.pi / 2)).sub contDiffOn_id
  exact hf.comp h1 (fun x hx => ⟨by linarith [hx.2, Real.pi_pos], by linarith [hx.1]⟩)

/-- The derivative of the mirror: `(f (π/2 - u))' = -f'(π/2 - u)` on `(0,π/4)`. -/
theorem deriv_mirror {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Icc 0 (Real.pi / 2))) :
    ∀ u ∈ Set.Ioo (0:ℝ) (Real.pi / 4),
      deriv (fun u : ℝ => f (Real.pi / 2 - u)) u = -deriv f (Real.pi / 2 - u) := by
  intro u hu
  have hmem : Real.pi / 2 - u ∈ Set.Ioo (0:ℝ) (Real.pi / 2) :=
    ⟨by linarith [hu.2, Real.pi_pos], by linarith [hu.1]⟩
  have hnhds : Set.Icc (0:ℝ) (Real.pi / 2) ∈ 𝓝 (Real.pi / 2 - u) :=
    mem_of_superset (Ioo_mem_nhds hmem.1 hmem.2) Set.Ioo_subset_Icc_self
  have hd : HasDerivAt f (deriv f (Real.pi / 2 - u)) (Real.pi / 2 - u) :=
    (hf.contDiffAt hnhds).differentiableAt_one.hasDerivAt
  have h1 : HasDerivAt (fun u : ℝ => Real.pi / 2 - u) (-1) u := by
    have h := (hasDerivAt_id u).const_sub (Real.pi / 2)
    simpa using h
  have h2 : HasDerivAt (fun u : ℝ => f (Real.pi / 2 - u))
      (deriv f (Real.pi / 2 - u) * (-1)) u := hd.comp u h1
  rw [h2.deriv]
  ring

/-- The mirror identity for the `f²`-integral (`sin 2θ` is invariant under `θ ↦ π/2 - θ`). -/
theorem mirror_sq_sin_rpow (p : ℝ) (f : ℝ → ℝ) :
    (∫ u in (0:ℝ)..(Real.pi / 4), (f (Real.pi / 2 - u)) ^ 2 * (Real.sin (2 * u)) ^ p)
      = ∫ θ in (Real.pi / 4)..(Real.pi / 2), (f θ) ^ 2 * (Real.sin (2 * θ)) ^ p := by
  rw [← integral_mirror_sub (fun θ : ℝ => (f θ) ^ 2 * (Real.sin (2 * θ)) ^ p)]
  exact intervalIntegral.integral_congr (fun u _ => by
    rw [show 2 * (Real.pi / 2 - u) = Real.pi - 2 * u by ring, Real.sin_pi_sub])

/-- The mirror identity for the `(f')²`-integral. -/
theorem deriv_mirror_sq_integral {β : ℝ} {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (Set.Icc 0 (Real.pi / 2))) :
    (∫ u in (0:ℝ)..(Real.pi / 4),
        (deriv (fun u : ℝ => f (Real.pi / 2 - u)) u) ^ 2 * (Real.sin (2 * u)) ^ (1 - β))
      = ∫ θ in (Real.pi / 4)..(Real.pi / 2),
          (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β) := by
  rw [← integral_mirror_sub (fun θ : ℝ => (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β))]
  refine integral_congr_Ioo (by positivity : (0:ℝ) ≤ Real.pi / 4) (fun u hu => ?_)
  rw [deriv_mirror hf u hu]
  have hsin : Real.sin (2 * (Real.pi / 2 - u)) = Real.sin (2 * u) := by
    rw [show 2 * (Real.pi / 2 - u) = Real.pi - 2 * u by ring, Real.sin_pi_sub]
  rw [hsin]
  ring

/-! ## The numeric constants -/

/-- `(4/π)^{β-1}(π/4)^{β+1} = (π/4)²`. -/
theorem rpow_quarter_mul (β : ℝ) :
    (4 / Real.pi) ^ (β - 1) * (Real.pi / 4) ^ (β + 1) = (Real.pi / 4) ^ 2 := by
  have hp : (0:ℝ) < Real.pi / 4 := by positivity
  have h1 : (4 / Real.pi) = (Real.pi / 4)⁻¹ := (inv_div Real.pi 4).symm
  rw [h1, Real.inv_rpow (le_of_lt hp), ← Real.rpow_neg (le_of_lt hp) (β - 1),
    ← Real.rpow_add hp, show -(β - 1) + (β + 1) = 2 by ring, Real.rpow_two]

/-- `(4/π)^{β-1}(π/4)^{β} = π/4`. -/
theorem rpow_quarter_mul' (β : ℝ) :
    (4 / Real.pi) ^ (β - 1) * (Real.pi / 4) ^ β = Real.pi / 4 := by
  have hp : (0:ℝ) < Real.pi / 4 := by positivity
  have h1 : (4 / Real.pi) = (Real.pi / 4)⁻¹ := (inv_div Real.pi 4).symm
  rw [h1, Real.inv_rpow (le_of_lt hp), ← Real.rpow_neg (le_of_lt hp) (β - 1),
    ← Real.rpow_add hp, show -(β - 1) + β = 1 by ring, Real.rpow_one]

/-- `(4/π)^{β-1}·(4/β²)·(π/4)^{β+1} = (4/β²)·(π/4)²`. -/
theorem quarter_const_mul (β : ℝ) :
    (4 / Real.pi) ^ (β - 1) * (4 / β ^ 2) * (Real.pi / 4) ^ (β + 1)
      = 4 / β ^ 2 * (Real.pi / 4) ^ 2 := by
  rw [mul_comm ((4 / Real.pi) ^ (β - 1)) (4 / β ^ 2), mul_assoc, rpow_quarter_mul β]

/-- `(4/π)^{β-1}·(2/β)·(π/4)^{β} = π/(2β)`. -/
theorem bdry_const_mul {β : ℝ} (hβ : β ≠ 0) :
    (4 / Real.pi) ^ (β - 1) * (2 / β) * (Real.pi / 4) ^ β = Real.pi / (2 * β) := by
  rw [mul_comm ((4 / Real.pi) ^ (β - 1)) (2 / β), mul_assoc, rpow_quarter_mul' β]
  field_simp
  ring

/-! ## The two half-interval Hardy estimates on `[0,π/4]` -/

/-- **The `sin(2θ)^{β-1}`-Hardy estimate on the left half.** -/
theorem hardy_half_a {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (Set.Icc 0 (Real.pi / 2))) :
    (∫ θ in (0:ℝ)..(Real.pi / 4), (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (β - 1))
      ≤ 4 / β ^ 2 * (Real.pi / 4) ^ 2
          * (∫ θ in (0:ℝ)..(Real.pi / 4),
              (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β))
        + Real.pi / (2 * β) * (f (Real.pi / 4)) ^ 2 := by
  have hbpos : (0:ℝ) < Real.pi / 4 := by positivity
  have hb0 : (0:ℝ) ≤ Real.pi / 4 := hbpos.le
  have hble : Real.pi / 4 ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have hsub : Set.Icc (0:ℝ) (Real.pi / 4) ⊆ Set.Icc 0 (Real.pi / 2) :=
    fun x hx => ⟨hx.1, by linarith [hx.2, Real.pi_pos]⟩
  have hcf : ContinuousOn (fun θ : ℝ => (f θ) ^ 2) (Set.uIcc 0 (Real.pi / 4)) := by
    rw [Set.uIcc_of_le hb0]
    exact (hf.continuousOn.mono hsub).pow 2
  -- the power-weighted Hardy inequality on `[0,π/4]` with exponent `β-1`
  have hH := power_hardy_boundary (a := β - 1) (b := Real.pi / 4) (by linarith) hbpos
    (hf.mono hsub)
  have hH' : (∫ t in (0:ℝ)..(Real.pi / 4), f t ^ 2 * t ^ (β - 1))
      ≤ (4 / β ^ 2) * (∫ t in (0:ℝ)..(Real.pi / 4), (deriv f t) ^ 2 * t ^ (β + 1))
        + (2 / β) * (Real.pi / 4) ^ β * (f (Real.pi / 4)) ^ 2 := by
    rw [show β - 1 + 1 = β from by ring, show β - 1 + 2 = β + 1 from by ring] at hH
    exact hH
  -- integrability
  have hII_sin1 : IntervalIntegrable (fun θ : ℝ => (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (β - 1))
      volume 0 (Real.pi / 4) :=
    II_mul_cont (II_sin_rpow_interval (by linarith : -1 < β - 1) hb0 le_rfl hble) hcf
  have hII_pow1 : IntervalIntegrable (fun θ : ℝ => (f θ) ^ 2 * θ ^ (β - 1))
      volume 0 (Real.pi / 4) :=
    II_mul_cont (intervalIntegral.intervalIntegrable_rpow' (a := (0:ℝ))
      (b := Real.pi / 4) (r := β - 1) (by linarith)) hcf
  have hII_pow2 : IntervalIntegrable (fun θ : ℝ => (deriv f θ) ^ 2 * θ ^ (β + 1))
      volume 0 (Real.pi / 4) :=
    II_deriv_sq_mul hb0 le_rfl hble hf
      (intervalIntegral.intervalIntegrable_rpow' (a := (0:ℝ)) (b := Real.pi / 4)
        (r := β + 1) (by linarith))
  have hII_sin2 : IntervalIntegrable
      (fun θ : ℝ => (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β)) volume 0 (Real.pi / 4) :=
    II_deriv_sq_mul_sin hb0 le_rfl hble hf (by linarith : -1 < 1 - β)
  -- the two weight comparisons
  have hcmp1 : (∫ θ in (0:ℝ)..(Real.pi / 4), (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (β - 1))
      ≤ (4 / Real.pi) ^ (β - 1) * ∫ θ in (0:ℝ)..(Real.pi / 4), (f θ) ^ 2 * θ ^ (β - 1) := by
    have hpt : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi / 4),
        (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (β - 1)
          ≤ (4 / Real.pi) ^ (β - 1) * ((f θ) ^ 2 * θ ^ (β - 1)) := by
      intro θ hθ
      have h := sin_rpow_sub_le_theta (β := β) hβ1 hθ
      calc (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (β - 1)
          ≤ (f θ) ^ 2 * ((4 / Real.pi) ^ (β - 1) * θ ^ (β - 1)) :=
            mul_le_mul_of_nonneg_left h (sq_nonneg _)
        _ = (4 / Real.pi) ^ (β - 1) * ((f θ) ^ 2 * θ ^ (β - 1)) := by ring
    exact (intervalIntegral.integral_mono_on_of_le_Ioo hb0 hII_sin1
      (hII_pow1.const_mul _) hpt).trans_eq (intervalIntegral.integral_const_mul _ _)
  have hcmp2 : (∫ θ in (0:ℝ)..(Real.pi / 4), (deriv f θ) ^ 2 * θ ^ (β + 1))
      ≤ (Real.pi / 4) ^ (β + 1)
        * ∫ θ in (0:ℝ)..(Real.pi / 4), (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β) := by
    have hpt : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi / 4),
        (deriv f θ) ^ 2 * θ ^ (β + 1)
          ≤ (Real.pi / 4) ^ (β + 1)
            * ((deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β)) := by
      intro θ hθ
      have h := theta_rpow_le_sin_rpow (β := β) hβ.le hθ
      calc (deriv f θ) ^ 2 * θ ^ (β + 1)
          ≤ (deriv f θ) ^ 2 * ((Real.pi / 4) ^ (β + 1) * (Real.sin (2 * θ)) ^ (1 - β)) :=
            mul_le_mul_of_nonneg_left h (sq_nonneg _)
        _ = (Real.pi / 4) ^ (β + 1) * ((deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β)) := by
            ring
    exact (intervalIntegral.integral_mono_on_of_le_Ioo hb0 hII_pow2
      (hII_sin2.const_mul _) hpt).trans_eq (intervalIntegral.integral_const_mul _ _)
  -- assembly
  have hd : (0:ℝ) ≤ 4 / β ^ 2 := by positivity
  have hc1 : (0:ℝ) ≤ (4 / Real.pi) ^ (β - 1) := Real.rpow_nonneg (by positivity) _
  calc (∫ θ in (0:ℝ)..(Real.pi / 4), (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (β - 1))
      ≤ (4 / Real.pi) ^ (β - 1) * ∫ θ in (0:ℝ)..(Real.pi / 4), (f θ) ^ 2 * θ ^ (β - 1) :=
        hcmp1
    _ ≤ (4 / Real.pi) ^ (β - 1)
          * ((4 / β ^ 2) * (∫ θ in (0:ℝ)..(Real.pi / 4), (deriv f θ) ^ 2 * θ ^ (β + 1))
            + (2 / β) * (Real.pi / 4) ^ β * (f (Real.pi / 4)) ^ 2) :=
        mul_le_mul_of_nonneg_left hH' hc1
    _ ≤ (4 / Real.pi) ^ (β - 1)
          * ((4 / β ^ 2) * ((Real.pi / 4) ^ (β + 1)
              * (∫ θ in (0:ℝ)..(Real.pi / 4),
                  (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β)))
            + (2 / β) * (Real.pi / 4) ^ β * (f (Real.pi / 4)) ^ 2) := by
        have hmid : (4 / β ^ 2) * (∫ θ in (0:ℝ)..(Real.pi / 4),
                (deriv f θ) ^ 2 * θ ^ (β + 1))
              + (2 / β) * (Real.pi / 4) ^ β * (f (Real.pi / 4)) ^ 2
            ≤ (4 / β ^ 2) * ((Real.pi / 4) ^ (β + 1)
                * (∫ θ in (0:ℝ)..(Real.pi / 4),
                    (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β)))
              + (2 / β) * (Real.pi / 4) ^ β * (f (Real.pi / 4)) ^ 2 := by
          have h := mul_le_mul_of_nonneg_left hcmp2 hd
          linarith [h]
        exact mul_le_mul_of_nonneg_left hmid hc1
    _ = 4 / β ^ 2 * (Real.pi / 4) ^ 2
          * (∫ θ in (0:ℝ)..(Real.pi / 4),
              (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β))
        + Real.pi / (2 * β) * (f (Real.pi / 4)) ^ 2 := by
        rw [show (4 / Real.pi) ^ (β - 1)
              * ((4 / β ^ 2) * ((Real.pi / 4) ^ (β + 1)
                  * (∫ θ in (0:ℝ)..(Real.pi / 4),
                      (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β)))
                + (2 / β) * (Real.pi / 4) ^ β * (f (Real.pi / 4)) ^ 2)
            = (4 / Real.pi) ^ (β - 1) * (4 / β ^ 2) * (Real.pi / 4) ^ (β + 1)
                * (∫ θ in (0:ℝ)..(Real.pi / 4),
                    (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β))
              + (4 / Real.pi) ^ (β - 1) * (2 / β) * (Real.pi / 4) ^ β
                  * (f (Real.pi / 4)) ^ 2 from by ring,
          quarter_const_mul β, bdry_const_mul hβ.ne']

/-- **The `sin(2θ)^β`-estimate on the left half** (`sin^β ≤ 1` + Poincaré–Hardy with `a = 0`). -/
theorem hardy_half_b {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (Set.Icc 0 (Real.pi / 2))) :
    (∫ θ in (0:ℝ)..(Real.pi / 4), (f θ) ^ 2 * (Real.sin (2 * θ)) ^ β)
      ≤ 4 * (Real.pi / 4) ^ 2
          * (∫ θ in (0:ℝ)..(Real.pi / 4),
              (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β))
        + 2 * (Real.pi / 4) * (f (Real.pi / 4)) ^ 2 := by
  have hbpos : (0:ℝ) < Real.pi / 4 := by positivity
  have hb0 : (0:ℝ) ≤ Real.pi / 4 := hbpos.le
  have hble : Real.pi / 4 ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have hsub : Set.Icc (0:ℝ) (Real.pi / 4) ⊆ Set.Icc 0 (Real.pi / 2) :=
    fun x hx => ⟨hx.1, by linarith [hx.2, Real.pi_pos]⟩
  have hcf : ContinuousOn (fun θ : ℝ => (f θ) ^ 2) (Set.uIcc 0 (Real.pi / 4)) := by
    rw [Set.uIcc_of_le hb0]
    exact (hf.continuousOn.mono hsub).pow 2
  -- step 1: `sin(2θ)^β ≤ 1`
  have hstep1 : (∫ θ in (0:ℝ)..(Real.pi / 4), (f θ) ^ 2 * (Real.sin (2 * θ)) ^ β)
      ≤ ∫ θ in (0:ℝ)..(Real.pi / 4), (f θ) ^ 2 := by
    have hIL : IntervalIntegrable (fun θ : ℝ => (f θ) ^ 2 * (Real.sin (2 * θ)) ^ β)
        volume 0 (Real.pi / 4) :=
      II_mul_cont (II_sin_rpow_interval (by linarith : -1 < β) hb0 le_rfl hble) hcf
    have hpt : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi / 4),
        (f θ) ^ 2 * (Real.sin (2 * θ)) ^ β ≤ (f θ) ^ 2 := by
      intro θ hθ
      calc (f θ) ^ 2 * (Real.sin (2 * θ)) ^ β ≤ (f θ) ^ 2 * 1 :=
            mul_le_mul_of_nonneg_left (sin_rpow_le_one' hβ.le hθ) (sq_nonneg _)
        _ = (f θ) ^ 2 := by ring
    exact intervalIntegral.integral_mono_on_of_le_Ioo hb0 hIL hcf.intervalIntegrable hpt
  -- step 2: the power Hardy inequality with `a = 0`
  have hstep2 : (∫ θ in (0:ℝ)..(Real.pi / 4), (f θ) ^ 2)
      ≤ 4 * (∫ θ in (0:ℝ)..(Real.pi / 4), (deriv f θ) ^ 2 * θ ^ 2)
        + 2 * (Real.pi / 4) * (f (Real.pi / 4)) ^ 2 := by
    have hH := power_hardy_boundary (a := 0) (b := Real.pi / 4) (by norm_num) hbpos
      (hf.mono hsub)
    rw [show (0:ℝ) + 1 = 1 from by ring, show (0:ℝ) + 2 = 2 from by ring,
      show (4:ℝ) / 1 ^ 2 = 4 from by norm_num] at hH
    simp only [Real.rpow_zero, mul_one, Real.rpow_one, Real.rpow_two, div_one] at hH
    exact hH
  -- step 3: `θ² ≤ (π/4)² sin(2θ)^{1-β}`
  have hstep3 : (∫ θ in (0:ℝ)..(Real.pi / 4), (deriv f θ) ^ 2 * θ ^ 2)
      ≤ (Real.pi / 4) ^ 2
        * ∫ θ in (0:ℝ)..(Real.pi / 4), (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β) := by
    have hII3 : IntervalIntegrable (fun θ : ℝ => (deriv f θ) ^ 2 * θ ^ 2)
        volume 0 (Real.pi / 4) :=
      II_deriv_sq_mul hb0 le_rfl hble hf
        ((continuous_id.pow 2).continuousOn.intervalIntegrable)
    have hII4 : IntervalIntegrable
        (fun θ : ℝ => (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β)) volume 0 (Real.pi / 4) :=
      II_deriv_sq_mul_sin hb0 le_rfl hble hf (by linarith : -1 < 1 - β)
    have hpt : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi / 4),
        (deriv f θ) ^ 2 * θ ^ 2
          ≤ (Real.pi / 4) ^ 2 * ((deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β)) := by
      intro θ hθ
      have h := theta_sq_le_quarter_sq_sin_rpow (β := β) (by linarith) hθ
      calc (deriv f θ) ^ 2 * θ ^ 2
          ≤ (deriv f θ) ^ 2 * ((Real.pi / 4) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β)) :=
            mul_le_mul_of_nonneg_left h (sq_nonneg _)
        _ = (Real.pi / 4) ^ 2 * ((deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β)) := by ring
    exact (intervalIntegral.integral_mono_on_of_le_Ioo hb0 hII3
      (hII4.const_mul _) hpt).trans_eq (intervalIntegral.integral_const_mul _ _)
  calc (∫ θ in (0:ℝ)..(Real.pi / 4), (f θ) ^ 2 * (Real.sin (2 * θ)) ^ β)
      ≤ ∫ θ in (0:ℝ)..(Real.pi / 4), (f θ) ^ 2 := hstep1
    _ ≤ 4 * (∫ θ in (0:ℝ)..(Real.pi / 4), (deriv f θ) ^ 2 * θ ^ 2)
          + 2 * (Real.pi / 4) * (f (Real.pi / 4)) ^ 2 := hstep2
    _ ≤ 4 * ((Real.pi / 4) ^ 2
            * ∫ θ in (0:ℝ)..(Real.pi / 4),
                (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β))
          + 2 * (Real.pi / 4) * (f (Real.pi / 4)) ^ 2 :=
        add_le_add (mul_le_mul_of_nonneg_left hstep3 (by norm_num))
          (le_refl (2 * (Real.pi / 4) * (f (Real.pi / 4)) ^ 2))
    _ = 4 * (Real.pi / 4) ^ 2
          * (∫ θ in (0:ℝ)..(Real.pi / 4),
              (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β))
        + 2 * (Real.pi / 4) * (f (Real.pi / 4)) ^ 2 := by ring

/-! ## The assembly -/

/-- `sin(2θ)^q ≥ 0` on `[0,π/2]`. -/
theorem sin_two_nonneg_Icc {θ : ℝ} (hθ : θ ∈ Set.Icc 0 (Real.pi / 2)) :
    0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

theorem sin_weight_hardy {β : ℝ} {φ : ℝ → ℝ}
    (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hφ : ContDiffOn ℝ 1 φ (Set.Icc 0 (Real.pi / 2))) :
    (∫ θ in (0:ℝ)..(Real.pi/2), (φ θ)^2 * (Real.sin (2*θ))^(β - 1)
        ≤ 400 / β^2 * (∫ θ in (0:ℝ)..(Real.pi/2), (deriv φ θ)^2 * (Real.sin (2*θ))^(1 - β)
            + (φ (Real.pi/4))^2))
    ∧ (∫ θ in (0:ℝ)..(Real.pi/2), (φ θ)^2 * (Real.sin (2*θ))^β
        ≤ 400 * (∫ θ in (0:ℝ)..(Real.pi/2), (deriv φ θ)^2 * (Real.sin (2*θ))^(1 - β)
            + (φ (Real.pi/4))^2)) := by
  have hb0 : (0:ℝ) ≤ Real.pi / 4 := by positivity
  have hb2 : Real.pi / 4 ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have hp2 : (0:ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have hc2nn : (0:ℝ) ≤ (φ (Real.pi / 4)) ^ 2 := sq_nonneg _
  -- the four half-interval bounds
  have hA1 := hardy_half_a (f := φ) hβ hβ1 hφ
  have hB1b := hardy_half_b (f := φ) hβ hβ1 hφ
  have hA2 : (∫ θ in (Real.pi / 4)..(Real.pi / 2), (φ θ) ^ 2 * (Real.sin (2 * θ)) ^ (β - 1))
      ≤ 4 / β ^ 2 * (Real.pi / 4) ^ 2
          * (∫ θ in (Real.pi / 4)..(Real.pi / 2),
              (deriv φ θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β))
        + Real.pi / (2 * β) * (φ (Real.pi / 4)) ^ 2 := by
    have hm := hardy_half_a (f := fun u : ℝ => φ (Real.pi / 2 - u)) hβ hβ1
      (contDiffOn_mirror hφ)
    rw [show Real.pi / 2 - Real.pi / 4 = Real.pi / 4 by ring] at hm
    rw [mirror_sq_sin_rpow (β - 1) φ, deriv_mirror_sq_integral (β := β) hφ] at hm
    exact hm
  have hB2b : (∫ θ in (Real.pi / 4)..(Real.pi / 2), (φ θ) ^ 2 * (Real.sin (2 * θ)) ^ β)
      ≤ 4 * (Real.pi / 4) ^ 2
          * (∫ θ in (Real.pi / 4)..(Real.pi / 2),
              (deriv φ θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β))
        + 2 * (Real.pi / 4) * (φ (Real.pi / 4)) ^ 2 := by
    have hm := hardy_half_b (f := fun u : ℝ => φ (Real.pi / 2 - u)) hβ hβ1
      (contDiffOn_mirror hφ)
    rw [show Real.pi / 2 - Real.pi / 4 = Real.pi / 4 by ring] at hm
    rw [mirror_sq_sin_rpow β φ, deriv_mirror_sq_integral (β := β) hφ] at hm
    exact hm
  -- integrability, so that the two halves add up to the whole
  have hcontφ : ContinuousOn (fun θ : ℝ => (φ θ) ^ 2) (Set.uIcc 0 (Real.pi / 2)) := by
    rw [Set.uIcc_of_le hp2]
    exact hφ.continuousOn.pow 2
  have hAint : IntervalIntegrable (fun θ : ℝ => (φ θ) ^ 2 * (Real.sin (2 * θ)) ^ (β - 1))
      volume 0 (Real.pi / 2) :=
    II_mul_cont (II_sin_rpow_interval (by linarith : -1 < β - 1) hp2 le_rfl le_rfl) hcontφ
  have hsub01 : Set.uIcc 0 (Real.pi / 4) ⊆ Set.uIcc 0 (Real.pi / 2) := by
    rw [Set.uIcc_of_le hb0, Set.uIcc_of_le hp2]
    exact fun x hx => ⟨hx.1, le_trans hx.2 hb2⟩
  have hsub12 : Set.uIcc (Real.pi / 4) (Real.pi / 2) ⊆ Set.uIcc 0 (Real.pi / 2) := by
    rw [Set.uIcc_of_le hb2, Set.uIcc_of_le hp2]
    exact fun x hx => ⟨le_trans hb0 hx.1, hx.2⟩
  have hAintL : IntervalIntegrable (fun θ : ℝ => (φ θ) ^ 2 * (Real.sin (2 * θ)) ^ (β - 1))
      volume 0 (Real.pi / 4) :=
    II_mul_cont (II_sin_rpow_interval (by linarith : -1 < β - 1) hb0 le_rfl hb2)
      (hcontφ.mono hsub01)
  have hAintR : IntervalIntegrable (fun θ : ℝ => (φ θ) ^ 2 * (Real.sin (2 * θ)) ^ (β - 1))
      volume (Real.pi / 4) (Real.pi / 2) :=
    II_mul_cont (II_sin_rpow_interval (by linarith : -1 < β - 1) hb2 hb0 le_rfl)
      (hcontφ.mono hsub12)
  have hMintL : IntervalIntegrable (fun θ : ℝ => (φ θ) ^ 2 * (Real.sin (2 * θ)) ^ β)
      volume 0 (Real.pi / 4) :=
    II_mul_cont (II_sin_rpow_interval (by linarith : -1 < β) hb0 le_rfl hb2) (hcontφ.mono hsub01)
  have hMintR : IntervalIntegrable (fun θ : ℝ => (φ θ) ^ 2 * (Real.sin (2 * θ)) ^ β)
      volume (Real.pi / 4) (Real.pi / 2) :=
    II_mul_cont (II_sin_rpow_interval (by linarith : -1 < β) hb2 hb0 le_rfl) (hcontφ.mono hsub12)
  have hDint := II_deriv_sq_mul_sin hb0 le_rfl hb2 hφ (by linarith : -1 < 1 - β)
  have hDintFull : IntervalIntegrable
      (fun θ : ℝ => (deriv φ θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β)) volume 0 (Real.pi / 2) :=
    II_deriv_sq_mul_sin hp2 le_rfl le_rfl hφ (by linarith : -1 < 1 - β)
  have hsplitA : (∫ θ in (0:ℝ)..(Real.pi / 2), (φ θ) ^ 2 * (Real.sin (2 * θ)) ^ (β - 1))
      = (∫ θ in (0:ℝ)..(Real.pi / 4), (φ θ) ^ 2 * (Real.sin (2 * θ)) ^ (β - 1))
        + ∫ θ in (Real.pi / 4)..(Real.pi / 2), (φ θ) ^ 2 * (Real.sin (2 * θ)) ^ (β - 1) :=
    (intervalIntegral.integral_add_adjacent_intervals hAintL hAintR).symm
  have hsplitM : (∫ θ in (0:ℝ)..(Real.pi / 2), (φ θ) ^ 2 * (Real.sin (2 * θ)) ^ β)
      = (∫ θ in (0:ℝ)..(Real.pi / 4), (φ θ) ^ 2 * (Real.sin (2 * θ)) ^ β)
        + ∫ θ in (Real.pi / 4)..(Real.pi / 2), (φ θ) ^ 2 * (Real.sin (2 * θ)) ^ β :=
    (intervalIntegral.integral_add_adjacent_intervals hMintL hMintR).symm
  have hsplitD : (∫ θ in (0:ℝ)..(Real.pi / 2),
        (deriv φ θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β))
      = (∫ θ in (0:ℝ)..(Real.pi / 4), (deriv φ θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β))
        + ∫ θ in (Real.pi / 4)..(Real.pi / 2),
            (deriv φ θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β) :=
    (intervalIntegral.integral_add_adjacent_intervals hDint
      (II_deriv_sq_mul_sin hb2 hb0 le_rfl hφ (by linarith : -1 < 1 - β))).symm
  have hDnn : (0:ℝ) ≤ ∫ θ in (0:ℝ)..(Real.pi / 4),
      (deriv φ θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β) :=
    intervalIntegral.integral_nonneg hb0 (fun u hu =>
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg
        (sin_two_nonneg_Icc ⟨hu.1, by linarith [hu.2, Real.pi_pos]⟩) _))
  have hDnn' : (0:ℝ) ≤ ∫ θ in (Real.pi / 4)..(Real.pi / 2),
      (deriv φ θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β) :=
    intervalIntegral.integral_nonneg hb2 (fun u hu =>
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg
        (sin_two_nonneg_Icc ⟨by linarith [hu.1, Real.pi_pos], hu.2⟩) _))
  -- the numeric comparisons
  have hcoef1 : (4 / β ^ 2) * (Real.pi / 4) ^ 2 ≤ 400 / β ^ 2 := by
    have hpi : 4 * (Real.pi / 4) ^ 2 ≤ 400 := by nlinarith [Real.pi_le_four, Real.pi_pos]
    calc (4 / β ^ 2) * (Real.pi / 4) ^ 2 = (4 * (Real.pi / 4) ^ 2) / β ^ 2 := by ring
      _ ≤ 400 / β ^ 2 := by
          exact div_le_div_of_nonneg_right hpi (by positivity)
  have hcoef2 : Real.pi / (2 * β) + Real.pi / (2 * β) ≤ (400 / β ^ 2) * (Real.pi / 2) := by
    have h1 : Real.pi / (2 * β) + Real.pi / (2 * β) = Real.pi / β := by
      field_simp
      ring
    rw [h1, div_le_iff₀ hβ]
    have h3 : (400 / β ^ 2) * (Real.pi / 2) * β = 200 * Real.pi / β := by
      field_simp
      ring
    rw [h3, le_div_iff₀ hβ]
    nlinarith [Real.pi_pos, hβ1]
  have hcoef3 : 4 * (Real.pi / 4) ^ 2 ≤ 400 := by nlinarith [Real.pi_le_four, Real.pi_pos]
  have hcoef4 : 2 * (Real.pi / 4) + 2 * (Real.pi / 4) ≤ 400 * (Real.pi / 2) := by
    have h : (2 : ℝ) * (Real.pi / 4) + 2 * (Real.pi / 4) = Real.pi := by ring
    rw [h]
    nlinarith [Real.pi_pos, Real.pi_le_four]
  -- the target's second argument is the integral of the *sum* `D + φ(π/4)²`
  have hR : (∫ θ in (0:ℝ)..(Real.pi / 2),
        ((deriv φ θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β) + (φ (Real.pi / 4)) ^ 2))
      = (∫ θ in (0:ℝ)..(Real.pi / 2), (deriv φ θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β))
        + Real.pi / 2 * (φ (Real.pi / 4)) ^ 2 := by
    rw [intervalIntegral.integral_add hDintFull intervalIntegrable_const,
      intervalIntegral.integral_const]
    simp only [sub_zero, smul_eq_mul]
  constructor
  · rw [hsplitA, hR, hsplitD]
    have hstep : (∫ θ in (0:ℝ)..(Real.pi / 4), (φ θ) ^ 2 * (Real.sin (2 * θ)) ^ (β - 1))
          + (∫ θ in (Real.pi / 4)..(Real.pi / 2), (φ θ) ^ 2 * (Real.sin (2 * θ)) ^ (β - 1))
        ≤ ((4 / β ^ 2) * (Real.pi / 4) ^ 2
              * (∫ θ in (0:ℝ)..(Real.pi / 4),
                  (deriv φ θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β))
            + Real.pi / (2 * β) * (φ (Real.pi / 4)) ^ 2)
          + ((4 / β ^ 2) * (Real.pi / 4) ^ 2
              * (∫ θ in (Real.pi / 4)..(Real.pi / 2),
                  (deriv φ θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β))
            + Real.pi / (2 * β) * (φ (Real.pi / 4)) ^ 2) := add_le_add hA1 hA2
    refine hstep.trans ?_
    have h1 : (4 / β ^ 2) * (Real.pi / 4) ^ 2
          * (∫ θ in (0:ℝ)..(Real.pi / 4),
              (deriv φ θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β))
        + (4 / β ^ 2) * (Real.pi / 4) ^ 2
          * (∫ θ in (Real.pi / 4)..(Real.pi / 2),
              (deriv φ θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β))
        ≤ (400 / β ^ 2)
          * ((∫ θ in (0:ℝ)..(Real.pi / 4),
              (deriv φ θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β))
            + ∫ θ in (Real.pi / 4)..(Real.pi / 2),
                (deriv φ θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β)) := by
      have ha := mul_le_mul_of_nonneg_right hcoef1 hDnn
      have hb := mul_le_mul_of_nonneg_right hcoef1 hDnn'
      nlinarith [ha, hb]
    have h2 : Real.pi / (2 * β) * (φ (Real.pi / 4)) ^ 2
          + Real.pi / (2 * β) * (φ (Real.pi / 4)) ^ 2
        ≤ (400 / β ^ 2) * (Real.pi / 2 * (φ (Real.pi / 4)) ^ 2) := by
      have hb := mul_le_mul_of_nonneg_right hcoef2 hc2nn
      linarith [hb]
    linarith [h1, h2]
  · rw [hsplitM, hR, hsplitD]
    have hstep : (∫ θ in (0:ℝ)..(Real.pi / 4), (φ θ) ^ 2 * (Real.sin (2 * θ)) ^ β)
          + (∫ θ in (Real.pi / 4)..(Real.pi / 2), (φ θ) ^ 2 * (Real.sin (2 * θ)) ^ β)
        ≤ (4 * (Real.pi / 4) ^ 2
              * (∫ θ in (0:ℝ)..(Real.pi / 4),
                  (deriv φ θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β))
            + 2 * (Real.pi / 4) * (φ (Real.pi / 4)) ^ 2)
          + (4 * (Real.pi / 4) ^ 2
              * (∫ θ in (Real.pi / 4)..(Real.pi / 2),
                  (deriv φ θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β))
            + 2 * (Real.pi / 4) * (φ (Real.pi / 4)) ^ 2) := add_le_add hB1b hB2b
    refine hstep.trans ?_
    have h1 : 4 * (Real.pi / 4) ^ 2
          * (∫ θ in (0:ℝ)..(Real.pi / 4),
              (deriv φ θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β))
        + 4 * (Real.pi / 4) ^ 2
          * (∫ θ in (Real.pi / 4)..(Real.pi / 2),
              (deriv φ θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β))
        ≤ 400
          * ((∫ θ in (0:ℝ)..(Real.pi / 4),
              (deriv φ θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β))
            + ∫ θ in (Real.pi / 4)..(Real.pi / 2),
                (deriv φ θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β)) := by
      have ha := mul_le_mul_of_nonneg_right hcoef3 hDnn
      have hb := mul_le_mul_of_nonneg_right hcoef3 hDnn'
      nlinarith [ha, hb]
    have h2 : 2 * (Real.pi / 4) * (φ (Real.pi / 4)) ^ 2
          + 2 * (Real.pi / 4) * (φ (Real.pi / 4)) ^ 2
        ≤ 400 * (Real.pi / 2 * (φ (Real.pi / 4)) ^ 2) := by
      have hb := mul_le_mul_of_nonneg_right hcoef4 hc2nn
      linarith [hb]
    linarith [h1, h2]

end Work.FTS.H2.Transport3Aux
