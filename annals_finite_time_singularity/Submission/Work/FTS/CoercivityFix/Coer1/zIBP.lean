/-
# The `z`-integration by parts of §6 in the interior class `SmoothQuad`

`Work.Coercivity.wip_L_self` proves the paper's identity

  `wip (w²σ) (𝓛u) u = ½ wip (w²σ) u u`

from the analytic hypothesis package `Work.Coercivity.IBP u`, whose smoothness field is
`Spaces.SmoothNbhd u` — *analyticity* on a neighbourhood of the closed quadrant, which the
cut-off data of the route cannot satisfy (design `FTS/N45_DESIGN_LEAD.md` §5 T1).  This file
re-proves the same identity from the interior package `Work.FTS.CoercivityFix.Coer1.ZIBP u`
(`C^∞` on the open quadrant, boundary limits, and the honesty of the two one-dimensional
integrals of the fundamental theorem of calculus for a.e. angle).

The proof is the one of `wip_L_self`: the pointwise identity
`𝓛u·u·w²σ = u²w²σ + ½ z∂_z(u²w²)σ` (`Work.FTS.CoercivityFix.Coer1.l_self_w_sq_Q`), Fubini,
and the slice-wise fundamental theorem of calculus
(`∫₀^∞ z∂_z((uw)²) dz = −∫₀^∞ (uw)² dz`, because the boundary term `z(u w)²` vanishes at both
ends of `(0,∞)`).  Since `SmoothQuad` is a statement about the *open* quadrant, all the
pointwise identities are applied for a.e. angle only; this is where the a.e. formulation of
the `ZIBP` slice hypotheses (and the restriction of the boundary limits to the open interval
`Ioo 0 (π/2)`) is used.
-/
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Submission.Work.FTS.CoercivityFix.Coer1.Defs
import Submission.Work.Coercivity.wip_L_self
import Submission.Work.Coercivity.deriv_zw_sq_integral
import Submission.Work.Coercivity.wip_eq_integral_prod

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Coer1

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The slice derivative of a `SmoothQuad` function -/

/-- The `z`-slice of a `SmoothQuad` function is differentiable at every `z > -1`, with
derivative `pz u z θ` (this is the `SmoothQuad` replacement of
`Spaces.hardyZ_hasDerivAt_slice`). -/
theorem hasDerivAt_slice_Q {u : Fn} (hu : Work.FTS.LocData.SmoothQuad u) {θ x : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) (hx : 0 < x) :
    HasDerivAt (fun z => u z θ) (Work.Spaces.pz u x θ) x :=
  (((hu.curry_z hθ).differentiableOn Work.FTS.LocData.smoothOrder_ne_zero).differentiableAt
    (isOpen_Ioi.mem_nhds (by simp only [Set.mem_Ioi]; linarith))).hasDerivAt

/-- The `z`-slice `z ↦ z (u(z,θ) w(z))²` is differentiable at every `x > 0`, with the
derivative `deriv` of itself. -/
theorem hasDerivAt_zw_sq_Q {u : Fn} (hu : Work.FTS.LocData.SmoothQuad u) {θ x : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) (hx : 0 < x) :
    HasDerivAt (fun z => z * (u z θ * Work.Spaces.w z) ^ 2)
      (deriv (fun z => z * (u z θ * Work.Spaces.w z) ^ 2) x) x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hu_d : HasDerivAt (fun z => u z θ) (Work.Spaces.pz u x θ) x :=
    hasDerivAt_slice_Q hu hθ hx
  have hw_d : HasDerivAt Work.Spaces.w (-2 * (1 + x) / x ^ 3) x :=
    Work.Coercivity.hasDerivAt_w hx0
  have huW : HasDerivAt (fun z => u z θ * Work.Spaces.w z)
      (Work.Spaces.pz u x θ * Work.Spaces.w x + u x θ * (-2 * (1 + x) / x ^ 3)) x :=
    hu_d.mul hw_d
  have h := (hasDerivAt_id x).mul (huW.pow 2)
  exact h.congr_deriv h.deriv.symm

/-- **The boundary term of the `z`-integration by parts vanishes, in integral form**: for
`θ` in the open interval, `∫₀^∞ ∂_z(z (u(·,θ) w)²) dz = 0`.  This is the fundamental theorem
of calculus on `(0,∞)`: the integrand is the derivative of `z ↦ z(u w)²`, which has limit `0`
both at `z = 0⁺` and at `z = ∞` by `ZIBP.bd0`/`ZIBP.bdTop`. -/
theorem deriv_zw_sq_integral_Q (u : Fn) (hu : ZIBP u) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hint : MeasureTheory.IntegrableOn
      (fun z => deriv (fun z' => z' * (u z' θ * Work.Spaces.w z') ^ 2) z) (Set.Ioi 0)) :
    ∫ z in Set.Ioi (0 : ℝ), deriv (fun z' => z' * (u z' θ * Work.Spaces.w z') ^ 2) z = 0 := by
  have hderiv : ∀ x ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun z => z * (u z θ * Work.Spaces.w z) ^ 2)
        (deriv (fun z => z * (u z θ * Work.Spaces.w z) ^ 2) x) x :=
    fun x hx => hasDerivAt_zw_sq_Q hu.smooth hθ hx
  have htop : Tendsto (fun z => z * (u z θ * Work.Spaces.w z) ^ 2) atTop (𝓝 0) :=
    hu.bdTop θ hθ
  have hcont : ContinuousWithinAt (fun z => z * (u z θ * Work.Spaces.w z) ^ 2)
      (Set.Ici (0 : ℝ)) 0 := by
    have h2 : Tendsto (fun z => z * (u z θ * Work.Spaces.w z) ^ 2) (𝓝[{(0 : ℝ)}] 0)
        (𝓝 (0 * (u 0 θ * Work.Spaces.w 0) ^ 2)) := by
      rw [nhdsWithin_singleton]
      exact tendsto_pure_nhds _ 0
    have h1 : Tendsto (fun z => z * (u z θ * Work.Spaces.w z) ^ 2) (𝓝[>] (0 : ℝ))
        (𝓝 (0 * (u 0 θ * Work.Spaces.w 0) ^ 2)) := by
      simpa using hu.bd0 θ hθ
    have h3 : Tendsto (fun z => z * (u z θ * Work.Spaces.w z) ^ 2)
        (𝓝[>] (0 : ℝ) ⊔ 𝓝[{(0 : ℝ)}] 0) (𝓝 (0 * (u 0 θ * Work.Spaces.w 0) ^ 2)) := h1.sup h2
    rw [nhdsGT_sup_nhdsWithin_singleton] at h3
    exact h3
  have key := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint htop
  simpa using key

/-- **The `z`-integration by parts of §6 on a single `θ`-slice**: for `θ` in the open
interval, `∫₀^∞ z ∂_z((u(z,θ) w(z))²) dz = − ∫₀^∞ (u(z,θ) w(z))² dz`. -/
theorem slice_z_deriv_integral_Q (u : Fn) (hu : ZIBP u) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hintD : MeasureTheory.IntegrableOn
      (fun z => deriv (fun z' => z' * (u z' θ * Work.Spaces.w z') ^ 2) z) (Set.Ioi 0))
    (hintS : MeasureTheory.IntegrableOn (fun z => (u z θ * Work.Spaces.w z) ^ 2) (Set.Ioi 0)) :
    ∫ z in Work.Spaces.Iz, z * deriv (fun z' => (u z' θ * Work.Spaces.w z') ^ 2) z
      = -∫ z in Work.Spaces.Iz, (u z θ * Work.Spaces.w z) ^ 2 := by
  have hftc := deriv_zw_sq_integral_Q u hu hθ hintD
  have hIzeq : Work.Spaces.Iz =ᵐ[(volume : Measure ℝ)] Set.Ioi 0 := by
    rw [MeasureTheory.ae_eq_set]
    refine ⟨?_, ?_⟩
    · have h : Work.Spaces.Iz \ Set.Ioi 0 = {0} := by
        ext x
        simp only [Set.mem_sdiff, Set.mem_Ioi, Set.mem_singleton_iff, Work.Spaces.Iz,
          Set.mem_Ici, not_lt]
        constructor
        · rintro ⟨h1, h2⟩; exact le_antisymm h2 h1
        · rintro rfl; exact ⟨le_refl 0, le_refl 0⟩
      rw [h, Real.volume_singleton]
    · have h : Set.Ioi (0 : ℝ) \ Work.Spaces.Iz = ∅ := by
        rw [Work.Spaces.Iz, Set.sdiff_eq_empty]
        exact Set.Ioi_subset_Ici_self
      rw [h, MeasureTheory.measure_empty]
  have hsub : ∫ z in Set.Ioi (0 : ℝ),
        (deriv (fun z' => z' * (u z' θ * Work.Spaces.w z') ^ 2) z
          - (u z θ * Work.Spaces.w z) ^ 2)
      = - ∫ z in Set.Ioi (0 : ℝ), (u z θ * Work.Spaces.w z) ^ 2 := by
    rw [MeasureTheory.integral_sub hintD hintS, hftc, zero_sub]
  have hcongr : ∫ z in Set.Ioi (0 : ℝ),
        (deriv (fun z' => z' * (u z' θ * Work.Spaces.w z') ^ 2) z
          - (u z θ * Work.Spaces.w z) ^ 2)
      = ∫ z in Set.Ioi (0 : ℝ), z * deriv (fun z' => (u z' θ * Work.Spaces.w z') ^ 2) z := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun z hz => ?_)
    rw [deriv_zw_sq_Q hu.smooth hz hθ]; ring
  have hL : ∫ z in Work.Spaces.Iz, z * deriv (fun z' => (u z' θ * Work.Spaces.w z') ^ 2) z
      = ∫ z in Set.Ioi (0 : ℝ), z * deriv (fun z' => (u z' θ * Work.Spaces.w z') ^ 2) z :=
    MeasureTheory.setIntegral_congr_set hIzeq
  have hR : ∫ z in Work.Spaces.Iz, (u z θ * Work.Spaces.w z) ^ 2
      = ∫ z in Set.Ioi (0 : ℝ), (u z θ * Work.Spaces.w z) ^ 2 :=
    MeasureTheory.setIntegral_congr_set hIzeq
  rw [hL, hR, ← hcongr, hsub]

/-! ## The `wip`-identity -/

/-- The integrand `𝓛u · u · w²σ` on the product `Iz × Iθ`. -/
def LwQ (u : Fn) (σ : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  Work.Coercivity.L u p.1 p.2 * u p.1 p.2 * Work.Spaces.w p.1 ^ 2 * σ p.2

/-- The integrand `u² w²σ` on the product `Iz × Iθ`. -/
def RwQ (u : Fn) (σ : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  u p.1 p.2 ^ 2 * Work.Spaces.w p.1 ^ 2 * σ p.2

/-- The integrand `z ∂_z((u w)²) σ` on the product `Iz × Iθ`. -/
def DwQ (u : Fn) (σ : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  p.1 * deriv (fun z' => (u z' p.2 * Work.Spaces.w z') ^ 2) p.1 * σ p.2

/-- **The paper's identity `(LW)` integrated: `⟨𝓛u, u⟩_{w²σ} = ½⟨u,u⟩_{w²σ}` in the interior
class `SmoothQuad`.** -/
theorem wip_L_self_Q (u : Fn) (hu : ZIBP u) (σ : ℝ → ℝ)
    (h1 : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => u z θ ^ 2 * Work.Spaces.w z ^ 2 * σ θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (h2 : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Coercivity.L u z θ * u z θ * Work.Spaces.w z ^ 2 * σ θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ) (Work.Coercivity.L u) u
      = (1 / 2) * Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ) u u := by
  set μ : MeasureTheory.Measure ℝ := MeasureTheory.volume.restrict Work.Spaces.Iz with hμ
  set ν : MeasureTheory.Measure ℝ := MeasureTheory.volume.restrict Work.Spaces.Iθ with hν
  have hmeas : μ.prod ν
      = (volume : MeasureTheory.Measure (ℝ × ℝ)).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    rw [hμ, hν, MeasureTheory.Measure.prod_restrict,
      ← MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
  have hF1 : MeasureTheory.Integrable (LwQ u σ) (μ.prod ν) := by
    rw [hmeas]; exact h2
  have hF2 : MeasureTheory.Integrable (RwQ u σ) (μ.prod ν) := by
    rw [hmeas]; exact h1
  -- a.e. positivity in the radial variable
  have haepos : ∀ᵐ p ∂(μ.prod ν), 0 < p.1 := by
    have hslice : ∀ᵐ z ∂μ, 0 < z := by
      rw [hμ, MeasureTheory.ae_restrict_iff (p := fun z => 0 < z) measurableSet_Ioi,
        MeasureTheory.ae_iff]
      have hset : {z : ℝ | ¬ (z ∈ Work.Spaces.Iz → 0 < z)} = {0} := by
        ext z
        simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, Work.Spaces.Iz, Set.mem_Ici, not_imp]
        constructor
        · rintro ⟨h1, h2⟩; exact le_antisymm (not_lt.mp h2) h1
        · intro h; rw [h]; exact ⟨le_refl 0, lt_irrefl 0⟩
      rw [hset, Real.volume_singleton]
    have h : ∀ᵐ p ∂(μ.prod ν), p ∈ Set.Ioi (0 : ℝ) ×ˢ Set.univ :=
      (MeasureTheory.Measure.ae_prod_mem_iff_ae_ae_mem
        (s := Set.Ioi (0 : ℝ) ×ˢ Set.univ) (measurableSet_Ioi.prod MeasurableSet.univ)).mpr
        (hslice.mono (fun x hx => Filter.Eventually.of_forall (fun _ => by simp [hx])))
    simpa using h
  -- a.e. interiority of the angle
  have haeθ : ∀ᵐ p ∂(μ.prod ν), p.2 ∈ Set.Ioo 0 (π / 2) := by
    have h1 : ∀ᵐ θ ∂ν, θ ∈ Set.Ioo (0 : ℝ) (π / 2) := by
      rw [hν]; exact ae_restrict_Iθ_mem_Ioo
    have h : ∀ᵐ p ∂(μ.prod ν), p ∈ Set.univ ×ˢ Set.Ioo (0 : ℝ) (π / 2) :=
      (MeasureTheory.Measure.ae_prod_mem_iff_ae_ae_mem
        (s := Set.univ ×ˢ Set.Ioo (0 : ℝ) (π / 2))
        (MeasurableSet.univ.prod measurableSet_Ioo)).mpr
        (Filter.Eventually.of_forall (fun _ => h1.mono (fun y hy => ⟨Set.mem_univ _, hy⟩)))
    simpa using h
  -- the pointwise identity `𝓛u·u·w²σ = u²w²σ + ½ z∂_z((uw)²)σ`, a.e. on the product
  have hae_id : ∀ᵐ p ∂(μ.prod ν), LwQ u σ p = RwQ u σ p + (1 / 2) * DwQ u σ p := by
    filter_upwards [haepos, haeθ] with p hp hθ
    have h := l_self_w_sq_Q hu.smooth hp hθ
    dsimp only [LwQ, RwQ, DwQ]
    rw [h]; ring
  have hF3 : MeasureTheory.Integrable (DwQ u σ) (μ.prod ν) := by
    have h2' : MeasureTheory.Integrable
        (fun p => 2 * LwQ u σ p - 2 * RwQ u σ p) (μ.prod ν) :=
      (hF1.const_mul 2).sub (hF2.const_mul 2)
    refine h2'.congr ?_
    filter_upwards [hae_id] with p hp
    linarith
  have hΦval : ∫ p, LwQ u σ p ∂(μ.prod ν)
      = ∫ p, RwQ u σ p ∂(μ.prod ν) + (1 / 2) * ∫ p, DwQ u σ p ∂(μ.prod ν) := by
    rw [MeasureTheory.integral_congr_ae hae_id]
    rw [MeasureTheory.integral_add hF2 (hF3.const_mul (1 / 2)),
      MeasureTheory.integral_const_mul]
  -- the derivative term is minus the norm: Fubini in `θ`, then the slice identity
  have hDval : ∫ p, DwQ u σ p ∂(μ.prod ν) = -∫ p, RwQ u σ p ∂(μ.prod ν) := by
    have hinner : (fun θ => ∫ z, DwQ u σ (z, θ) ∂μ)
        =ᵐ[ν] (fun θ => -∫ z, RwQ u σ (z, θ) ∂μ) := by
      filter_upwards [ae_restrict_Iθ_mem_Ioo, hu.intSq, hu.intDeriv]
        with θ hθIoo hθSq hθDer
      have h1 : (∫ z, DwQ u σ (z, θ) ∂μ)
          = (∫ z, z * deriv (fun z' => (u z' θ * Work.Spaces.w z') ^ 2) z ∂μ) * σ θ := by
        dsimp only [DwQ]
        rw [MeasureTheory.integral_mul_const]
      have h2 : (∫ z, z * deriv (fun z' => (u z' θ * Work.Spaces.w z') ^ 2) z ∂μ)
          = -(∫ z, (u z θ * Work.Spaces.w z) ^ 2 ∂μ) := by
        rw [show (∫ z, z * deriv (fun z' => (u z' θ * Work.Spaces.w z') ^ 2) z ∂μ)
            = ∫ z in Work.Spaces.Iz,
                z * deriv (fun z' => (u z' θ * Work.Spaces.w z') ^ 2) z from rfl,
          show (∫ z, (u z θ * Work.Spaces.w z) ^ 2 ∂μ)
            = ∫ z in Work.Spaces.Iz, (u z θ * Work.Spaces.w z) ^ 2 from rfl,
          slice_z_deriv_integral_Q u hu hθIoo hθDer hθSq]
      have h3 : (∫ z, RwQ u σ (z, θ) ∂μ)
          = (∫ z, (u z θ * Work.Spaces.w z) ^ 2 ∂μ) * σ θ := by
        dsimp only [RwQ]
        rw [MeasureTheory.integral_mul_const]
        congr 1
        exact MeasureTheory.integral_congr_ae
          (Filter.Eventually.of_forall (fun z => by ring))
      rw [h1, h2, h3]; ring
    rw [MeasureTheory.integral_prod_symm (DwQ u σ) hF3,
      MeasureTheory.integral_congr_ae hinner, MeasureTheory.integral_neg,
      ← MeasureTheory.integral_prod_symm (RwQ u σ) hF2]
  -- Fubini bridge: both `wip`s are product-measure integrals
  have hint2' : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Coercivity.L u z θ * u z θ
        * (Work.Spaces.w z ^ 2 * σ θ))) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    refine h2.congr ?_
    filter_upwards with p
    dsimp only [Function.uncurry]
    ring
  have hint' : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => u z θ * u z θ
        * (Work.Spaces.w z ^ 2 * σ θ))) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    refine h1.congr ?_
    filter_upwards with p
    dsimp only [Function.uncurry]
    ring
  have hwL : Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ)
        (Work.Coercivity.L u) u = ∫ p, LwQ u σ p ∂(μ.prod ν) := by
    rw [Work.Coercivity.wip_eq_integral_prod (fun z θ => Work.Spaces.w z ^ 2 * σ θ)
      (Work.Coercivity.L u) u hint2']
    rw [hμ, hν]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with p
    dsimp only [LwQ, Function.uncurry]
    ring
  have hwR : Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ) u u
      = ∫ p, RwQ u σ p ∂(μ.prod ν) := by
    rw [Work.Coercivity.wip_eq_integral_prod (fun z θ => Work.Spaces.w z ^ 2 * σ θ) u u hint']
    rw [hμ, hν]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with p
    dsimp only [RwQ, Function.uncurry]
    ring
  rw [hwL, hwR, hΦval, hDval]
  ring

end Work.FTS.CoercivityFix.Coer1
