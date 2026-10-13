/-
# `Coer1SO/wip_Dz_self_le_SO` — the `D_z`-self estimate in the **open** class

Verbatim open-class analogue of `Work.FTS.CoercivityFix.Assembly.wip_Dz_self_le`
(`Assembly/V_bounds.lean`).  The only hypothesis that changes is the `z`-integration-by-parts
package: `Work.FTS.CoercivityFix.Coer1SO.ZIBPO u` (smoothness `SmoothOpen`, i.e. `C^∞` on the
*open* quadrant `(0,∞) × (0,π/2)`) instead of `Work.FTS.CoercivityFix.Coer1.ZIBP u` (the same
package with analyticity on a neighbourhood of the closed quadrant, `SmoothQuad`).

The mathematics is unchanged:

* `⟨𝓛u, u⟩_{w²σ} = ½⟨u,u⟩_{w²σ}` — the paper's `z`-integration by parts, proved below as
  `wip_L_self_QO` (the open-class copy of `Coer1.wip_L_self_Q`, whose only inputs about the
  datum are the *pointwise* open-quadrant differentiability of the `z`-slices
  (`SmoothOpen.hasDerivAt_slice`, via `hasDerivAt_zw_sq_O`) and the two boundary limits);
* `𝓛u = u + D_z u − 2u/(1+z)`, so `⟨D_z u, u⟩_{w²σ} = 2⟨u/(1+z), u⟩_{w²σ} − ½⟨u,u⟩_{w²σ}`
  with `0 ≤ ⟨u/(1+z), u⟩_{w²σ} ≤ ⟨u,u⟩_{w²σ}` on `z ≥ 0`, giving the constant `5/2`.

The generic `wip`-linearity lemmas (`wip_add_left`, `wip_sub_left`, `wip_smul_left`,
`wip_self_nonneg`) carry no regularity hypothesis and are imported from their original modules;
the two remaining generic ones (`wip_congr_pt`, `wip_div_one_add_self_le`) are copied here so
that the heavy `Assembly/V_bounds.lean` is not on the import cone.

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Submission.Work.FTS.CoercivityFix.Coer1SO.Defs
import Submission.Work.FTS.CoercivityFix.Coer1SO.zibpO_of
import Submission.Work.FTS.CoercivityFix.Coer1.IntFacts
import Submission.Work.FTS.CoercivityFix.Coer1.Estimates
import Submission.Work.Coercivity.wip_Aop_ge
import Submission.Work.Coercivity.H1IP_homog
import Submission.Work.Coercivity.H1IP_nonneg
import Submission.Work.Coercivity.wip_eq_integral_prod

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Coer1SO

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The open-class `z`-integration by parts -/

/-- The `z`-slice `z ↦ z (u(z,θ) w(z))²` of a function `C^∞` on the *open* quadrant is
differentiable at every `x > 0`, with the derivative `deriv` of itself.  This is the
`SmoothOpen` analogue of `Coer1.hasDerivAt_zw_sq_Q`. -/
theorem hasDerivAt_zw_sq_O {u : Fn} (hu : Work.FTS.EllipticEst.SmoothOpen u) {θ x : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) (hx : 0 < x) :
    HasDerivAt (fun z => z * (u z θ * Work.Spaces.w z) ^ 2)
      (deriv (fun z => z * (u z θ * Work.Spaces.w z) ^ 2) x) x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hu_d : HasDerivAt (fun z => u z θ) (Work.Spaces.pz u x θ) x :=
    hu.hasDerivAt_slice hθ hx
  have hw_d : HasDerivAt Work.Spaces.w (-2 * (1 + x) / x ^ 3) x :=
    Work.Coercivity.hasDerivAt_w hx0
  have huW : HasDerivAt (fun z => u z θ * Work.Spaces.w z)
      (Work.Spaces.pz u x θ * Work.Spaces.w x + u x θ * (-2 * (1 + x) / x ^ 3)) x :=
    hu_d.mul hw_d
  have h := (hasDerivAt_id x).mul (huW.pow 2)
  exact h.congr_deriv h.deriv.symm

/-- **The boundary term of the `z`-integration by parts vanishes, in integral form** (open
class): for `θ` in the open interval, `∫₀^∞ ∂_z(z (u(·,θ) w)²) dz = 0`.  This is the
fundamental theorem of calculus on `(0,∞)`: the integrand is the derivative of
`z ↦ z(u w)²`, which has limit `0` both at `z = 0⁺` and at `z = ∞` by
`ZIBPO.bd0`/`ZIBPO.bdTop`. -/
theorem deriv_zw_sq_integral_O (u : Fn) (hu : ZIBPO u) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hint : MeasureTheory.IntegrableOn
      (fun z => deriv (fun z' => z' * (u z' θ * Work.Spaces.w z') ^ 2) z) (Set.Ioi 0)) :
    ∫ z in Set.Ioi (0 : ℝ), deriv (fun z' => z' * (u z' θ * Work.Spaces.w z') ^ 2) z = 0 := by
  have hderiv : ∀ x ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun z => z * (u z θ * Work.Spaces.w z) ^ 2)
        (deriv (fun z => z * (u z θ * Work.Spaces.w z) ^ 2) x) x :=
    fun x hx => hasDerivAt_zw_sq_O hu.smooth hθ hx
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

/-- **The `z`-integration by parts of §6 on a single `θ`-slice** (open class): for `θ` in the
open interval, `∫₀^∞ z ∂_z((u(z,θ) w(z))²) dz = − ∫₀^∞ (u(z,θ) w(z))² dz`. -/
theorem slice_z_deriv_integral_O (u : Fn) (hu : ZIBPO u) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hintD : MeasureTheory.IntegrableOn
      (fun z => deriv (fun z' => z' * (u z' θ * Work.Spaces.w z') ^ 2) z) (Set.Ioi 0))
    (hintS : MeasureTheory.IntegrableOn (fun z => (u z θ * Work.Spaces.w z) ^ 2) (Set.Ioi 0)) :
    ∫ z in Work.Spaces.Iz, z * deriv (fun z' => (u z' θ * Work.Spaces.w z') ^ 2) z
      = -∫ z in Work.Spaces.Iz, (u z θ * Work.Spaces.w z) ^ 2 := by
  have hftc := deriv_zw_sq_integral_O u hu hθ hintD
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
    rw [deriv_zw_sq_O hu.smooth hz hθ]; ring
  have hL : ∫ z in Work.Spaces.Iz, z * deriv (fun z' => (u z' θ * Work.Spaces.w z') ^ 2) z
      = ∫ z in Set.Ioi (0 : ℝ), z * deriv (fun z' => (u z' θ * Work.Spaces.w z') ^ 2) z :=
    MeasureTheory.setIntegral_congr_set hIzeq
  have hR : ∫ z in Work.Spaces.Iz, (u z θ * Work.Spaces.w z) ^ 2
      = ∫ z in Set.Ioi (0 : ℝ), (u z θ * Work.Spaces.w z) ^ 2 :=
    MeasureTheory.setIntegral_congr_set hIzeq
  rw [hL, hR, ← hcongr, hsub]

/-! ## The `wip`-identity in the open class -/

/-- The integrand `𝓛u · u · w²σ` on the product `Iz × Iθ`. -/
def LwSO (u : Fn) (σ : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  Work.Coercivity.L u p.1 p.2 * u p.1 p.2 * Work.Spaces.w p.1 ^ 2 * σ p.2

/-- The integrand `u² w²σ` on the product `Iz × Iθ`. -/
def RwSO (u : Fn) (σ : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  u p.1 p.2 ^ 2 * Work.Spaces.w p.1 ^ 2 * σ p.2

/-- The integrand `z ∂_z((u w)²) σ` on the product `Iz × Iθ`. -/
def DwSO (u : Fn) (σ : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  p.1 * deriv (fun z' => (u z' p.2 * Work.Spaces.w z') ^ 2) p.1 * σ p.2

/-- **The paper's identity `(LW)` integrated, in the open class `SmoothOpen`**:
`⟨𝓛u, u⟩_{w²σ} = ½⟨u,u⟩_{w²σ}`.  This is the open-class copy of `Coer1.wip_L_self_Q`; the
only change is that the pointwise identity `l_self_w_sq_O` (proved from
`SmoothOpen.hasDerivAt_slice`) replaces `l_self_w_sq_Q`. -/
theorem wip_L_self_QO (u : Fn) (hu : ZIBPO u) (σ : ℝ → ℝ)
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
  have hF1 : MeasureTheory.Integrable (LwSO u σ) (μ.prod ν) := by
    rw [hmeas]; exact h2
  have hF2 : MeasureTheory.Integrable (RwSO u σ) (μ.prod ν) := by
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
      rw [hν]; exact Work.FTS.CoercivityFix.Coer1.ae_restrict_Iθ_mem_Ioo
    have h : ∀ᵐ p ∂(μ.prod ν), p ∈ Set.univ ×ˢ Set.Ioo (0 : ℝ) (π / 2) :=
      (MeasureTheory.Measure.ae_prod_mem_iff_ae_ae_mem
        (s := Set.univ ×ˢ Set.Ioo (0 : ℝ) (π / 2))
        (MeasurableSet.univ.prod measurableSet_Ioo)).mpr
        (Filter.Eventually.of_forall (fun _ => h1.mono (fun y hy => ⟨Set.mem_univ _, hy⟩)))
    simpa using h
  -- the pointwise identity `𝓛u·u·w²σ = u²w²σ + ½ z∂_z((uw)²)σ`, a.e. on the product
  have hae_id : ∀ᵐ p ∂(μ.prod ν), LwSO u σ p = RwSO u σ p + (1 / 2) * DwSO u σ p := by
    filter_upwards [haepos, haeθ] with p hp hθ
    have h := l_self_w_sq_O hu.smooth hp hθ
    dsimp only [LwSO, RwSO, DwSO]
    rw [h]; ring
  have hF3 : MeasureTheory.Integrable (DwSO u σ) (μ.prod ν) := by
    have h2' : MeasureTheory.Integrable
        (fun p => 2 * LwSO u σ p - 2 * RwSO u σ p) (μ.prod ν) :=
      (hF1.const_mul 2).sub (hF2.const_mul 2)
    refine h2'.congr ?_
    filter_upwards [hae_id] with p hp
    linarith
  have hΦval : ∫ p, LwSO u σ p ∂(μ.prod ν)
      = ∫ p, RwSO u σ p ∂(μ.prod ν) + (1 / 2) * ∫ p, DwSO u σ p ∂(μ.prod ν) := by
    rw [MeasureTheory.integral_congr_ae hae_id]
    rw [MeasureTheory.integral_add hF2 (hF3.const_mul (1 / 2)),
      MeasureTheory.integral_const_mul]
  -- the derivative term is minus the norm: Fubini in `θ`, then the slice identity
  have hDval : ∫ p, DwSO u σ p ∂(μ.prod ν) = -∫ p, RwSO u σ p ∂(μ.prod ν) := by
    have hinner : (fun θ => ∫ z, DwSO u σ (z, θ) ∂μ)
        =ᵐ[ν] (fun θ => -∫ z, RwSO u σ (z, θ) ∂μ) := by
      filter_upwards [Work.FTS.CoercivityFix.Coer1.ae_restrict_Iθ_mem_Ioo, hu.intSq, hu.intDeriv]
        with θ hθIoo hθSq hθDer
      have h1 : (∫ z, DwSO u σ (z, θ) ∂μ)
          = (∫ z, z * deriv (fun z' => (u z' θ * Work.Spaces.w z') ^ 2) z ∂μ) * σ θ := by
        dsimp only [DwSO]
        rw [MeasureTheory.integral_mul_const]
      have h2 : (∫ z, z * deriv (fun z' => (u z' θ * Work.Spaces.w z') ^ 2) z ∂μ)
          = -(∫ z, (u z θ * Work.Spaces.w z) ^ 2 ∂μ) := by
        rw [show (∫ z, z * deriv (fun z' => (u z' θ * Work.Spaces.w z') ^ 2) z ∂μ)
            = ∫ z in Work.Spaces.Iz,
                z * deriv (fun z' => (u z' θ * Work.Spaces.w z') ^ 2) z from rfl,
          show (∫ z, (u z θ * Work.Spaces.w z) ^ 2 ∂μ)
            = ∫ z in Work.Spaces.Iz, (u z θ * Work.Spaces.w z) ^ 2 from rfl,
          slice_z_deriv_integral_O u hu hθIoo hθDer hθSq]
      have h3 : (∫ z, RwSO u σ (z, θ) ∂μ)
          = (∫ z, (u z θ * Work.Spaces.w z) ^ 2 ∂μ) * σ θ := by
        dsimp only [RwSO]
        rw [MeasureTheory.integral_mul_const]
        congr 1
        exact MeasureTheory.integral_congr_ae
          (Filter.Eventually.of_forall (fun z => by ring))
      rw [h1, h2, h3]; ring
    rw [MeasureTheory.integral_prod_symm (DwSO u σ) hF3,
      MeasureTheory.integral_congr_ae hinner, MeasureTheory.integral_neg,
      ← MeasureTheory.integral_prod_symm (RwSO u σ) hF2]
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
        (Work.Coercivity.L u) u = ∫ p, LwSO u σ p ∂(μ.prod ν) := by
    rw [Work.Coercivity.wip_eq_integral_prod (fun z θ => Work.Spaces.w z ^ 2 * σ θ)
      (Work.Coercivity.L u) u hint2']
    rw [hμ, hν]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with p
    dsimp only [LwSO, Function.uncurry]
    ring
  have hwR : Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ) u u
      = ∫ p, RwSO u σ p ∂(μ.prod ν) := by
    rw [Work.Coercivity.wip_eq_integral_prod (fun z θ => Work.Spaces.w z ^ 2 * σ θ) u u hint']
    rw [hμ, hν]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with p
    dsimp only [RwSO, Function.uncurry]
    ring
  rw [hwL, hwR, hΦval, hDval]
  ring

/-! ## The generic `wip` lemmas (copies of `Assembly/V_bounds.lean`'s, no regularity used) -/

/-- `wip` is a congruence in both pairing arguments. -/
theorem wip_congr_pt_SO {ρ : Fn} {A A' B B' : Fn} (hA : ∀ z θ, A z θ = A' z θ)
    (hB : ∀ z θ, B z θ = B' z θ) : Work.Coercivity.wip ρ A B = Work.Coercivity.wip ρ A' B' := by
  rw [Work.Coercivity.wip, Work.Coercivity.wip]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
  rw [hA z θ, hB z θ]

/-- `⟨u/(1+z), u⟩_{w²σ} ≤ ⟨u,u⟩_{w²σ}` for a nonnegative weight: the factor `1/(1+z) ≤ 1`
on `z ≥ 0`. -/
theorem wip_div_one_add_self_le_SO {ρ u : Fn} (hρ : ∀ z θ, θ ∈ Work.Spaces.Iθ → 0 ≤ ρ z θ)
    (h : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ => u z θ ^ 2 * ρ z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hd : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      u z θ ^ 2 * ρ z θ / (1 + z))) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    Work.Coercivity.wip ρ (fun z θ => u z θ / (1 + z)) u ≤ Work.Coercivity.wip ρ u u := by
  have hIsum : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      u z θ / (1 + z) * u z θ * ρ z θ)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    Work.FTS.CoercivityFix.Coer1.integrableOn_congr_fun_Q hd (fun z θ => by ring)
  have hIu : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      u z θ * u z θ * ρ z θ)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    Work.FTS.CoercivityFix.Coer1.integrableOn_congr_fun_Q h (fun z θ => by ring)
  have e1 : Work.Coercivity.wip ρ (fun z θ => u z θ / (1 + z)) u
      = ∫ p : ℝ × ℝ, u p.1 p.2 ^ 2 * ρ p.1 p.2 / (1 + p.1)
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
              (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [Work.Coercivity.wip_eq_integral_prod ρ (fun z θ => u z θ / (1 + z)) u hIsum]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    ring
  have e2 : Work.Coercivity.wip ρ u u
      = ∫ p : ℝ × ℝ, u p.1 p.2 ^ 2 * ρ p.1 p.2
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
              (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [Work.Coercivity.wip_eq_integral_prod ρ u u hIu]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    ring
  rw [e1, e2]
  have hI1 : MeasureTheory.Integrable (fun p : ℝ × ℝ => u p.1 p.2 ^ 2 * ρ p.1 p.2 / (1 + p.1))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [Work.FTS.CoercivityFix.Coer1.iz_prod_restrict]
    exact hd
  have hI2 : MeasureTheory.Integrable (fun p : ℝ × ℝ => u p.1 p.2 ^ 2 * ρ p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [Work.FTS.CoercivityFix.Coer1.iz_prod_restrict]
    exact h
  refine MeasureTheory.integral_mono_ae hI1 hI2 ?_
  filter_upwards [Work.FTS.CoercivityFix.Coer1.ae_prod_fst_pos,
    Work.FTS.CoercivityFix.Coer1.ae_prod_snd_mem_Ioo] with p hp1 hp2
  have hρnn : 0 ≤ ρ p.1 p.2 := hρ p.1 p.2 ⟨le_of_lt hp2.1, le_of_lt hp2.2⟩
  have hz : 0 < 1 + p.1 := by linarith [hp1]
  have hle : 1 / (1 + p.1) ≤ 1 := by
    rw [div_le_one hz]; linarith
  have hsq : 0 ≤ u p.1 p.2 ^ 2 * ρ p.1 p.2 := mul_nonneg (sq_nonneg _) hρnn
  calc u p.1 p.2 ^ 2 * ρ p.1 p.2 / (1 + p.1)
      = (u p.1 p.2 ^ 2 * ρ p.1 p.2) * (1 / (1 + p.1)) := by ring
    _ ≤ (u p.1 p.2 ^ 2 * ρ p.1 p.2) * 1 := mul_le_mul_of_nonneg_left hle hsq
    _ = u p.1 p.2 ^ 2 * ρ p.1 p.2 := mul_one _

/-! ## The `D_z`-self estimate in the open class -/

/-- **The pairing of a slot with itself is controlled by the norm.**  For `u` with the
open-class `z`-IBP hypotheses (`ZIBPO`), the honesty of `u²w²σ` and of `𝓛u·u·w²σ`, and
`σ ≥ 0` on `Iθ`, `|⟨D_z u, u⟩_{w²σ}| ≤ (5/2)⟨u, u⟩_{w²σ}`.

Indeed `⟨𝓛u, u⟩_{w²σ} = ½⟨u,u⟩_{w²σ}` and `𝓛u = u + D_z u - 2u/(1+z)`, so
`⟨D_z u, u⟩_{w²σ} = 2⟨u/(1+z), u⟩_{w²σ} - ½⟨u,u⟩_{w²σ}` with
`0 ≤ ⟨u/(1+z), u⟩_{w²σ} ≤ ⟨u,u⟩_{w²σ}`. -/
theorem wip_Dz_self_le_SO {u : Work.FTS.Galerkin.Fn}
    (hu : Work.FTS.CoercivityFix.Coer1SO.ZIBPO u)
    {σ : ℝ → ℝ} (hσ : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ σ θ)
    (h2 : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      u z θ ^ 2 * Work.Spaces.w z ^ 2 * σ θ)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hL : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      Work.Coercivity.L u z θ * u z θ * Work.Spaces.w z ^ 2 * σ θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    |Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ)
        (Work.Spaces.Dz u) u|
      ≤ (5 / 2) * Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ) u u := by
  have h2' : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      u z θ * u z θ * (Work.Spaces.w z ^ 2 * σ θ)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    Work.FTS.CoercivityFix.Coer1.integrableOn_congr_fun_Q h2 (fun z θ => by ring)
  have hL' : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      Work.Coercivity.L u z θ * u z θ * (Work.Spaces.w z ^ 2 * σ θ)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    Work.FTS.CoercivityFix.Coer1.integrableOn_congr_fun_Q hL (fun z θ => by ring)
  have h3 : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      u z θ * u z θ * (Work.Spaces.w z ^ 2 * σ θ) / (1 + z)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    Work.FTS.CoercivityFix.Coer1.integrableOn_div_one_add_Q h2'
  have hLu : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      (Work.Coercivity.L u z θ - u z θ) * u z θ * (Work.Spaces.w z ^ 2 * σ θ)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    refine (hL'.sub h2').congr (Filter.Eventually.of_forall fun p => ?_)
    rcases p with ⟨z, θ⟩
    simp only [Function.uncurry_apply_pair, Pi.sub_apply]
    ring
  have h2u : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      (2 * (u z θ / (1 + z))) * u z θ * (Work.Spaces.w z ^ 2 * σ θ)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    refine (h3.const_mul 2).congr (Filter.Eventually.of_forall fun p => ?_)
    rcases p with ⟨z, θ⟩
    simp only [Function.uncurry_apply_pair]
    ring
  have hself := wip_L_self_QO u hu σ h2 hL
  have e0 : Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ)
        (Work.Spaces.Dz u) u
      = Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ)
          (fun z θ => (Work.Coercivity.L u z θ - u z θ) + 2 * (u z θ / (1 + z))) u := by
    refine wip_congr_pt_SO (fun z θ => ?_) (fun z θ => rfl)
    simp only [Work.Coercivity.L, Work.Spaces.Dz]
    ring
  have e1 : Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ)
        (fun z θ => (Work.Coercivity.L u z θ - u z θ) + 2 * (u z θ / (1 + z))) u
      = Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ)
          (fun z θ => Work.Coercivity.L u z θ - u z θ) u
        + Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ)
          (fun z θ => 2 * (u z θ / (1 + z))) u :=
    Work.Coercivity.wip_add_left hLu h2u
  have e2 : Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ)
        (fun z θ => Work.Coercivity.L u z θ - u z θ) u
      = Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ) (Work.Coercivity.L u) u
        - Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ) u u :=
    Work.FTS.CoercivityFix.Coer1.wip_sub_left hL' h2'
  have e3 : Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ)
        (fun z θ => 2 * (u z θ / (1 + z))) u
      = 2 * Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ)
          (fun z θ => u z θ / (1 + z)) u :=
    Work.Coercivity.wip_smul_left
  have hkey : Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ)
        (Work.Spaces.Dz u) u
      = 2 * Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ)
            (fun z θ => u z θ / (1 + z)) u
        - (1 / 2) * Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ) u u := by
    rw [e0, e1, e2, e3, hself]
    ring
  have hρnn : ∀ z θ, θ ∈ Work.Spaces.Iθ → 0 ≤ (fun z θ => Work.Spaces.w z ^ 2 * σ θ) z θ :=
    fun z θ hθ => mul_nonneg (sq_nonneg _) (hσ θ hθ)
  have hA : 0 ≤ Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ) u u :=
    Work.Coercivity.wip_self_nonneg hρnn
  have hT3nn : 0 ≤ Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ)
      (fun z θ => u z θ / (1 + z)) u := by
    rw [Work.Coercivity.wip]
    refine MeasureTheory.setIntegral_nonneg measurableSet_Ici (fun z hz => ?_)
    refine MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ hθ => ?_)
    have hρ : 0 ≤ Work.Spaces.w z ^ 2 * σ θ := mul_nonneg (sq_nonneg _) (hσ θ hθ)
    have hz0 : (0 : ℝ) ≤ z := hz
    have h1z : 0 < 1 + z := by linarith
    have : u z θ / (1 + z) * u z θ = u z θ ^ 2 / (1 + z) := by ring
    rw [this]
    exact mul_nonneg (div_nonneg (sq_nonneg _) h1z.le) hρ
  have hT3le : Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ)
        (fun z θ => u z θ / (1 + z)) u
      ≤ Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ) u u :=
    wip_div_one_add_self_le_SO hρnn
      (Work.FTS.CoercivityFix.Coer1.integrableOn_congr_fun_Q h2 (fun z θ => by ring))
      (Work.FTS.CoercivityFix.Coer1.integrableOn_congr_fun_Q h3 (fun z θ => by ring))
  rw [hkey]
  have habs : |2 * Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ)
        (fun z θ => u z θ / (1 + z)) u
      - (1 / 2) * Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ) u u|
      ≤ 2 * Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ)
          (fun z θ => u z θ / (1 + z)) u
        + (1 / 2) * Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ) u u := by
    have h := abs_sub (2 * Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ)
          (fun z θ => u z θ / (1 + z)) u)
        ((1 / 2) * Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ) u u)
    have h1 : |2 * Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ)
          (fun z θ => u z θ / (1 + z)) u|
        = 2 * Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ)
            (fun z θ => u z θ / (1 + z)) u :=
      abs_of_nonneg (by linarith [hT3nn])
    have h2 : |(1 / 2) * Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ) u u|
        = (1 / 2) * Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ) u u :=
      abs_of_nonneg (by linarith [hA])
    rw [h1, h2] at h
    exact h
  linarith [habs, hA, hT3le]

end Work.FTS.CoercivityFix.Coer1SO
