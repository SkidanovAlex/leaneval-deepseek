/-
# `𝓛` is self-adjoint on `L²(w²σ)`: `⟨𝓛u, u⟩ = ½⟨u,u⟩`

The paper's identity `𝓛 g · w = g · w + z ∂_z(g·w)` (the file `Basic.lean`, lemma
`L_mul_w_deriv`) states that `𝓛` is the generator of the dilation `z ∂_z` conjugated by the
radial weight `w(z) = (1+z)²/z²`.  Consequently, for every `σ : ℝ → ℝ`, the weighted
`L²`-pairing

  `wip (fun z θ => w z ² σ θ) (𝓛u) u`

is *half* the weighted `L²`-norm of `u`.  The proof is the `z`-integration by parts of the
paper (the first step of the coercivity estimates of §6):

* pointwise, `𝓛u · u · w² = (u w)² + ½ z ∂_z((u w)²)`,
* the boundary term `z (u w)²` vanishes at `z = 0⁺` and at `z = ∞`, so
  `∫₀^∞ z ∂_z((u w)²) dz = -∫₀^∞ (u w)² dz` by the fundamental theorem of calculus.

Hence the answer `½ ∫∫ u² w² σ`.

The lemma is reduced to product-measure integrals over `[0,∞) × [0,π/2]` by Fubini
(`wip_eq_integral_prod`) and the boundary hypothesis package is `IBP u`.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Coercivity.Defs
import Submission.Work.Coercivity.Basic
import Submission.Work.Coercivity.pz_mul_w
import Submission.Work.Spaces.HardyZ
import Submission.Work.Coercivity.l_self_w_sq_eq
import Submission.Work.Coercivity.deriv_zw_sq_eq
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

namespace Work.Coercivity

set_option autoImplicit false

/-- **The `z`-integration by parts of §6, on a single `θ`-slice.**  For `u` satisfying the
analytic hypothesis package `IBP` and every `θ ∈ Iθ`,

  `∫₀^∞ z ∂_z((u(z,θ) w(z))²) dz = - ∫₀^∞ (u(z,θ) w(z))² dz`.

The derivative of `z (u w)²` is `(u w)² + z ∂_z((u w)²)` (product rule), and the integral of
that derivative over `(0,∞)` is `0` because `z (u w)² → 0` at `0⁺` (`IBP.bd0`) and at `∞`
(`IBP.bdTop`) — this is `deriv_zw_sq_integral`.  Integrating `(0,∞)` instead of `[0,∞)`
is harmless: the two sets differ by the null set `{0}`. -/
theorem slice_z_deriv_integral {u : ℝ → ℝ → ℝ} (hu : IBP u) {θ : ℝ} (hθ : θ ∈ Spaces.Iθ) :
    ∫ z in Spaces.Iz, z * deriv (fun z' => (u z' θ * Spaces.w z') ^ 2) z
      = -∫ z in Spaces.Iz, (u z θ * Spaces.w z) ^ 2 := by
  have hftc := deriv_zw_sq_integral hu hθ
  have hintD : IntegrableOn
      (fun z => deriv (fun z' => z' * (u z' θ * Spaces.w z') ^ 2) z) (Set.Ioi 0) :=
    hu.intDeriv θ hθ
  have hintSq : IntegrableOn (fun z => (u z θ * Spaces.w z) ^ 2) (Set.Ioi 0) :=
    hu.intSq θ hθ
  have hIzeq : Spaces.Iz =ᵐ[(volume : Measure ℝ)] Set.Ioi 0 := by
    rw [MeasureTheory.ae_eq_set]
    refine ⟨?_, ?_⟩
    · have h : Spaces.Iz \ Set.Ioi 0 = {0} := by
        ext x
        simp only [Set.mem_sdiff, Set.mem_Ioi, Set.mem_singleton_iff, Spaces.Iz, Set.mem_Ici,
          not_lt]
        constructor
        · rintro ⟨h1, h2⟩; exact le_antisymm h2 h1
        · rintro rfl; exact ⟨le_refl 0, le_refl 0⟩
      rw [h, Real.volume_singleton]
    · have h : Set.Ioi (0:ℝ) \ Spaces.Iz = ∅ := by
        rw [Spaces.Iz, Set.sdiff_eq_empty]
        exact Set.Ioi_subset_Ici_self
      rw [h, MeasureTheory.measure_empty]
  have hsub : ∫ z in Set.Ioi (0:ℝ),
        (deriv (fun z' => z' * (u z' θ * Spaces.w z') ^ 2) z - (u z θ * Spaces.w z) ^ 2)
      = - ∫ z in Set.Ioi (0:ℝ), (u z θ * Spaces.w z) ^ 2 := by
    rw [MeasureTheory.integral_sub hintD hintSq, hftc, zero_sub]
  have hcongr : ∫ z in Set.Ioi (0:ℝ),
        (deriv (fun z' => z' * (u z' θ * Spaces.w z') ^ 2) z - (u z θ * Spaces.w z) ^ 2)
      = ∫ z in Set.Ioi (0:ℝ), z * deriv (fun z' => (u z' θ * Spaces.w z') ^ 2) z := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun z hz => ?_)
    rw [deriv_zw_sq_eq hu hz hθ]; ring
  have hL : ∫ z in Spaces.Iz, z * deriv (fun z' => (u z' θ * Spaces.w z') ^ 2) z
      = ∫ z in Set.Ioi (0:ℝ), z * deriv (fun z' => (u z' θ * Spaces.w z') ^ 2) z :=
    MeasureTheory.setIntegral_congr_set hIzeq
  have hR : ∫ z in Spaces.Iz, (u z θ * Spaces.w z) ^ 2
      = ∫ z in Set.Ioi (0:ℝ), (u z θ * Spaces.w z) ^ 2 :=
    MeasureTheory.setIntegral_congr_set hIzeq
  rw [hL, hR, ← hcongr, hsub]

/-- The integrand `𝓛u · u · w²σ` on the product `Iz × Iθ`. -/
def LwF (u : ℝ → ℝ → ℝ) (sigma : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  L u p.1 p.2 * u p.1 p.2 * Spaces.w p.1 ^ 2 * sigma p.2

/-- The integrand `u² w²σ` on the product `Iz × Iθ`. -/
def RwF (u : ℝ → ℝ → ℝ) (sigma : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  u p.1 p.2 ^ 2 * Spaces.w p.1 ^ 2 * sigma p.2

/-- The integrand `z ∂_z((u w)²) σ` on the product `Iz × Iθ`. -/
def DwF (u : ℝ → ℝ → ℝ) (sigma : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  p.1 * deriv (fun z' => (u z' p.2 * Spaces.w z') ^ 2) p.1 * sigma p.2

theorem wip_L_self (u : ℝ → ℝ → ℝ) (hu : IBP u) (sigma : ℝ → ℝ)
    (hint : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => u z θ ^ 2 * Spaces.w z ^ 2 * sigma θ))
      (Spaces.Iz ×ˢ Spaces.Iθ))
    (hint2 : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => L u z θ * u z θ * Spaces.w z ^ 2 * sigma θ))
      (Spaces.Iz ×ˢ Spaces.Iθ)) :
    wip (fun z θ => Spaces.w z ^ 2 * sigma θ) (L u) u
      = (1 / 2) * wip (fun z θ => Spaces.w z ^ 2 * sigma θ) u u := by
  set μ : MeasureTheory.Measure ℝ := MeasureTheory.volume.restrict Spaces.Iz with hμ
  set ν : MeasureTheory.Measure ℝ := MeasureTheory.volume.restrict Spaces.Iθ with hν
  have hmeas : μ.prod ν
      = (volume : MeasureTheory.Measure (ℝ × ℝ)).restrict (Spaces.Iz ×ˢ Spaces.Iθ) := by
    rw [hμ, hν, MeasureTheory.Measure.prod_restrict,
      ← MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
  have hF1 : MeasureTheory.Integrable (LwF u sigma) (μ.prod ν) := by
    rw [hmeas]
    exact hint2
  have hF2 : MeasureTheory.Integrable (RwF u sigma) (μ.prod ν) := by
    rw [hmeas]
    exact hint
  -- a.e. positivity in the radial variable
  have haepos : ∀ᵐ p ∂(μ.prod ν), 0 < p.1 := by
    have hslice : ∀ᵐ z ∂μ, 0 < z := by
      rw [hμ, MeasureTheory.ae_restrict_iff (p := fun z => 0 < z) measurableSet_Ioi,
        MeasureTheory.ae_iff]
      have hset : {z : ℝ | ¬ (z ∈ Spaces.Iz → 0 < z)} = {0} := by
        ext z
        simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, Spaces.Iz, Set.mem_Ici, not_imp]
        constructor
        · rintro ⟨h1, h2⟩; exact le_antisymm (not_lt.mp h2) h1
        · intro h; rw [h]; exact ⟨le_refl 0, lt_irrefl 0⟩
      rw [hset, Real.volume_singleton]
    have h : ∀ᵐ p ∂(μ.prod ν), p ∈ Set.Ioi (0:ℝ) ×ˢ Set.univ :=
      (MeasureTheory.Measure.ae_prod_mem_iff_ae_ae_mem
        (s := Set.Ioi (0:ℝ) ×ˢ Set.univ) (measurableSet_Ioi.prod MeasurableSet.univ)).mpr
        (hslice.mono (fun x hx => Filter.Eventually.of_forall (fun _ => by simp [hx])))
    simpa using h
  -- a.e. membership of the angle in the interval
  have haeθ : ∀ᵐ p ∂(μ.prod ν), p.2 ∈ Spaces.Iθ := by
    have h : ∀ᵐ p ∂(μ.prod ν), p ∈ Set.univ ×ˢ Spaces.Iθ :=
      (MeasureTheory.Measure.ae_prod_mem_iff_ae_ae_mem
        (s := Set.univ ×ˢ Spaces.Iθ) (MeasurableSet.univ.prod measurableSet_Icc)).mpr
        (Filter.Eventually.of_forall
          (fun _ => (MeasureTheory.ae_restrict_mem measurableSet_Icc).mono
            (fun y hy => by
              simpa only [Set.mem_prod, Set.mem_univ, true_and, Spaces.Iθ] using hy)))
    simpa using h
  -- the pointwise identity `𝓛u·u·w²σ = u²w²σ + ½ z∂_z((uw)²)σ`, a.e. on the product
  have hae_id : ∀ᵐ p ∂(μ.prod ν),
      LwF u sigma p = RwF u sigma p + (1 / 2) * DwF u sigma p := by
    filter_upwards [haepos, haeθ] with p hp hθ
    have h := l_self_w_sq_eq hu hp hθ
    dsimp only [LwF, RwF, DwF]
    rw [h]; ring
  have hF3 : MeasureTheory.Integrable (DwF u sigma) (μ.prod ν) := by
    have h2 : MeasureTheory.Integrable
        (fun p => 2 * LwF u sigma p - 2 * RwF u sigma p) (μ.prod ν) :=
      (hF1.const_mul 2).sub (hF2.const_mul 2)
    refine h2.congr ?_
    filter_upwards [hae_id] with p hp
    linarith
  have hΦval : ∫ p, LwF u sigma p ∂(μ.prod ν)
      = ∫ p, RwF u sigma p ∂(μ.prod ν) + (1 / 2) * ∫ p, DwF u sigma p ∂(μ.prod ν) := by
    rw [MeasureTheory.integral_congr_ae hae_id]
    rw [MeasureTheory.integral_add hF2 (hF3.const_mul (1 / 2)),
      MeasureTheory.integral_const_mul]
  -- the derivative term is minus the norm: Fubini in `θ`, then the slice identity
  have hDval : ∫ p, DwF u sigma p ∂(μ.prod ν) = -∫ p, RwF u sigma p ∂(μ.prod ν) := by
    have hinner : (fun θ => ∫ z, DwF u sigma (z, θ) ∂μ)
        =ᵐ[ν] (fun θ => -∫ z, RwF u sigma (z, θ) ∂μ) := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      have h1 : (∫ z, DwF u sigma (z, θ) ∂μ)
          = (∫ z, z * deriv (fun z' => (u z' θ * Spaces.w z') ^ 2) z ∂μ) * sigma θ := by
        dsimp only [DwF]
        rw [MeasureTheory.integral_mul_const]
      have h2 : (∫ z, z * deriv (fun z' => (u z' θ * Spaces.w z') ^ 2) z ∂μ)
          = -(∫ z, (u z θ * Spaces.w z) ^ 2 ∂μ) := by
        rw [show (∫ z, z * deriv (fun z' => (u z' θ * Spaces.w z') ^ 2) z ∂μ)
            = ∫ z in Spaces.Iz, z * deriv (fun z' => (u z' θ * Spaces.w z') ^ 2) z from rfl,
          show (∫ z, (u z θ * Spaces.w z) ^ 2 ∂μ)
            = ∫ z in Spaces.Iz, (u z θ * Spaces.w z) ^ 2 from rfl,
          slice_z_deriv_integral hu hθ]
      have h3 : (∫ z, RwF u sigma (z, θ) ∂μ)
          = (∫ z, (u z θ * Spaces.w z) ^ 2 ∂μ) * sigma θ := by
        dsimp only [RwF]
        rw [MeasureTheory.integral_mul_const]
        congr 1
        exact MeasureTheory.integral_congr_ae
          (Filter.Eventually.of_forall (fun z => by ring))
      rw [h1, h2, h3]; ring
    rw [MeasureTheory.integral_prod_symm (DwF u sigma) hF3,
      MeasureTheory.integral_congr_ae hinner, MeasureTheory.integral_neg,
      ← MeasureTheory.integral_prod_symm (RwF u sigma) hF2]
  -- Fubini bridge: both `wip`s are product-measure integrals
  have hint2' : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => L u z θ * u z θ * (Spaces.w z ^ 2 * sigma θ)))
      (Spaces.Iz ×ˢ Spaces.Iθ) := by
    refine hint2.congr ?_
    filter_upwards with p
    dsimp only [Function.uncurry]
    ring
  have hint' : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => u z θ * u z θ * (Spaces.w z ^ 2 * sigma θ)))
      (Spaces.Iz ×ˢ Spaces.Iθ) := by
    refine hint.congr ?_
    filter_upwards with p
    dsimp only [Function.uncurry]
    ring
  have hwL : wip (fun z θ => Spaces.w z ^ 2 * sigma θ) (L u) u
      = ∫ p, LwF u sigma p ∂(μ.prod ν) := by
    rw [wip_eq_integral_prod (fun z θ => Spaces.w z ^ 2 * sigma θ) (L u) u hint2']
    rw [hμ, hν]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with p
    dsimp only [LwF, Function.uncurry]
    ring
  have hwR : wip (fun z θ => Spaces.w z ^ 2 * sigma θ) u u
      = ∫ p, RwF u sigma p ∂(μ.prod ν) := by
    rw [wip_eq_integral_prod (fun z θ => Spaces.w z ^ 2 * sigma θ) u u hint']
    rw [hμ, hν]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with p
    dsimp only [RwF, Function.uncurry]
    ring
  rw [hwL, hwR, hΦval, hDval]
  ring

end Work.Coercivity
