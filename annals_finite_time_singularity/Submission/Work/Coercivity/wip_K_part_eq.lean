import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Coercivity.Defs
import Submission.Work.Coercivity.Basic
import Submission.Work.Coercivity.L12_z_byparts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set

namespace Work.Coercivity

/-- The `K`-part of the `L₁₂` integration by parts, in the product-measure form used by
the `L²` coercivity chain: with `K(θ) = 3 sin θ cos²θ` and `L₁₂(f)(z) = ∫_z^∞ ∫_θ K f/s`,

`∫∫ 2 K(θ) f(z,θ) (w(z)/z · L₁₂(f)(z)) = -2 ∫_0^∞ (1+z)/z³ · L₁₂(f)(z)² dz`.

This is `L12_z_byparts` with the `θ`-integral performed first (Fubini) and the factor `2`
pulled out; the angular integral `∫_θ K(θ)f(z,θ)dθ = z · L₁₂-density(z)` is exactly the
density produced by differentiating `L₁₂(f)`. -/
theorem wip_K_part_eq (f : ℝ → ℝ → ℝ) (hfH : HardyHyp f)
    (hint : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => 2 * Spaces.K θ * f z θ * (Spaces.w z / z * L12f f z)))
      (Spaces.Iz ×ˢ Spaces.Iθ)) :
    (∫ p : ℝ × ℝ, 2 * Spaces.K p.2 * f p.1 p.2 * (Spaces.w p.1 / p.1 * L12f f p.1)
        ∂((MeasureTheory.volume.restrict Spaces.Iz).prod (MeasureTheory.volume.restrict Spaces.Iθ)))
      = -2 * ∫ z in Set.Ioi (0 : ℝ), (1 + z) / z ^ 3 * (L12f f z) ^ 2 := by
  -- The product of the two restricted measures is the restriction of the product measure
  -- to the quadrant; this is what lets Fubini consume `hint` directly.
  have hvol : MeasureTheory.volume.restrict (Spaces.Iz ×ˢ Spaces.Iθ)
      = (MeasureTheory.volume.restrict Spaces.Iz).prod
          (MeasureTheory.volume.restrict Spaces.Iθ) := by
    rw [MeasureTheory.Measure.volume_eq_prod]
    exact (MeasureTheory.Measure.prod_restrict _ _).symm
  set G : ℝ → ℝ → ℝ :=
    fun z θ => 2 * Spaces.K θ * f z θ * (Spaces.w z / z * L12f f z) with hGdef
  have hInt : Integrable (Function.uncurry G)
      ((MeasureTheory.volume.restrict Spaces.Iz).prod
        (MeasureTheory.volume.restrict Spaces.Iθ)) := by
    rw [← hvol]
    exact hint
  change (∫ p : ℝ × ℝ, Function.uncurry G p
      ∂((MeasureTheory.volume.restrict Spaces.Iz).prod
        (MeasureTheory.volume.restrict Spaces.Iθ)))
    = -2 * ∫ z in Set.Ioi (0 : ℝ), (1 + z) / z ^ 3 * (L12f f z) ^ 2
  -- Step 1: Fubini
  have step1 : (∫ p : ℝ × ℝ, Function.uncurry G p
        ∂((MeasureTheory.volume.restrict Spaces.Iz).prod
          (MeasureTheory.volume.restrict Spaces.Iθ)))
      = ∫ z in Spaces.Iz, ∫ θ in Spaces.Iθ, G z θ := by
    rw [MeasureTheory.integral_prod (Function.uncurry G) hInt]
    simp only [Function.uncurry]
  -- Step 2: the `θ`-integral factors out the coefficient that is constant in `θ`
  have step2 : (∫ z in Spaces.Iz, ∫ θ in Spaces.Iθ, G z θ)
      = ∫ z in Spaces.Iz,
          2 * (Spaces.w z / z * L12f f z) * (∫ θ in Spaces.Iθ, Spaces.K θ * f z θ) := by
    refine MeasureTheory.setIntegral_congr_fun ?_ ?_
    · rw [Spaces.Iz]; exact measurableSet_Ici
    · intro z _
      show (∫ θ in Spaces.Iθ, G z θ)
        = 2 * (Spaces.w z / z * L12f f z) * (∫ θ in Spaces.Iθ, Spaces.K θ * f z θ)
      have hfun : G z
          = fun θ => (2 * (Spaces.w z / z * L12f f z)) * (Spaces.K θ * f z θ) := by
        funext θ
        simp only [hGdef]
        ring
      rw [hfun, MeasureTheory.integral_const_mul]
  -- Step 3: `Iz = [0,∞)` and `(0,∞)` differ by the null set `{0}`
  have hae : Spaces.Iz =ᵐ[MeasureTheory.volume] Set.Ioi (0 : ℝ) := by
    rw [Spaces.Iz, MeasureTheory.ae_eq_set]
    constructor
    · have hset : Set.Ici (0 : ℝ) \ Set.Ioi (0 : ℝ) = {0} := by
        ext x
        simp only [Set.mem_sdiff, Set.mem_Ici, Set.mem_Ioi, Set.mem_singleton_iff]
        constructor
        · rintro ⟨h1, h2⟩; linarith
        · rintro rfl; exact ⟨le_refl 0, lt_irrefl 0⟩
      rw [hset]; exact measure_singleton 0
    · have hset : Set.Ioi (0 : ℝ) \ Set.Ici (0 : ℝ) = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        rintro x ⟨h1, h2⟩
        exact h2 (Set.mem_Ici.mpr (le_of_lt (Set.mem_Ioi.mp h1)))
      rw [hset]; simp
  have step3 : (∫ z in Spaces.Iz,
        2 * (Spaces.w z / z * L12f f z) * (∫ θ in Spaces.Iθ, Spaces.K θ * f z θ))
      = ∫ z in Set.Ioi (0 : ℝ),
          2 * (Spaces.w z / z * L12f f z) * (∫ θ in Spaces.Iθ, Spaces.K θ * f z θ) :=
    MeasureTheory.setIntegral_congr_set hae
  -- Step 4: pull the factor `2` out of the integral
  have step4 : (∫ z in Set.Ioi (0 : ℝ),
        2 * (Spaces.w z / z * L12f f z) * (∫ θ in Spaces.Iθ, Spaces.K θ * f z θ))
      = 2 * ∫ z in Set.Ioi (0 : ℝ),
          (Spaces.w z / z * L12f f z) * (∫ θ in Spaces.Iθ, Spaces.K θ * f z θ) := by
    rw [show (fun z => 2 * (Spaces.w z / z * L12f f z)
          * (∫ θ in Spaces.Iθ, Spaces.K θ * f z θ))
        = fun z => 2 * ((Spaces.w z / z * L12f f z)
          * (∫ θ in Spaces.Iθ, Spaces.K θ * f z θ)) from by funext z; ring]
    rw [MeasureTheory.integral_const_mul]
  -- Step 5: the radial integration by parts, from the same joint integrability
  have hint' : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Spaces.w z / z * L12f f z * (Spaces.K θ * f z θ)))
      (Spaces.Iz ×ˢ Spaces.Iθ) := by
    have hmain : Integrable
        (Function.uncurry (fun z θ => 2 * Spaces.K θ * f z θ * (Spaces.w z / z * L12f f z)))
        (MeasureTheory.volume.restrict (Spaces.Iz ×ˢ Spaces.Iθ)) := hint
    refine (hmain.const_mul ((1 : ℝ) / 2)).congr ?_
    filter_upwards with p
    simp only [Function.uncurry]
    ring
  have hkey : (∫ z in Set.Ioi (0 : ℝ),
        (Spaces.w z / z * L12f f z) * (∫ θ in Spaces.Iθ, Spaces.K θ * f z θ))
      = - ∫ z in Set.Ioi (0 : ℝ), (1 + z) / z ^ 3 * (L12f f z) ^ 2 :=
    L12_z_byparts f hfH hint'
  rw [step1, step2, step3, step4, hkey]
  ring

end Work.Coercivity
