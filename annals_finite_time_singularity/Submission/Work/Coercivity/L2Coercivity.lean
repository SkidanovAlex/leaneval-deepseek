/-
# Proposition `L2Coercivity`: coercivity of `𝓛_Γ` in the weighted `L²` space

This file proves Proposition `prop:L2Coercivity` of

  T. M. Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the
  incompressible Euler equations on `ℝ³`*, Annals of Math. **194** (2021),

namely

  `(𝓛_Γ(f) w, f w)_{L²} ≥ 1/4 |f w|²_{L²}`,

which in the notation of this development (`wip ρ g₁ g₂ = ∫∫ g₁ g₂ ρ`, `Ef f = |f w|²_{L²}`)
reads

  `(1/4) * Ef f ≤ wip (fun z _ => w z ^ 2) (LGamma α f) f`.

## The proof

Following the paper, with `w = (1+z)²/z²` and `g(z,θ) = 2zΓ(θ)/(c(1+z)²)`:

* `𝓛_Γ(f) = 𝓛(f) - g·L₁₂(f)`, hence
  `(𝓛_Γ(f)w, fw) = (𝓛(f)w, fw) - ∫∫ g L₁₂(f) f w²`;
* `(𝓛(f)w, fw) = ½ |fw|²` by the `z`-integration by parts `wip_L_self`
  (the paper's identity `𝓛(g)w = gw + z∂_z(gw)`);
* splitting `Γ/c = K + (Γ/c - K)` and using `w² z/(1+z)² = w/z`, the `L₁₂`-term becomes
  the sum of `∫∫ 2 K f (w/z) L₁₂(f)` and `∫∫ 2(Γ/c - K) f w (L₁₂(f)/z)`; the first is
  `-2∫₀^∞ (1+z)/z³ L₁₂(f)²` (`L12_z_byparts` + Fubini), which is `≥ -2 EL12z f`; the
  second is bounded (`wip_G_bound`, which needs `0 < α` so that `Γ` is bounded and the
  integral defining `GammaL2Bnd` is the honest one) by Cauchy–Schwarz in `θ` and then in
  `z`, using `|Γ/c - K|_{L²_θ} ≤ 7/10`, by `(7/5)√(Ef f)√(EL12z f)`;
* `½x² + 2y² - (7/5)xy ≥ ¼x²` because `(7/5)² < 4·(1/4)·2 = 2`, giving the claim.

All the `wip`s are honest absolutely convergent integrals: the hypothesis package
`CoerciveData` supplies the joint integrability of every integrand occurring in the
computation (`intL`, `intL12`, `intK`, `intG`, `intFeta`, …).
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Coercivity.Defs
import Submission.Work.Coercivity.Basic
import Submission.Work.Coercivity.wip_L_self
import Submission.Work.Coercivity.L12_z_byparts
import Submission.Work.Coercivity.f_sq_w_sq_integrable
import Submission.Work.Coercivity.wip_K_part_eq
import Submission.Work.Coercivity.integrableOn_GammaK_sq
import Submission.Work.Coercivity.wip_G_bound

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

/-- The restricted product measure `volume.restrict (Iz ×ˢ Iθ)` is the product of the two
restricted measures; this is the bridge that lets us use Mathlib's Fubini and
integrability API (stated for product measures) on the joint integrability hypotheses of
`CoerciveData`, which are stated for `Iz ×ˢ Iθ`. -/
private theorem integrableOn_prod {g : ℝ → ℝ → ℝ}
    (h : IntegrableOn (Function.uncurry g) (Spaces.Iz ×ˢ Spaces.Iθ)) :
    Integrable (fun p : ℝ × ℝ => g p.1 p.2)
      ((volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ)) := by
  have hvol : volume.restrict (Spaces.Iz ×ˢ Spaces.Iθ)
      = (volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ) := by
    rw [Measure.volume_eq_prod]
    exact (Measure.prod_restrict _ _).symm
  rw [IntegrableOn, hvol] at h
  exact h

/-- The pointwise algebra behind the decomposition of the `L₁₂`-term of `𝓛_Γ`: with
`w = (1+z)²/z²` and `z ≠ 0`, `c ≠ 0`,

`2zΓ/(c(1+z)²) · L · f · w² = 2K f (w/z) L + 2(Γ/c - K) f w (L/z)`.

(Both sides are also `0` at `z = 0`, which is why the identity is applied only a.e.) -/
private theorem split_pointwise {c Γ K L f : ℝ} {z : ℝ} (hc : c ≠ 0) (hz : z ≠ 0) :
    2 * z * Γ / (c * (1 + z) ^ 2) * L * f * Spaces.w z ^ 2
      = 2 * K * f * (Spaces.w z / z * L) + 2 * (Γ / c - K) * f * Spaces.w z * (L / z) := by
  simp only [Spaces.w]
  field_simp
  ring

/-- **Proposition `L2Coercivity` of the paper**: the weighted `L²` coercivity of
`𝓛_Γ`, `(𝓛_Γ(f)w, fw)_{L²} ≥ 1/4 |fw|²_{L²}`. -/
theorem L2Coercivity (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f : ℝ → ℝ → ℝ)
    (hf : IBP f) (hfH : HardyHyp f) (hΓ : GammaL2Bnd α) (hi : CoerciveData α f) :
    (1 / 4) * Ef f ≤ wip (fun z _ => Spaces.w z ^ 2) (LGamma α f) f := by
  set P : Measure (ℝ × ℝ) := (volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ) with hP
  have hc : Spaces.c α ≠ 0 := c_ne_zero hα hα1
  -- ## Joint integrability, transported to the product measure
  have h2 : IntegrableOn (Function.uncurry (fun z θ => f z θ * f z θ * Spaces.w z ^ 2))
      (Spaces.Iz ×ˢ Spaces.Iθ) := f_sq_w_sq_integrable α f hi
  have hF1 : Integrable (fun p : ℝ × ℝ => L f p.1 p.2 * f p.1 p.2 * Spaces.w p.1 ^ 2) P :=
    integrableOn_prod hi.intL
  have hF4 : Integrable (fun p : ℝ × ℝ =>
      (2 * p.1 * Spaces.Gam α p.2 / (Spaces.c α * (1 + p.1) ^ 2)) * L12f f p.1
        * f p.1 p.2 * Spaces.w p.1 ^ 2) P := integrableOn_prod hi.intL12
  have hF5 : Integrable (fun p : ℝ × ℝ =>
      2 * Spaces.K p.2 * f p.1 p.2 * (Spaces.w p.1 / p.1 * L12f f p.1)) P := by
    have h := integrableOn_prod (g := fun z θ => Spaces.w z / z * L12f f z * (Spaces.K θ * f z θ)) hi.intK
    exact (h.const_mul 2).congr (Eventually.of_forall fun p => by ring)
  have hF6 : Integrable (fun p : ℝ × ℝ =>
      2 * (Spaces.Gam α p.2 / Spaces.c α - Spaces.K p.2) * f p.1 p.2 * Spaces.w p.1
        * (L12f f p.1 / p.1)) P := by
    have h := integrableOn_prod (g := fun z θ =>
        Spaces.w z / z * L12f f z * ((Spaces.Gam α θ / Spaces.c α - Spaces.K θ) * f z θ)) hi.intG
    exact (h.const_mul 2).congr (Eventually.of_forall fun p => by ring)
  -- ## Step 1: `wip` as a product-measure integral
  have hwipLG : wip (fun z _ => Spaces.w z ^ 2) (LGamma α f) f
      = ∫ p, LGamma α f p.1 p.2 * f p.1 p.2 * Spaces.w p.1 ^ 2 ∂P := by
    rw [hP]
    exact wip_eq_integral_prod (fun z _ => Spaces.w z ^ 2) (LGamma α f) f (by simpa using hi.intLG)
  have hwipL : wip (fun z _ => Spaces.w z ^ 2) (L f) f
      = ∫ p, L f p.1 p.2 * f p.1 p.2 * Spaces.w p.1 ^ 2 ∂P := by
    rw [hP]
    exact wip_eq_integral_prod (fun z _ => Spaces.w z ^ 2) (L f) f (by simpa using hi.intL)
  -- ## Step 2: `𝓛_Γ(f) = 𝓛(f) - g L₁₂(f)`
  have hsplit : (∫ p, LGamma α f p.1 p.2 * f p.1 p.2 * Spaces.w p.1 ^ 2 ∂P)
      = (∫ p, L f p.1 p.2 * f p.1 p.2 * Spaces.w p.1 ^ 2 ∂P)
        - (∫ p, (2 * p.1 * Spaces.Gam α p.2 / (Spaces.c α * (1 + p.1) ^ 2))
            * L12f f p.1 * f p.1 p.2 * Spaces.w p.1 ^ 2 ∂P) := by
    rw [← MeasureTheory.integral_sub hF1 hF4]
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun p => ?_)
    simp only [LGamma]
    ring
  -- ## Step 3: `(𝓛(f)w, fw) = ½|fw|²` (the `z`-integration by parts for `𝓛`)
  have hLhalf : (∫ p, L f p.1 p.2 * f p.1 p.2 * Spaces.w p.1 ^ 2 ∂P) = (1 / 2) * Ef f := by
    rw [← hwipL, Ef_eq_wip]
    have h1 : IntegrableOn (Function.uncurry (fun z θ =>
        f z θ ^ 2 * Spaces.w z ^ 2 * (fun _ => (1 : ℝ)) θ)) (Spaces.Iz ×ˢ Spaces.Iθ) := by
      refine h2.congr (Eventually.of_forall fun p => ?_)
      simp only [Function.uncurry]
      ring
    have h2' : IntegrableOn (Function.uncurry (fun z θ =>
        L f z θ * f z θ * Spaces.w z ^ 2 * (fun _ => (1 : ℝ)) θ)) (Spaces.Iz ×ˢ Spaces.Iθ) := by
      refine hi.intL.congr (Eventually.of_forall fun p => ?_)
      simp only [Function.uncurry]
      ring
    have h := wip_L_self f hf (fun _ => (1 : ℝ)) h1 h2'
    simpa using h
  -- ## Step 4: splitting `Γ/c = K + (Γ/c - K)` in the `L₁₂`-term
  have hTsum : (∫ p, (2 * p.1 * Spaces.Gam α p.2 / (Spaces.c α * (1 + p.1) ^ 2))
        * L12f f p.1 * f p.1 p.2 * Spaces.w p.1 ^ 2 ∂P)
      = (∫ p, 2 * Spaces.K p.2 * f p.1 p.2 * (Spaces.w p.1 / p.1 * L12f f p.1) ∂P)
        + (∫ p, 2 * (Spaces.Gam α p.2 / Spaces.c α - Spaces.K p.2) * f p.1 p.2
            * Spaces.w p.1 * (L12f f p.1 / p.1) ∂P) := by
    rw [← MeasureTheory.integral_add hF5 hF6]
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun p => ?_)
    show 2 * p.1 * Spaces.Gam α p.2 / (Spaces.c α * (1 + p.1) ^ 2) * L12f f p.1
        * f p.1 p.2 * Spaces.w p.1 ^ 2
      = 2 * Spaces.K p.2 * f p.1 p.2 * (Spaces.w p.1 / p.1 * L12f f p.1)
        + 2 * (Spaces.Gam α p.2 / Spaces.c α - Spaces.K p.2) * f p.1 p.2
            * Spaces.w p.1 * (L12f f p.1 / p.1)
    by_cases hz : p.1 = 0
    · rw [hz]; simp [Spaces.w]
    · exact split_pointwise hc hz
  -- ## Joint integrability of the two pieces of the `L₁₂`-term
  have hintK : IntegrableOn (Function.uncurry (fun z θ =>
      2 * Spaces.K θ * f z θ * (Spaces.w z / z * L12f f z))) (Spaces.Iz ×ˢ Spaces.Iθ) := by
    have h : IntegrableOn (Function.uncurry (fun z θ =>
        2 * (Spaces.w z / z * L12f f z * (Spaces.K θ * f z θ)))) (Spaces.Iz ×ˢ Spaces.Iθ) :=
      hi.intK.const_mul 2
    refine h.congr (Eventually.of_forall fun p => ?_)
    simp only [Function.uncurry]
    ring
  have hintG : IntegrableOn (Function.uncurry (fun z θ =>
      2 * (Spaces.Gam α θ / Spaces.c α - Spaces.K θ) * f z θ * Spaces.w z
        * (L12f f z / z))) (Spaces.Iz ×ˢ Spaces.Iθ) := by
    have h : IntegrableOn (Function.uncurry (fun z θ =>
        2 * (Spaces.w z / z * L12f f z * ((Spaces.Gam α θ / Spaces.c α - Spaces.K θ) * f z θ))))
        (Spaces.Iz ×ˢ Spaces.Iθ) := hi.intG.const_mul 2
    refine h.congr (Eventually.of_forall fun p => ?_)
    simp only [Function.uncurry]
    ring
  -- ## Step 5: the two radial integrals of the paper
  set Y : ℝ := ∫ z in Set.Ioi (0 : ℝ), (1 + z) / z ^ 3 * (L12f f z) ^ 2 with hY
  set Z : ℝ := ∫ z in Set.Ioi (0 : ℝ), (L12f f z) ^ 2 / z ^ 2 with hZ
  have hEL : EL12z f = Z := by
    rw [hZ]
    simp only [EL12z, L2Sqz, Spaces.Iz]
    rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun z => ?_)
    exact div_pow (L12f f z) z 2
  -- the `K`-piece is `-2Y` (`L12_z_byparts`, i.e. the definition of `L₁₂`)
  have hWK : (∫ p, 2 * Spaces.K p.2 * f p.1 p.2 * (Spaces.w p.1 / p.1 * L12f f p.1) ∂P) = -2 * Y := by
    rw [hP, hY]
    exact wip_K_part_eq f hfH hintK
  -- the `(Γ/c - K)`-piece is bounded by `(7/5)√(Ef)√(EL12z)` (Cauchy–Schwarz twice)
  have hBsq : IntegrableOn
      (fun θ : ℝ => (Spaces.Gam α θ / Spaces.c α - Spaces.K θ) ^ 2) Spaces.Iθ :=
    integrableOn_GammaK_sq α hα hα1
  have hWG : (∫ p, 2 * (Spaces.Gam α p.2 / Spaces.c α - Spaces.K p.2) * f p.1 p.2 * Spaces.w p.1
        * (L12f f p.1 / p.1) ∂P) ≤ (7 / 5) * Real.sqrt (Ef f) * Real.sqrt Z := by
    have h := (abs_le.mp (wip_G_bound α hα hα1 f hfH h2 hΓ hBsq hintG)).2
    rw [hEL] at h
    exact h
  -- `Z ≤ Y`, since `(1+z)/z³ ≥ 1/z²` on `(0,∞)`
  have hZY : Z ≤ Y := by
    rw [hZ, hY]
    refine MeasureTheory.integral_mono_ae ?_ (L12_z_byparts_rhs_integrable f hfH) ?_
    · refine (hfH.intA 1 (by norm_num)).congr (Eventually.of_forall fun z => ?_)
      norm_num
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
      have hz0 : 0 < z := hz
      rw [← sub_nonneg]
      have hsub : (1 + z) / z ^ 3 * (L12f f z) ^ 2 - (L12f f z) ^ 2 / z ^ 2
          = (L12f f z) ^ 2 / z ^ 3 := by
        field_simp
        ring
      rw [hsub]
      positivity
  -- ## Step 6: the numerical conclusion `½x² + 2y² - (7/5)xy ≥ ¼x²`
  have hEfnn : 0 ≤ Ef f := by
    rw [Ef, Spaces.L2Sq]
    exact integral_nonneg fun z => integral_nonneg fun θ => sq_nonneg _
  have hZnn : 0 ≤ Z := by
    rw [hZ]
    exact integral_nonneg fun z => div_nonneg (sq_nonneg _) (sq_nonneg _)
  have hnum : (1 / 2) * Ef f + 2 * Z - (7 / 5) * Real.sqrt (Ef f) * Real.sqrt Z ≥ (1 / 4) * Ef f := by
    nlinarith [Real.sq_sqrt hEfnn, Real.sq_sqrt hZnn,
      sq_nonneg (Real.sqrt (Ef f) - 14 / 5 * Real.sqrt Z), sq_nonneg (Real.sqrt Z)]
  calc wip (fun z _ => Spaces.w z ^ 2) (LGamma α f) f
      = (1 / 2) * Ef f - (∫ p, 2 * Spaces.K p.2 * f p.1 p.2 * (Spaces.w p.1 / p.1 * L12f f p.1) ∂P)
          - (∫ p, 2 * (Spaces.Gam α p.2 / Spaces.c α - Spaces.K p.2) * f p.1 p.2
              * Spaces.w p.1 * (L12f f p.1 / p.1) ∂P) := by
        rw [hwipLG, hsplit, hLhalf, hTsum]; ring
    _ = (1 / 2) * Ef f + 2 * Y - (∫ p, 2 * (Spaces.Gam α p.2 / Spaces.c α - Spaces.K p.2)
              * f p.1 p.2 * Spaces.w p.1 * (L12f f p.1 / p.1) ∂P) := by
        rw [hWK]; ring
    _ ≥ (1 / 2) * Ef f + 2 * Z - (7 / 5) * Real.sqrt (Ef f) * Real.sqrt Z := by
        linarith [hWG, hZY]
    _ ≥ (1 / 4) * Ef f := hnum

end Work.Coercivity
