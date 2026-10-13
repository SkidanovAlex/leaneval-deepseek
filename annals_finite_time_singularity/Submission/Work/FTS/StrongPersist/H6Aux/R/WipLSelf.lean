import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Coercivity.Defs
import Submission.Work.FTS.StrongPersist.H6Aux.wip_Dz_ibp
import Submission.Work.Coercivity.wip_eq_integral_prod
import Submission.Work.FTS.EllipticEst.weight_algebra_fts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `⟨𝓛u, u⟩_{w²σ} = ½ ⟨u,u⟩_{w²σ}` from the `D_z`-IBP hypotheses

The paper's identity `𝓛u · u · w² = (u w)² + ½ z ∂_z((u w)²)` integrates (against the
angular weight `σ`) to

  `wip (w²σ) (𝓛u) u = ½ ∫∫ u² w² σ`,

i.e. `𝓛` is self-adjoint for the weighted `L²` pairing.  The file
`Submission/Work/Coercivity/wip_L_self.lean` proves this from the *analytic* hypothesis
package `IBP u` (boundary limits assumed), and
`Submission/Work/FTS/CoercivityFix/Coer1/zIBP.lean` from `SmoothQuad` plus the boundary
limits.  Here the hypotheses are the three *integrability* assumptions
(`u²w²σ`, `(D_z u)·u·w²σ` and `u²·∂_z(z w²)·σ`) together with `SmoothOpen u`; the
boundary terms of the `z`-integration by parts are then *derived* from integrability by
`Work.FTS.StrongPersist.H6Aux.wip_Dz_ibp`.

The proof is pure algebra once the IBP is available.  Writing `ρ = w²σ` and `Φ = w²`:

* `𝓛u · u · ρ = u²ρ + (D_z u)·u·ρ - 2u²ρ/(1+z)` (pointwise, the definition of `𝓛`),
* `∫∫ (D_z u)·u·ρ = -(1/2) ∫∫ u² ∂_z(zΦ) σ` (`wip_Dz_ibp`),
* `∂_z(z Φ) = ((z-3)/(1+z)) Φ` for `z > 0`
  (`Work.FTS.EllipticEst.weight_algebra_fts`), hence *pointwise*

  `u²ρ + (1/2)(u² ∂_z(zΦ) σ - u²ρ) = u²ρ - 2u²ρ/(1+z)`,

so the three pieces combine to `(1/2)∫∫ u²ρ`.

The whole computation is lifted to the product measure `μ ⊗ ν`
(`μ = volume.restrict I_z`, `ν = volume.restrict I_θ`), where the linearity of the
integral is available unconditionally; the bridge is
`Work.Coercivity.wip_eq_integral_prod`.
-/

namespace Work.FTS.StrongPersist.H6Aux.R

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Product-measure bookkeeping -/

/-- The restriction of the plane Lebesgue measure to `I_z ×ˢ I_θ` is the product of the two
restricted measures. -/
private theorem volume_restrict_prod_loc :
    volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
      = (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ) := by
  rw [MeasureTheory.Measure.volume_eq_prod]
  exact (MeasureTheory.Measure.prod_restrict _ _).symm

/-- `IntegrableOn` on the quadrant is `Integrable` against the product of the two restricted
measures. -/
private theorem integrableOn_prod_iff_loc {g : ℝ → ℝ → ℝ} :
    MeasureTheory.IntegrableOn (Function.uncurry g) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
      ↔ MeasureTheory.Integrable (fun p : ℝ × ℝ => g p.1 p.2)
          ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
  rw [MeasureTheory.IntegrableOn, volume_restrict_prod_loc]
  rfl

/-- Almost every point of the product measure has positive first coordinate. -/
private theorem ae_prod_pos_loc :
    ∀ᵐ p ∂((volume.restrict Work.Spaces.Iz).prod
      (volume.restrict Work.Spaces.Iθ)), 0 < p.1 := by
  rw [MeasureTheory.ae_iff]
  have hset : {p : ℝ × ℝ | ¬ (0 < p.1)} = Set.Iic (0 : ℝ) ×ˢ Set.univ := by
    ext p
    simp only [Set.mem_setOf_eq, not_lt, Set.mem_prod, Set.mem_Iic, Set.mem_univ, and_true]
  have hIz : (volume.restrict Work.Spaces.Iz) (Set.Iic (0 : ℝ)) = 0 := by
    rw [MeasureTheory.Measure.restrict_apply measurableSet_Iic]
    have hI : Work.Spaces.Iz ∩ Set.Iic (0 : ℝ) = {0} := by
      ext z
      simp only [Work.Spaces.Iz, Set.mem_inter_iff, Set.mem_Ici, Set.mem_Iic,
        Set.mem_singleton_iff]
      constructor
      · rintro ⟨h1, h2⟩; exact le_antisymm h2 h1
      · rintro rfl; exact ⟨le_refl 0, le_refl 0⟩
    rw [Set.inter_comm, hI, Real.volume_singleton]
  rw [hset, MeasureTheory.Measure.prod_prod, hIz, zero_mul]

/-- The derivative of the derived weight `z ↦ z·w z²`, in the factored form used to match the
weight `w²` itself: `∂_z(z w²) = ((z-3)/(1+z))·w²` for `z > 0`. -/
private theorem deriv_zw2 {z : ℝ} (hz : 0 < z) :
    deriv (fun y : ℝ => y * (Work.Spaces.w y) ^ 2) z
      = (Work.Spaces.w z) ^ 2 * ((z - 3) / (1 + z)) := by
  rw [Work.FTS.EllipticEst.weight_algebra_fts.2.2.2.1 z (ne_of_gt hz)]
  have hz0 : z ≠ 0 := ne_of_gt hz
  have h1z : (1 : ℝ) + z ≠ 0 := by linarith
  rw [Work.Spaces.w]
  field_simp

/-! ## The four integrands, on the product -/

/-- `u·u·w²σ`. -/
private def pAF (u : ℝ → ℝ → ℝ) (σ : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  u p.1 p.2 * u p.1 p.2 * ((Work.Spaces.w p.1) ^ 2 * σ p.2)

/-- `(D_z u)·u·w²σ`. -/
private def pBF (u : ℝ → ℝ → ℝ) (σ : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  Work.Spaces.Dz u p.1 p.2 * u p.1 p.2 * ((Work.Spaces.w p.1) ^ 2 * σ p.2)

/-- `u·u·∂_z(z·w²)·σ`. -/
private def pDF (u : ℝ → ℝ → ℝ) (σ : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  u p.1 p.2 * u p.1 p.2
    * (deriv (fun y : ℝ => y * (Work.Spaces.w y) ^ 2) p.1 * σ p.2)

/-- `(𝓛u)·u·w²σ`. -/
private def pLF (u : ℝ → ℝ → ℝ) (σ : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  Work.Coercivity.L u p.1 p.2 * u p.1 p.2 * ((Work.Spaces.w p.1) ^ 2 * σ p.2)

theorem WipLSelf {u : ℝ → ℝ → ℝ} {σ : ℝ → ℝ}
    (hs : Work.FTS.EllipticEst.SmoothOpen u)
    (h1 : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => u z θ ^ 2 * (Work.Spaces.w z) ^ 2 * σ θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (h2 : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.Dz u z θ * u z θ * (Work.Spaces.w z) ^ 2 * σ θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (h3 : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => u z θ ^ 2 * deriv (fun z' => z' * (Work.Spaces.w z') ^ 2) z
        * σ θ)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    Work.Coercivity.wip (fun z θ => (Work.Spaces.w z) ^ 2 * σ θ) (Work.Coercivity.L u) u
      = (1 / 2) * (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          u z θ ^ 2 * ((Work.Spaces.w z) ^ 2 * σ θ)) := by
  set m : MeasureTheory.Measure (ℝ × ℝ) :=
    (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ) with hm
  -- ## 0.  The weight `Φ = w²` is `C¹` on `(0,∞)`
  have hΦ : ContDiffOn ℝ 1 (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi 0) := by
    have hw1 : ContDiffOn ℝ 1 (fun z : ℝ => Work.Spaces.w z) (Set.Ioi 0) := by
      show ContDiffOn ℝ 1 (fun z : ℝ => (1 + z) ^ 2 / z ^ 2) (Set.Ioi 0)
      exact ContDiffOn.div (by fun_prop) (by fun_prop)
        (fun z hz => pow_ne_zero 2 (ne_of_gt (show (0 : ℝ) < z from hz)))
    exact hw1.pow 2
  -- ## 1.  The three integrands in `wip`-shape
  have h1w : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => u z θ * u z θ * ((Work.Spaces.w z) ^ 2 * σ θ)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    refine h1.congr ?_
    filter_upwards with p
    dsimp only [Function.uncurry]
    ring
  have h2w : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.Dz u z θ * u z θ
        * ((Work.Spaces.w z) ^ 2 * σ θ))) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    refine h2.congr ?_
    filter_upwards with p
    dsimp only [Function.uncurry]
    ring
  have h3w : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => u z θ * u z θ
        * (deriv (fun z' => z' * (Work.Spaces.w z') ^ 2) z * σ θ)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    refine h3.congr ?_
    filter_upwards with p
    dsimp only [Function.uncurry]
    ring
  -- ## 2.  The `z`-integration by parts, from `wip_Dz_ibp`
  have hDz : Work.Coercivity.wip (fun z θ => (Work.Spaces.w z) ^ 2 * σ θ)
        (Work.Spaces.Dz u) u
      = -(1 / 2) * (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          u z θ ^ 2 * deriv (fun z' => z' * (Work.Spaces.w z') ^ 2) z * σ θ) :=
    Work.FTS.StrongPersist.H6Aux.wip_Dz_ibp (h := u)
      (Φ := fun z : ℝ => (Work.Spaces.w z) ^ 2) (σ := σ) hs hΦ h1 h2 h3
  -- ## 3.  Integrability of the four product integrands
  have hAFint : MeasureTheory.Integrable (pAF u σ) m := by
    rw [hm]
    exact integrableOn_prod_iff_loc.mp h1w
  have hBFint : MeasureTheory.Integrable (pBF u σ) m := by
    rw [hm]
    exact integrableOn_prod_iff_loc.mp h2w
  have hDFint : MeasureTheory.Integrable (pDF u σ) m := by
    rw [hm]
    exact integrableOn_prod_iff_loc.mp h3w
  -- the `2u²ρ/(1+z)` piece, dominated by `2u²ρ` because `1+z ≥ 1` on `Iz`
  have hCint : MeasureTheory.Integrable
      (fun p : ℝ × ℝ =>
        2 * (u p.1 p.2 * u p.1 p.2 * ((Work.Spaces.w p.1) ^ 2 * σ p.2)) / (1 + p.1)) m := by
    have hbase : MeasureTheory.Integrable
        (fun p : ℝ × ℝ =>
          2 * (u p.1 p.2 * u p.1 p.2 * ((Work.Spaces.w p.1) ^ 2 * σ p.2))) m :=
      hAFint.const_mul 2
    have hg : AEStronglyMeasurable (fun p : ℝ × ℝ => (1 : ℝ) / (1 + p.1)) m :=
      ((((measurable_const : Measurable fun _ : ℝ => (1 : ℝ)).div
          (measurable_const.add measurable_id))).comp measurable_fst).aestronglyMeasurable
    have hbdd : ∀ᵐ p ∂m, ‖(1 : ℝ) / (1 + p.1)‖ ≤ (1 : ℝ) := by
      filter_upwards [ae_prod_pos_loc] with p hp
      have hz : (0 : ℝ) ≤ p.1 := le_of_lt hp
      have h1p : (0 : ℝ) < 1 + p.1 := by linarith
      rw [Real.norm_eq_abs, abs_div, abs_of_pos h1p, abs_one, div_le_one h1p]
      linarith
    refine (hbase.mul_bdd hg hbdd).congr ?_
    filter_upwards with p
    rw [div_eq_mul_inv]
    ring
  -- `𝓛u·u·ρ` is integrable: it is `u²ρ + (D_z u)uρ - 2u²ρ/(1+z)`
  have hLFint : MeasureTheory.Integrable (pLF u σ) m := by
    have hsum : MeasureTheory.Integrable
        (fun p : ℝ × ℝ =>
          u p.1 p.2 * u p.1 p.2 * ((Work.Spaces.w p.1) ^ 2 * σ p.2)
            + Work.Spaces.Dz u p.1 p.2 * u p.1 p.2 * ((Work.Spaces.w p.1) ^ 2 * σ p.2)
            - 2 * (u p.1 p.2 * u p.1 p.2 * ((Work.Spaces.w p.1) ^ 2 * σ p.2))
                / (1 + p.1)) m :=
      (hAFint.add hBFint).sub hCint
    refine hsum.congr ?_
    filter_upwards with p
    simp only [pLF, Work.Coercivity.L, Work.Spaces.Dz]
    ring
  have hHalfint : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (1 / 2) * (pDF u σ p - pAF u σ p)) m :=
    (hDFint.sub hAFint).const_mul (1 / 2)
  -- ## 4.  The `wip`-to-product conversions
  have hwipA : Work.Coercivity.wip (fun z θ => (Work.Spaces.w z) ^ 2 * σ θ) u u
      = ∫ p, pAF u σ p ∂m := by
    rw [Work.Coercivity.wip_eq_integral_prod (fun z θ => (Work.Spaces.w z) ^ 2 * σ θ) u u h1w]
    rw [hm]
    simp only [pAF]
  have hwipB : Work.Coercivity.wip (fun z θ => (Work.Spaces.w z) ^ 2 * σ θ)
        (Work.Spaces.Dz u) u = ∫ p, pBF u σ p ∂m := by
    rw [Work.Coercivity.wip_eq_integral_prod (fun z θ => (Work.Spaces.w z) ^ 2 * σ θ)
      (Work.Spaces.Dz u) u h2w]
    rw [hm]
    simp only [pBF]
  have hDconv : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        u z θ ^ 2 * deriv (fun z' => z' * (Work.Spaces.w z') ^ 2) z * σ θ)
      = ∫ p, pDF u σ p ∂m := by
    have hstep1 : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          u z θ ^ 2 * deriv (fun z' => z' * (Work.Spaces.w z') ^ 2) z * σ θ)
        = Work.Coercivity.wip
            (fun z θ => deriv (fun z' => z' * (Work.Spaces.w z') ^ 2) z * σ θ) u u := by
      simp only [Work.Coercivity.wip]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
      ring
    have hstep2 : Work.Coercivity.wip
          (fun z θ => deriv (fun z' => z' * (Work.Spaces.w z') ^ 2) z * σ θ) u u
        = ∫ p, pDF u σ p ∂m := by
      rw [Work.Coercivity.wip_eq_integral_prod
        (fun z θ => deriv (fun z' => z' * (Work.Spaces.w z') ^ 2) z * σ θ) u u h3w]
      rw [hm]
      simp only [pDF]
    exact hstep1.trans hstep2
  have hwipL : Work.Coercivity.wip (fun z θ => (Work.Spaces.w z) ^ 2 * σ θ)
        (Work.Coercivity.L u) u = ∫ p, pLF u σ p ∂m := by
    rw [Work.Coercivity.wip_eq_integral_prod (fun z θ => (Work.Spaces.w z) ^ 2 * σ θ)
      (Work.Coercivity.L u) u
      ((integrableOn_prod_iff_loc
        (g := fun z θ => Work.Coercivity.L u z θ * u z θ * ((Work.Spaces.w z) ^ 2 * σ θ))).mpr
        hLFint)]
    rw [hm]
    simp only [pLF]
  -- ## 5.  The `D_z`-pairing, in product form
  have hBF_eq : ∫ p, pBF u σ p ∂m = -(1 / 2) * ∫ p, pDF u σ p ∂m := by
    rw [← hwipB, hDz, hDconv]
  -- ## 6.  The pointwise identity and the split of the integral
  have hid : pLF u σ =ᵐ[m] (fun p : ℝ × ℝ =>
      pAF u σ p + pBF u σ p + (1 / 2) * (pDF u σ p - pAF u σ p)) := by
    filter_upwards [ae_prod_pos_loc] with p hp
    have hder := deriv_zw2 hp
    have h1z : (1 : ℝ) + p.1 ≠ 0 := by linarith
    simp only [pLF, pAF, pBF, pDF, Work.Coercivity.L, Work.Spaces.Dz]
    rw [hder]
    field_simp
    ring
  have hstep : ∫ p, pLF u σ p ∂m
      = (∫ p, pAF u σ p ∂m) + (∫ p, pBF u σ p ∂m)
        + (1 / 2) * ((∫ p, pDF u σ p ∂m) - (∫ p, pAF u σ p ∂m)) := by
    have e0 : ∫ p, pLF u σ p ∂m
        = ∫ p, pAF u σ p + pBF u σ p + (1 / 2) * (pDF u σ p - pAF u σ p) ∂m :=
      MeasureTheory.integral_congr_ae hid
    have e1 : ∫ p, pAF u σ p + pBF u σ p + (1 / 2) * (pDF u σ p - pAF u σ p) ∂m
        = (∫ p, pAF u σ p + pBF u σ p ∂m)
          + (∫ p, (1 / 2) * (pDF u σ p - pAF u σ p) ∂m) :=
      MeasureTheory.integral_add (hAFint.add hBFint) hHalfint
    have e2 : ∫ p, pAF u σ p + pBF u σ p ∂m
        = (∫ p, pAF u σ p ∂m) + (∫ p, pBF u σ p ∂m) :=
      MeasureTheory.integral_add hAFint hBFint
    have e3 : ∫ p, (1 / 2) * (pDF u σ p - pAF u σ p) ∂m
        = (1 / 2) * ∫ p, pDF u σ p - pAF u σ p ∂m :=
      MeasureTheory.integral_const_mul (1 / 2) _
    have e4 : ∫ p, pDF u σ p - pAF u σ p ∂m
        = (∫ p, pDF u σ p ∂m) - (∫ p, pAF u σ p ∂m) :=
      MeasureTheory.integral_sub hDFint hAFint
    rw [e0, e1, e2, e3, e4]
  -- ## 7.  Assembly
  have hkey : Work.Coercivity.wip (fun z θ => (Work.Spaces.w z) ^ 2 * σ θ)
        (Work.Coercivity.L u) u
      = (1 / 2) * Work.Coercivity.wip (fun z θ => (Work.Spaces.w z) ^ 2 * σ θ) u u := by
    rw [hwipL, hstep, hBF_eq, ← hwipA]
    ring
  have hR : Work.Coercivity.wip (fun z θ => (Work.Spaces.w z) ^ 2 * σ θ) u u
      = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          u z θ ^ 2 * ((Work.Spaces.w z) ^ 2 * σ θ) := by
    simp only [Work.Coercivity.wip]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    ring
  rw [hkey, hR]

end

end Work.FTS.StrongPersist.H6Aux.R
