/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsE4Thr/L12JepsAux/Inner.lean`

The **inner** differentiation step of the target `Work.FTS.StrongEps.EpsE4Thr.L12JepsDeriv`: for a
fixed radius `r > 0`, the derivative in the fake time of the angular integral
`L12dens K (J_ε (slice g ·)) r` is the angular integral of the derivative profile.

The three analytic inputs are hypotheses here and are discharged in the final file:

* `hint` — the `p`-integrability of the value integrand (the target's `hint` at `(r,θ)`);
* `hbd` — a bound for the right-hand-side profile over the shifted points (the target's `hbdU r hr`);
* `hvalBd` — a bound for the value profile over the shifted points (the target's `hsliceU r hr`);
* `hmeasV`/`hmeasD` — the a.e.-strong measurability *in `θ`* of `J_ε` of the two profiles on
  `[0, π/2]`.  This is the genuinely non-elementary input (produced from the all-`(r,θ)`
  integrability `hint` in `L12JepsAux.Basic`/`aesm_Jeps_slice_of_aesm_logPull`); it is *not*
  supplied by the target's hypotheses on their face, because a Bochner integral of a merely
  `p`-integrable integrand need not be measurable in `θ`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Submission.Work.FTS.StrongEps.EpsE4Thr.L12JepsAux.Basic
import Submission.Work.FTS.StrongEps.EpsE4Thr.Jeps_family_deriv

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Topology
open Work.FTS.StrongEps (Jeps Jker zShift thShift IsMollKernel IsSmoothKernel
  epsRHSP IsEpsSolP abs_Jeps_le_sup Jeps_eq_zero)
open Work.FTS.Galerkin (Fn Fam slice)

namespace Work.FTS.StrongEps.EpsE4Thr.L12JepsAux

set_option autoImplicit false

/-- `K` is continuous. -/
lemma continuous_K : Continuous Work.Spaces.K := by
  show Continuous fun θ : ℝ => 3 * Real.sin θ * Real.cos θ ^ 2
  fun_prop

/-- The angular weight of `L₁₂` is bounded by `3` on the whole line (in particular on `Iθ`). -/
lemma abs_K_le (θ : ℝ) : |Work.Spaces.K θ| ≤ 3 := by
  have h1 : |Real.sin θ| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_sin θ, Real.sin_le_one θ⟩
  have h2 : Real.cos θ ^ 2 ≤ 1 := by
    nlinarith [Real.cos_le_one θ, Real.neg_one_le_cos θ]
  rw [Work.Spaces.K, abs_mul, abs_mul, abs_sq, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
  nlinarith [abs_nonneg (Real.sin θ), h1, h2]

/-- **The inner differentiation**: for every `r > 0`, the fake-time derivative of the angular
density `L12dens K (J_ε (slice g x)) r` at `τ` is `L12dens K (J_ε (epsRHSP … g τ)) r`. -/
theorem hasDerivAt_L12dens_Jeps {ρ : ℝ × ℝ → ℝ} {α T ε r : ℝ} {Φs : Fn} {E : Fn → Fn}
    {g₀ : Fn} {g : Fam} {τ : ℝ}
    (hρ : IsMollKernel ρ) (hε : 0 < ε) (hr : 0 < r)
    (hsol : IsEpsSolP α ρ ε T Φs E g₀ g) (hτ : τ ∈ Set.Ioo 0 T)
    (hint : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), ∀ s ∈ Set.Icc 0 T,
      MeasureTheory.Integrable (fun p : ℝ × ℝ => Jker ρ ε p *
        slice g s (zShift r p.1) (thShift θ p.2)) MeasureTheory.volume)
    (hbd : ∃ C : ℝ, 0 ≤ C ∧ ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), ∀ p : ℝ × ℝ, ‖p‖ ≤ ε →
      ∀ s ∈ Set.Icc 0 T,
        |epsRHSP α ρ ε Φs E g s (zShift r p.1) (thShift θ p.2)| ≤ C)
    (hvalBd : ∃ C : ℝ, 0 ≤ C ∧ ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), ∀ p : ℝ × ℝ, ‖p‖ ≤ ε →
      |slice g τ (zShift r p.1) (thShift θ p.2)| ≤ C)
    (hmeasV : ∀ x ∈ Set.Ioo 0 T, MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => Jeps ρ ε (slice g x) r θ)
      (MeasureTheory.volume.restrict (Set.Icc 0 (Real.pi / 2))))
    (hmeasD : MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => Jeps ρ ε (epsRHSP α ρ ε Φs E g τ) r θ)
      (MeasureTheory.volume.restrict (Set.Icc 0 (Real.pi / 2)))) :
    HasDerivAt (fun x => Work.FM.L12dens Work.Spaces.K (Jeps ρ ε (slice g x)) r)
      (Work.FM.L12dens Work.Spaces.K (Jeps ρ ε (epsRHSP α ρ ε Φs E g τ)) r) τ := by
  obtain ⟨Cd, hCd0, hCd⟩ := hbd
  obtain ⟨Cv, hCv0, hCv⟩ := hvalBd
  have hs : Set.Ioo (0 : ℝ) T ∈ 𝓝 τ := isOpen_Ioo.mem_nhds hτ
  -- `θ` lies in the open interval almost everywhere on `[0, π/2]`
  have haeθ : ∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.Icc 0 (Real.pi / 2))),
      θ ∈ Set.Ioo 0 (Real.pi / 2) := by
    rw [← MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc' (μ := MeasureTheory.volume) (by simp) (by simp))]
    exact MeasureTheory.self_mem_ae_restrict measurableSet_Ioo
  -- strong measurability of the two `θ`-integrands
  have hmeasV' : ∀ᶠ x in 𝓝 τ, MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => Work.Spaces.K θ * Jeps ρ ε (slice g x) r θ / r)
      (MeasureTheory.volume.restrict (Set.Icc 0 (Real.pi / 2))) := by
    filter_upwards [hs] with x hx
    have h := ((hmeasV x hx).mul (continuous_K.aestronglyMeasurable)).mul_const (r⁻¹)
    refine h.congr (Eventually.of_forall fun θ => ?_)
    simp only [Pi.mul_apply, div_eq_mul_inv]
    ring
  have hmeasD' : MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => Work.Spaces.K θ * Jeps ρ ε (epsRHSP α ρ ε Φs E g τ) r θ / r)
      (MeasureTheory.volume.restrict (Set.Icc 0 (Real.pi / 2))) := by
    have h := (hmeasD.mul (continuous_K.aestronglyMeasurable)).mul_const (r⁻¹)
    refine h.congr (Eventually.of_forall fun θ => ?_)
    simp only [Pi.mul_apply, div_eq_mul_inv]
    ring
  -- integrability at the base point
  have hF_int : MeasureTheory.Integrable
      (fun θ : ℝ => Work.Spaces.K θ * Jeps ρ ε (slice g τ) r θ / r)
      (MeasureTheory.volume.restrict (Set.Icc 0 (Real.pi / 2))) := by
    have hm : MeasureTheory.AEStronglyMeasurable
        (fun θ : ℝ => Work.Spaces.K θ * Jeps ρ ε (slice g τ) r θ / r)
        (MeasureTheory.volume.restrict (Set.Icc 0 (Real.pi / 2))) := by
      have h := ((hmeasV τ hτ).mul (continuous_K.aestronglyMeasurable)).mul_const (r⁻¹)
      refine h.congr (Eventually.of_forall fun θ => ?_)
      simp only [Pi.mul_apply, div_eq_mul_inv]
      ring
    refine MeasureTheory.Integrable.of_bound hm (3 * Cv / r) ?_
    refine Eventually.of_forall fun θ => ?_
    by_cases hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)
    · have hJ : |Jeps ρ ε (slice g τ) r θ| ≤ Cv :=
        abs_Jeps_le_sup ρ hρ hε hr hθ
          (fun p hp1 hp2 => hCv θ hθ p (norm_le_of_abs_le hp1 hp2)) hCv0
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hr, abs_mul]
      exact div_le_div_of_nonneg_right
        (mul_le_mul (abs_K_le θ) hJ (abs_nonneg _) (by norm_num)) hr.le
    · rw [Jeps_eq_zero ρ ε _ (fun hc => hθ hc.2), mul_zero, zero_div, norm_zero]
      exact div_nonneg (mul_nonneg (by norm_num) hCv0) hr.le
  -- the dominating function
  have hbd_int : MeasureTheory.Integrable (fun _ : ℝ => 3 * Cd / r)
      (MeasureTheory.volume.restrict (Set.Icc 0 (Real.pi / 2))) := by
    rw [MeasureTheory.integrable_const_iff]; exact Or.inr inferInstance
  have h_bound : ∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.Icc 0 (Real.pi / 2))),
      ∀ x ∈ Set.Ioo (0 : ℝ) T,
        ‖Work.Spaces.K θ * Jeps ρ ε (epsRHSP α ρ ε Φs E g x) r θ / r‖ ≤ 3 * Cd / r := by
    refine Eventually.of_forall fun θ x hx => ?_
    by_cases hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)
    · have hJ : |Jeps ρ ε (epsRHSP α ρ ε Φs E g x) r θ| ≤ Cd :=
        abs_Jeps_le_sup ρ hρ hε hr hθ
          (fun p hp1 hp2 => hCd θ hθ p (norm_le_of_abs_le hp1 hp2) x ⟨hx.1.le, hx.2.le⟩) hCd0
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hr, abs_mul]
      exact div_le_div_of_nonneg_right
        (mul_le_mul (abs_K_le θ) hJ (abs_nonneg _) (by norm_num)) hr.le
    · rw [Jeps_eq_zero ρ ε _ (fun hc => hθ hc.2), mul_zero, zero_div, norm_zero]
      exact div_nonneg (mul_nonneg (by norm_num) hCd0) hr.le
  -- the pointwise derivative, from `Jeps_family_deriv`
  have h_diff : ∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.Icc 0 (Real.pi / 2))),
      ∀ x ∈ Set.Ioo (0 : ℝ) T,
        HasDerivAt (fun y => Work.Spaces.K θ * Jeps ρ ε (slice g y) r θ / r)
          (Work.Spaces.K θ * Jeps ρ ε (epsRHSP α ρ ε Φs E g x) r θ / r) x := by
    filter_upwards [haeθ] with θ hθ x hx
    have hW : ∀ s ∈ Set.Ioo 0 T, ∀ y φ : ℝ, 0 < y → φ ∈ Set.Ioo 0 (Real.pi / 2) →
        HasDerivAt (fun t => slice g t y φ) (epsRHSP α ρ ε Φs E g s y φ) s := by
      intro s hs' y φ hy hφ
      exact (hsol.2 y φ s hy hφ ⟨hs'.1.le, hs'.2.le⟩).hasDerivAt (Icc_mem_nhds hs'.1 hs'.2)
    have hder := Jeps_family_deriv hρ hε hW hr hθ (fun s hs' => hint θ hθ s hs')
      ⟨Cd, hCd0, fun p hp s hs' => hCd θ hθ p hp s hs'⟩ hx
    have h1 : HasDerivAt (fun t => Jeps ρ ε (slice g t) r θ)
        (Jeps ρ ε (epsRHSP α ρ ε Φs E g x) r θ) x :=
      hder.hasDerivAt (Icc_mem_nhds hx.1 hx.2)
    have h2 : HasDerivAt (fun y => (Work.Spaces.K θ / r) * Jeps ρ ε (slice g y) r θ)
        ((Work.Spaces.K θ / r) * Jeps ρ ε (epsRHSP α ρ ε Φs E g x) r θ) x :=
      h1.const_mul (Work.Spaces.K θ / r)
    have hfun : (fun y => (Work.Spaces.K θ / r) * Jeps ρ ε (slice g y) r θ)
        = fun y => Work.Spaces.K θ * Jeps ρ ε (slice g y) r θ / r :=
      funext fun y => by ring
    rw [hfun] at h2
    convert h2 using 1
    ring
  -- the parametric differentiation lemma
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := MeasureTheory.volume.restrict (Set.Icc 0 (Real.pi / 2)))
    (𝕜 := ℝ) (E := ℝ)
    (F := fun x θ => Work.Spaces.K θ * Jeps ρ ε (slice g x) r θ / r)
    (F' := fun x θ => Work.Spaces.K θ * Jeps ρ ε (epsRHSP α ρ ε Φs E g x) r θ / r)
    (bound := fun _ : ℝ => 3 * Cd / r)
    (x₀ := τ) (s := Set.Ioo 0 T) hs hmeasV' hF_int hmeasD' h_bound hbd_int h_diff
  simpa only [Work.FM.L12dens] using hmain.2

end Work.FTS.StrongEps.EpsE4Thr.L12JepsAux
