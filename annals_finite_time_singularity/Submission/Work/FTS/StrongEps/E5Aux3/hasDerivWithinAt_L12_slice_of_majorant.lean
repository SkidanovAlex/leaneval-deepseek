import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Submission.Work.FTS.Galerkin.Defs
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongEps.PZero
import Submission.Work.FM.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.StrongEps.E5Aux3.hasDerivWithinAt_L12_slice_of_majorant`

The fake-time derivative of the `L₁₂`-zero mode of the (unmollified) family:

  `∂_τ L₁₂ (slice g τ)(0) = L₁₂ (epsRHSP … g τ)(0)`,

i.e. the `(j,i) = (0,0)` slot of the chain rule for `IsEpsSolP` families, with the *σ-uniform*
majorant `hmaj` replacing the window bounds that the mollified siblings need.

Two differentiations under the integral:

* **inner** (`θ`-level, `hasDerivAt_L12dens_slice`): for every `r > 0`, the map
  `σ ↦ L12dens K (slice g σ) r = ∫_θ K(θ)·g(r,θ,σ)/r dθ` has derivative
  `L12dens K (epsRHSP … g τ) r` at interior points of `Icc 0 T`.  The pointwise-in-`θ`
  derivative is `hsol`; the domination is the pointwise bound of `hmaj`, and the
  integrability of the value integrand is `hmaj`'s `θ`-integrability of `G`.
* **outer** (`r`-level): `hasDerivAt_integral_of_dominated_loc_of_deriv_le` with the majorant
  `bound r := ∫_θ G r θ ds` (integrable by `hmaj`), the value integrability `hval` and the
  a.e.-measurability of the derived density `hder`.

The only genuinely non-elementary input is the **a.e. strong measurability in `θ`** of the
right-hand side slice `θ ↦ K(θ)·epsRHSP … g τ r θ / r`
(`aeStronglyMeasurable_K_mul_epsRHSP_slice`): no hypothesis states it, and a derivative of a
function that is merely differentiable in the time variable need not be measurable.  It is
*produced* here from the joint `C¹`-regularity `hcont` of the family, by exhibiting the slice as an
a.e. limit of the continuous difference quotients `(σₙ - τ)⁻¹(g(r,θ,σₙ) - g(r,θ,τ))` along the
sequences `σₙ = τ + (T-τ)/(n+1) ↓ τ` and using the pointwise derivative `hsol`.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.StrongEps.E5Aux3

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-! ## Auxiliary facts about the angular interval and the family -/

/-- `K` is continuous. -/
lemma continuous_K : Continuous Work.Spaces.K := by
  show Continuous fun θ : ℝ => 3 * Real.sin θ * Real.cos θ ^ 2
  fun_prop

/-- `a / r * x = a * x / r`, the form in which the angular density is written. -/
lemma K_div_mul_eq_mul_div (a x r : ℝ) : a / r * x = a * x / r := by ring

/-- `volume.restrict (Ioo 0 (π/2)) = volume.restrict Iθ`. -/
lemma restrict_Ioo_eq_restrict_Icc :
    volume.restrict (Set.Ioo 0 (π / 2)) = volume.restrict (Set.Icc 0 (π / 2)) :=
  MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioo_ae_eq_Icc' (μ := volume) (by simp) (by simp))

/-- Almost every point of `Iθ` lies in the open interval. -/
lemma ae_mem_Ioo_Icc :
    ∀ᵐ θ ∂(volume.restrict (Set.Icc 0 (π / 2))), θ ∈ Set.Ioo 0 (π / 2) := by
  rw [← restrict_Ioo_eq_restrict_Icc]
  exact MeasureTheory.self_mem_ae_restrict measurableSet_Ioo

/-- A function continuous on the open angular interval is a.e.-strongly measurable on `Iθ`. -/
lemma aestronglyMeasurable_restrict_Icc_of_continuousOn_Ioo {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Ioo 0 (π / 2))) :
    MeasureTheory.AEStronglyMeasurable f (volume.restrict (Set.Icc 0 (π / 2))) := by
  rw [← restrict_Ioo_eq_restrict_Icc]
  exact hf.aestronglyMeasurable measurableSet_Ioo

/-- **The `θ`-slice of the family is continuous on the open angular interval.**
This is the `θ ↦ (r, θ, σ)`-slice of the joint `C¹`-regularity `hcont` of the family. -/
lemma continuousOn_slice_of_contDiffOn {T : ℝ} {g : Fam}
    (hcont : ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Icc 0 T))
    {r σ : ℝ} (hr : 0 < r) (hσ : σ ∈ Set.Icc 0 T) :
    ContinuousOn (fun θ : ℝ => g r θ σ) (Set.Ioo 0 (π / 2)) := by
  have hF : ContinuousOn (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Icc 0 T) := hcont.continuousOn
  have hmap : ContinuousOn (fun θ : ℝ => (r, (θ, σ))) (Set.Ioo 0 (π / 2)) :=
    (continuous_const.prodMk (continuous_id.prodMk continuous_const)).continuousOn
  refine (hF.comp hmap ?_)
  intro θ hθ
  exact ⟨hr, hθ, hσ⟩

/-- A bounded integrand dominated (pointwise on `Iθ`) by an integrable function is integrable. -/
lemma integrableOn_K_mul_of_le {f : ℝ → ℝ → ℝ} {r : ℝ} {G : ℝ → ℝ}
    (hmeas : MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => Work.Spaces.K θ * f r θ / r)
      (volume.restrict (Set.Icc 0 (π / 2))))
    (hG : MeasureTheory.Integrable (fun θ : ℝ => G θ) (volume.restrict (Set.Icc 0 (π / 2))))
    (hbd : ∀ θ ∈ Set.Icc 0 (π / 2), ‖Work.Spaces.K θ * f r θ / r‖ ≤ G θ) :
    MeasureTheory.Integrable (fun θ : ℝ => Work.Spaces.K θ * f r θ / r)
      (volume.restrict (Set.Icc 0 (π / 2))) :=
  MeasureTheory.Integrable.mono' hG hmeas
    (by
      filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with θ hθ
      exact hbd θ hθ)

/-- **The angular density is dominated by the `θ`-integral of the majorant.** -/
lemma norm_L12dens_le_integral {f : ℝ → ℝ → ℝ} {r : ℝ} {G : ℝ → ℝ}
    (hmeas : MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => Work.Spaces.K θ * f r θ / r)
      (volume.restrict (Set.Icc 0 (π / 2))))
    (hG : MeasureTheory.Integrable (fun θ : ℝ => G θ) (volume.restrict (Set.Icc 0 (π / 2))))
    (hbd : ∀ θ ∈ Set.Icc 0 (π / 2), ‖Work.Spaces.K θ * f r θ / r‖ ≤ G θ) :
    ‖Work.FM.L12dens Work.Spaces.K f r‖ ≤ ∫ θ in Set.Icc 0 (π / 2), G θ := by
  have hint := integrableOn_K_mul_of_le hmeas hG hbd
  calc ‖Work.FM.L12dens Work.Spaces.K f r‖
      = ‖∫ θ : ℝ, Work.Spaces.K θ * f r θ / r
          ∂(volume.restrict (Set.Icc 0 (π / 2)))‖ := by
        simp only [Work.FM.L12dens]
    _ ≤ ∫ θ : ℝ, ‖Work.Spaces.K θ * f r θ / r‖
          ∂(volume.restrict (Set.Icc 0 (π / 2))) :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ θ : ℝ, G θ ∂(volume.restrict (Set.Icc 0 (π / 2))) :=
        MeasureTheory.integral_mono_ae hint.norm hG
          (by
            filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with θ hθ
            exact hbd θ hθ)

/-! ## Measurability in `θ` of the right-hand-side slice -/

/-- **The `θ`-slice of the right-hand side is a.e.-strongly measurable on `Iθ`.**

The scheme `hsol` gives, at every interior point `x` of the time interval and every `θ` in the
open angular interval, the pointwise derivative of `σ ↦ g r θ σ`; since the slices
`θ ↦ g r θ σₙ` are continuous on the open angular interval (`hcont`), the difference quotients are
continuous, hence a.e.-strongly measurable on `Iθ`, and their a.e. limit — the slice of the right
hand side — inherits measurability. -/
lemma aeStronglyMeasurable_K_mul_epsRHSP_slice {α T ε : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn}
    {E : Fn → Fn} {g₀ : Fn} {g : Fam}
    (hsol : IsEpsSolP α ρ ε T Φs E g₀ g)
    (hcont : ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Icc 0 T))
    {r x : ℝ} (hr : 0 < r) (hx : x ∈ Set.Ioo 0 T) :
    MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => Work.Spaces.K θ * epsRHSP α ρ ε Φs E g x r θ / r)
      (volume.restrict (Set.Icc 0 (π / 2))) := by
  have hxI : x ∈ Set.Icc (0 : ℝ) T := ⟨hx.1.le, hx.2.le⟩
  have hTx : 0 < T - x := by linarith [hx.2]
  set σ : ℕ → ℝ := fun n => x + (T - x) / ((n : ℝ) + 1) with hσ
  have hσn : ∀ n : ℕ, σ n = x + (T - x) / ((n : ℝ) + 1) := fun n => by rw [hσ]
  have hσmem : ∀ n, σ n ∈ Set.Icc (0 : ℝ) T := by
    intro n
    have hden : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hq0 : 0 < (T - x) / ((n : ℝ) + 1) := div_pos hTx hden
    have hq : (T - x) / ((n : ℝ) + 1) ≤ T - x := by
      rw [div_le_iff₀ hden]
      nlinarith
    rw [hσn n]
    exact ⟨by linarith [hx.1], by linarith⟩
  have hσne : ∀ n, σ n ≠ x := by
    intro n h
    have hden : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hq0 : 0 < (T - x) / ((n : ℝ) + 1) := div_pos hTx hden
    rw [hσn n] at h
    linarith
  have hσtend : Tendsto σ atTop (𝓝 x) := by
    have h1 : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      Filter.tendsto_atTop_add_const_right _ 1 (tendsto_natCast_atTop_atTop (R := ℝ))
    have h2 : Tendsto (fun n : ℕ => (T - x) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      Filter.Tendsto.div_atTop tendsto_const_nhds h1
    have h3 : Tendsto (fun n : ℕ => x + (T - x) / ((n : ℝ) + 1)) atTop (𝓝 (x + 0)) :=
      h2.const_add x
    simpa only [hσ, add_zero] using h3
  have hσwithin : Tendsto σ atTop (𝓝[Set.Icc (0 : ℝ) T \ {x}] x) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within σ hσtend
      (Eventually.of_forall fun n => ⟨hσmem n, hσne n⟩)
  have hsl : ∀ n, ContinuousOn (fun θ : ℝ => g r θ (σ n)) (Set.Ioo 0 (π / 2)) :=
    fun n => continuousOn_slice_of_contDiffOn hcont hr (hσmem n)
  have hmeas : ∀ n, MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => slope (fun s => (Work.Spaces.K θ / r) * g r θ s) x (σ n))
      (volume.restrict (Set.Icc 0 (π / 2))) := by
    intro n
    refine aestronglyMeasurable_restrict_Icc_of_continuousOn_Ioo ?_
    have h1 : ContinuousOn (fun θ : ℝ => (Work.Spaces.K θ / r) * g r θ (σ n))
        (Set.Ioo 0 (π / 2)) :=
      (continuous_K.div_const r).continuousOn.mul (hsl n)
    have h2 : ContinuousOn (fun θ : ℝ => (Work.Spaces.K θ / r) * g r θ x)
        (Set.Ioo 0 (π / 2)) :=
      (continuous_K.div_const r).continuousOn.mul
        (continuousOn_slice_of_contDiffOn hcont hr hxI)
    refine ((h1.sub h2).const_mul ((σ n - x)⁻¹)).congr ?_
    intro θ hθ
    simp only [Pi.sub_apply, slope, smul_eq_mul, vsub_eq_sub]
  have hlim : ∀ᵐ θ ∂(volume.restrict (Set.Icc 0 (π / 2))),
      Tendsto (fun n : ℕ => slope (fun s => (Work.Spaces.K θ / r) * g r θ s) x (σ n)) atTop
        (𝓝 (Work.Spaces.K θ * epsRHSP α ρ ε Φs E g x r θ / r)) := by
    filter_upwards [ae_mem_Ioo_Icc] with θ hθ
    have h1 : HasDerivWithinAt (fun s => (Work.Spaces.K θ / r) * g r θ s)
        ((Work.Spaces.K θ / r) * epsRHSP α ρ ε Φs E g x r θ) (Set.Icc 0 T) x :=
      (hsol.2 r θ x hr hθ hxI).const_mul (Work.Spaces.K θ / r)
    have h2 := (hasDerivWithinAt_iff_tendsto_slope.mp h1).comp hσwithin
    have h3 : (Work.Spaces.K θ / r) * epsRHSP α ρ ε Φs E g x r θ
        = Work.Spaces.K θ * epsRHSP α ρ ε Φs E g x r θ / r :=
      K_div_mul_eq_mul_div ..
    rw [h3] at h2
    exact h2
  exact aestronglyMeasurable_of_tendsto_ae atTop hmeas hlim

/-! ## The inner (`θ`-level) differentiation -/

/-- **For fixed `r > 0`, the fake-time derivative of the angular density is the angular density of
the right-hand side.**

This is `hasDerivAt_integral_of_dominated_loc_of_deriv_le` in the angular variable: the pointwise
derivative is `hsol`, the domination is the pointwise bound of `hmaj`, and the base-point
integrability is `hmaj`'s `θ`-integrability of the majorant. -/
lemma hasDerivAt_L12dens_slice {α T ε : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn}
    {g₀ : Fn} {g : Fam} {G : ℝ → ℝ → ℝ}
    (hsol : IsEpsSolP α ρ ε T Φs E g₀ g)
    (hcont : ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Icc 0 T))
    (hGθ : ∀ r ∈ Set.Ioi (0 : ℝ),
      MeasureTheory.IntegrableOn (fun θ : ℝ => G r θ) (Set.Icc 0 (π / 2)))
    (hGbd : ∀ τ ∈ Set.Icc 0 T, ∀ r ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Icc 0 (π / 2),
      ‖Work.Spaces.K θ * slice g τ r θ / r‖ ≤ G r θ ∧
      ‖Work.Spaces.K θ * epsRHSP α ρ ε Φs E g τ r θ / r‖ ≤ G r θ)
    {r : ℝ} (hr : 0 < r) {x : ℝ} (hx : x ∈ Set.Ioo 0 T) :
    HasDerivAt (fun σ : ℝ => Work.FM.L12dens Work.Spaces.K (slice g σ) r)
      (Work.FM.L12dens Work.Spaces.K (epsRHSP α ρ ε Φs E g x) r) x := by
  have hxI : x ∈ Set.Icc (0 : ℝ) T := ⟨hx.1.le, hx.2.le⟩
  have hs : Set.Ioo (0 : ℝ) T ∈ 𝓝 x := isOpen_Ioo.mem_nhds hx
  have hbase := hGθ r hr
  have hsl : ∀ σ ∈ Set.Icc (0 : ℝ) T,
      ContinuousOn (fun θ : ℝ => g r θ σ) (Set.Ioo 0 (π / 2)) :=
    fun σ hσ => continuousOn_slice_of_contDiffOn hcont hr hσ
  have hF_meas : ∀ᶠ σ in 𝓝 x, MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => Work.Spaces.K θ * g r θ σ / r)
      (volume.restrict (Set.Icc 0 (π / 2))) := by
    filter_upwards [hs] with σ hσ
    have h1 : ContinuousOn (fun θ : ℝ => (Work.Spaces.K θ / r) * g r θ σ)
        (Set.Ioo 0 (π / 2)) :=
      (continuous_K.div_const r).continuousOn.mul (hsl σ ⟨hσ.1.le, hσ.2.le⟩)
    refine (aestronglyMeasurable_restrict_Icc_of_continuousOn_Ioo h1).congr
      (Eventually.of_forall fun θ => ?_)
    simp only [K_div_mul_eq_mul_div]
  have hF_int : MeasureTheory.Integrable (fun θ : ℝ => Work.Spaces.K θ * g r θ x / r)
      (volume.restrict (Set.Icc 0 (π / 2))) := by
    have h1 : ContinuousOn (fun θ : ℝ => (Work.Spaces.K θ / r) * g r θ x)
        (Set.Ioo 0 (π / 2)) :=
      (continuous_K.div_const r).continuousOn.mul (hsl x hxI)
    refine integrableOn_K_mul_of_le ?_ hbase (fun θ hθ => (hGbd x hxI r hr θ hθ).1)
    refine (aestronglyMeasurable_restrict_Icc_of_continuousOn_Ioo h1).congr
      (Eventually.of_forall fun θ => ?_)
    simp only [Work.FTS.Galerkin.slice, K_div_mul_eq_mul_div]
  have hF'_meas : MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => Work.Spaces.K θ * epsRHSP α ρ ε Φs E g x r θ / r)
      (volume.restrict (Set.Icc 0 (π / 2))) :=
    aeStronglyMeasurable_K_mul_epsRHSP_slice hsol hcont hr hx
  have h_bound : ∀ᵐ θ ∂(volume.restrict (Set.Icc 0 (π / 2))),
      ∀ σ ∈ Set.Ioo (0 : ℝ) T,
        ‖Work.Spaces.K θ * epsRHSP α ρ ε Φs E g σ r θ / r‖ ≤ G r θ := by
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with θ hθ σ hσ
    exact (hGbd σ ⟨hσ.1.le, hσ.2.le⟩ r hr θ hθ).2
  have h_diff : ∀ᵐ θ ∂(volume.restrict (Set.Icc 0 (π / 2))),
      ∀ σ ∈ Set.Ioo (0 : ℝ) T,
        HasDerivAt (fun s => Work.Spaces.K θ * g r θ s / r)
          (Work.Spaces.K θ * epsRHSP α ρ ε Φs E g σ r θ / r) σ := by
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with θ hθ σ hσ
    by_cases hθo : θ ∈ Set.Ioo 0 (π / 2)
    · have h1 := (hsol.2 r θ σ hr hθo ⟨hσ.1.le, hσ.2.le⟩).hasDerivAt
        (Icc_mem_nhds hσ.1 hσ.2)
      have h2 : HasDerivAt (fun s => (Work.Spaces.K θ / r) * g r θ s)
          ((Work.Spaces.K θ / r) * epsRHSP α ρ ε Φs E g σ r θ) σ :=
        h1.const_mul (Work.Spaces.K θ / r)
      have h3 : (Work.Spaces.K θ / r) * epsRHSP α ρ ε Φs E g σ r θ
          = Work.Spaces.K θ * epsRHSP α ρ ε Φs E g σ r θ / r :=
        K_div_mul_eq_mul_div ..
      rw [h3] at h2
      exact h2.congr_of_eventuallyEq (Eventually.of_forall fun s => by ring)
    · have hθ0 : θ = 0 ∨ θ = π / 2 := by
        rcases lt_or_ge 0 θ with h | h
        · rcases lt_or_eq_of_le hθ.2 with h2 | h2
          · exact absurd ⟨h, h2⟩ hθo
          · exact Or.inr h2
        · exact Or.inl (le_antisymm h hθ.1)
      have hK0 : Work.Spaces.K θ = 0 := by
        rcases hθ0 with rfl | hπ
        · simp [Work.Spaces.K]
        · rw [Work.Spaces.K, hπ]
          simp [Real.cos_pi_div_two]
      have hfun : (fun s : ℝ => Work.Spaces.K θ * g r θ s / r) = fun _ => (0 : ℝ) := by
        funext s
        rw [hK0]
        ring
      have hval : Work.Spaces.K θ * epsRHSP α ρ ε Φs E g σ r θ / r = 0 := by
        rw [hK0]
        ring
      rw [hfun, hval]
      exact hasDerivAt_const σ 0
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Icc 0 (π / 2))) (𝕜 := ℝ) (E := ℝ)
    (F := fun σ θ => Work.Spaces.K θ * g r θ σ / r)
    (F' := fun σ θ => Work.Spaces.K θ * epsRHSP α ρ ε Φs E g σ r θ / r)
    (bound := fun θ => G r θ)
    (x₀ := x) (s := Set.Ioo 0 T) hs hF_meas hF_int hF'_meas h_bound hbase h_diff
  simpa only [Work.FM.L12dens, Work.FTS.Galerkin.slice] using hmain.2

theorem hasDerivWithinAt_L12_slice_of_majorant {α T ε : ℝ} {ρ : ℝ × ℝ → ℝ}
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    {g₀ : Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hsol : Work.FTS.StrongEps.IsEpsSolP α ρ ε T Φs E g₀ g)
    (hcont : ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Icc 0 T))
    (hval : ∀ τ ∈ Set.Icc 0 T, MeasureTheory.IntegrableOn
      (fun r : ℝ => Work.FM.L12dens Work.Spaces.K (Work.FTS.Galerkin.slice g τ) r) (Set.Ioi 0))
    (hder : ∀ τ ∈ Set.Icc 0 T, MeasureTheory.IntegrableOn
      (fun r : ℝ => Work.FM.L12dens Work.Spaces.K
        (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g τ) r) (Set.Ioi 0))
    (hmaj : ∃ G : ℝ → ℝ → ℝ,
      (∀ τ ∈ Set.Icc 0 T,
        MeasureTheory.IntegrableOn (fun r : ℝ => ∫ θ in Work.Spaces.Iθ, G r θ) (Set.Ioi 0)) ∧
      (∀ r ∈ Set.Ioi (0 : ℝ), MeasureTheory.IntegrableOn (fun θ : ℝ => G r θ) Work.Spaces.Iθ) ∧
      ∀ τ ∈ Set.Icc 0 T, ∀ r ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Work.Spaces.Iθ,
        ‖Work.Spaces.K θ * Work.FTS.Galerkin.slice g τ r θ / r‖ ≤ G r θ ∧
        ‖Work.Spaces.K θ * Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g τ r θ / r‖ ≤ G r θ)
    {τ : ℝ} (hτ : τ ∈ Set.Ioo 0 T) :
    HasDerivWithinAt (fun σ : ℝ => Work.Construction.L12 (Work.FTS.Galerkin.slice g σ) 0)
      (Work.Construction.L12 (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g τ) 0) (Set.Icc 0 T) τ := by
  obtain ⟨G, hGint, hGθ, hGbd⟩ := hmaj
  have hτI : τ ∈ Set.Icc (0 : ℝ) T := ⟨hτ.1.le, hτ.2.le⟩
  have hs : Set.Ioo (0 : ℝ) T ∈ 𝓝 τ := isOpen_Ioo.mem_nhds hτ
  -- the inner (`θ`-level) derivative, at every `r > 0` and every interior time
  have hinner : ∀ r ∈ Set.Ioi (0 : ℝ), ∀ σ ∈ Set.Ioo 0 T,
      HasDerivAt (fun σ' : ℝ => Work.FM.L12dens Work.Spaces.K (slice g σ') r)
        (Work.FM.L12dens Work.Spaces.K (epsRHSP α ρ ε Φs E g σ) r) σ :=
    fun r hr σ hσ => hasDerivAt_L12dens_slice hsol hcont hGθ hGbd hr hσ
  have hF_meas : ∀ᶠ σ in 𝓝 τ, MeasureTheory.AEStronglyMeasurable
      (fun r : ℝ => Work.FM.L12dens Work.Spaces.K (slice g σ) r)
      (volume.restrict (Set.Ioi 0)) := by
    filter_upwards [hs] with σ hσ
    exact (hval σ ⟨hσ.1.le, hσ.2.le⟩).aestronglyMeasurable
  have hF_int : MeasureTheory.Integrable
      (fun r : ℝ => Work.FM.L12dens Work.Spaces.K (slice g τ) r)
      (volume.restrict (Set.Ioi 0)) := hval τ hτI
  have hF'_meas : MeasureTheory.AEStronglyMeasurable
      (fun r : ℝ => Work.FM.L12dens Work.Spaces.K (epsRHSP α ρ ε Φs E g τ) r)
      (volume.restrict (Set.Ioi 0)) := (hder τ hτI).aestronglyMeasurable
  have hbd_int : MeasureTheory.Integrable
      (fun r : ℝ => ∫ θ in Set.Icc 0 (π / 2), G r θ) (volume.restrict (Set.Ioi 0)) :=
    hGint τ hτI
  have h_bound : ∀ᵐ r ∂(volume.restrict (Set.Ioi 0)),
      ∀ σ ∈ Set.Ioo (0 : ℝ) T,
        ‖Work.FM.L12dens Work.Spaces.K (epsRHSP α ρ ε Φs E g σ) r‖
          ≤ ∫ θ in Set.Icc 0 (π / 2), G r θ := by
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with r hr σ hσ
    exact norm_L12dens_le_integral
      (aeStronglyMeasurable_K_mul_epsRHSP_slice hsol hcont hr hσ)
      (hGθ r hr)
      (fun θ hθ => (hGbd σ ⟨hσ.1.le, hσ.2.le⟩ r hr θ hθ).2)
  have h_diff : ∀ᵐ r ∂(volume.restrict (Set.Ioi 0)),
      ∀ σ ∈ Set.Ioo (0 : ℝ) T,
        HasDerivAt (fun σ' : ℝ => Work.FM.L12dens Work.Spaces.K (slice g σ') r)
          (Work.FM.L12dens Work.Spaces.K (epsRHSP α ρ ε Φs E g σ) r) σ := by
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with r hr
    exact hinner r hr
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ioi 0)) (𝕜 := ℝ) (E := ℝ)
    (F := fun σ r => Work.FM.L12dens Work.Spaces.K (slice g σ) r)
    (F' := fun σ r => Work.FM.L12dens Work.Spaces.K (epsRHSP α ρ ε Φs E g σ) r)
    (bound := fun r => ∫ θ in Set.Icc 0 (π / 2), G r θ)
    (x₀ := τ) (s := Set.Ioo 0 T) hs hF_meas hF_int hF'_meas h_bound hbd_int h_diff
  simpa only [Work.Construction.L12, Work.FM.L12] using hmain.2.hasDerivWithinAt

end Work.FTS.StrongEps.E5Aux3
