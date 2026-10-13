/-
Copyright: work module for the Elgindi finite-time singularity project.

# Basic facts about the `L₁₂` density

`L₁₂(F)(z) = ∫_z^∞ ∫_0^{π/2} F(s,θ)K(θ)/s dθ ds` (`Work.Elliptic.L12`) is the iterated
tail integral of the angular density `L12dens F s = ∫_θ K(θ)F(s,θ)/s dθ`.  This file collects
the three analytic facts about the density that the elliptic estimates need:

* `L12dens g` is integrable on `(0,∞)` (from the `ℋ⁴`-membership of `g`: the weight
  `s/(1+s)² = 1/(s w s)` of the density is square-integrable and the angular integral is
  dominated by `√(∫_θ HkIntegrand α 4 g s θ)` through `1/(s w s) ≤ ...`);
* `∂_z L₁₂(g)(z) = -L12dens g z` for `z > 0`;
* `L12dens g` is continuous at every `z > 0`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.HardyZ
import Submission.Work.FM.Core2

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Elliptic

set_option autoImplicit false

/-! ## Elementary rewrites -/

/-- The angular moment `∫_θ K(θ)·g(s,θ) dθ` which is `s` times the density `L12dens g s`. -/
def angMoment (g : ℝ → ℝ → ℝ) (z : ℝ) : ℝ := ∫ θ in Work.Spaces.Iθ, Ktheta θ * g z θ

/-- `L12dens g s = angMoment g s / s`. -/
theorem L12dens_eq_angMoment_div (g : ℝ → ℝ → ℝ) (s : ℝ) :
    L12dens g s = angMoment g s / s := by
  rw [L12dens, angMoment, MeasureTheory.integral_div]

/-- The set integral over `Iθ = [0,π/2]` is the interval integral over `0..π/2`. -/
theorem integral_Iθ_eq_interval_aux (f : ℝ → ℝ) :
    (∫ θ in Work.Spaces.Iθ, f θ) = ∫ θ in (0 : ℝ)..(π/2), f θ := by
  rw [intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ π/2)]
  rw [Work.Spaces.Iθ, ← MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioc_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := π/2))]

/-- `Ktheta` is continuous. -/
theorem continuous_ktheta : Continuous Ktheta := by
  unfold Ktheta; fun_prop

/-- The `θ`-slice `θ ↦ g s θ` of a function smooth on a neighbourhood of the closed quadrant
is continuous on `Iθ`, for `s ∈ (-1,∞)`. -/
theorem continuousOn_slice_theta_Iθ (g : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd g)
    {s : ℝ} (hs : s ∈ Set.Ioi (-1)) :
    ContinuousOn (fun θ => g s θ) Work.Spaces.Iθ := by
  have hslice : ContDiffOn ℝ ⊤ (fun θ => g s θ) (Set.Ioo (-1) (π/2 + 1)) := by
    have h := hsm
    unfold Work.Spaces.SmoothNbhd at h
    have h2 : ContDiffOn ℝ ⊤ (fun θ : ℝ => (s, θ)) (Set.Ioo (-1) (π/2 + 1)) :=
      contDiffOn_const.prodMk contDiffOn_id
    have h3 := h.comp h2 (fun θ hθ => ⟨hs, hθ⟩)
    have hfun : (Function.uncurry g ∘ fun θ : ℝ => (s, θ)) = fun θ => g s θ := rfl
    rwa [hfun] at h3
  exact hslice.continuousOn.mono
    (fun θ hθ => ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩)

/-- A.e. statement for the restricted measure on `Iθ`: it suffices to prove the statement on
the open interval, where the angular weight `sin(2θ)` does not vanish. -/
theorem ae_restrict_Iθ_of_Ioo {p : ℝ → Prop} (h : ∀ θ, 0 < θ → θ < π/2 → p θ) :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), p θ := by
  rw [Work.Spaces.Iθ, ← MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := π/2))]
  exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
    (fun θ hθ => h θ hθ.1 hθ.2)

/-! ## Continuity of the density -/

/-- The density `L12dens g` is continuous at every `z > 0`. -/
theorem L12dens_continuousAt_aux (g : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd g)
    (z : ℝ) (hz : 0 < z) : ContinuousAt (L12dens g) z := by
  have hzn : z ∈ Set.Ioi (-1) := by simp only [Set.mem_Ioi]; linarith
  have hbox : Set.Icc (z/2) (z+1) ×ˢ Work.Spaces.Iθ
      ⊆ Set.Ioi (-1) ×ˢ Set.Ioo (-1) (π/2 + 1) := by
    rintro ⟨x, θ⟩ ⟨hx, hθ⟩
    exact ⟨by simp only [Set.mem_Ioi]; linarith [hx.1],
      ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩⟩
  have hcpt : IsCompact (Set.Icc (z/2) (z+1) ×ˢ Work.Spaces.Iθ) := isCompact_Icc.prod isCompact_Icc
  obtain ⟨M, hM⟩ := hcpt.exists_bound_of_continuousOn (hsm.continuousOn.mono hbox)
  have hs_nhds : Set.Ioo (z/2) (z+1) ∈ 𝓝 z := Ioo_mem_nhds (by linarith) (by linarith)
  have hA : ContinuousAt (fun x : ℝ => ∫ θ in Work.Spaces.Iθ, Ktheta θ * g x θ) z := by
    refine MeasureTheory.continuousAt_of_dominated (μ := volume.restrict Work.Spaces.Iθ)
      (F := fun x θ => Ktheta θ * g x θ) (bound := fun θ => M * |Ktheta θ|) ?_ ?_ ?_ ?_
    · filter_upwards [hs_nhds] with x hx
      exact (continuous_ktheta.continuousOn.mul
        (continuousOn_slice_theta_Iθ g hsm (by simp only [Set.mem_Ioi]; linarith [hx.1]))).aestronglyMeasurable
        measurableSet_Icc
    · filter_upwards [hs_nhds] with x hx
      filter_upwards [self_mem_ae_restrict measurableSet_Icc] with θ hθ
      have hbound : |g x θ| ≤ M := by
        have h := hM (x, θ) ⟨⟨le_of_lt hx.1, le_of_lt hx.2⟩, hθ⟩
        simpa only [Real.norm_eq_abs, Function.uncurry] using h
      rw [Real.norm_eq_abs, abs_mul]
      calc |Ktheta θ| * |g x θ| ≤ |Ktheta θ| * M :=
            mul_le_mul_of_nonneg_left hbound (abs_nonneg _)
        _ = M * |Ktheta θ| := by ring
    · exact (continuous_ktheta.abs.continuousOn.integrableOn_compact isCompact_Icc).const_mul M
    · filter_upwards [self_mem_ae_restrict measurableSet_Icc] with θ hθ
      exact (Work.Spaces.hardyZ_contDiffOn_slice g hsm hθ).continuousOn.continuousAt
        (isOpen_Ioi.mem_nhds hzn) |>.const_mul (Ktheta θ)
  refine (hA.div continuous_id.continuousAt (ne_of_gt hz)).congr ?_
  filter_upwards [isOpen_Ioi.mem_nhds hz] with x hx
  exact (L12dens_eq_angMoment_div g x).symm

/-- The density `L12dens g` is continuous on `(0,∞)`. -/
theorem L12dens_continuousOn_aux (g : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd g) :
    ContinuousOn (L12dens g) (Set.Ioi 0) :=
  fun z hz => (L12dens_continuousAt_aux g hsm z hz).continuousWithinAt

/-! ## The pointwise bound on the density -/

/-- The angular integral defining the density is dominated by the square root of the `ℋ⁴`
integrand, with the weight `s/(1+s)²`. -/
theorem L12dens_abs_le_aux (α : ℝ) (g : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd g)
    (hmem : Work.Spaces.HkMem α 4 g) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℝ, 0 < s →
      |L12dens g s| ≤ C * (s / (1 + s) ^ 2)
        * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ) := by
  refine ⟨Real.sqrt (∫ θ in Work.Spaces.Iθ, Ktheta θ ^ 2) + 1, by positivity, fun s hs => ?_⟩
  have hw_pos : 0 < Work.Spaces.w s := by rw [Work.Spaces.w]; positivity
  have hsin_cont : ContinuousOn (fun θ => g s θ) (Set.uIcc (0 : ℝ) (π/2)) := by
    rw [Set.uIcc_of_le (by positivity : (0 : ℝ) ≤ π/2)]
    exact continuousOn_slice_theta_Iθ g hsm (by simp only [Set.mem_Ioi]; linarith)
  -- pointwise domination of `g²` by the `ℋ⁴`-integrand
  have hpt : ∀ θ : ℝ, 0 < θ → θ < π/2 →
      (g s θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g s θ / (Work.Spaces.w s) ^ 2 := by
    intro θ hθ0 hθ1
    have hsin : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
    set S : ℝ := (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) with hSdef
    have hS : 0 < S := by rw [hSdef]; exact Real.rpow_pos_of_pos hsin _
    have hkey := Work.Spaces.sq_le_HkIntegrand_z α 4 g s θ 0 (by norm_num)
    simp only [Work.Spaces.DzIter_zero] at hkey
    have hrewrite : (g s θ) ^ 2
        = (g s θ * (Work.Spaces.w s / S)) ^ 2 * (S / Work.Spaces.w s) ^ 2 := by
      rw [mul_pow, div_pow, div_pow]
      field_simp
    have hSsq : S ^ 2 ≤ (1 : ℝ) := by
      have h2 : S ^ 2 = (Real.sin (2 * θ)) ^ Work.Spaces.eta := by
        rw [hSdef, ← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hsin)]
        norm_num
      calc S ^ 2 = (Real.sin (2 * θ)) ^ Work.Spaces.eta := h2
        _ ≤ 1 := Real.rpow_le_one (le_of_lt hsin) (Real.sin_le_one _)
            (le_of_lt Work.Spaces.eta_pos)
    have hSw : (S / Work.Spaces.w s) ^ 2 ≤ 1 / (Work.Spaces.w s) ^ 2 := by
      rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hSsq, pow_pos hw_pos 2]
    rw [hrewrite]
    refine le_trans (mul_le_mul_of_nonneg_right hkey (sq_nonneg _)) ?_
    refine le_trans (mul_le_mul_of_nonneg_left hSw
      (Work.Spaces.HkIntegrand_nonneg α 4 g s θ)) ?_
    rw [one_div, div_eq_mul_inv]
  have hg2_int : IntegrableOn (fun θ => (g s θ) ^ 2) Work.Spaces.Iθ :=
    ((continuousOn_slice_theta_Iθ g hsm (by simp only [Set.mem_Ioi]; linarith)).pow 2).integrableOn_compact
      isCompact_Icc
  have hk_int : IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 4 g s θ / (Work.Spaces.w s) ^ 2)
      Work.Spaces.Iθ := (hmem.1 s hs.le).div_const _
  have hg2_le : ∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2
      ≤ (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ) / (Work.Spaces.w s) ^ 2 := by
    refine le_trans (integral_mono_ae hg2_int hk_int (ae_restrict_Iθ_of_Ioo hpt)) ?_
    rw [MeasureTheory.integral_div]
  -- Cauchy–Schwarz in the angle
  have hCS : |angMoment g s| ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, Ktheta θ ^ 2)
      * Real.sqrt (∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2) := by
    have h := Work.Spaces.hardyZ_interval_integral_mul_le_sqrt 0 (π/2) (by positivity)
      (f := Ktheta) (g := fun θ => g s θ) continuous_ktheta.continuousOn hsin_cont
    simpa only [angMoment, ← integral_Iθ_eq_interval_aux (fun θ => Ktheta θ * g s θ),
      ← integral_Iθ_eq_interval_aux (fun θ => Ktheta θ ^ 2),
      ← integral_Iθ_eq_interval_aux (fun θ => (g s θ) ^ 2)] using h
  have hsqrt_le : Real.sqrt (∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2)
      ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ) / Work.Spaces.w s := by
    refine le_trans (Real.sqrt_le_sqrt hg2_le) ?_
    rw [Real.sqrt_div (integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 4 g s θ),
      Real.sqrt_sq_eq_abs, abs_of_pos hw_pos]
  have hmain : |L12dens g s| ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, Ktheta θ ^ 2)
      * ((s / (1 + s) ^ 2) * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ)) := by
    have hstep : |angMoment g s| / s ≤ (Real.sqrt (∫ θ in Work.Spaces.Iθ, Ktheta θ ^ 2)
        * (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ) / Work.Spaces.w s)) / s := by
      rw [div_le_div_iff_of_pos_right hs]
      exact le_trans hCS (mul_le_mul_of_nonneg_left hsqrt_le (Real.sqrt_nonneg _))
    calc |L12dens g s| = |angMoment g s| / s := by
          rw [L12dens_eq_angMoment_div, abs_div, abs_of_pos hs]
      _ ≤ _ := hstep
      _ = Real.sqrt (∫ θ in Work.Spaces.Iθ, Ktheta θ ^ 2)
            * ((s / (1 + s) ^ 2) * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ)) := by
          rw [Work.Spaces.w]
          field_simp
  refine le_trans hmain ?_
  have hX : 0 ≤ (s / (1 + s) ^ 2) * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ) :=
    mul_nonneg (by positivity) (Real.sqrt_nonneg _)
  calc Real.sqrt (∫ θ in Work.Spaces.Iθ, Ktheta θ ^ 2)
        * ((s / (1 + s) ^ 2) * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ))
      ≤ (Real.sqrt (∫ θ in Work.Spaces.Iθ, Ktheta θ ^ 2) + 1)
        * ((s / (1 + s) ^ 2) * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ)) :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hX
    _ = (Real.sqrt (∫ θ in Work.Spaces.Iθ, Ktheta θ ^ 2) + 1) * (s / (1 + s) ^ 2)
        * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ) := by ring

/-! ## Integrability of the weight `s²/(1+s)⁴` -/

/-- The square of the weight `ψ(s) = s/(1+s)²` is integrable on `(0,∞)`. -/
theorem psi_sq_integrable_aux :
    MeasureTheory.IntegrableOn (fun s : ℝ => (s / (1 + s) ^ 2) ^ 2) (Set.Ioi 0) := by
  have hcont : ContinuousOn (fun s : ℝ => (s / (1 + s) ^ 2) ^ 2) (Set.Ioi (-1)) := by
    refine ContinuousOn.pow (ContinuousOn.div continuousOn_id
      ((continuousOn_const.add continuousOn_id).pow 2) ?_) 2
    intro x hx
    have hx1 : (0:ℝ) < 1 + x := by
      simp only [Set.mem_Ioi] at hx
      linarith
    exact pow_ne_zero 2 (ne_of_gt hx1)
  have hcont1 : ContinuousOn (fun s : ℝ => (s / (1 + s) ^ 2) ^ 2) (Set.Icc (0:ℝ) 1) :=
    hcont.mono (fun x hx => by simp only [Set.mem_Ioi]; linarith [hx.1])
  have h1 : IntegrableOn (fun s : ℝ => (s / (1 + s) ^ 2) ^ 2) (Set.Ioc 0 1) :=
    (hcont1.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  have h2 : IntegrableOn (fun s : ℝ => (s / (1 + s) ^ 2) ^ 2) (Set.Ioi 1) := by
    have hbase : IntegrableOn (fun s : ℝ => s ^ (-(2:ℝ))) (Set.Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)
    refine Integrable.mono' hbase ?_ ?_
    · refine (hcont.mono ?_).aestronglyMeasurable measurableSet_Ioi
      intro x hx
      simp only [Set.mem_Ioi] at hx ⊢
      linarith
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
      have hs1 : 1 ≤ s := le_of_lt hs
      have hs0 : 0 < s := lt_trans zero_lt_one hs
      have hred : s ^ (-(2:ℝ)) = (s ^ 2)⁻¹ := by
        rw [Real.rpow_neg (le_of_lt hs0)]; simp
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), hred]
      have h4 : s ^ 4 ≤ (1 + s) ^ 4 := by nlinarith [hs1, sq_nonneg s]
      calc (s / (1 + s) ^ 2) ^ 2 = s ^ 2 / (1 + s) ^ 4 := by
            rw [div_pow, ← pow_mul]
        _ ≤ (s ^ 2)⁻¹ := by
            rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
            nlinarith [h4]
  rw [← Set.Ioc_union_Ioi_eq_Ioi (by norm_num : (0:ℝ) ≤ 1)]
  exact h1.union h2

/-! ## The main theorem -/

theorem L12densFacts (α : ℝ) (g : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd g)
    (hmem : Work.Spaces.HkMem α 4 g) :
    MeasureTheory.IntegrableOn (Work.Elliptic.L12dens g) (Set.Ioi 0)
      ∧ (∀ z : ℝ, 0 < z →
          HasDerivAt (fun z => Work.Elliptic.L12 g z) (-(Work.Elliptic.L12dens g z)) z)
      ∧ (∀ z : ℝ, 0 < z → ContinuousAt (Work.Elliptic.L12dens g) z) := by
  have hcontAt : ∀ z : ℝ, 0 < z → ContinuousAt (L12dens g) z :=
    fun z hz => L12dens_continuousAt_aux g hsm z hz
  have hcontOn : ContinuousOn (L12dens g) (Set.Ioi 0) := L12dens_continuousOn_aux g hsm
  obtain ⟨C, hCpos, hCbd⟩ := L12dens_abs_le_aux α g hsm hmem
  have hh_int : IntegrableOn
      (fun s => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ) (Set.Ioi 0) :=
    hmem.2.mono_set Set.Ioi_subset_Ici_self
  have hdom : IntegrableOn (fun s => (C/2) * ((s / (1 + s) ^ 2) ^ 2
      + ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ)) (Set.Ioi 0) :=
    (psi_sq_integrable_aux.add hh_int).const_mul (C/2)
  have hint : IntegrableOn (L12dens g) (Set.Ioi 0) := by
    refine hdom.mono' (hcontOn.aestronglyMeasurable measurableSet_Ioi) ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
    have h1 := hCbd s hs
    have hHnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ :=
      integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 4 g s θ
    have hAM : 2 * ((s / (1 + s) ^ 2)
        * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ))
        ≤ (s / (1 + s) ^ 2) ^ 2
          + ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ := by
      nlinarith [sq_nonneg ((s / (1 + s) ^ 2)
        - Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ)),
        Real.sq_sqrt hHnn]
    rw [Real.norm_eq_abs]
    calc |L12dens g s| ≤ C * (s / (1 + s) ^ 2)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ) := h1
      _ = (C/2) * (2 * ((s / (1 + s) ^ 2)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ))) := by ring
      _ ≤ (C/2) * ((s / (1 + s) ^ 2) ^ 2
          + ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ) :=
          mul_le_mul_of_nonneg_left hAM (by linarith)
  refine ⟨hint, fun z hz => ?_, hcontAt⟩
  exact Work.FM.hasDerivAt_L12 (K := Work.FM.Kpaper) (f := g) (a := 0) (ρ := z) hint
    (hcontAt z hz) hz

end Work.Elliptic
