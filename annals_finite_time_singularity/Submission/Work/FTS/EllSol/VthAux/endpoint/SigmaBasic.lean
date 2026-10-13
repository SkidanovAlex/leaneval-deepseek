/-
Copyright: work module for the Elgindi finite-time singularity project.

Elementary facts about the angular weight `σ θ = sin (2θ) ^ (-η)` (with `η = 99/100`), used by
the weighted angular interpolation `Work.FTS.EllSol.VthAux.endpoint.nuWeightedInterp`:

* `σ ≥ 1` on the open interval `(0, π/2)`;
* `Iθ = [0, π/2]` agrees a.e. with the open interval, so the nonnegativity holds a.e.;
* consequently a nonnegative function dominated a.e. by `σ · g` is integrable on `Iθ` and has
  no larger integral (`sigma_mono`);
* Cauchy–Schwarz for interval integrals (`sq_integral_mul_le`), plus the elementary subset
  facts `uIcc`, `Ioc`, `Icc ⊆ (0, π/2)` for interior endpoints.
-/
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.cs_integral

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.VthAux.endpoint

set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem sin_two_pos_of_mem {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- The weight `sin (2θ) ^ (-η)` is `≥ 1` on the open interval. -/
theorem one_le_sigma {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    1 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
  have hs := sin_two_pos_of_mem hθ
  have hpow : (Real.sin (2 * θ)) ^ Work.Spaces.eta ≤ 1 := by
    have h1 : (Real.sin (2 * θ)) ^ Work.Spaces.eta ≤ (1 : ℝ) ^ Work.Spaces.eta :=
      Real.rpow_le_rpow hs.le (Real.sin_le_one _) Work.Spaces.eta_pos.le
    simpa using h1
  rw [Real.rpow_neg hs.le]
  exact (one_le_inv₀ (Real.rpow_pos_of_pos hs _)).mpr hpow

theorem restrict_Itheta :
    volume.restrict Work.Spaces.Iθ = volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  apply Measure.restrict_congr_set
  show Set.Icc (0 : ℝ) (Real.pi / 2) =ᵐ[volume] Set.Ioo (0 : ℝ) (Real.pi / 2)
  exact MeasureTheory.Ioo_ae_eq_Icc.symm

theorem ae_mem_Ioo_Itheta :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
  rw [restrict_Itheta]
  exact ae_restrict_mem isOpen_Ioo.measurableSet

/-- A nonnegative function dominated a.e. by `σ · g` is integrable on `Iθ` and has no larger
integral.  (Used with `g = f²` and `g = (f'')²`.) -/
theorem sigma_mono {g : ℝ → ℝ} (hg : ∀ θ, 0 ≤ g θ)
    (hmeas : AEStronglyMeasurable g (volume.restrict Work.Spaces.Iθ))
    (h : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * g θ) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn g Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, g θ)
        ≤ ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * g θ := by
  have hae : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      g θ ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * g θ := by
    filter_upwards [ae_mem_Ioo_Itheta] with θ hθ
    calc g θ = 1 * g θ := (one_mul _).symm
      _ ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * g θ :=
          mul_le_mul_of_nonneg_right (one_le_sigma hθ) (hg θ)
  have hgint : MeasureTheory.IntegrableOn g Work.Spaces.Iθ := by
    refine Integrable.mono' h hmeas ?_
    filter_upwards [hae] with θ hθ
    rw [Real.norm_of_nonneg (hg θ)]
    exact hθ
  exact ⟨hgint, integral_mono_ae hgint h hae⟩

/-- `σ` is nonnegative a.e. on `Iθ`. -/
theorem ae_sigma_nonneg :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
  filter_upwards [ae_mem_Ioo_Itheta] with θ hθ
  exact Real.rpow_nonneg (sin_two_pos_of_mem hθ).le _

/-- `(∫_a^b u v)² ≤ (∫_a^b u²) (∫_a^b v²)` for interval integrals (`a ≤ b`). -/
theorem sq_integral_mul_le {a b : ℝ} (hab : a ≤ b) {u v : ℝ → ℝ}
    (hu : AEStronglyMeasurable u (volume.restrict (Set.Ioc a b)))
    (hv : AEStronglyMeasurable v (volume.restrict (Set.Ioc a b)))
    (hu2 : MeasureTheory.IntegrableOn (fun x => (u x) ^ 2) (Set.Ioc a b))
    (hv2 : MeasureTheory.IntegrableOn (fun x => (v x) ^ 2) (Set.Ioc a b)) :
    (∫ x in a..b, u x * v x) ^ 2
      ≤ (∫ x in a..b, (u x) ^ 2) * (∫ x in a..b, (v x) ^ 2) := by
  have h := Work.Spaces.cs_integral
    ((MeasureTheory.memLp_two_iff_integrable_sq hu).mpr hu2)
    ((MeasureTheory.memLp_two_iff_integrable_sq hv).mpr hv2)
  rw [← intervalIntegral.integral_of_le hab, ← intervalIntegral.integral_of_le hab,
    ← intervalIntegral.integral_of_le hab] at h
  exact h

/-- `uIcc a b ⊆ (0, π/2)` whenever both endpoints are in `(0, π/2)`. -/
theorem uIcc_subset_Ioo {a b : ℝ} (ha : a ∈ Set.Ioo (0 : ℝ) (Real.pi / 2))
    (hb : b ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Set.uIcc a b ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
  intro x hx
  rw [Set.mem_uIcc] at hx
  rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨lt_of_lt_of_le ha.1 h1, lt_of_le_of_lt h2 hb.2⟩
  · exact ⟨lt_of_lt_of_le hb.1 h1, lt_of_le_of_lt h2 ha.2⟩

/-- `Ioc a b ⊆ (0, π/2)` whenever both endpoints are in `(0, π/2)`. -/
theorem Ioc_subset_Ioo {a b : ℝ} (ha : a ∈ Set.Ioo (0 : ℝ) (Real.pi / 2))
    (hb : b ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Set.Ioc a b ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
  intro x hx
  rw [Set.mem_Ioc] at hx
  exact ⟨lt_of_lt_of_le ha.1 hx.1.le, lt_of_le_of_lt hx.2 hb.2⟩

/-- `Icc a b ⊆ (0, π/2)` whenever both endpoints are in `(0, π/2)`. -/
theorem Icc_subset_Ioo {a b : ℝ} (ha : a ∈ Set.Ioo (0 : ℝ) (Real.pi / 2))
    (hb : b ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Set.Icc a b ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
  intro x hx
  rw [Set.mem_Icc] at hx
  exact ⟨lt_of_lt_of_le ha.1 hx.1, lt_of_le_of_lt hx.2 hb.2⟩

/-- `|∫_a^b g| ≤ √(b-a) √(∫_a^b g²)` for `a ≤ b` (Cauchy–Schwarz with the constant function
`1`). -/
theorem abs_integral_le_sqrt_mul_sqrt {a b : ℝ} (hab : a ≤ b) {g : ℝ → ℝ}
    (hcont : ContinuousOn g (Set.Icc a b))
    (hint : MeasureTheory.IntegrableOn (fun x => (g x) ^ 2) (Set.Icc a b)) :
    |∫ x in a..b, g x| ≤ Real.sqrt (b - a) * Real.sqrt (∫ x in a..b, (g x) ^ 2) := by
  have hcontIoc : ContinuousOn g (Set.Ioc a b) := hcont.mono Set.Ioc_subset_Icc_self
  have hii : MeasureTheory.IntegrableOn (fun x => (g x) ^ 2) (Set.Ioc a b) :=
    hint.mono_set Set.Ioc_subset_Icc_self
  have hone : MeasureTheory.IntegrableOn (fun x : ℝ => (1 : ℝ) ^ 2) (Set.Ioc a b) :=
    MeasureTheory.integrableOn_const (C := (1 : ℝ) ^ 2)
      (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have hcs := sq_integral_mul_le hab (hcontIoc.aestronglyMeasurable measurableSet_Ioc)
    aestronglyMeasurable_const hii hone
  have h1 : (∫ x in a..b, (1 : ℝ) ^ 2) = b - a := by
    rw [intervalIntegral.integral_const]
    norm_num
  rw [h1] at hcs
  have hcs' : (∫ x in a..b, g x) ^ 2 ≤ (∫ x in a..b, (g x) ^ 2) * (b - a) := by
    simpa using hcs
  calc |∫ x in a..b, g x| = Real.sqrt ((∫ x in a..b, g x) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt ((∫ x in a..b, (g x) ^ 2) * (b - a)) := Real.sqrt_le_sqrt hcs'
    _ = Real.sqrt (b - a) * Real.sqrt (∫ x in a..b, (g x) ^ 2) := by
        rw [Real.sqrt_mul (intervalIntegral.integral_nonneg hab (fun x _ => sq_nonneg _)), mul_comm]

end Work.FTS.EllSol.VthAux.endpoint
