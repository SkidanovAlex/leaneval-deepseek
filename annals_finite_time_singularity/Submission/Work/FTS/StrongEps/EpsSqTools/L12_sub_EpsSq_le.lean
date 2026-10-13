/-
Copyright: work module for the Elgindi finite-time singularity project.

# `|L₁₂ f z - L₁₂ g z| ≤ C √(EpsSq α (f - g))` on the whole half-line `z ∈ Iz`

The `ε`-scheme's space `X` (`Work.FTS.StrongEps.EpsSq`, `EpsMem`) carries the angular weight
`epsW α z θ = w z / sin(2θ)^{γ/2}` with `γ = 1 + α/10 ≥ 1`, which is *stronger* at the endpoints
`θ = 0, π/2` than the `η`-weight of `HkIntegrand`.  This is exactly what makes the Cauchy–Schwarz
bound for the model operator `L₁₂` **uniform in `z`** (the `HkSq`-version `L12AbsLe` only gives
`|L₁₂ h z| ≤ C √(HkSq)/√z`, which explodes at `z = 0`).

## The estimate

With `K(θ) = 3 sin θ cos²θ`, `Wlam s = s/(1+s)² = 1/(s·w s)` and `Swe α θ = sin(2θ)^{γ/2}`,

  `K θ · h s θ / s = Wlam s · (K θ · Swe α θ · (h s θ · epsW α s θ))`

(both sides vanish at `θ = 0, π/2`, where `K` and `Swe` do; the identity is `K_mul_h_div_s_eq_eps`).
Cauchy–Schwarz in `θ` against the angular profile `K·Swe` gives

  `|L₁₂dens h s| ≤ Wlam s · BKe α · √(∫_θ (h s θ · epsW α s θ)²)`,

and Cauchy–Schwarz in `s` — with the *uniform* weight bound `∫_{s>z} Wlam² ≤ W2e = ∫_{(0,∞)} Wlam²`
for every `z ≥ 0` — gives, with `G s = ∫_θ (h s θ epsW α s θ)²` and `EpsSq α h = ∫_{Iz} G`,

  `|L₁₂ h z| ≤ BKe α · √W2e · √(EpsSq α h)`,   `BKe α = √(∫_θ (K θ · Swe α θ)²) ≤ 5`.

The constant `5√W2e + 1` (with `W2e = ∫_{(0,∞)} (s/(1+s)²)²` finite) is α-free and `z`-free.

The only analytic input on the datum `h` is the level-`0` integrability `EpsMem α h`: no
smoothness and no a.e. measurability of the slices is required — the Cauchy–Schwarz steps are
arranged so that the only measurable functions are the continuous weight `Wlam`, the continuous
angular profile `K·Swe`, and the square root `√(∫_θ (h epsW)²)` of the marginal (measurable
because the marginal is integrable).  Where the Bochner integral is the junk value `0`, the
estimate holds trivially.

The main theorem of the file, `L12_sub_EpsSq_le`, then follows from the additivity
`L12_sub_HkMem` (which turns `L₁₂ f - L₁₂ g` into `L₁₂ (f - g)`) applied to the helper
`L12_le_sqrt_EpsSq`.
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.NormNum.RealSqrt
import Submission.Work.FTS.StrongEps.EpsSq_Jeps_le
import Submission.Work.FTS.StrongEps.EComparison.L12_sub_HkMem
import Submission.Work.Elliptic.L12densFacts
import Submission.Work.FTS.GalBasis.cc.Defs
import Submission.Work.FTS.EllipticEst.remov.Ebs.abs_integral_mul_le_sqrt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory

namespace Work.FTS.StrongEps.EpsSqTools

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The angular factor `sin(2θ)^{γ/2}` of the `ε`-weight -/

/-- `Swe α θ = sin(2θ)^{γ/2}` with `γ = gam α`: the angular factor of `epsW α z θ = w z / Swe α θ`. -/
def Swe (α θ : ℝ) : ℝ := Real.sin (2 * θ) ^ (Work.Spaces.gam α / 2)

/-- `BKe α = √(∫_θ (K(θ)·Swe α θ)² dθ)`: the angular `L²`-norm of the profile `K·Swe`. -/
def BKe (α : ℝ) : ℝ :=
  Real.sqrt (∫ θ in Work.Spaces.Iθ, (Work.Spaces.K θ * Swe α θ) ^ 2)

/-- `W2e = ∫_{(0,∞)} Wlam²`: the finite `L²`-mass of the radial weight `Wlam s = s/(1+s)²`. -/
def W2e : ℝ := ∫ s in Set.Ioi (0 : ℝ), Work.FTS.GalBasis.cc.Wlam s ^ 2

lemma Swe_nonneg_of_mem_Iθ {α θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Swe α θ := by
  rw [Swe]
  exact Real.rpow_nonneg (Work.FTS.GalBasis.cc.sin_two_nonneg_of_mem_Iθ hθ) _

lemma Swe_pos_of_mem_Ioo {α θ : ℝ} (hα : 0 < Work.Spaces.gam α / 2)
    (hθ0 : 0 < θ) (hθ1 : θ < π / 2) : 0 < Swe α θ := by
  rw [Swe]
  exact Real.rpow_pos_of_pos
    (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])) _

lemma Swe_le_one {α θ : ℝ} (hα : 0 ≤ Work.Spaces.gam α / 2) (hθ : θ ∈ Work.Spaces.Iθ) :
    Swe α θ ≤ 1 := by
  rw [Swe]
  exact Real.rpow_le_one (Work.FTS.GalBasis.cc.sin_two_nonneg_of_mem_Iθ hθ) (Real.sin_le_one _) hα

lemma continuous_Swe {α : ℝ} (hα : 0 ≤ Work.Spaces.gam α / 2) : Continuous (Swe α) := by
  change Continuous (fun θ : ℝ => Real.sin (2 * θ) ^ (Work.Spaces.gam α / 2))
  exact (Real.continuous_rpow_const hα).comp
    (Real.continuous_sin.comp (continuous_const.mul continuous_id))

lemma continuous_K : Continuous Work.Spaces.K := by
  change Continuous fun θ : ℝ => 3 * Real.sin θ * Real.cos θ ^ 2
  fun_prop

/-- Where `Swe` vanishes on `Iθ`, so does `K`. -/
lemma Swe_eq_zero_imp_K_eq_zero {α θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) (h : Swe α θ = 0) :
    Work.Spaces.K θ = 0 := by
  rw [Swe] at h
  have hsin := Work.FTS.GalBasis.cc.sin_two_nonneg_of_mem_Iθ hθ
  have hzero : Real.sin (2 * θ) = 0 := ((Real.rpow_eq_zero_iff_of_nonneg hsin).mp h).1
  rw [Real.sin_two_mul] at hzero
  have : Real.sin θ = 0 ∨ Real.cos θ = 0 := by
    rcases mul_eq_zero.mp hzero with h' | h'
    · exact Or.inl (by linarith [h'])
    · exact Or.inr h'
  rw [Work.Spaces.K]
  rcases this with h' | h' <;> simp [h']

/-! ## The pointwise factorisation of the `L₁₂`-density integrand -/

/-- For `s > 0` and `θ ∈ Iθ` the density integrand factorises as the radial weight `Wlam s`
times the pairing of the angular profile `K·Swe` with the `ε`-weighted datum `h·epsW`. -/
lemma K_mul_h_div_s_eq_eps (α : ℝ) (h : ℝ → ℝ → ℝ) {s : ℝ} (hs : 0 < s) :
    ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.K θ * h s θ / s
        = Work.FTS.GalBasis.cc.Wlam s
            * (Work.Spaces.K θ * Swe α θ * (h s θ * epsW α s θ)) := by
  intro θ hθ
  by_cases hS : Swe α θ = 0
  · have hK : Work.Spaces.K θ = 0 := Swe_eq_zero_imp_K_eq_zero hθ hS
    rw [hS, hK]
    simp
  · have hstep : Swe α θ * (h s θ * epsW α s θ) = h s θ * Work.Spaces.w s := by
      have he : epsW α s θ = Work.Spaces.w s / Swe α θ := rfl
      rw [he]
      rw [show Swe α θ * (h s θ * (Work.Spaces.w s / Swe α θ))
            = h s θ * (Swe α θ * (Work.Spaces.w s / Swe α θ)) from by ring]
      rw [mul_div_cancel₀ _ hS]
    exact (calc Work.FTS.GalBasis.cc.Wlam s * (Work.Spaces.K θ * Swe α θ * (h s θ * epsW α s θ))
        = Work.Spaces.K θ
            * (Work.FTS.GalBasis.cc.Wlam s * (Swe α θ * (h s θ * epsW α s θ))) := by ring
      _ = Work.Spaces.K θ
            * (Work.FTS.GalBasis.cc.Wlam s * (h s θ * Work.Spaces.w s)) := by rw [hstep]
      _ = Work.Spaces.K θ
            * (h s θ * (Work.Spaces.w s * Work.FTS.GalBasis.cc.Wlam s)) := by ring
      _ = Work.Spaces.K θ * (h s θ * (1 / s)) := by
            rw [Work.FTS.GalBasis.cc.w_mul_Wlam hs]
      _ = Work.Spaces.K θ * h s θ / s := by ring).symm

/-! ## The angular Cauchy–Schwarz step -/

lemma BKe_nonneg (α : ℝ) : 0 ≤ BKe α := Real.sqrt_nonneg _

/-- **Angular Cauchy–Schwarz against the `ε`-weighted datum.**  If the `θ`-slice of the
`ε`-integrand is integrable, then the pairing `∫_θ K θ · Swe α θ · (h s θ · epsW α s θ)` is
dominated by the product of the angular profile norm `BKe α` and the square root of the slice
energy. -/
theorem abs_integral_K_Swe_eps_le {α : ℝ} (hα : 0 ≤ Work.Spaces.gam α / 2)
    (h : ℝ → ℝ → ℝ) {s : ℝ}
    (hint : IntegrableOn (fun θ => (h s θ * epsW α s θ) ^ 2) Work.Spaces.Iθ) :
    |∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Swe α θ * (h s θ * epsW α s θ)|
      ≤ BKe α * Real.sqrt (∫ θ in Work.Spaces.Iθ, (h s θ * epsW α s θ) ^ 2) := by
  set u : ℝ → ℝ := fun θ => Work.Spaces.K θ * Swe α θ with hu
  set v : ℝ → ℝ := fun θ => h s θ * epsW α s θ with hv
  set w : ℝ → ℝ := fun θ => Real.sqrt ((h s θ * epsW α s θ) ^ 2) with hw
  have hIθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hw_nn : ∀ θ : ℝ, 0 ≤ w θ := fun θ => Real.sqrt_nonneg _
  have hvw : ∀ θ : ℝ, |v θ| ≤ w θ := by
    intro θ
    show |h s θ * epsW α s θ| ≤ Real.sqrt ((h s θ * epsW α s θ) ^ 2)
    rw [Real.sqrt_sq_eq_abs]
  have hcont_u : Continuous u := by
    rw [hu]
    exact continuous_K.mul (continuous_Swe hα)
  have hw_aesm : AEStronglyMeasurable w (volume.restrict Work.Spaces.Iθ) := by
    rw [hw]
    exact (hint.aestronglyMeasurable.aemeasurable.sqrt).aestronglyMeasurable
  have hu2_int : IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ :=
    (hcont_u.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hw2_int : IntegrableOn (fun θ => (w θ) ^ 2) Work.Spaces.Iθ := by
    refine hint.congr_fun (fun θ _ => ?_) hIθ
    rw [hw]
    exact (Real.sq_sqrt (sq_nonneg _)).symm
  have huw_int : IntegrableOn (fun θ => |u θ| * w θ) Work.Spaces.Iθ := by
    have hmaj : IntegrableOn (fun θ => ((u θ) ^ 2 + (w θ) ^ 2) / 2) Work.Spaces.Iθ :=
      (hu2_int.add hw2_int).div_const 2
    refine hmaj.mono' ((hcont_u.abs.aestronglyMeasurable).mul hw_aesm) ?_
    filter_upwards with θ
    have h1 : 0 ≤ |u θ| := abs_nonneg _
    have h2 : 0 ≤ w θ := hw_nn θ
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h2, abs_of_nonneg h1]
    have key : |u θ| * w θ ≤ (|u θ| ^ 2 + (w θ) ^ 2) / 2 := by
      nlinarith [sq_nonneg (|u θ| - w θ), sq_nonneg (|u θ| + w θ)]
    rw [sq_abs (u θ)] at key
    exact key
  have hMemLp_u : MemLp (fun θ => |u θ|) 2 (volume.restrict Work.Spaces.Iθ) :=
    (memLp_two_iff_integrable_sq (μ := volume.restrict Work.Spaces.Iθ)
      (f := fun θ => |u θ|) hcont_u.abs.aestronglyMeasurable).mpr
      (hu2_int.congr (Filter.Eventually.of_forall fun θ => (sq_abs (u θ)).symm))
  have hMemLp_w : MemLp w 2 (volume.restrict Work.Spaces.Iθ) :=
    (memLp_two_iff_integrable_sq (μ := volume.restrict Work.Spaces.Iθ) hw_aesm).mpr hw2_int
  have hcs := Work.FTS.EllipticEst.remov.Ebs.abs_integral_mul_le_sqrt (u := fun θ => |u θ|)
    (v := w) hMemLp_u hMemLp_w
  have hsqrt_u : Real.sqrt (∫ θ in Work.Spaces.Iθ, |u θ| ^ 2) = BKe α := by
    rw [BKe]
    congr 1
    rw [hu]
    exact integral_congr_ae (Filter.Eventually.of_forall fun θ => sq_abs (Work.Spaces.K θ * Swe α θ))
  have hsqrt_w : Real.sqrt (∫ θ in Work.Spaces.Iθ, (w θ) ^ 2)
      = Real.sqrt (∫ θ in Work.Spaces.Iθ, (h s θ * epsW α s θ) ^ 2) := by
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    rw [hw]
    exact Real.sq_sqrt (sq_nonneg _)
  have h1 : |∫ θ in Work.Spaces.Iθ, u θ * v θ|
      ≤ ∫ θ in Work.Spaces.Iθ, |u θ * v θ| := by
    simpa only [Real.norm_eq_abs] using
      (MeasureTheory.norm_integral_le_integral_norm (μ := volume.restrict Work.Spaces.Iθ)
        (f := fun θ => u θ * v θ))
  have h2 : ∫ θ in Work.Spaces.Iθ, |u θ * v θ| ≤ ∫ θ in Work.Spaces.Iθ, |u θ| * w θ := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun θ => abs_nonneg _) huw_int
      (Filter.Eventually.of_forall fun θ => ?_)
    show |u θ * v θ| ≤ |u θ| * w θ
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hvw θ) (abs_nonneg _)
  have h3 : ∫ θ in Work.Spaces.Iθ, |u θ| * w θ
      = |∫ θ in Work.Spaces.Iθ, |u θ| * w θ| := by
    rw [abs_of_nonneg]
    exact integral_nonneg fun θ => mul_nonneg (abs_nonneg _) (hw_nn θ)
  calc |∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Swe α θ * (h s θ * epsW α s θ)|
      = |∫ θ in Work.Spaces.Iθ, u θ * v θ| := by simp only [hu, hv]
    _ ≤ ∫ θ in Work.Spaces.Iθ, |u θ * v θ| := h1
    _ ≤ ∫ θ in Work.Spaces.Iθ, |u θ| * w θ := h2
    _ = |∫ θ in Work.Spaces.Iθ, |u θ| * w θ| := h3
    _ ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, |u θ| ^ 2)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, (w θ) ^ 2) := hcs
    _ = BKe α * Real.sqrt (∫ θ in Work.Spaces.Iθ, (h s θ * epsW α s θ) ^ 2) := by
        rw [hsqrt_u, hsqrt_w]

/-- **The `z`- and `α`-free bound `BKe α ≤ 5`** for `α ∈ (0,1]`: on `Iθ` one has `K ≤ 3` and
`Swe ≤ 1`, so the integrand is at most `9` and the angular interval has measure `π/2 < 2`. -/
lemma BKe_le_five {α : ℝ} (hα : α ∈ Set.Ioc 0 1) : BKe α ≤ 5 := by
  have hgam : 0 ≤ Work.Spaces.gam α / 2 := by rw [Work.Spaces.gam]; linarith [hα.1]
  have hbd : ∀ θ ∈ Work.Spaces.Iθ, (Work.Spaces.K θ * Swe α θ) ^ 2 ≤ 9 := by
    intro θ hθ
    have hK := Work.FTS.GalBasis.cc.K_le_three_of_mem_Iθ hθ
    have hK0 := Work.FTS.GalBasis.cc.K_nonneg_of_mem_Iθ hθ
    have hSw := Swe_le_one hgam hθ
    have hSw0 := Swe_nonneg_of_mem_Iθ (α := α) hθ
    have hspan : 0 ≤ Work.Spaces.K θ * Swe α θ := mul_nonneg hK0 hSw0
    have hprod : Work.Spaces.K θ * Swe α θ ≤ 3 := by
      nlinarith [mul_le_mul hK hSw hSw0 (by norm_num : (0 : ℝ) ≤ 3)]
    have hsq := mul_self_le_mul_self hspan hprod
    nlinarith [hsq]
  have h9int : IntegrableOn (fun _ : ℝ => (9 : ℝ)) Work.Spaces.Iθ :=
    integrableOn_const (by rw [Work.Spaces.Iθ, Real.volume_Icc]; simp)
  have hle : ∫ θ in Work.Spaces.Iθ, (Work.Spaces.K θ * Swe α θ) ^ 2
      ≤ ∫ θ in Work.Spaces.Iθ, (9 : ℝ) :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => sq_nonneg _) h9int
      (ae_restrict_of_forall_mem (by simp [Work.Spaces.Iθ]) (fun θ hθ => hbd θ hθ))
  have h9 : ∫ θ in Work.Spaces.Iθ, (9 : ℝ) = 9 * (π / 2) := by
    rw [MeasureTheory.setIntegral_const, MeasureTheory.measureReal_def, Work.Spaces.Iθ,
      Real.volume_Icc, ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
    ring
  have hfin : ∫ θ in Work.Spaces.Iθ, (Work.Spaces.K θ * Swe α θ) ^ 2 ≤ 25 := by
    rw [h9] at hle
    nlinarith [Real.pi_lt_four]
  rw [BKe]
  calc Real.sqrt (∫ θ in Work.Spaces.Iθ, (Work.Spaces.K θ * Swe α θ) ^ 2)
      ≤ Real.sqrt 25 := Real.sqrt_le_sqrt hfin
    _ = 5 := by norm_num

/-! ## The pointwise bound on the density -/

/-- **The `L₁₂`-density bound in the `ε`-weight.**  If the `θ`-slice of the `ε`-integrand is
integrable, then for `s > 0`

`|L₁₂dens h s| ≤ BKe α · Wlam s · √(∫_θ (h s θ · epsW α s θ)²)`. -/
theorem abs_L12dens_le_eps {α : ℝ} (hα : 0 ≤ Work.Spaces.gam α / 2)
    (h : ℝ → ℝ → ℝ) {s : ℝ} (hs : 0 < s)
    (hint : IntegrableOn (fun θ => (h s θ * epsW α s θ) ^ 2) Work.Spaces.Iθ) :
    |Work.Construction.L12dens h s|
      ≤ BKe α * (Work.FTS.GalBasis.cc.Wlam s
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, (h s θ * epsW α s θ) ^ 2)) := by
  have hId : Work.Construction.L12dens h s
      = ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * h s θ / s := rfl
  have hcongr : (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * h s θ / s)
      = ∫ θ in Work.Spaces.Iθ, Work.FTS.GalBasis.cc.Wlam s
          * (Work.Spaces.K θ * Swe α θ * (h s θ * epsW α s θ)) :=
    MeasureTheory.setIntegral_congr_fun (by simp [Work.Spaces.Iθ])
      (fun θ hθ => K_mul_h_div_s_eq_eps α h hs θ hθ)
  rw [hId, hcongr, integral_const_mul, abs_mul,
    abs_of_nonneg (Work.FTS.GalBasis.cc.Wlam_nonneg hs.le)]
  calc Work.FTS.GalBasis.cc.Wlam s
        * |∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Swe α θ * (h s θ * epsW α s θ)|
      ≤ Work.FTS.GalBasis.cc.Wlam s
          * (BKe α * Real.sqrt (∫ θ in Work.Spaces.Iθ, (h s θ * epsW α s θ) ^ 2)) :=
        mul_le_mul_of_nonneg_left (abs_integral_K_Swe_eps_le hα h hint)
          (Work.FTS.GalBasis.cc.Wlam_nonneg hs.le)
    _ = BKe α * (Work.FTS.GalBasis.cc.Wlam s
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, (h s θ * epsW α s θ) ^ 2)) := by ring

/-! ## The radial Cauchy–Schwarz data -/

/-- The radial weight `Wlam` is square-integrable on `(0,∞)` (it equals `s/(1+s)²`). -/
lemma Wlam_sq_integrableOn_Ioi0 :
    IntegrableOn (fun s : ℝ => Work.FTS.GalBasis.cc.Wlam s ^ 2) (Set.Ioi (0 : ℝ)) := by
  simpa only [Work.FTS.GalBasis.cc.Wlam] using Work.Elliptic.psi_sq_integrable_aux

lemma Wlam_aesm_restrict {z : ℝ} (hz : 0 ≤ z) :
    AEStronglyMeasurable Work.FTS.GalBasis.cc.Wlam (volume.restrict (Set.Ioi z)) := by
  have h0 : AEStronglyMeasurable Work.FTS.GalBasis.cc.Wlam
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
    change AEStronglyMeasurable (fun s : ℝ => s / (1 + s) ^ 2) (volume.restrict (Set.Ioi 0))
    refine ContinuousOn.aestronglyMeasurable (μ := volume)
      (continuousOn_id.div ((continuousOn_const.add continuousOn_id).pow 2) ?_) measurableSet_Ioi
    intro s hs
    have hne : (1 : ℝ) + s ≠ 0 := by
      simp only [Set.mem_Ioi] at hs
      linarith
    exact pow_ne_zero 2 hne
  exact h0.mono_measure (MeasureTheory.Measure.restrict_mono_set volume (fun x hx => by
    simp only [Set.mem_Ioi] at hx ⊢
    linarith))

/-! ## The main estimate for a single datum -/

/-- **`|L₁₂ h z| ≤ C √(EpsSq α h)` uniformly in `α ∈ (0,1]` and `z ∈ [0,∞)`**, from the sole
hypothesis `EpsMem α h` (level-`0` `ε`-integrability of `h`). -/
theorem L12_le_sqrt_EpsSq : ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, α ∈ Set.Ioc 0 1 →
    ∀ h : Work.FTS.Galerkin.Fn, EpsMem α h → ∀ z ∈ Work.Spaces.Iz,
      |Work.Construction.L12 h z| ≤ C * Real.sqrt (EpsSq α h) := by
  refine ⟨5 * Real.sqrt W2e + 1, by have := Real.sqrt_nonneg W2e; linarith, ?_⟩
  intro α hα h hmem z hz
  have hz0 : (0 : ℝ) ≤ z := hz
  have hgam : 0 ≤ Work.Spaces.gam α / 2 := by rw [Work.Spaces.gam]; linarith [hα.1]
  -- the angular marginal of the `ε`-integrand, its square root, and the radial data
  set F : ℝ → ℝ := fun s => ∫ θ in Work.Spaces.Iθ, (h s θ * epsW α s θ) ^ 2 with hF
  set A : ℝ → ℝ := fun s => Real.sqrt (F s) with hA
  have hFnn : ∀ s : ℝ, 0 ≤ F s := fun s => integral_nonneg fun θ => sq_nonneg _
  have hAnn : ∀ s : ℝ, 0 ≤ A s := fun s => Real.sqrt_nonneg _
  have hA2 : ∀ s : ℝ, A s ^ 2 = F s := fun s => Real.sq_sqrt (hFnn s)
  have hFdef : ∀ s : ℝ, F s = ∫ θ in Work.Spaces.Iθ, (h s θ * epsW α s θ) ^ 2 := fun _ => rfl
  -- Fubini: the marginal `F` is integrable on `Iz`, and its slices are a.e. integrable
  have hsub : Set.Ioi z ⊆ Work.Spaces.Iz := by
    intro x hx
    simp only [Set.mem_Ioi] at hx
    simp only [Work.Spaces.Iz, Set.mem_Ici]
    linarith
  have hEprod_Iz : Integrable (fun p : ℝ × ℝ => (h p.1 p.2 * epsW α p.1 p.2) ^ 2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
    rw [MeasureTheory.Measure.prod_restrict]
    exact hmem
  have hFint_Iz : IntegrableOn F Work.Spaces.Iz := hEprod_Iz.integral_prod_left
  have hEprod : Integrable (fun p : ℝ × ℝ => (h p.1 p.2 * epsW α p.1 p.2) ^ 2)
      ((volume.restrict (Set.Ioi z)).prod (volume.restrict Work.Spaces.Iθ)) := by
    rw [MeasureTheory.Measure.prod_restrict]
    exact hmem.mono_set (Set.prod_mono hsub subset_rfl)
  have hFint : IntegrableOn F (Set.Ioi z) := hEprod.integral_prod_left
  have hslice : ∀ᵐ s ∂(volume.restrict (Set.Ioi z)),
      IntegrableOn (fun θ => (h s θ * epsW α s θ) ^ 2) Work.Spaces.Iθ := hEprod.prod_right_ae
  have hEpsSq : EpsSq α h = ∫ s in Work.Spaces.Iz, F s := by
    rw [hF]
    rfl
  -- `A² = F` is integrable on `(z,∞)`, and `A` is `L²` there
  have hA2int : IntegrableOn (fun s => A s ^ 2) (Set.Ioi z) :=
    hFint.congr_fun (fun s _ => (hA2 s).symm) measurableSet_Ioi
  have hA_aesm : AEStronglyMeasurable A (volume.restrict (Set.Ioi z)) := by
    rw [hA]
    exact (hFint.aestronglyMeasurable.aemeasurable.sqrt).aestronglyMeasurable
  have hA_memLp : MemLp A 2 (volume.restrict (Set.Ioi z)) :=
    (memLp_two_iff_integrable_sq hA_aesm).mpr hA2int
  -- the radial weight `Wlam` is `L²((z,∞))`
  have hsub0 : Set.Ioi z ⊆ Set.Ioi (0 : ℝ) := fun x hx => by
    simp only [Set.mem_Ioi] at hx ⊢
    linarith
  have hWlam_sq_int : IntegrableOn (fun s => Work.FTS.GalBasis.cc.Wlam s ^ 2) (Set.Ioi z) :=
    Wlam_sq_integrableOn_Ioi0.mono_set hsub0
  have hWlam_sq_le : ∫ s in Set.Ioi z, Work.FTS.GalBasis.cc.Wlam s ^ 2 ≤ W2e :=
    MeasureTheory.setIntegral_mono_set Wlam_sq_integrableOn_Ioi0
      (Filter.Eventually.of_forall fun x => sq_nonneg _)
      (Filter.Eventually.of_forall fun x hx => hsub0 hx)
  have hWlam_memLp : MemLp Work.FTS.GalBasis.cc.Wlam 2 (volume.restrict (Set.Ioi z)) :=
    (memLp_two_iff_integrable_sq (Wlam_aesm_restrict hz0)).mpr hWlam_sq_int
  -- radial Cauchy–Schwarz
  have hFle : ∫ s in Set.Ioi z, F s ≤ EpsSq α h := by
    rw [hEpsSq]
    exact MeasureTheory.setIntegral_mono_set hFint_Iz
      (Filter.Eventually.of_forall fun x => hFnn x)
      (Filter.Eventually.of_forall fun x hx => by
        simp only [Set.mem_Ioi] at hx
        simp only [Work.Spaces.Iz, Set.mem_Ici]
        linarith)
  have hCS : ∫ s in Set.Ioi z, Work.FTS.GalBasis.cc.Wlam s * A s
      ≤ Real.sqrt W2e * Real.sqrt (EpsSq α h) := by
    have hcs := Work.FTS.EllipticEst.remov.Ebs.abs_integral_mul_le_sqrt
      (u := Work.FTS.GalBasis.cc.Wlam) (v := A) (s := Set.Ioi z) hWlam_memLp hA_memLp
    have hA2eq : (∫ s in Set.Ioi z, A s ^ 2) = ∫ s in Set.Ioi z, F s :=
      MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun s _ => hA2 s)
    have hnn : 0 ≤ ∫ s in Set.Ioi z, Work.FTS.GalBasis.cc.Wlam s * A s := by
      refine MeasureTheory.integral_nonneg_of_ae ?_
      filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with s hs
      have hzs : z < s := Set.mem_Ioi.mp hs
      exact mul_nonneg
        (Work.FTS.GalBasis.cc.Wlam_nonneg (le_of_lt (lt_of_le_of_lt hz0 hzs))) (hAnn s)
    have hWle : Real.sqrt (∫ s in Set.Ioi z, Work.FTS.GalBasis.cc.Wlam s ^ 2)
        ≤ Real.sqrt W2e := Real.sqrt_le_sqrt hWlam_sq_le
    have hAle : Real.sqrt (∫ s in Set.Ioi z, A s ^ 2) ≤ Real.sqrt (EpsSq α h) := by
      rw [hA2eq]
      exact Real.sqrt_le_sqrt hFle
    calc ∫ s in Set.Ioi z, Work.FTS.GalBasis.cc.Wlam s * A s
        = |∫ s in Set.Ioi z, Work.FTS.GalBasis.cc.Wlam s * A s| := (abs_of_nonneg hnn).symm
      _ ≤ Real.sqrt (∫ s in Set.Ioi z, Work.FTS.GalBasis.cc.Wlam s ^ 2)
            * Real.sqrt (∫ s in Set.Ioi z, A s ^ 2) := hcs
      _ ≤ Real.sqrt W2e * Real.sqrt (EpsSq α h) :=
          mul_le_mul hWle hAle (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  -- the a.e. density bound and the integrability of the majorant
  have hbd : ∀ᵐ s ∂(volume.restrict (Set.Ioi z)), |Work.Construction.L12dens h s|
      ≤ BKe α * (Work.FTS.GalBasis.cc.Wlam s * A s) := by
    filter_upwards [hslice, MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with s hsl hs
    have hzs : z < s := Set.mem_Ioi.mp hs
    have h := abs_L12dens_le_eps hgam h (by linarith) hsl
    simpa only [hA, hFdef] using h
  have hAMGM : ∀ s ∈ Set.Ioi z,
      Work.FTS.GalBasis.cc.Wlam s * A s ≤ Work.FTS.GalBasis.cc.Wlam s ^ 2 + A s ^ 2 :=
    fun s _ => by nlinarith [sq_nonneg (Work.FTS.GalBasis.cc.Wlam s - A s)]
  have hsum_int : IntegrableOn
      (fun s => Work.FTS.GalBasis.cc.Wlam s ^ 2 + A s ^ 2) (Set.Ioi z) :=
    hWlam_sq_int.add hA2int
  have hmax_int : IntegrableOn
      (fun s => BKe α * (Work.FTS.GalBasis.cc.Wlam s * A s)) (Set.Ioi z) := by
    refine MeasureTheory.Integrable.mono' (hsum_int.const_mul (BKe α))
      (((Wlam_aesm_restrict hz0).mul hA_aesm).const_mul (BKe α)) ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with s hs
    have hzs : z < s := Set.mem_Ioi.mp hs
    have hnn : 0 ≤ BKe α * (Work.FTS.GalBasis.cc.Wlam s * A s) :=
      mul_nonneg (BKe_nonneg α)
        (mul_nonneg (Work.FTS.GalBasis.cc.Wlam_nonneg (le_of_lt (lt_of_le_of_lt hz0 hzs)))
          (hAnn s))
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    exact mul_le_mul_of_nonneg_left (hAMGM s hs) (BKe_nonneg α)
  -- assembly
  have h1 : |Work.Construction.L12 h z|
      ≤ ∫ s in Set.Ioi z, |Work.Construction.L12dens h s| := by
    have hL : Work.Construction.L12 h z
        = ∫ s in Set.Ioi z, Work.Construction.L12dens h s := rfl
    rw [hL]
    simpa only [Real.norm_eq_abs] using
      (MeasureTheory.norm_integral_le_integral_norm (μ := volume.restrict (Set.Ioi z))
        (f := fun s => Work.Construction.L12dens h s))
  have h2 : ∫ s in Set.Ioi z, |Work.Construction.L12dens h s|
      ≤ ∫ s in Set.Ioi z, BKe α * (Work.FTS.GalBasis.cc.Wlam s * A s) :=
    MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun s => abs_nonneg _) hmax_int hbd
  have h3 : ∫ s in Set.Ioi z, BKe α * (Work.FTS.GalBasis.cc.Wlam s * A s)
      = BKe α * ∫ s in Set.Ioi z, Work.FTS.GalBasis.cc.Wlam s * A s :=
    MeasureTheory.integral_const_mul _ _
  calc |Work.Construction.L12 h z|
      ≤ ∫ s in Set.Ioi z, |Work.Construction.L12dens h s| := h1
    _ ≤ ∫ s in Set.Ioi z, BKe α * (Work.FTS.GalBasis.cc.Wlam s * A s) := h2
    _ = BKe α * ∫ s in Set.Ioi z, Work.FTS.GalBasis.cc.Wlam s * A s := h3
    _ ≤ BKe α * (Real.sqrt W2e * Real.sqrt (EpsSq α h)) :=
        mul_le_mul_of_nonneg_left hCS (BKe_nonneg α)
    _ ≤ 5 * (Real.sqrt W2e * Real.sqrt (EpsSq α h)) :=
        mul_le_mul_of_nonneg_right (BKe_le_five hα)
          (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    _ = (5 * Real.sqrt W2e) * Real.sqrt (EpsSq α h) := by ring
    _ ≤ (5 * Real.sqrt W2e + 1) * Real.sqrt (EpsSq α h) :=
        mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)

/-! ## The requested theorem -/

theorem L12_sub_EpsSq_le : ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, α ∈ Set.Ioc 0 1 →
    ∀ f g : Work.FTS.Galerkin.Fn,
      Work.FTS.EllipticEst.SmoothOpen f → Work.FTS.EllipticEst.SmoothOpen g →
      Work.Spaces.HkMem α 4 f → Work.Spaces.HkMem α 4 g →
      Work.FTS.StrongEps.EpsMem α (fun z θ => f z θ - g z θ) →
      ∀ z ∈ Work.Spaces.Iz,
        |Work.Construction.L12 f z - Work.Construction.L12 g z|
          ≤ C * Real.sqrt (Work.FTS.StrongEps.EpsSq α (fun z θ => f z θ - g z θ)) := by
  obtain ⟨C, hC, hCbound⟩ := L12_le_sqrt_EpsSq
  refine ⟨C, hC, ?_⟩
  intro α hα f g hfs hgs hmf hmg he z hz
  rw [← Work.FTS.StrongEps.EComparison.L12_sub_HkMem hfs hgs hmf hmg z hz]
  exact hCbound α hα (fun z θ => f z θ - g z θ) he z hz

end Work.FTS.StrongEps.EpsSqTools
