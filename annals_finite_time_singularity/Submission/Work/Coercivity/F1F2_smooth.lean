/-
# Smoothness (analyticity) of the radial commutator factors `F₁`, `F₂`

The commutator defect `E₁ = D_θ 𝓛_Γ^T f - 𝓛_Γ^T (D_θ f)` of the `ℋ^k`-coercivity
chapter splits as `E₁(z,θ) = Γ(θ)·F₁(z) + D_θΓ(θ)·F₂(z)` with the two *radial* factors

  `F₁ = L₁₂(D_θ f)·2z/(c(1+z)²) - L₁₂(Transport(D_θ f))(0)·2z²/(c(1+z)³)`,
  `F₂ = L₁₂(Transport f)(0)·2z²/(c(1+z)³) - L₁₂(f)·2z/(c(1+z)²)`

(`Work.Coercivity.CT.F1`, `Work.Coercivity.CT.F2`).  This module proves that both are
`ContDiffOn ℝ ⊤` on `(0,∞)`; note that in this Mathlib the order `⊤` is the **analytic**
order `ω` (`ContDiffOn ℝ ⊤ f s ↔ AnalyticOn ℝ f s` for open `s`), so the statement is
that `F₁` and `F₂` are real-analytic on `(0,∞)`.

The two ingredients are:

* `L₁₂^K(g)(z) = ∫_z^∞ L12dens K g s ds` where `L12dens K g s = (∫_θ K θ g(s,θ) dθ)/s`;
  the angular density is analytic because the parametric integral `z ↦ ∫_θ K θ g(z,θ) dθ`
  of a jointly analytic family is analytic (`thetaIntegral_analytic`, imported), and the
  tail integral of an analytic integrable density is analytic (`tailIntegral_analytic`,
  imported);
* the two rational coefficients `2z/(c(1+z)²)`, `2z²/(c(1+z)³)` are analytic on `(0,∞)`
  (using `1/10 ≤ c α`, so `c α ≠ 0`).

The hypotheses `IntegrableOn (L12dens K (D_θ f)) (Ioi 0)` and
`IntegrableOn (L12dens K f) (Ioi 0)` are exactly those needed for the tail-integral
representation of `L₁₂` (`Work.FM.hasDerivAt_L12`).
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Order.Interval.Basic
import Submission.Work.Coercivity.CTDefs
import Submission.Work.Spaces.CurrySmooth
import Submission.Work.Spaces.c_bounds
import Submission.Work.Coercivity.thetaIntegral_analytic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-! ## The boxes on which `SmoothNbhd` is tested -/

/-- The box of `Work.Spaces.SmoothNbhd` (an open neighbourhood of the closed quadrant). -/
abbrev nbhdBox : Set (ℝ × ℝ) := Set.Ioi (-1 : ℝ) ×ˢ Set.Ioo (-1) (π / 2 + 1)

/-- The box used as the hypothesis of `thetaIntegral_analytic`. -/
abbrev nbhdBox0 : Set (ℝ × ℝ) := Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-1) (π / 2 + 1)

theorem isOpen_nbhdBox : IsOpen nbhdBox := isOpen_Ioi.prod isOpen_Ioo

theorem isOpen_nbhdBox0 : IsOpen nbhdBox0 := isOpen_Ioi.prod isOpen_Ioo

/-! ## `D_θ f` is again smooth on a neighbourhood of the quadrant -/

/-- `K(θ) = 3 sin θ cos²θ` is real-analytic. -/
theorem contDiffOn_K : ContDiffOn ℝ ⊤ (fun θ : ℝ => Spaces.K θ) Set.univ := by
  have h : ContDiffOn ℝ ⊤ (fun θ : ℝ => 3 * Real.sin θ * Real.cos θ ^ 2) Set.univ := by
    fun_prop
  exact h.congr (fun θ _ => by simp only [Spaces.K])

/-- The angular dependence `(z,θ) ↦ K(θ)` is real-analytic on every set. -/
theorem contDiffOn_K_fst (s : Set (ℝ × ℝ)) :
    ContDiffOn ℝ ⊤ (fun p : ℝ × ℝ => Spaces.K p.2) s :=
  contDiffOn_K.comp contDiffOn_snd (fun _ _ => trivial)

/-- `D_θ f` is smooth on a neighbourhood of the quadrant whenever `f` is. -/
theorem SmoothNbhd_Dth (f : ℝ → ℝ → ℝ) (hf : Spaces.SmoothNbhd f) :
    Spaces.SmoothNbhd (Spaces.Dth f) := by
  have hpth : ContDiffOn ℝ ⊤ (Function.uncurry (Spaces.pth f)) nbhdBox :=
    Spaces.contDiffOn_uncurry_pth isOpen_nbhdBox
      (show ContDiffOn ℝ ⊤ (Function.uncurry f) nbhdBox from hf)
  have hsin : ContDiffOn ℝ ⊤ (fun p : ℝ × ℝ => Real.sin (2 * p.2)) nbhdBox := by
    fun_prop
  have hmul : ContDiffOn ℝ ⊤
      (fun p : ℝ × ℝ => Real.sin (2 * p.2) * Function.uncurry (Spaces.pth f) p) nbhdBox :=
    hsin.mul hpth
  refine hmul.congr (fun p _ => ?_)
  simp only [Function.uncurry, Spaces.Dth]

/-! ## Analyticity of the angular density `z ↦ L12dens K g z` -/

/-- The parametric `θ`-integral `z ↦ ∫_θ K(θ) g(z,θ) dθ` is real-analytic on `(0,∞)`
for `g` smooth on an open neighbourhood of the closed quadrant. -/
theorem angInt_contDiffOn (g : ℝ → ℝ → ℝ) (hg : Spaces.SmoothNbhd g) :
    ContDiffOn ℝ ⊤ (fun z => ∫ θ in Spaces.Iθ, Spaces.K θ * g z θ) (Set.Ioi 0) := by
  have hg' : ContDiffOn ℝ ⊤ (Function.uncurry g) nbhdBox0 :=
    (show ContDiffOn ℝ ⊤ (Function.uncurry g) nbhdBox from hg).mono
      (fun p hp => ⟨by
        have h : (0 : ℝ) < p.1 := hp.1
        exact lt_trans (by norm_num : (-1 : ℝ) < 0) h, hp.2⟩)
  have hKg : ContDiffOn ℝ ⊤ (Function.uncurry (fun z θ => Spaces.K θ * g z θ)) nbhdBox0 := by
    have hmul : ContDiffOn ℝ ⊤
        (fun p : ℝ × ℝ => Spaces.K p.2 * Function.uncurry g p) nbhdBox0 :=
      (contDiffOn_K_fst nbhdBox0).mul hg'
    refine hmul.congr (fun p _ => ?_)
    simp only [Function.uncurry]
  have h := thetaIntegral_analytic (F := fun z θ => Spaces.K θ * g z θ) hKg
  have hA : AnalyticOn ℝ (fun z => ∫ θ in Spaces.Iθ, Spaces.K θ * g z θ) (Set.Ioi 0) := by
    simpa only [Spaces.Iθ] using h
  exact (contDiffOn_omega_iff_analyticOn isOpen_Ioi.uniqueDiffOn).mpr hA

/-- `L12dens K g z = (∫_θ K θ g(z,θ) dθ)/z` is real-analytic on `(0,∞)`. -/
theorem L12dens_contDiffOn (g : ℝ → ℝ → ℝ) (hg : Spaces.SmoothNbhd g) :
    ContDiffOn ℝ ⊤ (fun z => FM.L12dens Spaces.K g z) (Set.Ioi 0) := by
  have hnum := angInt_contDiffOn g hg
  have heq : (fun z : ℝ => FM.L12dens Spaces.K g z)
      = fun z => (∫ θ in Spaces.Iθ, Spaces.K θ * g z θ) / z := by
    funext z
    rw [FM.L12dens, MeasureTheory.integral_div]
    rfl
  rw [heq]
  have h := ContDiffOn.div hnum contDiffOn_id (fun z hz => ne_of_gt hz)
  refine h.congr (fun z _ => ?_)
  simp only [Pi.div_apply, id_eq]

/-! ## The primitive of an analytic function is analytic -/

/-- **The primitive of a real-analytic function is real-analytic.**
If `w` is analytic at `z₀` then so is `z ↦ ∫_{z₀}^{z} w`: the power series of `w` around `z₀`
is integrated term by term (`intervalIntegral.hasSum_integral_of_dominated_convergence`), and the
integrated series is the power series of the primitive. -/
theorem primitive_analyticAt (w : ℝ → ℝ) (z₀ : ℝ) (hw : AnalyticAt ℝ w z₀) :
    AnalyticAt ℝ (fun z => ∫ s in z₀..z, w s) z₀ := by
  obtain ⟨p, hp⟩ := hw
  have hconv : ∀ᶠ u in 𝓝 (0 : ℝ), HasSum (fun n => u ^ n • p.coeff n) (w (z₀ + u)) :=
    hasFPowerSeriesAt_iff.mp hp
  obtain ⟨ε, _hε0, hε⟩ := Metric.eventually_nhds_iff.mp hconv
  have hε' : ∀ u : ℝ, |u| < ε → HasSum (fun n => u ^ n • p.coeff n) (w (z₀ + u)) := by
    intro u hu
    exact hε (y := u) (by rw [Real.dist_eq, sub_zero]; exact hu)
  have hε2 : (0 : ℝ) < ε / 2 := by linarith
  -- summability of the majorant
  have hsumm : Summable (fun n : ℕ => ‖p.coeff n‖ * (ε / 2) ^ n) := by
    have h2 : |ε / 2| < ε := by rw [abs_of_pos hε2]; linarith
    have hs : Summable (fun n : ℕ => (ε / 2) ^ n • p.coeff n) := (hε' (ε / 2) h2).summable
    have hs' : Summable (fun n : ℕ => ‖(ε / 2) ^ n • p.coeff n‖) :=
      (summable_norm_iff (f := fun n : ℕ => (ε / 2) ^ n • p.coeff n)).mpr hs
    have heq : (fun n : ℕ => ‖(ε / 2) ^ n • p.coeff n‖)
        = fun n : ℕ => ‖p.coeff n‖ * (ε / 2) ^ n := by
      funext n
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (pow_pos hε2 n)]
      ring
    rwa [heq] at hs'
  -- every point of `Ι 0 t` is within `ε/2` of `0` when `|t| < ε/2`
  have hmem : ∀ t u : ℝ, |t| < ε / 2 → u ∈ Set.uIoc (0 : ℝ) t → |u| ≤ ε / 2 := by
    intro t u ht hu
    have h1 : |u| ≤ |t| := by
      rw [Set.mem_uIoc] at hu
      rcases hu with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [abs_of_pos h1, abs_of_nonneg (by linarith : (0 : ℝ) ≤ t)]
        exact h2
      · rw [abs_of_nonpos h2, abs_of_neg (by linarith : t < 0)]
        linarith
    linarith
  -- term by term integration of the power series of `w`
  have hmain : ∀ t : ℝ, |t| < ε / 2 →
      HasSum (fun n : ℕ => (t ^ (n + 1) / ((n : ℝ) + 1)) • p.coeff n)
        (∫ u in (0 : ℝ)..t, w (z₀ + u)) := by
    intro t ht
    have hstep := intervalIntegral.hasSum_integral_of_dominated_convergence
      (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := t)
      (F := fun n u => u ^ n • p.coeff n) (f := fun u => w (z₀ + u))
      (fun n u => ‖p.coeff n‖ * (ε / 2) ^ n)
      (fun n => ((continuous_id.pow n).smul continuous_const).aestronglyMeasurable)
      (fun n => Filter.Eventually.of_forall fun u hu => by
        have hle : |u| ≤ ε / 2 := hmem t u ht hu
        have hle' : |u| ^ n ≤ (ε / 2) ^ n := pow_le_pow_left₀ (abs_nonneg u) hle n
        rw [norm_smul, Real.norm_eq_abs, abs_pow]
        calc |u| ^ n * ‖p.coeff n‖ ≤ (ε / 2) ^ n * ‖p.coeff n‖ :=
              mul_le_mul_of_nonneg_right hle' (norm_nonneg _)
          _ = ‖p.coeff n‖ * (ε / 2) ^ n := by ring)
      (Filter.Eventually.of_forall fun u _ => hsumm)
      intervalIntegrable_const
      (Filter.Eventually.of_forall fun u hu => hε' u (by linarith [hmem t u ht hu]))
    convert hstep using 1
    funext n
    have hthis : (fun u : ℝ => u ^ n • p.coeff n) = fun u => p.coeff n * u ^ n := by
      funext u; rw [smul_eq_mul, mul_comm]
    rw [hthis, intervalIntegral.integral_const_mul, integral_pow,
      zero_pow (Nat.succ_ne_zero n), sub_zero]
    simp only [smul_eq_mul]
    ring_nf
  -- the power series of the primitive
  set b : ℕ → ℝ := fun n => if n = 0 then 0 else p.coeff (n - 1) / (n : ℝ) with hb
  have hbsucc : ∀ n : ℕ, b (n + 1) = p.coeff n / ((n : ℝ) + 1) := by
    intro n
    simp [hb]
  have hcompr : ∀ t : ℝ, (∫ u in (0 : ℝ)..t, w (z₀ + u)) = ∫ s in z₀..z₀ + t, w s := by
    intro t
    rw [intervalIntegral.integral_comp_add_left]
    simp
  refine ⟨FormalMultilinearSeries.ofScalars ℝ b, ?_⟩
  rw [hasFPowerSeriesAt_iff]
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hε2] with t ht
  have ht' : |t| < ε / 2 := by
    simpa [Metric.mem_ball, Real.dist_eq] using ht
  have h1 := hmain t ht'
  rw [hcompr t] at h1
  have hfun : (fun n : ℕ => (t ^ (n + 1) / ((n : ℝ) + 1)) • p.coeff n)
      = fun n : ℕ => b (n + 1) * t ^ (n + 1) := by
    funext n
    rw [hbsucc n, smul_eq_mul, div_eq_mul_inv, div_eq_mul_inv]
    ring
  rw [hfun] at h1
  have hsum0 : (∑ i ∈ Finset.range 1, b i * t ^ i) = 0 := by simp [hb]
  have h3 := (hasSum_nat_add_iff (f := fun n : ℕ => b n * t ^ n) 1).mp h1
  rw [hsum0, add_zero] at h3
  simpa [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, mul_comm] using h3

/-- **The tail integral of an analytic integrable function is analytic.** -/
theorem tailIntegral_analytic_self (w : ℝ → ℝ) (hw : ContDiffOn ℝ ⊤ w (Set.Ioi 0))
    (hint : MeasureTheory.IntegrableOn w (Set.Ioi 0)) :
    AnalyticOn ℝ (fun z => ∫ s in Set.Ioi z, w s) (Set.Ioi 0) := by
  rw [isOpen_Ioi.analyticOn_iff_analyticOnNhd]
  intro z₀ hz₀
  have hAn : AnalyticOn ℝ w (Set.Ioi 0) :=
    (contDiffOn_omega_iff_analyticOn isOpen_Ioi.uniqueDiffOn).mp hw
  have hAw : AnalyticAt ℝ w z₀ := (isOpen_Ioi.analyticOn_iff_analyticOnNhd.mp hAn) z₀ hz₀
  have hprim : AnalyticAt ℝ (fun z => ∫ s in z₀..z, w s) z₀ := primitive_analyticAt w z₀ hAw
  have hrel : (fun z => ∫ s in Set.Ioi z, w s)
      =ᶠ[𝓝 z₀] fun z => (∫ s in Set.Ioi z₀, w s) - ∫ s in z₀..z, w s := by
    filter_upwards [isOpen_Ioi.mem_nhds hz₀] with z hz
    have hz' : (0 : ℝ) < z := hz
    have h1 : MeasureTheory.IntegrableOn w (Set.Ioi z₀) :=
      hint.mono_set (Set.Ioi_subset_Ioi hz₀.le)
    have h2 : MeasureTheory.IntegrableOn w (Set.Ioi z) :=
      hint.mono_set (Set.Ioi_subset_Ioi hz'.le)
    have h := intervalIntegral.integral_Ioi_sub_Ioi' h1 h2
    linarith
  exact (analyticAt_congr hrel).mpr (analyticAt_const.sub hprim)

/-! ## Analyticity of `L₁₂^K(g)` -/

/-- The tail integral `L₁₂^K(g)(z) = ∫_z^∞ L12dens K g s ds` is real-analytic on `(0,∞)`
whenever the density is real-analytic and integrable there. -/
theorem L12f_contDiffOn (g : ℝ → ℝ → ℝ) (hg : Spaces.SmoothNbhd g)
    (hint : IntegrableOn (FM.L12dens Spaces.K g) (Set.Ioi 0)) :
    ContDiffOn ℝ ⊤ (fun z => L12f g z) (Set.Ioi 0) := by
  have hd := L12dens_contDiffOn g hg
  have h := tailIntegral_analytic_self (w := fun s => FM.L12dens Spaces.K g s) hd hint
  have hA : AnalyticOn ℝ (fun z => L12f g z) (Set.Ioi 0) := by
    simpa only [L12f, FM.L12] using h
  exact (contDiffOn_omega_iff_analyticOn isOpen_Ioi.uniqueDiffOn).mpr hA

/-! ## The two rational coefficients -/

theorem pcoef_contDiffOn (α : ℝ) (hc : Spaces.c α ≠ 0) :
    ContDiffOn ℝ ⊤ (CT.pcoef α) (Set.Ioi 0) := by
  have h1 : ContDiffOn ℝ ⊤ (fun z : ℝ => 2 * z) (Set.Ioi 0) := by fun_prop
  have h2 : ContDiffOn ℝ ⊤ (fun z : ℝ => Spaces.c α * (1 + z) ^ 2) (Set.Ioi 0) := by fun_prop
  have h3 : ∀ z ∈ Set.Ioi (0 : ℝ), Spaces.c α * (1 + z) ^ 2 ≠ 0 := by
    intro z hz
    have hz' : (0 : ℝ) < z := hz
    exact mul_ne_zero hc (pow_ne_zero 2 (by linarith))
  have h := ContDiffOn.div h1 h2 h3
  refine h.congr (fun z _ => ?_)
  simp only [CT.pcoef, Pi.div_apply]

theorem Wcoef_contDiffOn (α : ℝ) (hc : Spaces.c α ≠ 0) :
    ContDiffOn ℝ ⊤ (CT.Wcoef α) (Set.Ioi 0) := by
  have h1 : ContDiffOn ℝ ⊤ (fun z : ℝ => 2 * z ^ 2) (Set.Ioi 0) := by fun_prop
  have h2 : ContDiffOn ℝ ⊤ (fun z : ℝ => Spaces.c α * (1 + z) ^ 3) (Set.Ioi 0) := by fun_prop
  have h3 : ∀ z ∈ Set.Ioi (0 : ℝ), Spaces.c α * (1 + z) ^ 3 ≠ 0 := by
    intro z hz
    have hz' : (0 : ℝ) < z := hz
    exact mul_ne_zero hc (pow_ne_zero 3 (by linarith))
  have h := ContDiffOn.div h1 h2 h3
  refine h.congr (fun z _ => ?_)
  simp only [CT.Wcoef, Pi.div_apply]

/-! ## The main statement -/

theorem F1F2_smooth (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f : ℝ → ℝ → ℝ)
    (hf : Work.Spaces.SmoothNbhd f)
    (hint1 : MeasureTheory.IntegrableOn (Work.FM.L12dens Work.Spaces.K (Work.Spaces.Dth f)) (Set.Ioi 0))
    (hint2 : MeasureTheory.IntegrableOn (Work.FM.L12dens Work.Spaces.K f) (Set.Ioi 0)) :
    ContDiffOn ℝ ⊤ (Work.Coercivity.CT.F1 α f) (Set.Ioi 0)
      ∧ ContDiffOn ℝ ⊤ (Work.Coercivity.CT.F2 α f) (Set.Ioi 0) := by
  have hc : Spaces.c α ≠ 0 := by
    have h := (Work.Spaces.c_bounds α hα hα1).1
    linarith
  have hDth : Spaces.SmoothNbhd (Spaces.Dth f) := SmoothNbhd_Dth f hf
  have hA1 : ContDiffOn ℝ ⊤ (fun z => L12f (Spaces.Dth f) z) (Set.Ioi 0) :=
    L12f_contDiffOn (Spaces.Dth f) hDth hint1
  have hA2 : ContDiffOn ℝ ⊤ (fun z => L12f f z) (Set.Ioi 0) :=
    L12f_contDiffOn f hf hint2
  have hp : ContDiffOn ℝ ⊤ (CT.pcoef α) (Set.Ioi 0) := pcoef_contDiffOn α hc
  have hW : ContDiffOn ℝ ⊤ (CT.Wcoef α) (Set.Ioi 0) := Wcoef_contDiffOn α hc
  constructor
  · have h : CT.F1 α f = fun z => CT.pcoef α z * CT.A1 f z - CT.Wcoef α z * CT.KC1 f := by
      funext z
      simp only [CT.F1, CT.pcoef, CT.Wcoef]
    rw [h]
    exact (hp.mul hA1).sub (hW.mul contDiffOn_const)
  · have h : CT.F2 α f = fun z => CT.Wcoef α z * CT.KC0 f - CT.pcoef α z * CT.A2 f z := by
      funext z
      simp only [CT.F2, CT.pcoef, CT.Wcoef]
    rw [h]
    exact (hW.mul contDiffOn_const).sub (hp.mul hA2)

end Work.Coercivity
