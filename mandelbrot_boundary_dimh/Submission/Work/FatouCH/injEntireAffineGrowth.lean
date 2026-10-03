import Mathlib
import Submission.Unif.UnivalentCompactness
import Submission.Unif.Commons.Analysis.Complex.Analytic.deriv_ne_zero_of_injOn

/-!
# An injective entire function is affine (growth-theorem route)

If `f : ℂ → ℂ` is entire and injective then `f z = a * z + b` with `a ≠ 0`.

Proof.  Normalise so that `f 0 = 0`, `deriv f 0 = 1`.  For every `R > 0` the rescaled function
`ζ ↦ f (R ζ)/R` is again injective on the unit disc with value `0` and derivative `1` at `0`, so the
Koebe growth bound of `Submission.exists_growth_bound_normalized_injective` applies to it.  At the
point `ζ = z/(2‖z‖)` (modulus `1/2`) and `R = 2‖z‖` this gives the **global linear growth bound**
`‖f z‖ ≤ 2 (3 ^ C - 1) ‖z‖`.  Cauchy's estimates for the first derivative of an entire function of
linear growth then give `‖deriv f a‖ ≤ 2 K` for all `a`; Liouville makes `deriv f` constant, equal
to `deriv f 0 = 1`, and the mean value inequality gives `f z = z`.  Undoing the normalisation
finishes.

(This avoids the removable-singularity/coefficient route: no Taylor expansion of an entire function
is needed.)
-/

namespace Work.FatouCH

open Set Metric Complex
open scoped Topology

/-! ### Derivative plumbing, phrased with explicit lambdas -/

theorem deriv_fun_sub_id {f : ℂ → ℂ} {a : ℂ} (hf : DifferentiableAt ℂ f a) :
    deriv (fun z : ℂ => f z - z) a = deriv f a - 1 := by
  have h : (fun z : ℂ => f z - z) = (f - id) := by
    funext z
    simp [Pi.sub_apply]
  rw [h, deriv_sub hf differentiableAt_id, deriv_id]

theorem deriv_fun_sub_const {f : ℂ → ℂ} {c a : ℂ} (hf : DifferentiableAt ℂ f a) :
    deriv (fun z : ℂ => f z - c) a = deriv f a := by
  have h : (fun z : ℂ => f z - c) = (f - fun _ : ℂ => c) := by
    funext z
    simp [Pi.sub_apply]
  rw [h, deriv_sub hf (differentiableAt_const c), deriv_const, sub_zero]

/-! ### Global linear growth -/

/-- **Global linear growth of a normalised injective entire function.** -/
theorem norm_le_of_injective_entire_normalized {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (hinj : Function.Injective g) (h0 : g 0 = 0) (h1 : deriv g 0 = 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ z : ℂ, ‖g z‖ ≤ K * ‖z‖ := by
  obtain ⟨C, hC, hgrowth⟩ := Submission.exists_growth_bound_normalized_injective
  have h3C : (1 : ℝ) < (3 : ℝ) ^ C := Real.one_lt_rpow (by norm_num) hC
  refine ⟨2 * ((3 : ℝ) ^ C - 1), by linarith, fun z => ?_⟩
  rcases eq_or_ne z 0 with rfl | hz
  · simp [h0]
  · have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz
    set R : ℝ := 2 * ‖z‖ with hRdef
    have hRpos : 0 < R := by rw [hRdef]; positivity
    have hRne : (R : ℂ) ≠ 0 := by exact_mod_cast hRpos.ne'
    set w : ℂ := z / (R : ℂ) with hwdef
    have hRw : (R : ℂ) * w = z := by
      rw [hwdef]; field_simp
    have hwnorm : ‖w‖ = 1 / 2 := by
      rw [hwdef, norm_div, Complex.norm_of_nonneg hRpos.le, hRdef]
      field_simp
    have hwball : w ∈ ball (0 : ℂ) 1 := by
      rw [Metric.mem_ball, dist_eq_norm, sub_zero, hwnorm]; norm_num
    set G : ℂ → ℂ := fun ζ => (R : ℂ)⁻¹ * g ((R : ℂ) * ζ) with hGdef
    have hGdiff : Differentiable ℂ G := by
      rw [hGdef]
      exact ((hg.comp (differentiable_id.const_mul (R : ℂ))).const_mul ((R : ℂ)⁻¹))
    have hGan : ∀ ζ ∈ ball (0 : ℂ) 1, AnalyticAt ℂ G ζ := fun ζ _ =>
      hGdiff.differentiableOn.analyticAt (Filter.univ_mem)
    have hGinj : Set.InjOn G (ball (0 : ℂ) 1) := by
      intro ζ₁ _ ζ₂ _ h
      simp only [hGdef] at h
      have h' : g ((R : ℂ) * ζ₁) = g ((R : ℂ) * ζ₂) := mul_left_cancel₀ (inv_ne_zero hRne) h
      exact mul_left_cancel₀ hRne (hinj h')
    have hG0 : G 0 = 0 := by simp [hGdef, h0]
    have hG1 : deriv G 0 = 1 := by
      have hin : HasDerivAt (fun ζ : ℂ => (R : ℂ) * ζ) (R : ℂ) 0 := by
        have h := (hasDerivAt_id (0 : ℂ)).const_mul (R : ℂ)
        simpa using h
      have hout : HasDerivAt g (deriv g 0) ((fun ζ : ℂ => (R : ℂ) * ζ) 0) := by
        have h := (hg ((R : ℂ) * 0)).hasDerivAt
        rw [mul_zero] at h
        simpa using h
      have hcomp : HasDerivAt (fun ζ : ℂ => g ((R : ℂ) * ζ)) (deriv g 0 * (R : ℂ)) 0 := by
        have h := hout.comp 0 hin
        simpa [Function.comp_def] using h
      have hmul : HasDerivAt (fun ζ : ℂ => (R : ℂ)⁻¹ * g ((R : ℂ) * ζ))
          ((R : ℂ)⁻¹ * (deriv g 0 * (R : ℂ))) 0 := by
        have h := hcomp.const_mul ((R : ℂ)⁻¹)
        simpa [Function.comp_def] using h
      have hfin : deriv G 0 = (R : ℂ)⁻¹ * (deriv g 0 * (R : ℂ)) := by
        rw [hGdef]
        exact hmul.deriv
      rw [hfin, h1, one_mul, inv_mul_cancel₀ hRne]
    have hgr := hgrowth G hGan hGinj hG0 hG1 w hwball
    have hgw : G w = (R : ℂ)⁻¹ * g z := by
      simp only [hGdef, hRw]
    rw [hgw, norm_mul, norm_inv, Complex.norm_of_nonneg hRpos.le, hwnorm] at hgr
    have h3 : (1 + 1 / 2) / (1 - 1 / 2) = (3 : ℝ) := by norm_num
    rw [h3] at hgr
    have hmul := mul_le_mul_of_nonneg_right hgr hRpos.le
    have hkey : R⁻¹ * ‖g z‖ * R = ‖g z‖ := by
      rw [mul_assoc, mul_comm ‖g z‖ R, ← mul_assoc, inv_mul_cancel₀ hRpos.ne', one_mul]
    rw [add_mul, one_mul, hkey] at hmul
    have hfin : ‖g z‖ ≤ ((3 : ℝ) ^ C - 1) * R := by linarith
    rw [hRdef] at hfin
    linarith

/-! ### Cauchy estimates, Liouville -/

/-- Cauchy's estimate: an entire function of linear growth has a bounded derivative. -/
theorem norm_deriv_le_of_linear_growth {g : ℂ → ℂ} (hg : Differentiable ℂ g) {K : ℝ}
    (hKpos : 0 ≤ K) (hK : ∀ z : ℂ, ‖g z‖ ≤ K * ‖z‖) (a : ℂ) : ‖deriv g a‖ ≤ 2 * K := by
  set R : ℝ := ‖a‖ + 1 with hRdef
  have hRpos : 0 < R := by rw [hRdef]; positivity
  have hdcc : DiffContOnCl ℂ g (ball a R) := hg.differentiableOn.diffContOnCl
  have hsup : ∀ z ∈ sphere a R, ‖g z‖ ≤ K * (‖a‖ + R) := by
    intro z hz
    have hz' : ‖z - a‖ = R := by
      rw [Metric.mem_sphere, dist_eq_norm] at hz; exact hz
    have hzn : ‖z‖ ≤ ‖a‖ + R := by
      calc ‖z‖ = ‖(z - a) + a‖ := by ring_nf
        _ ≤ ‖z - a‖ + ‖a‖ := norm_add_le _ _
        _ = R + ‖a‖ := by rw [hz']
        _ = ‖a‖ + R := by ring
    exact le_trans (hK z) (mul_le_mul_of_nonneg_left hzn hKpos)
  have hb := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
      (f := g) (c := a) (R := R) (C := K * (‖a‖ + R)) 1 hRpos hdcc hsup
  have h2 : K * (‖a‖ + R) / R ≤ 2 * K := by
    rw [hRdef]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < ‖a‖ + 1)]
    nlinarith
  calc ‖deriv g a‖ = ‖iteratedDeriv 1 g a‖ := by rw [iteratedDeriv_one]
    _ ≤ (Nat.factorial 1 : ℝ) * (K * (‖a‖ + R)) / R ^ 1 := hb
    _ = K * (‖a‖ + R) / R := by norm_num
    _ ≤ 2 * K := h2

/-- A bounded entire function is constant (Liouville); applied here to `deriv g`. -/
theorem deriv_eq_const_of_linear_growth {g : ℂ → ℂ} (hg : Differentiable ℂ g) {K : ℝ}
    (hKpos : 0 ≤ K) (hK : ∀ z : ℂ, ‖g z‖ ≤ K * ‖z‖) :
    ∀ a : ℂ, deriv g a = deriv g 0 := by
  have hbdd : Bornology.IsBounded (range (deriv g)) := by
    refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 2 * K)).subset ?_
    rintro y ⟨a, rfl⟩
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    exact norm_deriv_le_of_linear_growth hg hKpos hK a
  obtain ⟨c, hc⟩ := hg.deriv.exists_eq_const_of_bounded hbdd
  intro a
  rw [hc]
  simp only [Function.const_apply]

/-- A normalised injective entire function whose derivative is constantly `1` is the identity. -/
theorem eq_id_of_deriv_const_one {g : ℂ → ℂ} (hg : Differentiable ℂ g) (h0 : g 0 = 0)
    (hd : ∀ a : ℂ, deriv g a = 1) : ∀ z : ℂ, g z = z := by
  set F : ℂ → ℂ := fun z => g z - z with hFdef
  have hzero : ∀ a : ℂ, deriv F a = 0 := by
    intro a
    rw [hFdef, deriv_fun_sub_id (hg a), hd a]
    ring
  intro z
  have hMVT := convex_univ.norm_image_sub_le_of_norm_deriv_le (f := F) (C := 0)
    (fun w _ => by rw [hFdef]; exact (hg w).sub differentiableAt_id)
    (fun w _ => by rw [hzero w]; simp) (Set.mem_univ (0 : ℂ)) (Set.mem_univ z)
  have hz : ‖F z - F 0‖ = 0 := by
    have : ‖F z - F 0‖ ≤ 0 * ‖z - 0‖ := hMVT
    simpa using this
  have h1 : F z - F 0 = 0 := norm_eq_zero.mp hz
  rw [hFdef] at h1
  simp only at h1
  rw [h0] at h1
  simp only [sub_zero] at h1
  linear_combination h1

/-- **An injective entire function is affine** (Shishikura's FX-AFF without the fixed-point
hypothesis). -/
theorem injEntire_affine_growth {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hinj : Function.Injective f) :
    ∃ a b : ℂ, a ≠ 0 ∧ ∀ z : ℂ, f z = a * z + b := by
  have hderiv0 : deriv f 0 ≠ 0 := by
    refine Commons.Analysis.Complex.Analytic.deriv_ne_zero_of_injOn one_pos ?_ ?_
    · exact hf.differentiableOn.analyticAt Filter.univ_mem
    · intro x _ y _ hxy; exact hinj hxy
  set a : ℂ := deriv f 0 with hadef
  have ha0 : a ≠ 0 := by rw [hadef]; exact hderiv0
  set G : ℂ → ℂ := fun z => a⁻¹ * (f z - f 0) with hGdef
  have hGdiff : Differentiable ℂ G := by
    rw [hGdef]
    exact ((hf.sub (differentiable_const (f 0))).const_mul a⁻¹)
  have hGinj : Function.Injective G := by
    intro z₁ z₂ h
    simp only [hGdef] at h
    have h' : f z₁ - f 0 = f z₂ - f 0 := mul_left_cancel₀ (inv_ne_zero ha0) h
    have h'' : f z₁ = f z₂ := by
      simpa using congrArg (fun y : ℂ => y + f 0) h'
    exact hinj h''
  have hG0 : G 0 = 0 := by simp [hGdef]
  have hG1 : deriv G 0 = 1 := by
    have hD : HasDerivAt (fun z : ℂ => f z - f 0) (deriv f 0) 0 :=
      (hf 0).hasDerivAt.sub_const (f 0)
    have h1 : deriv G 0 = a⁻¹ * deriv f 0 := by
      rw [hGdef]
      exact (hD.const_mul a⁻¹).deriv
    rw [h1, ← hadef, inv_mul_cancel₀ ha0]
  obtain ⟨K, hKpos, hK⟩ := norm_le_of_injective_entire_normalized hGdiff hGinj hG0 hG1
  have hderivG : ∀ y : ℂ, deriv G y = 1 := by
    intro y
    rw [deriv_eq_const_of_linear_growth hGdiff hKpos.le hK y, hG1]
  have hGid : ∀ z : ℂ, G z = z := eq_id_of_deriv_const_one hGdiff hG0 hderivG
  refine ⟨a, f 0, ha0, fun z => ?_⟩
  have h := hGid z
  simp only [hGdef] at h
  have h' : f z - f 0 = a * z := by
    have h2 := congrArg (fun y : ℂ => a * y) h
    rw [← mul_assoc, mul_inv_cancel₀ ha0, one_mul] at h2
    exact h2
  rw [sub_eq_iff_eq_add] at h'
  exact h'

end Work.FatouCH
