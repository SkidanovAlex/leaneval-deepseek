import Mathlib
import Submission.Work.LinnikAreas.TuranOther.PFZeroSumDefs
import Submission.Work.LinnikAreas.TuranOther.levelFactorDefs

noncomputable section
open scoped Topology
open Filter

namespace Work.LinnikAreas.TuranOther

lemma analyticAt_iteratedDeriv {g : ℂ → ℂ} {y : ℂ} (hg : AnalyticAt ℂ g y) (k : ℕ) :
    AnalyticAt ℂ (iteratedDeriv k g) y := by
  induction k with
  | zero => simpa using hg
  | succ k ih => simpa [iteratedDeriv_succ] using ih.deriv

lemma iteratedDeriv_comp_affine {α β : ℂ} {g : ℂ → ℂ} {x : ℂ} (k : ℕ)
    (hg : AnalyticAt ℂ g (α * x + β)) :
    iteratedDeriv k (fun s : ℂ => g (α * s + β)) x = α ^ k * iteratedDeriv k g (α * x + β) := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    have hmem : ∀ᶠ s in 𝓝 x, AnalyticAt ℂ g (α * s + β) := by
      have h1 : ∀ᶠ y in 𝓝 (α * x + β), AnalyticAt ℂ g y := hg.eventually_analyticAt
      have h2 : Tendsto (fun s : ℂ => α * s + β) (𝓝 x) (𝓝 (α * x + β)) :=
        (by continuity : Continuous fun s : ℂ => α * s + β).continuousAt
      exact h2.eventually h1
    have hEq : (iteratedDeriv k (fun s : ℂ => g (α * s + β))) =ᶠ[𝓝 x]
        (fun s : ℂ => α ^ k * iteratedDeriv k g (α * s + β)) := by
      filter_upwards [hmem] with s hs
      exact ih (x := s) hs
    have hdiff : DifferentiableAt ℂ (iteratedDeriv k g) (α * x + β) :=
      (analyticAt_iteratedDeriv hg k).differentiableAt
    have hAf : HasDerivAt (fun s : ℂ => α * s + β) α x := by
      simpa using (hasDerivAt_const_mul (x := x) α).add_const β
    have hF : HasDerivAt (iteratedDeriv k g) (deriv (iteratedDeriv k g) (α * x + β))
        (α * x + β) := hdiff.hasDerivAt
    have hcomp : HasDerivAt ((iteratedDeriv k g) ∘ (fun s : ℂ => α * s + β))
        (deriv (iteratedDeriv k g) (α * x + β) * α) x :=
      HasDerivAt.comp (x := x) (hh₂ := hF) (hh := hAf)
    rw [iteratedDeriv_succ, hEq.deriv_eq, iteratedDeriv_succ, deriv_const_mul_field]
    change α ^ k * deriv ((iteratedDeriv k g) ∘ (fun s : ℂ => α * s + β)) x
      = α ^ (k + 1) * deriv (iteratedDeriv k g) (α * x + β)
    rw [hcomp.deriv, pow_succ]
    ring

lemma levelFacAltCotSeries {k : ℕ} (hk : 1 ≤ k) {z : ℂ} (hz : 0 < z.im) :
    iteratedDeriv k (fun x : ℂ => (Real.pi : ℂ) * Complex.cot (Real.pi * x)) z =
      (-1 : ℂ) ^ k * (k.factorial : ℂ)
        * (tsum (fun n : ℤ => (z + (n : ℂ)) ^ (-(k + 1) : ℤ))) := by
  have hz' : z ∈ UpperHalfPlane.upperHalfPlaneSet := hz
  have hmain := iteratedDerivWithin_cot_pi_mul_eq_mul_tsum_zpow hk hz'
  rw [show (-1 - (k : ℤ)) = (-(k + 1) : ℤ) by ring] at hmain
  have hconv : iteratedDerivWithin k (fun x : ℂ => (Real.pi : ℂ) * Complex.cot (Real.pi * x))
      UpperHalfPlane.upperHalfPlaneSet z
      = iteratedDeriv k (fun x : ℂ => (Real.pi : ℂ) * Complex.cot (Real.pi * x)) z :=
    (iteratedDerivWithin_of_isOpen UpperHalfPlane.isOpen_upperHalfPlaneSet) hz'
  rw [← hconv]
  exact hmain

/-- `w ↦ π·cot(π·w)` is analytic at every point of the upper half plane. -/
lemma analyticAt_pi_cot_pi {w : ℂ} (hw : 0 < w.im) :
    AnalyticAt ℂ (fun x : ℂ => (Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * x)) w := by
  have hsin : Complex.sin ((Real.pi : ℂ) * w) ≠ 0 := by
    rw [Complex.sin_ne_zero_iff]
    intro m hm
    have h2 : ((Real.pi : ℂ) * w).im = 0 := by
      rw [hm]; simp [Complex.mul_im]
    have h3 : ((Real.pi : ℂ) * w).im = Real.pi * w.im := by simp [Complex.mul_im]
    rw [h3] at h2
    nlinarith [Real.pi_pos, hw]
  have hc : AnalyticAt ℂ (fun x : ℂ => Complex.cos ((Real.pi : ℂ) * x)) w :=
    Complex.analyticAt_cos.comp (analyticAt_const.mul analyticAt_id)
  have hs : AnalyticAt ℂ (fun x : ℂ => Complex.sin ((Real.pi : ℂ) * x)) w :=
    Complex.analyticAt_sin.comp (analyticAt_const.mul analyticAt_id)
  have hdiv : AnalyticAt ℂ
      (fun x : ℂ => Complex.cos ((Real.pi : ℂ) * x) / Complex.sin ((Real.pi : ℂ) * x)) w :=
    hc.div hs hsin
  have hfun : (fun x : ℂ => (Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * x))
      = fun x : ℂ => (Real.pi : ℂ)
          * (Complex.cos ((Real.pi : ℂ) * x) / Complex.sin ((Real.pi : ℂ) * x)) := by
    funext x
    rw [Complex.cot_eq_cos_div_sin]
  rw [hfun]
  exact analyticAt_const.mul hdiv

lemma levelFactor_logDeriv_eqOn {p : ℕ} (hp : p.Prime) {a : ℂ} (ha : ‖a‖ = 1) :
    Set.EqOn (logDeriv (fun s : ℂ => 1 - a * (p : ℂ) ^ (-s)))
      (fun s : ℂ => lvlC p * ((Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * (lvlC p * (s - lvlRoot p a)))) - (lvlL p : ℂ) / 2)
      {s : ℂ | 0 < s.re} := by
  intro s hs
  have hs' : 0 < s.re := hs
  have hane : a ≠ 0 := by
    intro h
    rw [h, norm_zero] at ha
    exact zero_ne_one ha
  have hLne : lvlL p ≠ 0 := lvlL_ne_zero hp
  have hLpos : 0 < lvlL p := lvlL_pos hp
  set L : ℂ := (lvlL p : ℂ) with hL
  set q : ℂ := Complex.exp (-(L * s)) with hq
  have hfs : (1 : ℂ) - a * (p : ℂ) ^ (-s) = 1 - a * q := by
    rw [cpow_eq_exp_lvlL hp s, ← hL, ← hq]
  have hderiv : deriv (fun t : ℂ => 1 - a * (p : ℂ) ^ (-t)) s = a * L * q := by
    have hfun : (fun t : ℂ => 1 - a * (p : ℂ) ^ (-t))
        = fun t : ℂ => 1 - a * Complex.exp (-(L * t)) := by
      funext t
      rw [cpow_eq_exp_lvlL hp t, ← hL]
    rw [hfun]
    have h1 : HasDerivAt (fun t : ℂ => -(L * t)) (-L) s :=
      (hasDerivAt_const_mul (x := s) L).neg
    have h2 : HasDerivAt (fun t : ℂ => Complex.exp (-(L * t)))
        (Complex.exp (-(L * s)) * (-L)) s :=
      (Complex.hasDerivAt_exp (-(L * s))).comp s h1
    have h3 : HasDerivAt (fun t : ℂ => a * Complex.exp (-(L * t)))
        (a * (Complex.exp (-(L * s)) * (-L))) s := h2.const_mul a
    have h4 : HasDerivAt (fun t : ℂ => 1 - a * Complex.exp (-(L * t)))
        (-(a * (Complex.exp (-(L * s)) * (-L)))) s := h3.const_sub 1
    rw [h4.deriv, ← hq]
    ring
  have hlog : logDeriv (fun t : ℂ => 1 - a * (p : ℂ) ^ (-t)) s = a * L * q / (1 - a * q) := by
    rw [logDeriv_apply, hderiv, hfs]
  have hexp : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (lvlC p * (s - lvlRoot p a)))
      = a * q := by
    have harg : (2 * (Real.pi : ℂ) * Complex.I) * (lvlC p * (s - lvlRoot p a))
        = -(L * s) + L * lvlRoot p a := by
      have h := two_pi_I_mul_lvlC_mul p (s - lvlRoot p a)
      rw [h, ← hL]
      ring
    rw [harg, Complex.exp_add, ← hq, hL, exp_lvlL_mul_lvlRoot hLne hane]
    ring
  have hlt : ‖a * q‖ < 1 := by
    rw [norm_mul, ha, one_mul, hq, Complex.norm_exp]
    have hre : (-(L * s)).re = -(lvlL p * s.re) := by
      rw [hL]
      simp [Complex.mul_re]
    rw [hre, Real.exp_lt_one_iff]
    nlinarith [hLpos, hs']
  have h1 : (1 : ℂ) - a * q ≠ 0 := by
    intro h
    have hh : a * q = 1 := (sub_eq_zero.mp h).symm
    rw [hh, norm_one] at hlt
    exact lt_irrefl 1 hlt
  rw [hlog]
  change a * L * q / (1 - a * q)
    = lvlC p * ((Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * (lvlC p * (s - lvlRoot p a)))) - L / 2
  rw [Complex.cot_pi_eq_exp_ratio, hexp]
  have hcp : lvlC p * (Real.pi : ℂ) = Complex.I * L / 2 := by
    rw [lvlC, ← hL]
    field_simp
  rw [← mul_assoc, hcp]
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  field_simp
  ring

/-- The `k`-th derived logarithmic derivative of the level factor, as the lattice sum. -/
lemma levelFactor_iteratedDeriv_eq_tsum {p : ℕ} (hp : p.Prime) {a : ℂ} (ha : ‖a‖ = 1)
    (k : ℕ) (hk : 1 ≤ k) {t : ℂ} (ht : 1 < t.re) :
    iteratedDeriv k (logDeriv (fun s : ℂ => 1 - a * (p : ℂ) ^ (-s))) t
      = (-1 : ℂ) ^ k * (k.factorial : ℂ)
        * tsum (fun n : ℤ => (t - lvlZero p a n) ^ (-(k + 1) : ℤ)) := by
  have hLne : lvlL p ≠ 0 := lvlL_ne_zero hp
  have hcne : lvlC p ≠ 0 := lvlC_ne_zero' hLne
  have htU : t ∈ {s : ℂ | 0 < s.re} := by
    show (0 : ℝ) < t.re
    linarith
  set c : ℂ := lvlC p with hc
  set u : ℂ := lvlRoot p a with hu
  set z : ℂ := c * t + -(c * u) with hz
  set F : ℂ → ℂ := fun x => (Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * x) with hF
  set G : ℂ → ℂ := fun w => c * F w - (lvlL p : ℂ) / 2 with hG
  set h : ℂ → ℂ := fun s => G (c * s + -(c * u)) with hh
  set S : ℂ := tsum (fun n : ℤ => (t - lvlZero p a n) ^ (-(k + 1) : ℤ)) with hS
  have hzi : 0 < z.im := by
    have h0 := lvlC_mul_im_pos hp ha ht
    have h1 : z = lvlC p * (t - lvlRoot p a) := by
      rw [hz, hc, hu]
      ring
    rw [h1]
    exact h0
  have hF0 : AnalyticAt ℂ F z := by
    rw [hF]
    exact analyticAt_pi_cot_pi hzi
  have hEqOn : Set.EqOn (logDeriv (fun s : ℂ => 1 - a * (p : ℂ) ^ (-s))) h {s : ℂ | 0 < s.re} := by
    intro s hs
    have hmain := levelFactor_logDeriv_eqOn hp ha hs
    have harg : lvlC p * s + -(lvlC p * lvlRoot p a) = lvlC p * (s - lvlRoot p a) := by ring
    show logDeriv (fun s : ℂ => 1 - a * (p : ℂ) ^ (-s)) s = G (c * s + -(c * u))
    rw [hG, hF, hc, hu, harg]
    exact hmain
  have hU : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have step1 : iteratedDeriv k (logDeriv (fun s : ℂ => 1 - a * (p : ℂ) ^ (-s))) t
      = iteratedDeriv k h t := by
    rw [← (iteratedDerivWithin_of_isOpen hU) htU]
    rw [(iteratedDerivWithin_congr hEqOn) htU]
    rw [(iteratedDerivWithin_of_isOpen hU) htU]
  have hGan : AnalyticAt ℂ G z := by
    rw [hG]
    exact (analyticAt_const.mul hF0).sub analyticAt_const
  have step2 : iteratedDeriv k h t = c ^ k * iteratedDeriv k G z := by
    have hmain := iteratedDeriv_comp_affine (α := c) (β := -(c * u)) (g := G) (x := t) k hGan
    exact hmain
  have step3 : iteratedDeriv k G z = c * iteratedDeriv k F z := by
    have hcF : ContDiffAt ℂ (k : ℕ∞) (fun w : ℂ => c * F w) z :=
      (analyticAt_const.mul hF0).contDiffAt
    have hconst : ContDiffAt ℂ (k : ℕ∞) (fun _ : ℂ => (lvlL p : ℂ) / 2) z := contDiffAt_const
    have hc0 : iteratedDeriv k (fun _ : ℂ => (lvlL p : ℂ) / 2) z = 0 := by
      have := iteratedDeriv_const_add (f := fun _ : ℂ => (0 : ℂ)) (x := z)
        (by omega : 0 < k) ((lvlL p : ℂ) / 2)
      simpa using this
    rw [hG]
    change iteratedDeriv k ((fun w : ℂ => c * F w) - (fun _ : ℂ => (lvlL p : ℂ) / 2)) z
      = c * iteratedDeriv k F z
    rw [iteratedDeriv_sub hcF hconst, iteratedDeriv_const_mul_field, hc0, sub_zero]
  have step4 : iteratedDeriv k F z = (-1 : ℂ) ^ k * (k.factorial : ℂ)
      * tsum (fun n : ℤ => (z + (n : ℂ)) ^ (-(k + 1) : ℤ)) := by
    rw [hF]
    exact levelFacAltCotSeries hk hzi
  have hzsum : ∀ n : ℤ, z + (n : ℂ) = c * (t - lvlZero p a n) := by
    intro n
    have hP := lvlC_mul_lvlPeriod (p := p) hLne
    rw [hz, hc, hu, lvlZero]
    linear_combination (n : ℂ) * hP
  have hterm : ∀ n : ℤ, (z + (n : ℂ)) ^ (-(k + 1) : ℤ)
      = c ^ (-(k + 1) : ℤ) * (t - lvlZero p a n) ^ (-(k + 1) : ℤ) := by
    intro n
    rw [hzsum n, mul_zpow]
  have hsum_eq : tsum (fun n : ℤ => (z + (n : ℂ)) ^ (-(k + 1) : ℤ))
      = c ^ (-(k + 1) : ℤ) * S := by
    rw [hS, ← tsum_mul_left]
    exact tsum_congr hterm
  have hcc : c ^ (k + 1) * c ^ (-(k + 1) : ℤ) = 1 := by
    rw [← zpow_natCast, ← zpow_add₀ hcne]
    simp
  have hcpow : c ^ k * c * c ^ (-(k + 1) : ℤ) = 1 := by
    rw [← pow_succ, hcc]
  rw [step1, step2, step3, step4, hsum_eq,
    show c ^ k * (c * ((-1 : ℂ) ^ k * (k.factorial : ℂ) * (c ^ (-(k + 1) : ℤ) * S)))
        = ((-1 : ℂ) ^ k * (k.factorial : ℂ)) * (c ^ k * c * c ^ (-(k + 1) : ℤ)) * S by ring,
    hcpow]
  rw [hS]
  ring

lemma deriv_lvlE (p : ℕ) (a : ℂ) (u : ℂ) :
    deriv (lvlE p a) u = a * (lvlL p : ℂ) * Complex.exp (-((lvlL p : ℂ) * u)) := by
  have h1 : HasDerivAt (fun t : ℂ => -((lvlL p : ℂ) * t)) (-(lvlL p : ℂ)) u :=
    (hasDerivAt_const_mul (x := u) (lvlL p : ℂ)).neg
  have h2 : HasDerivAt (fun t : ℂ => Complex.exp (-((lvlL p : ℂ) * t)))
      (Complex.exp (-((lvlL p : ℂ) * u)) * (-(lvlL p : ℂ))) u :=
    (Complex.hasDerivAt_exp (-((lvlL p : ℂ) * u))).comp u h1
  have h3 : HasDerivAt (fun t : ℂ => a * Complex.exp (-((lvlL p : ℂ) * t)))
      (a * (Complex.exp (-((lvlL p : ℂ) * u)) * (-(lvlL p : ℂ)))) u := h2.const_mul a
  have h4 : HasDerivAt (fun t : ℂ => 1 - a * Complex.exp (-((lvlL p : ℂ) * t)))
      (-(a * (Complex.exp (-((lvlL p : ℂ) * u)) * (-(lvlL p : ℂ))))) u := h3.const_sub 1
  have hmain : deriv (fun t : ℂ => 1 - a * Complex.exp (-((lvlL p : ℂ) * t))) u
      = a * (lvlL p : ℂ) * Complex.exp (-((lvlL p : ℂ) * u)) := by
    rw [h4.deriv]; ring
  exact hmain

/-- Summability of the lattice series `Σ_{n:ℤ} (t - lvlZero p a n)^{-(k+1)}`. -/
lemma summable_sub_lvlZero_zpow {p : ℕ} (hp : p.Prime) (a : ℂ) (k : ℕ) (hk : 1 ≤ k) (t : ℂ) :
    Summable (fun n : ℤ => (t - lvlZero p a n) ^ (-(k + 1) : ℤ)) := by
  have hLne : lvlL p ≠ 0 := lvlL_ne_zero hp
  have hbase : Summable (fun d : ℤ =>
      (lvlC p * (t - lvlRoot p a) + (d : ℂ)) ^ (-(k + 1) : ℤ)) := by
    have h := EisensteinSeries.linear_right_summable (lvlC p * (t - lvlRoot p a)) 1
      (k := (((k + 1 : ℕ) : ℤ))) (by omega)
    refine h.congr (fun d => ?_)
    have he : (((k + 1 : ℕ) : ℤ)) = ((k : ℤ) + 1) := by push_cast; ring
    rw [Int.cast_one, one_mul, he, ← zpow_neg]
  refine (hbase.mul_left ((lvlC p)⁻¹ ^ (-(k + 1) : ℤ))).congr (fun n => ?_)
  rw [sub_lvlZero_eq hLne a n t, mul_zpow]

/-- The multiplicity-weighted zero sum of one level factor equals its lattice series. -/
lemma levelFactor_zeroSum_eq_lattice {p : ℕ} (hp : p.Prime) {a : ℂ} (ha : ‖a‖ = 1)
    (k : ℕ) (hk : 1 ≤ k) {t : ℂ} (ht : 1 < t.re) :
    Summable (fun u : ℂ =>
        ((analyticOrderNatAt (lvlE p a) u : ℕ) : ℂ) * (t - u) ^ (-(k + 1) : ℤ)) ∧
      zeroSumK (lvlE p a) t k
        = tsum (fun n : ℤ => (t - lvlZero p a n) ^ (-(k + 1) : ℤ)) := by
  have hLne : lvlL p ≠ 0 := lvlL_ne_zero hp
  have hLc : (lvlL p : ℂ) ≠ 0 := by exact_mod_cast hLne
  have hane : a ≠ 0 := by
    intro h
    rw [h, norm_zero] at ha
    exact zero_ne_one ha
  have hzero : ∀ u : ℂ, lvlE p a u = 0 ↔ ∃ n : ℤ, u = lvlZero p a n := by
    intro u
    constructor
    · intro hu
      have h1 : a * Complex.exp (-((lvlL p : ℂ) * u)) = 1 := by
        have h := lvlE_apply p a u
        rw [h] at hu
        exact (sub_eq_zero.mp hu).symm
      have he : Complex.exp (-((lvlL p : ℂ) * u)) = a⁻¹ := by
        rw [mul_comm] at h1
        exact eq_inv_of_mul_eq_one_left h1
      have he0 : Complex.exp (-((lvlL p : ℂ) * lvlRoot p a)) = a⁻¹ := by
        rw [Complex.exp_neg, exp_lvlL_mul_lvlRoot (p := p) hLne hane]
      obtain ⟨m, hm⟩ := Complex.exp_eq_exp_iff_exists_int.mp (he.trans he0.symm)
      have h3 : (lvlL p : ℂ) * (u - lvlRoot p a)
          = (-m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
        linear_combination (-1) * hm
      refine ⟨-m, ?_⟩
      rw [lvlZero, lvlPeriod]
      have hkey : u - lvlRoot p a
          = (-m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I / (lvlL p : ℂ)) := by
        field_simp
        linear_combination h3
      rw [Int.cast_neg]
      linear_combination hkey
    · rintro ⟨n, rfl⟩
      exact lvlE_lvlZero hLne hane n
  have hderiv_ne : ∀ n : ℤ, deriv (lvlE p a) (lvlZero p a n) ≠ 0 := by
    intro n
    rw [deriv_lvlE]
    have he : Complex.exp (-((lvlL p : ℂ) * lvlZero p a n)) = a⁻¹ := by
      rw [Complex.exp_neg, exp_lvlL_mul_lvlZero (p := p) hLne hane n]
    rw [he]
    have : a * (lvlL p : ℂ) * a⁻¹ = (lvlL p : ℂ) := by field_simp
    rw [this]
    exact hLc
  have horder_one : ∀ n : ℤ, analyticOrderNatAt (lvlE p a) (lvlZero p a n) = 1 := by
    intro n
    have h0 : lvlE p a (lvlZero p a n) = 0 := lvlE_lvlZero hLne hane n
    have h1 : analyticOrderAt (lvlE p a) (lvlZero p a n) = 1 :=
      AnalyticAt.analyticOrderAt_eq_one_of_zero_deriv_ne_zero (analyticAt_lvlE p a _) h0
        (hderiv_ne n)
    rw [analyticOrderNatAt, h1]
    rfl
  have horder_zero : ∀ u : ℂ, (∀ n : ℤ, u ≠ lvlZero p a n) →
      analyticOrderNatAt (lvlE p a) u = 0 := by
    intro u hu
    have hne : lvlE p a u ≠ 0 := by
      intro h
      obtain ⟨n, hn⟩ := (hzero u).mp h
      exact hu n hn
    have h1 : analyticOrderAt (lvlE p a) u = 0 :=
      (analyticAt_lvlE p a u).analyticOrderAt_eq_zero.mpr hne
    rw [analyticOrderNatAt, h1]
    exact ENat.toNat_zero
  have hzero_re : ∀ n : ℤ, (lvlZero p a n).re = 0 := by
    intro n
    have hP : lvlPeriod p = ((2 * Real.pi / lvlL p : ℝ) : ℂ) * Complex.I := by
      rw [lvlPeriod]; push_cast; ring
    rw [lvlZero, Complex.add_re, lvlRoot_re ha, hP]
    simp [Complex.mul_re, Complex.mul_im]
  have ht_ne : ∀ n : ℤ, t ≠ lvlZero p a n := by
    intro n h
    have hre := congrArg Complex.re h
    rw [hzero_re n] at hre
    linarith
  set F : ℂ → ℂ := fun u => ((analyticOrderNatAt (lvlE p a) u : ℕ) : ℂ)
    * (t - u) ^ (-(k + 1) : ℤ) with hFdef
  set g : ℤ → ℂ := fun n => (t - lvlZero p a n) ^ (-(k + 1) : ℤ) with hgdef
  have hinj : Function.Injective (fun x : ↑(Function.support g) => lvlZero p a (x : ℤ)) := by
    intro x y hxy
    exact Subtype.ext (lvlZero_injective hLne a hxy)
  have hsub : Function.support F
      ⊆ Set.range (fun x : ↑(Function.support g) => lvlZero p a (x : ℤ)) := by
    intro u hu
    rw [Function.mem_support] at hu
    have hord : analyticOrderNatAt (lvlE p a) u ≠ 0 := by
      intro h0
      apply hu
      show ((analyticOrderNatAt (lvlE p a) u : ℕ) : ℂ) * (t - u) ^ (-(k + 1) : ℤ) = 0
      rw [h0]
      simp
    obtain ⟨n, hn⟩ := (hzero u).mp (apply_eq_zero_of_analyticOrderNatAt_ne_zero hord)
    exact ⟨⟨n, by
      rw [Function.mem_support, hgdef]
      exact zpow_ne_zero _ (sub_ne_zero.mpr (ht_ne n))⟩, hn.symm⟩
  have hval : ∀ x : ↑(Function.support g), F (lvlZero p a (x : ℤ)) = g (x : ℤ) := by
    intro x
    show ((analyticOrderNatAt (lvlE p a) (lvlZero p a (x : ℤ)) : ℕ) : ℂ)
        * (t - lvlZero p a (x : ℤ)) ^ (-(k + 1) : ℤ)
      = (t - lvlZero p a (x : ℤ)) ^ (-(k + 1) : ℤ)
    rw [horder_one (x : ℤ)]
    norm_num
  have hsumg : Summable g := by
    rw [hgdef]
    exact summable_sub_lvlZero_zpow hp a k hk t
  have key : HasSum F (tsum g) ↔ HasSum g (tsum g) :=
    hasSum_iff_hasSum_of_ne_zero_bij (f := F) (g := g)
      (fun x : ↑(Function.support g) => lvlZero p a (x : ℤ)) hinj hsub hval
  have hFsum : Summable F := (key.mpr hsumg.hasSum).summable
  have hFtsum : tsum F = tsum g := (key.mpr hsumg.hasSum).tsum_eq
  refine ⟨?_, ?_⟩
  · exact hFsum
  · rw [zeroSumK, ← hFdef]
    exact hFtsum

/-! ## The degenerate level factor `1` -/

lemma analyticOrderNatAt_levelConst (u : ℂ) : analyticOrderNatAt (fun _ : ℂ => (1 : ℂ)) u = 0 := by
  have h : analyticOrderAt (fun _ : ℂ => (1 : ℂ)) u = 0 :=
    (analyticAt_const (v := (1 : ℂ)) (x := u)).analyticOrderAt_eq_zero.mpr one_ne_zero
  rw [analyticOrderNatAt, h]
  exact ENat.toNat_zero

lemma zeroSumK_levelConst (t : ℂ) (k : ℕ) : zeroSumK (fun _ : ℂ => (1 : ℂ)) t k = 0 := by
  rw [zeroSumK]
  simp [analyticOrderNatAt_levelConst]

lemma iteratedDeriv_logDeriv_levelConst (t : ℂ) (k : ℕ) :
    iteratedDeriv k (logDeriv (fun _ : ℂ => (1 : ℂ))) t = 0 := by
  have h : logDeriv (fun _ : ℂ => (1 : ℂ)) = fun _ : ℂ => 0 := by
    funext z
    rw [logDeriv_apply]
    simp
  rw [h]
  exact iteratedDeriv_fun_const_zero

/-! ## The target theorem -/

theorem levelFacZeroSumAlt {p : ℕ} (hp : p.Prime) (a : ℂ) (ha : a = 0 ∨ ‖a‖ = 1)
    (k : ℕ) (hk : 1 ≤ k) {t : ℂ} (ht : 1 < t.re) :
    Summable (fun u : ℂ =>
        ((analyticOrderNatAt (fun s : ℂ => 1 - a * (p : ℂ) ^ (-s)) u : ℕ) : ℂ)
          * (t - u) ^ (-(k + 1) : ℤ)) ∧
      iteratedDeriv k (logDeriv (fun s : ℂ => 1 - a * (p : ℂ) ^ (-s))) t =
        (-1 : ℂ) ^ k * (k.factorial : ℂ)
          * Work.LinnikAreas.TuranOther.zeroSumK (fun s : ℂ => 1 - a * (p : ℂ) ^ (-s)) t k := by
  rcases ha with rfl | h1
  · have hfun : (fun s : ℂ => 1 - (0 : ℂ) * (p : ℂ) ^ (-s)) = fun _ : ℂ => (1 : ℂ) := by
      funext s
      simp
    rw [hfun]
    refine ⟨?_, ?_⟩
    · have h0 : (fun u : ℂ => ((analyticOrderNatAt (fun _ : ℂ => (1 : ℂ)) u : ℕ) : ℂ)
            * (t - u) ^ (-(k + 1) : ℤ)) = fun _ : ℂ => 0 := by
        funext u
        rw [analyticOrderNatAt_levelConst]
        simp
      rw [h0]
      exact summable_zero
    · rw [iteratedDeriv_logDeriv_levelConst, zeroSumK_levelConst]
      ring
  · obtain ⟨hsum, hzs⟩ := levelFactor_zeroSum_eq_lattice hp h1 k hk ht
    have hfun : lvlE p a = fun s : ℂ => 1 - a * (p : ℂ) ^ (-s) := lvlE_eq hp a
    have hder := levelFactor_iteratedDeriv_eq_tsum hp h1 k hk ht
    refine ⟨?_, ?_⟩
    · rw [← hfun]
      exact hsum
    · rw [hder, ← hfun, hzs]

end Work.LinnikAreas.TuranOther
