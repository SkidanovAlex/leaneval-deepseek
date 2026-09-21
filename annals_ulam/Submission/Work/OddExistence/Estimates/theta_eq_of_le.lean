import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.Kernel.Diag

/-!
# The kernel `Θ` does not depend on the perturbation for `σ ≤ s`

The last two rows of the paper's kernel `Θ n h s σ z` are the `u`-derivatives at `u = s` of the
Abel average `G₂`, and the kernel `Kvec` of that average vanishes identically for first arguments
`a > σ`: the radicand of the first kernel factorises as `ψ(a) = (σ - a) · krad(a)`, so for `a > σ`

* either `krad a ≤ 0`, and then `Kden = √(krad a) = 0`, so `K₁ = J₁ / 0 = 0`;
* or `krad a > 0`, and then `ψ(a) < 0`, so `√(ψ a) = 0`, `J₁ = 0` and again `K₁ = 0`,

and identically for `K₂`.  Consequently the Abel average `G₂ n h u σ z` vanishes for every
`u > σ` (the `τ`-integrand vanishes except at the single point `τ = 1`), and then its `s`-limit
`deriv (fun u => G₂ n h u σ z) s` vanishes at every `s ≥ σ` — including `s = σ`, where the
function is zero to the right of `σ` and `deriv` is `0` either because the function is not
differentiable there or because the right difference quotients vanish.

Hence for `σ ≤ s` the whole kernel agrees with the unperturbed one,

`Θ n h s σ z = Θ n 0 s σ z`,

with no hypothesis on `h` beyond smoothness.  In particular the estimate asked for in
`Work.OddExistence.Estimates.theta_close` holds *with `C * δ` replaced by `0`* in that range;
only the range `σ > s` is non-trivial there.

Everything here is stated for an arbitrary `C¹` perturbation `h`.
-/

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

set_option linter.unusedSimpArgs false

namespace Work.OddVolterra

noncomputable section

/-! ## Vanishing of the Abel kernels for `a > σ` -/

/-- For first arguments `a > σ` the first Abel kernel vanishes identically. -/
lemma K1_eq_zero_of_lt {h : ℝ → ℝ} (hh : ContDiff ℝ 1 h) (n : ℕ) {a σ t : ℝ} (ha : σ < a) :
    K1 n h a σ t = 0 := by
  rcases lt_trichotomy (krad h σ t a) 0 with hk | hk | hk
  · rw [K1, Kden_eq_sqrt_krad, Real.sqrt_eq_zero_of_nonpos (le_of_lt hk), div_zero]
  · rw [K1, Kden_eq_sqrt_krad, hk, Real.sqrt_zero, div_zero]
  · have hne : ¬ (σ = a) := ne_of_lt ha
    have hpsi : psi h (fun t' => line h σ t') a t = (σ - a) * krad h σ t a :=
      psi_eq_mul_krad hh σ t a
    have hneg : psi h (fun t' => line h σ t') a t < 0 := by
      rw [hpsi]
      exact mul_neg_of_neg_of_pos (by linarith) hk
    rw [K1, J1, if_neg hne, Real.sqrt_eq_zero_of_nonpos (le_of_lt hneg), mul_zero, zero_div]

/-- For first arguments `a > σ` the second Abel kernel vanishes identically. -/
lemma K2_eq_zero_of_lt {h : ℝ → ℝ} (hh : ContDiff ℝ 1 h) (n : ℕ) {a σ t : ℝ} (ha : σ < a) :
    K2 n h a σ t = 0 := by
  rcases lt_trichotomy (krad h σ t a) 0 with hk | hk | hk
  · rw [K2, Kden_eq_sqrt_krad, Real.sqrt_eq_zero_of_nonpos (le_of_lt hk), div_zero]
  · rw [K2, Kden_eq_sqrt_krad, hk, Real.sqrt_zero, div_zero]
  · have hne : ¬ (σ = a) := ne_of_lt ha
    have hpsi : psi h (fun t' => line h σ t') a t = (σ - a) * krad h σ t a :=
      psi_eq_mul_krad hh σ t a
    have hneg : psi h (fun t' => line h σ t') a t < 0 := by
      rw [hpsi]
      exact mul_neg_of_neg_of_pos (by linarith) hk
    rw [K2, J2, if_neg hne, Real.sqrt_eq_zero_of_nonpos (le_of_lt hneg), mul_zero, zero_div]

/-- For first arguments `a > σ` the two-component kernel `Kvec` vanishes identically. -/
lemma Kvec_apply_eq_zero_of_lt {h : ℝ → ℝ} (hh : ContDiff ℝ 1 h) (n : ℕ) {a σ : ℝ}
    (ha : σ < a) (x y x' y' : ℝ) (i : Fin 2) : (Kvec n h a σ x y x' y') i = 0 := by
  have h1 : K1 n h a σ (-x) = 0 := K1_eq_zero_of_lt hh n ha
  have h2 : K1 n h a σ y = 0 := K1_eq_zero_of_lt hh n ha
  have h3 : K2 n h a σ (-x) = 0 := K2_eq_zero_of_lt hh n ha
  have h4 : K2 n h a σ y = 0 := K2_eq_zero_of_lt hh n ha
  fin_cases i <;> simp [Kvec, h1, h2, h3, h4]

/-! ## Vanishing of the Abel average above `σ` -/

/-- The Abel average `G₂ n h u σ x y x' y'` vanishes for every `u > σ`: the `τ`-integrand
involves the vanishing kernel as soon as `τ < 1`. -/
lemma G2_apply_eq_zero_of_lt {h : ℝ → ℝ} (hh : ContDiff ℝ 1 h) (n : ℕ) {u σ : ℝ}
    (hσu : σ < u) (x y x' y' : ℝ) (i : Fin 2) : (G2 n h u σ x y x' y') i = 0 := by
  have hae : (fun τ : ℝ =>
      (Kvec n h (u + τ * (σ - u)) σ x y x' y') i / Real.sqrt (τ * (1 - τ)))
      =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] 0 := by
    change ∀ᵐ τ ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)),
      (Kvec n h (u + τ * (σ - u)) σ x y x' y') i / Real.sqrt (τ * (1 - τ)) = 0
    refine (ae_restrict_iff' measurableSet_Ioc).mpr ?_
    rw [MeasureTheory.ae_iff]
    refine measure_mono_null ?_ (Real.volume_singleton (a := (1 : ℝ)))
    intro τ hτ
    simp only [Set.mem_setOf_eq] at hτ
    rw [Classical.not_imp] at hτ
    simp only [Set.mem_singleton_iff]
    by_contra hne1
    have hlt : τ < 1 := lt_of_le_of_ne hτ.1.2 hne1
    have hgt : σ < u + τ * (σ - u) := by nlinarith [hτ.1.1, hlt, hσu]
    have hz := Kvec_apply_eq_zero_of_lt hh n hgt x y x' y' i
    rw [hz] at hτ
    simp at hτ
  simp only [G2]
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [MeasureTheory.integral_congr_ae hae]
  simp

/-! ## Vanishing of the derivative for `s ≥ σ` -/

/-- A function that vanishes on the right of `σ` has `deriv` zero at `σ`: either it is not
differentiable there (and `deriv` is `0` by definition), or it is differentiable, hence
continuous, so the right limit forces `F σ = 0`, and then the slope vanishes to the right. -/
lemma deriv_eq_zero_of_eventuallyEq_zero_right {F : ℝ → ℝ} {σ : ℝ}
    (hF : ∀ u : ℝ, σ < u → F u = 0) : deriv F σ = 0 := by
  by_cases hd : DifferentiableAt ℝ F σ
  · have htend : Tendsto F (𝓝[>] σ) (𝓝 (F σ)) :=
      hd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have htend0 : Tendsto F (𝓝[>] σ) (𝓝 (0 : ℝ)) := by
      refine Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [self_mem_nhdsWithin] with u hu
      exact (hF u hu).symm
    have hFσ : F σ = 0 := tendsto_nhds_unique htend htend0
    have hslope : Tendsto (slope F σ) (𝓝[>] σ) (𝓝 (deriv F σ)) :=
      hd.hasDerivAt.tendsto_slope.mono_left (by
        rw [nhdsWithin_le_iff]
        exact Filter.mem_of_superset self_mem_nhdsWithin (fun u hu => by
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
          exact ne_of_gt hu))
    have hcongr : slope F σ =ᶠ[𝓝[>] σ] (fun _ : ℝ => (0 : ℝ)) := by
      filter_upwards [self_mem_nhdsWithin] with u hu
      simp [slope, hF u hu, hFσ]
    have hslope0 : Tendsto (slope F σ) (𝓝[>] σ) (𝓝 (0 : ℝ)) :=
      Filter.Tendsto.congr' hcongr.symm tendsto_const_nhds
    exact (tendsto_nhds_unique hslope0 hslope).symm
  · rw [deriv, fderiv_zero_of_not_differentiableAt hd]
    simp

/-- The first-slot derivative of the Abel average vanishes at every `s ≥ σ`. -/
lemma deriv_G2_apply_eq_zero_of_le {h : ℝ → ℝ} (hh : ContDiff ℝ 1 h) (n : ℕ) {s σ : ℝ}
    (hσs : σ ≤ s) (x y x' y' : ℝ) (i : Fin 2) :
    deriv (fun u : ℝ => (G2 n h u σ x y x' y') i) s = 0 := by
  rcases lt_or_eq_of_le hσs with hlt | heq
  · have hev : (fun u : ℝ => (G2 n h u σ x y x' y') i) =ᶠ[𝓝 s] 0 := by
      filter_upwards [isOpen_Ioi.mem_nhds hlt] with u hu
      exact G2_apply_eq_zero_of_lt hh n hu x y x' y' i
    rw [hev.deriv_eq]
    simp
  · subst heq
    exact deriv_eq_zero_of_eventuallyEq_zero_right
      (fun u hu => G2_apply_eq_zero_of_lt hh n hu x y x' y' i)

/-! ## `Θ` is the unperturbed one for `σ ≤ s` -/

/-- For slopes `σ ≤ s` the kernel `Θ n h s σ z` does not depend on the perturbation `h`. -/
theorem Theta_eq_self_of_le {h : ℝ → ℝ} (hh : ContDiff ℝ 1 h) (n : ℕ) {s σ : ℝ}
    (hσs : σ ≤ s) (z : St) : Theta n h s σ z = Theta n 0 s σ z := by
  have h1 := deriv_G2_apply_eq_zero_of_le (h := h) hh n hσs (z 0) (z 1) (z 2) (z 3) 0
  have h2 := deriv_G2_apply_eq_zero_of_le (h := h) hh n hσs (z 0) (z 1) (z 2) (z 3) 1
  have h1' := deriv_G2_apply_eq_zero_of_le (h := (0 : ℝ → ℝ)) contDiff_const n hσs
    (z 0) (z 1) (z 2) (z 3) 0
  have h2' := deriv_G2_apply_eq_zero_of_le (h := (0 : ℝ → ℝ)) contDiff_const n hσs
    (z 0) (z 1) (z 2) (z 3) 1
  funext i
  fin_cases i <;> simp [Theta, h1, h2, h1', h2']

/-- Consequently the difference of `Θ` for `h` and for `0` vanishes for `σ ≤ s`. -/
theorem Theta_sub_self_eq_zero_of_le {h : ℝ → ℝ} (hh : ContDiff ℝ 1 h) (n : ℕ) {s σ : ℝ}
    (hσs : σ ≤ s) (z : St) : Theta n h s σ z - Theta n 0 s σ z = 0 := by
  rw [Theta_eq_self_of_le hh n hσs z, sub_self]

end

end Work.OddVolterra
