import Mathlib
import Submission.Work.GM.Affine.setup
import Submission.Commons.Analysis.Fourier.poisson_summation_scaled

/-!
# GM §9: the comb sum is dominated by the aliasing mass

`∑_{m₃ ∈ [-n,n]} f ((x + m₃)/m) ≤ m · ∑_{k ∈ ℤ} ‖Fhat f (k m)‖`.

This is the elementary Poisson-summation step of GM §9 (`aliasing f m` is the "aliasing mass"
`Σ_k ‖Fhat f (k m)‖` of `setup.lean`).  Poisson summation (`Real.tsum_eq_tsum_fourier_...`) is
applied to the dilated function `u ↦ f (u/m)`; the dilate has compact support and Fourier transform
`m · Fhat f (m·)`, which is summable along the lattice by `DecayHyp`.
-/

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false

namespace Work.GM.Affine

noncomputable section

/-- The support of the integer shifts `k ↦ g (x + k)` of a compactly supported function is
finite. -/
lemma finite_support_int_shift {E : Type*} [TopologicalSpace E] [Zero E] {g : ℝ → E}
    (hcs : HasCompactSupport g) (x : ℝ) :
    (Function.support (fun k : ℤ => g (x + (k:ℝ)))).Finite := by
  obtain ⟨r, hr⟩ := hcs.isCompact.isBounded.subset_closedBall (0 : ℝ)
  have hb : ∀ k : ℤ, g (x + (k:ℝ)) ≠ 0 → |(k:ℝ)| ≤ r + |x| := by
    intro k hk
    have hmem : x + (k:ℝ) ∈ tsupport g := subset_tsupport g hk
    have h1 : x + (k:ℝ) ∈ Metric.closedBall (0:ℝ) r := hr hmem
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, Real.norm_eq_abs] at h1
    calc |(k:ℝ)| = |(x + (k:ℝ)) - x| := by ring_nf
      _ ≤ |x + (k:ℝ)| + |x| := abs_sub _ _
      _ ≤ r + |x| := by linarith
  set C : ℝ := r + |x| with hC
  refine (Set.finite_Icc (-⌈C⌉) (⌈C⌉)).subset ?_
  intro k hk
  obtain ⟨h1, h2⟩ := abs_le.mp (hb k hk)
  have hceil : C ≤ ((⌈C⌉ : ℤ) : ℝ) := Int.le_ceil C
  rw [Set.mem_Icc]
  constructor
  · have : (-(⌈C⌉ : ℝ)) ≤ (k:ℝ) := by linarith
    exact_mod_cast this
  · have : (k:ℝ) ≤ ((⌈C⌉ : ℤ) : ℝ) := by linarith
    exact_mod_cast this

/-- The integer shifts of a compactly supported function form a summable family. -/
lemma summable_int_shift {E : Type*} [TopologicalSpace E] [AddCommMonoid E] {g : ℝ → E}
    (hcs : HasCompactSupport g) (x : ℝ) : Summable fun k : ℤ => g (x + (k:ℝ)) :=
  summable_of_hasFiniteSupport (finite_support_int_shift hcs x)

/-- The dilation `u ↦ f (u/m)` (`m > 0`) of a compactly supported function has compact support. -/
lemma hasCompactSupport_div (f : ℝ → ℝ) {m : ℝ} (hm : 0 < m) (hcs : HasCompactSupport f) :
    HasCompactSupport fun u : ℝ => (f (u/m) : ℂ) := by
  have h1 : HasCompactSupport (fun v : ℝ => (f v : ℂ)) := hcs.comp_left Complex.ofReal_zero
  have h2 := h1.comp_homeomorph (Homeomorph.mulLeft₀ (m⁻¹) (inv_ne_zero (ne_of_gt hm)))
  have h3 : (fun u : ℝ => (f (u/m) : ℂ))
      = ((fun v : ℝ => (f v : ℂ)) ∘ (Homeomorph.mulLeft₀ (m⁻¹) (inv_ne_zero (ne_of_gt hm)))) := by
    funext u; simp [Function.comp, div_eq_mul_inv, mul_comm]
  rw [h3]
  exact h2

/-- A compactly supported function is `O (|x|^{-b})` at infinity, for any `b`. -/
lemma isBigO_cocompact_rpow {g : ℝ → ℂ} (hcs : HasCompactSupport g) (b : ℝ) :
    g =O[Filter.cocompact ℝ] (fun y : ℝ => |y| ^ (-b)) := by
  refine Asymptotics.IsBigO.of_bound 1 ?_
  rw [Filter.eventually_iff, Filter.mem_cocompact]
  refine ⟨tsupport g ∪ Metric.closedBall (0:ℝ) 1, hcs.isCompact.union (isCompact_closedBall 0 1), ?_⟩
  intro y hy
  simp only [Set.mem_compl_iff, Set.mem_union, not_or] at hy
  change ‖g y‖ ≤ 1 * ‖|y| ^ (-b)‖
  have h0 : g y = 0 := by
    by_contra hne
    exact hy.1 (subset_tsupport g hne)
  have hrp : (0:ℝ) ≤ |y| ^ (-b) := Real.rpow_nonneg (abs_nonneg y) _
  rw [h0, norm_zero, Real.norm_eq_abs, abs_of_nonneg hrp, one_mul]
  exact hrp

/-- Fourier transform of a dilated function: `𝓕 (fun u => f (u/m)) y = m · Fhat f (m y)`. -/
lemma fourier_div_ofReal (f : ℝ → ℝ) {m : ℝ} (hm : 0 < m) (y : ℝ) :
    𝓕 (fun u : ℝ => (f (u/m) : ℂ)) y = (m : ℂ) * Fhat f (y * m) := by
  have h := Commons.Analysis.Fourier.fourier_comp_div (fun u : ℝ => (f u : ℂ)) hm y
  simpa [Fhat, Function.comp] using h

/-- The lattice values of `Fhat f` form a summable family, by the decay hypothesis (with `j = 2`). -/
lemma summable_fhat_lattice {c : ℕ → ℝ → ℝ} {T : ℝ} {f : ℝ → ℝ} (hdec : DecayHyp c T f)
    {ε : ℝ} (hε : 0 < ε) {m : ℝ} (hm : 0 < m) :
    Summable fun k : ℤ => ‖Fhat f ((k:ℝ) * m)‖ := by
  set B : ℝ := c 2 ε * T ^ ε * T ^ 2 * supf f / m ^ 2 with hB
  have hle : ∀ k : ℤ, k ≠ 0 → ‖Fhat f ((k:ℝ) * m)‖ ≤ max B 0 / ((k:ℝ)^2) := by
    intro k hk
    have hk0 : (k:ℝ) * m ≠ 0 := by simp [hk, ne_of_gt hm]
    have hd := hdec 2 ε hε ((k:ℝ)*m) hk0
    have h1 : (T / |(k:ℝ) * m|) ^ 2 = T^2 / ((k:ℝ)^2 * m^2) := by
      rw [div_pow, abs_mul, abs_of_pos hm, mul_pow, sq_abs]
    calc ‖Fhat f ((k:ℝ)*m)‖ ≤ c 2 ε * T^ε * (T/|(k:ℝ)*m|)^2 * supf f := hd
      _ = B / ((k:ℝ)^2) := by rw [h1, hB]; ring
      _ ≤ max B 0 / ((k:ℝ)^2) := div_le_div_of_nonneg_right (le_max_left _ _) (by positivity)
  have hsum : Summable fun k : ℤ => max B 0 / ((k:ℝ)^2) := by
    have h1 : Summable fun k : ℤ => (1:ℝ) / ((k:ℝ)^2) :=
      (Real.summable_one_div_int_pow (p:=2)).mpr (by norm_num)
    have h2 := h1.mul_left (max B 0)
    refine h2.congr (fun k => ?_)
    ring
  refine Summable.of_norm_bounded_eventually hsum ?_
  filter_upwards [Filter.eventually_cofinite_ne (0:ℤ)] with k hk
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  exact hle k hk

theorem comb_sum_le {c : ℕ → ℝ → ℝ} {T : ℝ} {f : ℝ → ℝ} (hf : Continuous f)
    (hnn : ∀ u, 0 ≤ f u) (hcs : HasCompactSupport f) (hdec : DecayHyp c T f) {ε : ℝ}
    (hε : 0 < ε) {m : ℝ} (hm : 0 < m) (n : ℤ) (x : ℝ) :
    ∑ m₃ ∈ Finset.Icc (-n) n, f ((x + (m₃ : ℝ)) / m) ≤ m * aliasing f m := by
  have hcont : Continuous (fun u : ℝ => (f (u/m) : ℂ)) :=
    (Complex.continuous_ofReal.comp hf).comp (continuous_id.div_const m)
  have hcs_h : HasCompactSupport (fun u : ℝ => (f (u/m) : ℂ)) := hasCompactSupport_div f hm hcs
  have hO : (fun u : ℝ => (f (u/m) : ℂ)) =O[Filter.cocompact ℝ]
      (fun y : ℝ => |y| ^ (-(2:ℝ))) := isBigO_cocompact_rpow hcs_h 2
  have hfour : ∀ y : ℝ, 𝓕 (fun u : ℝ => (f (u/m) : ℂ)) y = (m : ℂ) * Fhat f (y * m) :=
    fun y => fourier_div_ofReal f hm y
  have hsumm_Fhat : Summable fun k : ℤ => ‖Fhat f ((k:ℝ) * m)‖ := summable_fhat_lattice hdec hε hm
  have hsumm_h : Summable fun k : ℤ => 𝓕 (fun u : ℝ => (f (u/m) : ℂ)) (k:ℝ) := by
    have hA : Summable fun k : ℤ => m * ‖Fhat f ((k:ℝ) * m)‖ := hsumm_Fhat.mul_left m
    have hB : Summable fun k : ℤ => ‖(m:ℂ) * Fhat f ((k:ℝ) * m)‖ := by
      refine hA.congr (fun k => ?_)
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hm.le]
    have hC : Summable fun k : ℤ => ‖𝓕 (fun u : ℝ => (f (u/m) : ℂ)) (k:ℝ)‖ := by
      refine hB.congr (fun k => ?_)
      rw [hfour]
    exact hC.of_norm
  have hsumm_shift : Summable fun k : ℤ => (fun u : ℝ => (f (u/m) : ℂ)) (x + k) :=
    summable_int_shift hcs_h x
  have hpois := Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable hcont (b := 2) (by norm_num)
    hO hsumm_h x
  have hre_shift : (∑' k : ℤ, (fun u : ℝ => (f (u/m) : ℂ)) (x + k)).re
      = ∑' k : ℤ, f ((x + (k:ℝ))/m) := by
    rw [Complex.re_tsum hsumm_shift]
    exact tsum_congr (fun k => by simp)
  have hsumm_shift_re : Summable fun k : ℤ => f ((x + (k:ℝ))/m) := by
    have h := hsumm_shift.map Complex.reCLM Complex.reCLM.continuous
    refine h.congr (fun k => ?_)
    simp
  have hfin : ∑ m₃ ∈ Finset.Icc (-n) n, f ((x + (m₃:ℝ))/m)
      ≤ ∑' k : ℤ, f ((x + (k:ℝ))/m) :=
    hsumm_shift_re.sum_le_tsum (Finset.Icc (-n) n) (fun i _ => hnn _)
  have hfour_tsum : (∑' k : ℤ,
        (𝓕 (fun u : ℝ => (f (u/m) : ℂ)) (k:ℝ)) * fourier k (x : UnitAddCircle))
      = (m:ℂ) * ∑' k : ℤ, Fhat f ((k:ℝ) * m) * fourier k (x : UnitAddCircle) := by
    rw [← tsum_mul_left]
    refine tsum_congr (fun k => ?_)
    rw [hfour]
    ring
  have hfu : ∀ k : ℤ, ‖fourier k (x : UnitAddCircle)‖ = 1 := fun k => by
    rw [fourier_apply, Circle.norm_coe]
  have hsumm_dual_norm : Summable fun k : ℤ =>
      ‖Fhat f ((k:ℝ) * m) * fourier k (x : UnitAddCircle)‖ := by
    refine hsumm_Fhat.congr (fun k => ?_)
    rw [norm_mul, hfu k, mul_one]
  calc ∑ m₃ ∈ Finset.Icc (-n) n, f ((x + (m₃:ℝ))/m)
      ≤ ∑' k : ℤ, f ((x + (k:ℝ))/m) := hfin
    _ = (∑' k : ℤ, (fun u : ℝ => (f (u/m) : ℂ)) (x + k)).re := hre_shift.symm
    _ = (∑' k : ℤ,
          (𝓕 (fun u : ℝ => (f (u/m) : ℂ)) (k:ℝ)) * fourier k (x : UnitAddCircle)).re := by
        rw [hpois]
    _ = ((m:ℂ) * ∑' k : ℤ,
          Fhat f ((k:ℝ)*m) * fourier k (x : UnitAddCircle)).re := by rw [hfour_tsum]
    _ ≤ ‖(m:ℂ) * ∑' k : ℤ, Fhat f ((k:ℝ)*m) * fourier k (x : UnitAddCircle)‖ :=
        Complex.re_le_norm _
    _ = m * ‖∑' k : ℤ, Fhat f ((k:ℝ)*m) * fourier k (x : UnitAddCircle)‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hm.le]
    _ ≤ m * ∑' k : ℤ, ‖Fhat f ((k:ℝ)*m) * fourier k (x : UnitAddCircle)‖ := by
        refine mul_le_mul_of_nonneg_left ?_ hm.le
        exact norm_tsum_le_tsum_norm hsumm_dual_norm
    _ = m * ∑' k : ℤ, ‖Fhat f ((k:ℝ)*m)‖ := by
        congr 1
        refine tsum_congr (fun k => ?_)
        rw [norm_mul, hfu k, mul_one]
    _ = m * aliasing f m := rfl

end

end Work.GM.Affine
