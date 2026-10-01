/-
# ZeroFreeTables — testFn72_defs

Definitions and elementary facts for the test function of Heath-Brown (1992),
Lemma 7.2 (the limiting case `θ → 0` of the variational problem of §7).

With `γ = 1/λ`, HB's auxiliary function is

  `g t = λ (1 − λ² t²)`  on `[-γ,γ]`,  `0` outside,

a continuous, even, non-negative function vanishing at `±γ`, and the test function
is `f = g ∗ g`.  Lemma 7.2 states

  `f x = (λ/30) (2 − λx)³ (4 + 6λx + λ²x²)`  for `0 ≤ x ≤ 2γ`,

with `f x = 0` for `x ≥ 2γ`, and gives `f 0 = 16λ/15`, `F 0 = 8/9`,
`F(−λ) = 8/5`, where `F` is the Laplace transform `F z = ∫₀^{x₀} e^{−zt} f t dt`.

This module fixes the notations (`tf72g`, `tf72f`, `tf72conv`, `tf72Fc`) and the
elementary facts about `g` and `f` used everywhere downstream (continuity,
positivity, support, the polynomial shape on `[0,2/λ]`, `C²` and the second
derivative bound of HB's Condition 1).
-/
import Mathlib

noncomputable section
namespace Work.ZeroFreeTables

/-- HB Lemma 7.2's auxiliary `g`: continuous, even, non-negative, supported in
`[-1/λ, 1/λ]`, and vanishing at `±1/λ`. -/
def tf72g (lam : ℝ) (t : ℝ) : ℝ := lam * max 0 (1 - lam^2 * t^2)

/-- HB Lemma 7.2's test function `f = g ∗ g`, written as the explicit polynomial on
`[0, 2/λ]` (and `0` elsewhere). -/
def tf72f (lam : ℝ) (t : ℝ) : ℝ :=
  if 0 ≤ t then (lam/30)*(max 0 (2 - lam*t))^3*(4 + 6*lam*t + lam^2*t^2) else 0

/-- The convolution `g ∗ g` over `ℝ` (HB's even, two-sided version of `f`). -/
def tf72conv (lam : ℝ) (t : ℝ) : ℝ := ∫ s, tf72g lam s * tf72g lam (t - s)

/-- The Laplace transform of the test function, for complex arguments. -/
def tf72Fc (lam : ℝ) (z : ℂ) : ℂ :=
  ∫ t in (0:ℝ)..(2/lam), Complex.exp (-(z * (t:ℂ))) * ((tf72f lam t : ℝ) : ℂ)

/-! ## Elementary facts about `g` -/

theorem tf72g_nonneg (lam : ℝ) (hlam : 0 < lam) : ∀ t : ℝ, 0 ≤ tf72g lam t := by
  intro t; unfold tf72g; positivity

theorem tf72g_even (lam : ℝ) : ∀ t : ℝ, tf72g lam (-t) = tf72g lam t := by
  intro t; unfold tf72g; ring_nf

theorem tf72g_cont (lam : ℝ) : Continuous (tf72g lam) := by
  unfold tf72g; fun_prop

theorem tf72g_supp (lam : ℝ) (hlam : 0 < lam) :
    ∀ t : ℝ, 1/lam ≤ |t| → tf72g lam t = 0 := by
  intro t ht
  unfold tf72g
  have h1 : lam^2 * (1/lam)^2 = 1 := by
    rw [one_div, inv_pow]; exact mul_inv_cancel₀ (pow_ne_zero 2 hlam.ne')
  have ht2 : (1/lam)^2 ≤ t^2 := by
    have h0 : (0:ℝ) ≤ 1/lam := by positivity
    have hh := mul_self_le_mul_self h0 ht
    simpa [sq, sq_abs] using hh
  have hle : 1 - lam^2 * t^2 ≤ 0 := by nlinarith [ht2, sq_nonneg lam]
  rw [max_eq_left hle]; ring

/-! ## Elementary facts about `f` -/

theorem tf72f_at_zero (lam : ℝ) (hlam : 0 < lam) : tf72f lam 0 = 16 * lam / 15 := by
  unfold tf72f
  rw [if_pos (le_refl (0:ℝ)), max_eq_right (by norm_num : (0:ℝ) ≤ 2 - lam*0)]
  ring

theorem tf72f_nonneg (lam : ℝ) (hlam : 0 < lam) : ∀ t : ℝ, 0 ≤ tf72f lam t := by
  intro t
  unfold tf72f
  split_ifs with ht
  · have h2 : 0 ≤ 4 + 6*lam*t + lam^2*t^2 := by nlinarith [sq_nonneg (lam*t), sq_nonneg lam]
    positivity
  · norm_num

theorem tf72f_cont (lam : ℝ) (hlam : 0 < lam) : ContinuousOn (tf72f lam) (Set.Ici 0) := by
  have hh : Continuous
      (fun t => (lam/30)*(max 0 (2 - lam*t))^3*(4 + 6*lam*t + lam^2*t^2)) := by fun_prop
  refine hh.continuousOn.congr ?_
  intro t ht
  unfold tf72f
  simp only [Set.mem_Ici] at ht
  rw [if_pos ht]

theorem tf72f_supp (lam : ℝ) (hlam : 0 < lam) : ∀ t : ℝ, 2/lam ≤ t → tf72f lam t = 0 := by
  intro t ht
  unfold tf72f
  have h2 : 2 - lam*t ≤ 0 := by
    have h3 : lam * (2/lam) ≤ lam * t := mul_le_mul_of_nonneg_left ht hlam.le
    rw [mul_div_cancel₀ _ hlam.ne'] at h3; linarith
  rw [if_pos (le_trans (by positivity : (0:ℝ) ≤ 2/lam) ht), max_eq_left h2]
  ring

theorem tf72f_eq_poly (lam : ℝ) (hlam : 0 < lam) : ∀ t ∈ Set.Icc 0 (2/lam),
    tf72f lam t = (lam/30)*(2 - lam*t)^3*(4 + 6*lam*t + lam^2*t^2) := by
  intro t ht
  unfold tf72f
  have h2 : 0 ≤ 2 - lam*t := by
    have h3 : lam * t ≤ lam * (2/lam) := mul_le_mul_of_nonneg_left ht.2 hlam.le
    rw [mul_div_cancel₀ _ hlam.ne'] at h3; linarith
  rw [if_pos ht.1, max_eq_right h2]

theorem tf72f_diff (lam : ℝ) (hlam : 0 < lam) :
    ContDiffOn ℝ 2 (tf72f lam) (Set.Ioo 0 (2/lam)) := by
  have hp : ContDiff ℝ 2
      (fun t => (lam/30)*(2 - lam*t)^3*(4 + 6*lam*t + lam^2*t^2)) := by fun_prop
  refine hp.contDiffOn.congr (fun t ht => ?_)
  unfold tf72f
  rw [if_pos ht.1.le]
  have h3 : lam*t < lam*(2/lam) := mul_lt_mul_of_pos_left ht.2 hlam
  rw [mul_div_cancel₀ _ hlam.ne'] at h3
  rw [max_eq_right (by linarith : (0:ℝ) ≤ 2 - lam*t)]

theorem tf72f_bound (lam : ℝ) (hlam : 0 < lam) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Set.Ioo (0:ℝ) (2/lam), ‖iteratedDeriv 2 (tf72f lam) t‖ ≤ B := by
  have hcd : ContDiff ℝ 2
      (fun t => (lam/30)*(2 - lam*t)^3*(4 + 6*lam*t + lam^2*t^2)) := by fun_prop
  have hcont : Continuous (iteratedDeriv 2
      (fun t => (lam/30)*(2 - lam*t)^3*(4 + 6*lam*t + lam^2*t^2))) :=
    hcd.continuous_iteratedDeriv 2 le_rfl
  obtain ⟨C, hC⟩ :=
    (isCompact_Icc (a := (0:ℝ)) (b := 2/lam)).exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun t ht => ?_⟩
  have hEq : iteratedDeriv 2 (tf72f lam) t
      = iteratedDeriv 2 (fun t => (lam/30)*(2 - lam*t)^3*(4 + 6*lam*t + lam^2*t^2)) t := by
    have hs : IsOpen (Set.Ioo (0:ℝ) (2/lam)) := isOpen_Ioo
    have hcg : Set.EqOn (tf72f lam)
        (fun t => (lam/30)*(2 - lam*t)^3*(4 + 6*lam*t + lam^2*t^2)) (Set.Ioo (0:ℝ) (2/lam)) := by
      intro x hx
      unfold tf72f
      rw [if_pos hx.1.le]
      have h3 : lam*x < lam*(2/lam) := mul_lt_mul_of_pos_left hx.2 hlam
      rw [mul_div_cancel₀ _ hlam.ne'] at h3
      rw [max_eq_right (by linarith : (0:ℝ) ≤ 2 - lam*x)]
    rw [← iteratedDerivWithin_of_isOpen (f := tf72f lam) (n := 2) hs ht,
        iteratedDerivWithin_congr hcg ht,
        iteratedDerivWithin_of_isOpen (n := 2) hs ht]
  rw [hEq]
  exact (hC t (Set.Ioo_subset_Icc_self ht)).trans (le_max_left _ _)

end Work.ZeroFreeTables
