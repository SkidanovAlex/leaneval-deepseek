import Mathlib
import Submission.Work.HFN.BlLow.window_geom
import Submission.Work.Asymptotics.BlLow.ClearTS
import Submission.Work.Asymptotics.Graze.Vanishing
import Submission.Work.Asymptotics.arcT_jprime_dense

/-!
# The numerator window bound on the low bad-line region `blLowSet`

For `τ` in `blLowSet = {τ ∈ 𝒟 : 2/5 ≤ Im τ ≤ 1/2, |Re τ| > 3/4}` and `t` in the spike window
`|t - Im τ| ≤ 1/8`, the numerator

  `M(z) = AfunFun ℓ d τ z · (z - z₀) + (n/2π)(j z - j z₀)`,   `z₀ = zpole τ = τ - n`, `n = tsign τ`,

of the CKMRV kernel's principal part at `z = i t` satisfies the "two-branch" bound

  `‖M(i t)‖ ≤ C ‖i t - z₀‖² ‖i t - crossedPt τ‖`.

The two branches are the double zero `z₀ = τ - tsign τ` of `M` and the crossed point
`crossedPt τ = tsign τ + S·τ`, at which the cleared kernel (hence `AfunFun`) vanishes and which
carries the unique `j`-coincidence of the closure of `blLowSet`
(`Work.Asymptotics.BlLow.coincidence_classification`).

The proof follows the pattern of `Work.Asymptotics.HalfFunnel.M_bound_region`: the function
`M` is bounded on the fixed compact region `blRegC`; dividing out the double zero at `z₀` gives
a holomorphic `g` with `g (crossedPt τ) = 0`, and the one-zero maximum-modulus bound applied at
`crossedPt τ` supplies the missing factor.
-/
noncomputable section

set_option maxHeartbeats 4000000

open Filter
open UpperHalfPlane
open scoped Topology

namespace Work.HFN.BlLow
open Work.Asymptotics Work.Asymptotics.BlLow  -- ck-hfn-fix: fork moved out of Work.Asymptotics

open Work.Kernels
open Work.Asymptotics.HalfFunnel Work.HFN.HalfFunnel

/-! ## 1. The complex region carrying all configuration points -/

/-- The compact region of `ℂ` containing `τ`, `zpole τ`, `i t`, `crossedPt τ` for `τ ∈ blLowSet`
and `t` in the window, together with the discs of radii `1/8` (around `zpole τ`) and `1/32`
(around `crossedPt τ`) used in the maximum principle. -/
def blRegC : Set ℂ := {u : ℂ | |u.re| ≤ 3 ∧ (1 : ℝ) / 4 ≤ u.im ∧ u.im ≤ 3 / 4}

lemma isClosed_blRegC : IsClosed blRegC := by
  have h1 : IsClosed {u : ℂ | |u.re| ≤ (3 : ℝ)} :=
    isClosed_le (continuous_abs.comp Complex.continuous_re) continuous_const
  have h2 : IsClosed {u : ℂ | (1 : ℝ) / 4 ≤ u.im} :=
    isClosed_le continuous_const Complex.continuous_im
  have h3 : IsClosed {u : ℂ | u.im ≤ (3 : ℝ) / 4} :=
    isClosed_le Complex.continuous_im continuous_const
  have hset : blRegC = {u : ℂ | |u.re| ≤ (3 : ℝ)} ∩ {u : ℂ | (1 : ℝ) / 4 ≤ u.im} ∩
      {u : ℂ | u.im ≤ (3 : ℝ) / 4} := by
    ext u; simp only [blRegC, Set.mem_ofPred_eq, Set.mem_inter_iff]; tauto
  rw [hset]
  exact (h1.inter h2).inter h3

lemma norm_le_four_of_mem_blRegC {u : ℂ} (hu : u ∈ blRegC) : ‖u‖ ≤ 4 := by
  have h1 : ‖u‖ ≤ |u.re| + |u.im| := Complex.norm_le_abs_re_add_abs_im u
  have h2 : u.im ≤ 3 / 4 := hu.2.2
  have h3 : |u.im| ≤ 3 / 4 := abs_le.mpr ⟨by linarith [hu.2.1], h2⟩
  linarith [hu.1, h3, h1]

lemma isCompact_blRegC : IsCompact blRegC := by
  have hball : blRegC ⊆ Metric.closedBall (0 : ℂ) 4 := by
    intro u hu
    rw [Metric.mem_closedBall, dist_zero_right]
    exact norm_le_four_of_mem_blRegC hu
  exact Metric.isCompact_iff_isClosed_bounded.mpr
    ⟨isClosed_blRegC, Metric.isBounded_closedBall.subset hball⟩

lemma blRegC_im_pos {u : ℂ} (hu : u ∈ blRegC) : 0 < u.im := by linarith [hu.2.1]

lemma continuousOn_ofComplex_blRegC :
    ContinuousOn (fun u : ℂ => UpperHalfPlane.ofComplex u) blRegC :=
  Work.Asymptotics.continuousOn_ofComplex_im_pos.mono (fun _ hu => blRegC_im_pos hu)

/-- Membership in `blRegC` from a disc condition. -/
lemma mem_blRegC_of_norm_sub_le {p u : ℂ} {r : ℝ} (hre : |p.re| + r ≤ 3)
    (him1 : (1 : ℝ) / 4 ≤ p.im - r) (him2 : p.im + r ≤ 3 / 4) (h : ‖u - p‖ ≤ r) :
    u ∈ blRegC := by
  have hrep : u.re = p.re + (u - p).re := by simp [Complex.sub_re]
  have himp : u.im = p.im + (u - p).im := by simp [Complex.sub_im]
  have hr : |(u - p).re| ≤ r := le_trans (Complex.abs_re_le_norm (u - p)) h
  have hi : |(u - p).im| ≤ r := le_trans (Complex.abs_im_le_norm (u - p)) h
  have hi1 : -r ≤ (u - p).im := (abs_le.mp hi).1
  have hi2 : (u - p).im ≤ r := (abs_le.mp hi).2
  refine ⟨?_, ?_, ?_⟩
  · rw [hrep]
    have := abs_add_le p.re (u - p).re
    linarith [hre, hr]
  · rw [himp]; linarith
  · rw [himp]; linarith

/-! ## 2. Elementary bounds for `blLowSet` -/

lemma blLowSet_normSq_bounds {τ : ℍ} (hτ : blLowSet τ) :
    (289 : ℝ) / 400 < ‖(τ : ℂ)‖ ^ 2 ∧ ‖(τ : ℂ)‖ ^ 2 ≤ 5 / 4 := by
  obtain ⟨h1, h2⟩ := blLowSet_re_abs_bounds hτ
  obtain ⟨h3, h4⟩ := blLowSet_im_bounds hτ
  have hsq : ‖(τ : ℂ)‖ ^ 2 = τ.re ^ 2 + τ.im ^ 2 := normSq_coe τ
  have hre1sq : ((3 : ℝ) / 4) ^ 2 < τ.re ^ 2 := by
    have h : ((3 : ℝ) / 4) ^ 2 < |τ.re| ^ 2 := by nlinarith [h1, abs_nonneg τ.re]
    rwa [sq_abs] at h
  have hhim1 : ((2 : ℝ) / 5) ^ 2 ≤ τ.im ^ 2 := by nlinarith [h3, h4, τ.im_pos]
  have hre2sq : τ.re ^ 2 < 1 := by
    have h : |τ.re| ^ 2 < 1 := by nlinarith [h2, abs_nonneg τ.re]
    rwa [sq_abs] at h
  have hhim2 : τ.im ^ 2 ≤ ((1 : ℝ) / 2) ^ 2 := by nlinarith [h3, h4, τ.im_pos]
  constructor
  · rw [hsq]; nlinarith [hre1sq, hhim1]
  · rw [hsq]; nlinarith [hre2sq, hhim2]

lemma blLowSet_mem_blRegC {τ : ℍ} (hτ : blLowSet τ) : (τ : ℂ) ∈ blRegC := by
  obtain ⟨h1, h2⟩ := blLowSet_re_abs_bounds hτ
  obtain ⟨h3, h4⟩ := blLowSet_im_bounds hτ
  have hb := abs_lt.mp h2
  refine ⟨?_, by rw [UpperHalfPlane.coe_im]; linarith, by rw [UpperHalfPlane.coe_im]; linarith⟩
  rw [UpperHalfPlane.coe_re]
  rw [abs_le]
  exact ⟨by linarith [hb.1], by linarith [hb.2]⟩

lemma zpole_mem_blRegC {τ : ℍ} (hτ : blLowSet τ) : ((zpole τ : ℍ) : ℂ) ∈ blRegC := by
  have hre := abs_lt.mp (zpole_re_abs_lt_blLow hτ)
  obtain ⟨h3, h4⟩ := blLowSet_im_bounds hτ
  have him : ((zpole τ : ℍ) : ℂ).im = τ.im := by
    rw [UpperHalfPlane.coe_im, zpole_im]
  refine ⟨?_, ?_, ?_⟩
  · rw [UpperHalfPlane.coe_re, abs_le]
    exact ⟨by linarith [hre.1], by linarith [hre.2]⟩
  · rw [him]; linarith
  · rw [him]; linarith

lemma imagAxis_mem_blRegC {τ : ℍ} {t : ℝ} (hτ : blLowSet τ) (ht : 0 < t)
    (hw : |t - τ.im| ≤ 1 / 8) : ((imagAxis t ht : ℍ) : ℂ) ∈ blRegC := by
  obtain ⟨hb1, hb2⟩ := blLow_window_bounds hτ ht hw
  have hcoe : ((imagAxis t ht : ℍ) : ℂ) = (t : ℂ) * Complex.I := rfl
  rw [hcoe]
  have him : ((t : ℂ) * Complex.I).im = t := by simp
  have hre : ((t : ℂ) * Complex.I).re = 0 := by simp
  refine ⟨by rw [hre]; norm_num, by rw [him]; linarith, by rw [him]; linarith⟩

lemma crossedPt_re_abs_le {τ : ℍ} (hτ : blLowSet τ) :
    |(crossedPt τ).re| ≤ 1 + 400 / 289 := by
  obtain ⟨hns1, hns2⟩ := blLowSet_normSq_bounds hτ
  have hns0 : 0 < ‖(τ : ℂ)‖ ^ 2 := by linarith
  have h2 := (blLowSet_re_abs_bounds hτ).2
  have htsabs : |tsign τ| = 1 := by
    rcases Work.HFN.HalfFunnel.tsign_eq_one_or_neg_one τ with h | h <;>
      rw [h] <;> norm_num
  have hratio : |τ.re / ‖(τ : ℂ)‖ ^ 2| ≤ 400 / 289 := by
    rw [abs_div, abs_of_pos hns0, div_le_iff₀ hns0]
    have hle : |τ.re| ≤ 1 := le_of_lt h2
    nlinarith
  rw [crossedPt_re]
  calc |tsign τ - τ.re / ‖(τ : ℂ)‖ ^ 2|
      ≤ |tsign τ| + |τ.re / ‖(τ : ℂ)‖ ^ 2| := abs_sub _ _
    _ = 1 + |τ.re / ‖(τ : ℂ)‖ ^ 2| := by rw [htsabs]
    _ ≤ 1 + 400 / 289 := by linarith

lemma crossedPt_im_bounds {τ : ℍ} (hτ : blLowSet τ) :
    (8 : ℝ) / 25 ≤ (crossedPt τ).im ∧ (crossedPt τ).im ≤ 200 / 289 := by
  obtain ⟨hns1, hns2⟩ := blLowSet_normSq_bounds hτ
  have hns0 : 0 < ‖(τ : ℂ)‖ ^ 2 := by linarith
  obtain ⟨h3, h4⟩ := blLowSet_im_bounds hτ
  have him := crossedPt_im τ
  constructor
  · rw [him, le_div_iff₀ hns0]; nlinarith
  · rw [him, div_le_iff₀ hns0]; nlinarith

lemma crossedPt_mem_blRegC {τ : ℍ} (hτ : blLowSet τ) : ((crossedPt τ : ℍ) : ℂ) ∈ blRegC := by
  have hre := crossedPt_re_abs_le hτ
  have him := crossedPt_im_bounds hτ
  refine ⟨?_, ?_, ?_⟩
  · rw [UpperHalfPlane.coe_re]; linarith
  · rw [UpperHalfPlane.coe_im]; linarith
  · rw [UpperHalfPlane.coe_im]; linarith

lemma ball_zpole_subset_blRegC {τ : ℍ} (hτ : blLowSet τ) {u : ℂ}
    (h : ‖u - ((zpole τ : ℍ) : ℂ)‖ ≤ 1 / 8) : u ∈ blRegC := by
  have hre : |(zpole τ).re| < 1 / 4 := zpole_re_abs_lt_blLow hτ
  obtain ⟨h3, h4⟩ := blLowSet_im_bounds hτ
  have him : ((zpole τ : ℍ) : ℂ).im = τ.im := by
    rw [UpperHalfPlane.coe_im, zpole_im]
  refine mem_blRegC_of_norm_sub_le ?_ ?_ ?_ h
  · rw [UpperHalfPlane.coe_re]; linarith
  · rw [him]; linarith
  · rw [him]; linarith

lemma ball_crossedPt_subset_blRegC {τ : ℍ} (hτ : blLowSet τ) {u : ℂ}
    (h : ‖u - ((crossedPt τ : ℍ) : ℂ)‖ ≤ 1 / 32) : u ∈ blRegC := by
  have hre := crossedPt_re_abs_le hτ
  have him := crossedPt_im_bounds hτ
  refine mem_blRegC_of_norm_sub_le ?_ ?_ ?_ h
  · rw [UpperHalfPlane.coe_re]; linarith
  · rw [UpperHalfPlane.coe_im]; linarith
  · rw [UpperHalfPlane.coe_im]; linarith

/-! ## 3. Uniform bounds on `blRegC` -/

lemma exists_bound_AfunFun_blReg (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ w : ℍ, (τ : ℂ) ∈ blRegC → (w : ℂ) ∈ blRegC →
      ‖AfunFun ℓ d τ w‖ ≤ C := by
  obtain ⟨C₀, hC₀⟩ := (isCompact_blRegC.prod isCompact_blRegC).exists_bound_of_continuousOn
    ((Work.Asymptotics.continuous_AfunFun ℓ d).continuousOn.comp
      ((continuousOn_ofComplex_blRegC.comp continuous_fst.continuousOn
          (fun p hp => hp.1)).prodMk
        (continuousOn_ofComplex_blRegC.comp continuous_snd.continuousOn
          (fun p hp => hp.2)))
      (fun p _ => Set.mem_univ _))
  refine ⟨max C₀ 0, le_max_right _ _, fun τ w hτ hw => ?_⟩
  have h1 : ‖AfunFun ℓ d τ w‖
      = ‖AfunFun ℓ d (UpperHalfPlane.ofComplex (τ : ℂ)) (UpperHalfPlane.ofComplex (w : ℂ))‖ := by
    rw [UpperHalfPlane.ofComplex_apply, UpperHalfPlane.ofComplex_apply]
  rw [h1]
  exact le_trans (hC₀ ((τ : ℂ), (w : ℂ)) ⟨hτ, hw⟩) (le_max_left _ _)

lemma exists_bound_jInvariantFun_blReg :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℍ, (w : ℂ) ∈ blRegC → ‖jInvariantFun w‖ ≤ C := by
  obtain ⟨C₀, hC₀⟩ := isCompact_blRegC.exists_bound_of_continuousOn
    (Work.Residues.continuous_jInvariantFun.continuousOn.comp continuousOn_ofComplex_blRegC
      (fun _ _ => Set.mem_univ _))
  refine ⟨max C₀ 0, le_max_right _ _, fun w hw => ?_⟩
  have h1 : ‖jInvariantFun w‖ = ‖jInvariantFun (UpperHalfPlane.ofComplex (w : ℂ))‖ := by
    rw [UpperHalfPlane.ofComplex_apply]
  rw [h1]
  exact le_trans (hC₀ (w : ℂ) hw) (le_max_left _ _)

/-- The numerator `M = Mchart` is uniformly bounded on the region `blRegC`. -/
lemma Mchart_bound_blReg (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ CM : ℝ, 0 ≤ CM ∧ ∀ (τ : ℍ) (n : ℤ) (u : ℂ), (n = 1 ∨ n = -1) →
      (tsign τ : ℝ) = (n : ℝ) → blLowSet τ → u ∈ blRegC →
      ‖Mchart ℓ d τ n u‖ ≤ CM := by
  obtain ⟨C_A, hC_A0, hAb⟩ := exists_bound_AfunFun_blReg ℓ d hd
  obtain ⟨C_j, hC_j0, hjb⟩ := exists_bound_jInvariantFun_blReg
  refine ⟨C_A * 4 + 2 * C_j, by positivity, fun τ n u hn hcast hτ hu => ?_⟩
  have huim : 0 < u.im := blRegC_im_pos hu
  have hcoe : ((UpperHalfPlane.ofComplex u : ℍ) : ℂ) = u := by
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos huim, UpperHalfPlane.coe_mk]
  have hzreg : ((zpole τ : ℍ) : ℂ) ∈ blRegC := zpole_mem_blRegC hτ
  have hzcoe : ((zpole τ : ℍ) : ℂ) = (τ : ℂ) - (n : ℂ) := zpole_coe_eq τ hcast
  have hA : ‖AfunFun ℓ d τ (UpperHalfPlane.ofComplex u)‖ ≤ C_A :=
    hAb τ _ (blLowSet_mem_blRegC hτ) (by rw [hcoe]; exact hu)
  have hJu : ‖jInvariantFun (UpperHalfPlane.ofComplex u)‖ ≤ C_j :=
    hjb _ (by rw [hcoe]; exact hu)
  have hJz : ‖jInvariantFun ((-(n : ℝ)) +ᵥ τ)‖ ≤ C_j := by
    have h1 : (-(n : ℝ)) +ᵥ τ = zpole τ := by rw [Work.Asymptotics.HalfFunnel.zpole, hcast]
    rw [h1, Work.HFN.HalfFunnel.zpole_jInvariantFun]
    exact hjb τ (blLowSet_mem_blRegC hτ)
  have hdu : ‖u - ((τ : ℂ) - (n : ℂ))‖ ≤ 4 := by
    have h1 : ((τ : ℂ) - (n : ℂ)) = ((zpole τ : ℍ) : ℂ) := hzcoe.symm
    rw [h1]
    have h := Complex.norm_le_abs_re_add_abs_im (u - ((zpole τ : ℍ) : ℂ))
    have h1' : |(u - ((zpole τ : ℍ) : ℂ)).re| ≤ 3 + 1 / 4 := by
      rw [Complex.sub_re, UpperHalfPlane.coe_re, abs_le]
      have hz := abs_lt.mp (zpole_re_abs_lt_blLow hτ)
      have hu1 := abs_le.mp hu.1
      constructor <;> linarith
    have h2' : |(u - ((zpole τ : ℍ) : ℂ)).im| ≤ 3 / 4 := by
      rw [Complex.sub_im, UpperHalfPlane.coe_im, zpole_im, abs_le]
      obtain ⟨h3', h4'⟩ := blLowSet_im_bounds hτ
      constructor <;> linarith [hu.2.1, hu.2.2]
    linarith
  have hcoef : ‖((n : ℂ) / (2 * (Real.pi : ℂ)))‖ ≤ 1 := by
    rw [norm_div]
    have hn1 : ‖(n : ℂ)‖ ≤ 1 := by
      rcases hn with h | h <;> rw [h] <;> norm_num
    have hden : (1 : ℝ) ≤ ‖(2 : ℂ) * (Real.pi : ℂ)‖ := by
      rw [norm_mul, Complex.norm_ofNat, Complex.norm_of_nonneg Real.pi_pos.le]
      linarith [Real.pi_gt_three]
    rw [div_le_one (by linarith : (0 : ℝ) < ‖(2 : ℂ) * (Real.pi : ℂ)‖)]
    linarith
  have hMj : ‖jInvariantFun (UpperHalfPlane.ofComplex u) - jInvariantFun ((-(n : ℝ)) +ᵥ τ)‖
      ≤ 2 * C_j := by
    have h := norm_sub_le (jInvariantFun (UpperHalfPlane.ofComplex u))
      (jInvariantFun ((-(n : ℝ)) +ᵥ τ))
    linarith
  have h1 : ‖AfunFun ℓ d τ (UpperHalfPlane.ofComplex u) * (u - ((τ : ℂ) - (n : ℂ)))‖
      ≤ C_A * 4 := by
    rw [norm_mul]
    exact mul_le_mul hA hdu (norm_nonneg _) hC_A0
  have h2 : ‖((n : ℂ) / (2 * (Real.pi : ℂ)))
      * (jInvariantFun (UpperHalfPlane.ofComplex u) - jInvariantFun ((-(n : ℝ)) +ᵥ τ))‖
      ≤ 2 * C_j := by
    rw [norm_mul]
    calc ‖((n : ℂ) / (2 * (Real.pi : ℂ)))‖
          * ‖jInvariantFun (UpperHalfPlane.ofComplex u) - jInvariantFun ((-(n : ℝ)) +ᵥ τ)‖
        ≤ 1 * (2 * C_j) := mul_le_mul hcoef hMj (norm_nonneg _) (by norm_num)
      _ = 2 * C_j := one_mul _
  have hsum := norm_add_le (AfunFun ℓ d τ (UpperHalfPlane.ofComplex u)
      * (u - ((τ : ℂ) - (n : ℂ))))
    (((n : ℂ) / (2 * (Real.pi : ℂ)))
      * (jInvariantFun (UpperHalfPlane.ofComplex u) - jInvariantFun ((-(n : ℝ)) +ᵥ τ)))
  rw [Mchart]
  linarith [hsum, h1, h2]

/-! ## 4. The crossed point is a zero of the numerator -/

/-- The cleared kernel vanishes along the orbit of any grazing element, unconditionally
(the `j' ≠ 0` hypothesis of `Work.Asymptotics.Graze.KfunClear_vanish_graze` being removed by
continuity and density of the non-vanishing locus of `j'`). -/
theorem KfunClear_vanish_graze_all (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (hγ : Graze.GrazeElem γ) :
    ∀ z : ℍ, KfunClear ℓ d (γ • z) z = 0 := by
  intro z
  have hsmulGL : Continuous (fun w : ℍ => (γ : GL (Fin 2) ℝ) • w) := continuous_const_smul _
  have hpair : Continuous (fun w : ℍ => (((γ : GL (Fin 2) ℝ) • w), w)) :=
    Continuous.prodMk hsmulGL continuous_id
  have hg : Continuous (fun p : ℍ × ℍ => AfunFun ℓ d p.1 p.2) :=
    Work.Asymptotics.continuous_AfunFun ℓ d
  have hcomp : Continuous ((fun p : ℍ × ℍ => AfunFun ℓ d p.1 p.2) ∘
      (fun w : ℍ => (((γ : GL (Fin 2) ℝ) • w), w))) := Continuous.comp hg hpair
  have hcontGL : Continuous (fun w : ℍ => AfunFun ℓ d ((γ : GL (Fin 2) ℝ) • w) w) := hcomp
  have hcont : Continuous (fun w : ℍ => AfunFun ℓ d (γ • w) w) := by
    simpa only [ModularGroup.sl_moeb] using hcontGL
  have hzero : ∀ w : ℍ, Work.Residues.jprime w ≠ 0 → AfunFun ℓ d (γ • w) w = 0 := by
    intro w hw
    have h := Graze.KfunClear_vanish_graze ℓ d hd γ hγ w hw
    rw [KfunClear_eq_mul_AfunFun] at h
    exact (mul_eq_zero.mp h).resolve_left
      (mul_ne_zero (ClassicalFacts.DeltaFun_ne_zero _)
        (pow_ne_zero _ (ClassicalFacts.DeltaFun_ne_zero _)))
  have hdense : Dense {w : ℍ | Work.Residues.jprime w ≠ 0} := by
    rw [Metric.dense_iff]
    intro x r hr
    obtain ⟨y, hy, hjy⟩ := Work.Asymptotics.exists_jprime_ne_zero_near' x r hr
    exact ⟨y, Metric.mem_ball.mpr (by rw [dist_comm]; exact hy), hjy⟩
  have hall : ∀ w : ℍ, AfunFun ℓ d (γ • w) w = 0 := by
    intro w
    have hclosed : IsClosed {w : ℍ | AfunFun ℓ d (γ • w) w = 0} :=
      isClosed_eq hcont continuous_const
    have hsub : {w : ℍ | Work.Residues.jprime w ≠ 0} ⊆
        {w : ℍ | AfunFun ℓ d (γ • w) w = 0} := hzero
    have h1 : (Set.univ : Set ℍ) ⊆ {w : ℍ | AfunFun ℓ d (γ • w) w = 0} := by
      rw [← hdense.closure_eq]
      exact hclosed.closure_subset_iff.mpr hsub
    exact h1 (Set.mem_univ w)
  rw [KfunClear_eq_mul_AfunFun, hall z, mul_zero]

/-- `AfunFun` vanishes at the crossed point: `AfunFun ℓ d τ (crossedPt τ) = 0`. -/
theorem AfunFun_crossedPt_zero (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (τ : ℍ) :
    AfunFun ℓ d τ (crossedPt τ) = 0 := by
  have hkey : KfunClear ℓ d τ (crossedPt τ) = 0 := by
    rcases lt_or_ge 0 τ.re with h | h
    · have hγ : Graze.GrazeElem ((ModularGroup.T * ModularGroup.S)⁻¹) := Or.inr (Or.inl rfl)
      have h1 : (ModularGroup.T * ModularGroup.S) • τ = crossedPt τ := by
        rw [crossedPt, show tsign τ = 1 from (Work.HFN.HalfFunnel.tsign_eq_one_iff τ).mpr h,
          mul_smul, UpperHalfPlane.modular_T_smul]
      have hpt : ((ModularGroup.T * ModularGroup.S)⁻¹) • (crossedPt τ) = τ := by
        rw [← h1, inv_smul_smul]
      have hz := KfunClear_vanish_graze_all ℓ d hd _ hγ (crossedPt τ)
      rwa [hpt] at hz
    · have hγ : Graze.GrazeElem (ModularGroup.S * ModularGroup.T) := Or.inr (Or.inr (Or.inl rfl))
      have hsign : tsign τ = -1 :=
        (Work.HFN.HalfFunnel.tsign_eq_neg_one_iff τ).mpr h
      have h2 : ModularGroup.T • ((-1 : ℝ) +ᵥ (ModularGroup.S • τ)) = ModularGroup.S • τ := by
        rw [UpperHalfPlane.modular_T_smul, ← vadd_assoc]
        norm_num
      have h3 : ModularGroup.S • (ModularGroup.S • τ) = τ := KL.S_smul_S_smul' τ
      have hpt : (ModularGroup.S * ModularGroup.T) • (crossedPt τ) = τ := by
        rw [crossedPt, hsign, mul_smul, h2, h3]
      have hz := KfunClear_vanish_graze_all ℓ d hd _ hγ (crossedPt τ)
      rwa [hpt] at hz
  rw [KfunClear_eq_mul_AfunFun] at hkey
  exact (mul_eq_zero.mp hkey).resolve_left
    (mul_ne_zero (ClassicalFacts.DeltaFun_ne_zero _)
      (pow_ne_zero _ (ClassicalFacts.DeltaFun_ne_zero _)))

/-- The chart version of the crossed-point vanishing:
`Mchart ℓ d τ n (crossedPt τ) = 0` for `n = ±1`. -/
lemma Mchart_crossedPt_zero (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (τ : ℍ) (n : ℤ)
    (hn : n = 1 ∨ n = -1) (hcast : (tsign τ : ℝ) = (n : ℝ)) :
    Mchart ℓ d τ n ((crossedPt τ : ℍ) : ℂ) = 0 := by
  rw [Mchart_ofComplex]
  rw [AfunFun_crossedPt_zero ℓ d hd τ, zero_mul, zero_add]
  have h1 : jInvariantFun (crossedPt τ) = jInvariantFun ((-(n : ℝ)) +ᵥ τ) := by
    rw [crossedPt_jInvariantFun]
    have h2 : (-(n : ℝ)) +ᵥ τ = zpole τ := by
      rw [Work.Asymptotics.HalfFunnel.zpole, hcast]
    rw [h2, Work.HFN.HalfFunnel.zpole_jInvariantFun]
  rw [h1, sub_self, mul_zero]

/-- On `blLowSet` the crossed point and the translate pole are distinct. -/
lemma crossedPt_ne_zpole {τ : ℍ} (hτ : blLowSet τ) :
    ((crossedPt τ : ℍ) : ℂ) ≠ ((zpole τ : ℍ) : ℂ) := by
  intro h
  have hre : (crossedPt τ).re = (zpole τ).re := by
    rw [← UpperHalfPlane.coe_re, ← UpperHalfPlane.coe_re]; exact congrArg Complex.re h
  have him : (crossedPt τ).im = (zpole τ).im := by
    rw [← UpperHalfPlane.coe_im, ← UpperHalfPlane.coe_im]; exact congrArg Complex.im h
  rw [crossedPt_im, Work.HFN.HalfFunnel.zpole_im] at him
  rw [crossedPt_re, Work.HFN.HalfFunnel.zpole_re] at hre
  have hns0 : 0 < ‖(τ : ℂ)‖ ^ 2 := by
    have h := normSq_coe τ
    nlinarith [τ.im_pos, sq_nonneg τ.re]
  have hns : ‖(τ : ℂ)‖ ^ 2 = 1 := by
    have h2 : τ.im = τ.im * ‖(τ : ℂ)‖ ^ 2 := (div_eq_iff (ne_of_gt hns0)).mp him
    have h3 : τ.im * ‖(τ : ℂ)‖ ^ 2 = τ.im * 1 := by rw [mul_one]; exact h2.symm
    exact mul_left_cancel₀ (ne_of_gt τ.im_pos) h3
  rw [hns, div_one] at hre
  have hre' : τ.re = tsign τ := by linarith
  have habs : |τ.re| = 1 := by
    rw [hre']
    rcases Work.HFN.HalfFunnel.tsign_eq_one_or_neg_one τ with h | h <;> rw [h] <;> norm_num
  have hlt := (blLowSet_re_abs_bounds hτ).2
  linarith [habs, hlt]

/-! ## 5. The window (two-branch) bound for the numerator -/

theorem window_Mnum_bound (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ CM : ℝ, 0 ≤ CM ∧ ∀ (τ : ℍ) (t : ℝ) (ht : 0 < t),
      blLowSet τ → |t - τ.im| ≤ 1 / 8 →
      ‖Work.Asymptotics.HalfFunnel.Mnum ℓ d τ t ht‖
        ≤ CM * ‖((Work.Kernels.imagAxis t ht : ℍ) : ℂ)
            - (((Work.Asymptotics.HalfFunnel.zpole τ) : ℍ) : ℂ)‖ ^ 2
          * ‖((Work.Kernels.imagAxis t ht : ℍ) : ℂ)
            - ((crossedPt τ : ℍ) : ℂ)‖ := by
  obtain ⟨CM, hCM, hMb⟩ := Mchart_bound_blReg ℓ d hd
  refine ⟨2 ^ 19 * CM + 1, by positivity, ?_⟩
  intro τ t ht hτ hw
  obtain ⟨n, hn, hcast⟩ := tsign_eq_intCast τ
  set Q : ℂ := (τ : ℂ) - (n : ℂ) with hQ
  set zc : ℂ := (t : ℂ) * Complex.I with hzc
  set Sc : ℂ := ((crossedPt τ : ℍ) : ℂ) with hSc
  have hz₀c : ((zpole τ : ℍ) : ℂ) = Q := by rw [hQ]; exact zpole_coe_eq τ hcast
  have hQim : (1 : ℝ) / 4 ≤ Q.im := by
    have h2 : Q.im = τ.im := by rw [← hz₀c, UpperHalfPlane.coe_im, zpole_im]
    rw [h2]
    linarith [(blLowSet_im_bounds hτ).1]
  have hQpos : 0 < Q.im := by linarith
  have hΩ : {u : ℂ | 0 < u.im} ∈ 𝓝 Q :=
    (isOpen_lt continuous_const Complex.continuous_im).mem_nhds hQpos
  have hM0 : Mchart ℓ d τ n Q = 0 := by rw [hQ]; exact Mchart_self_zero ℓ d τ n
  have hMd0 : deriv (Mchart ℓ d τ n) Q = 0 := by
    rw [hQ]; exact deriv_Mchart_self_zero ℓ d hd τ n hn
  have hScne : Sc ≠ Q := by
    intro h
    have h1 : Sc = ((zpole τ : ℍ) : ℂ) := h.trans hz₀c.symm
    rw [hSc] at h1
    exact crossedPt_ne_zpole hτ h1
  have hMSc : Mchart ℓ d τ n Sc = 0 := by
    rw [hSc]; exact Mchart_crossedPt_zero ℓ d hd τ n hn hcast
  set g : ℂ → ℂ := dslope (dslope (Mchart ℓ d τ n) Q) Q with hg
  have hA1 : dslope (Mchart ℓ d τ n) Q Q = 0 := by rw [dslope_same]; exact hMd0
  have hfac : ∀ w : ℂ, Mchart ℓ d τ n w = (w - Q) ^ 2 * g w := by
    intro w
    have h1 : (w - Q) * dslope (Mchart ℓ d τ n) Q w = Mchart ℓ d τ n w := by
      simpa using sub_smul_dslope_of_zero hM0 w
    have h2 : (w - Q) * g w = dslope (Mchart ℓ d τ n) Q w := by
      rw [hg]; simpa using sub_smul_dslope_of_zero hA1 w
    rw [← h1, ← h2]; ring
  have hgSc : g Sc = 0 := by
    have h := hfac Sc
    rw [hMSc] at h
    exact (mul_eq_zero.mp h.symm).resolve_left (pow_ne_zero 2 (sub_ne_zero.mpr hScne))
  have hgd : DifferentiableOn ℂ g {u : ℂ | 0 < u.im} := by
    rw [hg]
    exact (Complex.differentiableOn_dslope hΩ).mpr
      ((Complex.differentiableOn_dslope hΩ).mpr (differentiableOn_Mchart ℓ d hd τ n))
  have hgc : ContinuousOn g {u : ℂ | 0 < u.im} := by
    rw [hg]
    have h1 : ContinuousOn (dslope (Mchart ℓ d τ n) Q) {u : ℂ | 0 < u.im} :=
      (continuousOn_dslope hΩ).mpr
        ⟨(differentiableOn_Mchart ℓ d hd τ n).continuousOn,
          (differentiableOn_Mchart ℓ d hd τ n).differentiableAt hΩ⟩
    exact (continuousOn_dslope hΩ).mpr ⟨h1, ((Complex.differentiableOn_dslope hΩ).mpr
      (differentiableOn_Mchart ℓ d hd τ n)).differentiableAt hΩ⟩
  have him_of_le : ∀ u : ℂ, ‖u - Q‖ ≤ 1 / 8 → 0 < u.im := by
    intro u hu
    have h1 := Complex.abs_im_le_norm (u - Q)
    rw [Complex.sub_im] at h1
    have h2 := abs_le.mp h1
    linarith [h2.1, hu, hQim]
  have hgc_dcc : DiffContOnCl ℂ g (Metric.ball Q (1 / 8)) :=
    ⟨hgd.mono (fun u hu => him_of_le u (by
        have h := Metric.mem_ball.mp hu; rw [dist_eq_norm] at h; exact le_of_lt h)),
     hgc.mono (fun u hu => him_of_le u (by
        have h := Metric.mem_closedBall.mp (Metric.closure_ball_subset_closedBall hu)
        rwa [dist_eq_norm] at h))⟩
  have hregQ : ∀ w : ℂ, ‖w - Q‖ ≤ 1 / 8 → w ∈ blRegC := by
    intro w hw'
    rw [← hz₀c] at hw'
    exact ball_zpole_subset_blRegC hτ hw'
  have hfront : ∀ w ∈ frontier (Metric.ball Q (1 / 8)), ‖g w‖ ≤ 64 * CM := by
    intro w hw'
    have hwd : ‖w - Q‖ = 1 / 8 := by
      rw [← dist_eq_norm]
      exact Metric.mem_sphere.mp (Metric.frontier_ball_subset_sphere hw')
    have hwreg : w ∈ blRegC := hregQ w (le_of_eq hwd)
    have hMw : ‖Mchart ℓ d τ n w‖ ≤ CM := hMb τ n w hn hcast hτ hwreg
    have hmul : ‖Mchart ℓ d τ n w‖ = (1 / 64 : ℝ) * ‖g w‖ := by
      rw [hfac w, norm_mul, norm_pow, hwd]; norm_num
    linarith [hMw, hmul, norm_nonneg (g w)]
  have hg64 : ∀ u : ℂ, ‖u - Q‖ < 1 / 8 → ‖g u‖ ≤ 64 * CM := by
    intro u hu
    refine Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hgc_dcc hfront ?_
    exact subset_closure (Metric.mem_ball.mpr (by rw [dist_eq_norm]; exact hu))
  have hScim : (1 / 4 : ℝ) ≤ Sc.im := by
    have h := (crossedPt_mem_blRegC hτ).2.1
    rw [hSc, UpperHalfPlane.coe_im]
    exact h
  have himSc_of_le : ∀ u : ℂ, ‖u - Sc‖ ≤ 1 / 32 → 0 < u.im := by
    intro u hu
    have h1 := Complex.abs_im_le_norm (u - Sc)
    rw [Complex.sub_im] at h1
    have h2 := abs_le.mp h1
    linarith [h2.1, hu, hScim]
  have hregSc : ∀ w : ℂ, ‖w - Sc‖ ≤ 1 / 32 → w ∈ blRegC := by
    intro w hw'
    rw [hSc] at hw'
    exact ball_crossedPt_subset_blRegC hτ hw'
  have hg4096 : ∀ u : ℂ, ‖u - Sc‖ ≤ 1 / 32 → ‖g u‖ ≤ 4096 * CM := by
    intro u hu
    rcases lt_or_ge ‖u - Q‖ (1 / 8) with hlt | hge
    · have h := hg64 u hlt; linarith [hCM]
    · have hureg : u ∈ blRegC := hregSc u hu
      have hMu : ‖Mchart ℓ d τ n u‖ ≤ CM := hMb τ n u hn hcast hτ hureg
      have hmul : ‖Mchart ℓ d τ n u‖ = ‖u - Q‖ ^ 2 * ‖g u‖ := by
        rw [hfac u, norm_mul, norm_pow]
      have h2 : (1 / 64 : ℝ) ≤ ‖u - Q‖ ^ 2 := by
        nlinarith [hge, norm_nonneg (u - Q)]
      have h3 : (1 / 64 : ℝ) * ‖g u‖ ≤ ‖Mchart ℓ d τ n u‖ := by
        rw [hmul]; exact mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
      linarith [h3, hMu, hCM]
  have hone : ∀ u : ℂ, ‖u - Sc‖ ≤ 1 / 128 → ‖g u‖ ≤ 2 ^ 18 * CM * ‖u - Sc‖ := by
    intro u hu
    have hdcc : DiffContOnCl ℂ g (Metric.ball Sc (1 / 32)) :=
      ⟨hgd.mono (fun x hx => himSc_of_le x (by
            have h := Metric.mem_ball.mp hx; rw [dist_eq_norm] at h; exact le_of_lt h)),
       hgc.mono (fun x hx => himSc_of_le x (by
            have h := Metric.mem_closedBall.mp (Metric.closure_ball_subset_closedBall hx)
            rwa [dist_eq_norm] at h))⟩
    have hbd : ∀ z ∈ Metric.ball Sc (1 / 32), ‖g z‖ ≤ 4096 * CM := by
      intro z hz
      have h := Metric.mem_ball.mp hz
      rw [dist_eq_norm] at h
      exact hg4096 z (le_of_lt h)
    have hmem : Sc ∈ Metric.ball Sc (1 / 32 / 2) :=
      Metric.mem_ball.mpr (by rw [dist_self]; norm_num)
    have hkey := KL.norm_le_mul_dist_of_one_zero (f := g) (c := Sc) (ρ := 1 / 32)
      (M := 4096 * CM) (by norm_num) hdcc hbd hmem hgSc
    have hconst : 2 * (4096 * CM) / (1 / 32) = 2 ^ 18 * CM := by norm_num; ring
    have hmain := hkey u (Metric.mem_ball.mpr (by rw [dist_eq_norm]; linarith [hu]))
    rwa [hconst] at hmain
  have hzc' : ((Work.Kernels.imagAxis t ht : ℍ) : ℂ) = zc := by rw [hzc]; rfl
  have hzcReg : zc ∈ blRegC := by
    rw [← hzc']; exact imagAxis_mem_blRegC hτ ht hw
  have hMn : Mnum ℓ d τ t ht = Mchart ℓ d τ n zc := by
    rw [hzc]; exact Mnum_eq_Mchart ℓ d ht hcast
  have hMz : ‖Mnum ℓ d τ t ht‖ = ‖zc - Q‖ ^ 2 * ‖g zc‖ := by
    rw [hMn, hfac zc, norm_mul, norm_pow]
  rw [hzc', hz₀c]
  have ha2 : 0 ≤ ‖zc - Q‖ ^ 2 := sq_nonneg _
  have hb2 : 0 ≤ ‖zc - Sc‖ := norm_nonneg _
  by_cases hb : ‖zc - Sc‖ ≤ 1 / 128
  · have h1 := hone zc hb
    have hA : ‖Mnum ℓ d τ t ht‖ ≤ 2 ^ 18 * CM * (‖zc - Q‖ ^ 2 * ‖zc - Sc‖) := by
      rw [hMz]
      calc ‖zc - Q‖ ^ 2 * ‖g zc‖ ≤ ‖zc - Q‖ ^ 2 * (2 ^ 18 * CM * ‖zc - Sc‖) :=
            mul_le_mul_of_nonneg_left h1 ha2
        _ = 2 ^ 18 * CM * (‖zc - Q‖ ^ 2 * ‖zc - Sc‖) := by ring
    have hle : 2 ^ 18 * CM ≤ 2 ^ 19 * CM + 1 := by nlinarith [hCM]
    calc ‖Mnum ℓ d τ t ht‖ ≤ 2 ^ 18 * CM * (‖zc - Q‖ ^ 2 * ‖zc - Sc‖) := hA
      _ ≤ (2 ^ 19 * CM + 1) * (‖zc - Q‖ ^ 2 * ‖zc - Sc‖) :=
            mul_le_mul_of_nonneg_right hle (mul_nonneg ha2 hb2)
      _ = (2 ^ 19 * CM + 1) * ‖zc - Q‖ ^ 2 * ‖zc - Sc‖ := by ring
  · push_neg at hb
    by_cases ha : ‖zc - Q‖ < 1 / 8
    · have h1 := hg64 zc ha
      have hbpos : 0 < ‖zc - Sc‖ := by linarith
      have hA : ‖Mnum ℓ d τ t ht‖ ≤ 64 * CM * ‖zc - Q‖ ^ 2 := by
        rw [hMz]
        calc ‖zc - Q‖ ^ 2 * ‖g zc‖ ≤ ‖zc - Q‖ ^ 2 * (64 * CM) :=
              mul_le_mul_of_nonneg_left h1 ha2
          _ = 64 * CM * ‖zc - Q‖ ^ 2 := by ring
      have hstep1 : 64 * CM * ‖zc - Q‖ ^ 2 ≤ 2 ^ 12 * CM * ‖zc - Q‖ ^ 2 := by
        have h2 : 64 * CM ≤ 2 ^ 12 * CM := by nlinarith [hCM]
        exact mul_le_mul_of_nonneg_right h2 ha2
      have hstep2 : 2 ^ 12 * CM * ‖zc - Q‖ ^ 2
          ≤ (2 ^ 19 * CM + 1) * ‖zc - Q‖ ^ 2 * ‖zc - Sc‖ := by
        have h2 : 2 ^ 12 * CM * ‖zc - Q‖ ^ 2 ≤ 2 ^ 19 * CM * ‖zc - Q‖ ^ 2 * ‖zc - Sc‖ := by
          have h3 : (1 / 128 : ℝ) * (2 ^ 19 * CM * ‖zc - Q‖ ^ 2)
              ≤ ‖zc - Sc‖ * (2 ^ 19 * CM * ‖zc - Q‖ ^ 2) :=
            mul_le_mul_of_nonneg_right hb.le (by positivity)
          have h4 : (1 / 128 : ℝ) * (2 ^ 19 * CM * ‖zc - Q‖ ^ 2)
              = 2 ^ 12 * CM * ‖zc - Q‖ ^ 2 := by norm_num; ring
          linarith [h3, h4]
        have h5 : 2 ^ 19 * CM * ‖zc - Q‖ ^ 2 * ‖zc - Sc‖
            ≤ (2 ^ 19 * CM + 1) * ‖zc - Q‖ ^ 2 * ‖zc - Sc‖ := by
          have h6 : 0 ≤ ‖zc - Q‖ ^ 2 * ‖zc - Sc‖ := mul_nonneg ha2 hb2
          nlinarith [h6, hCM]
        linarith [h2, h5]
      linarith [hA, hstep1, hstep2]
    · push_neg at ha
      have hMu : ‖Mchart ℓ d τ n zc‖ ≤ CM := hMb τ n zc hn hcast hτ hzcReg
      have hA : ‖Mnum ℓ d τ t ht‖ ≤ CM := by rw [hMn]; exact hMu
      have hab : (1 / 8 : ℝ) * (1 / 8) * (1 / 128) ≤ ‖zc - Q‖ ^ 2 * ‖zc - Sc‖ := by
        have h3 : (1 / 8 : ℝ) * (1 / 8) ≤ ‖zc - Q‖ ^ 2 := by
          rw [pow_two]; exact mul_le_mul ha ha (by norm_num) (norm_nonneg _)
        exact mul_le_mul h3 hb.le (by norm_num) ha2
      have hle : CM ≤ (2 ^ 19 * CM + 1) * ‖zc - Q‖ ^ 2 * ‖zc - Sc‖ := by
        have h7 : (2 ^ 19 * CM + 1) * ((1 / 8 : ℝ) * (1 / 8) * (1 / 128))
            ≤ (2 ^ 19 * CM + 1) * (‖zc - Q‖ ^ 2 * ‖zc - Sc‖) :=
          mul_le_mul_of_nonneg_left hab (by positivity)
        have h8 : (2 ^ 19 * CM + 1) * ((1 / 8 : ℝ) * (1 / 8) * (1 / 128))
            = 2 ^ 6 * CM + 1 / 8192 := by norm_num; ring
        nlinarith [h7, h8, hCM]
      linarith [hA, hle]

end Work.HFN.BlLow
