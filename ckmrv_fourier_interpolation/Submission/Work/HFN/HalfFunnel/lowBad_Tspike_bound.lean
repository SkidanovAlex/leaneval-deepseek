import Mathlib
import Submission.Work.Asymptotics.HalfFunnel.lowBadTspike_defs
import Submission.Work.HFN.HalfFunnel.lowBadAux
import Submission.Work.Asymptotics.Kaxis_local_coincidence
import Submission.Work.Asymptotics.Kaxis_principal_part_bound
import Submission.Work.Asymptotics.orbit_imagAxis_of_mem_DomainD
import Submission.Work.Asymptotics.jInvariantFun_eq_smul_of_eq
import Submission.Work.Asymptotics.MiddleRange.exists_j_sub_lower_lambda_near_I
import Submission.Work.Asymptotics.MiddleRange.exists_lambdaFun_lipschitz
import Submission.Work.Asymptotics.jDiff_lower_imagAxis
import Submission.Work.Asymptotics.Kfun_principal_part_z_lip
import Submission.Work.Rigidity.LambdaAnharmonic
import Submission.Work.Residues.KernelPoleLocation

/-!
# The spike bound for the bad-line region

This file proves `Work.Asymptotics.HalfFunnel.lowBad_Tspike_bound`: on the bad-line region
`lowBadSet` and inside the spike window `|t - Im τ| ≤ 1/8`, the CKMRV kernel on the imaginary
axis differs from its translate pole by a bounded amount, uniformly in `τ` and `t`.

The proof writes the difference as `-M / ((j z - j z₀)(z - z₀))` with the same pole `z₀ = τ - n`,
`n = tsign τ`, and bounds the two factors separately:

* the two-branch lower bound `‖j z - j z₀‖ ≥ c ‖z - z₀‖‖z - S z₀‖`
  (`Work.Asymptotics.HalfFunnel.jBranch_lower`), and
* the corresponding upper bound for the numerator `M`
  (`Work.Asymptotics.HalfFunnel.M_bound_region`).
-/

noncomputable section

set_option maxHeartbeats 4000000

open MeasureTheory UpperHalfPlane

namespace Work.HFN.HalfFunnel
open Work.Asymptotics Work.Asymptotics.HalfFunnel  -- ck-hfn-fix: fork moved out of Work.Asymptotics

open Work.Kernels

/-! ## 1. The pole location and the window -/

lemma zpole_coe (τ : ℍ) : ((zpole τ : ℍ) : ℂ) = (τ : ℂ) - (tsign τ : ℂ) := by
  rw [zpole, UpperHalfPlane.coe_vadd]
  push_cast
  ring

lemma zpole_re (τ : ℍ) : (zpole τ).re = τ.re - tsign τ := by
  rw [← UpperHalfPlane.coe_re, zpole_coe, Complex.sub_re, UpperHalfPlane.coe_re,
    Complex.ofReal_re]

lemma zpole_im (τ : ℍ) : (zpole τ).im = τ.im := by
  rw [← UpperHalfPlane.coe_im, zpole_coe, Complex.sub_im, UpperHalfPlane.coe_im,
    Complex.ofReal_im, sub_zero]

lemma tsign_eq_one_or_neg_one (τ : ℍ) : tsign τ = 1 ∨ tsign τ = -1 := by
  unfold tsign
  split <;> simp

lemma tsign_eq_one_iff (τ : ℍ) : tsign τ = 1 ↔ 0 < τ.re := by
  unfold tsign
  constructor
  · intro h
    by_contra hc
    rw [if_neg hc] at h
    norm_num at h
  · intro h; rw [if_pos h]

lemma tsign_eq_neg_one_iff (τ : ℍ) : tsign τ = -1 ↔ τ.re ≤ 0 := by
  unfold tsign
  constructor
  · intro h
    by_contra hc
    rw [if_pos (lt_of_not_ge hc)] at h
    norm_num at h
  · intro h
    rw [if_neg (not_lt.mpr h)]

lemma intCast_tsign (τ : ℍ) : ∃ n : ℤ, (n = 1 ∨ n = -1) ∧ (tsign τ : ℂ) = (n : ℂ) := by
  rcases tsign_eq_one_or_neg_one τ with h | h
  · exact ⟨1, Or.inl rfl, by rw [h]; norm_num⟩
  · exact ⟨-1, Or.inr rfl, by rw [h]; norm_num⟩

/-! ## 2. The basic bounds on the region and the window -/

lemma lowBadSet_re_abs_bounds {τ : ℍ} (hτ : lowBadSet τ) : 3 / 4 < |τ.re| ∧ |τ.re| < 1 := by
  obtain ⟨hD, -, -, hre⟩ := hτ
  have h1 : -1 < τ.re := hD.1
  have h2 : τ.re < 1 := hD.2.1
  refine ⟨?_, ?_⟩
  · rcases hre with h | h
    · rw [abs_of_pos (by linarith)]; exact h
    · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_lt]; exact ⟨h1, h2⟩

lemma lowBadSet_im_bounds {τ : ℍ} (hτ : lowBadSet τ) : 1 / 2 ≤ τ.im ∧ τ.im ≤ 2 :=
  ⟨hτ.2.1, hτ.2.2.1⟩

/-- On the bad-line region, `zpole τ = τ - tsign τ` has real part in `(-1/4, 1/4)`, hence a
nonzero real part. -/
lemma zpole_re_abs_lt {τ : ℍ} (hτ : lowBadSet τ) : |(zpole τ).re| < 1 / 4 := by
  obtain ⟨h34, h1⟩ := lowBadSet_re_abs_bounds hτ
  have hlt : τ.re < 1 := (abs_lt.mp h1).2
  have hgt : -1 < τ.re := (abs_lt.mp h1).1
  rw [zpole_re]
  rcases lt_or_ge 0 τ.re with hpos | hneg
  · rw [(tsign_eq_one_iff τ).mpr hpos]
    have h34' : 3 / 4 < τ.re := by
      rw [abs_of_pos hpos] at h34; exact h34
    rw [abs_lt]
    constructor <;> linarith
  · rw [(tsign_eq_neg_one_iff τ).mpr hneg]
    have hneg' : τ.re < -(3 / 4) := by
      rcases hτ.2.2.2 with h | h
      · exact absurd h (by linarith)
      · exact h
    rw [abs_lt]
    constructor <;> linarith

lemma zpole_re_ne_zero {τ : ℍ} (hτ : lowBadSet τ) : (zpole τ).re ≠ 0 := by
  obtain ⟨-, h1⟩ := lowBadSet_re_abs_bounds hτ
  have hlt : τ.re < 1 := (abs_lt.mp h1).2
  have hgt : -1 < τ.re := (abs_lt.mp h1).1
  rw [zpole_re]
  rcases lt_or_ge 0 τ.re with hpos | hneg
  · rw [(tsign_eq_one_iff τ).mpr hpos]
    linarith
  · rw [(tsign_eq_neg_one_iff τ).mpr hneg]
    linarith

lemma zpole_im_bounds {τ : ℍ} (hτ : lowBadSet τ) : 1 / 2 ≤ (zpole τ).im ∧ (zpole τ).im ≤ 2 := by
  rw [zpole_im]
  exact lowBadSet_im_bounds hτ

/-- The pole location `zpole τ` lies in the CKMRV fundamental domain `𝒟` whenever
`τ ∈ lowBadSet`. -/
lemma zpole_mem_DomainD {τ : ℍ} (hτ : lowBadSet τ) : zpole τ ∈ DomainD := by
  have hre := zpole_re_abs_lt hτ
  have him := zpole_im_bounds hτ
  have hre' := abs_lt.mp hre
  refine ⟨by linarith [hre'.1], by linarith [hre'.2], ?_, ?_⟩
  · have hsq : ((1 / 2 : ℝ)) ^ 2 < ‖((zpole τ : ℍ) : ℂ) - (1 / 2 : ℂ)‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      have h1 : (((zpole τ : ℍ) : ℂ) - (1 / 2 : ℂ)).re = (zpole τ).re - 1 / 2 := by
        rw [Complex.sub_re, UpperHalfPlane.coe_re]; simp
      have h2 : (((zpole τ : ℍ) : ℂ) - (1 / 2 : ℂ)).im = (zpole τ).im := by
        rw [Complex.sub_im, UpperHalfPlane.coe_im]; simp
      rw [h1, h2]
      nlinarith [hre'.1, hre'.2, him.1, sq_nonneg ((zpole τ).re - 1 / 2)]
    nlinarith [norm_nonneg (((zpole τ : ℍ) : ℂ) - (1 / 2 : ℂ))]
  · have hsq : ((1 / 2 : ℝ)) ^ 2 < ‖((zpole τ : ℍ) : ℂ) + (1 / 2 : ℂ)‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      have h1 : (((zpole τ : ℍ) : ℂ) + (1 / 2 : ℂ)).re = (zpole τ).re + 1 / 2 := by
        rw [Complex.add_re, UpperHalfPlane.coe_re]; simp
      have h2 : (((zpole τ : ℍ) : ℂ) + (1 / 2 : ℂ)).im = (zpole τ).im := by
        rw [Complex.add_im, UpperHalfPlane.coe_im]; simp
      rw [h1, h2]
      nlinarith [hre'.1, hre'.2, him.1, sq_nonneg ((zpole τ).re + 1 / 2)]
    nlinarith [norm_nonneg (((zpole τ : ℍ) : ℂ) + (1 / 2 : ℂ))]

lemma coe_imagAxis (t : ℝ) (ht : 0 < t) : ((imagAxis t ht : ℍ) : ℂ) = (t : ℂ) * Complex.I := rfl

private lemma imagAxis_re (t : ℝ) (ht : 0 < t) : (imagAxis t ht).re = 0 := by
  rw [← UpperHalfPlane.coe_re, coe_imagAxis]; simp

lemma imagAxis_im (t : ℝ) (ht : 0 < t) : (imagAxis t ht).im = t := by
  rw [← UpperHalfPlane.coe_im, coe_imagAxis]; simp

lemma window_bounds {τ : ℍ} {t : ℝ} (hτ : lowBadSet τ) (ht : 0 < t)
    (hw : |t - τ.im| ≤ 1 / 8) : 3 / 8 ≤ t ∧ t ≤ 17 / 8 := by
  obtain ⟨h1, h2⟩ := lowBadSet_im_bounds hτ
  have := abs_le.mp hw
  constructor <;> linarith

lemma norm_zpole_sub_imagAxis_le {τ : ℍ} {t : ℝ} (hτ : lowBadSet τ) (ht : 0 < t)
    (hw : |t - τ.im| ≤ 1 / 8) :
    ‖((zpole τ : ℍ) : ℂ) - ((imagAxis t ht : ℍ) : ℂ)‖ ≤ 3 / 8 := by
  have h1 : (((zpole τ : ℍ) : ℂ) - ((imagAxis t ht : ℍ) : ℂ))
      = (((zpole τ).re : ℝ) : ℂ) + (((zpole τ).im - t : ℝ) : ℂ) * Complex.I := by
    rw [coe_imagAxis]
    apply Complex.ext <;>
      simp [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.mul_re,
        Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
        UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] <;> ring
  rw [h1]
  refine le_trans (norm_le_re_im _ _) ?_
  have h2 : (zpole τ).im = τ.im := zpole_im τ
  rw [h2]
  have h3 : |τ.im - t| ≤ 1 / 8 := by
    rw [abs_sub_comm]; exact hw
  have h4 := abs_le.mp h3
  have h5 : |(zpole τ).re| ≤ 1 / 4 := le_of_lt (zpole_re_abs_lt hτ)
  linarith


/-! ## 3. The pole location is `j`-equivalent to `τ` -/

lemma tsign_eq_intCast (τ : ℍ) : ∃ n : ℤ, (n = 1 ∨ n = -1) ∧ (tsign τ : ℝ) = (n : ℝ) := by
  rcases tsign_eq_one_or_neg_one τ with h | h
  · exact ⟨1, Or.inl rfl, by rw [h]; norm_num⟩
  · exact ⟨-1, Or.inr rfl, by rw [h]; norm_num⟩

lemma zpole_eq_vadd (τ : ℍ) :
    ∃ n : ℤ, (n = 1 ∨ n = -1) ∧ zpole τ = (-(n : ℝ)) +ᵥ τ := by
  obtain ⟨n, hn, h⟩ := tsign_eq_intCast τ
  exact ⟨n, hn, by rw [zpole, h]⟩

lemma zpole_jInvariantFun (τ : ℍ) : jInvariantFun (zpole τ) = jInvariantFun τ := by
  obtain ⟨n, hn, h⟩ := zpole_eq_vadd τ
  rw [h]
  exact jInvariantFun_neg_vadd τ n hn

lemma zpole_coe_eq (τ : ℍ) {n : ℤ} (hn : (tsign τ : ℝ) = (n : ℝ)) :
    ((zpole τ : ℍ) : ℂ) = (τ : ℂ) - (n : ℂ) := by
  rw [zpole_coe]
  have : (tsign τ : ℂ) = (n : ℂ) := by rw [hn]; push_cast; ring
  rw [this]

/-! ## 4. No coincidence with the imaginary axis on the bad-line region -/

lemma jInvariantFun_zpole_ne_imagAxis {τ : ℍ} (hτ : lowBadSet τ) (t : ℝ) (ht : 0 < t) :
    jInvariantFun (zpole τ) ≠ jInvariantFun (imagAxis t ht) := by
  intro hcoin
  have hcoin' : jInvariantFun τ = jInvariantFun (imagAxis t ht) := by
    rw [← zpole_jInvariantFun τ]; exact hcoin
  obtain ⟨γ, hγ⟩ := jInvariantFun_eq_smul_of_eq hcoin'
  have hτD : τ ∈ DomainD := hτ.1
  have hγinv : γ⁻¹ • τ = imagAxis t ht := by
    rw [← hγ, ← mul_smul]; simp
  have hre : ((γ⁻¹ • τ : ℍ) : ℂ).re = 0 := by
    rw [hγinv, coe_imagAxis]; simp
  have hzero := orbit_imagAxis_of_mem_DomainD τ hτD γ⁻¹ hre
  have h34 := (lowBadSet_re_abs_bounds hτ).1
  rw [hzero, abs_zero] at h34
  norm_num at h34

/-! ## 5. The translate pole in denominator form -/

lemma tpole_eq_pole (τ : ℍ) (t : ℝ) (ht : 0 < t) :
    tpole τ t = ((tsign τ : ℂ) / (2 * (Real.pi : ℂ)))
      * ((((imagAxis t ht : ℍ) : ℂ) - ((zpole τ : ℍ) : ℂ)))⁻¹ := by
  rw [tpole, div_eq_mul_inv, div_eq_mul_inv, coe_imagAxis, zpole_coe]

lemma Kaxis_eq_Kfun (ℓ : LogLambdaData) (d : ℕ) {τ : ℍ} {t : ℝ} (ht : 0 < t) :
    Kaxis (Kfun ℓ d) τ t = Kfun ℓ d τ (imagAxis t ht) := by
  rw [Kaxis, dif_pos ht]

/-! ## 6. The numerator identity -/

lemma Kfun_sub_tpole_eq (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) {τ : ℍ} {t : ℝ}
    (ht : 0 < t) (hne : jInvariantFun (imagAxis t ht) ≠ jInvariantFun (zpole τ)) :
    Kfun ℓ d τ (imagAxis t ht) - tpole τ t
      = - Mnum ℓ d τ t ht
        / ((jInvariantFun (imagAxis t ht) - jInvariantFun (zpole τ))
            * (((imagAxis t ht : ℍ) : ℂ) - ((zpole τ : ℍ) : ℂ))) := by
  obtain ⟨n, hn, hcast⟩ := tsign_eq_intCast τ
  have hzp : zpole τ = (-(n : ℝ)) +ᵥ τ := by rw [zpole, hcast]
  have hzc : (tsign τ : ℂ) = (n : ℂ) := by rw [hcast]; push_cast; ring
  have hcoe : ((zpole τ : ℍ) : ℂ) = (τ : ℂ) - (n : ℂ) := zpole_coe_eq τ hcast
  have hne' : jInvariantFun (imagAxis t ht) ≠ jInvariantFun (((-(n : ℝ)) +ᵥ τ : ℍ)) := by
    rw [← hzp]; exact hne
  have hrem := remainder_eq ℓ d hd τ (imagAxis t ht) n hn hne'
  rw [← hzp, hcoe] at hrem
  rw [tpole_eq_pole τ t ht]
  unfold Mnum
  rw [hcoe, hzc]
  rw [hrem]



/-! ## 7. Uniform bounds on the extended region

The analytic inputs about the numerator `Mnum` need the functions `AfunFun` and `j` to be
uniformly bounded on a fixed region containing the pole `z₀`, the second branch `S z₀`, the
contour point `it` and small discs around them. -/

/-- A bounded region of the complex plane containing all configuration points of the
bad-line spike problem. -/
def spikeRegC : Set ℂ := {u : ℂ | |u.re| ≤ 2 ∧ 1 / 32 ≤ u.im ∧ u.im ≤ 7 / 2}

lemma isCompact_spikeRegC : IsCompact spikeRegC := by
  have h1 : IsClosed {u : ℂ | |u.re| ≤ 2} :=
    isClosed_le (continuous_abs.comp Complex.continuous_re) continuous_const
  have h2 : IsClosed {u : ℂ | (1:ℝ) / 32 ≤ u.im} :=
    isClosed_le continuous_const Complex.continuous_im
  have h3 : IsClosed {u : ℂ | u.im ≤ (7:ℝ) / 2} :=
    isClosed_le Complex.continuous_im continuous_const
  have heq : spikeRegC = {u : ℂ | |u.re| ≤ 2} ∩ {u : ℂ | (1:ℝ) / 32 ≤ u.im}
      ∩ {u : ℂ | u.im ≤ (7:ℝ) / 2} := by
    ext u
    constructor
    · intro h; exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩
    · intro h; exact ⟨h.1.1, h.1.2, h.2⟩
  have hclosed : IsClosed spikeRegC := by rw [heq]; exact (h1.inter h2).inter h3
  have hball : spikeRegC ⊆ Metric.closedBall (0:ℂ) 5 := by
    intro u hu
    obtain ⟨hre, him1, him2⟩ := hu
    rw [Metric.mem_closedBall, dist_zero_right]
    have h1 : ‖u‖ ^ 2 = u.re ^ 2 + u.im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
    have h2 : u.re ^ 2 ≤ 4 := by nlinarith [abs_le.mp hre, sq_nonneg u.re]
    have h3 : u.im ^ 2 ≤ (7 / 2 : ℝ) ^ 2 := by nlinarith [him1, him2]
    have h4 : ‖u‖ ^ 2 ≤ 25 := by rw [h1]; nlinarith
    nlinarith [norm_nonneg u]
  exact Metric.isCompact_iff_isClosed_bounded.mpr
    ⟨hclosed, Metric.isBounded_closedBall.subset hball⟩

lemma spikeRegC_norm_le {u : ℂ} (hu : u ∈ spikeRegC) : ‖u‖ ≤ 5 := by
  obtain ⟨hre, him1, him2⟩ := hu
  have hsq : ‖u‖ ^ 2 = u.re ^ 2 + u.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  have h2 : u.re ^ 2 ≤ 4 := by nlinarith [abs_le.mp hre, sq_nonneg u.re]
  have h3 : u.im ^ 2 ≤ (7 / 2 : ℝ) ^ 2 := by nlinarith [him1, him2]
  have h4 : ‖u‖ ^ 2 ≤ 25 := by rw [hsq]; nlinarith
  nlinarith [norm_nonneg u]

lemma spikeRegC_im_pos {u : ℂ} (hu : u ∈ spikeRegC) : 0 < u.im := by
  have := hu.2.1
  linarith

lemma continuousOn_ofComplex_spikeRegC :
    ContinuousOn (fun u : ℂ => UpperHalfPlane.ofComplex u) spikeRegC := by
  apply continuousOn_ofComplex_im_pos.mono
  intro u hu
  have h := hu.2.1
  show 0 < u.im
  linarith

/-- Uniform bound for `AfunFun` on the extended region. -/
lemma exists_bound_AfunFun_spike (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ w : ℍ), ((τ : ℂ) ∈ spikeRegC) → ((w : ℂ) ∈ spikeRegC) →
      ‖AfunFun ℓ d τ w‖ ≤ C := by
  obtain ⟨C₀, hC₀⟩ := (isCompact_spikeRegC.prod isCompact_spikeRegC).exists_bound_of_continuousOn
    ((continuous_AfunFun ℓ d).continuousOn.comp
      ((continuousOn_ofComplex_spikeRegC.comp continuous_fst.continuousOn
          (fun p hp => hp.1)).prodMk
        (continuousOn_ofComplex_spikeRegC.comp continuous_snd.continuousOn
          (fun p hp => hp.2)))
      (fun p _ => Set.mem_univ _))
  refine ⟨max C₀ 0, le_max_right _ _, fun τ w hτ hw => ?_⟩
  have h1 : ‖AfunFun ℓ d τ w‖
      = ‖AfunFun ℓ d (UpperHalfPlane.ofComplex (τ : ℂ)) (UpperHalfPlane.ofComplex (w : ℂ))‖ := by
    rw [UpperHalfPlane.ofComplex_apply, UpperHalfPlane.ofComplex_apply]
  rw [h1]
  exact le_trans (hC₀ ((τ : ℂ), (w : ℂ)) ⟨hτ, hw⟩) (le_max_left _ _)

/-- Uniform bound for `j` on the extended region. -/
lemma exists_bound_jInvariantFun_spike :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℍ, ((w : ℂ) ∈ spikeRegC) → ‖jInvariantFun w‖ ≤ C := by
  obtain ⟨C₀, hC₀⟩ := isCompact_spikeRegC.exists_bound_of_continuousOn
    (Work.Residues.continuous_jInvariantFun.continuousOn.comp continuousOn_ofComplex_spikeRegC
      (fun _ _ => Set.mem_univ _))
  refine ⟨max C₀ 0, le_max_right _ _, fun w hw => ?_⟩
  have h1 : ‖jInvariantFun w‖ = ‖jInvariantFun (UpperHalfPlane.ofComplex (w : ℂ))‖ := by
    rw [UpperHalfPlane.ofComplex_apply]
  rw [h1]
  exact le_trans (hC₀ (w : ℂ) hw) (le_max_left _ _)

/-! ## 7b. The geometry of the two branches -/

lemma tau_mem_spikeRegC {τ : ℍ} (hτ : lowBadSet τ) : ((τ : ℍ) : ℂ) ∈ spikeRegC := by
  obtain ⟨hre34, hre1⟩ := lowBadSet_re_abs_bounds hτ
  obtain ⟨him1, him2⟩ := lowBadSet_im_bounds hτ
  have him1' : (1 : ℝ) / 32 ≤ ((τ : ℍ) : ℂ).im := by
    rw [UpperHalfPlane.coe_im]; linarith
  have him2' : ((τ : ℍ) : ℂ).im ≤ 7 / 2 := by
    rw [UpperHalfPlane.coe_im]; linarith
  have hre' : |((τ : ℍ) : ℂ).re| ≤ 2 := by
    rw [UpperHalfPlane.coe_re, abs_le]
    exact ⟨by linarith [(abs_lt.mp hre1).1], by linarith [(abs_lt.mp hre1).2]⟩
  exact ⟨hre', him1', him2'⟩

lemma zpole_mem_spikeRegC {τ : ℍ} (hτ : lowBadSet τ) : ((zpole τ : ℍ) : ℂ) ∈ spikeRegC := by
  have hzre := abs_lt.mp (zpole_re_abs_lt hτ)
  have hzim : ((zpole τ : ℍ) : ℂ).im = τ.im := by
    rw [UpperHalfPlane.coe_im, zpole_im]
  obtain ⟨him1, him2⟩ := lowBadSet_im_bounds hτ
  have him1' : (1 : ℝ) / 32 ≤ ((zpole τ : ℍ) : ℂ).im := by rw [hzim]; linarith
  have him2' : ((zpole τ : ℍ) : ℂ).im ≤ 7 / 2 := by rw [hzim]; linarith
  have hre' : |((zpole τ : ℍ) : ℂ).re| ≤ 2 := by
    rw [UpperHalfPlane.coe_re, abs_le]
    exact ⟨by linarith [hzre.1], by linarith [hzre.2]⟩
  exact ⟨hre', him1', him2'⟩

lemma imagAxis_mem_spikeRegC {τ : ℍ} {t : ℝ} (hτ : lowBadSet τ) (ht : 0 < t)
    (hw : |t - τ.im| ≤ 1 / 8) : ((imagAxis t ht : ℍ) : ℂ) ∈ spikeRegC := by
  obtain ⟨hb1, hb2⟩ := window_bounds hτ ht hw
  rw [coe_imagAxis]
  have him : ((t : ℂ) * Complex.I).im = t := by simp
  have hre : ((t : ℂ) * Complex.I).re = 0 := by simp
  exact ⟨by rw [hre]; norm_num, by rw [him]; linarith, by rw [him]; linarith⟩

lemma Szpole_mem_spikeRegC {τ : ℍ} (hτ : lowBadSet τ) :
    ((ModularGroup.S • zpole τ : ℍ) : ℂ) ∈ spikeRegC := by
  have hzre := abs_lt.mp (zpole_re_abs_lt hτ)
  have hzim : (zpole τ).im = τ.im := zpole_im τ
  obtain ⟨him1, him2⟩ := lowBadSet_im_bounds hτ
  have hisim : (ModularGroup.S • zpole τ).im = (zpole τ).im / ‖((zpole τ : ℍ) : ℂ)‖ ^ 2 :=
    KL.im_S (zpole τ)
  have hinorm : ‖((zpole τ : ℍ) : ℂ)‖ ^ 2 = (zpole τ).re ^ 2 + (zpole τ).im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    ring
  have hreS : (ModularGroup.S • zpole τ).re = (-(zpole τ).re) / ‖((zpole τ : ℍ) : ℂ)‖ ^ 2 := by
    have hcoe : ((ModularGroup.S • zpole τ : ℍ) : ℂ) = -(((zpole τ : ℍ) : ℂ))⁻¹ :=
      Work.Rigidity.coe_S_smul (zpole τ)
    have h2 : ((((zpole τ : ℍ) : ℂ))⁻¹).re = (zpole τ).re / ‖((zpole τ : ℍ) : ℂ)‖ ^ 2 := by
      rw [Complex.inv_re, Complex.normSq_eq_norm_sq, UpperHalfPlane.coe_re]
    rw [← UpperHalfPlane.coe_re, hcoe, Complex.neg_re, h2, neg_div]
  have hnorm2 : (1 / 4 : ℝ) ≤ ‖((zpole τ : ℍ) : ℂ)‖ ^ 2 := by
    nlinarith [hinorm, hzim, him1]
  have hpos : 0 < ‖((zpole τ : ℍ) : ℂ)‖ ^ 2 := by linarith
  have hre_hi : (ModularGroup.S • zpole τ).re ≤ 2 := by
    rw [hreS, div_le_iff₀ hpos]
    nlinarith [hzre.2, hnorm2]
  have hre_lo : -2 ≤ (ModularGroup.S • zpole τ).re := by
    rw [hreS, le_div_iff₀ hpos]
    nlinarith [hzre.1, hnorm2]
  have hre2 : (zpole τ).re ^ 2 ≤ 1 / 16 := by
    nlinarith [sq_nonneg ((zpole τ).re - 1 / 4), sq_nonneg ((zpole τ).re + 1 / 4), hzre.1, hzre.2]
  have himsq : (zpole τ).im ^ 2 ≤ 2 * (zpole τ).im := by
    nlinarith [hzim, him1, him2, sq_nonneg ((zpole τ).im - 1)]
  have himpos : (1 : ℝ) / 2 ≤ (zpole τ).im := by rw [hzim]; exact him1
  have him1' : (1 : ℝ) / 32 ≤ ((ModularGroup.S • zpole τ : ℍ) : ℂ).im := by
    rw [UpperHalfPlane.coe_im, hisim, le_div_iff₀ hpos]
    have hz : ‖((zpole τ : ℍ) : ℂ)‖ ^ 2 ≤ 1 / 16 + 2 * (zpole τ).im := by linarith [hinorm, hre2, himsq]
    nlinarith [hz, himpos]
  have him2' : ((ModularGroup.S • zpole τ : ℍ) : ℂ).im ≤ 7 / 2 := by
    rw [UpperHalfPlane.coe_im, hisim, div_le_iff₀ hpos, hinorm]
    nlinarith [himpos, hre2, sq_nonneg (zpole τ).im]
  have hre' : |((ModularGroup.S • zpole τ : ℍ) : ℂ).re| ≤ 2 := by
    rw [UpperHalfPlane.coe_re, abs_le]
    exact ⟨hre_lo, hre_hi⟩
  exact ⟨hre', him1', him2'⟩


lemma spikeRegC_of_norm_sub_le {p u : ℂ} {r : ℝ} (hre : |p.re| + r ≤ 2)
    (him1 : 1 / 32 ≤ p.im - r) (him2 : p.im + r ≤ 7 / 2) (h : ‖u - p‖ ≤ r) :
    u ∈ spikeRegC := by
  have hrep : u.re = p.re + (u - p).re := by simp [Complex.sub_re]
  have himp : u.im = p.im + (u - p).im := by simp [Complex.sub_im]
  have hr : |(u - p).re| ≤ r := le_trans (Complex.abs_re_le_norm (u - p)) h
  have hi : |(u - p).im| ≤ r := le_trans (Complex.abs_im_le_norm (u - p)) h
  have hi1 : -r ≤ (u - p).im := (abs_le.mp hi).1
  have hi2 : (u - p).im ≤ r := (abs_le.mp hi).2
  refine ⟨?_, ?_, ?_⟩
  · rw [hrep]; linarith [abs_add_le p.re (u - p).re, hre]
  · rw [himp]; linarith [hi1, him1]
  · rw [himp]; linarith [hi2, him2]

lemma Szpole_re_abs_le_one {τ : ℍ} (hτ : lowBadSet τ) :
    |((ModularGroup.S • zpole τ : ℍ) : ℂ).re| ≤ 1 := by
  have hcoe : ((ModularGroup.S • zpole τ : ℍ) : ℂ) = -(((zpole τ : ℍ) : ℂ))⁻¹ :=
    Work.Rigidity.coe_S_smul (zpole τ)
  have hzre := abs_lt.mp (zpole_re_abs_lt hτ)
  have hzim : (zpole τ).im = τ.im := zpole_im τ
  obtain ⟨him1, him2⟩ := lowBadSet_im_bounds hτ
  have hnorm2 : (1 / 4 : ℝ) ≤ ‖((zpole τ : ℍ) : ℂ)‖ ^ 2 := by
    have hsq : ‖((zpole τ : ℍ) : ℂ)‖ ^ 2 = (zpole τ).re ^ 2 + (zpole τ).im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      simp only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]; ring
    rw [hsq, hzim]; nlinarith
  rw [hcoe, Complex.neg_re, Complex.inv_re, Complex.normSq_eq_norm_sq,
    UpperHalfPlane.coe_re, abs_neg, abs_div]
  rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖((zpole τ : ℍ) : ℂ)‖ ^ 2)]
  rw [div_le_one (by positivity : (0:ℝ) < ‖((zpole τ : ℍ) : ℂ)‖ ^ 2)]
  have h1 : |(zpole τ).re| < 1 / 4 := abs_lt.mpr hzre
  linarith [hnorm2, h1]

lemma Szpole_im_bounds {τ : ℍ} (hτ : lowBadSet τ) :
    1 / 16 ≤ ((ModularGroup.S • zpole τ : ℍ) : ℂ).im
      ∧ ((ModularGroup.S • zpole τ : ℍ) : ℂ).im ≤ 2 := by
  have hcoe : ((ModularGroup.S • zpole τ : ℍ) : ℂ) = -(((zpole τ : ℍ) : ℂ))⁻¹ :=
    Work.Rigidity.coe_S_smul (zpole τ)
  have hzre := abs_lt.mp (zpole_re_abs_lt hτ)
  have hzim : (zpole τ).im = τ.im := zpole_im τ
  obtain ⟨him1, him2⟩ := lowBadSet_im_bounds hτ
  have hsq : ‖((zpole τ : ℍ) : ℂ)‖ ^ 2 = (zpole τ).re ^ 2 + (zpole τ).im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]; ring
  have himval : ((ModularGroup.S • zpole τ : ℍ) : ℂ).im
      = (zpole τ).im / ‖((zpole τ : ℍ) : ℂ)‖ ^ 2 := by
    rw [hcoe, Complex.neg_im, Complex.inv_im, Complex.normSq_eq_norm_sq,
      UpperHalfPlane.coe_im]
    ring
  have hnorm2le : ‖((zpole τ : ℍ) : ℂ)‖ ^ 2 ≤ 65 / 16 := by
    rw [hsq, hzim]; nlinarith [sq_nonneg ((zpole τ).re), sq_nonneg ((zpole τ).im)]
  have hnorm2pos : 0 < ‖((zpole τ : ℍ) : ℂ)‖ ^ 2 := by
    rw [hsq, hzim]; nlinarith
  constructor
  · rw [himval, le_div_iff₀ hnorm2pos]
    nlinarith [hnorm2le, him1]
  · rw [himval, div_le_iff₀ hnorm2pos, hsq, hzim]
    nlinarith [him1, sq_nonneg ((zpole τ).re), sq_nonneg ((zpole τ).im)]

lemma zpole_ball_spikeRegC {τ : ℍ} (hτ : lowBadSet τ) {u : ℂ}
    (h : ‖u - ((zpole τ : ℍ) : ℂ)‖ ≤ 1 / 8) : u ∈ spikeRegC := by
  have ha : |((zpole τ : ℍ) : ℂ).re| ≤ 1 / 4 := by
    rw [UpperHalfPlane.coe_re]; exact le_of_lt (zpole_re_abs_lt hτ)
  have hb : (1 : ℝ) / 2 ≤ ((zpole τ : ℍ) : ℂ).im := by
    rw [UpperHalfPlane.coe_im, zpole_im]; exact (lowBadSet_im_bounds hτ).1
  have hc : ((zpole τ : ℍ) : ℂ).im ≤ 2 := by
    rw [UpperHalfPlane.coe_im, zpole_im]; exact (lowBadSet_im_bounds hτ).2
  exact spikeRegC_of_norm_sub_le (by linarith) (by linarith) (by linarith) h

lemma Szpole_ball_spikeRegC {τ : ℍ} (hτ : lowBadSet τ) {u : ℂ}
    (h : ‖u - ((ModularGroup.S • zpole τ : ℍ) : ℂ)‖ ≤ 1 / 32) : u ∈ spikeRegC :=
  spikeRegC_of_norm_sub_le
    (by linarith [Szpole_re_abs_le_one hτ])
    (by linarith [(Szpole_im_bounds hτ).1])
    (by linarith [(Szpole_im_bounds hτ).2]) h

lemma Mchart_S_zero (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (n : ℤ) (hn : n = 1 ∨ n = -1) (σ : ℍ) :
    Mchart ℓ d ((n : ℝ) +ᵥ σ) n ((ModularGroup.S • σ : ℍ) : ℂ) = 0 := by
  rw [Mchart_ofComplex]
  have h1 : ((((n : ℝ) +ᵥ σ : ℍ)) : ℂ) = (n : ℂ) + (σ : ℂ) := by
    rw [UpperHalfPlane.coe_vadd]; push_cast; ring
  have h2 : (-(n : ℝ)) +ᵥ ((n : ℝ) +ᵥ σ) = σ := by
    rw [← add_vadd, neg_add_cancel, zero_vadd]
  have h3 : (n : ℂ) + (σ : ℂ) - (n : ℂ) = (σ : ℂ) := by ring
  rw [h1, h2, h3, KernelFacts.jInvariantFun_S_smul, sub_self, mul_zero, add_zero,
    AfunFun_S_vadd_zero ℓ d hd n hn σ, zero_mul]

/-! ## 8a. The numerator in the `ℂ` chart -/

lemma Mnum_eq_Mchart (ℓ : LogLambdaData) (d : ℕ) {τ : ℍ} {t : ℝ} (ht : 0 < t)
    {n : ℤ} (hn : (tsign τ : ℝ) = (n : ℝ)) :
    Mnum ℓ d τ t ht = Mchart ℓ d τ n ((t : ℂ) * Complex.I) := by
  have h2 : ((imagAxis t ht : ℍ) : ℂ) = (t : ℂ) * Complex.I := coe_imagAxis t ht
  have h5 : UpperHalfPlane.ofComplex ((t : ℂ) * Complex.I) = imagAxis t ht := by
    rw [← h2]
    exact UpperHalfPlane.ofComplex_apply _
  have h3 : ((zpole τ : ℍ) : ℂ) = (τ : ℂ) - (n : ℂ) := zpole_coe_eq τ hn
  have h4 : (-(n : ℝ)) +ᵥ τ = zpole τ := by
    rw [zpole]
    rw [hn]
  have h1 : ((n : ℂ)) = (tsign τ : ℂ) := by rw [hn]; push_cast; ring
  unfold Mnum Mchart
  rw [h3, h4, h1, h5, h2]

/-- Uniform bound for `Mchart` on the extended region: the pole location is `z₀ = τ - n`, and
both `AfunFun` (in both variables) and `j` are uniformly bounded on `spikeRegC`, while the
translate `-(n:ℝ) +ᵥ τ` is `j`-equivalent to `τ`. -/
lemma Mchart_bound_region (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : ℍ) (n : ℤ) (u : ℂ), (n = 1 ∨ n = -1) →
      (tsign τ : ℝ) = (n : ℝ) → lowBadSet τ → u ∈ spikeRegC →
      ‖Mchart ℓ d τ n u‖ ≤ C := by
  obtain ⟨C_A, hC_A0, hAb⟩ := exists_bound_AfunFun_spike ℓ d hd
  obtain ⟨C_j, hC_j0, hjb⟩ := exists_bound_jInvariantFun_spike
  refine ⟨C_A * 10 + 2 * C_j, by positivity, fun τ n u hn hcast hτ hu => ?_⟩
  have huim : 0 < u.im := spikeRegC_im_pos hu
  have hcoe : ((UpperHalfPlane.ofComplex u : ℍ) : ℂ) = u := by
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos huim, UpperHalfPlane.coe_mk]
  have hA : ‖AfunFun ℓ d τ (UpperHalfPlane.ofComplex u)‖ ≤ C_A :=
    hAb τ _ (tau_mem_spikeRegC hτ) (by rw [hcoe]; exact hu)
  have hJu : ‖jInvariantFun (UpperHalfPlane.ofComplex u)‖ ≤ C_j :=
    hjb _ (by rw [hcoe]; exact hu)
  have hJz : ‖jInvariantFun ((-(n : ℝ)) +ᵥ τ)‖ ≤ C_j := by
    have h1 : (-(n : ℝ)) +ᵥ τ = zpole τ := by rw [zpole, hcast]
    rw [h1, zpole_jInvariantFun]
    exact hjb τ (tau_mem_spikeRegC hτ)
  have hdu : ‖u - ((τ : ℂ) - (n : ℂ))‖ ≤ 10 := by
    have hcoe' : ((τ : ℂ) - (n : ℂ)) ∈ spikeRegC := by
      have hthis : (-(n : ℝ)) +ᵥ τ = zpole τ := by rw [zpole, hcast]
      have h2 : (((-(n : ℝ)) +ᵥ τ : ℍ) : ℂ) = (τ : ℂ) - (n : ℂ) := by
        rw [hthis]; exact zpole_coe_eq τ hcast
      rw [← h2, hthis]
      exact zpole_mem_spikeRegC hτ
    have hle : ‖u - ((τ : ℂ) - (n : ℂ))‖ ≤ ‖u‖ + ‖((τ : ℂ) - (n : ℂ))‖ := norm_sub_le _ _
    linarith [spikeRegC_norm_le hu, spikeRegC_norm_le hcoe']
  have hcoef : ‖((n : ℂ) / (2 * (Real.pi : ℂ)))‖ ≤ 1 := by
    rw [norm_div]
    have hn1 : ‖(n : ℂ)‖ ≤ 1 := by
      rcases hn with h | h <;> rw [h] <;> norm_num
    have hden : (1 : ℝ) ≤ ‖(2 : ℂ) * (Real.pi : ℂ)‖ := by
      rw [norm_mul, Complex.norm_ofNat, Complex.norm_of_nonneg Real.pi_pos.le]
      linarith [Real.pi_gt_three]
    rw [div_le_one (by linarith : (0:ℝ) < ‖(2 : ℂ) * (Real.pi : ℂ)‖)]
    linarith
  have hMj : ‖jInvariantFun (UpperHalfPlane.ofComplex u) - jInvariantFun ((-(n : ℝ)) +ᵥ τ)‖
      ≤ 2 * C_j := by
    have h := norm_sub_le (jInvariantFun (UpperHalfPlane.ofComplex u))
      (jInvariantFun ((-(n : ℝ)) +ᵥ τ))
    linarith
  have h1 : ‖AfunFun ℓ d τ (UpperHalfPlane.ofComplex u) * (u - ((τ : ℂ) - (n : ℂ)))‖
      ≤ C_A * 10 := by
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

/-! ## 8b. The two analytic inputs of the spike bound

The two lemmas below are the analytic content: the two-branch lower bound for the `j`-difference
and the matching upper bound for the numerator `Mnum`. -/

/-! ## 8c. The lower bound for the `j`-difference on the spike region

The two-branch lower bound `jBranch_lower` is assembled here from three analytic inputs:

* `near_I_two_branch`: near the elliptic point `i` (where the two branches `z₀` and `S z₀` merge and
  `j'(i) = 0`) the two `λ`-differences `λz₀ - λ(it)` and `λ(it) - λ(S z₀)` are both comparable to
  the corresponding distances (`exists_lambdaFun_lipschitz` at `i`), and
  `exists_j_sub_lower_lambda_near_I` converts their product into `j z₀ - j it`;
* `jDiff_lower_arc`: uniformly on the compact arc `{i t : 3/8 ≤ t ≤ 17/8, |t - 1| ≥ η}` the
  `j`-difference expands distances (`jDiff_lower_imagAxis`, made uniform by a finite subcover);
* `far_two_branch`: on the compact set of configurations in which neither of the two distances
  `‖z₀ - it‖`, `‖it - S z₀‖` is small, the two-branch ratio is continuous and nonvanishing
  (`eq_or_eq_S_of_re_eq_zero` identifies the coincidence set), hence bounded below.
-/

lemma norm_S_sub_I (u : ℍ) :
    ‖((ModularGroup.S • u : ℍ) : ℂ) - Complex.I‖
      = ‖(u : ℂ) - Complex.I‖ / ‖(u : ℂ)‖ := by
  have hScoe : ((ModularGroup.S • u : ℍ) : ℂ) = -((u : ℂ))⁻¹ := Work.Rigidity.coe_S_smul u
  rw [hScoe, show -(↑u)⁻¹ - Complex.I = -((↑u)⁻¹ + Complex.I) by ring, norm_neg]
  have hne : (u : ℂ) ≠ 0 := by
    intro h
    have h2 : ((u : ℂ)).im = 0 := by rw [h]; simp
    rw [UpperHalfPlane.coe_im] at h2
    linarith [u.im_pos]
  have h1 : ((u : ℂ))⁻¹ + Complex.I
      = Complex.I * ((u : ℂ) - Complex.I) / (u : ℂ) := by
    rw [eq_div_iff hne, mul_sub, Complex.I_mul_I, add_mul, inv_mul_cancel₀ hne]
    ring
  rw [h1, norm_div, norm_mul, Complex.norm_I, one_mul]

theorem near_I_two_branch :
    ∃ δ c : ℝ, 0 < δ ∧ 0 < c ∧ ∀ u v : ℍ,
      ‖(u : ℂ) - Complex.I‖ < δ → ‖(v : ℂ) - Complex.I‖ < δ →
      c * ‖(u : ℂ) - (v : ℂ)‖ * ‖(v : ℂ) - ((ModularGroup.S • u : ℍ) : ℂ)‖
        ≤ ‖jInvariantFun u - jInvariantFun v‖ := by
  set Ih : ℍ := ⟨Complex.I, by simp⟩ with hIh
  obtain ⟨ρ₁, hρ₁, c₁, hc₁, h₁⟩ := Work.Asymptotics.MiddleRange.exists_j_sub_lower_lambda_near_I
  obtain ⟨ρ₂, hρ₂, c₂, hc₂, h₂⟩ :=
    Work.Asymptotics.MiddleRange.exists_lambdaFun_lipschitz Ih
  have hδ1 : min ρ₁ (min ρ₂ 1 / 2) ≤ ρ₁ := min_le_left _ _ 
  have hδ2 : min ρ₁ (min ρ₂ 1 / 2) ≤ ρ₂ / 2 := by
    have h := min_le_right ρ₁ (min ρ₂ 1 / 2)
    have h' := min_le_left ρ₂ (1:ℝ)
    linarith
  have hδ3 : min ρ₁ (min ρ₂ 1 / 2) ≤ 1 / 2 := by
    have h := min_le_right ρ₁ (min ρ₂ 1 / 2)
    have h' := min_le_right ρ₂ (1:ℝ)
    linarith
  refine ⟨min ρ₁ (min ρ₂ 1 / 2), c₁ * c₂ ^ 2, lt_min hρ₁ (by positivity), by positivity, ?_⟩
  intro u v hu hv
  have hu₁ : ‖(u : ℂ) - Complex.I‖ < ρ₁ := lt_of_lt_of_le hu hδ1
  have hv₁ : ‖(v : ℂ) - Complex.I‖ < ρ₁ := lt_of_lt_of_le hv hδ1
  have hu₂ : ‖(u : ℂ) - Complex.I‖ < ρ₂ := by linarith [hδ2, hu, hρ₂]
  have hv₂ : ‖(v : ℂ) - Complex.I‖ < ρ₂ := by linarith [hδ2, hv, hρ₂]
  have hu1 : ‖(u : ℂ) - Complex.I‖ < 1 := by linarith [hδ3, hu]
  have hunorm : (1 : ℝ) / 2 ≤ ‖(u : ℂ)‖ := by
    have h1 : ‖Complex.I‖ - ‖(u : ℂ)‖ ≤ ‖Complex.I - (u : ℂ)‖ := norm_sub_norm_le _ _
    rw [Complex.norm_I, norm_sub_rev] at h1
    have h2 : ‖(u : ℂ) - Complex.I‖ < (1 : ℝ) / 2 := by linarith [hu, hδ3]
    linarith
  have hunormpos : (0 : ℝ) < ‖(u : ℂ)‖ := by linarith
  have hSu : ‖((ModularGroup.S • u : ℍ) : ℂ) - Complex.I‖ < ρ₂ := by
    rw [norm_S_sub_I, div_lt_iff₀ hunormpos]
    have h1 : ‖(u : ℂ) - Complex.I‖ < ρ₂ / 2 := by linarith [hu, hδ2]
    have h2 : ρ₂ / 2 ≤ ρ₂ * ‖(u : ℂ)‖ := by
      have := mul_le_mul_of_nonneg_left hunorm hρ₂.le
      linarith
    linarith
  have h2a := h₂ u v hu₂ hv₂
  have h2b := h₂ v (ModularGroup.S • u) hv₂ hSu
  have hSlam : lambdaFun (ModularGroup.S • u) = 1 - lambdaFun u :=
    Work.Rigidity.lambdaFun_S_eq u
  have h3 : ‖lambdaFun u + lambdaFun v - 1‖
      = ‖lambdaFun v - lambdaFun (ModularGroup.S • u)‖ := by
    rw [hSlam]; congr 1; ring
  have h1 := h₁ u v hu₁ hv₁
  rw [h3] at h1
  have hA : 0 ≤ c₂ * ‖(u : ℂ) - (v : ℂ)‖ := mul_nonneg hc₂.le (norm_nonneg _)
  have hB : 0 ≤ c₂ * ‖(v : ℂ) - ((ModularGroup.S • u : ℍ) : ℂ)‖ :=
    mul_nonneg hc₂.le (norm_nonneg _)
  have step : c₁ * (c₂ * ‖(u : ℂ) - (v : ℂ)‖)
        * (c₂ * ‖(v : ℂ) - ((ModularGroup.S • u : ℍ) : ℂ)‖)
      ≤ c₁ * ‖lambdaFun u - lambdaFun v‖
        * ‖lambdaFun v - lambdaFun (ModularGroup.S • u)‖ :=
    mul_le_mul (mul_le_mul_of_nonneg_left h2a hc₁.le) h2b hB
      (by positivity)
  calc c₁ * c₂ ^ 2 * ‖(u : ℂ) - (v : ℂ)‖ * ‖(v : ℂ) - ((ModularGroup.S • u : ℍ) : ℂ)‖
      = c₁ * (c₂ * ‖(u : ℂ) - (v : ℂ)‖)
        * (c₂ * ‖(v : ℂ) - ((ModularGroup.S • u : ℍ) : ℂ)‖) := by ring
    _ ≤ ‖jInvariantFun u - jInvariantFun v‖ := le_trans step h1

private lemma min'_le' (s : Finset ℝ) (H : s.Nonempty) {x : ℝ} (hx : x ∈ s) : s.min' H ≤ x := by
  have := Finset.min'_le s x hx
  simpa using this

theorem jDiff_lower_arc (η : ℝ) (hη : 0 < η) :
    ∃ ρ c : ℝ, 0 < ρ ∧ 0 < c ∧ ∀ (t : ℝ) (x z : ℍ),
      3 / 8 ≤ t → t ≤ 17 / 8 → η ≤ |t - 1| →
      ‖(x : ℂ) - (t : ℂ) * Complex.I‖ < ρ → ‖(z : ℂ) - (t : ℂ) * Complex.I‖ < ρ →
      c * ‖(x : ℂ) - (z : ℂ)‖ ≤ ‖jInvariantFun x - jInvariantFun z‖ := by
  classical
  set A : Set ℝ := {t : ℝ | 3 / 8 ≤ t ∧ t ≤ 17 / 8 ∧ η ≤ |t - 1|} with hA
  have hAc : IsCompact A := by
    have hAeq : A = Set.Icc (3 / 8) (17 / 8) ∩ {t : ℝ | η ≤ |t - 1|} := by
      ext t
      simp only [hA, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_Icc]
      tauto
    rw [hAeq]
    have h1 : IsClosed {t : ℝ | η ≤ |t - 1|} :=
      isClosed_le continuous_const (continuous_abs.comp (continuous_id.sub continuous_const))
    exact isCompact_Icc.inter_right h1
  have hdata : ∀ t ∈ A, ∃ ρ c : ℝ, 0 < ρ ∧ 0 < c ∧ ∀ x z : ℍ,
      ‖(x : ℂ) - (t : ℂ) * Complex.I‖ < ρ → ‖(z : ℂ) - (t : ℂ) * Complex.I‖ < ρ →
      c * ‖(x : ℂ) - (z : ℂ)‖ ≤ ‖jInvariantFun x - jInvariantFun z‖ := by
    intro t ht
    have ht0 : 0 < t := by have := ht.1; linarith
    have hne : t ≠ 1 := by
      intro h
      rw [h] at ht
      have := ht.2.2
      simp at this
      linarith
    obtain ⟨ρ, c, hρ, hc, hb⟩ := Work.Asymptotics.jDiff_lower_imagAxis ht0 hne
    refine ⟨ρ, c, hρ, hc, fun x z hx hz => ?_⟩
    exact hb x z (by exact hx) (by exact hz)
  let R : ℝ → ℝ := fun t => if ht : t ∈ A then (hdata t ht).choose else 1
  let C : ℝ → ℝ := fun t => if ht : t ∈ A then (hdata t ht).choose_spec.choose else 1
  have hR : ∀ t (ht : t ∈ A), 0 < R t := by
    intro t ht; simp only [R, dif_pos ht]; exact (hdata t ht).choose_spec.choose_spec.1
  have hC : ∀ t (ht : t ∈ A), 0 < C t := by
    intro t ht; simp only [C, dif_pos ht]; exact (hdata t ht).choose_spec.choose_spec.2.1
  have hbd : ∀ t (ht : t ∈ A) (x z : ℍ),
      ‖(x : ℂ) - (t : ℂ) * Complex.I‖ < R t → ‖(z : ℂ) - (t : ℂ) * Complex.I‖ < R t →
      C t * ‖(x : ℂ) - (z : ℂ)‖ ≤ ‖jInvariantFun x - jInvariantFun z‖ := by
    intro t ht x z hx hz
    simp only [R, C, dif_pos ht] at hx hz ⊢
    exact (hdata t ht).choose_spec.choose_spec.2.2 x z hx hz
  have hcov : A ⊆ ⋃ i : {t : ℝ // t ∈ A}, Set.Ioo (i.1 - R i.1 / 4) (i.1 + R i.1 / 4) := by
    intro t ht
    refine Set.mem_iUnion.mpr ⟨⟨t, ht⟩, ?_⟩
    simp only [Set.mem_Ioo]
    have := hR t ht
    constructor <;> linarith
  obtain ⟨s, hs⟩ := hAc.elim_finite_subcover _ (fun _ => isOpen_Ioo) hcov
  have hmemcover : ∀ {t : ℝ}, t ∈ A → ∃ i ∈ s, t ∈ Set.Ioo (i.1 - R i.1 / 4) (i.1 + R i.1 / 4) := by
    intro t ht
    have h := hs ht
    rw [Set.mem_iUnion₂] at h
    obtain ⟨i, hi, hP⟩ := h
    exact ⟨i, hi, hP⟩
  by_cases hAne : A.Nonempty
  · obtain ⟨t0, ht0⟩ := hAne
    obtain ⟨i0, hi0, -⟩ := hmemcover ht0
    have hsne : s.Nonempty := ⟨i0, hi0⟩
    set sf : Finset ℝ := s.image (fun i => R i.1 / 4) with hsf
    set cf : Finset ℝ := s.image (fun i => C i.1) with hcf
    have hsfne : sf.Nonempty := by rw [hsf]; exact hsne.image _
    have hcfne : cf.Nonempty := by rw [hcf]; exact hsne.image _
    have hsfpos : 0 < sf.min' hsfne := by
      obtain ⟨a, -, haeq⟩ := Finset.mem_image.mp (Finset.min'_mem sf hsfne)
      rw [← haeq]
      exact div_pos (hR a.1 a.2) (by norm_num)
    have hcfpos : 0 < cf.min' hcfne := by
      obtain ⟨a, -, haeq⟩ := Finset.mem_image.mp (Finset.min'_mem cf hcfne)
      rw [← haeq]
      exact hC a.1 a.2
    refine ⟨sf.min' hsfne / 2, cf.min' hcfne, by linarith, hcfpos, ?_⟩
    intro t x z h1 h2 h3 hx hz
    have htA : t ∈ A := ⟨h1, h2, h3⟩
    obtain ⟨i, his, hti⟩ := hmemcover htA
    have hti' : |t - i.1| < R i.1 / 4 := by
      rw [Set.mem_Ioo] at hti
      rw [abs_lt]
      exact ⟨by linarith [hti.1], by linarith [hti.2]⟩
    have hδle : sf.min' hsfne ≤ R i.1 / 4 :=
      min'_le' sf hsfne (by rw [hsf]; exact Finset.mem_image.mpr ⟨i, his, rfl⟩)
    have hcle : cf.min' hcfne ≤ C i.1 :=
      min'_le' cf hcfne (by rw [hcf]; exact Finset.mem_image.mpr ⟨i, his, rfl⟩)
    have hiR : 0 < R i.1 := hR i.1 i.2
    have hdist : ‖(t : ℂ) * Complex.I - (i.1 : ℂ) * Complex.I‖ = |t - i.1| := by
      rw [← sub_mul, norm_mul, Complex.norm_I, mul_one, ← Complex.ofReal_sub,
        Complex.norm_real, Real.norm_eq_abs]
    have hsplit : ∀ y : ℂ, ‖y - (i.1 : ℂ) * Complex.I‖ ≤ ‖y - (t : ℂ) * Complex.I‖ + |t - i.1| := by
      intro y
      have h1' : (y - (t : ℂ) * Complex.I) + ((t : ℂ) * Complex.I - (i.1 : ℂ) * Complex.I)
          = y - (i.1 : ℂ) * Complex.I := by ring
      have h := norm_add_le (y - (t : ℂ) * Complex.I) ((t : ℂ) * Complex.I - (i.1 : ℂ) * Complex.I)
      rw [h1', hdist] at h
      exact h
    have h4 : sf.min' hsfne / 2 + R i.1 / 4 < R i.1 := by linarith [hδle, hiR]
    have hx' : ‖(x : ℂ) - (i.1 : ℂ) * Complex.I‖ < R i.1 := by
      linarith [hsplit (x : ℂ), hx, hti']
    have hz' : ‖(z : ℂ) - (i.1 : ℂ) * Complex.I‖ < R i.1 := by
      linarith [hsplit (z : ℂ), hz, hti']
    have hb := hbd i.1 i.2 x z hx' hz'
    calc cf.min' hcfne * ‖(x : ℂ) - (z : ℂ)‖ ≤ C i.1 * ‖(x : ℂ) - (z : ℂ)‖ :=
          mul_le_mul_of_nonneg_right hcle (norm_nonneg _)
      _ ≤ ‖jInvariantFun x - jInvariantFun z‖ := hb
  · refine ⟨1, 1, one_pos, one_pos, ?_⟩
    intro t x z h1 h2 h3 hx hz
    exact absurd ⟨t, ⟨h1, h2, h3⟩⟩ hAne

/-- Points of the compact box `K1` lie in the CKMRV fundamental domain `𝒟`. -/
lemma mem_DomainD_of_abs_re_im {z : ℂ} (hre : |z.re| ≤ 1 / 4)
    (him1 : (1 : ℝ) / 2 ≤ z.im) (him2 : z.im ≤ 2) :
    (⟨z, by linarith⟩ : ℍ) ∈ DomainD := by
  have hre' := abs_le.mp hre
  have hcoe : ((⟨z, by linarith⟩ : ℍ) : ℂ) = z := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · change (-1 : ℝ) < z.re; linarith [hre'.1]
  · change z.re < 1; linarith [hre'.2]
  · have h2 : (1 / 2 : ℝ) ^ 2 < ‖z - (1 / 2 : ℂ)‖ ^ 2 := by
      have hsq : ‖z - (1 / 2 : ℂ)‖ ^ 2 = (z.re - 1 / 2) ^ 2 + z.im ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
        norm_num
        ring
      rw [hsq]
      nlinarith [hre'.1, hre'.2, him1, him2, sq_nonneg (z.re - 1 / 2), sq_nonneg z.im]
    rw [hcoe]
    nlinarith [norm_nonneg (z - (1 / 2 : ℂ))]
  · have h2 : (1 / 2 : ℝ) ^ 2 < ‖z + (1 / 2 : ℂ)‖ ^ 2 := by
      have hsq : ‖z + (1 / 2 : ℂ)‖ ^ 2 = (z.re + 1 / 2) ^ 2 + z.im ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.add_re, Complex.add_im]
        norm_num
        ring
      rw [hsq]
      nlinarith [hre'.1, hre'.2, him1, him2, sq_nonneg (z.re + 1 / 2), sq_nonneg z.im]
    rw [hcoe]
    nlinarith [norm_nonneg (z + (1 / 2 : ℂ))]

lemma isCompact_K1 : IsCompact {z : ℂ | |z.re| ≤ 1 / 4 ∧ (1:ℝ)/2 ≤ z.im ∧ z.im ≤ 2} := by
  have e : {z : ℂ | |z.re| ≤ 1 / 4 ∧ (1:ℝ)/2 ≤ z.im ∧ z.im ≤ 2}
      = {z : ℂ | |z.re| ≤ 1 / 4} ∩ {z : ℂ | (1:ℝ)/2 ≤ z.im} ∩ {z : ℂ | z.im ≤ 2} := by
    ext z; simp only [Set.mem_setOf_eq, Set.mem_inter_iff]; tauto
  have hcl : IsClosed {z : ℂ | |z.re| ≤ 1 / 4 ∧ (1:ℝ)/2 ≤ z.im ∧ z.im ≤ 2} := by
    rw [e]
    exact IsClosed.inter (IsClosed.inter
      (isClosed_le (continuous_abs.comp Complex.continuous_re) continuous_const)
      (isClosed_le continuous_const Complex.continuous_im))
      (isClosed_le Complex.continuous_im continuous_const)
  have hsub : {z : ℂ | |z.re| ≤ 1 / 4 ∧ (1:ℝ)/2 ≤ z.im ∧ z.im ≤ 2}
      ⊆ Metric.closedBall (0 : ℂ) 3 := by
    intro z hz
    obtain ⟨hr, hi1, hi2⟩ := hz
    rw [Metric.mem_closedBall, dist_zero_right]
    have hsq : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
    have h1 : z.re ^ 2 ≤ 1 / 16 := by nlinarith [abs_le.mp hr, sq_nonneg z.re]
    have h2 : z.im ^ 2 ≤ 4 := by nlinarith [hi1, hi2]
    have h3 : ‖z‖ ^ 2 ≤ 9 := by rw [hsq]; linarith
    nlinarith [norm_nonneg z]
  exact (isCompact_closedBall (0:ℂ) 3).of_isClosed_subset hcl hsub

lemma isCompact_K2 : IsCompact {z : ℂ | z.re = 0 ∧ (3:ℝ)/8 ≤ z.im ∧ z.im ≤ 17/8} := by
  have e : {z : ℂ | z.re = 0 ∧ (3:ℝ)/8 ≤ z.im ∧ z.im ≤ 17/8}
      = {z : ℂ | z.re = 0} ∩ {z : ℂ | (3:ℝ)/8 ≤ z.im} ∩ {z : ℂ | z.im ≤ 17/8} := by
    ext z; simp only [Set.mem_setOf_eq, Set.mem_inter_iff]; tauto
  have hcl : IsClosed {z : ℂ | z.re = 0 ∧ (3:ℝ)/8 ≤ z.im ∧ z.im ≤ 17/8} := by
    rw [e]
    exact IsClosed.inter (IsClosed.inter
      (isClosed_eq Complex.continuous_re continuous_const)
      (isClosed_le continuous_const Complex.continuous_im))
      (isClosed_le Complex.continuous_im continuous_const)
  have hsub : {z : ℂ | z.re = 0 ∧ (3:ℝ)/8 ≤ z.im ∧ z.im ≤ 17/8} ⊆ Metric.closedBall (0:ℂ) 3 := by
    intro z hz
    obtain ⟨hr, hi1, hi2⟩ := hz
    rw [Metric.mem_closedBall, dist_zero_right]
    have hsq : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
    have h3 : ‖z‖ ^ 2 ≤ 9 := by rw [hsq, hr]; nlinarith [hi1, hi2]
    nlinarith [norm_nonneg z]
  exact (isCompact_closedBall (0:ℂ) 3).of_isClosed_subset hcl hsub

theorem far_two_branch (ε : ℝ) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ (u v : ℍ),
      |(u : ℂ).re| ≤ 1 / 4 → (1 : ℝ) / 2 ≤ (u : ℂ).im → (u : ℂ).im ≤ 2 →
      (v : ℂ).re = 0 → (3 : ℝ) / 8 ≤ (v : ℂ).im → (v : ℂ).im ≤ 17 / 8 →
      |(u : ℂ).im - (v : ℂ).im| ≤ 1 / 8 →
      ε ≤ ‖(u : ℂ) - (v : ℂ)‖ → ε ≤ ‖(v : ℂ) - ((ModularGroup.S • u : ℍ) : ℂ)‖ →
      c * ‖(u : ℂ) - (v : ℂ)‖ * ‖(v : ℂ) - ((ModularGroup.S • u : ℍ) : ℂ)‖
        ≤ ‖jInvariantFun u - jInvariantFun v‖ := by
  classical
  set K1 : Set ℂ := {z : ℂ | |z.re| ≤ 1 / 4 ∧ (1:ℝ)/2 ≤ z.im ∧ z.im ≤ 2} with hK1
  set K2 : Set ℂ := {z : ℂ | z.re = 0 ∧ (3:ℝ)/8 ≤ z.im ∧ z.im ≤ 17/8} with hK2
  set Z : Set (ℂ × ℂ) := {p : ℂ × ℂ | p.1 ∈ K1 ∧ p.2 ∈ K2 ∧ |p.1.im - p.2.im| ≤ 1 / 8 ∧
      ε ≤ ‖p.1 - p.2‖ ∧ ε * ‖p.1‖ ≤ ‖p.1 * p.2 + 1‖} with hZ
  have hZc : IsCompact Z := by
    have hZcl : IsClosed Z := by
      have e : Z = {p : ℂ × ℂ | p.1 ∈ K1} ∩ {p : ℂ × ℂ | p.2 ∈ K2}
          ∩ {p : ℂ × ℂ | |p.1.im - p.2.im| ≤ 1 / 8} ∩ {p : ℂ × ℂ | ε ≤ ‖p.1 - p.2‖}
          ∩ {p : ℂ × ℂ | ε * ‖p.1‖ ≤ ‖p.1 * p.2 + 1‖} := by
        ext p
        simp only [hZ, hK1, hK2, Set.mem_setOf_eq, Set.mem_inter_iff]
        tauto
      rw [e]
      refine IsClosed.inter (IsClosed.inter (IsClosed.inter (IsClosed.inter ?_ ?_) ?_) ?_) ?_
      · exact isCompact_K1.isClosed.preimage continuous_fst
      · exact isCompact_K2.isClosed.preimage continuous_snd
      · exact isClosed_le (continuous_abs.comp ((Complex.continuous_im.comp continuous_fst).sub
          (Complex.continuous_im.comp continuous_snd))) continuous_const
      · exact isClosed_le continuous_const ((continuous_fst.sub continuous_snd).norm)
      · exact isClosed_le (continuous_const.mul continuous_fst.norm)
          ((continuous_fst.mul continuous_snd).add continuous_const).norm
    have hsub : Z ⊆ K1 ×ˢ K2 := fun p hp => ⟨hp.1, hp.2.1⟩
    exact (isCompact_K1.prod isCompact_K2).of_isClosed_subset hZcl hsub
  have hZsub : ∀ p ∈ Z, 0 < p.1.im ∧ 0 < p.2.im := by
    intro p hp
    exact ⟨by linarith [hp.1.2.1], by linarith [hp.2.1.2.1]⟩
  have hZne : ∀ p ∈ Z, p.1 ≠ 0 := by
    intro p hp h
    have h1 : p.1.im = 0 := by rw [h]; simp
    linarith [(hZsub p hp).1]
  have hZbeta : ∀ p ∈ Z, p.2 + p.1⁻¹ = (p.1 * p.2 + 1) / p.1 := by
    intro p hp
    rw [eq_div_iff (hZne p hp), add_mul, inv_mul_cancel₀ (hZne p hp)]
    ring
  have hZnj : ∀ p ∈ Z,
      jInvariantFun (UpperHalfPlane.ofComplex p.1) ≠ jInvariantFun (UpperHalfPlane.ofComplex p.2) := by
    intro p hp hjeq
    have hpmem := hp
    obtain ⟨hp1, hp2, hpim, hα, hβ⟩ := hp
    have h1im : 0 < p.1.im := by linarith [hp1.2.1]
    have h2im : 0 < p.2.im := by linarith [hp2.2.1]
    have ho1 : UpperHalfPlane.ofComplex p.1 = (⟨p.1, h1im⟩ : ℍ) :=
      UpperHalfPlane.ofComplex_apply_of_im_pos h1im
    have ho2 : UpperHalfPlane.ofComplex p.2 = (⟨p.2, h2im⟩ : ℍ) :=
      UpperHalfPlane.ofComplex_apply_of_im_pos h2im
    rw [ho1, ho2] at hjeq
    have hσD : (⟨p.1, h1im⟩ : ℍ) ∈ DomainD := mem_DomainD_of_abs_re_im hp1.1 hp1.2.1 hp1.2.2
    have hτre : ((⟨p.2, h2im⟩ : ℍ) : ℂ).re = 0 := hp2.1
    rcases Work.Asymptotics.eq_or_eq_S_of_re_eq_zero hσD hτre hjeq with hcase | hcase
    · have hp12 : p.2 = p.1 := by
        simpa using congrArg (fun w : ℍ => (w : ℂ)) hcase
      rw [hp12, sub_self, norm_zero] at hα
      linarith
    · have hScoe : ((ModularGroup.S • (⟨p.1, h1im⟩ : ℍ) : ℍ) : ℂ) = -((p.1)⁻¹) :=
        Work.Rigidity.coe_S_smul _
      have h2 : p.2 = -((p.1))⁻¹ := by
        have hh := congrArg (fun w : ℍ => (w : ℂ)) hcase
        rw [hScoe] at hh
        simpa using hh
      have hn1 : p.1 * p.2 + 1 = 0 := by
        rw [h2, mul_neg, mul_inv_cancel₀ (hZne p hpmem)]
        ring
      have hpos : 0 < ε * ‖p.1‖ := by
        have : (1:ℝ)/2 ≤ ‖p.1‖ := by
          have h := Complex.abs_im_le_norm p.1
          rw [abs_of_pos h1im] at h
          linarith [hp1.2.1]
        positivity
      rw [hn1, norm_zero] at hβ
      linarith
  set f : ℂ × ℂ → ℝ := fun p =>
    ‖jInvariantFun (UpperHalfPlane.ofComplex p.1) - jInvariantFun (UpperHalfPlane.ofComplex p.2)‖
      / (‖p.1 - p.2‖ * ‖p.2 + p.1⁻¹‖) with hf
  have hfcont : ContinuousOn f Z := by
    rw [hf]
    have hnum : ContinuousOn (fun p : ℂ × ℂ =>
        jInvariantFun (UpperHalfPlane.ofComplex p.1) - jInvariantFun (UpperHalfPlane.ofComplex p.2)) Z := by
      refine ContinuousOn.sub ?_ ?_
      · exact Work.Residues.continuous_jInvariantFun.comp_continuousOn
          (continuousOn_ofComplex_im_pos.comp continuous_fst.continuousOn
            (fun p hp => (hZsub p hp).1))
      · exact Work.Residues.continuous_jInvariantFun.comp_continuousOn
          (continuousOn_ofComplex_im_pos.comp continuous_snd.continuousOn
            (fun p hp => (hZsub p hp).2))
    refine ContinuousOn.div hnum.norm ?_ ?_
    · exact ContinuousOn.mul ((continuous_fst.sub continuous_snd).continuousOn.norm)
        (ContinuousOn.add continuous_snd.continuousOn
          (ContinuousOn.inv₀ continuous_fst.continuousOn (fun p hp => hZne p hp))).norm
    · intro p hp
      have hβ : 0 < ‖p.2 + p.1⁻¹‖ := by
        rw [hZbeta p hp, norm_div]
        have hpos : 0 < ε * ‖p.1‖ := by
          have h1 : 0 < ‖p.1‖ := norm_pos_iff.mpr (hZne p hp)
          positivity
        have hnum : 0 < ‖p.1 * p.2 + 1‖ := lt_of_lt_of_le hpos hp.2.2.2.2
        exact div_pos hnum (norm_pos_iff.mpr (hZne p hp))
      have hα : 0 < ‖p.1 - p.2‖ := by
        have := hp.2.2.2.1
        linarith
      positivity
  have hfpos : ∀ p ∈ Z, 0 < f p := by
    intro p hp
    rw [hf]
    have h1 : 0 < ‖p.1 - p.2‖ := by have := hp.2.2.2.1; linarith
    have h2 : 0 < ‖p.2 + p.1⁻¹‖ := by
      rw [hZbeta p hp, norm_div]
      have hpos : 0 < ε * ‖p.1‖ := by
        have h1 : 0 < ‖p.1‖ := norm_pos_iff.mpr (hZne p hp)
        positivity
      have hnum : 0 < ‖p.1 * p.2 + 1‖ := lt_of_lt_of_le hpos hp.2.2.2.2
      exact div_pos hnum (norm_pos_iff.mpr (hZne p hp))
    have h3 : 0 < ‖jInvariantFun (UpperHalfPlane.ofComplex p.1)
        - jInvariantFun (UpperHalfPlane.ofComplex p.2)‖ :=
      norm_pos_iff.mpr (sub_ne_zero.mpr (hZnj p hp))
    positivity
  obtain ⟨c, hcpos, hcle⟩ := hZc.exists_forall_le' hfcont hfpos
  refine ⟨c, hcpos, ?_⟩
  intro u v h1 h2 h3 h4 h5 h6 h7 h8 h9
  have hScoe : ((ModularGroup.S • u : ℍ) : ℂ) = -(((u : ℂ))⁻¹) := Work.Rigidity.coe_S_smul u
  have hβeq : ‖(v : ℂ) + ((u : ℂ))⁻¹‖ = ‖(v : ℂ) - ((ModularGroup.S • u : ℍ) : ℂ)‖ := by
    rw [hScoe, sub_neg_eq_add]
  have hmem : (((u : ℂ), (v : ℂ)) : ℂ × ℂ) ∈ Z := by
    refine ⟨⟨h1, h2, h3⟩, ⟨h4, h5, h6⟩, h7, h8, ?_⟩
    have h9' : ε ≤ ‖(v : ℂ) + ((u : ℂ))⁻¹‖ := by rw [hβeq]; exact h9
    have hun : (0:ℝ) < ‖(u : ℂ)‖ := by
      have : (1:ℝ)/2 ≤ ‖(u : ℂ)‖ := by
        have h := Complex.abs_im_le_norm (u : ℂ)
        rw [abs_of_pos (by linarith : (0:ℝ) < (u:ℂ).im)] at h
        linarith
      linarith
    have hu0 : (u : ℂ) ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt hun)
    have hb : ‖(v : ℂ) + ((u : ℂ))⁻¹‖ = ‖(v : ℂ) * (u : ℂ) + 1‖ / ‖(u : ℂ)‖ := by
      have : (v : ℂ) + ((u : ℂ))⁻¹ = ((v : ℂ) * (u : ℂ) + 1) / (u : ℂ) := by
        rw [eq_div_iff hu0, add_mul, inv_mul_cancel₀ hu0]
      rw [this, norm_div]
    rw [hb, le_div_iff₀ hun] at h9'
    rw [mul_comm (v : ℂ) (u : ℂ)] at h9'
    exact h9'
  have hcp := hcle _ hmem
  have hα : 0 < ‖(u : ℂ) - (v : ℂ)‖ := by linarith [h8, hε]
  have hβ : 0 < ‖(v : ℂ) + ((u : ℂ))⁻¹‖ := by
    have := hβeq
    rw [this]; linarith [h9, hε]
  have hfac : f ((u : ℂ), (v : ℂ))
      = ‖jInvariantFun u - jInvariantFun v‖
        / (‖(u : ℂ) - (v : ℂ)‖ * ‖(v : ℂ) + ((u : ℂ))⁻¹‖) := by
    rw [hf]
    simp only
    rw [UpperHalfPlane.ofComplex_apply, UpperHalfPlane.ofComplex_apply]
  have hgoal : c * ‖(u : ℂ) - (v : ℂ)‖ * ‖(v : ℂ) + ((u : ℂ))⁻¹‖
      ≤ ‖jInvariantFun u - jInvariantFun v‖ := by
    have h1' : c * (‖(u : ℂ) - (v : ℂ)‖ * ‖(v : ℂ) + ((u : ℂ))⁻¹‖)
        ≤ f ((u : ℂ), (v : ℂ)) * (‖(u : ℂ) - (v : ℂ)‖ * ‖(v : ℂ) + ((u : ℂ))⁻¹‖) :=
      mul_le_mul_of_nonneg_right hcp (by positivity)
    rw [hfac, div_mul_cancel₀] at h1'
    · linarith [h1']
    · positivity
  rw [← hβeq]
  exact hgoal

/-- **The two-branch lower bound.**  On the bad-line region and inside the spike window, the
difference of `j` at the pole location `z₀ = zpole τ` and at the contour point `it` dominates the
product of the distances to the two coincident branches `z₀` and `S z₀`.

### Proof plan

Use `jSub_factorization` (proved in `Asymptotics/HalfFunnel/jSub_factorization.lean`):
`j u - j v = (λu - λv)(λu + λv - 1) Ψ(...)`, so
`‖j z₀ - j(it)‖ = ‖λz₀ - λ(it)‖ · ‖λz₀ + λ(it) - 1‖ · ‖Ψ(...)‖`
and `λz₀ + λz - 1 = λz - λ(S z₀)` (`Work.Kernels.LogLambda.lambdaFun_S`).  Then
* `Λ := lambdaFun` is uniformly locally bi-Lipschitz on the compact configuration set
  (`MiddleRange.exists_lambdaFun_lipschitz` at finitely many reference points, plus compactness
  of the pair set for the far pairs), giving both `λ`-differences as multiples of the Euclidean
  distances, and
* `Ψ` is bounded away from `0` on the configuration set: `Ψ = 0` together with the factorization
  would force `j z₀ = j(it)`, `λz₀ = λ(it)` or `λ(S z₀) = λ(it)`, each of which implies
  `j z₀ = j(it)`; use `Work.Rigidity.fiberGood_all` and the hypothesis `j z₀ ≠ j(it)` for the
  first two, and `lambdaFun_S` + `j(S z₀) = j(z₀)` for the third; then compactness.
-/
theorem jBranch_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ (τ : ℍ) (t : ℝ) (ht : 0 < t),
      lowBadSet τ → |t - τ.im| ≤ 1 / 8 →
      jInvariantFun (zpole τ) ≠ jInvariantFun (imagAxis t ht) →
      c * ‖((imagAxis t ht : ℍ) : ℂ) - ((zpole τ : ℍ) : ℂ)‖
        * ‖((imagAxis t ht : ℍ) : ℂ) - ((ModularGroup.S • zpole τ : ℍ) : ℂ)‖
        ≤ ‖jInvariantFun (zpole τ) - jInvariantFun (imagAxis t ht)‖ := by
  obtain ⟨δA, cN, hδApos, hcNpos, hN'⟩ := near_I_two_branch
  set δ : ℝ := min δA (1 / 2) with hδdef
  have hδpos : 0 < δ := lt_min hδApos (by norm_num)
  have hδle : δ ≤ δA := min_le_left _ _
  have hδhalf : δ ≤ 1 / 2 := min_le_right _ _
  have hN : ∀ u v : ℍ, ‖(u : ℂ) - Complex.I‖ < δ → ‖(v : ℂ) - Complex.I‖ < δ →
      cN * ‖(u : ℂ) - (v : ℂ)‖ * ‖(v : ℂ) - ((ModularGroup.S • u : ℍ) : ℂ)‖
        ≤ ‖jInvariantFun u - jInvariantFun v‖ :=
    fun u v hu hv => hN' u v (lt_of_lt_of_le hu hδle) (lt_of_lt_of_le hv hδle)
  obtain ⟨ρB, cB, hρBpos, hcBpos, hB⟩ := jDiff_lower_arc (δ / 4) (by linarith)
  set σ : ℝ := min (δ / 4) ρB with hσσ
  have hσpos : 0 < σ := lt_min (by linarith) hρBpos
  have hσ1 : σ ≤ δ / 4 := min_le_left _ _
  have hσ2 : σ ≤ ρB := min_le_right _ _
  obtain ⟨cC, hcCpos, hC⟩ := far_two_branch σ hσpos
  refine ⟨min (min cN (cB / 6)) cC, lt_min (lt_min hcNpos (by positivity)) hcCpos, ?_⟩
  intro τ t ht hτ hw hne
  set u : ℍ := zpole τ with hu
  set v : ℍ := imagAxis t ht with hv
  have hvcoe : ((v : ℍ) : ℂ) = (t : ℂ) * Complex.I := rfl
  have htim : (t : ℂ) * Complex.I = ((v : ℍ) : ℂ) := hvcoe.symm
  -- basic geometry
  have hzre : |((zpole τ : ℍ) : ℂ).re| ≤ 1 / 4 := by
    rw [UpperHalfPlane.coe_re]; exact le_of_lt (zpole_re_abs_lt hτ)
  have hzim : ((zpole τ : ℍ) : ℂ).im = τ.im := by rw [UpperHalfPlane.coe_im, zpole_im]
  have him := lowBadSet_im_bounds hτ
  have hwb := window_bounds hτ ht hw
  have hvim : ((v : ℍ) : ℂ).im = t := by rw [hvcoe]; simp
  have hvre : ((v : ℍ) : ℂ).re = 0 := by rw [hvcoe]; simp
  -- the two distances are bounded by 6
  have hα6 : ‖(u : ℂ) - (v : ℂ)‖ ≤ 6 := by
    have h1 : ‖(u : ℂ)‖ ≤ 3 := by
      have hsq : ‖(u : ℂ)‖ ^ 2 = (u : ℂ).re ^ 2 + (u : ℂ).im ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
      have hr : (u : ℂ).re ^ 2 ≤ 1 / 16 := by
        have := (abs_le.mp hzre).1
        have := (abs_le.mp hzre).2
        nlinarith [sq_nonneg ((u : ℂ).re)]
      have hi : (u : ℂ).im ^ 2 ≤ 4 := by rw [hzim]; nlinarith [him.1, him.2]
      have h2 : ‖(u : ℂ)‖ ^ 2 ≤ 9 := by rw [hsq]; linarith
      nlinarith [norm_nonneg (u : ℂ)]
    have h2 : ‖(v : ℂ)‖ ≤ 17 / 8 := by
      rw [hvcoe]
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith [hwb.1], hwb.2⟩
    calc ‖(u : ℂ) - (v : ℂ)‖ ≤ ‖(u : ℂ)‖ + ‖(v : ℂ)‖ := norm_sub_le _ _
      _ ≤ 3 + 17 / 8 := by linarith
      _ ≤ 6 := by norm_num
  have hβ6 : ‖(v : ℂ) - ((ModularGroup.S • u : ℍ) : ℂ)‖ ≤ 6 := by
    have h1 : ‖((ModularGroup.S • u : ℍ) : ℂ)‖ ≤ 2 := by
      have hScoeu : ((ModularGroup.S • u : ℍ) : ℂ) = -(((u : ℂ))⁻¹) := Work.Rigidity.coe_S_smul u
      rw [hScoeu, norm_neg, norm_inv]
      have hu1 : (1 : ℝ) / 2 ≤ ‖(u : ℂ)‖ := by
        have h := Complex.abs_im_le_norm (u : ℂ)
        rw [abs_of_pos (by rw [hzim]; linarith [him.1]), hzim] at h
        linarith [him.1, h]
      rw [inv_le_iff_one_le_mul₀ (by linarith)]
      linarith
    have h2 : ‖(v : ℂ)‖ ≤ 17 / 8 := by
      rw [hvcoe]
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith [hwb.1], hwb.2⟩
    calc ‖(v : ℂ) - ((ModularGroup.S • u : ℍ) : ℂ)‖
        ≤ ‖(v : ℂ)‖ + ‖((ModularGroup.S • u : ℍ) : ℂ)‖ := norm_sub_le _ _
      _ ≤ 17 / 8 + 2 := by linarith
      _ ≤ 6 := by norm_num
  -- the derivation of a gap from `1` in the non-near cases
  have hvinormeq : ‖(v : ℂ) - Complex.I‖ = |t - 1| := by
    rw [hvcoe, show (t : ℂ) * Complex.I - Complex.I = ((t - 1 : ℝ) : ℂ) * Complex.I by
      push_cast; ring]
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hgap2 : ¬ (‖(u : ℂ) - Complex.I‖ < δ ∧ ‖(v : ℂ) - Complex.I‖ < δ) →
      ‖(u : ℂ) - (v : ℂ)‖ < σ → δ / 4 ≤ |t - 1| := by
    intro hnc hlt
    by_contra hcon
    rw [not_le] at hcon
    have h1 : ‖(v : ℂ) - Complex.I‖ < δ / 4 := by rw [hvinormeq]; exact hcon
    have h2 : ‖(u : ℂ) - Complex.I‖ ≤ ‖(u : ℂ) - (v : ℂ)‖ + ‖(v : ℂ) - Complex.I‖ := by
      have h := norm_add_le ((u : ℂ) - (v : ℂ)) ((v : ℂ) - Complex.I)
      rw [show (u : ℂ) - (v : ℂ) + ((v : ℂ) - Complex.I) = (u : ℂ) - Complex.I by ring] at h
      exact h
    have h3 : ‖(u : ℂ) - Complex.I‖ < δ := by linarith [h2, hlt, hσ1, h1, hδpos]
    have h4 : ‖(v : ℂ) - Complex.I‖ < δ := by linarith [h1, hδpos]
    exact hnc ⟨h3, h4⟩
  have hgap3 : ¬ (‖(u : ℂ) - Complex.I‖ < δ ∧ ‖(v : ℂ) - Complex.I‖ < δ) →
      ‖(v : ℂ) - ((ModularGroup.S • u : ℍ) : ℂ)‖ < σ → δ / 4 ≤ |t - 1| := by
    intro hnc hlt
    by_contra hcon
    rw [not_le] at hcon
    have h1 : ‖(v : ℂ) - Complex.I‖ < δ / 4 := by rw [hvinormeq]; exact hcon
    have h2 : ‖((ModularGroup.S • u : ℍ) : ℂ) - Complex.I‖ < δ / 2 := by
      have h3 : ‖((ModularGroup.S • u : ℍ) : ℂ) - (v : ℂ)‖
          = ‖(v : ℂ) - ((ModularGroup.S • u : ℍ) : ℂ)‖ := norm_sub_rev _ _
      have h4 : ‖((ModularGroup.S • u : ℍ) : ℂ) - Complex.I‖
          ≤ ‖((ModularGroup.S • u : ℍ) : ℂ) - (v : ℂ)‖ + ‖(v : ℂ) - Complex.I‖ := by
        have h := norm_add_le (((ModularGroup.S • u : ℍ) : ℂ) - (v : ℂ)) ((v : ℂ) - Complex.I)
        rw [show ((ModularGroup.S • u : ℍ) : ℂ) - (v : ℂ) + ((v : ℂ) - Complex.I)
          = ((ModularGroup.S • u : ℍ) : ℂ) - Complex.I by ring] at h
        exact h
      rw [h3] at h4
      linarith [h4, hlt, hσ1, h1]
    have hSnorm : (3 : ℝ) / 4 ≤ ‖((ModularGroup.S • u : ℍ) : ℂ)‖ := by
      have h := norm_sub_norm_le Complex.I ((ModularGroup.S • u : ℍ) : ℂ)
      rw [Complex.norm_I, norm_sub_rev] at h
      linarith [h2, hδhalf]
    have hSne : ((ModularGroup.S • u : ℍ) : ℂ) ≠ 0 := by
      intro hzero
      have : ‖((ModularGroup.S • u : ℍ) : ℂ)‖ = 0 := by rw [hzero]; simp
      linarith [hSnorm]
    have hSS : ModularGroup.S • (ModularGroup.S • u) = u := KL.S_smul_S_smul' u
    have hkey := norm_S_sub_I (ModularGroup.S • u)
    rw [hSS] at hkey
    have h5 : ‖(u : ℂ) - Complex.I‖ ≤ 2 * ‖((ModularGroup.S • u : ℍ) : ℂ) - Complex.I‖ := by
      rw [hkey, div_le_iff₀ (by positivity)]
      have hle : (1 : ℝ) ≤ 2 * ‖((ModularGroup.S • u : ℍ) : ℂ)‖ := by linarith
      calc ‖((ModularGroup.S • u : ℍ) : ℂ) - Complex.I‖
          = 1 * ‖((ModularGroup.S • u : ℍ) : ℂ) - Complex.I‖ := by ring
        _ ≤ 2 * ‖((ModularGroup.S • u : ℍ) : ℂ)‖
              * ‖((ModularGroup.S • u : ℍ) : ℂ) - Complex.I‖ :=
            mul_le_mul_of_nonneg_right hle (norm_nonneg _)
        _ = 2 * ‖((ModularGroup.S • u : ℍ) : ℂ) - Complex.I‖
              * ‖((ModularGroup.S • u : ℍ) : ℂ)‖ := by ring
    have h6 : ‖(u : ℂ) - Complex.I‖ < δ := by linarith [h5, h2, hδpos]
    have h7 : ‖(v : ℂ) - Complex.I‖ < δ := by linarith [h1, hδpos]
    exact hnc ⟨h6, h7⟩
  by_cases hnear : ‖(u : ℂ) - Complex.I‖ < δ ∧ ‖(v : ℂ) - Complex.I‖ < δ
  · have h1 := hN u v hnear.1 hnear.2
    have h2 : ‖(v : ℂ) - (u : ℂ)‖ = ‖(u : ℂ) - (v : ℂ)‖ := norm_sub_rev _ _
    have h3 : min (min cN (cB / 6)) cC ≤ cN := le_trans (min_le_left _ _) (min_le_left _ _)
    rw [h2]
    calc min (min cN (cB / 6)) cC * ‖(u : ℂ) - (v : ℂ)‖
          * ‖(v : ℂ) - ((ModularGroup.S • u : ℍ) : ℂ)‖
        ≤ cN * ‖(u : ℂ) - (v : ℂ)‖ * ‖(v : ℂ) - ((ModularGroup.S • u : ℍ) : ℂ)‖ := by
          have hnn : 0 ≤ ‖(u : ℂ) - (v : ℂ)‖ * ‖(v : ℂ) - ((ModularGroup.S • u : ℍ) : ℂ)‖ :=
            mul_nonneg (norm_nonneg _) (norm_nonneg _)
          nlinarith [h3, hnn]
      _ ≤ ‖jInvariantFun u - jInvariantFun v‖ := h1
  · by_cases hα : ‖(u : ℂ) - (v : ℂ)‖ < σ
    · have hgap := hgap2 hnear hα
      have h1 : cB * ‖(u : ℂ) - (v : ℂ)‖ ≤ ‖jInvariantFun u - jInvariantFun v‖ := by
        refine hB t u v ?_ ?_ hgap ?_ ?_
        · linarith [hwb.1]
        · linarith [hwb.2]
        · rw [htim]; exact lt_of_lt_of_le hα hσ2
        · rw [htim, sub_self, norm_zero]; exact hρBpos
      have h2 : ‖(v : ℂ) - (u : ℂ)‖ = ‖(u : ℂ) - (v : ℂ)‖ := norm_sub_rev _ _
      have h3 : min (min cN (cB / 6)) cC ≤ cB / 6 := le_trans (min_le_left _ _) (min_le_right _ _)
      rw [h2]
      calc min (min cN (cB / 6)) cC * ‖(u : ℂ) - (v : ℂ)‖
            * ‖(v : ℂ) - ((ModularGroup.S • u : ℍ) : ℂ)‖
          ≤ cB / 6 * ‖(u : ℂ) - (v : ℂ)‖ * ‖(v : ℂ) - ((ModularGroup.S • u : ℍ) : ℂ)‖ := by
            have hnn : 0 ≤ ‖(u : ℂ) - (v : ℂ)‖ * ‖(v : ℂ) - ((ModularGroup.S • u : ℍ) : ℂ)‖ :=
              mul_nonneg (norm_nonneg _) (norm_nonneg _)
            nlinarith [h3, hnn]
        _ ≤ cB * ‖(u : ℂ) - (v : ℂ)‖ := by
            have hmn : (cB / 6) * ‖(u : ℂ) - (v : ℂ)‖
                * ‖(v : ℂ) - ((ModularGroup.S • u : ℍ) : ℂ)‖
                = ((cB / 6) * ‖(u : ℂ) - (v : ℂ)‖)
                  * ‖(v : ℂ) - ((ModularGroup.S • u : ℍ) : ℂ)‖ := by ring
            rw [hmn]
            calc ((cB / 6) * ‖(u : ℂ) - (v : ℂ)‖)
                  * ‖(v : ℂ) - ((ModularGroup.S • u : ℍ) : ℂ)‖
                ≤ ((cB / 6) * ‖(u : ℂ) - (v : ℂ)‖) * 6 :=
                  mul_le_mul_of_nonneg_left hβ6 (by positivity)
              _ = cB * ‖(u : ℂ) - (v : ℂ)‖ := by ring
        _ ≤ ‖jInvariantFun u - jInvariantFun v‖ := h1
    · have hα' : σ ≤ ‖(u : ℂ) - (v : ℂ)‖ := le_of_not_gt hα
      by_cases hβ : ‖(v : ℂ) - ((ModularGroup.S • u : ℍ) : ℂ)‖ < σ
      · have hgap := hgap3 hnear hβ
        have h1 : cB * ‖((ModularGroup.S • u : ℍ) : ℂ) - (v : ℂ)‖
            ≤ ‖jInvariantFun (ModularGroup.S • u) - jInvariantFun v‖ := by
          refine hB t (ModularGroup.S • u) v ?_ ?_ hgap ?_ ?_
          · linarith [hwb.1]
          · linarith [hwb.2]
          · rw [htim, norm_sub_rev]; exact lt_of_lt_of_le hβ hσ2
          · rw [htim, sub_self, norm_zero]; exact hρBpos
        have h2 : ‖jInvariantFun (ModularGroup.S • u) - jInvariantFun v‖
            = ‖jInvariantFun u - jInvariantFun v‖ := by
          rw [KernelFacts.jInvariantFun_S_smul]
        have h3 : min (min cN (cB / 6)) cC ≤ cB / 6 := le_trans (min_le_left _ _) (min_le_right _ _)
        rw [norm_sub_rev (v : ℂ) ((u : ℂ))]
        calc min (min cN (cB / 6)) cC * ‖(u : ℂ) - (v : ℂ)‖
              * ‖(v : ℂ) - ((ModularGroup.S • u : ℍ) : ℂ)‖
            ≤ cB / 6 * ‖(u : ℂ) - (v : ℂ)‖ * ‖(v : ℂ) - ((ModularGroup.S • u : ℍ) : ℂ)‖ := by
              have hnn : 0 ≤ ‖(u : ℂ) - (v : ℂ)‖ * ‖(v : ℂ) - ((ModularGroup.S • u : ℍ) : ℂ)‖ :=
                mul_nonneg (norm_nonneg _) (norm_nonneg _)
              nlinarith [h3, hnn]
          _ ≤ cB * ‖((ModularGroup.S • u : ℍ) : ℂ) - (v : ℂ)‖ := by
            have hbs : ‖((ModularGroup.S • u : ℍ) : ℂ) - (v : ℂ)‖
                = ‖(v : ℂ) - ((ModularGroup.S • u : ℍ) : ℂ)‖ := norm_sub_rev _ _
            rw [hbs]
            have hmn : (cB / 6) * ‖(u : ℂ) - (v : ℂ)‖
                * ‖(v : ℂ) - ((ModularGroup.S • u : ℍ) : ℂ)‖
                = ((cB / 6) * ‖(v : ℂ) - ((ModularGroup.S • u : ℍ) : ℂ)‖)
                  * ‖(u : ℂ) - (v : ℂ)‖ := by ring
            rw [hmn]
            calc ((cB / 6) * ‖(v : ℂ) - ((ModularGroup.S • u : ℍ) : ℂ)‖)
                  * ‖(u : ℂ) - (v : ℂ)‖
                ≤ ((cB / 6) * ‖(v : ℂ) - ((ModularGroup.S • u : ℍ) : ℂ)‖) * 6 :=
                  mul_le_mul_of_nonneg_left hα6 (by positivity)
              _ = cB * ‖(v : ℂ) - ((ModularGroup.S • u : ℍ) : ℂ)‖ := by ring
          _ ≤ ‖jInvariantFun u - jInvariantFun v‖ := by rw [← h2]; exact h1
      · have hβ' : σ ≤ ‖(v : ℂ) - ((ModularGroup.S • u : ℍ) : ℂ)‖ := le_of_not_gt hβ
        have h1 : cC * ‖(u : ℂ) - (v : ℂ)‖ * ‖(v : ℂ) - ((ModularGroup.S • u : ℍ) : ℂ)‖
            ≤ ‖jInvariantFun u - jInvariantFun v‖ := by
          have hmain := hC u v hzre (by rw [hzim]; exact him.1) (by rw [hzim]; exact him.2)
            hvre (by rw [hvim]; exact hwb.1) (by rw [hvim]; exact hwb.2)
            (by rw [hzim, hvim]; rw [abs_sub_comm]; exact hw) hα' hβ'
          exact hmain
        have h2 : ‖(v : ℂ) - (u : ℂ)‖ = ‖(u : ℂ) - (v : ℂ)‖ := norm_sub_rev _ _
        rw [h2]
        calc min (min cN (cB / 6)) cC * ‖(u : ℂ) - (v : ℂ)‖
              * ‖(v : ℂ) - ((ModularGroup.S • u : ℍ) : ℂ)‖
            ≤ cC * ‖(u : ℂ) - (v : ℂ)‖ * ‖(v : ℂ) - ((ModularGroup.S • u : ℍ) : ℂ)‖ := by
              have hnn : 0 ≤ ‖(u : ℂ) - (v : ℂ)‖ * ‖(v : ℂ) - ((ModularGroup.S • u : ℍ) : ℂ)‖ :=
                mul_nonneg (norm_nonneg _) (norm_nonneg _)
              have h4 : min (min cN (cB / 6)) cC ≤ cC := min_le_right _ _
              nlinarith [h4, hnn]
          _ ≤ ‖jInvariantFun u - jInvariantFun v‖ := h1

/-- **The numerator bound.**  `M(z) = A(τ,z)(z - z₀) + (n/2π)(j z - j z₀)`, with `z₀ = zpole τ`,
vanishes to second order at the pole `z₀` and to first order at `S z₀`, whence the cubic bound
`‖M(z)‖ ≤ C ‖z - z₀‖² ‖z - S z₀‖` on the spike region.

### Proof plan (in the `ℂ`-chart with `Mchart`)

Write `z₀c := (τ:ℂ) - (n:ℂ)`, `zc := t·I`, `Sc := ((S • zpole τ : ℍ) : ℂ) = -1/z₀c`, and let
`M := Mchart ℓ d τ n`; then `Mnum ℓ d τ t ht = M zc` (`Mnum_eq_Mchart`) and
`M Sc = 0` (the S-vanishing `AfunFun_S_vadd_zero` plus `j(S z₀) = j(z₀)`).

1. `M z₀c = 0`, `deriv M z₀c = 0` (`Mchart_self_zero`, `deriv_Mchart_self_zero`).
2. `g := dslope (dslope M z₀c) z₀c` satisfies `M u = (u - z₀c)^2 * g u` for all `u`
   (`sub_smul_dslope_of_zero` twice) and `g Sc = 0`.
3. `‖g u‖ ≤ 64 * CM` for `‖u - z₀c‖ ≤ 1/8`: maximum modulus on the disc of radius `1/8`
   around `z₀c`, with frontier bound `‖M w‖/‖w - z₀c‖² ≤ CM * 64` (`Mchart_bound_region`);
   use `Complex.norm_le_of_forall_mem_frontier_norm_le`.
4. `‖g u‖ ≤ 4096 * CM` for `‖u - Sc‖ ≤ 1/32`: if `‖Sc - z₀c‖ ≥ 1/32` use
   `‖g u‖ = ‖M u‖/‖u - z₀c‖²` with `‖u - z₀c‖ ≥ 1/64`; otherwise `‖u - z₀c‖ ≤ 1/64 + 1/32 < 1/8`
   and 3. applies.
5. `KL.norm_le_mul_dist_of_one_zero` for `g` at `Sc` with radius `1/32` and bound `4096 * CM`
   gives `‖g u‖ ≤ 64 * 4096 * CM * ‖u - Sc‖` for `‖u - Sc‖ ≤ 1/64`.
6. `‖Mnum‖ = ‖zc - z₀c‖² ‖g zc‖` is
   * `≤ a² * 2^18 CM * b` if `b := ‖zc - Sc‖ ≤ 1/64` (by 5.),
   * `≤ a² * 64 CM` if `a ≤ 1/8 < 64 b` (by 3.), so the bound holds since `b > 1/64`,
   * `≤ CM ≤ 2^12 CM * a² * b` if `a > 1/8` and `b > 1/64` (`Mchart_bound_region`).
   Hence `C := 2^18 CM + 2^12 CM + 1` works.
-/
theorem M_bound_region (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : ℍ) (t : ℝ) (ht : 0 < t),
      lowBadSet τ → |t - τ.im| ≤ 1 / 8 →
      ‖Mnum ℓ d τ t ht‖
        ≤ C * ‖((imagAxis t ht : ℍ) : ℂ) - ((zpole τ : ℍ) : ℂ)‖ ^ 2
            * ‖((imagAxis t ht : ℍ) : ℂ) - ((ModularGroup.S • zpole τ : ℍ) : ℂ)‖ := by
  obtain ⟨CM, hCM, hMb⟩ := Mchart_bound_region ℓ d hd
  refine ⟨2 ^ 19 * CM + 1, by positivity, ?_⟩
  intro τ t ht hτ hw
  obtain ⟨n, hn, hcast⟩ := tsign_eq_intCast τ
  have hzp : zpole τ = (-(n : ℝ)) +ᵥ τ := by rw [zpole, hcast]
  have hτvadd : (n : ℝ) +ᵥ zpole τ = τ := by
    rw [hzp, ← add_vadd, add_neg_cancel, zero_vadd]
  have hz₀c0 : ((zpole τ : ℍ) : ℂ) = (τ : ℂ) - (n : ℂ) := zpole_coe_eq τ hcast
  set z₀c : ℂ := (τ : ℂ) - (n : ℂ) with hz₀c_def
  set Sc : ℂ := ((ModularGroup.S • zpole τ : ℍ) : ℂ) with hSc
  set zc : ℂ := (t : ℂ) * Complex.I with hzc
  set g : ℂ → ℂ := dslope (dslope (Mchart ℓ d τ n) z₀c) z₀c with hg
  have hz₀c_coe : z₀c = ((zpole τ : ℍ) : ℂ) := by rw [hz₀c_def, hz₀c0]
  have hz₀im : 0 < z₀c.im := by rw [hz₀c_coe, UpperHalfPlane.coe_im]; exact (zpole τ).im_pos
  have hz₀im_half : (1 / 2 : ℝ) ≤ z₀c.im := by
    rw [hz₀c_coe, UpperHalfPlane.coe_im, zpole_im]; exact (lowBadSet_im_bounds hτ).1
  have hΩ : {u : ℂ | 0 < u.im} ∈ nhds z₀c :=
    (isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz₀im
  have hM0 : Mchart ℓ d τ n z₀c = 0 := by rw [hz₀c_def]; exact Mchart_self_zero ℓ d τ n
  have hMd0 : deriv (Mchart ℓ d τ n) z₀c = 0 := by
    rw [hz₀c_def]; exact deriv_Mchart_self_zero ℓ d hd τ n hn
  have hMSc : Mchart ℓ d τ n Sc = 0 := by
    have h := Mchart_S_zero ℓ d hd n hn (zpole τ)
    rw [hτvadd, ← hSc] at h
    exact h
  have hA1 : dslope (Mchart ℓ d τ n) z₀c z₀c = 0 := by rw [dslope_same]; exact hMd0
  have hfac : ∀ w : ℂ, Mchart ℓ d τ n w = (w - z₀c) ^ 2 * g w := by
    intro w
    have h1 : (w - z₀c) * dslope (Mchart ℓ d τ n) z₀c w = Mchart ℓ d τ n w := by
      simpa using sub_smul_dslope_of_zero hM0 w
    have h2 : (w - z₀c) * g w = dslope (Mchart ℓ d τ n) z₀c w := by
      rw [hg]; simpa using sub_smul_dslope_of_zero hA1 w
    rw [← h1, ← h2]; ring
  -- Sc ≠ z₀c
  have hScz₀c : Sc ≠ z₀c := by
    intro h
    have hcoe' : Sc = -(((zpole τ : ℍ) : ℂ))⁻¹ := by
      rw [hSc]; exact Work.Rigidity.coe_S_smul (zpole τ)
    have hne : ((zpole τ : ℍ) : ℂ) ≠ 0 := by
      intro h0
      have h1 : ((zpole τ : ℍ) : ℂ).im = 0 := by rw [h0]; simp
      rw [UpperHalfPlane.coe_im] at h1
      linarith [(zpole τ).im_pos]
    have h' : -(((zpole τ : ℍ) : ℂ))⁻¹ = ((zpole τ : ℍ) : ℂ) := by
      rw [hcoe'] at h
      rwa [hz₀c_coe] at h
    have h2 : (((zpole τ : ℍ) : ℂ)) ^ 2 = -1 := by
      have hm := congrArg (fun x : ℂ => x * ((zpole τ : ℍ) : ℂ)) h'
      rw [neg_mul, inv_mul_cancel₀ hne] at hm
      rw [pow_two]; exact hm.symm
    have hne_im : (((zpole τ : ℍ) : ℂ)).im ≠ 0 := by
      rw [UpperHalfPlane.coe_im]; exact ne_of_gt (zpole τ).im_pos
    have hre0 : (((zpole τ : ℍ) : ℂ)).re = 0 := by
      have h := congrArg Complex.im h2
      rw [pow_two, Complex.mul_im] at h
      simp only [Complex.neg_im, Complex.one_im, neg_zero] at h
      have hsum : (((zpole τ : ℍ) : ℂ)).re * (((zpole τ : ℍ) : ℂ)).im = 0 := by nlinarith [h]
      exact (mul_eq_zero.mp hsum).resolve_right hne_im
    rw [UpperHalfPlane.coe_re] at hre0
    exact zpole_re_ne_zero hτ hre0
  have hgSc : g Sc = 0 := by
    have h := hfac Sc
    rw [hMSc] at h
    exact (mul_eq_zero.mp h.symm).resolve_left (pow_ne_zero 2 (sub_ne_zero.mpr hScz₀c))
  -- differentiability / continuity of g
  have hgd : DifferentiableOn ℂ g {u : ℂ | 0 < u.im} := by
    rw [hg]
    exact (Complex.differentiableOn_dslope hΩ).mpr
      ((Complex.differentiableOn_dslope hΩ).mpr (differentiableOn_Mchart ℓ d hd τ n))
  have hgc : ContinuousOn g {u : ℂ | 0 < u.im} := by
    rw [hg]
    have h1 : ContinuousOn (dslope (Mchart ℓ d τ n) z₀c) {u : ℂ | 0 < u.im} :=
      (continuousOn_dslope hΩ).mpr
        ⟨(differentiableOn_Mchart ℓ d hd τ n).continuousOn,
          (differentiableOn_Mchart ℓ d hd τ n).differentiableAt hΩ⟩
    exact (continuousOn_dslope hΩ).mpr ⟨h1, ((Complex.differentiableOn_dslope hΩ).mpr
      (differentiableOn_Mchart ℓ d hd τ n)).differentiableAt hΩ⟩
  have him_of_le : ∀ u : ℂ, ‖u - z₀c‖ ≤ 1 / 8 → 0 < u.im := by
    intro u hu
    have h1 := Complex.abs_im_le_norm (u - z₀c)
    rw [Complex.sub_im] at h1
    have h2 := abs_le.mp h1
    linarith [h2.1, hu, hz₀im_half]
  have hgc_dcc : DiffContOnCl ℂ g (Metric.ball z₀c (1 / 8)) :=
    ⟨hgd.mono (fun u hu => him_of_le u (by
        have h := Metric.mem_ball.mp hu; rw [dist_eq_norm] at h; exact le_of_lt h)),
     hgc.mono (fun u hu => him_of_le u (by
        have h := Metric.mem_closedBall.mp (Metric.closure_ball_subset_closedBall hu)
        rwa [dist_eq_norm] at h))⟩
  have hfront : ∀ w ∈ frontier (Metric.ball z₀c (1 / 8)), ‖g w‖ ≤ 64 * CM := by
    intro w hw
    have hwd : ‖w - z₀c‖ = 1 / 8 := by
      rw [← dist_eq_norm]
      exact Metric.mem_sphere.mp (Metric.frontier_ball_subset_sphere hw)
    have hwreg : w ∈ spikeRegC :=
      zpole_ball_spikeRegC hτ (by rw [← hz₀c_coe, hwd])
    have hMw : ‖Mchart ℓ d τ n w‖ ≤ CM := hMb τ n w hn hcast hτ hwreg
    have hmul : ‖Mchart ℓ d τ n w‖ = (1 / 64 : ℝ) * ‖g w‖ := by
      rw [hfac w, norm_mul, norm_pow, hwd]; norm_num
    linarith [hMw, hmul, norm_nonneg (g w)]
  have hg64 : ∀ u : ℂ, ‖u - z₀c‖ < 1 / 8 → ‖g u‖ ≤ 64 * CM := by
    intro u hu
    refine Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hgc_dcc hfront ?_
    exact subset_closure (Metric.mem_ball.mpr (by rw [dist_eq_norm]; exact hu))
  have hSc_im : (1 / 16 : ℝ) ≤ Sc.im := by
    have h := (Szpole_im_bounds hτ).1
    rwa [← hSc] at h
  have himSc_of_le : ∀ u : ℂ, ‖u - Sc‖ ≤ 1 / 32 → 0 < u.im := by
    intro u hu
    have h1 := Complex.abs_im_le_norm (u - Sc)
    rw [Complex.sub_im] at h1
    have h2 := abs_le.mp h1
    linarith [h2.1, hu, hSc_im]
  have hg4096 : ∀ u : ℂ, ‖u - Sc‖ ≤ 1 / 32 → ‖g u‖ ≤ 4096 * CM := by
    intro u hu
    rcases lt_or_ge ‖u - z₀c‖ (1 / 8) with hlt | hge
    · have h := hg64 u hlt; linarith [hCM]
    · have hureg : u ∈ spikeRegC := by
        rw [hSc] at hu; exact Szpole_ball_spikeRegC hτ hu
      have hMu : ‖Mchart ℓ d τ n u‖ ≤ CM := hMb τ n u hn hcast hτ hureg
      have hmul : ‖Mchart ℓ d τ n u‖ = ‖u - z₀c‖ ^ 2 * ‖g u‖ := by
        rw [hfac u, norm_mul, norm_pow]
      have h2 : (1 / 64 : ℝ) ≤ ‖u - z₀c‖ ^ 2 := by
        nlinarith [hge, norm_nonneg (u - z₀c)]
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
  -- assemble
  have hzc' : ((imagAxis t ht : ℍ) : ℂ) = zc := by rw [coe_imagAxis, hzc]
  have hz₀c' : ((zpole τ : ℍ) : ℂ) = z₀c := hz₀c_coe.symm
  have hSc' : ((ModularGroup.S • zpole τ : ℍ) : ℂ) = Sc := hSc.symm
  rw [hzc', hz₀c']
  have hzcReg : zc ∈ spikeRegC := by
    rw [hzc, ← coe_imagAxis t ht]; exact imagAxis_mem_spikeRegC hτ ht hw
  have hMn : Mnum ℓ d τ t ht = Mchart ℓ d τ n zc := by
    rw [hzc]; exact Mnum_eq_Mchart ℓ d ht hcast
  have hMz : ‖Mnum ℓ d τ t ht‖ = ‖zc - z₀c‖ ^ 2 * ‖g zc‖ := by
    rw [hMn, hfac zc, norm_mul, norm_pow]
  have ha2 : 0 ≤ ‖zc - z₀c‖ ^ 2 := sq_nonneg _
  have hb2 : 0 ≤ ‖zc - Sc‖ := norm_nonneg _
  by_cases hb : ‖zc - Sc‖ ≤ 1 / 128
  · have h1 := hone zc hb
    have hA : ‖Mnum ℓ d τ t ht‖ ≤ 2 ^ 18 * CM * (‖zc - z₀c‖ ^ 2 * ‖zc - Sc‖) := by
      rw [hMz]
      calc ‖zc - z₀c‖ ^ 2 * ‖g zc‖ ≤ ‖zc - z₀c‖ ^ 2 * (2 ^ 18 * CM * ‖zc - Sc‖) :=
            mul_le_mul_of_nonneg_left h1 ha2
        _ = 2 ^ 18 * CM * (‖zc - z₀c‖ ^ 2 * ‖zc - Sc‖) := by ring
    have hle : 2 ^ 18 * CM ≤ 2 ^ 19 * CM + 1 := by nlinarith [hCM]
    calc ‖Mnum ℓ d τ t ht‖ ≤ 2 ^ 18 * CM * (‖zc - z₀c‖ ^ 2 * ‖zc - Sc‖) := hA
      _ ≤ (2 ^ 19 * CM + 1) * (‖zc - z₀c‖ ^ 2 * ‖zc - Sc‖) :=
            mul_le_mul_of_nonneg_right hle (mul_nonneg ha2 hb2)
      _ = (2 ^ 19 * CM + 1) * ‖zc - z₀c‖ ^ 2 * ‖zc - Sc‖ := by ring
  · push_neg at hb
    by_cases ha : ‖zc - z₀c‖ < 1 / 8
    · have h1 := hg64 zc ha
      have hbpos : 0 < ‖zc - Sc‖ := by linarith
      have hA : ‖Mnum ℓ d τ t ht‖ ≤ 64 * CM * ‖zc - z₀c‖ ^ 2 := by
        rw [hMz]
        calc ‖zc - z₀c‖ ^ 2 * ‖g zc‖ ≤ ‖zc - z₀c‖ ^ 2 * (64 * CM) :=
              mul_le_mul_of_nonneg_left h1 ha2
          _ = 64 * CM * ‖zc - z₀c‖ ^ 2 := by ring
      have hstep1 : 64 * CM * ‖zc - z₀c‖ ^ 2
          ≤ 2 ^ 12 * CM * ‖zc - z₀c‖ ^ 2 := by
        have h2 : 64 * CM ≤ 2 ^ 12 * CM := by nlinarith [hCM]
        exact mul_le_mul_of_nonneg_right h2 ha2
      have hstep2 : 2 ^ 12 * CM * ‖zc - z₀c‖ ^ 2
          ≤ (2 ^ 19 * CM + 1) * ‖zc - z₀c‖ ^ 2 * ‖zc - Sc‖ := by
        have h2 : 2 ^ 12 * CM * ‖zc - z₀c‖ ^ 2 ≤ 2 ^ 19 * CM * ‖zc - z₀c‖ ^ 2 * ‖zc - Sc‖ := by
          have h3 : (1 / 128 : ℝ) * (2 ^ 19 * CM * ‖zc - z₀c‖ ^ 2)
              ≤ ‖zc - Sc‖ * (2 ^ 19 * CM * ‖zc - z₀c‖ ^ 2) :=
            mul_le_mul_of_nonneg_right hb.le (by positivity)
          have h4 : (1 / 128 : ℝ) * (2 ^ 19 * CM * ‖zc - z₀c‖ ^ 2)
              = 2 ^ 12 * CM * ‖zc - z₀c‖ ^ 2 := by norm_num; ring
          linarith [h3, h4]
        have h5 : 2 ^ 19 * CM * ‖zc - z₀c‖ ^ 2 * ‖zc - Sc‖
            ≤ (2 ^ 19 * CM + 1) * ‖zc - z₀c‖ ^ 2 * ‖zc - Sc‖ := by
          have h6 : 0 ≤ ‖zc - z₀c‖ ^ 2 * ‖zc - Sc‖ := mul_nonneg ha2 hb2
          nlinarith [h6, hCM]
        linarith [h2, h5]
      linarith [hA, hstep1, hstep2]
    · push_neg at ha
      have hMu : ‖Mchart ℓ d τ n zc‖ ≤ CM := hMb τ n zc hn hcast hτ hzcReg
      have hA : ‖Mnum ℓ d τ t ht‖ ≤ CM := by rw [hMn]; exact hMu
      have hab : (1 / 8 : ℝ) * (1 / 8) * (1 / 128) ≤ ‖zc - z₀c‖ ^ 2 * ‖zc - Sc‖ := by
        have h3 : (1 / 8 : ℝ) * (1 / 8) ≤ ‖zc - z₀c‖ ^ 2 := by
          rw [pow_two]; exact mul_le_mul ha ha (by norm_num) (norm_nonneg _)
        exact mul_le_mul h3 hb.le (by norm_num) ha2
      have hle : CM ≤ (2 ^ 19 * CM + 1) * ‖zc - z₀c‖ ^ 2 * ‖zc - Sc‖ := by
        have h7 : (2 ^ 19 * CM + 1) * ((1 / 8 : ℝ) * (1 / 8) * (1 / 128))
            ≤ (2 ^ 19 * CM + 1) * (‖zc - z₀c‖ ^ 2 * ‖zc - Sc‖) :=
          mul_le_mul_of_nonneg_left hab (by positivity)
        have h8 : (2 ^ 19 * CM + 1) * ((1 / 8 : ℝ) * (1 / 8) * (1 / 128))
            = 2 ^ 6 * CM + 1 / 8192 := by norm_num; ring
        nlinarith [h7, h8, hCM]
      linarith [hA, hle]

/-! ## 9. The spike bound -/

private lemma final_arith {m A a b c C : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hC : 0 ≤ C) (hA : 0 < A) (hM : m ≤ C * a ^ 2 * b) (hj : c * a * b ≤ A) :
    m / (A * a) ≤ C / c := by
  rw [div_le_iff₀ (mul_pos hA ha)]
  have h1 : 0 ≤ C / c * a := mul_nonneg (div_nonneg hC hc.le) ha.le
  calc m ≤ C * a ^ 2 * b := hM
    _ = C / c * a * (c * a * b) := by field_simp
    _ ≤ C / c * a * A := mul_le_mul_of_nonneg_left hj h1
    _ = C / c * (A * a) := by ring

theorem lowBad_Tspike_bound (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : UpperHalfPlane) (t : ℝ),
      Work.Asymptotics.HalfFunnel.lowBadSet τ → 0 < t → t ≤ Work.Asymptotics.HalfFunnel.lowT →
      |t - τ.im| ≤ 1 / 8 →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - Work.Asymptotics.HalfFunnel.tpole τ t‖ ≤ C := by
  obtain ⟨c, hcpos, hjb⟩ := jBranch_lower
  obtain ⟨CM, hCM, hMb⟩ := M_bound_region ℓ d hd
  refine ⟨CM / c, by positivity, fun τ t hτ ht htT hw => ?_⟩
  have hne : jInvariantFun (imagAxis t ht) ≠ jInvariantFun (zpole τ) :=
    (jInvariantFun_zpole_ne_imagAxis hτ t ht).symm
  have ha_ne : (((zpole τ : ℍ) : ℂ) - ((imagAxis t ht : ℍ) : ℂ)) ≠ 0 := by
    intro h
    have h' : zpole τ = imagAxis t ht := UpperHalfPlane.ext (sub_eq_zero.mp h)
    exact hne (by rw [h'])
  have hb_ne : (((imagAxis t ht : ℍ) : ℂ) - ((ModularGroup.S • zpole τ : ℍ) : ℂ)) ≠ 0 := by
    intro h
    have h' : ModularGroup.S • zpole τ = imagAxis t ht :=
      UpperHalfPlane.ext (sub_eq_zero.mp h).symm
    refine hne ?_
    rw [← h']
    rw [KernelFacts.jInvariantFun_S_smul]
  have hM' := hMb τ t ht hτ hw
  have hj' : c * ‖((imagAxis t ht : ℍ) : ℂ) - ((zpole τ : ℍ) : ℂ)‖
        * ‖((imagAxis t ht : ℍ) : ℂ) - ((ModularGroup.S • zpole τ : ℍ) : ℂ)‖
      ≤ ‖jInvariantFun (imagAxis t ht) - jInvariantFun (zpole τ)‖ := by
    have h := hjb τ t ht hτ hw hne.symm
    have h2 : ‖jInvariantFun (zpole τ) - jInvariantFun (imagAxis t ht)‖
        = ‖jInvariantFun (imagAxis t ht) - jInvariantFun (zpole τ)‖ :=
      norm_sub_rev (jInvariantFun (zpole τ)) (jInvariantFun (imagAxis t ht))
    rw [h2] at h
    exact h
  have ha_pos : 0 < ‖((imagAxis t ht : ℍ) : ℂ) - ((zpole τ : ℍ) : ℂ)‖ := by
    rw [norm_sub_rev]
    exact norm_pos_iff.mpr ha_ne
  have hb_pos : 0 < ‖((imagAxis t ht : ℍ) : ℂ) - ((ModularGroup.S • zpole τ : ℍ) : ℂ)‖ :=
    norm_pos_iff.mpr hb_ne
  have hA_pos : 0 < ‖jInvariantFun (imagAxis t ht) - jInvariantFun (zpole τ)‖ :=
    lt_of_lt_of_le (mul_pos (mul_pos hcpos ha_pos) hb_pos) hj'
  have hgoal : ‖Kaxis (Kfun ℓ d) τ t - tpole τ t‖
      = ‖Mnum ℓ d τ t ht‖
        / (‖jInvariantFun (imagAxis t ht) - jInvariantFun (zpole τ)‖
            * ‖((imagAxis t ht : ℍ) : ℂ) - ((zpole τ : ℍ) : ℂ)‖) := by
    rw [Kaxis_eq_Kfun ℓ d ht, Kfun_sub_tpole_eq ℓ d hd ht hne, norm_div, norm_neg, norm_mul]
  rw [hgoal]
  exact final_arith ha_pos hb_pos hcpos hCM hA_pos hM' hj'

end Work.HFN.HalfFunnel
