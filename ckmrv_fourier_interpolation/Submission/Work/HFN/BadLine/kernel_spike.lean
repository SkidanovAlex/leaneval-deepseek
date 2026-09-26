import Mathlib
import Submission.Work.Asymptotics.HalfFunnel.lowBadDefs
import Submission.Work.Asymptotics.HalfFunnel.lowBadTspike_defs
import Submission.Work.HFN.HalfFunnel.lowBad_Tspike_bound
import Submission.Work.Asymptotics.HalfFunnel.Kaxis_cusp_of_bounded
import Submission.Work.Asymptotics.KaxisMid.Main
import Submission.Work.Asymptotics.Kaxis_local_coincidence
import Submission.Work.Asymptotics.Kaxis_principal_part_bound
import Submission.Work.HFN.BadLine.off_bound

namespace Work.HFN.BadLine
open Work.Asymptotics  -- ck-hfn-fix: fork moved out of Work.Asymptotics

set_option maxHeartbeats 1000000

open UpperHalfPlane

/-! ## Elementary facts about the translate pole `tpole` -/

/-- The translate pole in `ζ = i t` form. -/
lemma tpole_eq (τ : ℍ) (t : ℝ) (ht : 0 < t) :
    Work.Asymptotics.HalfFunnel.tpole τ t
      = ((Work.Asymptotics.HalfFunnel.tsign τ : ℂ) / (2 * (Real.pi : ℂ)))
          * ((((Work.Kernels.imagAxis t ht : ℍ) : ℂ)
            - ((Work.Asymptotics.HalfFunnel.zpole τ : ℍ) : ℂ)))⁻¹ := by
  have h : ((Work.Asymptotics.HalfFunnel.zpole τ : ℍ) : ℂ)
      = (τ : ℂ) - (Work.Asymptotics.HalfFunnel.tsign τ : ℂ) := by
    rw [Work.Asymptotics.HalfFunnel.zpole, UpperHalfPlane.coe_vadd]
    push_cast
    ring
  have hζ : ((Work.Kernels.imagAxis t ht : ℍ) : ℂ) = (t : ℂ) * Complex.I := rfl
  rw [Work.Asymptotics.HalfFunnel.tpole, div_eq_mul_inv, div_eq_mul_inv, hζ, h]

lemma zpole_im' (τ : ℍ) : (Work.Asymptotics.HalfFunnel.zpole τ).im = τ.im := by
  have h : ((Work.Asymptotics.HalfFunnel.zpole τ : ℍ) : ℂ)
      = (τ : ℂ) - (Work.Asymptotics.HalfFunnel.tsign τ : ℂ) := by
    rw [Work.Asymptotics.HalfFunnel.zpole, UpperHalfPlane.coe_vadd]
    push_cast
    ring
  rw [← UpperHalfPlane.coe_im, h]
  simp

lemma imagAxis_sub_zpole_im (τ : ℍ) (t : ℝ) (ht : 0 < t) :
    ((((Work.Kernels.imagAxis t ht : ℍ) : ℂ)
      - ((Work.Asymptotics.HalfFunnel.zpole τ : ℍ) : ℂ))).im = t - τ.im := by
  have hζ : ((Work.Kernels.imagAxis t ht : ℍ) : ℂ) = (t : ℂ) * Complex.I := rfl
  have h : ((Work.Asymptotics.HalfFunnel.zpole τ : ℍ) : ℂ)
      = (τ : ℂ) - (Work.Asymptotics.HalfFunnel.tsign τ : ℂ) := by
    rw [Work.Asymptotics.HalfFunnel.zpole, UpperHalfPlane.coe_vadd]
    push_cast
    ring
  rw [hζ, h]
  simp [Complex.sub_im, Complex.mul_im, UpperHalfPlane.coe_im]

/-- `‖tpole τ t‖ ≤ 1/(2π lowRho)` as soon as `lowRho ≤ |t - Im τ|`. -/
lemma norm_tpole_le_of_sep {τ : ℍ} {t : ℝ} (ht : 0 < t)
    (h : Work.Asymptotics.HalfFunnel.lowRho ≤ |t - τ.im|) :
    ‖Work.Asymptotics.HalfFunnel.tpole τ t‖
      ≤ 1 / (2 * Real.pi * Work.Asymptotics.HalfFunnel.lowRho) := by
  have hnum : ‖(Work.Asymptotics.HalfFunnel.tsign τ : ℂ) / (2 * Real.pi)‖
      = 1 / (2 * Real.pi) := by
    rw [norm_div]
    have h1 : ‖(Work.Asymptotics.HalfFunnel.tsign τ : ℂ)‖ = 1 := by
      unfold Work.Asymptotics.HalfFunnel.tsign
      split <;> norm_num
    rw [h1, norm_mul, Complex.norm_ofNat, Complex.norm_of_nonneg Real.pi_pos.le]
  have hden := imagAxis_sub_zpole_im τ t ht
  have hge : |t - τ.im| ≤ ‖(((Work.Kernels.imagAxis t ht : ℍ) : ℂ)
      - ((Work.Asymptotics.HalfFunnel.zpole τ : ℍ) : ℂ))‖ := by
    have h1 := Complex.abs_im_le_norm (((Work.Kernels.imagAxis t ht : ℍ) : ℂ)
      - ((Work.Asymptotics.HalfFunnel.zpole τ : ℍ) : ℂ))
    rwa [hden] at h1
  have hpos : 0 < Work.Asymptotics.HalfFunnel.lowRho := by
    rw [Work.Asymptotics.HalfFunnel.lowRho]; norm_num
  have h1 : (‖(((Work.Kernels.imagAxis t ht : ℍ) : ℂ)
      - ((Work.Asymptotics.HalfFunnel.zpole τ : ℍ) : ℂ))‖)⁻¹
      ≤ (Work.Asymptotics.HalfFunnel.lowRho)⁻¹ :=
    inv_anti₀ hpos (le_trans h hge)
  rw [tpole_eq τ t ht, norm_mul, hnum, norm_inv]
  calc (1 / (2 * Real.pi)) * (‖(((Work.Kernels.imagAxis t ht : ℍ) : ℂ)
        - ((Work.Asymptotics.HalfFunnel.zpole τ : ℍ) : ℂ))‖)⁻¹
      ≤ (1 / (2 * Real.pi)) * (Work.Asymptotics.HalfFunnel.lowRho)⁻¹ :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 1 / (2 * Real.pi * Work.Asymptotics.HalfFunnel.lowRho) := by
        field_simp

/-- `Kaxis (Kfun ℓ d) τ t = Kfun ℓ d τ (i t)` for `t > 0`. -/
lemma Kaxis_eq_Kfun' (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (τ : ℍ) {t : ℝ} (ht : 0 < t) :
    Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
      = Work.Kernels.Kfun ℓ d τ (Work.Kernels.imagAxis t ht) := by
  rw [Work.Kernels.Kaxis, dif_pos ht]

/-! ## The compact parameter region `KK` -/

/-- The compact region of the upper half plane containing `lowBadSet`. -/
def KK : Set ℍ := {τ | (3 / 4 : ℝ) ≤ |τ.re| ∧ |τ.re| ≤ 1 ∧ (1 / 2 : ℝ) ≤ τ.im ∧ τ.im ≤ 2}

lemma lowBadSet_subset_KK {τ : ℍ} (hτ : Work.Asymptotics.HalfFunnel.lowBadSet τ) : τ ∈ KK := by
  obtain ⟨hD, h1, h2, h3⟩ := hτ
  have h3' : (3 / 4 : ℝ) ≤ |τ.re| := by
    rcases h3 with h | h
    · exact le_trans (le_of_lt h) (le_abs_self τ.re)
    · have hneg : τ.re < 0 := by linarith
      rw [abs_of_neg hneg]; linarith
  have hre : |τ.re| ≤ 1 := abs_le.mpr ⟨le_of_lt hD.1, le_of_lt hD.2.1⟩
  exact ⟨h3', hre, h1, h2⟩

lemma isCompact_KK : IsCompact KK := by
  have hcl : IsClosed KK := by
    have h1 : IsClosed {τ : ℍ | (3 / 4 : ℝ) ≤ |τ.re|} :=
      isClosed_le continuous_const (continuous_abs.comp UpperHalfPlane.continuous_re)
    have h2 : IsClosed {τ : ℍ | |τ.re| ≤ 1} :=
      isClosed_le (continuous_abs.comp UpperHalfPlane.continuous_re) continuous_const
    have h3 : IsClosed {τ : ℍ | (1 / 2 : ℝ) ≤ τ.im} :=
      isClosed_le continuous_const UpperHalfPlane.continuous_im
    have h4 : IsClosed {τ : ℍ | τ.im ≤ 2} :=
      isClosed_le UpperHalfPlane.continuous_im continuous_const
    have hset : KK = {τ : ℍ | (3 / 4 : ℝ) ≤ |τ.re|} ∩ {τ : ℍ | |τ.re| ≤ 1}
        ∩ {τ : ℍ | (1 / 2 : ℝ) ≤ τ.im} ∩ {τ : ℍ | τ.im ≤ 2} := by
      ext τ; simp only [KK, Set.mem_ofPred_eq, Set.mem_inter_iff]; tauto
    rw [hset]
    exact ((h1.inter h2).inter h3).inter h4
  refine IsCompact.of_isClosed_subset (isCompact_closedBall (UpperHalfPlane.I) 6) hcl ?_
  intro τ hτ
  obtain ⟨-, hre, himlo, him⟩ := hτ
  refine Metric.mem_closedBall.mpr ?_
  have hnum : dist (τ : ℂ) Complex.I ≤ 4 := by
    rw [dist_eq_norm]
    calc ‖(τ : ℂ) - Complex.I‖ ≤ ‖(τ : ℂ)‖ + ‖Complex.I‖ := norm_sub_le _ _
      _ = ‖(τ : ℂ)‖ + 1 := by rw [Complex.norm_I]
      _ ≤ 4 := by
          have hsq : ‖(τ : ℂ)‖ ^ 2 = τ.re ^ 2 + τ.im ^ 2 := by
            rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
            simp only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
            ring
          have h1 : τ.re ^ 2 ≤ 1 := by rw [← sq_abs]; nlinarith [abs_nonneg τ.re, hre]
          have h2 : τ.im ^ 2 ≤ 4 := by nlinarith [show (0:ℝ) < τ.im from lt_of_lt_of_le (by norm_num) himlo]
          nlinarith [norm_nonneg (τ : ℂ)]
  have hI : ((UpperHalfPlane.I : ℍ) : ℂ) = Complex.I := UpperHalfPlane.coe_I
  have hIim : (UpperHalfPlane.I : ℍ).im = 1 := by simp [UpperHalfPlane.I]
  have hdist := UpperHalfPlane.dist_le_dist_coe_div_sqrt τ UpperHalfPlane.I
  rw [hI, hIim] at hdist
  have himpos : (0:ℝ) < τ.im := lt_of_lt_of_le (by norm_num) himlo
  have hden : 0 < Real.sqrt (τ.im * 1) := Real.sqrt_pos.mpr (by linarith)
  have hsqrt : Real.sqrt (1 / 2) ≤ Real.sqrt (τ.im * 1) := by
    apply Real.sqrt_le_sqrt; linarith
  have hs2 : Real.sqrt (τ.im * 1) ^ 2 = τ.im * 1 := Real.sq_sqrt (by linarith : (0:ℝ) ≤ τ.im * 1)
  have hs1 : Real.sqrt (1 / 2) ^ 2 = (1:ℝ) / 2 := Real.sq_sqrt (by norm_num)
  have hle : dist (τ : ℂ) Complex.I / Real.sqrt (τ.im * 1) ≤ 6 := by
    rw [div_le_iff₀ hden]
    nlinarith [hnum, hsqrt, hs2, hs1, Real.sqrt_nonneg (1/2), Real.sqrt_nonneg (τ.im * 1)]
  linarith

lemma KK_im_lower {τ : ℍ} (h : τ ∈ KK) : (1 / 2 : ℝ) ≤ τ.im := h.2.2.1
lemma KK_im_upper {τ : ℍ} (h : τ ∈ KK) : τ.im ≤ 2 := h.2.2.2
lemma KK_re_lower {τ : ℍ} (h : τ ∈ KK) : (3 / 4 : ℝ) ≤ |τ.re| := h.1
lemma KK_re_upper {τ : ℍ} (h : τ ∈ KK) : |τ.re| ≤ 1 := h.2.1
lemma KK_im_pos {τ : ℍ} (h : τ ∈ KK) : 0 < τ.im := lt_of_lt_of_le (by norm_num) (KK_im_lower h)

/-- A point of `KK` with `|Re τ| < 1` lies in CKMRV's fundamental domain `𝒟`. -/
lemma KK_mem_DomainD {τ : ℍ} (hτ : τ ∈ KK) (h : |τ.re| < 1) : τ ∈ DomainD := by
  obtain ⟨hre1, hre2⟩ := abs_lt.mp h
  have him : (1 / 2 : ℝ) ≤ τ.im := KK_im_lower hτ
  have habs : (3 / 4 : ℝ) ≤ |τ.re| := KK_re_lower hτ
  have hre_ne : τ.re ≠ (1 / 2 : ℝ) := by
    intro hc; rw [hc] at habs; norm_num at habs
  have hre_ne' : τ.re ≠ -(1 / 2 : ℝ) := by
    intro hc; rw [hc] at habs; norm_num at habs
  refine ⟨hre1, hre2, ?_, ?_⟩
  · have hsq : ‖(τ : ℂ) - (1 / 2 : ℂ)‖ ^ 2 = (τ.re - 1 / 2) ^ 2 + τ.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.sub_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
      norm_num
      ring
    have him' : (1 / 2 : ℝ) ^ 2 ≤ τ.im ^ 2 := by nlinarith
    have hre' : 0 < (τ.re - 1 / 2) ^ 2 := by
      have hne : τ.re - 1 / 2 ≠ 0 := sub_ne_zero.mpr hre_ne
      positivity
    nlinarith [sq_nonneg (‖(τ : ℂ) - (1 / 2 : ℂ)‖), norm_nonneg ((τ : ℂ) - (1 / 2 : ℂ))]
  · have hsq : ‖(τ : ℂ) + (1 / 2 : ℂ)‖ ^ 2 = (τ.re + 1 / 2) ^ 2 + τ.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [Complex.add_re, Complex.add_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
      norm_num
      ring
    have him' : (1 / 2 : ℝ) ^ 2 ≤ τ.im ^ 2 := by nlinarith
    have hre' : (1 / 4 : ℝ) ^ 2 ≤ (τ.re + 1 / 2) ^ 2 := by
      rcases le_or_gt 0 τ.re with hp | hn
      · have h1 : (3/4 : ℝ) ≤ τ.re := by simpa [abs_of_nonneg hp] using habs
        nlinarith
      · have h1 : (3/4 : ℝ) ≤ -τ.re := by simpa [abs_of_neg hn] using habs
        nlinarith
    nlinarith [sq_nonneg (‖(τ : ℂ) + (1 / 2 : ℂ)‖), norm_nonneg ((τ : ℂ) + (1 / 2 : ℂ))]

/-! ## The coincidence set for `τ ∈ KK` -/

lemma tsign_eq (τ : ℍ) :
    Work.Asymptotics.HalfFunnel.tsign τ = 1 ∨ Work.Asymptotics.HalfFunnel.tsign τ = -1 := by
  unfold Work.Asymptotics.HalfFunnel.tsign
  split <;> norm_num

lemma imagAxis_re_zero (t : ℝ) (ht : 0 < t) :
    (((Work.Kernels.imagAxis t ht : ℍ) : ℂ)).re = 0 := by
  simp [Work.Kernels.imagAxis]

/-- **A coincidence of the contour with the orbit of `τ ∈ KK` forces `Re τ = ±1`.** -/
lemma coinc_re {τ : ℍ} (hτ : τ ∈ KK) {t : ℝ} (ht : 0 < t)
    (h : Work.Kernels.jInvariantFun τ
      = Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)) :
    τ.re = 1 ∨ τ.re = -1 := by
  have habs : |τ.re| = 1 := by
    by_contra hne
    have hlt : |τ.re| < 1 := lt_of_le_of_ne (KK_re_upper hτ) hne
    have hD : τ ∈ DomainD := KK_mem_DomainD hτ hlt
    obtain ⟨γ, hγ⟩ := Work.Asymptotics.jInvariantFun_eq_smul_of_eq h
    have h1 : γ⁻¹ • τ = Work.Kernels.imagAxis t ht := by
      rw [← hγ, inv_smul_smul]
    have hre0 : (((γ⁻¹ • τ : ℍ) : ℂ)).re = 0 := by rw [h1]; exact imagAxis_re_zero t ht
    have h0 := Work.Asymptotics.orbit_imagAxis_of_mem_DomainD τ hD γ⁻¹ hre0
    have h2 : (3 / 4 : ℝ) ≤ |(0 : ℝ)| := by rw [← h0]; exact KK_re_lower hτ
    norm_num at h2
  rcases lt_trichotomy τ.re 0 with hneg | hzero | hpos
  · rw [abs_of_neg hneg] at habs; right; linarith
  · rw [hzero, abs_zero] at habs; exact absurd habs (by norm_num)
  · rw [abs_of_pos hpos] at habs; left; linarith

/-- `S • i t = i / t` on the imaginary axis. -/
lemma S_smul_imagAxis (t : ℝ) (ht : 0 < t) :
    ModularGroup.S • Work.Kernels.imagAxis t ht
      = Work.Kernels.imagAxis (1 / t) (by positivity) := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.modular_S_smul]
  show (-((t : ℂ) * Complex.I))⁻¹ = ((1 / t : ℝ) : ℂ) * Complex.I
  rw [inv_neg, mul_inv, Complex.inv_I]
  push_cast
  field_simp

lemma imagAxis_coe' (t : ℝ) (ht : 0 < t) :
    ((Work.Kernels.imagAxis t ht : ℍ) : ℂ) = (t : ℂ) * Complex.I := rfl

lemma imagAxis_eq_of_eq {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (h : Work.Kernels.imagAxis s hs = Work.Kernels.imagAxis t ht) : s = t := by
  have h1 : ((Work.Kernels.imagAxis s hs : ℍ) : ℂ)
      = ((Work.Kernels.imagAxis t ht : ℍ) : ℂ) := congrArg (fun z : ℍ => (z : ℂ)) h
  rw [imagAxis_coe', imagAxis_coe'] at h1
  have := congrArg Complex.im h1
  simpa using this

/-- **Two points of the imaginary axis have the same `j`-value iff they agree or are `S`-related.** -/
lemma imagAxis_j_eq {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (h : Work.Kernels.jInvariantFun (Work.Kernels.imagAxis s hs)
      = Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)) :
    s = t ∨ s = 1 / t := by
  obtain ⟨γ, hγ⟩ := Work.Asymptotics.jInvariantFun_eq_smul_of_eq h
  have h4 := Work.Asymptotics.eq_one_or_neg_one_or_S_of_smul_imagAxis (t := t) (u := s) ht hs (γ := γ) hγ
  rcases h4 with h1 | h1 | h1 | h1
  · left; rw [h1, one_smul] at hγ; exact (imagAxis_eq_of_eq ht hs hγ).symm
  · left
    have h5 : ((-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) • Work.Kernels.imagAxis t ht)
        = Work.Kernels.imagAxis t ht := by
      apply UpperHalfPlane.ext; simp
    rw [h1, h5] at hγ; exact (imagAxis_eq_of_eq ht hs hγ).symm
  · right
    rw [h1, S_smul_imagAxis t ht] at hγ
    exact (imagAxis_eq_of_eq (by positivity) hs hγ).symm
  · right
    have h5 : ((-ModularGroup.S) • Work.Kernels.imagAxis t ht)
        = ModularGroup.S • Work.Kernels.imagAxis t ht := by
      apply UpperHalfPlane.ext; simp
    rw [h1, h5, S_smul_imagAxis t ht] at hγ
    exact (imagAxis_eq_of_eq (by positivity) hs hγ).symm

/-- For `τ` with `Re τ = ±1`: `j τ = j (i Im τ)`. -/
lemma jInvariantFun_eq_imagAxis_of_re_abs_one {τ : UpperHalfPlane}
    (hre : τ.re = 1 ∨ τ.re = -1) :
    Work.Kernels.jInvariantFun τ
      = Work.Kernels.jInvariantFun (Work.Kernels.imagAxis τ.im τ.im_pos) := by
  have hvadd : τ = (τ.re : ℝ) +ᵥ (Work.Kernels.imagAxis τ.im τ.im_pos : UpperHalfPlane) := by
    refine UpperHalfPlane.ext ?_
    simp only [UpperHalfPlane.coe_vadd, Work.Kernels.imagAxis]
    rw [← Complex.re_add_im (τ : ℂ), UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  conv_lhs => rw [hvadd]
  rcases hre with h | h
  · rw [h]; exact Work.Kernels.KernelFacts.jInvariantFun_vadd_one _
  · rw [h]
    have h3 := Work.Kernels.KernelFacts.jInvariantFun_vadd_one
      ((-1 : ℝ) +ᵥ (Work.Kernels.imagAxis τ.im τ.im_pos : UpperHalfPlane))
    rw [show (1 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ (Work.Kernels.imagAxis τ.im τ.im_pos : UpperHalfPlane))
        = (Work.Kernels.imagAxis τ.im τ.im_pos : UpperHalfPlane) from by
      rw [← add_vadd]; norm_num] at h3
    exact h3.symm

/-- **The coincidence times for `τ ∈ KK` with `Re τ = ±1`.** -/
lemma coinc_t {τ : UpperHalfPlane} (hτ : τ ∈ KK) {t : ℝ} (ht : 0 < t)
    (h : Work.Kernels.jInvariantFun τ
      = Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)) :
    t = τ.im ∨ t = 1 / τ.im := by
  have hτs := jInvariantFun_eq_imagAxis_of_re_abs_one (coinc_re hτ ht h)
  exact imagAxis_j_eq ht τ.im_pos (h.symm.trans hτs)

/-! ## The two remaining analytic estimates

The target inequality is `‖K(τ,it) - tpole τ t‖ ≤ C`; off the coincidence set this is
`‖M(τ,it)‖ / (‖j(it) - j τ‖ ‖it - z₀‖)` with
`M(τ,ζ) = A(τ,ζ)(ζ - z₀) + (n/2π)(j ζ - j z₀)` (`Work.Asymptotics.remainder_eq`), and the two
estimates below are exactly the numerator bound (using the vanishing of `M` to second order at
the pole `z₀` and to first order at the `S`-conjugate `S z₀`) and the two-branch lower bound for
the `j`-difference. -/

/-- `tsign τ = 1 ∨ tsign τ = -1`. -/
lemma tsign_eq_one_or_neg_one (τ : ℍ) :
    Work.Asymptotics.HalfFunnel.tsign τ = 1 ∨ Work.Asymptotics.HalfFunnel.tsign τ = -1 :=
  tsign_eq τ

/-- The integer `n` with `(n : ℂ) = tsign τ`, together with `n = ±1`. -/
lemma tsign_intCast (τ : ℍ) :
    ∃ n : ℤ, (n = 1 ∨ n = -1) ∧ (Work.Asymptotics.HalfFunnel.tsign τ : ℂ) = (n : ℂ) := by
  rcases tsign_eq τ with h | h
  · exact ⟨1, Or.inl rfl, by rw [h]; norm_num⟩
  · exact ⟨-1, Or.inr rfl, by rw [h]; norm_num⟩

lemma zpole_eq_vadd (τ : ℍ) {n : ℤ} (hn : (Work.Asymptotics.HalfFunnel.tsign τ : ℂ) = (n : ℂ)) :
    Work.Asymptotics.HalfFunnel.zpole τ = ((-(n : ℝ)) +ᵥ τ) := by
  rw [Work.Asymptotics.HalfFunnel.zpole]
  congr 1
  have h : (Work.Asymptotics.HalfFunnel.tsign τ : ℂ) = (n : ℂ) := hn
  have h2 : Work.Asymptotics.HalfFunnel.tsign τ = (n : ℝ) := by
    exact_mod_cast h
  rw [h2]

lemma jInvariantFun_zpole (τ : ℍ) :
    Work.Kernels.jInvariantFun (Work.Asymptotics.HalfFunnel.zpole τ)
      = Work.Kernels.jInvariantFun τ := by
  obtain ⟨n, hn, hcast⟩ := tsign_intCast τ
  rw [zpole_eq_vadd τ hcast]
  exact Work.Asymptotics.jInvariantFun_neg_vadd_int n hn τ

lemma jInvariantFun_zpole_ne_imagAxis {τ : ℍ} (hτ : Work.Asymptotics.HalfFunnel.lowBadSet τ)
    (t : ℝ) (ht : 0 < t) :
    Work.Kernels.jInvariantFun (Work.Asymptotics.HalfFunnel.zpole τ)
      ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) := by
  intro h
  have hτK : τ ∈ KK := lowBadSet_subset_KK hτ
  have h2 : Work.Kernels.jInvariantFun τ
      = Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) := by
    rw [← jInvariantFun_zpole τ]; exact h
  have h3 := coinc_re hτK ht h2
  obtain ⟨hD, -, -, -⟩ := hτ
  have h4 := hD.2.1
  rcases h3 with h3 | h3 <;> linarith [hD.1]

/-- **The pole-subtracted kernel identity**, in the form used by the target. -/
lemma Kfun_sub_tpole_eq (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {τ : ℍ} {t : ℝ} (ht : 0 < t)
    (hne : Work.Kernels.jInvariantFun (Work.Asymptotics.HalfFunnel.zpole τ)
      ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)) :
    Work.Kernels.Kfun ℓ d τ (Work.Kernels.imagAxis t ht)
        - Work.Asymptotics.HalfFunnel.tpole τ t
      = - Work.Asymptotics.HalfFunnel.Mnum ℓ d τ t ht
        / ((Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)
              - Work.Kernels.jInvariantFun (Work.Asymptotics.HalfFunnel.zpole τ))
            * (((Work.Kernels.imagAxis t ht : ℍ) : ℂ)
                - ((Work.Asymptotics.HalfFunnel.zpole τ : ℍ) : ℂ))) := by
  obtain ⟨n, hn, hcast⟩ := tsign_intCast τ
  have hzp : Work.Asymptotics.HalfFunnel.zpole τ = ((-(n : ℝ)) +ᵥ τ) := zpole_eq_vadd τ hcast
  have hne' : Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)
      ≠ Work.Kernels.jInvariantFun (((-(n : ℝ)) +ᵥ τ : ℍ)) := by
    rw [← hzp]; exact hne.symm
  have h1 : Work.Asymptotics.HalfFunnel.tpole τ t
      = ((n : ℂ) / (2 * (Real.pi : ℂ)))
          * ((((Work.Kernels.imagAxis t ht : ℍ) : ℂ) - (((-(n : ℝ)) +ᵥ τ : ℍ) : ℂ)))⁻¹ := by
    rw [tpole_eq τ t ht, hzp, hcast]
  have h2 : Work.Asymptotics.HalfFunnel.Mnum ℓ d τ t ht
      = Work.Asymptotics.AfunFun ℓ d τ (Work.Kernels.imagAxis t ht)
          * (((Work.Kernels.imagAxis t ht : ℍ) : ℂ) - (((-(n : ℝ)) +ᵥ τ : ℍ) : ℂ))
        + ((n : ℂ) / (2 * (Real.pi : ℂ)))
          * (Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)
              - Work.Kernels.jInvariantFun (((-(n : ℝ)) +ᵥ τ : ℍ))) := by
    rw [Work.Asymptotics.HalfFunnel.Mnum, hzp, hcast]
  have h3 : (Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)
        - Work.Kernels.jInvariantFun (Work.Asymptotics.HalfFunnel.zpole τ))
      = (Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)
        - Work.Kernels.jInvariantFun (((-(n : ℝ)) +ᵥ τ : ℍ))) := by rw [hzp]
  have h4 : ((((Work.Kernels.imagAxis t ht : ℍ) : ℂ)
        - ((Work.Asymptotics.HalfFunnel.zpole τ : ℍ) : ℂ)))
      = ((((Work.Kernels.imagAxis t ht : ℍ) : ℂ) - (((-(n : ℝ)) +ᵥ τ : ℍ) : ℂ))) := by rw [hzp]
  rw [h1, h2, h3, h4, Work.Asymptotics.remainder_eq ℓ d hd τ (Work.Kernels.imagAxis t ht) n hn hne']

/-- **The translate-pole decomposition of the CKMRV kernel on the bad-line set.**

For `τ` in `lowBadSet` (`τ ∈ 𝒟`, `1/2 ≤ Im τ ≤ 2`, `|Re τ| > 3/4`) the contour point `z = it`
(`0 < t ≤ lowT = 3`) is at distance `|t - Im τ|` from the genuine simple pole `z = τ - n` of
`z ↦ K^{(d)}(τ,z)`, `n = tsign τ = sign(Re τ)`, whose principal part is the explicit rational
function `tpole τ t = (n/2π)/(it - (τ - n))`; subtracting it leaves a uniformly bounded remainder.

On the spike window `|t - Im τ| ≤ 1/8` this is `Work.Asymptotics.HalfFunnel.lowBad_Tspike_bound`;
off the spike we combine the boundedness of `K` with the elementary bound on `tpole`
(`norm_tpole_le_of_sep`). -/
theorem kernel_spike (ℓ : Work.Kernels.LogLambdaData) (d : Nat) (hd : d = 8 ∨ d = 24) :
    ∃ C : Real, 0 ≤ C ∧ ∀ (τ : UpperHalfPlane) (t : Real),
      Work.Asymptotics.HalfFunnel.lowBadSet τ → 0 < t → t ≤ Work.Asymptotics.HalfFunnel.lowT →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
        - Work.Asymptotics.HalfFunnel.tpole τ t‖ ≤ C := by
  obtain ⟨C₁, hC₁, h₁⟩ := Work.HFN.HalfFunnel.lowBad_Tspike_bound ℓ d hd
  obtain ⟨C₂, hC₂, h₂⟩ := Work.HFN.BadLine.off_bound ℓ d hd
  refine ⟨max C₁ (C₂ + 1 / (2 * Real.pi * Work.Asymptotics.HalfFunnel.lowRho)),
    le_max_of_le_left hC₁, fun τ t hτ ht hT => ?_⟩
  rcases le_or_gt |t - τ.im| (1 / 8) with hsp | hoff
  · exact le_trans (h₁ τ t hτ ht hT hsp) (le_max_left _ _)
  · have hb := h₂ τ t hτ ht hT hoff.le
    have hp := norm_tpole_le_of_sep (τ := τ) (t := t) ht
      (by rw [Work.Asymptotics.HalfFunnel.lowRho]; exact hoff.le)
    have h3 : ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
        - Work.Asymptotics.HalfFunnel.tpole τ t‖
        ≤ ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖
          + ‖Work.Asymptotics.HalfFunnel.tpole τ t‖ := by
      simpa using norm_sub_le (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t)
        (Work.Asymptotics.HalfFunnel.tpole τ t)
    refine le_trans h3 (le_trans (add_le_add hb hp) ?_)
    exact le_max_right _ _

end Work.HFN.BadLine
