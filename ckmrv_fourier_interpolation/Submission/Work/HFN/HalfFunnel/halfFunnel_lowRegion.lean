import Mathlib
import Submission.Work.Asymptotics.DomainD
import Submission.Work.HFN.kernelTransform_seminorm_on_compact
import Submission.Work.HFN.HalfFunnel.lowRegion_badLine
import Submission.Work.HFN.HalfFunnel.lowRegion_tangency

noncomputable section

namespace Work.HFN.HalfFunnel
open Work.Asymptotics Work.Asymptotics.HalfFunnel  -- ck-hfn-fix: fork moved out of Work.Asymptotics

open UpperHalfPlane

/-- The base point `i` of `ℍ`. -/
def hlrIPt : ℍ := ⟨Complex.I, by rw [Complex.I_im]; norm_num⟩

lemma hlrIPt_im : hlrIPt.im = 1 := by simp [hlrIPt]

lemma hlrIPt_coe : (hlrIPt : ℂ) = Complex.I := rfl

/-- The tangency point `1/2 + i/2 ∈ ∂𝒟` as a complex number. -/
def hlrCtanPlus : ℂ := (1 / 2 : ℝ) + (1 / 2 : ℝ) * Complex.I

/-- The tangency point `-1/2 + i/2 ∈ ∂𝒟` as a complex number. -/
def hlrCtanMinus : ℂ := (-(1 / 2) : ℝ) + (1 / 2 : ℝ) * Complex.I

/-- The part of the low strip `{τ ∈ 𝒟 : 1/2 ≤ Im τ ≤ 2}` whose closure is compact inside `𝒟`:
away from the bad lines `Re τ = ±1` and from the two tangency points `±1/2 + i/2`. -/
def hlrLowBulk : Set ℍ :=
  {τ | τ ∈ Work.Asymptotics.DomainD ∧ (1 : ℝ) / 2 ≤ τ.im ∧ τ.im ≤ 2 ∧ |τ.re| ≤ 3 / 4 ∧
    (1 : ℝ) / 8 ≤ ‖(τ : ℂ) - hlrCtanPlus‖ ∧ (1 : ℝ) / 8 ≤ ‖(τ : ℂ) - hlrCtanMinus‖}

/-- The "Euclidean rectangle" part of the low strip: `1/2 ≤ Im τ ≤ 2`, `|Re τ| ≤ 3/4`. -/
def hlrLowStrip : Set ℍ := {τ | (1 : ℝ) / 2 ≤ τ.im ∧ τ.im ≤ 2 ∧ |τ.re| ≤ 3 / 4}

lemma hlr_isClosed_lowStrip : IsClosed hlrLowStrip := by
  have h1 : IsClosed {τ : ℍ | (1 : ℝ) / 2 ≤ τ.im} :=
    isClosed_le continuous_const UpperHalfPlane.continuous_im
  have h2 : IsClosed {τ : ℍ | τ.im ≤ 2} :=
    isClosed_le UpperHalfPlane.continuous_im continuous_const
  have h3 : IsClosed {τ : ℍ | |τ.re| ≤ 3 / 4} :=
    isClosed_le (continuous_abs.comp UpperHalfPlane.continuous_re) continuous_const
  have h : hlrLowStrip = {τ : ℍ | (1 : ℝ) / 2 ≤ τ.im} ∩ {τ : ℍ | τ.im ≤ 2}
      ∩ {τ : ℍ | |τ.re| ≤ 3 / 4} := by
    ext τ; simp [hlrLowStrip, and_assoc]
  rw [h]
  exact (h1.inter h2).inter h3

lemma hlr_lowStrip_bounded : Bornology.IsBounded hlrLowStrip := by
  rw [Metric.isBounded_iff_subset_closedBall hlrIPt]
  refine ⟨10, fun τ hτ => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hτ
  rw [Metric.mem_closedBall]
  have hnum : ‖(τ : ℂ) - Complex.I‖ ≤ 5 := by
    have h := Complex.norm_le_abs_re_add_abs_im ((τ : ℂ) - Complex.I)
    rw [show ((τ : ℂ) - Complex.I).re = τ.re by simp,
      show ((τ : ℂ) - Complex.I).im = τ.im - 1 by simp] at h
    have h4 : |τ.im - 1| ≤ 2 := by
      rw [abs_le]; constructor <;> linarith
    have h5 : |τ.re| ≤ 3 / 4 := h3
    linarith
  have hstep : dist τ hlrIPt ≤ ‖(τ : ℂ) - Complex.I‖ / Real.sqrt (τ.im * hlrIPt.im) := by
    simpa [hlrIPt_coe, Complex.dist_eq] using UpperHalfPlane.dist_le_dist_coe_div_sqrt τ hlrIPt
  have hsqrt : (1 : ℝ) / 2 ≤ Real.sqrt (τ.im * hlrIPt.im) := by
    rw [hlrIPt_im, mul_one]
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    nlinarith [h1]
  calc dist τ hlrIPt ≤ ‖(τ : ℂ) - Complex.I‖ / Real.sqrt (τ.im * hlrIPt.im) := hstep
    _ ≤ 5 / (1 / 2 : ℝ) := div_le_div₀ (by norm_num) hnum (by norm_num) hsqrt
    _ = 10 := by norm_num

lemma hlr_isCompact_lowStrip : IsCompact hlrLowStrip := by
  rw [Metric.isCompact_iff_isClosed_bounded]
  exact ⟨hlr_isClosed_lowStrip, hlr_lowStrip_bounded⟩

lemma hlr_lowBulk_subset_lowStrip : hlrLowBulk ⊆ hlrLowStrip :=
  fun τ hτ => ⟨hτ.2.1, hτ.2.2.1, hτ.2.2.2.1⟩

lemma hlr_closure_lowBulk_subset_lowStrip : closure hlrLowBulk ⊆ hlrLowStrip :=
  closure_minimal hlr_lowBulk_subset_lowStrip hlr_isClosed_lowStrip

lemma hlr_isCompact_closure_lowBulk : IsCompact (closure hlrLowBulk) :=
  IsCompact.of_isClosed_subset hlr_isCompact_lowStrip isClosed_closure hlr_closure_lowBulk_subset_lowStrip

/-- A complex number in the closed upper half disc of radius `1/2` with `Im ≥ 1/2` is `i/2`. -/
lemma hlr_eq_half_I_of {w : ℂ} (him : (1 : ℝ) / 2 ≤ w.im) (hn : ‖w‖ ≤ 1 / 2) :
    w = (1 / 2 : ℂ) * Complex.I := by
  have him' : w.im = 1 / 2 := by
    have h1 : |w.im| ≤ ‖w‖ := Complex.abs_im_le_norm w
    rw [abs_of_nonneg (by linarith)] at h1
    linarith
  have hre : w.re = 0 := by
    have h2 : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
    nlinarith [sq_nonneg w.re, norm_nonneg w]
  rw [← Complex.re_add_im w, hre, him']
  norm_num

lemma hlr_closure_lowBulk_subset_DomainD : closure hlrLowBulk ⊆ Work.Asymptotics.DomainD := by
  have hP : closure hlrLowBulk ⊆ {τ : ℍ | (1 : ℝ) / 8 ≤ ‖(τ : ℂ) - hlrCtanPlus‖} :=
    closure_minimal (fun σ hσ => hσ.2.2.2.2.1)
      (isClosed_le continuous_const (continuous_norm.comp (continuous_coe.sub continuous_const)))
  have hM : closure hlrLowBulk ⊆ {τ : ℍ | (1 : ℝ) / 8 ≤ ‖(τ : ℂ) - hlrCtanMinus‖} :=
    closure_minimal (fun σ hσ => hσ.2.2.2.2.2)
      (isClosed_le continuous_const (continuous_norm.comp (continuous_coe.sub continuous_const)))
  intro τ hτ
  obtain ⟨h1, h2, h3⟩ := hlr_closure_lowBulk_subset_lowStrip hτ
  have hP' := hP hτ
  have hM' := hM hτ
  have hre1 : -1 < τ.re := by have := abs_le.mp h3; linarith [this.1]
  have hre2 : τ.re < 1 := by have := abs_le.mp h3; linarith [this.2]
  -- the disc `|z -+ 1/2| ≤ 1/2` meets `Im ≥ 1/2` only at the tangency points
  have hplus : (1 : ℝ) / 2 < ‖(τ : ℂ) - (1 / 2 : ℂ)‖ := by
    by_contra hcon
    push_neg at hcon
    have hw := hlr_eq_half_I_of (w := (τ : ℂ) - (1 / 2 : ℂ)) (by simpa using h1) hcon
    have hcoe : (τ : ℂ) = hlrCtanPlus := by
      have hre : τ.re = 1 / 2 := by
        have h := congrArg Complex.re hw
        simp only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, Complex.sub_re, Complex.mul_re,
          Complex.I_re, Complex.I_im, mul_one, mul_zero, sub_zero] at h
        norm_num at h
        linarith
      have him : τ.im = 1 / 2 := by
        have h := congrArg Complex.im hw
        simp only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, Complex.sub_im, Complex.mul_im,
          Complex.I_re, Complex.I_im, mul_one, mul_zero, sub_zero, zero_add] at h
        norm_num at h
        linarith
      apply Complex.ext
      · simpa [hlrCtanPlus] using hre
      · simpa [hlrCtanPlus] using him
    have hzero : ‖(τ : ℂ) - hlrCtanPlus‖ = 0 := by rw [← hcoe, sub_self, norm_zero]
    have hPb : (1 : ℝ) / 8 ≤ ‖(τ : ℂ) - hlrCtanPlus‖ := hP'
    linarith [hPb, hzero]
  have hminus : (1 : ℝ) / 2 < ‖(τ : ℂ) + (1 / 2 : ℂ)‖ := by
    by_contra hcon
    push_neg at hcon
    have hw := hlr_eq_half_I_of (w := (τ : ℂ) + (1 / 2 : ℂ)) (by simpa using h1) hcon
    have hcoe : (τ : ℂ) = hlrCtanMinus := by
      have hre : τ.re = -(1 / 2) := by
        have h := congrArg Complex.re hw
        simp only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, Complex.add_re, Complex.mul_re,
          Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero] at h
        norm_num at h
        linarith
      have him : τ.im = 1 / 2 := by
        have h := congrArg Complex.im hw
        simp only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, Complex.add_im, Complex.mul_im,
          Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add] at h
        norm_num at h
        linarith
      apply Complex.ext
      · simpa [hlrCtanMinus] using hre
      · simpa [hlrCtanMinus] using him
    have hzero : ‖(τ : ℂ) - hlrCtanMinus‖ = 0 := by rw [← hcoe, sub_self, norm_zero]
    have hMb : (1 : ℝ) / 8 ≤ ‖(τ : ℂ) - hlrCtanMinus‖ := hM'
    linarith [hMb, hzero]
  exact ⟨hre1, hre2, hplus, hminus⟩



/-- **Coverage of the low strip** by the relatively compact bulk part, the two bad-line parts
`Re τ > 3/4`, `Re τ < -3/4`, and the two tangency neighbourhoods. -/
lemma hlr_lowRegion_cover {τ : ℍ} (hτ : τ ∈ Work.Asymptotics.DomainD) (h1 : (1 : ℝ) / 2 ≤ τ.im)
    (h2 : τ.im ≤ 2) :
    τ ∈ hlrLowBulk ∨ 3 / 4 < τ.re ∨ τ.re < -(3 / 4) ∨
      ‖(τ : ℂ) - hlrCtanPlus‖ < 1 / 8 ∨ ‖(τ : ℂ) - hlrCtanMinus‖ < 1 / 8 := by
  by_cases hp : ‖(τ : ℂ) - hlrCtanPlus‖ < 1 / 8
  · exact Or.inr (Or.inr (Or.inr (Or.inl hp)))
  · by_cases hm : ‖(τ : ℂ) - hlrCtanMinus‖ < 1 / 8
    · exact Or.inr (Or.inr (Or.inr (Or.inr hm)))
    · push_neg at hp hm
      by_cases h3 : τ.re ≤ 3 / 4
      · by_cases h4 : -(3 / 4) ≤ τ.re
        · exact Or.inl ⟨hτ, h1, h2, abs_le.mpr ⟨h4, h3⟩, hp, hm⟩
        · push_neg at h4
          exact Or.inr (Or.inr (Or.inl h4))
      · push_neg at h3
        exact Or.inr (Or.inl h3)

/-- **The low-strip `r`-seminorm bound on the relatively compact part.**  On `closure hlrLowBulk`
(compact inside `𝒟`) this is `Work.Asymptotics.kernelTransform_seminorm_on_compact`. -/
theorem hlr_lowRegion_bulk_bound (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∀ k l : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : UpperHalfPlane) (r : ℝ), τ ∈ hlrLowBulk →
      (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ =>
        Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) τ s) r‖ ≤ C := by
  intro k l
  obtain ⟨C, hC, h⟩ :=
    kernelTransform_seminorm_on_compact ℓ d hd hlr_isCompact_closure_lowBulk
      hlr_closure_lowBulk_subset_DomainD k l
  exact ⟨C, hC, fun τ r hτ => h τ r (subset_closure hτ)⟩

/-- **The low half of the CKMRV half-funnel `r`-seminorm bound** (declare in namespace
`Work.Asymptotics`).  The region `S = {τ ∈ 𝒟 : 1/2 ≤ Im τ ≤ 2}` is bounded (`‖τ‖ ≤ √5`), so the
conclusion is equivalent to a single constant: `∀ τ ∈ S, ∀ r, |r|^k ‖∂_r^l F(τ,·)(r)‖ ≤ C`.
Together with the funnel bound `Work.Asymptotics.kernelTransform_seminorm_funnel` (`2 ≤ Im τ`)
it gives the target `Work.Asymptotics.kernelTransform_seminorm_halfFunnel`, whose assembly is
already written in `Submission/Work/Asymptotics/kernelTransform_seminorm_halfFunnel.lean`.

The inputs below are all proved without added axioms (all importable) and the strategy: `S` is **not** relatively compact in `𝒟`
(`(1-ε) + i/2 ∈ 𝒟 → 1 + i/2 ∉ 𝒟`; the tangency points `±1/2 + i/2` lie in `∂𝒟`), so
`kernelTransform_seminorm_on_compact` does not suffice.  Split `S` into three parts:

1. `{|Re τ ∓ 1| ≥ 1/4, dist(τ, ±1/2+i/2) ≥ 1/8}`: closure compact inside `𝒟` ⟹
   `Work.Asymptotics.kernelTransform_seminorm_on_compact`.
2. near the bad lines `Re τ = ±1` (`3/4 < τ.re` resp. `τ.re < -3/4`): the contour passes the pole
   `z = τ ∓ 1` at distance `|Re τ ∓ 1|`; the machine exists and is proved:
   `Work.Asymptotics.middle_bound_near_bad_line`,
   `Work.Asymptotics.tail_integral_bound_near_bad_line`,
   `Work.Asymptotics.small_t_integral_bound_near_bad_line`, plus the assembly plan written in the
   header of `Submission/Work/Asymptotics/norm_kernelTransform_le_near_bad_line.lean`.  Apply it
   to the `r`-derivatives too (differentiating under the integral sign brings down extra factors
   `(π t)^m`, absorbed by enlarging the window and the polynomial exponent).
3. near the tangency points (`|τ.re ∓ 1/2| < 1/8`, `1/2 ≤ Im τ ≤ 5/8`): here all poles of
   `z ↦ K(τ,z)` stay at distance `≥ 1/10` from the contour — machine-checked enumeration of
   `SL(2,ℤ)`-words of length `≤ 11` (using the six-dimensional representation of `R/𝓘` to evaluate
   `φ`): for `τ = 1/2 + i(1/2+δ)` the closest poles are `α = S T⁷ S T⁻¹` at `|Re z| = 0.11`, the
   translate poles `z = τ - n` at `|Re z| ≥ 1/2`, and no pole has height `≥ 1` — so `Kaxis` is
   uniformly bounded on the contour; the flatness at `t → 0⁺` follows from
   `Work.Asymptotics.growthPrefactor_lower_atZero` plus the polynomial bound of the cleared kernel
   (`Work.Asymptotics.KClear_mg2`/`contour_bound_Kfun`), and the cusp-`i∞` expansion for large `t`.
   Note `Work.Asymptotics.paperLayer_seminorm` is proved for *any* region on which its two
   hypotheses `hflat` and `hT` hold — its proof is region-generic (no compactness is used) — so it
   can be re-run for this region, combined with `Work.Asymptotics.kernelTransform_seminorm_of_layer`
   and `Work.Asymptotics.paperLayer_agreement`.  For `d = 24` and `0 < r² ≤ 2` the integrand is
   non-integrable and the transform is the junk value `0`, which is harmless. -/
theorem halfFunnel_lowRegion (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∀ k l : ℕ, ∃ α β γ δ : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γ ∧ 0 ≤ δ ∧
      ∀ (τ : UpperHalfPlane) (r : ℝ), τ ∈ Work.Asymptotics.DomainD → (1 : ℝ) / 2 ≤ τ.im →
        τ.im ≤ 2 →
        (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ =>
          Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) τ s) r‖
          ≤ α * (τ.im) ^ (-β) + γ * (‖(τ : ℂ)‖) ^ δ := by
  intro k l
  obtain ⟨Cb, hCb, hb⟩ := hlr_lowRegion_bulk_bound ℓ d hd k l
  obtain ⟨Cbl, hCbl, hbl⟩ := lowRegion_badLine ℓ d hd k l
  obtain ⟨Ct, hCt, ht⟩ := lowRegion_tangency ℓ d hd k l
  refine ⟨Cb + Cbl + Ct, 0, 0, 0, by linarith, le_rfl, le_rfl, le_rfl, ?_⟩
  intro τ r hτ h1 h2
  have key : (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ =>
        Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) τ s) r‖ ≤ Cb + Cbl + Ct := by
    rcases hlr_lowRegion_cover hτ h1 h2 with hbulk | hbad | hbadneg | htanP | htanM
    · have := hb τ r hbulk; linarith
    · have := hbl τ r hτ h1 h2 (Or.inl hbad); linarith
    · have := hbl τ r hτ h1 h2 (Or.inr hbadneg); linarith
    · have := ht τ r hτ h1 h2 (Or.inl htanP); linarith
    · have := ht τ r hτ h1 h2 (Or.inr htanM); linarith
  simp only [neg_zero, Real.rpow_zero, mul_one, zero_mul, add_zero]
  exact key


end Work.HFN.HalfFunnel
