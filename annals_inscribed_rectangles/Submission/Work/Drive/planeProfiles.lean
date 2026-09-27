import Mathlib

/-!
# The radial profiles of the plane chart

The disk model `Q : ℂ → Y` of the capped plane of a smooth Jordan curve is built in the transport
chapter out of the *symmetric chord data* of `γ` (the even descents of `symmMid` and `symmWC`), read
in the **band coordinate** `τ = (half-separation)²`.  This file supplies the two *radial profiles* of
that construction, which are the only places where the disk parameter `z` itself (rather than the
chord data) enters:

* `Work.Drive.wCollapse` is the smooth replacement of the unit direction `z / ‖z‖`: it agrees with
  `z / ‖z‖` for `‖z‖ ≥ 1/2` and is a genuine smooth `ℂ`-valued function on all of `ℂ` (it collapses to
  `0` at the centre).  It is what makes the cap side of the plane chart defined at `z = 0`, where the
  direction `arg z` is not even continuous;
* `Work.Drive.tauProf` is the band coordinate as a function of the squared radius: it agrees with
  `(π²/2)(‖z‖ - 1/2)` for `‖z‖ ≥ 1/2` (the value for which the chart reproduces the strip chart of
  `Work.Drive.stripChart`, cf. `Neutral/stripDiskPresentationNeutral.lean`) and is *strictly negative*
  for `‖z‖ < 1/2`, which is exactly what makes the plane chart cross the gluing torus into the **cap**
  solid torus (the disk coordinate `D = M / √(‖M‖² + 4τ‖W‖²)` of the descent has
  `‖D‖ > 1` for `τ < 0`).

Both profiles are cut off by `Real.smoothTransition`, so that the radial dependence is *locally
constant* near the centre; this is what makes them `C^∞` at `z = 0` (no Whitney extension is needed).
-/

namespace Work.Drive

noncomputable section

open scoped Topology
open Filter

/-! ## The cut-off -/

/-- A smooth cut-off which is `0` for `s ≤ a / 2` and `1` for `s ≥ a`. -/
def profCut (a s : ℝ) : ℝ := Real.smoothTransition (2 * s / a - 1)

lemma profCut_contDiff (a : ℝ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (profCut a) := by
  unfold profCut
  exact Real.smoothTransition.contDiff.comp
    (((contDiff_const (c := (2 : ℝ))).mul contDiff_id).div_const a |>.sub contDiff_const)

lemma profCut_nonneg (a s : ℝ) : 0 ≤ profCut a s := Real.smoothTransition.nonneg _

lemma profCut_le_one (a s : ℝ) : profCut a s ≤ 1 := Real.smoothTransition.le_one _

lemma profCut_eq_zero {a s : ℝ} (ha : 0 < a) (h : s ≤ a / 2) : profCut a s = 0 := by
  unfold profCut
  refine Real.smoothTransition.zero_of_nonpos ?_
  have h2 : 2 * s / a ≤ 1 := by
    rw [div_le_iff₀ ha]; linarith
  linarith

lemma profCut_eq_one {a s : ℝ} (ha : 0 < a) (h : a ≤ s) : profCut a s = 1 := by
  unfold profCut
  refine Real.smoothTransition.one_of_one_le ?_
  have h2 : 2 ≤ 2 * s / a := by
    rw [le_div_iff₀ ha]; linarith
  linarith

/-! ## The unit-direction profile -/

/-- The smooth replacement of the unit direction: `wProf s = 1 / √s` for `s ≥ 1/4`, and `wProf s = 0`
for `s ≤ 1/8`.  It is `C^∞` on all of `ℝ` because it *vanishes identically* near `0`. -/
def wProf (s : ℝ) : ℝ := profCut (1 / 4) s / Real.sqrt s

lemma contDiff_wProf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) wProf := by
  rw [contDiff_iff_contDiffAt]
  intro s
  rcases lt_or_ge s (1 / 8) with h | h
  · refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds h] with t ht
    simp only [Set.mem_Iio] at ht
    show wProf t = (0 : ℝ)
    unfold wProf
    rw [profCut_eq_zero (a := 1 / 4) (by norm_num) (by linarith), zero_div]
  · have hs : 0 < s := by linarith
    unfold wProf
    exact (profCut_contDiff (1 / 4)).contDiffAt.div (Real.contDiffAt_sqrt (ne_of_gt hs))
      (ne_of_gt (Real.sqrt_pos.mpr hs))

lemma wProf_eq {s : ℝ} (h : 1 / 4 ≤ s) : wProf s = 1 / Real.sqrt s := by
  unfold wProf
  rw [profCut_eq_one (a := 1 / 4) (by norm_num) h]

lemma wProf_nonneg (s : ℝ) : 0 ≤ wProf s := by
  unfold wProf
  exact div_nonneg (profCut_nonneg _ _) (Real.sqrt_nonneg _)

/-! ## The collapsed direction -/

/-- The collapsed unit direction: the point with `wCollapse z = z / ‖z‖` for `‖z‖ ≥ 1/2` and
`wCollapse z = 0` for `‖z‖` small.  It is `C^∞` on all of `ℂ` and odd, `wCollapse (-z) = - wCollapse z`.
-/
def wCollapse (z : ℂ) : ℂ := ((wProf (‖z‖ ^ 2) : ℝ) : ℂ) * z

lemma contDiff_norm_sq_complex : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℂ => ‖z‖ ^ 2) := by
  rw [show (fun z : ℂ => ‖z‖ ^ 2) = fun z => Complex.normSq z from by
    funext z; rw [Complex.normSq_eq_norm_sq]]
  rw [show (fun z : ℂ => Complex.normSq z) = fun z => z.re * z.re + z.im * z.im from by
    funext z; rw [Complex.normSq_apply]]
  exact ((Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add
    (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff))

lemma contDiff_wCollapse : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) wCollapse := by
  unfold wCollapse
  exact ((Complex.ofRealCLM.contDiff.comp (contDiff_wProf.comp contDiff_norm_sq_complex))).mul
    contDiff_id

lemma wCollapse_eq {z : ℂ} (h : 1 / 2 ≤ ‖z‖) : wCollapse z = z / ((‖z‖ : ℝ) : ℂ) := by
  unfold wCollapse
  have h4 : (1 : ℝ) / 4 ≤ ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  rw [wProf_eq h4, Real.sqrt_sq (norm_nonneg z), one_div, Complex.ofReal_inv]
  rw [div_eq_mul_inv, mul_comm]

lemma norm_ofReal_complex (r : ℝ) : ‖(((r : ℝ)) : ℂ)‖ = |r| := by
  have h : ‖(((r : ℝ)) : ℂ)‖ ^ 2 = r ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
    ring
  calc ‖(((r : ℝ)) : ℂ)‖ = Real.sqrt (‖(((r : ℝ)) : ℂ)‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (r ^ 2) := by rw [h]
    _ = |r| := Real.sqrt_sq_eq_abs r

lemma wProf_mul_sqrt_le_one (s : ℝ) : wProf s * Real.sqrt s ≤ 1 := by
  rcases lt_or_ge s (1 / 8) with h | h
  · have h0 : wProf s = 0 := by
      unfold wProf
      rw [profCut_eq_zero (a := 1 / 4) (by norm_num) (by linarith)]
      exact zero_div _
    rw [h0, zero_mul]
    norm_num
  · have hs' : 0 < s := by linarith
    have hne : Real.sqrt s ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hs')
    have h1 : wProf s * Real.sqrt s = profCut (1 / 4) s := by
      unfold wProf
      exact div_mul_cancel₀ _ hne
    rw [h1]
    exact profCut_le_one _ _

/-- The collapsed direction stays in the closed unit disk. -/
lemma norm_wCollapse_le_one (z : ℂ) : ‖wCollapse z‖ ≤ 1 := by
  have h1 : ‖wCollapse z‖ = wProf (‖z‖ ^ 2) * ‖z‖ := by
    unfold wCollapse
    rw [norm_mul, norm_ofReal_complex, abs_of_nonneg (wProf_nonneg _)]
  rw [h1]
  have := wProf_mul_sqrt_le_one (‖z‖ ^ 2)
  rwa [Real.sqrt_sq (norm_nonneg z)] at this

lemma wCollapse_neg (z : ℂ) : wCollapse (-z) = -wCollapse z := by
  unfold wCollapse
  rw [norm_neg, mul_neg]

/-! ## The band profile -/

/-- The band coordinate as a function of the squared radius.  For `s ≥ 1/8` it is
`(π²/2) (√s - 1/2)`, and for `s ≤ 1/16` it is the constant `τ` (so that the profile is locally constant
near `0`, hence `C^∞`, and so that the chart is `C^∞` at the centre of the disk). -/
def tauProf (τ s : ℝ) : ℝ :=
  profCut (1 / 8) s * (Real.pi ^ 2 / 2 * (Real.sqrt s - 1 / 2)) + (1 - profCut (1 / 8) s) * τ

lemma contDiff_tauProf (τ : ℝ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (tauProf τ) := by
  rw [contDiff_iff_contDiffAt]
  intro s
  rcases lt_or_ge s (1 / 16) with h | h
  · refine (contDiffAt_const (c := τ)).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds h] with t ht
    simp only [Set.mem_Iio] at ht
    show tauProf τ t = τ
    unfold tauProf
    rw [profCut_eq_zero (a := 1 / 8) (by norm_num) (by linarith)]
    ring
  · have hs : 0 < s := by linarith
    unfold tauProf
    refine ContDiffAt.add ?_ ?_
    · refine ContDiffAt.mul (profCut_contDiff (1 / 8)).contDiffAt ?_
      refine ContDiffAt.mul contDiffAt_const ?_
      exact (Real.contDiffAt_sqrt (ne_of_gt hs)).sub contDiffAt_const
    · exact ContDiffAt.mul (contDiffAt_const.sub (profCut_contDiff (1 / 8)).contDiffAt)
        contDiffAt_const

lemma tauProf_eq {τ s : ℝ} (h : 1 / 8 ≤ s) :
    tauProf τ s = Real.pi ^ 2 / 2 * (Real.sqrt s - 1 / 2) := by
  unfold tauProf
  rw [profCut_eq_one (a := 1 / 8) (by norm_num) h]
  ring

lemma tauProf_eq_const {τ s : ℝ} (h : s ≤ 1 / 16) : tauProf τ s = τ := by
  unfold tauProf
  rw [profCut_eq_zero (a := 1 / 8) (by norm_num) (by linarith)]
  ring

lemma tauProf_neg {τ s : ℝ} (hτ : τ < 0) (hs : s < 1 / 4) : tauProf τ s < 0 := by
  have hb0 : 0 ≤ profCut (1 / 8) s := profCut_nonneg _ _
  have hb1 : profCut (1 / 8) s ≤ 1 := profCut_le_one _ _
  have hlt : Real.sqrt s < 1 / 2 := by
    rcases lt_or_ge s 0 with h | h
    · rw [Real.sqrt_eq_zero_of_nonpos (le_of_lt h)]; norm_num
    · have h' := Real.sqrt_lt_sqrt h hs
      rwa [show Real.sqrt (1 / 4) = 1 / 2 from by
        rw [show (1 : ℝ) / 4 = (1 / 2) ^ 2 from by norm_num]; exact Real.sqrt_sq (by norm_num)] at h'
  have hmain : Real.pi ^ 2 / 2 * (Real.sqrt s - 1 / 2) < 0 := by
    have hp : (0 : ℝ) < Real.pi ^ 2 / 2 := by positivity
    nlinarith [Real.pi_pos]
  rcases eq_or_lt_of_le hb0 with hb | hb
  · unfold tauProf
    rw [← hb, zero_mul, sub_zero, one_mul]
    simpa using hτ
  · unfold tauProf
    have h1 : profCut (1 / 8) s * (Real.pi ^ 2 / 2 * (Real.sqrt s - 1 / 2)) < 0 :=
      mul_neg_of_pos_of_neg hb hmain
    have h2 : (1 - profCut (1 / 8) s) * τ ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hb1) (le_of_lt hτ)
    have := add_lt_add_of_lt_of_le h1 h2
    simpa using this

/-! ## The composed profiles on the disk -/

/-- The band coordinate of the plane chart: `τ` at the centre of the disk, equal to
`(π²/2)(‖z‖ - 1/2)` for `‖z‖ ≥ 1/2`, and strictly negative for `‖z‖ < 1/2`. -/
def tauComp (τ : ℝ) (z : ℂ) : ℝ := tauProf τ (‖z‖ ^ 2)

lemma contDiff_tauComp (τ : ℝ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (tauComp τ) := by
  unfold tauComp
  exact (contDiff_tauProf τ).comp contDiff_norm_sq_complex

lemma tauComp_eq {τ : ℝ} {z : ℂ} (h : 1 / 2 ≤ ‖z‖) :
    tauComp τ z = Real.pi ^ 2 / 2 * (‖z‖ - 1 / 2) := by
  unfold tauComp
  rw [tauProf_eq (τ := τ) (by nlinarith [norm_nonneg z] : (1 : ℝ) / 8 ≤ ‖z‖ ^ 2),
    Real.sqrt_sq (norm_nonneg z)]

lemma tauComp_neg {τ : ℝ} (hτ : τ < 0) {z : ℂ} (h : ‖z‖ < 1 / 2) : tauComp τ z < 0 := by
  unfold tauComp
  exact tauProf_neg hτ (by nlinarith [norm_nonneg z])

lemma tauComp_eq_const {τ : ℝ} {z : ℂ} (h : ‖z‖ ^ 2 ≤ 1 / 16) : tauComp τ z = τ :=
  tauProf_eq_const h

lemma tauComp_sqrt_eq {τ : ℝ} {z : ℂ} (h : 1 / 2 ≤ ‖z‖) :
    Real.sqrt (tauComp τ z) = Real.sqrt (Real.pi ^ 2 / 2 * (‖z‖ - 1 / 2)) := by
  rw [tauComp_eq h]

end

end Work.Drive
