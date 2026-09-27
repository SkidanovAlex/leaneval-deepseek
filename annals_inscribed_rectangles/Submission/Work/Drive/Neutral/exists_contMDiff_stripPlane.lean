import Mathlib
import Submission.Work.Drive.Neutral.stripSeamChart
import Submission.Work.Drive.Neutral.stripTauChart
import Submission.Work.Drive.stripChartSmooth
import Submission.Work.Drive.exists_even_smooth_cutoff
import Submission.Work.Drive.contDiffOn_even_comp_sqrt
import Submission.Work.Drive.seeleyDescent_ext
import Submission.Work.Drive.Neutral.seamChart_eq_stripTauChart_at
import Submission.Work.Drive.Neutral.stripTauChart_congr

/-!
# The strip plane chart

`Work.Drive.stripChart γ hγne 0` presents the configuration strip `M` of a smooth embedded plane
curve `γ` in the capping space, but only off the diagonal: along the strip the chord data is a
function of the square `τ = s²` of the opening parameter `s`, and the map
`(σ, τ) ↦ stripChart γ hγne 0 (σ + √τ, σ - √τ)` is the *plane* chart of `M ∪ cap` across the
gluing torus.  Since `τ ↦ √τ` is not differentiable at the origin this is not automatic: the
smoothness across `τ = 0` is the content of the even descent of the symmetric chord data.

This file proves the global form:

* `Work.Drive.Neutral.exists_contMDiff_stripPlane_of_descent` — given a globally `C^∞` germ of the symmetric
  data around `(σ₀, 0)` which reproduces the descent on `τ ≥ 0`, there is a globally `C^∞` map `P`
  of the plane into the capping space which is `stripChart γ hγne 0 (σ + √τ, σ - √τ)` on the
  half-strip `{0 < τ < ε}` around the seam point;
* `Work.Drive.Neutral.exists_contMDiff_stripPlane` — the unconditional form.

The construction is the seam chart of `Work.Drive.stripSeamChart`: the data germ is interpolated with
a smooth bump into *globally* defined configuration data whose side conditions (`r > 0`, third
coordinate non-zero, and the branch condition of the halving) hold everywhere, and the seam chart of
that data is globally `C^∞` (`Work.Drive.Neutral.contMDiff_seamChart`).
-/

namespace Work.Drive.Neutral

open Manifold Filter
open scoped Manifold ContDiff Topology
open Classical

set_option linter.style.haveILetI false

noncomputable section

variable {γ : Circle → ℝ × ℝ}

/-! ## 1. Elementary helpers -/

/-- A strict convex combination of two positive numbers is positive. -/
private lemma pos_of_convex_mul {x a b : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) (ha : 0 < a) (hb : 0 < b) :
    0 < x * a + (1 - x) * b := by
  rcases le_total a b with h | h
  · nlinarith
  · nlinarith

/-- The exponential of the circle is injective on an arc of length `< 2π` around `σ`. -/
lemma circle_exp_add_ne_sub {σ s : ℝ} (h0 : 0 < s) (hπ : s < Real.pi) :
    Circle.exp (σ + s) ≠ Circle.exp (σ - s) := by
  intro heq
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp heq
  have h2 : s = (m : ℝ) * Real.pi := by linarith
  have hpos : 0 < (m : ℝ) := by nlinarith [Real.pi_pos]
  have hmpos : 0 < m := by exact_mod_cast hpos
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by
    have : (1 : ℤ) ≤ m := by omega
    exact_mod_cast this
  nlinarith [Real.pi_pos, hπ]

/-- **The branch condition of the seam chart is automatic near the base point.**  If the third
configuration coordinate at `q` is within `1/8` of the unit value `u₀` at the base point `p₀`, then
`seamW G p₀ q + 1` does not vanish, so that the halving `Work.Drive.Neutral.seamHalf` is smooth there. -/
private lemma seamW_add_one_ne_zero {G : EuclideanSpace ℝ (Fin 2) → ℝ × ℂ × ℂ}
    {p₀ q : EuclideanSpace ℝ (Fin 2)} {u₀ : ℂ} (hu₀ : ‖u₀‖ = 1)
    (hp₀ : (G p₀).2.2 = u₀) (hz : ‖(G q).2.2 - u₀‖ ≤ 1 / 8) :
    seamW G p₀ q + 1 ≠ 0 := by
  have hu₀u₀ : u₀ * star u₀ = 1 := by
    have hc := Complex.mul_conj u₀
    rw [starRingEnd_apply, Complex.normSq_eq_norm_sq, hu₀] at hc
    norm_num at hc
    exact hc
  -- the real part of `z * star u₀` is close to `1`
  have hre : (7 / 8 : ℝ) ≤ ((G q).2.2 * star u₀).re := by
    have hzu : (G q).2.2 * star u₀ - 1 = ((G q).2.2 - u₀) * star u₀ := by
      rw [sub_mul, hu₀u₀]
    have hnorm : ‖(G q).2.2 * star u₀ - 1‖ ≤ 1 / 8 := by
      rw [hzu, norm_mul, norm_star, hu₀, mul_one]
      exact hz
    have h2 : |((G q).2.2 * star u₀).re - 1| ≤ 1 / 8 := by
      have h3 : ((G q).2.2 * star u₀).re - 1 = ((G q).2.2 * star u₀ - 1).re := by simp
      rw [h3]
      exact le_trans (Complex.abs_re_le_norm _) hnorm
    rw [abs_le] at h2
    linarith [h2.1]
  -- the norm of `z` is bounded below
  have hzn : (7 / 8 : ℝ) ≤ ‖(G q).2.2‖ := by
    have h := norm_sub_le ((G q).2.2) ((G q).2.2 - u₀)
    rw [show (G q).2.2 - ((G q).2.2 - u₀) = u₀ by ring, hu₀] at h
    linarith
  have hzpos : 0 < ‖(G q).2.2‖ := by linarith
  -- `seamW` is a positive multiple of `z * star u₀`
  have hkey : seamW G p₀ q + 1
      = ((G q).2.2 * star u₀) * (((‖(G q).2.2‖)⁻¹ : ℝ) : ℂ) + 1 := by
    rw [seamW, hp₀]
    simp only [seamCN, Complex.ofReal_inv]
    ring
  intro hcontr
  have hX : ((G q).2.2 * star u₀) * (((‖(G q).2.2‖)⁻¹ : ℝ) : ℂ) + 1 = 0 := by
    rw [← hkey]
    exact hcontr
  have hW : ((G q).2.2 * star u₀) * (((‖(G q).2.2‖)⁻¹ : ℝ) : ℂ) = -1 := by
    calc ((G q).2.2 * star u₀) * (((‖(G q).2.2‖)⁻¹ : ℝ) : ℂ)
        = ((G q).2.2 * star u₀) * (((‖(G q).2.2‖)⁻¹ : ℝ) : ℂ) + 1 - 1 := by ring
      _ = 0 - 1 := by rw [hX]
      _ = -1 := by ring
  have hpos : 0 < (((G q).2.2 * star u₀) * (((‖(G q).2.2‖)⁻¹ : ℝ) : ℂ)).re := by
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    exact mul_pos (by linarith) (inv_pos.mpr hzpos)
  rw [hW] at hpos
  norm_num at hpos

/-! ## 2. The strip plane chart from a global germ of the symmetric data -/

open Manifold in
open scoped Manifold ContDiff in
/-- **The strip plane chart, given a global smooth germ of the symmetric data.**  If the symmetric
chord data of `γ` has a globally `C^∞` representative `G₀` which reproduces the descent
`symmData γ (σ, √τ)` for `τ ≥ 0` near `(σ₀, 0)`, then there are `ε > 0` and a globally `C^∞` map
`P` of the plane into the capping space which is `stripChart γ hγne 0 (σ + √τ, σ - √τ)` on the
half-strip `{0 < τ < ε}` around the seam point. -/
theorem exists_contMDiff_stripPlane_of_descent
    (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (hγne : ∀ x : Circle, γ x ≠ 0) (σ₀ : ℝ)
    (hdesc : ∃ G₀ : ℝ × ℝ → ℝ × ℂ × ℂ,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G₀ ∧
      (∀ᶠ p in nhds (σ₀, 0), 0 ≤ p.2 → G₀ p = symmData γ (p.1, Real.sqrt p.2))) :
    ∃ (ε : ℝ) (P : EuclideanSpace ℝ (Fin 2) → CappingSpace),
      0 < ε ∧
      (letI := cappingCharted
       ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) P) ∧
      (∀ q : EuclideanSpace ℝ (Fin 2), |q 0 - σ₀| < ε → 0 < q 1 → q 1 < ε →
        P q = stripChart γ hγne 0 (mk2 (q 0 + Real.sqrt (q 1)) (q 0 - Real.sqrt (q 1)))) := by
  letI := cappingCharted
  obtain ⟨G₀, hG₀cd, hG₀val⟩ := hdesc
  -- the plane point of the seam and the plane version of the germ
  let c : EuclideanSpace ℝ (Fin 2) := mk2 σ₀ 0
  let Gloc : EuclideanSpace ℝ (Fin 2) → ℝ × ℂ × ℂ := fun q => G₀ (q 0, q 1)
  have hpair : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin 2) => (q 0, q 1)) := by fun_prop
  have hGloc_cd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Gloc := hG₀cd.comp hpair
  have hGloc_val : ∀ᶠ q in nhds c, 0 ≤ q 1 →
      Gloc q = symmData γ (q 0, Real.sqrt (q 1)) := by
    filter_upwards [(hpair.continuous.continuousAt).preimage_mem_nhds hG₀val] with q hq hq0
    exact hq hq0
  have hGloc_c : Gloc c = symmData γ (σ₀, 0) := by
    have h := hGloc_val.self_of_nhds (le_refl (0 : ℝ))
    simpa [c] using h
  let u₀ : ℂ := symmE γ σ₀ 0
  have hu₀ : ‖u₀‖ = 1 := symmE_norm γ σ₀ 0 (symmWC_zero_ne_zero hγ σ₀)
  have hGloc_c_thd : (Gloc c).2.2 = u₀ := by rw [hGloc_c]; rfl
  -- the open neighbourhood conditions at the seam point
  have hpos_ev : ∀ᶠ q in nhds c, 0 < (Gloc q).1 := by
    have hcont : ContinuousAt (fun q => (Gloc q).1) c :=
      (hGloc_cd.continuous.continuousAt).fst
    have hval : 0 < (Gloc c).1 := by rw [hGloc_c]; exact symmR_pos hγne σ₀ 0
    exact hcont.preimage_mem_nhds ((isOpen_lt continuous_const continuous_id).mem_nhds hval)
  have hnorm_ev : ∀ᶠ q in nhds c, ‖(Gloc q).2.1‖ < 5 / 4 := by
    have hcont : ContinuousAt (fun q => ‖(Gloc q).2.1‖) c :=
      ((hGloc_cd.continuous.continuousAt).snd.fst).norm
    have hval : ‖(Gloc c).2.1‖ < 5 / 4 := by
      rw [hGloc_c]
      exact lt_of_le_of_lt (symmD_norm_le_one γ σ₀ 0) (by norm_num)
    exact hcont.preimage_mem_nhds ((isOpen_lt continuous_id continuous_const).mem_nhds hval)
  have hnear_ev : ∀ᶠ q in nhds c, ‖(Gloc q).2.2 - u₀‖ < 1 / 8 := by
    have hcont : ContinuousAt (fun q => ‖(Gloc q).2.2 - u₀‖) c :=
      ((hGloc_cd.continuous.continuousAt).snd.snd.sub continuousAt_const).norm
    have hval : ‖(Gloc c).2.2 - u₀‖ < 1 / 8 := by rw [hGloc_c_thd]; norm_num
    exact hcont.preimage_mem_nhds ((isOpen_lt continuous_id continuous_const).mem_nhds hval)
  -- extract the radii
  obtain ⟨R₁, hR₁pos, hR₁⟩ := Metric.eventually_nhds_iff.mp hGloc_val
  obtain ⟨R₂, hR₂pos, hR₂⟩ := Metric.eventually_nhds_iff.mp hpos_ev
  obtain ⟨R₃, hR₃pos, hR₃⟩ := Metric.eventually_nhds_iff.mp hnorm_ev
  obtain ⟨R₄, hR₄pos, hR₄⟩ := Metric.eventually_nhds_iff.mp hnear_ev
  let R : ℝ := min (min R₁ R₂) (min (min R₃ R₄) ((Real.pi / 2) ^ 2 / 2))
  have hRpos : 0 < R := by
    refine lt_min (lt_min hR₁pos hR₂pos) (lt_min (lt_min hR₃pos hR₄pos) ?_)
    positivity
  have hRle₁ : R ≤ R₁ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hRle₂ : R ≤ R₂ := le_trans (min_le_left _ _) (min_le_right _ _)
  have hRle₃ : R ≤ R₃ :=
    le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
  have hRle₄ : R ≤ R₄ :=
    le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
  have hRleπ : R ≤ (Real.pi / 2) ^ 2 / 2 :=
    le_trans (min_le_right _ _) (min_le_right _ _)
  have hball₁ : ∀ q, dist q c < R → 0 ≤ q 1 →
      Gloc q = symmData γ (q 0, Real.sqrt (q 1)) :=
    fun q hq hq0 => hR₁ (lt_of_lt_of_le hq hRle₁) hq0
  have hball₂ : ∀ q, dist q c < R → 0 < (Gloc q).1 :=
    fun q hq => hR₂ (lt_of_lt_of_le hq hRle₂)
  have hball₃ : ∀ q, dist q c < R → ‖(Gloc q).2.1‖ < 5 / 4 :=
    fun q hq => hR₃ (lt_of_lt_of_le hq hRle₃)
  have hball₄ : ∀ q, dist q c < R → ‖(Gloc q).2.2 - u₀‖ < 1 / 8 :=
    fun q hq => hR₄ (lt_of_lt_of_le hq hRle₄)
  -- the bump and the interpolated data
  let bump : ContDiffBump c := ⟨R / 4, R / 2, by linarith, by linarith⟩
  have hbump_supp : tsupport bump ⊆ Metric.ball c R := by
    have h1 : tsupport bump ⊆ Metric.closedBall c (R / 2) := by
      intro q hq
      have hq' : q ∈ closure (Function.support bump) := hq
      rw [ContDiffBump.support_eq] at hq'
      have hq'' : q ∈ closure (Metric.ball c (R / 2)) := by simpa using hq'
      rwa [closure_ball c (by linarith : R / 2 ≠ 0)] at hq''
    intro q hq
    have := h1 hq
    rw [Metric.mem_closedBall] at this
    rw [Metric.mem_ball]
    linarith
  have hbump_tsupp : ∀ q ∈ tsupport bump, dist q c < R := fun q hq => by
    have := hbump_supp hq
    rwa [Metric.mem_ball] at this
  have hbump_c : bump c = 1 := by
    refine ContDiffBump.one_of_mem_closedBall bump ?_
    rw [Metric.mem_closedBall]
    simpa using bump.rIn_pos.le
  -- the interpolated data, componentwise
  let r : EuclideanSpace ℝ (Fin 2) → ℝ := fun q => bump q * (Gloc q).1 + (1 - bump q) * 1
  let d : EuclideanSpace ℝ (Fin 2) → ℂ := fun q => ((bump q : ℝ) : ℂ) * (Gloc q).2.1
  let z : EuclideanSpace ℝ (Fin 2) → ℂ :=
    fun q => ((bump q : ℝ) : ℂ) * (Gloc q).2.2 + ((1 - bump q : ℝ) : ℂ) * u₀
  have hbcd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin 2) => bump q) := ContDiffBump.contDiff bump
  have hGcd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin 2) => (r q, d q, z q)) := by
    refine ((hbcd.mul hGloc_cd.fst).add ((contDiff_const.sub hbcd).mul contDiff_const)).prodMk ?_
    refine (((Complex.ofRealCLM.contDiff.comp hbcd).mul hGloc_cd.snd.fst)).prodMk ?_
    exact ((Complex.ofRealCLM.contDiff.comp hbcd).mul hGloc_cd.snd.snd).add
      ((Complex.ofRealCLM.contDiff.comp (contDiff_const.sub hbcd)).mul contDiff_const)
  -- the global side conditions
  have hz : ∀ q, ‖z q - u₀‖ ≤ 1 / 8 := by
    intro q
    rcases eq_or_ne (bump q) 0 with hq | hq
    · have hzq : z q = u₀ := by simp [z, hq]
      rw [hzq, sub_self, norm_zero]
      norm_num
    · have hmem : q ∈ tsupport bump := subset_closure (Function.mem_support.mpr hq)
      have hb : ‖(Gloc q).2.2 - u₀‖ < 1 / 8 := hball₄ q (hbump_tsupp q hmem)
      have hkey : z q - u₀ = ((bump q : ℝ) : ℂ) * ((Gloc q).2.2 - u₀) := by
        simp only [z, Complex.ofReal_sub, Complex.ofReal_one]
        ring
      rw [hkey, norm_mul, Complex.norm_real]
      have hb1 : |bump q| ≤ 1 := by
        rw [abs_of_nonneg (ContDiffBump.nonneg (f := bump) (x := q))]
        exact ContDiffBump.le_one (f := bump) (x := q)
      calc |bump q| * ‖(Gloc q).2.2 - u₀‖ ≤ 1 * (1 / 8) :=
            mul_le_mul hb1 (le_of_lt hb) (norm_nonneg _) (by norm_num)
        _ = 1 / 8 := by norm_num
  have hnorm_d : ∀ q, ‖d q‖ ≤ 5 / 4 := by
    intro q
    rcases eq_or_ne (bump q) 0 with hq | hq
    · have hdq : d q = 0 := by simp [d, hq]
      rw [hdq, norm_zero]
      norm_num
    · have hmem : q ∈ tsupport bump := subset_closure (Function.mem_support.mpr hq)
      have hb : ‖(Gloc q).2.1‖ < 5 / 4 := hball₃ q (hbump_tsupp q hmem)
      have hkey : d q = ((bump q : ℝ) : ℂ) * (Gloc q).2.1 := rfl
      rw [hkey, norm_mul, Complex.norm_real]
      have hb1 : |bump q| ≤ 1 := by
        rw [abs_of_nonneg (ContDiffBump.nonneg (f := bump) (x := q))]
        exact ContDiffBump.le_one (f := bump) (x := q)
      calc |bump q| * ‖(Gloc q).2.1‖ ≤ 1 * (5 / 4) :=
            mul_le_mul hb1 (le_of_lt hb) (norm_nonneg _) (by norm_num)
        _ = 5 / 4 := by norm_num
  have hGpos : ∀ q, 0 < r q := by
    intro q
    rcases eq_or_ne (bump q) 0 with hq | hq
    · have hrq : r q = 1 := by simp [r, hq]
      rw [hrq]; norm_num
    · have hmem : q ∈ tsupport bump := subset_closure (Function.mem_support.mpr hq)
      have hb : 0 < (Gloc q).1 := hball₂ q (hbump_tsupp q hmem)
      have hkey : r q = bump q * (Gloc q).1 + (1 - bump q) * 1 := rfl
      rw [hkey]
      exact pos_of_convex_mul (ContDiffBump.nonneg (f := bump) (x := q))
        (ContDiffBump.le_one (f := bump) (x := q)) hb (by norm_num)
  have hGthd : ∀ q, z q ≠ 0 := by
    intro q
    have h2 : (7 / 8 : ℝ) ≤ ‖z q‖ := by
      have h := norm_sub_le (z q) (z q - u₀)
      rw [show z q - (z q - u₀) = u₀ by ring, hu₀] at h
      linarith [hz q]
    intro hzero
    rw [hzero, norm_zero] at h2
    norm_num at h2
  have hGsqrt : ∀ q, 1 - ‖d q‖ ^ 2 / 2 ≠ 0 := by
    intro q
    have h2 : ‖d q‖ ^ 2 ≤ (5 / 4) ^ 2 := by
      simpa only [pow_two] using mul_self_le_mul_self (norm_nonneg (d q)) (hnorm_d q)
    intro hzero
    nlinarith
  have hGc : (fun q => (r q, d q, z q)) c = (r c, d c, z c) := rfl
  have hrdc : r c = (Gloc c).1 := by simp [r, hbump_c]
  have hzc : z c = u₀ := by simp [z, hbump_c, hGloc_c_thd]
  have hnthd : ‖z c‖ = 1 := by rw [hzc]; exact hu₀
  have hunit : ‖((r c, d c, z c) : ℝ × ℂ × ℂ).2.2‖ = 1 := hnthd
  have hw : ∀ q, seamW (fun q => (r q, d q, z q)) c q + 1 ≠ 0 := by
    intro q
    refine seamW_add_one_ne_zero (G := fun q => (r q, d q, z q)) hu₀ ?_ ?_
    · show z c = u₀
      exact hzc
    · show ‖z q - u₀‖ ≤ 1 / 8
      exact hz q
  refine ⟨R / 8, seamChart (fun q => (r q, d q, z q)) c hunit, by positivity, ?_, ?_⟩
  · exact contMDiff_seamChart (G := fun q => (r q, d q, z q)) (p₀ := c) hunit hGcd hGpos hGthd
      hGsqrt hw
  · -- the value on the half-strip
    intro q hq0 hq1 hq2
    have hdist : dist q c < R / 4 := by
      have hb : dist q c ≤ |q 0 - σ₀| + |q 1| := by
        rw [EuclideanSpace.dist_eq, Fin.sum_univ_two]
        have h0 : dist (q.ofLp 0) ((mk2 σ₀ 0).ofLp 0) = |q 0 - σ₀| := by
          rw [Real.dist_eq]; simp [mk2]
        have h1 : dist (q.ofLp 1) ((mk2 σ₀ 0).ofLp 1) = |q 1| := by
          rw [Real.dist_eq]; simp [mk2]
        rw [h0, h1, Real.sqrt_le_iff]
        refine ⟨by positivity, ?_⟩
        have ha : (0 : ℝ) ≤ |q 0 - σ₀| := abs_nonneg _
        have hb : (0 : ℝ) ≤ |q 1| := abs_nonneg _
        have h1 : |q 0 - σ₀| ^ 2 = (q 0 - σ₀) ^ 2 := sq_abs _
        have h2 : |q 1| ^ 2 = q 1 ^ 2 := sq_abs _
        nlinarith [mul_nonneg ha hb]
      rw [abs_of_pos hq1] at hb
      linarith
    have hbump_q : bump q = 1 := by
      refine ContDiffBump.one_of_mem_closedBall bump ?_
      show dist q c ≤ R / 4
      exact le_of_lt hdist
    have hGlocq : Gloc q = symmData γ (q 0, Real.sqrt (q 1)) :=
      hball₁ q (lt_of_lt_of_le hdist (by linarith)) (le_of_lt hq1)
    have hGq : (r q, d q, z q) = symmData γ (q 0, Real.sqrt (q 1)) := by
      have hrd : r q = symmR γ (q 0) (Real.sqrt (q 1)) := by
        simp only [r, hbump_q, hGlocq, symmData]
        norm_num
      have hdd : d q = symmD γ (q 0) (Real.sqrt (q 1)) := by
        simp only [d, hbump_q, hGlocq, symmData]
        norm_num
      have hzz : z q = symmE γ (q 0) (Real.sqrt (q 1)) := by
        simp only [z, hbump_q, hGlocq, symmData]
        norm_num
      simp only [hrd, hdd, hzz, symmData]
    have hspi : |Real.sqrt (q 1)| < Real.pi / 2 := by
      rw [abs_of_nonneg (Real.sqrt_nonneg _),
        Real.sqrt_lt' (by positivity : (0 : ℝ) < Real.pi / 2)]
      nlinarith [Real.pi_pos, hq2, hRleπ]
    have hsq : (Real.sqrt (q 1)) ^ 2 = q 1 := Real.sq_sqrt (le_of_lt hq1)
    have hqq : q = mk2 (q 0) ((Real.sqrt (q 1)) ^ 2) := by
      rw [hsq]
      ext i
      fin_cases i <;> simp [mk2]
    have hπ : Real.sqrt (q 1) < Real.pi := by
      rw [Real.sqrt_lt' Real.pi_pos]
      nlinarith [Real.pi_pos, hq2, hRleπ]
    calc seamChart (fun q => (r q, d q, z q)) c hunit q
        = stripTauChart hγ hγne (fun q => (r q, d q, z q)) σ₀ q :=
          seamChart_eq_stripTauChart_at γ hγ hγne σ₀ hunit (le_of_lt hq1) (hGpos q)
            (by rw [hGq]; exact symmD_norm_le_one γ _ _)
            (by rw [hGq]; exact symmE_norm γ _ _ (symmWC_ne_zero_of_lt hγ hspi))
            (hw q)
      _ = stripTauChart hγ hγne
            (fun q' : EuclideanSpace ℝ (Fin 2) => symmData γ (q' 0, Real.sqrt (q' 1))) σ₀ q :=
          stripTauChart_congr γ hγ hγne hGq
      _ = stripTauChart hγ hγne
            (fun q' : EuclideanSpace ℝ (Fin 2) => symmData γ (q' 0, Real.sqrt (q' 1))) σ₀
            (mk2 (q 0) ((Real.sqrt (q 1)) ^ 2)) := by
          conv_lhs => rw [hqq]
      _ = stripChart γ hγne 0 (mk2 (q 0 + Real.sqrt (q 1)) (q 0 - Real.sqrt (q 1))) :=
          stripTauChart_eq_stripChart hγ hγne (fun _ _ => rfl) σ₀ (Real.sqrt_pos.mpr hq1).ne' hspi
            (circle_exp_add_ne_sub (Real.sqrt_pos.mpr hq1) hπ)

/-! ## 3. The global germ of the symmetric data -/

/-- `χ • f` is globally `C^∞` when `χ` is `C^∞` with closed support inside an open set on which `f`
is `C^∞` (general form of
`Work.Drive.contDiff_smul_of_contDiffOn_of_tsupport_subset`). -/
private lemma contDiff_smul_of_contDiffOn_of_tsupport_subset'' {X E : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : X → E} {U : Set X} (hU : IsOpen U) (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f U)
    {χ : X → ℝ} (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) (hsupp : tsupport χ ⊆ U) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => χ x • f x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport χ
  · exact hχ.contDiffAt.smul (hf.contDiffAt (hU.mem_nhds (hsupp hx)))
  · have hmem : (tsupport χ)ᶜ ∈ 𝓝 x := (isClosed_closure).compl_mem_nhds hx
    have h0 : (fun y => χ y • f y) =ᶠ[𝓝 x] (fun _ => (0 : E)) := by
      filter_upwards [hmem] with y hy
      have hχy : χ y = 0 := by
        rw [← Function.notMem_support]
        intro hy'
        exact hy (subset_closure hy')
      rw [hχy, zero_smul]
    exact (contDiffAt_const (c := (0 : E))).congr_of_eventuallyEq h0

/-- **The global even descent of the symmetric data.**  There is a globally `C^∞` map of the plane
into the configuration data which reproduces `symmData γ (σ, √τ)` for `τ ≥ 0` near `(σ₀, 0)`. -/
theorem exists_contDiff_symmData_descent_global
    (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (hγne : ∀ x : Circle, γ x ≠ 0) (σ₀ : ℝ) :
    ∃ G : ℝ × ℝ → ℝ × ℂ × ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G ∧
      (∀ᶠ p in nhds (σ₀, 0), 0 ≤ p.2 → G p = symmData γ (p.1, Real.sqrt p.2)) := by
  set ρ : ℝ := Real.pi / 8 with hρdef
  have hρpos : 0 < ρ := by rw [hρdef]; positivity
  obtain ⟨χ, hχcd, -, -, hχone, hχsupp, hχeven⟩ :=
    exists_even_smooth_cutoff σ₀ (Ω := Metric.ball (σ₀, 0) ρ) Metric.isOpen_ball
      (Metric.mem_ball_self hρpos)
  have hU : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => symmData γ p)
      (Metric.ball (σ₀, 0) (2 * ρ)) := by
    intro p hp
    have h2 : |p.2| < Real.pi / 2 := by
      have h3 : dist p (σ₀, 0) < 2 * ρ := Metric.mem_ball.mp hp
      rw [Prod.dist_eq] at h3
      have h4 : |p.2 - 0| < 2 * ρ := lt_of_le_of_lt (le_max_right _ _) h3
      rw [hρdef] at h4
      simp only [sub_zero] at h4
      linarith [Real.pi_pos]
    exact (contDiffAt_symmData hγ hγne (symmWC_ne_zero_of_lt hγ h2)).contDiffWithinAt
  have htsupp : tsupport χ ⊆ Metric.ball (σ₀, 0) (2 * ρ) := by
    have h1 : tsupport χ ⊆ closure (Metric.ball (σ₀, 0) ρ) := closure_mono hχsupp
    rw [closure_ball (σ₀, 0) hρpos.ne'] at h1
    intro p hp
    have h2 : dist p (σ₀, 0) ≤ ρ := by
      have := h1 hp
      rwa [Metric.mem_closedBall] at this
    rw [Metric.mem_ball]
    linarith
  have hfcd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => χ p • symmData γ p) :=
    contDiff_smul_of_contDiffOn_of_tsupport_subset'' Metric.isOpen_ball hU hχcd htsupp
  have heven : ∀ (x t : ℝ), (fun p : ℝ × ℝ => χ p • symmData γ p) (x, -t)
      = (fun p : ℝ × ℝ => χ p • symmData γ p) (x, t) := by
    intro x t
    show χ (x, -t) • symmData γ (x, -t) = χ (x, t) • symmData γ (x, t)
    rw [hχeven (x, t), symmData_neg hγ x t]
  obtain ⟨G, hG, hGval⟩ := seeleyDescent_ext hfcd heven
  refine ⟨G, hG, ?_⟩
  have hcont : ContinuousAt (fun p : ℝ × ℝ => (p.1, Real.sqrt p.2)) (σ₀, 0) :=
    (Continuous.prodMk continuous_fst (Real.continuous_sqrt.comp continuous_snd)).continuousAt
  have hχone' : ∀ᶠ q in nhds (σ₀, Real.sqrt (0 : ℝ)), χ q = 1 := by simpa using hχone
  have hχev : ∀ᶠ p in nhds (σ₀, 0), χ (p.1, Real.sqrt p.2) = 1 :=
    hcont.eventually hχone'
  filter_upwards [hχev] with p hp hp0
  rw [hGval p.1 p.2 hp0, hp, one_smul]

open Manifold in
open scoped Manifold ContDiff in
/-- **The strip plane chart is globally `C^∞` across the seam.**  For a smooth embedded plane curve
`γ` avoiding the origin and every seam parameter `σ₀` there are `ε > 0` and a `C^∞` map `P` of the
plane into the capping space which is `stripChart γ hγne 0 (σ + √τ, σ - √τ)` on the half-strip
`{0 < τ < ε}`. -/
theorem exists_contMDiff_stripPlane
    (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (hγne : ∀ x : Circle, γ x ≠ 0) (σ₀ : ℝ) :
    ∃ (ε : ℝ) (P : EuclideanSpace ℝ (Fin 2) → CappingSpace),
      0 < ε ∧
      (letI := cappingCharted
       ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) P) ∧
      (∀ q : EuclideanSpace ℝ (Fin 2), |q 0 - σ₀| < ε → 0 < q 1 → q 1 < ε →
        P q = stripChart γ hγne 0 (mk2 (q 0 + Real.sqrt (q 1)) (q 0 - Real.sqrt (q 1)))) :=
  exists_contMDiff_stripPlane_of_descent hγ hγne σ₀
    (exists_contDiff_symmData_descent_global hγ hγne σ₀)

end

end Work.Drive.Neutral
