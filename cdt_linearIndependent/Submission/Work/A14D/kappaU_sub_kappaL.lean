import Mathlib
import Submission.Work.A14.defs
import Submission.Work.A14D.setup
import Submission.Work.A14D.D_local_at_one
import Submission.Work.A14D.H_local_at_one
import Submission.Work.A14D.uh_ode
import Submission.Work.A14D.uh_not_holo_at_ninth
import Submission.Work.A14D.logCoeff_exists
import Submission.Work.A14D.log_structured_vanishes
import Submission.Work.C17g.linear_ode_convex
import Submission.Work.A14D.crux_jump

namespace Work.A14D

open Complex Metric Filter
open scoped BigOperators Topology

noncomputable section

/-- The lens `ball (1/9) δ ∩ ball 1 (8/9)` on which `u_h` is manifestly holomorphic. -/
def kappaLens (δ : ℝ) : Set ℂ := Metric.ball ninth δ ∩ Metric.ball 1 (8 / 9)

lemma kappaLens_subset_ball (δ : ℝ) : kappaLens δ ⊆ Metric.ball ninth δ :=
  Set.inter_subset_left

lemma kappaLens_subset_ball1 (δ : ℝ) : kappaLens δ ⊆ Metric.ball 1 (8 / 9) :=
  Set.inter_subset_right

lemma isOpen_kappaLens (δ : ℝ) : IsOpen (kappaLens δ) :=
  Metric.isOpen_ball.inter Metric.isOpen_ball

lemma convex_kappaLens (δ : ℝ) : Convex ℝ (kappaLens δ) :=
  (convex_ball ninth δ).inter (convex_ball (1 : ℂ) (8 / 9))

lemma kappaLens_subset_slit {δ : ℝ} :
    kappaLens δ ⊆ Metric.ball ninth δ ∩ {z : ℂ | z.im ≠ 0 ∨ ninth.re < z.re} := by
  intro z hz
  obtain ⟨h1, h2⟩ := hz
  refine ⟨h1, ?_⟩
  by_cases him : z.im = 0
  · right
    rw [Metric.mem_ball, Complex.dist_eq] at h2
    have h3 : |(z - 1).re| ≤ ‖z - 1‖ := Complex.abs_re_le_norm (z - 1)
    have h3' : |(z - 1).re| < 8 / 9 := lt_of_le_of_lt h3 h2
    have h4 : (z - 1).re = z.re - 1 := Complex.sub_re z 1
    rw [h4] at h3'
    have h5 : -(8 / 9 : ℝ) < z.re - 1 := (abs_lt.mp h3').1
    have h9 : ninth.re = 1 / 9 := by simp [ninth]
    have : (1 / 9 : ℝ) < z.re := by linarith
    simpa [h9] using this
  · exact Or.inl him

lemma halfU_subset_Om1 (δ : ℝ) : halfU δ ⊆ Om1 :=
  fun z hz => Or.inl (ne_of_gt hz.2)

lemma halfL_subset_Om1 (δ : ℝ) : halfL δ ⊆ Om1 :=
  fun z hz => Or.inl (ne_of_lt hz.2)

lemma isOpen_halfU (δ : ℝ) : IsOpen (halfU δ) :=
  Metric.isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_im)

lemma isOpen_halfL (δ : ℝ) : IsOpen (halfL δ) :=
  Metric.isOpen_ball.inter (isOpen_lt Complex.continuous_im continuous_const)

/-- The holomorphic solution `u_h` of `LZ = 0` at `z = 1` has a non-zero log coefficient at
`1/9`, witnessed on the lens `ball (1/9) δ ∩ ball 1 (8/9)`. -/
theorem uh_lens_logCoeff {y9 : ℂ → ℂ} {δ : ℝ} (hY : Y9 y9 δ) :
    ∃ lam : ℂ, lam ≠ 0 ∧ LogCoeff y9 δ (kappaLens δ) uh lam := by
  have hY' := hY
  obtain ⟨hδpos, hδ20, hy9d, hy9ne, hy9ode⟩ := hY
  have hud : DifferentiableOn ℂ uh (kappaLens δ) :=
    uh_ode.1.mono (fun z hz => kappaLens_subset_ball1 δ hz)
  have hode : ∀ z ∈ kappaLens δ, LZ uh z = 0 :=
    fun z hz => uh_ode.2.2 z (kappaLens_subset_ball1 δ hz)
  obtain ⟨lam, hlam⟩ :=
    logCoeff_exists hY' (kappaLens δ) (isOpen_kappaLens δ) (convex_kappaLens δ)
      (kappaLens_subset_slit (δ := δ)) uh hud hode
  refine ⟨lam, ?_, hlam⟩
  intro h0
  subst h0
  obtain ⟨hh, hhhd, hheq⟩ := hlam
  refine uh_not_holo_at_ninth ⟨hh, δ, hδpos, hhhd, ?_⟩
  intro z hz
  have hthis := hheq z hz
  simp only [zero_mul, zero_add] at hthis
  exact hthis.symm

/-- One-sided boundary values of `log (· - 1)` at a real point `x < 1`, from above. -/
lemma tendsto_log_sub_one_of_lt {x : ℝ} (hx : x < 1) :
    Tendsto (fun z : ℂ => Complex.log (z - 1)) (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ))
      (𝓝 ((Real.log (1 - x) : ℂ) + Real.pi * Complex.I)) := by
  have hw : ((x : ℂ) - 1).re < 0 := by
    rw [Complex.sub_re, Complex.ofReal_re, Complex.one_re]; linarith
  have hwim : ((x : ℂ) - 1).im = 0 := by
    rw [Complex.sub_im, Complex.ofReal_im, Complex.one_im]; ring
  have hbase := Complex.tendsto_log_nhdsWithin_im_nonneg_of_re_neg_of_im_zero hw hwim
  have hnorm : ‖(x : ℂ) - 1‖ = 1 - x := by
    rw [show (x : ℂ) - 1 = ((x - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_neg (by linarith : x - 1 < 0)]
    ring
  rw [hnorm] at hbase
  have hmap : Tendsto (fun z : ℂ => z - 1) (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ))
      (𝓝[{w : ℂ | 0 ≤ w.im}] ((x : ℂ) - 1)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · exact ((continuousAt_id.sub continuousAt_const)).tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz
      have h : (z - 1).im = z.im := by simp
      rw [h]; exact le_of_lt hz
  exact hbase.comp hmap

/-- One-sided boundary values of `log (· - 1)` at a real point `x < 1`, from below. -/
lemma tendsto_log_sub_one_gt {x : ℝ} (hx : x < 1) :
    Tendsto (fun z : ℂ => Complex.log (z - 1)) (𝓝[{z : ℂ | z.im < 0}] (x : ℂ))
      (𝓝 ((Real.log (1 - x) : ℂ) - Real.pi * Complex.I)) := by
  have hw : ((x : ℂ) - 1).re < 0 := by
    rw [Complex.sub_re, Complex.ofReal_re, Complex.one_re]; linarith
  have hwim : ((x : ℂ) - 1).im = 0 := by
    rw [Complex.sub_im, Complex.ofReal_im, Complex.one_im]; ring
  have hbase := Complex.tendsto_log_nhdsWithin_im_neg_of_re_neg_of_im_zero hw hwim
  have hnorm : ‖(x : ℂ) - 1‖ = 1 - x := by
    rw [show (x : ℂ) - 1 = ((x - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_neg (by linarith : x - 1 < 0)]
    ring
  rw [hnorm] at hbase
  have hmap : Tendsto (fun z : ℂ => z - 1) (𝓝[{z : ℂ | z.im < 0}] (x : ℂ))
      (𝓝[{w : ℂ | w.im < 0}] ((x : ℂ) - 1)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · exact ((continuousAt_id.sub continuousAt_const)).tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz
      have h : (z - 1).im = z.im := by simp
      rw [h]; exact hz
  exact hbase.comp hmap

private lemma mem_closure_halfU_cap {δ : ℝ} (hδ : 0 < δ) (hδ20 : δ ≤ 1 / 20) {x : ℝ}
    (hx1 : 1 / 9 < x) (hx2 : x < 1 / 9 + δ) :
    (x : ℂ) ∈ closure (halfU δ ∩ Metric.ball 1 (8 / 9)) := by
  have hxlt : x < 1 := by linarith
  set s : ℝ := x - 1 / 9 with hsdef
  have hs0 : 0 < s := by rw [hsdef]; linarith
  have hsδ : s < δ := by rw [hsdef]; linarith
  rw [Metric.mem_closure_iff]
  intro ε hε
  set t : ℝ := min (ε / 4) (min ((δ - s) / 4) ((8 / 9 - (1 - x)) / 4)) with htdef
  have ht0 : 0 < t := by
    rw [htdef]
    exact lt_min (by linarith) (lt_min (by linarith) (by linarith))
  have htε : t < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hts : t ≤ (δ - s) / 4 := le_trans (min_le_right _ _) (min_le_left _ _)
  have ht8 : t ≤ (8 / 9 - (1 - x)) / 4 := le_trans (min_le_right _ _) (min_le_right _ _)
  have hsq : ∀ (a b : ℝ), ‖((a : ℝ) : ℂ) + ((b : ℝ) : ℂ) * Complex.I‖ ^ 2 = a ^ 2 + b ^ 2 := by
    intro a b
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_I_re, Complex.mul_I_im]
    ring
  have hball : ‖((s : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I‖ < δ := by
    have hsq' := hsq s t
    have hkey : s ^ 2 + t ^ 2 < δ ^ 2 := by
      have h1 : t ^ 2 ≤ ((δ - s) / 4) ^ 2 := pow_le_pow_left₀ (le_of_lt ht0) hts 2
      have h1' : 16 * t ^ 2 ≤ (δ - s) ^ 2 := by nlinarith [h1]
      have hf : 17 * s ^ 2 - 2 * δ * s - 15 * δ ^ 2 < 0 := by
        have h0 : (s - δ) * (17 * s + 15 * δ) < 0 :=
          mul_neg_of_neg_of_pos (by linarith) (by linarith)
        have h1 : (s - δ) * (17 * s + 15 * δ) = 17 * s ^ 2 - 2 * δ * s - 15 * δ ^ 2 := by ring
        rwa [h1] at h0
      nlinarith [hf, h1']
    have hnn : (0 : ℝ) ≤ ‖((s : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I‖ := norm_nonneg _
    nlinarith [hsq', hkey, hnn, hδ]
  have hball1 : ‖((x - 1 : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I‖ < 8 / 9 := by
    have hsq' := hsq (x - 1) t
    have hkey : (x - 1) ^ 2 + t ^ 2 < (8 / 9) ^ 2 := by
      have h1 : t ^ 2 ≤ ((8 / 9 - (1 - x)) / 4) ^ 2 := pow_le_pow_left₀ (le_of_lt ht0) ht8 2
      have h1' : 16 * t ^ 2 ≤ (8 / 9 - (1 - x)) ^ 2 := by nlinarith [h1]
      have hf : 17 * (1 - x) ^ 2 - 2 * (8 / 9) * (1 - x) - 15 * (8 / 9) ^ 2 < 0 := by
        have h0 : (1 - x - 8 / 9) * (17 * (1 - x) + 15 * (8 / 9)) < 0 :=
          mul_neg_of_neg_of_pos (by linarith) (by linarith)
        have h1 : (1 - x - 8 / 9) * (17 * (1 - x) + 15 * (8 / 9))
            = 17 * (1 - x) ^ 2 - 2 * (8 / 9) * (1 - x) - 15 * (8 / 9) ^ 2 := by ring
        rwa [h1] at h0
      have hxeq : (x - 1) ^ 2 = (1 - x) ^ 2 := by ring
      rw [hxeq]
      nlinarith [hf, h1']
    have hnn : (0 : ℝ) ≤ ‖((x - 1 : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I‖ := norm_nonneg _
    nlinarith [hsq', hkey, hnn]
  refine ⟨(x : ℂ) + ((t : ℝ) : ℂ) * Complex.I, ?_, ?_⟩
  · -- membership
    have hsub1 : (x : ℂ) + ((t : ℝ) : ℂ) * Complex.I - ninth =
        ((s : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I := by
      rw [hsdef, ninth]; push_cast; ring
    have hsub2 : (x : ℂ) + ((t : ℝ) : ℂ) * Complex.I - 1 =
        ((x - 1 : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I := by push_cast; ring
    constructor
    · constructor
      · rw [Metric.mem_ball, Complex.dist_eq, hsub1]; exact hball
      · have him : ((x : ℂ) + ((t : ℝ) : ℂ) * Complex.I).im = t := by simp
        rw [Set.mem_ofPred_eq, him]; exact ht0
    · rw [Metric.mem_ball, Complex.dist_eq, hsub2]; exact hball1
  · -- dist
    rw [Complex.dist_eq]
    have hsub : (x : ℂ) - ((x : ℂ) + ((t : ℝ) : ℂ) * Complex.I) = -(((t : ℝ) : ℂ) * Complex.I) := by
      ring
    rw [hsub, norm_neg, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos ht0]
    linarith


private lemma mem_closure_halfL_cap {δ : ℝ} (hδ : 0 < δ) (hδ20 : δ ≤ 1 / 20) {x : ℝ}
    (hx1 : 1 / 9 < x) (hx2 : x < 1 / 9 + δ) :
    (x : ℂ) ∈ closure (halfL δ ∩ Metric.ball 1 (8 / 9)) := by
  have hxlt : x < 1 := by linarith
  set s : ℝ := x - 1 / 9 with hsdef
  have hs0 : 0 < s := by rw [hsdef]; linarith
  have hsδ : s < δ := by rw [hsdef]; linarith
  rw [Metric.mem_closure_iff]
  intro ε hε
  set t : ℝ := min (ε / 4) (min ((δ - s) / 4) ((8 / 9 - (1 - x)) / 4)) with htdef
  have ht0 : 0 < t := by
    rw [htdef]
    exact lt_min (by linarith) (lt_min (by linarith) (by linarith))
  have htε : t < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hts : t ≤ (δ - s) / 4 := le_trans (min_le_right _ _) (min_le_left _ _)
  have ht8 : t ≤ (8 / 9 - (1 - x)) / 4 := le_trans (min_le_right _ _) (min_le_right _ _)
  have hsq : ∀ (a b : ℝ), ‖((a : ℝ) : ℂ) - ((b : ℝ) : ℂ) * Complex.I‖ ^ 2 = a ^ 2 + b ^ 2 := by
    intro a b
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_I_re, Complex.mul_I_im]
    ring
  have hball : ‖((s : ℝ) : ℂ) - ((t : ℝ) : ℂ) * Complex.I‖ < δ := by
    have hsq' := hsq s t
    have hkey : s ^ 2 + t ^ 2 < δ ^ 2 := by
      have h1 : t ^ 2 ≤ ((δ - s) / 4) ^ 2 := pow_le_pow_left₀ (le_of_lt ht0) hts 2
      have h1' : 16 * t ^ 2 ≤ (δ - s) ^ 2 := by nlinarith [h1]
      have hf : 17 * s ^ 2 - 2 * δ * s - 15 * δ ^ 2 < 0 := by
        have h0 : (s - δ) * (17 * s + 15 * δ) < 0 :=
          mul_neg_of_neg_of_pos (by linarith) (by linarith)
        have h1 : (s - δ) * (17 * s + 15 * δ) = 17 * s ^ 2 - 2 * δ * s - 15 * δ ^ 2 := by ring
        rwa [h1] at h0
      nlinarith [hf, h1']
    have hnn : (0 : ℝ) ≤ ‖((s : ℝ) : ℂ) - ((t : ℝ) : ℂ) * Complex.I‖ := norm_nonneg _
    nlinarith [hsq', hkey, hnn, hδ]
  have hball1 : ‖((x - 1 : ℝ) : ℂ) - ((t : ℝ) : ℂ) * Complex.I‖ < 8 / 9 := by
    have hsq' := hsq (x - 1) t
    have hkey : (x - 1) ^ 2 + t ^ 2 < (8 / 9) ^ 2 := by
      have h1 : t ^ 2 ≤ ((8 / 9 - (1 - x)) / 4) ^ 2 := pow_le_pow_left₀ (le_of_lt ht0) ht8 2
      have h1' : 16 * t ^ 2 ≤ (8 / 9 - (1 - x)) ^ 2 := by nlinarith [h1]
      have hf : 17 * (1 - x) ^ 2 - 2 * (8 / 9) * (1 - x) - 15 * (8 / 9) ^ 2 < 0 := by
        have h0 : (1 - x - 8 / 9) * (17 * (1 - x) + 15 * (8 / 9)) < 0 :=
          mul_neg_of_neg_of_pos (by linarith) (by linarith)
        have h1 : (1 - x - 8 / 9) * (17 * (1 - x) + 15 * (8 / 9))
            = 17 * (1 - x) ^ 2 - 2 * (8 / 9) * (1 - x) - 15 * (8 / 9) ^ 2 := by ring
        rwa [h1] at h0
      have hxeq : (x - 1) ^ 2 = (1 - x) ^ 2 := by ring
      rw [hxeq]
      nlinarith [hf, h1']
    have hnn : (0 : ℝ) ≤ ‖((x - 1 : ℝ) : ℂ) - ((t : ℝ) : ℂ) * Complex.I‖ := norm_nonneg _
    nlinarith [hsq', hkey, hnn]
  have hsub1 : (x : ℂ) - ((t : ℝ) : ℂ) * Complex.I - ninth =
      ((s : ℝ) : ℂ) - ((t : ℝ) : ℂ) * Complex.I := by
    rw [hsdef, ninth]; push_cast; ring
  have hsub2 : (x : ℂ) - ((t : ℝ) : ℂ) * Complex.I - 1 =
      ((x - 1 : ℝ) : ℂ) - ((t : ℝ) : ℂ) * Complex.I := by push_cast; ring
  refine ⟨(x : ℂ) - ((t : ℝ) : ℂ) * Complex.I, ?_, ?_⟩
  · constructor
    · constructor
      · rw [Metric.mem_ball, Complex.dist_eq, hsub1]; exact hball
      · have him : ((x : ℂ) - ((t : ℝ) : ℂ) * Complex.I).im = -t := by simp
        rw [Set.mem_ofPred_eq, him]; linarith
    · rw [Metric.mem_ball, Complex.dist_eq, hsub2]; exact hball1
  · rw [Complex.dist_eq]
    have hsub : (x : ℂ) - ((x : ℂ) - ((t : ℝ) : ℂ) * Complex.I) = ((t : ℝ) : ℂ) * Complex.I := by ring
    rw [hsub, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos ht0]
    linarith


/-- **The jump relation.**  For real `x ∈ (1/9, 1/9+δ)` the difference of the two one-sided
values of `D` at `x` (the two certificates `hUeq`, `hLeq`) equals `(π²c/2)·u_h(x)`: the factor
`log (z-1)` jumps by `-2πi` while `E1` (holomorphic at `x`) does not. -/
private lemma key_rel
    {y9 : ℂ → ℂ} {δ : ℝ} (hδpos : 0 < δ) (hδ20 : δ ≤ 1 / 20)
    (c : ℤ) {D E1 : ℂ → ℂ}
    (hE1eq : ∀ z ∈ Om1 ∩ Metric.ball 1 (8 / 9),
      D z = E1 z + (Real.pi * Complex.I * (c : ℂ) / 4) * uh z * Complex.log (z - 1))
    {hUf hLf hlf : ℂ → ℂ}
    (hUfd : DifferentiableOn ℂ hUf (Metric.ball ninth δ))
    (hLfd : DifferentiableOn ℂ hLf (Metric.ball ninth δ))
    (hlfd : DifferentiableOn ℂ hlf (Metric.ball ninth δ))
    (hy9d : DifferentiableOn ℂ y9 (Metric.ball ninth δ))
    {κU κL lam : ℂ}
    (hUeq : ∀ z ∈ halfU δ, D z = κU * y9 z * Complex.log (z - ninth) + hUf z)
    (hLeq : ∀ z ∈ halfL δ, D z = κL * y9 z * Complex.log (z - ninth) + hLf z)
    (hlens : ∀ z ∈ kappaLens δ, uh z = lam * y9 z * Complex.log (z - ninth) + hlf z)
    (hE1at : ∀ x : ℝ, x ∈ Set.Ioo (1 / 9) 1 → DifferentiableAt ℂ E1 (x : ℂ)) :
    ∀ x : ℝ, x ∈ Set.Ioo (1 / 9) (1 / 9 + δ) →
      ((κL - κU) - (Real.pi ^ 2 * (c : ℂ) / 2) * lam) * y9 (x : ℂ)
          * Complex.log ((x : ℂ) - ninth)
        = (Real.pi ^ 2 * (c : ℂ) / 2) * hlf (x : ℂ) - (hLf (x : ℂ) - hUf (x : ℂ)) := by
  intro x hx
  obtain ⟨hx1, hx2⟩ := hx
  have hxlt1 : x < 1 := by linarith
  set xc : ℂ := (x : ℂ) with hxcdef
  have hxre : xc.re = x := by rw [hxcdef]; simp
  have hxim : xc.im = 0 := by rw [hxcdef]; simp
  have hxball9 : xc ∈ Metric.ball ninth δ := by
    rw [Metric.mem_ball, Complex.dist_eq]
    have h : xc - ninth = ((x - 1 / 9 : ℝ) : ℂ) := by rw [hxcdef, ninth]; push_cast; ring
    rw [h, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : (0:ℝ) < x - 1/9)]
    linarith
  have hxball1 : xc ∈ Metric.ball 1 (8 / 9) := by
    rw [Metric.mem_ball, Complex.dist_eq]
    have h : xc - 1 = ((x - 1 : ℝ) : ℂ) := by rw [hxcdef]; push_cast; ring
    rw [h, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith : x - 1 < 0)]
    linarith
  have hmem9 : (xc - ninth).re = x - 1 / 9 := by
    rw [Complex.sub_re, hxre]; norm_num [ninth]
  have hlogN : ContinuousAt (fun z : ℂ => Complex.log (z - ninth)) xc := by
    have hmem : xc - ninth ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]; left; rw [hmem9]; linarith
    exact ((Complex.differentiableAt_log hmem).comp xc (differentiableAt_id.sub_const ninth)).continuousAt
  have hy9c : ContinuousAt y9 xc :=
    hy9d.continuousOn.continuousAt (Metric.isOpen_ball.mem_nhds hxball9)
  have hE1c : ContinuousAt E1 xc := (hE1at x ⟨hx1, hxlt1⟩).continuousAt
  have huhc : ContinuousAt uh xc :=
    uh_ode.1.continuousOn.continuousAt (Metric.isOpen_ball.mem_nhds hxball1)
  have hUfc : ContinuousAt hUf xc :=
    hUfd.continuousOn.continuousAt (Metric.isOpen_ball.mem_nhds hxball9)
  have hLfc : ContinuousAt hLf xc :=
    hLfd.continuousOn.continuousAt (Metric.isOpen_ball.mem_nhds hxball9)
  have hUrel : κU * y9 xc * Complex.log (xc - ninth) + hUf xc
      = E1 xc + (Real.pi * Complex.I * (c : ℂ) / 4) * uh xc
          * ((Real.log (1 - x) : ℂ) + Real.pi * Complex.I) := by
    haveI : (𝓝[halfU δ ∩ Metric.ball 1 (8 / 9)] xc).NeBot :=
      mem_closure_iff_nhdsWithin_neBot.mp (mem_closure_halfU_cap hδpos hδ20 hx1 hx2)
    have h1 : Tendsto D (𝓝[halfU δ ∩ Metric.ball 1 (8 / 9)] xc)
        (𝓝 (κU * y9 xc * Complex.log (xc - ninth) + hUf xc)) := by
      have hcert : Tendsto (fun z : ℂ => κU * y9 z * Complex.log (z - ninth) + hUf z)
          (𝓝[halfU δ ∩ Metric.ball 1 (8 / 9)] xc)
          (𝓝 (κU * y9 xc * Complex.log (xc - ninth) + hUf xc)) :=
        Tendsto.add
          (Tendsto.mul (Tendsto.mul tendsto_const_nhds
            (hy9c.tendsto.mono_left nhdsWithin_le_nhds))
            (hlogN.tendsto.mono_left nhdsWithin_le_nhds))
          (hUfc.tendsto.mono_left nhdsWithin_le_nhds)
      exact Filter.Tendsto.congr' (by
        filter_upwards [self_mem_nhdsWithin] with z hz
        exact (hUeq z hz.1).symm) hcert
    have h2 : Tendsto D (𝓝[halfU δ ∩ Metric.ball 1 (8 / 9)] xc)
        (𝓝 (E1 xc + (Real.pi * Complex.I * (c : ℂ) / 4) * uh xc
          * ((Real.log (1 - x) : ℂ) + Real.pi * Complex.I))) := by
      have hlogU : Tendsto (fun z : ℂ => Complex.log (z - 1))
          (𝓝[halfU δ ∩ Metric.ball 1 (8 / 9)] xc)
          (𝓝 ((Real.log (1 - x) : ℂ) + Real.pi * Complex.I)) :=
        (tendsto_log_sub_one_of_lt hxlt1).mono_left
          (nhdsWithin_mono xc (fun z hz => hz.1.2))
      have hexpr : Tendsto
          (fun z : ℂ => E1 z + (Real.pi * Complex.I * (c : ℂ) / 4) * uh z * Complex.log (z - 1))
          (𝓝[halfU δ ∩ Metric.ball 1 (8 / 9)] xc)
          (𝓝 (E1 xc + (Real.pi * Complex.I * (c : ℂ) / 4) * uh xc
            * ((Real.log (1 - x) : ℂ) + Real.pi * Complex.I))) :=
        Tendsto.add (hE1c.tendsto.mono_left nhdsWithin_le_nhds)
          (Tendsto.mul (Tendsto.mul tendsto_const_nhds
            (huhc.tendsto.mono_left nhdsWithin_le_nhds)) hlogU)
      exact Filter.Tendsto.congr' (by
        filter_upwards [self_mem_nhdsWithin] with z hz
        exact (hE1eq z ⟨halfU_subset_Om1 δ hz.1, hz.2⟩).symm) hexpr
    exact tendsto_nhds_unique h1 h2
  have hLrel : κL * y9 xc * Complex.log (xc - ninth) + hLf xc
      = E1 xc + (Real.pi * Complex.I * (c : ℂ) / 4) * uh xc
          * ((Real.log (1 - x) : ℂ) - Real.pi * Complex.I) := by
    haveI : (𝓝[halfL δ ∩ Metric.ball 1 (8 / 9)] xc).NeBot :=
      mem_closure_iff_nhdsWithin_neBot.mp (mem_closure_halfL_cap hδpos hδ20 hx1 hx2)
    have h1 : Tendsto D (𝓝[halfL δ ∩ Metric.ball 1 (8 / 9)] xc)
        (𝓝 (κL * y9 xc * Complex.log (xc - ninth) + hLf xc)) := by
      have hcert : Tendsto (fun z : ℂ => κL * y9 z * Complex.log (z - ninth) + hLf z)
          (𝓝[halfL δ ∩ Metric.ball 1 (8 / 9)] xc)
          (𝓝 (κL * y9 xc * Complex.log (xc - ninth) + hLf xc)) :=
        Tendsto.add
          (Tendsto.mul (Tendsto.mul tendsto_const_nhds
            (hy9c.tendsto.mono_left nhdsWithin_le_nhds))
            (hlogN.tendsto.mono_left nhdsWithin_le_nhds))
          (hLfc.tendsto.mono_left nhdsWithin_le_nhds)
      exact Filter.Tendsto.congr' (by
        filter_upwards [self_mem_nhdsWithin] with z hz
        exact (hLeq z hz.1).symm) hcert
    have h2 : Tendsto D (𝓝[halfL δ ∩ Metric.ball 1 (8 / 9)] xc)
        (𝓝 (E1 xc + (Real.pi * Complex.I * (c : ℂ) / 4) * uh xc
          * ((Real.log (1 - x) : ℂ) - Real.pi * Complex.I))) := by
      have hlogL : Tendsto (fun z : ℂ => Complex.log (z - 1))
          (𝓝[halfL δ ∩ Metric.ball 1 (8 / 9)] xc)
          (𝓝 ((Real.log (1 - x) : ℂ) - Real.pi * Complex.I)) :=
        (tendsto_log_sub_one_gt hxlt1).mono_left
          (nhdsWithin_mono xc (fun z hz => hz.1.2))
      have hexpr : Tendsto
          (fun z : ℂ => E1 z + (Real.pi * Complex.I * (c : ℂ) / 4) * uh z * Complex.log (z - 1))
          (𝓝[halfL δ ∩ Metric.ball 1 (8 / 9)] xc)
          (𝓝 (E1 xc + (Real.pi * Complex.I * (c : ℂ) / 4) * uh xc
            * ((Real.log (1 - x) : ℂ) - Real.pi * Complex.I))) :=
        Tendsto.add (hE1c.tendsto.mono_left nhdsWithin_le_nhds)
          (Tendsto.mul (Tendsto.mul tendsto_const_nhds
            (huhc.tendsto.mono_left nhdsWithin_le_nhds)) hlogL)
      exact Filter.Tendsto.congr' (by
        filter_upwards [self_mem_nhdsWithin] with z hz
        exact (hE1eq z ⟨halfL_subset_Om1 δ hz.1, hz.2⟩).symm) hexpr
    exact tendsto_nhds_unique h1 h2
  -- the jump relation
  have hjump : (κL - κU) * y9 xc * Complex.log (xc - ninth) + (hLf xc - hUf xc)
      = (Real.pi ^ 2 * (c : ℂ) / 2) * uh xc := by
    have hsub : κL * y9 xc * Complex.log (xc - ninth) + hLf xc
        - (κU * y9 xc * Complex.log (xc - ninth) + hUf xc)
        = (Real.pi * Complex.I * (c : ℂ) / 4) * uh xc
            * ((Real.log (1 - x) : ℂ) - Real.pi * Complex.I)
          - (Real.pi * Complex.I * (c : ℂ) / 4) * uh xc
            * ((Real.log (1 - x) : ℂ) + Real.pi * Complex.I) := by
      linear_combination hLrel - hUrel
    have hval : (Real.pi * Complex.I * (c : ℂ) / 4) * uh xc
            * ((Real.log (1 - x) : ℂ) - Real.pi * Complex.I)
          - (Real.pi * Complex.I * (c : ℂ) / 4) * uh xc
            * ((Real.log (1 - x) : ℂ) + Real.pi * Complex.I)
        = (Real.pi ^ 2 * (c : ℂ) / 2) * uh xc := by
      have hI : Complex.I * Complex.I = (-1 : ℂ) := Complex.I_mul_I
      linear_combination (-(Real.pi ^ 2 * (c : ℂ) * uh xc / 2)) * hI
    rw [← hval]
    linear_combination hsub
  have huhcert : uh xc = lam * y9 xc * Complex.log (xc - ninth) + hlf xc :=
    hlens xc ⟨hxball9, hxball1⟩
  rw [huhcert] at hjump
  linear_combination hjump

/-- **Assembly.**  Given the analytic crux (the local holomorphic part of the jump at `1`
extends across `(1/9,1)`), the design's identity `(K)` follows: the difference of the two
one-sided log coefficients of `D` at `1/9` is the jump of the `log (z-1)`-term, i.e.
`(π²c/2)·λ` with `λ` the log coefficient of `u_h` on the lens. -/
private lemma main_of_crux (a b c : ℤ) (h : Submission.CDTPlan.ARel a b c)
    (HU HL : ℂ → ℂ)
    (hHU : DifferentiableOn ℂ HU SU ∧ (∀ z ∈ SU, LZ HU z = rhsZ b c z) ∧
      ∀ z ∈ SU ∩ ball 0 1, HU z = Hfun a b c z)
    (hHL : DifferentiableOn ℂ HL SL ∧ (∀ z ∈ SL, LZ HL z = rhsZ b c z) ∧
      ∀ z ∈ SL ∩ ball 0 1, HL z = Hfun a b c z)
    (y9 : ℂ → ℂ) (δ : ℝ) (hY : Y9 y9 δ)
    (D : ℂ → ℂ) (hD : DifferentiableOn ℂ D Om1) (hDL : ∀ z ∈ Om1, LZ D z = 0)
    (hDj : ∀ z ∈ SU ∩ SL, D z = HU z - HL z)
    (κU κL : ℂ) (hU : LogCoeff y9 δ (halfU δ) D κU) (hL : LogCoeff y9 δ (halfL δ) D κL)
    (hcrux : ∃ E1 : ℂ → ℂ,
      DifferentiableOn ℂ E1 (Om1 ∩ Metric.ball 1 (8 / 9)) ∧
      (∀ x : ℝ, x ∈ Set.Ioo (1 / 9) 1 → DifferentiableAt ℂ E1 (x : ℂ)) ∧
      ∀ z ∈ Om1 ∩ Metric.ball 1 (8 / 9),
        D z = E1 z + (Real.pi * Complex.I * (c : ℂ) / 4) * uh z * Complex.log (z - 1)) :
    ∃ lam : ℂ, lam ≠ 0 ∧ LogCoeff y9 δ (kappaLens δ) uh lam ∧
      κU - κL = -(Real.pi ^ 2 * (c : ℂ) / 2) * lam := by
  obtain ⟨hδpos, hδ20, hy9d, hy9ne, hy9ode⟩ := hY
  obtain ⟨lam, hlam_ne, hlam⟩ := uh_lens_logCoeff (δ := δ) ⟨hδpos, hδ20, hy9d, hy9ne, hy9ode⟩
  refine ⟨lam, hlam_ne, hlam, ?_⟩
  obtain ⟨hlf, hlfd, hlens⟩ := hlam
  obtain ⟨hUf, hUfd, hUeq⟩ := hU
  obtain ⟨hLf, hLfd, hLeq⟩ := hL
  obtain ⟨E1, hE1d, hE1at, hE1eq⟩ := hcrux
  set C : ℂ := (κL - κU) - (Real.pi ^ 2 * (c : ℂ) / 2) * lam with hCdef
  set φ : ℂ → ℂ := fun z => (Real.pi ^ 2 * (c : ℂ) / 2) * hlf z - (hLf z - hUf z) with hφdef
  have hrel := key_rel hδpos hδ20 c hE1eq hUfd hLfd hlfd hy9d hUeq hLeq hlens hE1at
  have hb9 : ninth ∈ Metric.ball ninth δ := Metric.mem_ball_self hδpos
  have h9nhds : Metric.ball ninth δ ∈ 𝓝 ninth := Metric.isOpen_ball.mem_nhds hb9
  have hφc : ContinuousAt φ ninth := by
    rw [hφdef]
    exact ContinuousAt.sub
      (ContinuousAt.const_mul (hlfd.continuousOn.continuousAt h9nhds) _)
      (ContinuousAt.sub (hLfd.continuousOn.continuousAt h9nhds)
        (hUfd.continuousOn.continuousAt h9nhds))
  have hC0 : C = 0 := by
    by_contra hCne
    have hy9pos : 0 < ‖y9 ninth‖ := norm_pos_iff.mpr hy9ne
    set xn : ℕ → ℝ := fun n => 1 / 9 + δ / (2 * ((n : ℝ) + 2)) with hxndef
    have hxnmem : ∀ n, xn n ∈ Set.Ioo (1 / 9) (1 / 9 + δ) := by
      intro n
      have hpos : 0 < δ / (2 * ((n : ℝ) + 2)) := by positivity
      have hlt : δ / (2 * ((n : ℝ) + 2)) < δ := by
        rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * ((n : ℝ) + 2))]
        have h2 : (1 : ℝ) < 2 * ((n : ℝ) + 2) := by
          have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
          linarith
        nlinarith [hδpos, h2]
      rw [hxndef]; constructor <;> linarith
    have hxn_tend : Tendsto (fun n : ℕ => ((xn n : ℝ) : ℂ)) atTop (𝓝 ninth) := by
      have hk : Tendsto (fun n : ℕ => δ / (2 * ((n : ℝ) + 2))) atTop (𝓝 0) := by
        have h3 : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
        have h5 : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop := by
          have h := Filter.Tendsto.add_atTop
            (tendsto_const_nhds : Tendsto (fun _ : ℕ => (2:ℝ)) atTop (𝓝 2)) h3
          simpa [add_comm] using h
        have h6 : Tendsto (fun n : ℕ => 2 * ((n : ℝ) + 2)) atTop atTop :=
          Filter.Tendsto.const_mul_atTop (by norm_num : (0:ℝ) < 2) h5
        exact h6.const_div_atTop δ
      have h1 : Tendsto (fun n : ℕ => xn n) atTop (𝓝 (1 / 9)) := by
        have h := Filter.Tendsto.add
          (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 / 9 : ℝ)) atTop (𝓝 (1 / 9))) hk
        simpa [hxndef] using h
      have h2 := (Complex.continuous_ofReal.tendsto (1 / 9)).comp h1
      simpa [Function.comp_def, ninth] using h2
    have hreln : ∀ n, C * y9 ((xn n : ℝ) : ℂ) * Complex.log (((xn n : ℝ) : ℂ) - ninth)
        = φ ((xn n : ℝ) : ℂ) := fun n => hrel (xn n) (hxnmem n)
    have hnorm : ∀ n, ‖C‖ * ‖y9 ((xn n : ℝ) : ℂ)‖
        * ‖Complex.log (((xn n : ℝ) : ℂ) - ninth)‖ = ‖φ ((xn n : ℝ) : ℂ)‖ := by
      intro n
      rw [← hreln n, norm_mul, norm_mul]
    have hlogval : ∀ n, ‖Complex.log (((xn n : ℝ) : ℂ) - ninth)‖
        = Real.log (2 * ((n : ℝ) + 2) / δ) := by
      intro n
      have ht : (0 : ℝ) < δ / (2 * ((n : ℝ) + 2)) := by positivity
      have h2 : (1 : ℝ) < 2 * ((n : ℝ) + 2) := by
        have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      have hval : δ / (2 * ((n : ℝ) + 2)) < 1 := by
        rw [div_lt_one (by positivity : (0:ℝ) < 2 * ((n : ℝ) + 2))]; linarith
      have hsub : ((xn n : ℝ) : ℂ) - ninth = ((δ / (2 * ((n : ℝ) + 2)) : ℝ) : ℂ) := by
        rw [hxndef, ninth]; push_cast; ring
      rw [hsub]
      rw [← Complex.ofReal_log (le_of_lt ht), Complex.norm_real, Real.norm_eq_abs, abs_of_neg (Real.log_neg ht hval)]
      have hkey : Real.log (2 * ((n : ℝ) + 2) / δ)
          = -Real.log (δ / (2 * ((n : ℝ) + 2))) := by
        rw [show 2 * ((n : ℝ) + 2) / δ = (δ / (2 * ((n : ℝ) + 2)))⁻¹ by rw [inv_div],
          Real.log_inv]
      rw [hkey]
    have hy9ev : ∀ᶠ n : ℕ in atTop, ‖y9 ninth‖ / 2 ≤ ‖y9 ((xn n : ℝ) : ℂ)‖ := by
      have hcont : Tendsto (fun n : ℕ => y9 ((xn n : ℝ) : ℂ)) atTop (𝓝 (y9 ninth)) :=
        (hy9d.continuousOn.continuousAt h9nhds).tendsto.comp hxn_tend
      have hev := Filter.eventually_atTop.mpr (Metric.tendsto_atTop.mp hcont (‖y9 ninth‖ / 2)
        (by positivity))
      filter_upwards [hev] with n hn
      have h1 : ‖y9 ((xn n : ℝ) : ℂ) - y9 ninth‖ < ‖y9 ninth‖ / 2 := by
        simpa [Complex.dist_eq] using hn
      have h2 : ‖y9 ninth‖ ≤ ‖y9 ((xn n : ℝ) : ℂ)‖ + ‖y9 ((xn n : ℝ) : ℂ) - y9 ninth‖ := by
        have h3 := norm_add_le (y9 ((xn n : ℝ) : ℂ)) (y9 ninth - y9 ((xn n : ℝ) : ℂ))
        have h4 : y9 ((xn n : ℝ) : ℂ) + (y9 ninth - y9 ((xn n : ℝ) : ℂ)) = y9 ninth := by ring
        rw [h4] at h3
        calc ‖y9 ninth‖ ≤ ‖y9 ((xn n : ℝ) : ℂ)‖ + ‖y9 ninth - y9 ((xn n : ℝ) : ℂ)‖ := h3
          _ = ‖y9 ((xn n : ℝ) : ℂ)‖ + ‖y9 ((xn n : ℝ) : ℂ) - y9 ninth‖ := by rw [norm_sub_rev]
      linarith
    have hφev : ∀ᶠ n : ℕ in atTop, ‖φ ((xn n : ℝ) : ℂ)‖ ≤ ‖φ ninth‖ + 1 := by
      have hcont : Tendsto (fun n : ℕ => φ ((xn n : ℝ) : ℂ)) atTop (𝓝 (φ ninth)) :=
        hφc.tendsto.comp hxn_tend
      have hev := Filter.eventually_atTop.mpr (Metric.tendsto_atTop.mp hcont 1 (by norm_num))
      filter_upwards [hev] with n hn
      have h1 : ‖φ ((xn n : ℝ) : ℂ) - φ ninth‖ < 1 := by simpa [Complex.dist_eq] using hn
      have h2 : ‖φ ((xn n : ℝ) : ℂ)‖ ≤ ‖φ ((xn n : ℝ) : ℂ) - φ ninth‖ + ‖φ ninth‖ := by
        have h3 := norm_add_le (φ ((xn n : ℝ) : ℂ) - φ ninth) (φ ninth)
        have h4 : φ ((xn n : ℝ) : ℂ) - φ ninth + φ ninth = φ ((xn n : ℝ) : ℂ) := by ring
        rw [h4] at h3; exact h3
      linarith
    have hlogtend : Tendsto (fun n : ℕ => Real.log (2 * ((n : ℝ) + 2) / δ)) atTop atTop := by
      have h3 : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
      have h5 : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop := by
        have h := Filter.Tendsto.add_atTop
          (tendsto_const_nhds : Tendsto (fun _ : ℕ => (2:ℝ)) atTop (𝓝 2)) h3
        simpa [add_comm] using h
      have h6 : Tendsto (fun n : ℕ => 2 * ((n : ℝ) + 2)) atTop atTop :=
        Filter.Tendsto.const_mul_atTop (by norm_num : (0:ℝ) < 2) h5
      exact Real.tendsto_log_atTop.comp (h6.atTop_div_const hδpos)
    have hbound : ∀ᶠ n : ℕ in atTop,
        ‖C‖ * (‖y9 ninth‖ / 2) * Real.log (2 * ((n : ℝ) + 2) / δ) ≤ ‖φ ninth‖ + 1 := by
      filter_upwards [hy9ev, hφev] with n h1 h2
      calc ‖C‖ * (‖y9 ninth‖ / 2) * Real.log (2 * ((n : ℝ) + 2) / δ)
          = ‖C‖ * (‖y9 ninth‖ / 2) * ‖Complex.log (((xn n : ℝ) : ℂ) - ninth)‖ := by
            rw [hlogval n]
        _ ≤ ‖C‖ * ‖y9 ((xn n : ℝ) : ℂ)‖ * ‖Complex.log (((xn n : ℝ) : ℂ) - ninth)‖ := by
            have h3 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (norm_nonneg C))
              (norm_nonneg (Complex.log (((xn n : ℝ) : ℂ) - ninth)))
            linarith
        _ = ‖φ ((xn n : ℝ) : ℂ)‖ := hnorm n
        _ ≤ ‖φ ninth‖ + 1 := h2
    have hthr : ∀ᶠ n : ℕ in atTop,
        ‖φ ninth‖ + 1 < ‖C‖ * (‖y9 ninth‖ / 2) * Real.log (2 * ((n : ℝ) + 2) / δ) :=
      (Filter.Tendsto.const_mul_atTop (by positivity)
        hlogtend).eventually_gt_atTop (‖φ ninth‖ + 1)
    obtain ⟨n, hn1, hn2⟩ := (hbound.and hthr).exists
    linarith
  have hκ : κL - κU = (Real.pi ^ 2 * (c : ℂ) / 2) * lam := by
    rw [hCdef] at hC0
    linear_combination hC0
  linear_combination -hκ

/-! ## The requested lemma -/

/-- Design identity `(K)`: the difference of the two log coefficients of the jump `D` at `1/9` is
`-(π² c / 2) · λ`, where `λ` is the (non-zero) log coefficient of `uh` on the lens
`ball (1/9) δ ∩ ball 1 (8/9)`.

`κU = κL` is NOT true here (the two half-discs are not connected through the identity theorem: every
real point of `ball (1/9) δ` lies on the slit `(-∞,1]`); numerically `κU - κL = -32.6483885562…`
for `c = -4` and `0` for `c = 0`.  The full route and the numerical check are in
`Submission/Work/A14D/_num/README.md` (continuation of the ODE; the key steps are: refine
`D_local_at_one` to `D = -2πi·e1 + (π i c/4)·uh·log (z-1)`, put `e2 := -(c/16)·uh` and
`N := e1 + 2·e2·ell`, get `D = -2πi N ± 4π² e2` on the two sides of `ball 1 δ`, continue `N`, `e2`
to the convex `Sstar = ball 0 1 ∩ {1/9 < re}` on which `ell` is holomorphic, and use linearity of
the log coefficient: `κU - κL = 8π²·Λ(e2) = -(π²c/2)·λ`). -/
theorem kappaU_sub_kappaL (a b c : ℤ) (h : Submission.CDTPlan.ARel a b c)
    (HU HL : ℂ → ℂ)
    (hHU : DifferentiableOn ℂ HU SU ∧ (∀ z ∈ SU, LZ HU z = rhsZ b c z) ∧
      ∀ z ∈ SU ∩ ball 0 1, HU z = Hfun a b c z)
    (hHL : DifferentiableOn ℂ HL SL ∧ (∀ z ∈ SL, LZ HL z = rhsZ b c z) ∧
      ∀ z ∈ SL ∩ ball 0 1, HL z = Hfun a b c z)
    (y9 : ℂ → ℂ) (δ : ℝ) (hY : Y9 y9 δ)
    (D : ℂ → ℂ) (hD : DifferentiableOn ℂ D Om1) (hDL : ∀ z ∈ Om1, LZ D z = 0)
    (hDj : ∀ z ∈ SU ∩ SL, D z = HU z - HL z)
    (κU κL : ℂ) (hU : LogCoeff y9 δ (halfU δ) D κU) (hL : LogCoeff y9 δ (halfL δ) D κL) :
    ∃ lam : ℂ, lam ≠ 0 ∧ LogCoeff y9 δ (Metric.ball ninth δ ∩ Metric.ball 1 (8 / 9)) uh lam ∧
      κU - κL = -(Real.pi ^ 2 * (c : ℂ) / 2) * lam := by
  exact main_of_crux a b c h HU HL hHU hHL y9 δ hY D hD hDL hDj κU κL hU hL
    (crux_jump a b c h HU HL hHU hHL D hD hDL hDj)

end

end Work.A14D
