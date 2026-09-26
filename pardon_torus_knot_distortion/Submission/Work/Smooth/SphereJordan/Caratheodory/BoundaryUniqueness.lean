import Mathlib
import Submission.Work.Smooth.SphereJordan.Caratheodory.HalfPlaneReflection

/-!
# Boundary uniqueness for holomorphic functions on the disc

If `f` is holomorphic on the unit disc, continuous on its closure, and vanishes on a neighbourhood
(in the unit circle) of a boundary point `z₀`, then `f` vanishes identically.

The proof straightens the boundary at `z₀` with the Möbius map `mobMap z₀` (which sends `z₀ ↦ 0`
and the disc to the upper half-plane), applies the half-plane boundary-uniqueness lemma
`half_plane_eq_zero` (proved in `HalfPlaneReflection.lean` by Schwarz reflection), and concludes
with the identity theorem.
-/

noncomputable section

open Set Metric Filter Complex

open scoped Topology

namespace Work.Smooth.SphereJordan.Caratheodory

/-! ## The straightening Möbius map -/

/-- The Möbius map sending the boundary point `z₀` to `0` and the centre of the disc to `I`. -/
def mobMap (z₀ : ℂ) (w : ℂ) : ℂ := -Complex.I * (w - z₀) / (w + z₀)

/-- Its inverse, sending `I` to `0` and `0` to `z₀`, and the upper half-plane into the disc. -/
def mobInv (z₀ : ℂ) (u : ℂ) : ℂ := z₀ * (Complex.I - u) / (Complex.I + u)

@[simp] lemma mobMap_apply (z₀ w : ℂ) : mobMap z₀ w = -Complex.I * (w - z₀) / (w + z₀) := rfl

@[simp] lemma mobInv_apply (z₀ u : ℂ) : mobInv z₀ u = z₀ * (Complex.I - u) / (Complex.I + u) := rfl

lemma mobMap_self (z₀ : ℂ) : mobMap z₀ z₀ = 0 := by
  simp only [mobMap, sub_self, mul_zero, zero_div]

lemma mobMap_zero {z₀ : ℂ} (hz₀ : z₀ ≠ 0) : mobMap z₀ 0 = Complex.I := by
  show (-Complex.I) * (0 - z₀) / (0 + z₀) = Complex.I
  rw [zero_sub, zero_add, neg_mul_neg, mul_div_assoc, div_self hz₀, mul_one]

lemma mobInv_zero {z₀ : ℂ} (hz₀ : z₀ ≠ 0) : mobInv z₀ 0 = z₀ := by
  show z₀ * (Complex.I - 0) / (Complex.I + 0) = z₀
  rw [sub_zero, add_zero, mul_div_assoc, div_self Complex.I_ne_zero, mul_one]

/-! ## The two maps are inverse to each other -/

lemma mobInv_add_ne_zero {z₀ u : ℂ} (hz₀ : z₀ ≠ 0) (hu : Complex.I + u ≠ 0) :
    mobInv z₀ u + z₀ ≠ 0 := by
  have hval : mobInv z₀ u + z₀ = z₀ * (2 * Complex.I) / (Complex.I + u) := by
    simp only [mobInv]
    field_simp
    ring
  rw [hval]
  exact div_ne_zero (mul_ne_zero hz₀ (by norm_num)) hu

lemma mobMap_mobInv {z₀ u : ℂ} (hz₀ : z₀ ≠ 0) (hu : Complex.I + u ≠ 0) :
    mobMap z₀ (mobInv z₀ u) = u := by
  rw [mobMap, div_eq_iff (mobInv_add_ne_zero hz₀ hu)]
  simp only [mobInv]
  field_simp
  ring

lemma mobMap_add_ne_zero {z₀ w : ℂ} (hz₀ : z₀ ≠ 0) (hw : w + z₀ ≠ 0) :
    Complex.I + mobMap z₀ w ≠ 0 := by
  have hval : Complex.I + mobMap z₀ w = Complex.I * (2 * z₀) / (w + z₀) := by
    simp only [mobMap]
    field_simp
    ring
  rw [hval]
  exact div_ne_zero (mul_ne_zero Complex.I_ne_zero (mul_ne_zero (by norm_num) hz₀)) hw

lemma mobInv_mobMap {z₀ w : ℂ} (hz₀ : z₀ ≠ 0) (hw : w + z₀ ≠ 0) :
    mobInv z₀ (mobMap z₀ w) = w := by
  simp only [mobInv]
  rw [div_eq_iff (mobMap_add_ne_zero hz₀ hw)]
  simp only [mobMap]
  field_simp
  ring

/-! ## Elementary norm and imaginary-part computations -/

lemma normSq_I_sub (u : ℂ) : Complex.normSq (Complex.I - u) = u.re ^ 2 + (1 - u.im) ^ 2 := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.I_re, Complex.I_im]
  ring

lemma normSq_I_add (u : ℂ) : Complex.normSq (Complex.I + u) = u.re ^ 2 + (1 + u.im) ^ 2 := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im]
  ring

lemma normSq_I_sub_le_iff (u : ℂ) :
    Complex.normSq (Complex.I - u) ≤ Complex.normSq (Complex.I + u) ↔ 0 ≤ u.im := by
  rw [normSq_I_sub, normSq_I_add]
  constructor <;> intro h <;> nlinarith [h]

lemma normSq_I_sub_lt_iff (u : ℂ) :
    Complex.normSq (Complex.I - u) < Complex.normSq (Complex.I + u) ↔ 0 < u.im := by
  rw [normSq_I_sub, normSq_I_add]
  constructor <;> intro h <;> nlinarith [h]

lemma normSq_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) : Complex.normSq z = 1 := by
  rw [Complex.normSq_eq_norm_sq, hz]
  norm_num

lemma norm_mobInv' (z₀ u : ℂ) (hne : Complex.I + u ≠ 0) :
    ‖mobInv z₀ u‖ = ‖z₀‖ * (‖Complex.I - u‖ / ‖Complex.I + u‖) := by
  simp only [mobInv, norm_mul, norm_div]
  ring

lemma mobInv_norm_lt_one {z₀ u : ℂ} (hz₀ : ‖z₀‖ = 1) (hu : 0 < u.im)
    (hne : Complex.I + u ≠ 0) : ‖mobInv z₀ u‖ < 1 := by
  rw [norm_mobInv' z₀ u hne, hz₀, one_mul, div_lt_one (norm_pos_iff.mpr hne)]
  have h2 : ‖Complex.I - u‖ ^ 2 < ‖Complex.I + u‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    exact (normSq_I_sub_lt_iff u).mpr hu
  exact (sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h2

lemma mobInv_norm_le_one {z₀ u : ℂ} (hz₀ : ‖z₀‖ = 1) (hu : 0 ≤ u.im)
    (hne : Complex.I + u ≠ 0) : ‖mobInv z₀ u‖ ≤ 1 := by
  rw [norm_mobInv' z₀ u hne, hz₀, one_mul, div_le_one (norm_pos_iff.mpr hne)]
  have h2 : ‖Complex.I - u‖ ^ 2 ≤ ‖Complex.I + u‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    exact (normSq_I_sub_le_iff u).mpr hu
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h2

lemma mobInv_norm_eq_one {z₀ u : ℂ} (hz₀ : ‖z₀‖ = 1) (hu : u.im = 0)
    (hne : Complex.I + u ≠ 0) : ‖mobInv z₀ u‖ = 1 := by
  rw [norm_mobInv' z₀ u hne, hz₀, one_mul]
  have h2 : ‖Complex.I - u‖ ^ 2 = ‖Complex.I + u‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, normSq_I_sub, normSq_I_add,
      hu]
    ring
  have h3 : ‖Complex.I - u‖ = ‖Complex.I + u‖ := by
    refine le_antisymm ?_ ?_
    · exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (le_of_eq h2)
    · exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (le_of_eq h2.symm)
  rw [h3, div_self (norm_ne_zero_iff.mpr hne)]

/-! ## The imaginary part of the Möbius map -/

lemma mobMap_normSq_relation {z₀ w : ℂ} (hz₀ : z₀ ≠ 0) (hz₀n : Complex.normSq z₀ = 1)
    (hw : w + z₀ ≠ 0) :
    Complex.normSq (Complex.I - mobMap z₀ w)
      = Complex.normSq w * Complex.normSq (Complex.I + mobMap z₀ w) := by
  have h1 : (Complex.I - mobMap z₀ w) * (w + z₀) = 2 * Complex.I * w := by
    simp only [mobMap]
    field_simp
    ring
  have h2 : (Complex.I + mobMap z₀ w) * (w + z₀) = 2 * Complex.I * z₀ := by
    simp only [mobMap]
    field_simp
    ring
  have hn1 : Complex.normSq (Complex.I - mobMap z₀ w) * Complex.normSq (w + z₀)
      = Complex.normSq (2 * Complex.I * w) := by
    rw [← Complex.normSq_mul, h1]
  have hn2 : Complex.normSq (Complex.I + mobMap z₀ w) * Complex.normSq (w + z₀)
      = Complex.normSq (2 * Complex.I * z₀) := by
    rw [← Complex.normSq_mul, h2]
  have h2c : Complex.normSq (2 : ℂ) = 4 := by
    rw [Complex.normSq_eq_norm_sq]
    norm_num
  have hIc : Complex.normSq Complex.I = 1 := by
    rw [Complex.normSq_eq_norm_sq]
    simp
  have hz1 : Complex.normSq (2 * Complex.I * w) = 4 * Complex.normSq w := by
    rw [Complex.normSq_mul, Complex.normSq_mul, h2c, hIc]
    ring
  have hz2 : Complex.normSq (2 * Complex.I * z₀) = 4 * Complex.normSq z₀ := by
    rw [Complex.normSq_mul, Complex.normSq_mul, h2c, hIc]
    ring
  have hwz : Complex.normSq (w + z₀) ≠ 0 := (Complex.normSq_pos.mpr hw).ne'
  have key : Complex.normSq (Complex.I - mobMap z₀ w) * Complex.normSq (w + z₀)
      = (Complex.normSq w * Complex.normSq (Complex.I + mobMap z₀ w))
        * Complex.normSq (w + z₀) := by
    rw [hn1, hz1]
    rw [mul_assoc, hn2, hz2, hz₀n]
    ring
  exact mul_right_cancel₀ hwz key

lemma two_im_eq {T : ℂ} :
    Complex.normSq (Complex.I + T) - Complex.normSq (Complex.I - T) = 4 * T.im := by
  rw [normSq_I_add, normSq_I_sub]
  ring

lemma mobMap_im_pos {z₀ w : ℂ} (hz₀ : ‖z₀‖ = 1) (hw1 : ‖w‖ < 1) (hw : w + z₀ ≠ 0) :
    0 < (mobMap z₀ w).im := by
  have hz₀' : z₀ ≠ 0 := by
    intro h; rw [h] at hz₀; simp at hz₀
  have hrel := mobMap_normSq_relation hz₀' (normSq_of_norm_eq_one hz₀) hw
  have hT : Complex.normSq (Complex.I + mobMap z₀ w) ≠ 0 := by
    intro h0
    have hplus : Complex.I + mobMap z₀ w = 0 := Complex.normSq_eq_zero.mp h0
    have h1 : Complex.normSq (Complex.I - mobMap z₀ w) = 0 := by
      have h2 : Complex.normSq (Complex.I - mobMap z₀ w) * Complex.normSq (w + z₀) = 0 := by
        rw [hrel, h0, mul_zero, zero_mul]
      rcases mul_eq_zero.mp h2 with h | h
      · exact h
      · exact absurd h ((Complex.normSq_pos.mpr hw).ne')
    have hminus : Complex.I - mobMap z₀ w = 0 := Complex.normSq_eq_zero.mp h1
    have hsum : (Complex.I + mobMap z₀ w) + (Complex.I - mobMap z₀ w) = 0 := by
      rw [hplus, hminus, add_zero]
    have h2I : (2 : ℂ) * Complex.I = 0 := by linear_combination hsum
    have hne2 : (2 : ℂ) * Complex.I ≠ 0 := by norm_num
    exact hne2 h2I
  have hpos : 0 < Complex.normSq (Complex.I + mobMap z₀ w) :=
    lt_of_le_of_ne (Complex.normSq_nonneg _) (Ne.symm hT)
  have hwlt : Complex.normSq w < 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [hw1, norm_nonneg w]
  nlinarith [hrel, two_im_eq (T := mobMap z₀ w), hpos, hwlt]

/-! ## Continuity and differentiability of the straightened coordinates -/

lemma continuousOn_mobInv {z₀ : ℂ} {s : Set ℂ} (h : ∀ u ∈ s, Complex.I + u ≠ 0) :
    ContinuousOn (mobInv z₀) s := by
  show ContinuousOn (fun u : ℂ => z₀ * (Complex.I - u) / (Complex.I + u)) s
  exact ((continuous_const.mul (continuous_const.sub continuous_id)).continuousOn).div
    ((continuous_const.add continuous_id).continuousOn) h

lemma differentiableAt_mobInv {z₀ u : ℂ} (hu : Complex.I + u ≠ 0) :
    DifferentiableAt ℂ (mobInv z₀) u := by
  show DifferentiableAt ℂ (fun u : ℂ => z₀ * (Complex.I - u) / (Complex.I + u)) u
  exact ((differentiableAt_const z₀).mul ((differentiableAt_const Complex.I).sub
    differentiableAt_id)).div ((differentiableAt_const Complex.I).add differentiableAt_id) hu

/-! ## The boundary-uniqueness theorem -/

theorem eq_zero_of_eventuallyEq_zero_on_sphere {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.ball (0 : ℂ) 1))
    (hcont : ContinuousOn f (Metric.closedBall (0 : ℂ) 1))
    {z₀ : ℂ} (hz₀ : ‖z₀‖ = 1)
    (h : Filter.Eventually (fun ζ => f ζ = 0) (nhdsWithin z₀ (Metric.sphere (0 : ℂ) 1))) :
    ∀ z ∈ Metric.ball (0 : ℂ) 1, f z = 0 := by
  have hz₀' : z₀ ≠ 0 := by intro h'; rw [h'] at hz₀; simp at hz₀
  -- (1) a neighbourhood in the circle on which `f` vanishes
  obtain ⟨ε₀, hε₀pos, hε₀⟩ : ∃ ε > 0, ∀ ζ : ℂ, dist ζ z₀ < ε → ζ ∈ Metric.sphere (0 : ℂ) 1 →
      f ζ = 0 := by
    have h1 := h
    rw [eventually_nhdsWithin_iff] at h1
    obtain ⟨ε, hε, hε'⟩ := Metric.eventually_nhds_iff.mp h1
    exact ⟨ε, hε, fun ζ hζ hζs => hε' hζ hζs⟩
  -- (2) `mobInv` is continuous at `0`
  have hcont_ball : ContinuousOn (mobInv z₀) (Metric.ball (0 : ℂ) 1) := by
    refine continuousOn_mobInv (fun u hu => ?_)
    intro hcon
    have : u = -Complex.I := by linear_combination hcon
    rw [this, Metric.mem_ball, dist_zero_right, norm_neg, Complex.norm_I] at hu
    norm_num at hu
  have hcont0 : ContinuousAt (mobInv z₀) 0 :=
    hcont_ball.continuousAt (Metric.isOpen_ball.mem_nhds (by
      rw [Metric.mem_ball, dist_zero_right]
      norm_num))
  obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousAt_iff.mp hcont0 ε₀ hε₀pos
  rw [mobInv_zero hz₀'] at hδ
  -- (3) the radius of the half-plane lemma
  set ρ : ℝ := min (1 / 2) (δ / 2) with hρdef
  have hρpos : 0 < ρ := lt_min (by norm_num) (by linarith)
  have hρhalf : ρ ≤ 1 / 2 := min_le_left _ _
  have hρδ : ρ ≤ δ / 2 := min_le_right _ _
  have hne : ∀ u : ℂ, ‖u‖ < ρ → Complex.I + u ≠ 0 := by
    intro u hu hcon
    have : u = -Complex.I := by linear_combination hcon
    rw [this, norm_neg, Complex.norm_I] at hu
    linarith
  have hball_mem : ∀ u : ℂ, u ∈ Metric.ball (0 : ℂ) ρ → Complex.I + u ≠ 0 :=
    fun u hu => hne u (by rwa [Metric.mem_ball, dist_zero_right] at hu)
  -- (4) the straightened function `g = f ∘ mobInv`
  set g : ℂ → ℂ := fun u => f (mobInv z₀ u) with hg
  have hgdiff : ∀ u : ℂ, ‖u‖ < ρ → 0 < u.im → DifferentiableAt ℂ g u := by
    intro u hu hui
    have hne' := hne u hu
    have hmem : mobInv z₀ u ∈ Metric.ball (0 : ℂ) 1 := by
      rw [Metric.mem_ball, dist_zero_right]
      exact mobInv_norm_lt_one hz₀ hui hne'
    rw [hg]
    exact ((hf _ hmem).differentiableAt).comp u (differentiableAt_mobInv hne')
  have hgcont : ContinuousOn g (Metric.ball (0 : ℂ) ρ ∩ {u : ℂ | 0 ≤ u.im}) := by
    rw [hg]
    have h1 : ContinuousOn (mobInv z₀) (Metric.ball (0 : ℂ) ρ ∩ {u : ℂ | 0 ≤ u.im}) :=
      continuousOn_mobInv (fun u hu => hball_mem u hu.1)
    refine hcont.comp h1 ?_
    intro u hu
    rw [Metric.mem_closedBall, dist_zero_right]
    exact mobInv_norm_le_one hz₀ hu.2 (hball_mem u hu.1)
  have hzero : ∀ u : ℂ, ‖u‖ < ρ → u.im = 0 → g u = 0 := by
    intro u hu hui
    have hne' := hne u hu
    have hnorm : ‖mobInv z₀ u‖ = 1 := mobInv_norm_eq_one hz₀ hui hne'
    have hmem : mobInv z₀ u ∈ Metric.sphere (0 : ℂ) 1 := by
      rw [Metric.mem_sphere, dist_zero_right]
      exact hnorm
    have hdist : dist (mobInv z₀ u) z₀ < ε₀ := hδ (by rw [dist_zero_right]; linarith)
    rw [hg]
    exact hε₀ _ hdist hmem
  have hhalf : ∀ u : ℂ, ‖u‖ < ρ → 0 < u.im → g u = 0 :=
    half_plane_eq_zero hρpos hgdiff hgcont hzero
  -- (5) `f` vanishes near `z₀` in the disc
  have hnear : ∃ δ' > 0, δ' ≤ 1 ∧ ∀ w : ℂ, ‖w‖ < 1 → ‖w - z₀‖ < δ' → f w = 0 := by
    have hcont0 : ContinuousAt (mobMap z₀) z₀ := by
      have h1 : ContinuousAt (fun w : ℂ => -Complex.I * (w - z₀)) z₀ := by fun_prop
      have h2 : ContinuousAt (fun w : ℂ => w + z₀) z₀ := by fun_prop
      have h3 : (z₀ + z₀) ≠ 0 := by
        intro hcon
        have : z₀ = 0 := by linear_combination (1 / 2 : ℂ) * hcon
        exact hz₀' this
      have h4 : (fun w : ℂ => w + z₀) z₀ ≠ 0 := by simpa using h3
      exact h1.div h2 h4
    obtain ⟨δ', hδ'pos, hδ'⟩ := Metric.continuousAt_iff.mp hcont0 ρ hρpos
    refine ⟨min δ' 1, lt_min hδ'pos one_pos, min_le_right _ _, fun w hw1 hwnear => ?_⟩
    have hδ'le : min δ' 1 ≤ δ' := min_le_left _ _
    have hδ'one : min δ' 1 ≤ 1 := min_le_right _ _
    have hwm : ‖mobMap z₀ w‖ < ρ := by
      have := hδ' (by rw [dist_eq_norm]; exact lt_of_lt_of_le hwnear hδ'le)
      rwa [mobMap_self z₀, dist_zero_right] at this
    have hwn : w + z₀ ≠ 0 := by
      intro hcon
      have : w = -z₀ := by linear_combination hcon
      rw [this, norm_neg, hz₀] at hw1
      linarith
    have him : 0 < (mobMap z₀ w).im := mobMap_im_pos hz₀ hw1 hwn
    have hres := hhalf (mobMap z₀ w) hwm him
    rw [hg] at hres
    have hres' : f (mobInv z₀ (mobMap z₀ w)) = 0 := by simpa only [] using hres
    rwa [mobInv_mobMap hz₀' hwn] at hres'
  obtain ⟨δ', hδ'pos, hδ'le, hδ'⟩ := hnear
  -- (6) the identity theorem
  set w₀ : ℂ := z₀ * (((1 : ℝ) - δ' / 2 : ℝ) : ℂ) with hw₀def
  have hw₀mem : ‖w₀‖ < 1 := by
    rw [hw₀def, norm_mul, hz₀, one_mul]
    have h2 : ‖(((1 : ℝ) - δ' / 2 : ℝ) : ℂ)‖ = |1 - δ' / 2| := RCLike.norm_ofReal _
    rw [h2, abs_lt]
    constructor <;> linarith
  have hw₀ball : w₀ ∈ Metric.ball (0 : ℂ) 1 := by
    rw [Metric.mem_ball, dist_zero_right]
    exact hw₀mem
  have hw₀dist : ‖w₀ - z₀‖ < δ' := by
    rw [hw₀def]
    have hsub : z₀ * (((1 : ℝ) - δ' / 2 : ℝ) : ℂ) - z₀
        = z₀ * ((((1 : ℝ) - δ' / 2 : ℝ) : ℂ) - 1) := by
      rw [mul_sub, mul_one]
    rw [hsub, norm_mul, hz₀, one_mul]
    have hsub2 : (((1 : ℝ) - δ' / 2 : ℝ) : ℂ) - 1 = -(((δ' / 2 : ℝ)) : ℂ) := by
      push_cast
      ring
    rw [hsub2, norm_neg]
    have h2 : ‖(((δ' / 2 : ℝ)) : ℂ)‖ = |δ' / 2| := RCLike.norm_ofReal _
    rw [h2, abs_of_pos (by linarith)]
    linarith
  have hw₀van : f w₀ = 0 := hδ' w₀ hw₀mem hw₀dist
  have hev : f =ᶠ[𝓝 w₀] 0 := by
    have h1 : Metric.ball (0 : ℂ) 1 ∈ 𝓝 w₀ := Metric.isOpen_ball.mem_nhds hw₀ball
    have h2 : Metric.ball z₀ δ' ∈ 𝓝 w₀ := by
      refine Metric.isOpen_ball.mem_nhds ?_
      rw [Metric.mem_ball, dist_eq_norm]
      exact hw₀dist
    filter_upwards [h1, h2] with w hw1 hw2
    exact hδ' w (by rwa [Metric.mem_ball, dist_zero_right] at hw1)
      (by simpa [dist_eq_norm] using hw2)
  have hpre : IsPreconnected (Metric.ball (0 : ℂ) 1) := (convex_ball (0 : ℂ) 1).isPreconnected
  exact fun z hz => hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hpre hw₀ball hev hz

end Work.Smooth.SphereJordan.Caratheodory
