import Mathlib
import Submission.Commons.Topology.Brouwer.brouwer_fixed_point_closedBall

namespace Commons.Topology.Crossing

open Set Metric

/-! ## Auxiliary facts about the unit square `[0,1]² ⊂ ℂ` -/

/-- The unit square `[0,1]² ⊂ ℂ`. -/
def Q01 : Set ℂ := {z : ℂ | z.re ∈ Set.Icc (0:ℝ) 1 ∧ z.im ∈ Set.Icc (0:ℝ) 1}

lemma convex_Q01 : Convex ℝ Q01 := by
  have h1 : Convex ℝ (Complex.re ⁻¹' Set.Icc (0:ℝ) 1) :=
    (convex_Icc (0:ℝ) 1).linear_preimage (Complex.reCLM : ℂ →ₗ[ℝ] ℝ)
  have h2 : Convex ℝ (Complex.im ⁻¹' Set.Icc (0:ℝ) 1) :=
    (convex_Icc (0:ℝ) 1).linear_preimage (Complex.imCLM : ℂ →ₗ[ℝ] ℝ)
  have h := h1.inter h2
  convert h using 1
  ext z
  simp [Q01, Set.mem_inter_iff, and_assoc]

lemma isClosed_Q01 : IsClosed Q01 := by
  have h1 : IsClosed (Complex.re ⁻¹' Set.Icc (0:ℝ) 1) := isClosed_Icc.preimage Complex.continuous_re
  have h2 : IsClosed (Complex.im ⁻¹' Set.Icc (0:ℝ) 1) := isClosed_Icc.preimage Complex.continuous_im
  convert h1.inter h2 using 1
  ext z
  simp [Q01, Set.mem_inter_iff, and_assoc]

lemma isBounded_Q01 : Bornology.IsBounded Q01 := by
  refine (Metric.isBounded_closedBall (x := (0:ℂ)) (r := 2)).subset ?_
  intro z hz
  rw [Metric.mem_closedBall, dist_zero_right]
  have h1 := hz.1.1; have h2 := hz.1.2; have h3 := hz.2.1; have h4 := hz.2.2
  have hn : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  nlinarith [sq_nonneg z.re, sq_nonneg z.im, norm_nonneg z]

lemma interior_Q01_nonempty : (interior Q01).Nonempty := by
  refine ⟨(1/2 : ℂ) + (1/2 : ℂ) * Complex.I, ?_⟩
  have hU : IsOpen (Complex.re ⁻¹' Set.Ioo (0:ℝ) 1 ∩ Complex.im ⁻¹' Set.Ioo (0:ℝ) 1) :=
    (isOpen_Ioo.preimage Complex.continuous_re).inter (isOpen_Ioo.preimage Complex.continuous_im)
  have hsub : (Complex.re ⁻¹' Set.Ioo (0:ℝ) 1 ∩ Complex.im ⁻¹' Set.Ioo (0:ℝ) 1) ⊆ Q01 := by
    intro z hz
    exact ⟨⟨le_of_lt hz.1.1, le_of_lt hz.1.2⟩, ⟨le_of_lt hz.2.1, le_of_lt hz.2.2⟩⟩
  refine interior_maximal hsub hU ?_
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ioo]
  constructor <;> constructor <;> norm_num [Complex.add_re, Complex.mul_re]

lemma re_ofReal_add_ofReal_mul_I (a b : ℝ) : (((a:ℝ):ℂ) + ((b:ℝ):ℂ) * Complex.I).re = a := by simp
lemma im_ofReal_add_ofReal_mul_I (a b : ℝ) : (((a:ℝ):ℂ) + ((b:ℝ):ℂ) * Complex.I).im = b := by simp

/-- **Brouwer fixed point theorem for the unit square `[0,1]²`.** -/
theorem brouwer_fixed_point_Q01 (f : C(Q01, Q01)) : ∃ x, f x = x := by
  obtain ⟨e, _, hcl, _⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall
      convex_Q01 interior_Q01_nonempty isBounded_Q01
  have hcl' : e '' Q01 = Metric.closedBall (0:ℂ) 1 := by
    rw [← hcl, isClosed_Q01.closure_eq]
  let φ : Q01 ≃ₜ Metric.closedBall (0:ℂ) 1 :=
    (e.image Q01).trans (Homeomorph.setCongr hcl')
  let g : C(Metric.closedBall (0:ℂ) 1, Metric.closedBall (0:ℂ) 1) :=
    (φ : C(Q01, Metric.closedBall (0:ℂ) 1)).comp
      (f.comp (φ.symm : C(Metric.closedBall (0:ℂ) 1, Q01)))
  obtain ⟨y, hy⟩ := Commons.Topology.Brouwer.brouwer_fixed_point_unitDisk g
  refine ⟨φ.symm y, ?_⟩
  have hgy : φ (f (φ.symm y)) = y := by
    simpa [g, ContinuousMap.comp_apply] using hy
  calc f (φ.symm y) = φ.symm (φ (f (φ.symm y))) := (Homeomorph.symm_apply_apply φ _).symm
    _ = φ.symm y := by rw [hgy]

/-! ## The crossing construction -/

/-- First difference component. -/
noncomputable def crossA (h v : C(unitInterval, ℂ)) (z : Q01) : ℝ :=
  (v ⟨z.1.im, z.2.2⟩).re - (h ⟨z.1.re, z.2.1⟩).re

/-- Second difference component. -/
noncomputable def crossB (h v : C(unitInterval, ℂ)) (z : Q01) : ℝ :=
  (h ⟨z.1.re, z.2.1⟩).im - (v ⟨z.1.im, z.2.2⟩).im

/-- Supremum of the two difference components. -/
noncomputable def crossN (h v : C(unitInterval, ℂ)) (z : Q01) : ℝ :=
  max |crossA h v z| |crossB h v z|

lemma continuous_crossA (h v : C(unitInterval, ℂ)) : Continuous (crossA h v) := by
  change Continuous (fun z : Q01 => (v ⟨z.1.im, z.2.2⟩).re - (h ⟨z.1.re, z.2.1⟩).re)
  fun_prop

lemma continuous_crossB (h v : C(unitInterval, ℂ)) : Continuous (crossB h v) := by
  change Continuous (fun z : Q01 => (h ⟨z.1.re, z.2.1⟩).im - (v ⟨z.1.im, z.2.2⟩).im)
  fun_prop

lemma continuous_crossN (h v : C(unitInterval, ℂ)) : Continuous (crossN h v) := by
  change Continuous (fun z : Q01 => max |crossA h v z| |crossB h v z|)
  exact (continuous_crossA h v).abs.max (continuous_crossB h v).abs

theorem crossing_lemma_square (h v : C(unitInterval, ℂ))
    (hh : ∀ s, (h s).re ∈ Set.Icc 0 1 ∧ (h s).im ∈ Set.Icc 0 1)
    (hv : ∀ t, (v t).re ∈ Set.Icc 0 1 ∧ (v t).im ∈ Set.Icc 0 1)
    (h0 : (h 0).re = 0) (h1 : (h 1).re = 1)
    (v0 : (v 0).im = 0) (v1 : (v 1).im = 1) :
    ∃ s t, h s = v t := by
  by_contra hcon
  push Not at hcon
  -- `crossN` is strictly positive, since a zero would exhibit an intersection.
  have hNne : ∀ z : Q01, crossN h v z ≠ 0 := by
    intro z hz
    have hA0 : crossA h v z = 0 := by
      have hle : |crossA h v z| ≤ max |crossA h v z| |crossB h v z| := le_max_left _ _
      rw [crossN] at hz
      rw [hz] at hle
      exact abs_eq_zero.mp (le_antisymm hle (abs_nonneg _))
    have hB0 : crossB h v z = 0 := by
      have hle : |crossB h v z| ≤ max |crossA h v z| |crossB h v z| := le_max_right _ _
      rw [crossN] at hz
      rw [hz] at hle
      exact abs_eq_zero.mp (le_antisymm hle (abs_nonneg _))
    exact hcon ⟨z.1.re, z.2.1⟩ ⟨z.1.im, z.2.2⟩ (by
      apply Complex.ext
      · rw [crossA] at hA0; linarith
      · rw [crossB] at hB0; linarith)
  have hNpos : ∀ z : Q01, 0 < crossN h v z := fun z =>
    lt_of_le_of_ne (le_trans (abs_nonneg _) (le_max_left _ _)) (Ne.symm (hNne z))
  -- The self-map of the square.
  have hGmem : ∀ z : Q01,
      (((1:ℝ)/2 + crossA h v z / (2 * crossN h v z) : ℝ) : ℂ)
        + (((1:ℝ)/2 + crossB h v z / (2 * crossN h v z) : ℝ) : ℂ) * Complex.I ∈ Q01 := by
    intro z
    have hAz : |crossA h v z| ≤ crossN h v z := le_max_left _ _
    have hBz : |crossB h v z| ≤ crossN h v z := le_max_right _ _
    have hNz : 0 < crossN h v z := hNpos z
    have h2N : (0:ℝ) < 2 * crossN h v z := by linarith
    constructor
    · rw [re_ofReal_add_ofReal_mul_I]
      have hle : |crossA h v z / (2 * crossN h v z)| ≤ 1/2 := by
        rw [abs_div, abs_of_pos h2N, div_le_iff₀ h2N]
        linarith
      have := abs_le.mp hle
      constructor <;> linarith
    · rw [im_ofReal_add_ofReal_mul_I]
      have hle : |crossB h v z / (2 * crossN h v z)| ≤ 1/2 := by
        rw [abs_div, abs_of_pos h2N, div_le_iff₀ h2N]
        linarith
      have := abs_le.mp hle
      constructor <;> linarith
  have hcont : Continuous fun z : Q01 =>
      (((1:ℝ)/2 + crossA h v z / (2 * crossN h v z) : ℝ) : ℂ)
        + (((1:ℝ)/2 + crossB h v z / (2 * crossN h v z) : ℝ) : ℂ) * Complex.I := by
    apply Continuous.add
    · apply Complex.continuous_ofReal.comp
      apply Continuous.add continuous_const
      exact (continuous_crossA h v).div ((continuous_crossN h v).const_mul 2)
        (fun z => ne_of_gt (by have := hNpos z; linarith))
    · apply Continuous.mul
      · apply Complex.continuous_ofReal.comp
        apply Continuous.add continuous_const
        exact (continuous_crossB h v).div ((continuous_crossN h v).const_mul 2)
          (fun z => ne_of_gt (by have := hNpos z; linarith))
      · exact continuous_const
  let G : C(Q01, Q01) := ContinuousMap.mk _ (Continuous.subtype_mk hcont hGmem)
  obtain ⟨x, hx⟩ := brouwer_fixed_point_Q01 G
  have hxval : ((G x : Q01) : ℂ) = (x : ℂ) := congrArg Subtype.val hx
  have hGre : ((G x : Q01) : ℂ).re = (1:ℝ)/2 + crossA h v x / (2 * crossN h v x) := by
    show (G x : Q01).1.re = _
    simp only [G, ContinuousMap.coe_mk, re_ofReal_add_ofReal_mul_I]
  have hGim : ((G x : Q01) : ℂ).im = (1:ℝ)/2 + crossB h v x / (2 * crossN h v x) := by
    show (G x : Q01).1.im = _
    simp only [G, ContinuousMap.coe_mk, im_ofReal_add_ofReal_mul_I]
  have hxre : (x : ℂ).re = (1:ℝ)/2 + crossA h v x / (2 * crossN h v x) := by
    rw [← hxval, hGre]
  have hxim : (x : ℂ).im = (1:ℝ)/2 + crossB h v x / (2 * crossN h v x) := by
    rw [← hxval, hGim]
  -- The fixed point lies on the boundary of the square.
  have hboundary : |(x : ℂ).re - 1/2| = 1/2 ∨ |(x : ℂ).im - 1/2| = 1/2 := by
    have h2N : (0:ℝ) < 2 * crossN h v x := by have := hNpos x; linarith
    have e1 : (x : ℂ).re - 1/2 = crossA h v x / (2 * crossN h v x) := by linarith [hxre]
    have e2 : (x : ℂ).im - 1/2 = crossB h v x / (2 * crossN h v x) := by linarith [hxim]
    rcases max_cases |crossA h v x| |crossB h v x| with he | he
    · left
      have hNx : crossN h v x = |crossA h v x| := by rw [crossN]; exact he.1
      have hne : |crossA h v x| ≠ 0 := by rw [← hNx]; exact hNne x
      rw [e1, abs_div, abs_of_pos h2N, hNx]
      field_simp
    · right
      have hNx : crossN h v x = |crossB h v x| := by rw [crossN]; exact he.1
      have hne : |crossB h v x| ≠ 0 := by rw [← hNx]; exact hNne x
      rw [e2, abs_div, abs_of_pos h2N, hNx]
      field_simp
  have hxbd : (x : ℂ).re = 1 ∨ (x : ℂ).re = 0 ∨ (x : ℂ).im = 1 ∨ (x : ℂ).im = 0 := by
    rcases hboundary with hb | hb
    · rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1/2)).mp hb with h | h
      · left; linarith
      · right; left; linarith
    · rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1/2)).mp hb with h | h
      · right; right; left; linarith
      · right; right; right; linarith
  -- Each boundary case contradicts the sign conditions.
  have hdiv2 : (2 * crossN h v x) ≠ 0 := by have := hNpos x; linarith
  rcases hxbd with hxr | hxr | hxi | hxi
  · have hAxN : crossA h v x = crossN h v x := by
      have e : crossA h v x / (2 * crossN h v x) = 1/2 := by linarith [hxre, hxr]
      rw [div_eq_iff hdiv2] at e
      linarith
    have hAval : crossA h v x = (v ⟨(x:ℂ).im, x.2.2⟩).re - 1 := by
      rw [crossA]
      rw [show (⟨(x : ℂ).re, x.2.1⟩ : unitInterval) = 1 from Subtype.ext hxr, h1]
    have hvle : (v ⟨(x:ℂ).im, x.2.2⟩).re ≤ 1 := (hv _).1.2
    linarith [hNpos x]
  · have hAxN : crossA h v x = -crossN h v x := by
      have e : crossA h v x / (2 * crossN h v x) = -1/2 := by linarith [hxre, hxr]
      rw [div_eq_iff hdiv2] at e
      linarith
    have hAval : crossA h v x = (v ⟨(x:ℂ).im, x.2.2⟩).re - 0 := by
      rw [crossA]
      rw [show (⟨(x : ℂ).re, x.2.1⟩ : unitInterval) = 0 from Subtype.ext hxr, h0]
    have hvge : (0:ℝ) ≤ (v ⟨(x:ℂ).im, x.2.2⟩).re := (hv _).1.1
    linarith [hNpos x]
  · have hBxN : crossB h v x = crossN h v x := by
      have e : crossB h v x / (2 * crossN h v x) = 1/2 := by linarith [hxim, hxi]
      rw [div_eq_iff hdiv2] at e
      linarith
    have hBval : crossB h v x = (h ⟨(x:ℂ).re, x.2.1⟩).im - 1 := by
      rw [crossB]
      rw [show (⟨(x : ℂ).im, x.2.2⟩ : unitInterval) = 1 from Subtype.ext hxi, v1]
    have hhle : (h ⟨(x:ℂ).re, x.2.1⟩).im ≤ 1 := (hh _).2.2
    linarith [hNpos x]
  · have hBxN : crossB h v x = -crossN h v x := by
      have e : crossB h v x / (2 * crossN h v x) = -1/2 := by linarith [hxim, hxi]
      rw [div_eq_iff hdiv2] at e
      linarith
    have hBval : crossB h v x = (h ⟨(x:ℂ).re, x.2.1⟩).im - 0 := by
      rw [crossB]
      rw [show (⟨(x : ℂ).im, x.2.2⟩ : unitInterval) = 0 from Subtype.ext hxi, v0]
    have hhge : (0:ℝ) ≤ (h ⟨(x:ℂ).re, x.2.1⟩).im := (hh _).2.1
    linarith [hNpos x]

end Commons.Topology.Crossing
