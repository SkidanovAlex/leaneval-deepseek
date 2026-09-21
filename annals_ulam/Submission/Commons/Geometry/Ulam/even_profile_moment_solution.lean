import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace Commons.Geometry.Ulam

open scoped ContDiff RealInnerProductSpace

set_option autoImplicit false

noncomputable section

/-- The upper unit semicircle, `√(1 - t^2)`, used as an even profile. -/
def semicircle (t : ℝ) : ℝ := Real.sqrt (1 - t ^ 2)

/-- The positive intersection parameter for slope `s`. -/
def profileX (s : ℝ) : ℝ := 1 / Real.sqrt (1 + s ^ 2)

lemma profileX_sq (s : ℝ) : (profileX s) ^ 2 = 1 / (1 + s ^ 2) := by
  unfold profileX
  have hden_pos : 0 < 1 + s ^ 2 := by nlinarith [sq_nonneg s]
  rw [one_div]
  rw [inv_pow]
  rw [Real.sq_sqrt (le_of_lt hden_pos)]
  rw [one_div]

lemma profileX_pos (s : ℝ) (hs : 0 < s) : 0 < profileX s := by
  unfold profileX
  positivity

lemma profileX_mem_Icc (s : ℝ) : profileX s ∈ Set.Icc (-1) 1 := by
  unfold profileX
  have hden_pos : 0 < 1 + s ^ 2 := by nlinarith [sq_nonneg s]
  have hsqrt_pos : 0 < Real.sqrt (1 + s ^ 2) := Real.sqrt_pos.2 hden_pos
  have hsqrt_ge_one : 1 ≤ Real.sqrt (1 + s ^ 2) := by
    have h : (1 : ℝ) ≤ 1 + s ^ 2 := by nlinarith [sq_nonneg s]
    have hs := Real.sqrt_le_sqrt h
    simpa using hs
  constructor
  · have hpos : 0 ≤ 1 / Real.sqrt (1 + s ^ 2) := by positivity
    linarith
  · rw [div_le_one hsqrt_pos]
    exact hsqrt_ge_one

lemma semicircle_sq_of_mem_Icc {t : ℝ} (ht : t ∈ Set.Icc (-1) 1) :
    (semicircle t) ^ 2 = 1 - t ^ 2 := by
  unfold semicircle
  have hx1 : -1 ≤ t := ht.1
  have hx2 : t ≤ 1 := ht.2
  have habs : |t| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  have hsq' : t ^ 2 ≤ (1 : ℝ) ^ 2 :=
    (sq_le_sq (a := t) (b := (1 : ℝ))).2 (by simpa using habs)
  have hsq : t ^ 2 ≤ 1 := by simpa using hsq'
  exact Real.sq_sqrt (by nlinarith)

lemma semicircle_support_subset : Function.support semicircle ⊆ Set.Icc (-1) 1 := by
  rw [Function.support_subset_iff]
  intro x hx
  have hnonneg : 0 ≤ 1 - x ^ 2 := by
    by_contra h
    have hle : 1 - x ^ 2 ≤ 0 := le_of_lt (lt_of_not_ge h)
    have hsqrt : Real.sqrt (1 - x ^ 2) = 0 := Real.sqrt_eq_zero_of_nonpos hle
    exact hx (by simpa [semicircle] using hsqrt)
  have hsq : x ^ 2 ≤ 1 := by nlinarith
  have hsq' : x ^ 2 ≤ (1 : ℝ) ^ 2 := by simpa using hsq
  have habs : |x| ≤ |(1 : ℝ)| := (sq_le_sq (a := x) (b := (1 : ℝ))).1 hsq'
  rw [abs_le] at habs
  constructor <;> nlinarith

lemma semicircle_contDiffOn : ContDiffOn ℝ ∞ semicircle (Set.Ioo (-1) 1) := by
  unfold semicircle
  apply ContDiffOn.sqrt
  · fun_prop
  · intro x hx
    have hx1 : -1 < x := (Set.mem_Ioo.mp hx).1
    have hx2 : x < 1 := (Set.mem_Ioo.mp hx).2
    have hsq : x ^ 2 < 1 := by
      have habs : |x| < |(1 : ℝ)| := by simpa using (abs_lt.mpr ⟨hx1, hx2⟩)
      simpa using (sq_lt_sq (a := x) (b := (1 : ℝ))).2 habs
    nlinarith

lemma semicircle_pos_of_mem_Ioo {t : ℝ} (ht : t ∈ Set.Ioo (-1) 1) : 0 < semicircle t := by
  have ht1 : -1 < t := (Set.mem_Ioo.mp ht).1
  have ht2 : t < 1 := (Set.mem_Ioo.mp ht).2
  have hsq : t ^ 2 < 1 := by
    have habs : |t| < |(1 : ℝ)| := by simpa using (abs_lt.mpr ⟨ht1, ht2⟩)
    simpa using (sq_lt_sq (a := t) (b := (1 : ℝ))).2 habs
  have hpos : 0 < 1 - t ^ 2 := by nlinarith
  simpa [semicircle] using (Real.sqrt_pos.2 hpos)

lemma semicircle_even (t : ℝ) : semicircle (-t) = semicircle t := by
  unfold semicircle
  ring_nf

lemma semicircle_concaveOn : ConcaveOn ℝ (Set.Icc (-1) 1) semicircle := by
  have hq : ConcaveOn ℝ (Set.Icc (-1) 1) (fun t : ℝ => 1 - t ^ 2) := by
    have hconst : ConcaveOn ℝ (Set.Icc (-1) 1) (fun _ : ℝ => (1 : ℝ)) :=
      concaveOn_const 1 (convex_Icc _ _)
    have hsq : ConvexOn ℝ (Set.Icc (-1) 1) (fun t : ℝ => t ^ 2) := by
      have h : ConvexOn ℝ Set.univ (fun t : ℝ => t ^ 2) := by
        simpa [pow_two] using (Even.convexOn_pow (𝕜 := ℝ) even_two)
      exact h.subset (by intro x hx; trivial) (convex_Icc _ _)
    exact (hconst.sub hsq).congr (by intro x hx; rfl)
  have hq_image : (fun t : ℝ => 1 - t ^ 2) '' Set.Icc (-1) 1 = Set.Icc 0 1 := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx1 : -1 ≤ x := hx.1
      have hx2 : x ≤ 1 := hx.2
      have habs : |x| ≤ 1 := by
        rw [abs_le]
        constructor <;> linarith
      have hsq' : x ^ 2 ≤ (1 : ℝ) ^ 2 :=
        (sq_le_sq (a := x) (b := (1 : ℝ))).2 (by simpa using habs)
      have hsq : x ^ 2 ≤ 1 := by simpa using hsq'
      constructor <;> nlinarith
    · rintro hy
      have hy0 : 0 ≤ y := hy.1
      have hy1 : y ≤ 1 := hy.2
      refine ⟨Real.sqrt (1 - y), ?_, ?_⟩
      · constructor
        · have hsqrt_nonneg : 0 ≤ Real.sqrt (1 - y) := Real.sqrt_nonneg _
          linarith
        · have hsqrt_le : Real.sqrt (1 - y) ≤ 1 := by
            have harg : 1 - y ≤ 1 := by linarith
            have hsqrt : Real.sqrt (1 - y) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt harg
            simpa using hsqrt
          exact hsqrt_le
      · have harg_nonneg : 0 ≤ 1 - y := by linarith
        change 1 - (Real.sqrt (1 - y)) ^ 2 = y
        rw [Real.sq_sqrt harg_nonneg]
        ring
  have hsqrt_dom :
      ConcaveOn ℝ ((fun t : ℝ => 1 - t ^ 2) '' Set.Icc (-1) 1) Real.sqrt := by
    rw [hq_image]
    exact Real.strictConcaveOn_sqrt.concaveOn.subset (fun y hy => hy.1) (convex_Icc _ _)
  have hmono : MonotoneOn Real.sqrt ((fun t : ℝ => 1 - t ^ 2) '' Set.Icc (-1) 1) := by
    rw [hq_image]
    intro x hx y hy hxy
    exact Real.sqrt_le_sqrt hxy
  have hcomp := hsqrt_dom.comp hq hmono
  exact hcomp

lemma semicircle_profileX_sq (s : ℝ) : (semicircle (profileX s)) ^ 2 = (s * profileX s) ^ 2 := by
  rw [semicircle_sq_of_mem_Icc (profileX_mem_Icc s)]
  rw [profileX_sq]
  have hden_pos : 0 < 1 + s ^ 2 := by nlinarith [sq_nonneg s]
  unfold profileX
  have hsqrt_pos : 0 < Real.sqrt (1 + s ^ 2) := Real.sqrt_pos.2 hden_pos
  field_simp [hsqrt_pos.ne', Real.sq_sqrt (le_of_lt hden_pos)]
  rw [Real.sq_sqrt (le_of_lt hden_pos)]
  ring

/-- The integrand appearing in the second moment equation, after simplifying the profile. -/
def momentIntegrand (n : ℕ) (s t : ℝ) : ℝ :=
  ((1 - t ^ 2) - (s * t) ^ 2) ^ (n - 1) * t

lemma momentIntegrand_neg (n : ℕ) (s t : ℝ) : momentIntegrand n s (-t) = - momentIntegrand n s t := by
  unfold momentIntegrand
  ring_nf

lemma odd_momentIntegral_zero {n : ℕ} {s : ℝ} (a : ℝ) :
    (∫ t in (-a)..a, momentIntegrand n s t) = 0 := by
  have h_comp :
      (∫ t in (-a)..a, momentIntegrand n s (-t)) = ∫ t in (-a)..a, momentIntegrand n s t := by
    have h := intervalIntegral.integral_comp_neg (a := -a) (b := a) (f := fun t => momentIntegrand n s t)
    simpa using h
  have h_congr :
      (∫ t in (-a)..a, momentIntegrand n s (-t)) = ∫ t in (-a)..a, - momentIntegrand n s t := by
    apply intervalIntegral.integral_congr
    intro t ht
    exact momentIntegrand_neg n s t
  have h_neg :
      (∫ t in (-a)..a, - momentIntegrand n s t) = - ∫ t in (-a)..a, momentIntegrand n s t := by
    simpa using intervalIntegral.integral_neg (a := -a) (b := a) (f := fun t => momentIntegrand n s t)
  have h1 : ∫ t in (-a)..a, momentIntegrand n s (-t) = - ∫ t in (-a)..a, momentIntegrand n s t := by
    rw [h_congr, h_neg]
  have h2 : ∫ t in (-a)..a, momentIntegrand n s t = - ∫ t in (-a)..a, momentIntegrand n s t := by
    exact h_comp.symm.trans h1
  linarith

lemma even_profile_moment_solution (n : ℕ) (hn : 2 ≤ n) :
    ∃ τ : ℝ, 0 < τ ∧ ∃ h x y f : ℝ → ℝ,
      Function.support h ⊆ Set.Icc (1 - 2 * τ) (1 - τ) ∧
      ContDiffOn ℝ ∞ h Set.univ ∧
      Function.support f ⊆ Set.Icc (-1) 1 ∧
      ContDiffOn ℝ ∞ f (Set.Ioo (-1) 1) ∧
      ConcaveOn ℝ (Set.Icc (-1) 1) f ∧
      f (-1) = 0 ∧ f 1 = 0 ∧
      (∀ t ∈ Set.Ioo (-1) 1, 0 < f t) ∧
      (∀ s : ℝ, 0 < s →
        0 < x s ∧ 0 < y s ∧
        (f (y s)) ^ 2 = (s * y s + h s) ^ 2 ∧
        (f (-x s)) ^ 2 = (s * (-x s) + h s) ^ 2) ∧
      (∀ s : ℝ, 0 < s →
        (∫ t in (-x s)..(y s), (f t ^ 2 - (s * t + h s) ^ 2) ^ n) =
          (∫ t in (-(1 / Real.sqrt (1 + s ^ 2)))..(1 / Real.sqrt (1 + s ^ 2)),
            ((1 - t ^ 2) - (s * t) ^ 2) ^ n)) ∧
      (∀ s : ℝ, 0 < s →
        (∫ t in (-x s)..(y s), (f t ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) * (t + deriv h s)) = 0) := by
  refine ⟨1, by norm_num, (fun _ : ℝ => (0 : ℝ)), (fun s : ℝ => profileX s),
    (fun s : ℝ => profileX s), semicircle, ?_⟩
  constructor
  · simp
  constructor
  · fun_prop
  constructor
  · exact semicircle_support_subset
  constructor
  · exact semicircle_contDiffOn
  constructor
  · exact semicircle_concaveOn
  constructor
  · simp [semicircle]
  constructor
  · simp [semicircle]
  constructor
  · intro t ht
    exact semicircle_pos_of_mem_Ioo ht
  constructor
  · intro s hs
    refine ⟨profileX_pos s hs, profileX_pos s hs, ?_, ?_⟩
    · simpa using semicircle_profileX_sq s
    · have hpos := semicircle_profileX_sq s
      rw [semicircle_even]
      have hmul : s * (-profileX s) = - (s * profileX s) := by ring
      rw [hmul]
      simpa [pow_two] using hpos
  constructor
  · intro s hs
    have hpos : 0 < profileX s := profileX_pos s hs
    have hle : -profileX s ≤ profileX s := by linarith
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hle] at ht
    have htIcc : t ∈ Set.Icc (-1) 1 := by
      constructor
      · have hmem := profileX_mem_Icc s
        have : -1 ≤ -profileX s := by linarith [hmem.2]
        linarith [ht.1]
      · have hmem := profileX_mem_Icc s
        linarith [ht.2, hmem.2]
    change (semicircle t ^ 2 - (s * t + 0) ^ 2) ^ n = ((1 - t ^ 2) - (s * t) ^ 2) ^ n
    rw [semicircle_sq_of_mem_Icc htIcc]
    simp
  · intro s hs
    have hpos : 0 < profileX s := profileX_pos s hs
    have hle : -profileX s ≤ profileX s := by linarith
    have hderiv : deriv (fun _ : ℝ => (0 : ℝ)) s = 0 := by simp
    have hmain :
        (∫ t in (-profileX s)..(profileX s),
          (semicircle t ^ 2 - (s * t + 0) ^ 2) ^ (n - 1) * (t + deriv (fun _ : ℝ => (0 : ℝ)) s)) =
          ∫ t in (-profileX s)..(profileX s), momentIntegrand n s t := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hle] at ht
      have htIcc : t ∈ Set.Icc (-1) 1 := by
        constructor
        · have hmem := profileX_mem_Icc s
          have : -1 ≤ -profileX s := by linarith [hmem.2]
          linarith [ht.1]
        · have hmem := profileX_mem_Icc s
          linarith [ht.2, hmem.2]
      change (semicircle t ^ 2 - (s * t + 0) ^ 2) ^ (n - 1) *
          (t + deriv (fun _ : ℝ => (0 : ℝ)) s) = momentIntegrand n s t
      rw [semicircle_sq_of_mem_Icc htIcc]
      rw [hderiv]
      unfold momentIntegrand
      ring_nf
    rw [hmain, odd_momentIntegral_zero (a := profileX s)]

end

end Commons.Geometry.Ulam