import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Submission.Commons.Geometry.Ulam.even_profile_moment_solution

namespace Commons.Geometry.Ulam

open MeasureTheory Filter
open scoped BigOperators ContDiff Pointwise RealInnerProductSpace

set_option autoImplicit false

noncomputable section

/-- The integrand of the odd-dimensional semicircle moment, as a function of the
rescaled variable `u = √(1 + s²) t`. -/
def oddSemicircleMomentIntegrand (n : ℕ) (t : ℝ) : ℝ :=
  (1 - t ^ 2) ^ n * Real.sqrt (1 - t ^ 2)

/-- The constant `C` in the first odd moment equation for the unit semicircle. -/
def oddSemicircleMomentConstant (n : ℕ) : ℝ :=
  ∫ t in (-1 : ℝ)..(1 : ℝ), oddSemicircleMomentIntegrand n t

/-- The scaling relation for the odd semicircle moment. -/
lemma oddSemicircleMoment_scale (n : ℕ) {s : ℝ} (hs : 0 < s) :
    (∫ t in (-profileX s)..(profileX s),
      (1 - (1 + s ^ 2) * t ^ 2) ^ n * Real.sqrt (1 - (1 + s ^ 2) * t ^ 2))
      = oddSemicircleMomentConstant n / Real.sqrt (1 + s ^ 2) := by
  let c : ℝ := Real.sqrt (1 + s ^ 2)
  have hc_pos : 0 < c := by
    dsimp [c]
    have hden_pos : 0 < 1 + s ^ 2 := by nlinarith [sq_nonneg s]
    exact Real.sqrt_pos.2 hden_pos
  have hc_ne : c ≠ 0 := ne_of_gt hc_pos
  have hcmul : c * profileX s = 1 := by
    dsimp [c, profileX]
    have hden_pos : 0 < 1 + s ^ 2 := by nlinarith [sq_nonneg s]
    field_simp [ne_of_gt (Real.sqrt_pos.2 hden_pos)]
  have hcomp := intervalIntegral.integral_comp_mul_left
    (f := fun u : ℝ => oddSemicircleMomentIntegrand n u)
    (a := -profileX s) (b := profileX s) (c := c) hc_ne
  have hcongr :
      (∫ t in (-profileX s)..(profileX s),
        (1 - (1 + s ^ 2) * t ^ 2) ^ n * Real.sqrt (1 - (1 + s ^ 2) * t ^ 2))
      = ∫ t in (-profileX s)..(profileX s), oddSemicircleMomentIntegrand n (c * t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    unfold oddSemicircleMomentIntegrand
    have hcsq : c ^ 2 = 1 + s ^ 2 := by
      dsimp [c]
      have hden_pos : 0 < 1 + s ^ 2 := by nlinarith [sq_nonneg s]
      exact Real.sq_sqrt (le_of_lt hden_pos)
    rw [← hcsq]
    ring_nf
  rw [hcongr, hcomp]
  have hend1 : c * (-profileX s) = -1 := by
    rw [mul_neg, hcmul]
  have hend2 : c * profileX s = 1 := hcmul
  rw [hend1, hend2]
  change c⁻¹ * oddSemicircleMomentConstant n =
    oddSemicircleMomentConstant n / Real.sqrt (1 + s ^ 2)
  dsimp [oddSemicircleMomentConstant, c]
  rw [inv_mul_eq_div]

/-- The weight in the odd second moment, after substituting the semicircle and
`h = 0`. -/
def oddSemicircleWeight (n : ℕ) (s t : ℝ) : ℝ :=
  (1 - (1 + s ^ 2) * t ^ 2) ^ (n - 1) * Real.sqrt (1 - (1 + s ^ 2) * t ^ 2)

lemma oddSemicircleWeight_even (n : ℕ) (s t : ℝ) :
    oddSemicircleWeight n s (-t) = oddSemicircleWeight n s t := by
  unfold oddSemicircleWeight
  ring_nf

lemma oddSemicircleWeight_mul_t_neg (n : ℕ) (s t : ℝ) :
    oddSemicircleWeight n s (-t) * (-t) = - (oddSemicircleWeight n s t * t) := by
  rw [oddSemicircleWeight_even]
  ring

lemma oddSemicircleWeight_t_integral_zero (n : ℕ) (s a : ℝ) :
    (∫ t in (-a)..a, oddSemicircleWeight n s t * t) = 0 := by
  have h_comp :
      (∫ t in (-a)..a, oddSemicircleWeight n s (-t) * (-t)) =
        ∫ t in (-a)..a, oddSemicircleWeight n s t * t := by
    have h := intervalIntegral.integral_comp_neg (a := -a) (b := a)
      (f := fun t => oddSemicircleWeight n s t * t)
    simpa using h
  have h_congr :
      (∫ t in (-a)..a, oddSemicircleWeight n s (-t) * (-t)) =
        ∫ t in (-a)..a, - (oddSemicircleWeight n s t * t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    exact oddSemicircleWeight_mul_t_neg n s t
  have h_neg :
      (∫ t in (-a)..a, - (oddSemicircleWeight n s t * t)) =
        - ∫ t in (-a)..a, oddSemicircleWeight n s t * t := by
    simpa using intervalIntegral.integral_neg (a := -a) (b := a)
      (f := fun t => oddSemicircleWeight n s t * t)
  have h1 : (∫ t in (-a)..a, oddSemicircleWeight n s (-t) * (-t)) =
      - ∫ t in (-a)..a, oddSemicircleWeight n s t * t := by
    rw [h_congr, h_neg]
  have h2 : (∫ t in (-a)..a, oddSemicircleWeight n s t * t) =
      - ∫ t in (-a)..a, oddSemicircleWeight n s t * t := by
    exact h_comp.symm.trans h1
  linarith

lemma exists_odd_section_solution {d : ℕ} (hd : 3 ≤ d) (hdodd : Odd d) :
    letI : NeZero d := ⟨by omega⟩
    ∃ n : ℕ, d = 2 * n + 1 ∧ 1 ≤ n ∧
    ∃ R₁ R₂ C : ℝ, ∃ f h x y : ℝ → ℝ,
      Function.support f ⊆ Set.Icc (-R₁) R₂ ∧
      ContDiffOn ℝ ∞ f (Set.Ioo (-R₁) R₂) ∧
      ConcaveOn ℝ (Set.Icc (-R₁) R₂) f ∧
      f (-R₁) = 0 ∧ f R₂ = 0 ∧
      (∀ t ∈ Set.Ioo (-R₁) R₂, 0 < f t) ∧
      ContDiff ℝ ∞ h ∧
      h 0 = 0 ∧
      h ≠ 0 ∧
      (∀ s : ℝ, 0 < s → 0 < x s ∧ 0 < y s) ∧
      (∀ s : ℝ, 0 < s →
        f (- x s) = - (s * (- x s) + h s) ∧
        f (y s) = s * y s + h s) ∧
      (∀ s : ℝ, 0 < s →
        (∫ t in (- x s)..(y s),
          (f t ^ 2 - (s * t + h s) ^ 2) ^ n * Real.sqrt (f t ^ 2 - (s * t + h s) ^ 2)) =
            C / Real.sqrt (1 + s ^ 2)) ∧
      (∀ s : ℝ, 0 < s →
        (∫ t in (- x s)..(y s),
          (f t ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) * Real.sqrt (f t ^ 2 - (s * t + h s) ^ 2) *
            (t + deriv h s)) = 0) := by
  letI : NeZero d := ⟨by omega⟩
  obtain ⟨n, hdn⟩ := hdodd
  have hn : 1 ≤ n := by omega
  obtain ⟨hbump, htsupp, _hcomp, hdiff, _hrng, hbump_neg2⟩ :=
    exists_contDiff_tsupport_subset (E := ℝ) (s := Set.Ioo (-3 : ℝ) (-1 : ℝ)) (x := (-2 : ℝ))
      (n := ⊤) (by exact Ioo_mem_nhds (by norm_num) (by norm_num))
  have hsupp : Function.support hbump ⊆ Set.Icc (-3 : ℝ) (-1 : ℝ) := by
    intro s hs
    have hs_ts : s ∈ tsupport hbump := subset_tsupport hbump hs
    have hs_ioo : s ∈ Set.Ioo (-3 : ℝ) (-1 : ℝ) := htsupp hs_ts
    exact ⟨le_of_lt hs_ioo.1, le_of_lt hs_ioo.2⟩
  have hbump_zero_of_pos : ∀ s : ℝ, 0 < s → hbump s = 0 := by
    intro s hs
    by_contra hsne
    have hs_mem_support : s ∈ Function.support hbump := by
      simpa [Function.mem_support] using hsne
    have hs_mem : s ∈ Set.Icc (-3 : ℝ) (-1 : ℝ) := hsupp hs_mem_support
    have : s ≤ -1 := hs_mem.2
    linarith
  have hbump_zero : hbump 0 = 0 := by
    by_contra h0ne
    have h0mem : (0 : ℝ) ∈ Function.support hbump := by
      simpa [Function.mem_support] using h0ne
    have h0int : (0 : ℝ) ∈ Set.Icc (-3 : ℝ) (-1 : ℝ) := hsupp h0mem
    have : (0 : ℝ) ≤ -1 := h0int.2
    norm_num at this
  have hbump_ne : hbump ≠ 0 := by
    rw [Function.ne_iff]
    refine ⟨-2, ?_⟩
    rw [hbump_neg2]
    norm_num
  have hderiv_zero_of_pos : ∀ s : ℝ, 0 < s → deriv hbump s = 0 := by
    intro s hs
    have h_eventually : hbump =ᶠ[nhds s] (fun _ : ℝ => (0 : ℝ)) := by
      have hneigh : Set.Ioo (s / 2) (s + 1) ∈ nhds s :=
        Ioo_mem_nhds (by exact half_lt_self hs) (by linarith)
      filter_upwards [hneigh] with t ht
      have ht_pos : 0 < t := by linarith [ht.1]
      by_contra ht_ne
      have ht_mem_support : t ∈ Function.support hbump := by
        simpa [Function.mem_support] using ht_ne
      have ht_mem : t ∈ Set.Icc (-3 : ℝ) (-1 : ℝ) := hsupp ht_mem_support
      have : t ≤ -1 := ht_mem.2
      linarith
    have hderiv : deriv hbump s = deriv (fun _ : ℝ => (0 : ℝ)) s := h_eventually.deriv_eq
    rw [hderiv]
    simp
  refine ⟨n, hdn, hn, 1, 1, oddSemicircleMomentConstant n, semicircle, hbump,
    profileX, profileX, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact semicircle_support_subset
  · exact semicircle_contDiffOn
  · exact semicircle_concaveOn
  · simp [semicircle]
  · simp [semicircle]
  · intro t ht
    exact semicircle_pos_of_mem_Ioo ht
  · simpa using hdiff
  · exact hbump_zero
  · exact hbump_ne
  · intro s hs
    exact ⟨profileX_pos s hs, profileX_pos s hs⟩
  · intro s hs
    rw [hbump_zero_of_pos s hs]
    have hposx : 0 < profileX s := profileX_pos s hs
    have hsq := semicircle_profileX_sq s
    have hf_nonneg : 0 ≤ semicircle (profileX s) := Real.sqrt_nonneg _
    have hline_nonneg : 0 ≤ s * profileX s := by positivity
    have hright : semicircle (profileX s) = s * profileX s :=
      (sq_eq_sq₀ hf_nonneg hline_nonneg).mp (by simpa using hsq)
    have hleft : semicircle (-profileX s) = s * profileX s := by
      rw [semicircle_even]
      exact hright
    constructor
    · rw [hleft]
      ring
    · simpa using hright
  · intro s hs
    rw [hbump_zero_of_pos s hs]
    have hpos : 0 < profileX s := profileX_pos s hs
    have hle : -profileX s ≤ profileX s := by linarith
    have hmain :
        (∫ t in (-profileX s)..(profileX s),
          (semicircle t ^ 2 - (s * t + 0) ^ 2) ^ n *
            Real.sqrt (semicircle t ^ 2 - (s * t + 0) ^ 2))
        = ∫ t in (-profileX s)..(profileX s),
          (1 - (1 + s ^ 2) * t ^ 2) ^ n * Real.sqrt (1 - (1 + s ^ 2) * t ^ 2) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hle] at ht
      have htIcc : t ∈ Set.Icc (-1 : ℝ) 1 := by
        constructor
        · have hmem := profileX_mem_Icc s
          have : -1 ≤ -profileX s := by linarith [hmem.2]
          linarith [ht.1]
        · have hmem := profileX_mem_Icc s
          linarith [ht.2, hmem.2]
      change (semicircle t ^ 2 - (s * t + 0) ^ 2) ^ n *
        Real.sqrt (semicircle t ^ 2 - (s * t + 0) ^ 2) =
        (1 - (1 + s ^ 2) * t ^ 2) ^ n * Real.sqrt (1 - (1 + s ^ 2) * t ^ 2)
      rw [semicircle_sq_of_mem_Icc htIcc]
      ring_nf
    rw [hmain]
    exact oddSemicircleMoment_scale n hs
  · intro s hs
    rw [hbump_zero_of_pos s hs, hderiv_zero_of_pos s hs]
    have hpos : 0 < profileX s := profileX_pos s hs
    have hle : -profileX s ≤ profileX s := by linarith
    have hmain :
        (∫ t in (-profileX s)..(profileX s),
          (semicircle t ^ 2 - (s * t + 0) ^ 2) ^ (n - 1) *
            Real.sqrt (semicircle t ^ 2 - (s * t + 0) ^ 2) * (t + 0))
        = ∫ t in (-profileX s)..(profileX s), oddSemicircleWeight n s t * t := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hle] at ht
      have htIcc : t ∈ Set.Icc (-1 : ℝ) 1 := by
        constructor
        · have hmem := profileX_mem_Icc s
          have : -1 ≤ -profileX s := by linarith [hmem.2]
          linarith [ht.1]
        · have hmem := profileX_mem_Icc s
          linarith [ht.2, hmem.2]
      change (semicircle t ^ 2 - (s * t + 0) ^ 2) ^ (n - 1) *
        Real.sqrt (semicircle t ^ 2 - (s * t + 0) ^ 2) * (t + 0) =
        oddSemicircleWeight n s t * t
      rw [semicircle_sq_of_mem_Icc htIcc]
      unfold oddSemicircleWeight
      ring_nf
    rw [hmain]
    exact oddSemicircleWeight_t_integral_zero n s (profileX s)

end

end Commons.Geometry.Ulam