import Mathlib
import Submission.Work.Asymptotics.HalfFunnel.tangDefs
import Submission.Work.Asymptotics.jInvariantFun_eq_smul_of_eq

namespace Work.Asymptotics.HalfFunnel

open UpperHalfPlane ModularGroup

noncomputable section

/-! ## Elementary geometry of the tangency region

The tangency region is the union of two quarter-balls (of radius `1/8` in the hyperbolic
metric, but here only the Euclidean ball matters) about `±1/2 + i/2`; all the estimates below
use only that the point has imaginary part in `[1/2, 5/8)` and real part in
`(3/8,5/8) ∪ (-5/8,-3/8)`, together with the fact that it lies in the CKMRV fundamental
domain `𝒟`. -/

/-- Membership in the tangency region forces the point into the union of the two small
quarter-balls of radius `1/8` about the tangency points: the imaginary part lies in
`[1/2, 5/8)` and the real part in `(3/8,5/8) ∪ (-5/8,-3/8)`. -/
lemma ctanRegion_bounds (τ : ℍ) (hτ : τ ∈ ctanRegion) :
    (1 / 2 ≤ τ.im ∧ τ.im < 5 / 8) ∧
      ((3 / 8 < τ.re ∧ τ.re < 5 / 8) ∨ (-(5 / 8) < τ.re ∧ τ.re < -(3 / 8))) := by
  have hP : ((τ : ℂ) - ctanP).re = τ.re - 1 / 2 := by
    simp [ctanP, Complex.sub_re, UpperHalfPlane.coe_re]
  have hPi : ((τ : ℂ) - ctanP).im = τ.im - 1 / 2 := by
    simp [ctanP, Complex.sub_im, UpperHalfPlane.coe_im]
  have hM : ((τ : ℂ) - ctanM).re = τ.re + 1 / 2 := by
    simp [ctanM, Complex.sub_re, UpperHalfPlane.coe_re]
  have hMi : ((τ : ℂ) - ctanM).im = τ.im - 1 / 2 := by
    simp [ctanM, Complex.sub_im, UpperHalfPlane.coe_im]
  rcases hτ.2.2.2 with h | h
  · have him : |τ.im - 1 / 2| < 1 / 8 := by
      have := Complex.abs_im_le_norm ((τ : ℂ) - ctanP)
      rw [hPi] at this
      exact lt_of_le_of_lt this h
    have hre : |τ.re - 1 / 2| < 1 / 8 := by
      have := Complex.abs_re_le_norm ((τ : ℂ) - ctanP)
      rw [hP] at this
      exact lt_of_le_of_lt this h
    refine ⟨⟨hτ.2.1, ?_⟩, Or.inl ?_⟩
    · have := (abs_lt.mp him).2; linarith
    · have := abs_lt.mp hre; constructor <;> linarith [this.1, this.2]
  · have him : |τ.im - 1 / 2| < 1 / 8 := by
      have := Complex.abs_im_le_norm ((τ : ℂ) - ctanM)
      rw [hMi] at this
      exact lt_of_le_of_lt this h
    have hre : |τ.re + 1 / 2| < 1 / 8 := by
      have := Complex.abs_re_le_norm ((τ : ℂ) - ctanM)
      rw [hM] at this
      exact lt_of_le_of_lt this h
    refine ⟨⟨hτ.2.1, ?_⟩, Or.inr ?_⟩
    · have := (abs_lt.mp him).2; linarith
    · have := abs_lt.mp hre; constructor <;> linarith [this.1, this.2]

/-! ## Bounds on `u / (u^2 + Y^2)` -/

/-- For `u ∈ (3/8,5/8)` and `Y ∈ [1/2,5/8)`, the ratio `u/(u²+Y²)` lies in `(1/4,1]`. -/
lemma ratio_pos {u Y : ℝ} (hu1 : 3 / 8 < u) (hu2 : u < 5 / 8) (hY1 : 1 / 2 ≤ Y)
    (hY2 : Y < 5 / 8) : 1 / 4 < u / (u ^ 2 + Y ^ 2) ∧ u / (u ^ 2 + Y ^ 2) ≤ 1 := by
  have hpos : 0 < u ^ 2 + Y ^ 2 := by nlinarith [sq_nonneg u, hY1]
  constructor
  · rw [lt_div_iff₀ hpos]; nlinarith [sq_nonneg (u - 5 / 8), sq_nonneg (u - 3 / 8), sq_nonneg Y]
  · rw [div_le_one hpos]; nlinarith [sq_nonneg (u - 1 / 2), sq_nonneg Y]

/-- For `u ∈ (-5/8,-3/8)` and `Y ∈ [1/2,5/8)`, the ratio `u/(u²+Y²)` lies in `[-1,-1/4)`. -/
lemma ratio_neg {u Y : ℝ} (hu1 : -(5 / 8) < u) (hu2 : u < -(3 / 8)) (hY1 : 1 / 2 ≤ Y)
    (hY2 : Y < 5 / 8) : -1 ≤ u / (u ^ 2 + Y ^ 2) ∧ u / (u ^ 2 + Y ^ 2) < -(1 / 4) := by
  have hpos : 0 < u ^ 2 + Y ^ 2 := by nlinarith [sq_nonneg u, hY1]
  constructor
  · rw [le_div_iff₀ hpos]; nlinarith [sq_nonneg (u + 1 / 2), sq_nonneg Y]
  · rw [div_lt_iff₀ hpos]; nlinarith [sq_nonneg (u + 5 / 8), sq_nonneg (u + 3 / 8), sq_nonneg Y]

/-- Strictness at the endpoint `-1`: if `u ∈ (-5/8,-3/8)` and `(u+1/2)²+Y² > 1/4` (which is
the CKMRV fundamental-domain condition, read in the variable `u+1/2 = τ.re ∓ 1/2`), then
`u/(u²+Y²) > -1`. -/
lemma ratio_gt_neg_one {u Y : ℝ} (hu1 : -(5 / 8) < u) (hu2 : u < -(3 / 8))
    (hD : 1 / 4 < (u + 1 / 2) ^ 2 + Y ^ 2) : -1 < u / (u ^ 2 + Y ^ 2) := by
  have hpos : 0 < u ^ 2 + Y ^ 2 := by nlinarith [sq_nonneg u, hu1, hu2]
  rw [lt_div_iff₀ hpos]
  nlinarith [sq_nonneg (u + 1 / 2)]

/-! ## Combinatorial control of the integer offset -/

/-- If `X ∈ (3/8,5/8) ∪ (-5/8,-3/8)`, `u = X + m` for an integer `m` and `|u| < 1`, then `u`
lies in the same union. -/
lemma u_mem_of {X u : ℝ} {m : ℤ}
    (hX : (3 / 8 < X ∧ X < 5 / 8) ∨ (-(5 / 8) < X ∧ X < -(3 / 8))) (hm : |u| < 1)
    (hrel : u = X + (m : ℝ)) :
    (3 / 8 < u ∧ u < 5 / 8) ∨ (-(5 / 8) < u ∧ u < -(3 / 8)) := by
  have hulo : -1 < u := (abs_lt.mp hm).1
  have huhi : u < 1 := (abs_lt.mp hm).2
  have hmv : (m : ℝ) = u - X := by linarith [hrel]
  rcases hX with hA | hB
  · have hm2a : (-2 : ℤ) < m := by
      have : (-2 : ℝ) < (m : ℝ) := by rw [hmv]; linarith [hulo, hA.2]
      exact_mod_cast this
    have hm2b : m < 1 := by
      have : (m : ℝ) < 1 := by rw [hmv]; linarith [huhi, hA.1]
      exact_mod_cast this
    interval_cases m
    · right; rw [hrel]; push_cast; constructor <;> linarith [hA.1, hA.2]
    · left; rw [hrel]; push_cast; simpa using hA
  · have hm2a : (-1 : ℤ) < m := by
      have : (-1 : ℝ) < (m : ℝ) := by rw [hmv]; linarith [hulo, hB.1]
      exact_mod_cast this
    have hm2b : m < 2 := by
      have : (m : ℝ) < 2 := by rw [hmv]; linarith [huhi, hB.2]
      exact_mod_cast this
    interval_cases m
    · right; rw [hrel]; push_cast; simpa using hB
    · left; rw [hrel]; push_cast; constructor <;> linarith [hB.1, hB.2]

/-- Sign analysis of the offset: if `X ∈ (3/8,5/8) ∪ (-5/8,-3/8)`, `u = X + m` also lies in
that union and `m` is an integer, then `u > 0` determines `m` (`0` in the right half-axis, `1`
in the left), and `u < 0` determines `m` (`-1` in the right half-axis, `0` in the left). -/
lemma cd_cases {X u : ℝ} {m : ℤ}
    (hX : (3 / 8 < X ∧ X < 5 / 8) ∨ (-(5 / 8) < X ∧ X < -(3 / 8)))
    (hu : (3 / 8 < u ∧ u < 5 / 8) ∨ (-(5 / 8) < u ∧ u < -(3 / 8))) (hrel : u = X + (m : ℝ)) :
    (0 < u → ((3 / 8 < X ∧ X < 5 / 8) ∧ m = 0) ∨ ((-(5 / 8) < X ∧ X < -(3 / 8)) ∧ m = 1)) ∧
    (u < 0 → ((3 / 8 < X ∧ X < 5 / 8) ∧ m = -1) ∨ ((-(5 / 8) < X ∧ X < -(3 / 8)) ∧ m = 0)) := by
  have hulo : -5 / 8 < u := by rcases hu with h | h <;> linarith [h.1]
  have huhi : u < 5 / 8 := by rcases hu with h | h <;> linarith [h.2]
  have hmv : (m : ℝ) = u - X := by linarith [hrel]
  constructor
  · intro hu0
    rcases hX with hA | hB
    · left
      refine ⟨hA, ?_⟩
      have hm_ge : (-1 : ℤ) < m := by
        have : (-1 : ℝ) < (m : ℝ) := by rw [hmv]; linarith [hu0, hA.2]
        exact_mod_cast this
      have hm_lt : m < 1 := by
        have : (m : ℝ) < 1 := by rw [hmv]; linarith [huhi, hA.1]
        exact_mod_cast this
      omega
    · right
      refine ⟨hB, ?_⟩
      have hm_ge : (0 : ℤ) < m := by
        have : (0 : ℝ) < (m : ℝ) := by rw [hmv]; linarith [hu0, hB.2]
        exact_mod_cast this
      have hm_lt : m < 2 := by
        have : (m : ℝ) < 2 := by rw [hmv]; linarith [huhi, hB.1]
        exact_mod_cast this
      omega
  · intro hu0
    rcases hX with hA | hB
    · left
      refine ⟨hA, ?_⟩
      have hm_lt : m < 0 := by
        have : (m : ℝ) < 0 := by rw [hmv]; linarith [hu0, hA.1]
        exact_mod_cast this
      have hm_ge : (-2 : ℤ) < m := by
        have : (-2 : ℝ) < (m : ℝ) := by rw [hmv]; linarith [hulo, hA.2]
        exact_mod_cast this
      omega
    · right
      refine ⟨hB, ?_⟩
      have hm_lt : m < 1 := by
        have : (m : ℝ) < 1 := by rw [hmv]; linarith [hu0, hB.1]
        exact_mod_cast this
      have hm_ge : (0 : ℤ) ≤ m := by
        have h1 : (-1 : ℤ) < m := by
          have : (-1 : ℝ) < (m : ℝ) := by rw [hmv]; linarith [hulo, hB.2]
          exact_mod_cast this
        omega
      omega

/-! ## The algebraic normal form of a Möbius transform with `c² = 1` -/

/-- If `c² = 1` and `ad - bc = 1` then `(aτ+b)/(cτ+d) = ca - 1/(τ+cd)`. -/
private lemma moebius_sub_inv (τ c d a b : ℂ) (hc : c ^ 2 = 1) (hdet : a * d - b * c = 1)
    (hden : c * τ + d ≠ 0) (hden2 : τ + c * d ≠ 0) :
    (a * τ + b) / (c * τ + d) = c * a - 1 / (τ + c * d) := by
  rw [div_eq_iff hden]
  have key : c * (τ + c * d) = c * τ + d := by
    rw [mul_add, ← mul_assoc, ← pow_two, hc, one_mul]
  have hratio : (1 / (τ + c * d)) * (c * τ + d) = c := by
    rw [one_div, ← key, mul_comm c (τ + c * d), ← mul_assoc, inv_mul_cancel₀ hden2, one_mul]
  rw [sub_mul, hratio]
  have hgoal : c * a * (c * τ + d) - c - (a * τ + b) = 0 := by
    linear_combination (τ * a + b) * hc + c * hdet
  linear_combination -hgoal

/-! ## Auxiliary integer and norm computations -/

/-- The integer squares not exceeding `4`. -/
private lemma int_cases_of_sq_le_four (c : ℤ) (h : (c : ℝ) ^ 2 ≤ 4) :
    c = -2 ∨ c = -1 ∨ c = 0 ∨ c = 1 ∨ c = 2 := by
  have habs : (-2 : ℝ) ≤ (c : ℝ) ∧ (c : ℝ) ≤ 2 := by
    have h' : (c : ℝ) ^ 2 ≤ (2 : ℝ) ^ 2 := by norm_num at h ⊢; exact h
    have h2 := abs_le.mp (sq_le_sq.mp h')
    rwa [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at h2
  have hz1 : (-2 : ℤ) ≤ c := by exact_mod_cast habs.1
  have hz2 : c ≤ 2 := by exact_mod_cast habs.2
  omega

/-- The squared norm of `τ - 1/2`. -/
private lemma normSq_sub_half (τ : ℍ) :
    ‖(τ : ℂ) - (1 / 2 : ℂ)‖ ^ 2 = (τ.re - 1 / 2) ^ 2 + τ.im ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  norm_num
  ring

/-- The squared norm of `τ + 1/2`. -/
private lemma normSq_add_half (τ : ℍ) :
    ‖(τ : ℂ) + (1 / 2 : ℂ)‖ ^ 2 = (τ.re + 1 / 2) ^ 2 + τ.im ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  norm_num
  ring

/-- The fundamental-domain conditions, in coordinates. -/
private lemma domainD_conditions {τ : ℍ} (hτD : τ ∈ DomainD) :
    1 / 4 < (τ.re - 1 / 2) ^ 2 + τ.im ^ 2 ∧ 1 / 4 < (τ.re + 1 / 2) ^ 2 + τ.im ^ 2 := by
  refine ⟨?_, ?_⟩
  · have h := hτD.2.2.1
    have hp : (0 : ℝ) < ‖(τ : ℂ) - (1 / 2 : ℂ)‖ := by linarith
    have hlt : (1 / 4 : ℝ) < ‖(τ : ℂ) - (1 / 2 : ℂ)‖ ^ 2 := by nlinarith [h, hp]
    rwa [normSq_sub_half] at hlt
  · have h := hτD.2.2.2
    have hp : (0 : ℝ) < ‖(τ : ℂ) + (1 / 2 : ℂ)‖ := by linarith
    have hlt : (1 / 4 : ℝ) < ‖(τ : ℂ) + (1 / 2 : ℂ)‖ ^ 2 := by nlinarith [h, hp]
    rwa [normSq_add_half] at hlt

/-- `(c)² = 4` is incompatible with the region and the fundamental domain. -/
private lemma sq_ne_four_of {τ : ℍ} (hτD : τ ∈ DomainD) (hy1 : 1 / 2 ≤ τ.im)
    (hy2 : τ.im < 5 / 8)
    (hxcase : (3 / 8 < τ.re ∧ τ.re < 5 / 8) ∨ (-(5 / 8) < τ.re ∧ τ.re < -(3 / 8)))
    {c d : ℤ} (hF1 : ((c : ℝ) * τ.re + (d : ℝ)) ^ 2 + ((c : ℝ) * τ.im) ^ 2 ≤ 2 * τ.im)
    (hsq : (c : ℝ) ^ 2 = 4) : False := by
  have hY : τ.im = 1 / 2 := by
    have h2 : ((c : ℝ) * τ.im) ^ 2 ≤ 2 * τ.im :=
      by nlinarith [hF1, sq_nonneg ((c : ℝ) * τ.re + (d : ℝ))]
    rw [mul_pow, hsq] at h2
    nlinarith [h2, hy1, τ.im_pos]
  have hzero : (c : ℝ) * τ.re + (d : ℝ) = 0 := by
    have h3 : ((c : ℝ) * τ.re + (d : ℝ)) ^ 2 ≤ 0 := by
      have h := hF1
      have hcy : ((c : ℝ) * τ.im) ^ 2 = 1 := by rw [hY, mul_pow, hsq]; norm_num
      linarith [h, hcy]
    nlinarith [sq_nonneg ((c : ℝ) * τ.re + (d : ℝ)), h3]
  have hXb : 3 / 8 < |τ.re| ∧ |τ.re| < 5 / 8 := by
    rcases hxcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [abs_of_pos (by linarith)]; exact ⟨h1, h2⟩
    · rw [abs_of_neg (by linarith)]; constructor <;> linarith
  have hcr : (c : ℝ) * τ.re = -(d : ℝ) := by linarith [hzero]
  have hcabs : |(c : ℝ)| = 2 := by
    have h1 : |(c : ℝ)| ^ 2 = 4 := by rw [sq_abs, hsq]
    nlinarith [abs_nonneg (c : ℝ), h1]
  have hd_eq : ((|d| : ℤ) : ℝ) = 2 * |τ.re| := by
    have h2 : |((d : ℤ) : ℝ)| = 2 * |τ.re| := by
      have h3 : |(c : ℝ) * τ.re| = |((d : ℤ) : ℝ)| := by rw [hcr, abs_neg]
      rw [abs_mul, hcabs] at h3
      linarith [h3]
    rwa [← Int.cast_abs] at h2
  have hXabs : |τ.re| = 1 / 2 := by
    have hlo : (3 : ℝ) / 4 < ((|d| : ℤ) : ℝ) := by linarith [hd_eq, hXb.1]
    have hhi : ((|d| : ℤ) : ℝ) < 5 / 4 := by linarith [hd_eq, hXb.2]
    have hdz : |d| = 1 := by
      have h1 : (1 : ℤ) ≤ |d| := by
        have hpos : (0 : ℝ) < ((|d| : ℤ) : ℝ) := by linarith
        have hz : (0 : ℤ) < |d| := by exact_mod_cast hpos
        omega
      have h2 : |d| < 2 := by
        have : ((|d| : ℤ) : ℝ) < 2 := by linarith
        exact_mod_cast this
      omega
    have h1' : ((|d| : ℤ) : ℝ) = 1 := by rw [hdz]; norm_num
    linarith [hd_eq, h1']
  have hx12 : τ.re = 1 / 2 ∨ τ.re = -(1 / 2) := by
    rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1 / 2)).mp hXabs with h | h
    · exact Or.inl h
    · exact Or.inr h
  rcases hx12 with hx | hx
  · have h := hτD.2.2.1
    have hp : (0 : ℝ) < ‖(τ : ℂ) - (1 / 2 : ℂ)‖ := by linarith
    have hlt : (1 / 4 : ℝ) < ‖(τ : ℂ) - (1 / 2 : ℂ)‖ ^ 2 := by nlinarith [h, hp]
    rw [normSq_sub_half, hx, hY] at hlt
    norm_num at hlt
  · have h := hτD.2.2.2
    have hp : (0 : ℝ) < ‖(τ : ℂ) + (1 / 2 : ℂ)‖ := by linarith
    have hlt : (1 / 4 : ℝ) < ‖(τ : ℂ) + (1 / 2 : ℂ)‖ ^ 2 := by nlinarith [h, hp]
    rw [normSq_add_half, hx, hY] at hlt
    norm_num at hlt

/-- **The orbit point in the rectangle is the first pole.**

If `τ` lies in the tangency region and `ζ` is a point of the rectangle
`[0,1/4] × [1/2,3/2]` with `j(ζ) = j(τ)`, then `ζ` is the first pole `z₁τ`. -/
theorem tangOrbitRect (τ ζ : UpperHalfPlane) (hτ : τ ∈ ctanRegion)
    (hre : 0 ≤ ζ.re) (hre' : ζ.re ≤ 1 / 4) (him : (1 : ℝ) / 2 ≤ ζ.im) (him' : ζ.im ≤ 3 / 2)
    (hj : Work.Kernels.jInvariantFun ζ = Work.Kernels.jInvariantFun τ) :
    ζ = poleOne τ := by
  obtain ⟨g, hg⟩ := Work.Asymptotics.jInvariantFun_eq_smul_of_eq hj
  obtain ⟨⟨hy1, hy2⟩, hxcase⟩ := ctanRegion_bounds τ hτ
  have hτD : τ ∈ DomainD := hτ.1
  obtain ⟨hDm, hDp⟩ := domainD_conditions hτD
  set c : ℤ := g 1 0 with hc
  set d : ℤ := g 1 1 with hd
  set a : ℤ := g 0 0 with ha
  set b : ℤ := g 0 1 with hb
  have hdet : a * d - b * c = 1 := by
    have hh := g.2
    rw [Matrix.det_fin_two] at hh
    rw [← hc, ← hd, ← ha, ← hb] at hh
    exact_mod_cast hh
  have hcoe : (ζ : ℂ) = ((a:ℂ)*(τ:ℂ)+(b:ℂ))/((c:ℂ)*(τ:ℂ)+(d:ℂ)) := by
    have h0 : (ζ:ℂ) = (((g 0 0 : ℤ):ℂ)*(τ:ℂ)+((g 0 1 : ℤ):ℂ))
        /(((g 1 0 : ℤ):ℂ)*(τ:ℂ)+((g 1 1 : ℤ):ℂ)) := by
      rw [← hg, UpperHalfPlane.coe_specialLinearGroup_apply]
      simp only [algebraMap_int_eq]
      simp
    rw [h0, ← ha, ← hb, ← hc, ← hd]
  have him_eq : ζ.im = τ.im / ‖((c:ℝ):ℂ)*(τ:ℂ)+((d:ℝ):ℂ)‖^2 := by
    have hD : ((g 1 0 : ℤ):ℂ)*(τ:ℂ)+((g 1 1 : ℤ):ℂ) = ((c:ℝ):ℂ)*(τ:ℂ)+((d:ℝ):ℂ) := by
      rw [hc, hd]; push_cast <;> ring
    rw [← hg, ModularGroup.im_smul_eq_div_normSq, ModularGroup.denom_apply,
      Complex.normSq_eq_norm_sq, hD]
  have hNcoords : ‖((c:ℝ):ℂ)*(τ:ℂ)+((d:ℝ):ℂ)‖^2
      = ((c:ℝ)*τ.re+(d:ℝ))^2+((c:ℝ)*τ.im)^2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    ring
  have hNne : ‖((c:ℝ):ℂ)*(τ:ℂ)+((d:ℝ):ℂ)‖^2 ≠ 0 := by
    intro h0
    rw [him_eq, h0, div_zero] at him
    linarith [him]
  have hNpos : 0 < ‖((c:ℝ):ℂ)*(τ:ℂ)+((d:ℝ):ℂ)‖^2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm hNne)
  rw [him_eq] at him
  have hF1 : ((c:ℝ)*τ.re+(d:ℝ))^2+((c:ℝ)*τ.im)^2 ≤ 2*τ.im := by
    rw [← hNcoords]
    have hmul := mul_le_mul_of_nonneg_right him (le_of_lt hNpos)
    rw [div_mul_cancel₀ _ (ne_of_gt hNpos)] at hmul
    linarith
  have hcsq_le : (c:ℝ)^2 * τ.im ≤ 2 := by
    have h1 : ((c:ℝ)*τ.im)^2 ≤ 2*τ.im := by
      nlinarith [hF1, sq_nonneg ((c:ℝ)*τ.re+(d:ℝ))]
    nlinarith [h1, τ.im_pos]
  have hc_sq_le4 : (c:ℝ)^2 ≤ 4 := by nlinarith [hcsq_le, hy1]
  have hc_le2 := int_cases_of_sq_le_four c hc_sq_le4
  have hc_ne_abs2 : (c:ℝ)^2 ≠ 4 := fun h => sq_ne_four_of hτD hy1 hy2 hxcase hF1 h
  have hc_ne0 : c ≠ 0 := by
    intro hc0
    have had : a * d = 1 := by rw [hc0] at hdet; linarith
    have had1 : (a = 1 ∧ d = 1) ∨ (a = -1 ∧ d = -1) := by
      rcases Int.eq_one_or_neg_one_of_mul_eq_one' had with h' | h'
      · exact Or.inl h'
      · exact Or.inr h'
    have hζm : (ζ:ℂ) = (τ:ℂ) + ((d*b:ℤ):ℂ) := by
      rw [hcoe, hc0]
      simp only [Int.cast_zero, zero_mul, zero_add]
      rcases had1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]; push_cast; ring
      · rw [h1, h2]; push_cast; ring
    have hre_eq : ζ.re = τ.re + ((d*b:ℤ):ℝ) := by
      have h := congrArg Complex.re hζm
      rw [Complex.add_re, UpperHalfPlane.coe_re] at h
      have hc' : ((d*b:ℤ):ℂ).re = ((d*b:ℤ):ℝ) := by push_cast; simp
      rw [hc'] at h
      exact h
    rcases hxcase with ⟨hx1, hx2⟩ | ⟨hx1, hx2⟩
    · have h1 : (-(5:ℝ)/8) < ((d*b:ℤ):ℝ) := by linarith [hre_eq, hre, hx2]
      have h2 : ((d*b:ℤ):ℝ) < (-(1:ℝ)/8) := by linarith [hre_eq, hre', hx1]
      have hz1 : (-1:ℤ) < d*b := by
        have : (-1:ℝ) < ((d*b:ℤ):ℝ) := by linarith
        exact_mod_cast this
      have hz2 : d*b < 0 := by
        have : ((d*b:ℤ):ℝ) < 0 := by linarith
        exact_mod_cast this
      omega
    · have h1 : (3:ℝ)/8 < ((d*b:ℤ):ℝ) := by linarith [hre_eq, hre, hx1]
      have h2 : ((d*b:ℤ):ℝ) < (7:ℝ)/8 := by linarith [hre_eq, hre', hx2]
      have hz1 : (0:ℤ) < d*b := by
        have : (0:ℝ) < ((d*b:ℤ):ℝ) := by linarith
        exact_mod_cast this
      have hz2 : d*b < 1 := by
        have : ((d*b:ℤ):ℝ) < 1 := by linarith
        exact_mod_cast this
      omega
  have hc_pm1 : c = 1 ∨ c = -1 := by
    rcases hc_le2 with h | h | h | h | h
    · exact absurd (by rw [h]; norm_num) hc_ne_abs2
    · exact Or.inr h
    · exact absurd h hc_ne0
    · exact Or.inl h
    · exact absurd (by rw [h]; norm_num) hc_ne_abs2
  have hcsq1 : (c:ℝ)^2 = 1 := by rcases hc_pm1 with h | h <;> rw [h] <;> norm_num
  have hcsqC : (c:ℂ)^2 = 1 := by rcases hc_pm1 with h | h <;> rw [h] <;> norm_num
  have hcabs : |(c:ℝ)| = 1 := by rcases hc_pm1 with h | h <;> rw [h] <;> norm_num
  have hden : (c:ℂ)*(τ:ℂ)+(d:ℂ) ≠ 0 := by
    intro h0
    apply hNne
    have : ((c:ℝ):ℂ)*(τ:ℂ)+((d:ℝ):ℂ) = 0 := by rw [← h0]; push_cast; ring
    rw [this]; simp
  have hζ : (ζ:ℂ) = (c:ℂ)*(a:ℂ) - 1/((τ:ℂ)+(c:ℂ)*(d:ℂ)) := by
    have hdetC : (a:ℂ)*(d:ℂ)-(b:ℂ)*(c:ℂ) = 1 := by exact_mod_cast hdet
    have hden2 : (τ:ℂ) + (c:ℂ)*(d:ℂ) ≠ 0 := by
      intro h0
      apply hden
      have key : (c:ℂ)*((τ:ℂ)+(c:ℂ)*(d:ℂ)) = (c:ℂ)*(τ:ℂ)+(d:ℂ) := by
        rw [mul_add, ← mul_assoc, ← pow_two, hcsqC, one_mul]
      rw [h0, mul_zero] at key
      exact key.symm
    have h := moebius_sub_inv (τ:ℂ) (c:ℂ) (d:ℂ) (a:ℂ) (b:ℂ) hcsqC hdetC hden hden2
    rw [hcoe, h]
  -- the fundamental real-part identity
  have hζre0 : ζ.re = (c:ℝ)*(a:ℝ)
      - (τ.re + (c:ℝ)*(d:ℝ))/((τ.re+(c:ℝ)*(d:ℝ))^2 + τ.im^2) := by
    have hw : ((τ:ℂ)+(c:ℂ)*(d:ℂ)).re = τ.re + (c:ℝ)*(d:ℝ) := by
      simp [Complex.add_re, Complex.mul_re, UpperHalfPlane.coe_re]
    have hwn : Complex.normSq ((τ:ℂ)+(c:ℂ)*(d:ℂ))
        = (τ.re+(c:ℝ)*(d:ℝ))^2 + τ.im^2 := by
      rw [Complex.normSq_apply, hw]
      have him2 : ((τ:ℂ)+(c:ℂ)*(d:ℂ)).im = τ.im := by
        simp [Complex.add_im, Complex.mul_im, UpperHalfPlane.coe_im]
      rw [him2]; ring
    have h1 : ((c:ℂ)*(a:ℂ)).re = (c:ℝ)*(a:ℝ) := by simp [Complex.mul_re]
    have hr := congrArg Complex.re hζ
    rw [Complex.sub_re, h1, one_div, Complex.inv_re, hw, hwn] at hr
    simpa using hr
  -- the offset
  set u : ℝ := τ.re + (c:ℝ)*(d:ℝ) with hu
  have hrel : u = τ.re + ((c*d:ℤ):ℝ) := by rw [hu]; push_cast; ring
  have hsq_lt : ((c:ℝ)*τ.re+(d:ℝ))^2 < 1 := by
    have h1 : ((c:ℝ)*τ.re+(d:ℝ))^2 + τ.im^2 ≤ 2*τ.im := by
      have h2 : ((c:ℝ)*τ.im)^2 = τ.im^2 := by rw [mul_pow, hcsq1, one_mul]
      linarith [hF1, h2]
    nlinarith [h1, hy1, hy2]
  have hlt1 : |(c:ℝ)*τ.re+(d:ℝ)| < 1 := (sq_lt_one_iff_abs_lt_one _).mp hsq_lt
  have hcu : (c:ℝ) * u = (c:ℝ)*τ.re+(d:ℝ) := by
    rw [hu, mul_add, ← mul_assoc, ← pow_two, hcsq1, one_mul]
  have hu_abs : |u| < 1 := by
    have h2 : |(c:ℝ)*u| < 1 := by rw [hcu]; exact hlt1
    rwa [abs_mul, hcabs, one_mul] at h2
  have hmem : (3/8 < u ∧ u < 5/8) ∨ (-(5/8) < u ∧ u < -(3/8)) :=
    u_mem_of hxcase hu_abs hrel
  have hu_lo : -(5/8 : ℝ) < u := by rcases hmem with h | h <;> linarith [h.1]
  have hu_hi : u < 5/8 := by rcases hmem with h | h <;> linarith [h.2]
  have hζre : ζ.re = ((c*a:ℤ):ℝ) - u/(u^2+τ.im^2) := by
    rw [hu, hζre0]
    push_cast
    ring
  rcases lt_trichotomy u 0 with hun | huz | hup
  · -- `u < 0`: the offset is strongly negative, contradiction
    have hcc := (cd_cases hxcase hmem hrel).2 hun
    have hu_nhi : u < -(3/8 : ℝ) := by rcases hmem with h | h <;> linarith [h.1, h.2, hun]
    have hD : 1/4 < (u + 1/2)^2 + τ.im^2 := by
      rcases hcc with ⟨hA, hm⟩ | ⟨hB, hm⟩
      · have he : u + 1/2 = τ.re - 1/2 := by rw [hrel, hm]; push_cast; ring
        rw [he]; linarith [hDm]
      · have he : u + 1/2 = τ.re + 1/2 := by rw [hrel, hm]; push_cast; ring
        rw [he]; linarith [hDp]
    have ht := ratio_gt_neg_one hu_lo hu_nhi hD
    have hneg := ratio_neg hu_lo hu_nhi hy1 hy2
    have hca : c*a = -1 := by
      have e : ((c*a:ℤ):ℝ) = ζ.re + u/(u^2+τ.im^2) := by linarith [hζre]
      have h1 : ((c*a:ℤ):ℝ) < 0 := by linarith [e, hre', hneg.2]
      have h2 : (-1:ℝ) ≤ ((c*a:ℤ):ℝ) := by linarith [e, hre, hneg.1]
      have hz1 : c*a < 0 := by exact_mod_cast h1
      have hz2 : (-1:ℤ) ≤ c*a := by exact_mod_cast h2
      omega
    have : ζ.re = -1 - u/(u^2+τ.im^2) := by rw [hζre, hca]; push_cast; ring
    have ht2 : u/(u^2+τ.im^2) ≤ -1 := by linarith [hre, this]
    linarith [ht, ht2]
  · -- `u = 0` is impossible
    rcases hmem with h | h <;> linarith [h.1, h.2, huz]
  · -- `u > 0`: the offset is `0` or `1`, and the pole is `1 - 1/(τ + cd)`
    have hcc := (cd_cases hxcase hmem hrel).1 hup
    have hu_pos_lo : 3/8 < u := by rcases hmem with h | h <;> linarith [h.1, h.2, hup]
    have hpos := ratio_pos hu_pos_lo hu_hi hy1 hy2
    have hca : c*a = 1 := by
      have e : ((c*a:ℤ):ℝ) = ζ.re + u/(u^2+τ.im^2) := by linarith [hζre]
      have h1 : (1:ℝ)/4 < ((c*a:ℤ):ℝ) := by linarith [e, hre, hpos.1]
      have h2 : ((c*a:ℤ):ℝ) ≤ 5/4 := by linarith [e, hre', hpos.2]
      have hz1 : (0:ℤ) < c*a := by
        have : (0:ℝ) < ((c*a:ℤ):ℝ) := by linarith
        exact_mod_cast this
      have hz2 : c*a < 2 := by
        have : ((c*a:ℤ):ℝ) < 2 := by linarith
        exact_mod_cast this
      omega
    rcases hcc with ⟨hA, hm⟩ | ⟨hB, hm⟩
    · -- right half-axis: `cd = 0`, so the pole is `1 - 1/τ`
      apply UpperHalfPlane.ext
      have hcaC : (c:ℂ)*(a:ℂ) = 1 := by rw [← Int.cast_mul, hca]; norm_num
      have hcdC : (c:ℂ)*(d:ℂ) = 0 := by rw [← Int.cast_mul, hm]; norm_num
      have hζv : (ζ:ℂ) = 1 - 1/(τ:ℂ) := by
        rw [hζ, hcaC, hcdC, add_zero]
      have hpole : (poleOne τ : ℂ) = 1 - 1/(τ:ℂ) := by
        rw [poleOne_coe, if_neg (by linarith [hA.1] : ¬ τ.re < 0)]
      rw [hζv, hpole]
    · -- left half-axis: `cd = 1`, so the pole is `τ/(1+τ)`
      apply UpperHalfPlane.ext
      have hcaC : (c:ℂ)*(a:ℂ) = 1 := by rw [← Int.cast_mul, hca]; norm_num
      have hcdC : (c:ℂ)*(d:ℂ) = 1 := by rw [← Int.cast_mul, hm]; norm_num
      have hne : (τ:ℂ) + 1 ≠ 0 := by
        intro h
        have h1 : (τ:ℂ) = -1 := by linear_combination h
        have h2 : (τ:ℂ).im = 0 := by rw [h1]; simp
        rw [UpperHalfPlane.coe_im] at h2
        linarith [τ.im_pos]
      have hζv : (ζ:ℂ) = (τ:ℂ)/(1+(τ:ℂ)) := by
        rw [hζ, hcaC, hcdC, add_comm (1:ℂ) (τ:ℂ)]
        field_simp
        ring
      have hpole : (poleOne τ : ℂ) = (τ:ℂ)/(1+(τ:ℂ)) := by
        rw [poleOne_coe, if_pos (by linarith [hB.2] : τ.re < 0)]
      rw [hζv, hpole]

end

end Work.Asymptotics.HalfFunnel
