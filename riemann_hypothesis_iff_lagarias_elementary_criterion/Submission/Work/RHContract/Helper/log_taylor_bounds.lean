import Mathlib

namespace Work.RHContract.Helper

/-- If `f : ℝ → ℝ` is continuous on `[0, b]` and has nonnegative derivative on `(0, b)`, then
`f 0 ≤ f b`. -/
lemma le_of_hasDerivAt_nonneg_Icc {f g : ℝ → ℝ} {b : ℝ} (hb : 0 ≤ b)
    (hcont : ContinuousOn f (Set.Icc 0 b))
    (hd : ∀ x ∈ Set.Ioo 0 b, HasDerivAt f (g x) x)
    (hg : ∀ x ∈ Set.Ioo 0 b, 0 ≤ g x) : f 0 ≤ f b := by
  have hmono : MonotoneOn f (Set.Icc 0 b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 b) hcont
    · rw [interior_Icc]
      intro y hy
      exact (hd y hy).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro y hy
      rw [(hd y hy).deriv]
      exact hg y hy
  exact hmono (Set.mem_Icc.mpr ⟨le_rfl, hb⟩) (Set.mem_Icc.mpr ⟨hb, le_rfl⟩) hb

theorem log_taylor_bounds :
    (∀ y : ℝ, 0 ≤ y → y ^ 2 / 2 - y ^ 3 / 3 ≤ y - Real.log (1 + y)) ∧
    (∀ t : ℝ, 0 ≤ t → t - Real.log (1 + t) ≤ t ^ 2 / 2) ∧
    (∀ t : ℝ, 0 ≤ t → t / (1 + t) ≤ Real.log (1 + t)) ∧
    (∀ u : ℝ, 0 ≤ u → u < 1 → Real.log (1 - u) + u ≤ -(u ^ 2 / 2)) ∧
    (∀ u : ℝ, 0 ≤ u → u ≤ 1 / 2 →
      0 ≤ -Real.log (1 - u ^ 3) + Real.log (1 - u) + u + u ^ 2 / (2 * (1 - u))) ∧
    (∀ z : ℝ, 0 ≤ z → z < 1 → z ≤ -Real.log (1 - z)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- (1) `y²/2 - y³/3 ≤ y - log(1+y)`
    intro y hy
    have hcont : ContinuousOn (fun z : ℝ => z - Real.log (1+z) - z^2/2 + z^3/3) (Set.Icc 0 y) := by
      have hlog : ContinuousOn (fun z : ℝ => Real.log (1+z)) (Set.Icc 0 y) :=
        ContinuousOn.log ((continuous_const.add continuous_id).continuousOn)
          (by intro z hz; have h : (0:ℝ) ≤ z := hz.1; linarith)
      have h1 : ContinuousOn (fun z : ℝ => z) (Set.Icc 0 y) := continuousOn_id
      have h2 : ContinuousOn (fun z : ℝ => z^2/2) (Set.Icc 0 y) := (continuousOn_id.pow 2).div_const 2
      have h3 : ContinuousOn (fun z : ℝ => z^3/3) (Set.Icc 0 y) := (continuousOn_id.pow 3).div_const 3
      exact ((h1.sub hlog).sub h2).add h3
    have hd : ∀ x ∈ Set.Ioo 0 y, HasDerivAt (fun z : ℝ => z - Real.log (1+z) - z^2/2 + z^3/3) (1 - 1/(1+x) - x + x^2) x := by
      intro x hx
      have hlog : HasDerivAt (fun z : ℝ => Real.log (1+z)) (1/(1+x)) x := by
        have h : HasDerivAt (fun z : ℝ => (1:ℝ) + z) 1 x := (hasDerivAt_id x).const_add (1:ℝ)
        exact h.log (by linarith [hx.1])
      have h1 : HasDerivAt (fun z : ℝ => z) 1 x := hasDerivAt_id x
      have h2 : HasDerivAt (fun z : ℝ => z^2/2) x x := by
        have hh : HasDerivAt (fun z : ℝ => z^2) (2*x) x := by simpa using hasDerivAt_pow 2 x
        have hhh : HasDerivAt (fun z : ℝ => z^2/2) ((2*x)/2) x := hh.div_const 2
        convert hhh using 1; ring
      have h3 : HasDerivAt (fun z : ℝ => z^3/3) (x^2) x := by
        have hh : HasDerivAt (fun z : ℝ => z^3) (3*x^2) x := by simpa using hasDerivAt_pow 3 x
        have hhh : HasDerivAt (fun z : ℝ => z^3/3) ((3*x^2)/3) x := hh.div_const 3
        convert hhh using 1; ring
      exact ((h1.sub hlog).sub h2).add h3
    have hg : ∀ x ∈ Set.Ioo 0 y, 0 ≤ 1 - 1/(1+x) - x + x^2 := by
      intro x hx
      have hx0 : 0 < x := hx.1
      have hkey : 1 - 1/(1+x) - x + x^2 = x^3/(1+x) := by
        field_simp
        ring
      rw [hkey]
      exact div_nonneg (pow_nonneg hx0.le 3) (by linarith)
    have hmain := le_of_hasDerivAt_nonneg_Icc (f := fun z : ℝ => z - Real.log (1+z) - z^2/2 + z^3/3)
        (g := fun z : ℝ => 1 - 1/(1+z) - z + z^2) hy hcont hd hg
    have h0 : (0:ℝ) - Real.log (1+0) - 0^2/2 + 0^3/3 = 0 := by simp
    rw [h0] at hmain
    linarith
  · -- (2) `t - log(1+t) ≤ t²/2`
    intro t ht
    have h1 : 2*t/(t+2) ≤ Real.log (1+t) := Real.le_log_one_add_of_nonneg ht
    have h3 : t - 2*t/(t+2) = t^2/(t+2) := by field_simp; ring
    have h4 : t^2/(t+2) ≤ t^2/2 := by
      rw [div_le_iff₀ (by linarith : (0:ℝ) < t+2)]
      nlinarith [sq_nonneg t, ht]
    linarith
  · -- (3) `t/(1+t) ≤ log(1+t)`
    intro t ht
    have h := Real.one_sub_inv_le_log_of_pos (by linarith : (0:ℝ) < 1 + t)
    have he : (1:ℝ) - (1+t)⁻¹ = t/(1+t) := by field_simp; ring
    rw [he] at h
    exact h
  · -- (4) `log(1-u) + u ≤ -(u²/2)`
    intro u hu hu1
    have hu1pos : 0 < 1 - u := by linarith
    have hx : 0 ≤ u/(1-u) := div_nonneg hu hu1pos.le
    have hlog := Real.le_log_one_add_of_nonneg hx
    have hrw : 1 + u/(1-u) = 1/(1-u) := by field_simp; ring
    rw [hrw] at hlog
    have hlog2 : Real.log (1/(1-u)) = -(Real.log (1-u)) := by
      rw [Real.log_div one_ne_zero (ne_of_gt hu1pos), Real.log_one]; ring
    rw [hlog2] at hlog
    have hb : (u/(1-u))+2 ≠ 0 := by linarith [hx]
    have hd : (2:ℝ) - u ≠ 0 := by linarith
    have hsimp : 2*(u/(1-u))/((u/(1-u))+2) = 2*u/(2-u) := by
      rw [div_eq_div_iff hb hd]
      field_simp
      ring
    rw [hsimp] at hlog
    have hbound : u + u^2/2 ≤ 2*u/(2-u) := by
      rw [le_div_iff₀ (by linarith : (0:ℝ) < 2 - u)]
      nlinarith [mul_nonneg hu (sq_nonneg u)]
    linarith
  · -- (5) second-order bound for `-log(1-u³) + log(1-u) + u + u²/(2(1-u))`
    intro u hu hu2
    have hu1pos : 0 < 1 - u := by linarith
    have hfac : 1 - u^3 = (1-u)*(1+u+u^2) := by ring
    have hlogmul : Real.log (1 - u^3) = Real.log (1-u) + Real.log (1+u+u^2) := by
      rw [hfac, Real.log_mul (by linarith : (1-u) ≠ 0)
        (by have h : (0:ℝ) ≤ u := hu; positivity : (1+u+u^2) ≠ 0)]
    have heq : -Real.log (1-u^3) + Real.log (1-u) + u + u^2/(2*(1-u))
        = u + u^2/(2*(1-u)) - Real.log (1+u+u^2) := by linarith [hlogmul]
    rw [heq]
    have hcont : ContinuousOn (fun z : ℝ => z + z^2/(2*(1-z)) - Real.log (1+z+z^2)) (Set.Icc 0 u) := by
      have h1 : ContinuousOn (fun z : ℝ => z) (Set.Icc 0 u) := continuousOn_id
      have h2 : ContinuousOn (fun z : ℝ => z^2/(2*(1-z))) (Set.Icc 0 u) := by
        apply ContinuousOn.div
        · exact continuousOn_id.pow 2
        · exact ((continuous_const.sub continuous_id).const_mul 2).continuousOn
        · intro z hz
          have h : (0:ℝ) < 1 - z := by linarith [hz.2, hu2]
          positivity
      have h3 : ContinuousOn (fun z : ℝ => Real.log (1+z+z^2)) (Set.Icc 0 u) := by
        apply ContinuousOn.log
        · exact ((continuous_const.add continuous_id).continuousOn).add (continuousOn_id.pow 2)
        · intro z hz
          have hz0 : 0 ≤ z := hz.1
          positivity
      exact (h1.add h2).sub h3
    have hd : ∀ x ∈ Set.Ioo 0 u, HasDerivAt (fun z : ℝ => z + z^2/(2*(1-z)) - Real.log (1+z+z^2))
        (1 + (2*x - x^2)/(2*(1-x)^2) - (1+2*x)/(1+x+x^2)) x := by
      intro x hx
      have hx0 : 0 < x := hx.1
      have hnum : HasDerivAt (fun z : ℝ => z^2) (2*x) x := by simpa using hasDerivAt_pow 2 x
      have hden : HasDerivAt (fun z : ℝ => 2*(1-z)) (-2) x := by
        have h1 : HasDerivAt (fun z : ℝ => (1:ℝ) - z) (-1) x := (hasDerivAt_id x).const_sub 1
        simpa using h1.const_mul (2:ℝ)
      have hxlt : (0:ℝ) < 1 - x := by linarith [hx.2, hu2]
      have hfrac := hnum.div hden (mul_ne_zero (by norm_num) (ne_of_gt hxlt))
      have hfrac' : HasDerivAt (fun z : ℝ => z^2/(2*(1-z))) ((2*x - x^2)/(2*(1-x)^2)) x := by
        have hval : ((2*x) * (2*(1-x)) - x^2 * (-2)) / (2*(1-x))^2 = (2*x - x^2)/(2*(1-x)^2) := by
          field_simp
          ring
        rw [hval] at hfrac
        exact hfrac
      have hin : HasDerivAt (fun z : ℝ => 1 + z + z^2) (1 + 2*x) x := by
        have ha : HasDerivAt (fun z : ℝ => (1:ℝ) + z) 1 x := (hasDerivAt_id x).const_add 1
        have hb : HasDerivAt (fun z : ℝ => z^2) (2*x) x := by simpa using hasDerivAt_pow 2 x
        exact ha.add hb
      have hlog' : HasDerivAt (fun z : ℝ => Real.log (1+z+z^2)) ((1+2*x)/(1+x+x^2)) x :=
        hin.log (by positivity)
      exact ((hasDerivAt_id x).add hfrac').sub hlog'
    have hg : ∀ x ∈ Set.Ioo 0 u, 0 ≤ 1 + (2*x - x^2)/(2*(1-x)^2) - (1+2*x)/(1+x+x^2) := by
      intro x hx
      have hx1 : 0 < x := hx.1
      have hxlt : (0:ℝ) < 1 - x := by linarith [hx.2, hu2]
      have key : 1 + (2*x - x^2)/(2*(1-x)^2) - (1+2*x)/(1+x+x^2)
          = x^2*(x^2-5*x+7)/(2*(1-x)^2*(1+x+x^2)) := by
        have h1 : (1:ℝ) - x ≠ 0 := by linarith
        have h2 : (1:ℝ) + x + x^2 ≠ 0 := by positivity
        field_simp
        ring
      rw [key]
      apply div_nonneg
      · exact mul_nonneg (sq_nonneg x) (by nlinarith [sq_nonneg (x - 5/2)])
      · exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg (1-x)))
          (by nlinarith [sq_nonneg x, hx1.le])
    have hmain := le_of_hasDerivAt_nonneg_Icc
      (f := fun z : ℝ => z + z^2/(2*(1-z)) - Real.log (1+z+z^2))
      (g := fun z : ℝ => 1 + (2*z - z^2)/(2*(1-z)^2) - (1+2*z)/(1+z+z^2)) hu hcont hd hg
    have h0 : (0:ℝ) + 0^2/(2*(1-0)) - Real.log (1+0+0^2) = 0 := by simp
    rw [h0] at hmain
    linarith
  · -- (6) `z ≤ -log(1-z)`
    intro z hz hz1
    have h := Real.log_le_sub_one_of_pos (by linarith : (0:ℝ) < 1 - z)
    linarith

end Work.RHContract.Helper
