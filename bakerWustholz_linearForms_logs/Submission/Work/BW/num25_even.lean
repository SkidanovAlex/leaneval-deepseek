import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- For `u ≥ 0`, `log (1+u) ≤ u - u²/2 + u³/3` (three-term upper bound for the log series). -/
lemma log_one_add_le_cubic {u : ℝ} (hu : 0 ≤ u) :
    Real.log (1 + u) ≤ u - u^2/2 + u^3/3 := by
  have hderiv : ∀ x : ℝ, -1 < x →
      HasDerivAt (fun x : ℝ => x - x^2/2 + x^3/3 - Real.log (1 + x)) (x^3/(1+x)) x := by
    intro x hx
    have hx0 : (1:ℝ) + x ≠ 0 := by linarith
    have h1 : HasDerivAt (fun x : ℝ => x - x^2/2 + x^3/3) (1 - x + x^2) x := by
      have hx1 : HasDerivAt (fun x : ℝ => x) 1 x := hasDerivAt_id x
      have hx2 : HasDerivAt (fun x : ℝ => x^2) (2*x) x := by simpa using hasDerivAt_pow 2 x
      have hx3 : HasDerivAt (fun x : ℝ => x^3) (3*x^2) x := by simpa using hasDerivAt_pow 3 x
      have h := (hx1.sub (hx2.div_const 2)).add (hx3.div_const 3)
      convert h using 1 <;> ring
    have h2 : HasDerivAt (fun x : ℝ => Real.log (1 + x)) (1/(1+x)) x := by
      have hx' : HasDerivAt (fun x : ℝ => 1 + x) 1 x := by
        simpa using (hasDerivAt_id x).const_add 1
      have := hx'.log hx0
      convert this using 1 <;> ring
    have h := h1.sub h2
    have hv : (1 - x + x^2) - 1/(1+x) = x^3/(1+x) := by
      field_simp <;> ring_nf
    rw [hv] at h
    exact h
  have hmono : MonotoneOn (fun x : ℝ => x - x^2/2 + x^3/3 - Real.log (1 + x)) (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · apply ContinuousOn.sub
      · fun_prop
      · apply ContinuousOn.log _ _
        · fun_prop
        · intro x hx; simp only [Set.mem_Ici] at hx; linarith
    · rw [interior_Ici]
      intro x hx
      exact (hderiv x (by linarith [Set.mem_Ioi.mp hx])).differentiableAt.differentiableWithinAt
    · rw [interior_Ici]
      intro x hx
      have hx0 : 0 < x := hx
      rw [(hderiv x (by linarith)).deriv]
      positivity
  have h0 := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hu) hu
  simp only [Set.mem_Ici] at h0
  simp at h0
  linarith

/-- `4π/e² ≤ 2`, equivalently `2π ≤ e²`. -/
lemma base_ineq : 4*Real.pi/Real.exp 2 ≤ 2 := by
  rw [div_le_iff₀ (Real.exp_pos 2)]
  have he1 : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have he2 : Real.exp 2 = (Real.exp 1)^2 := by
    rw [show (2:ℝ) = 1 + 1 by norm_num, Real.exp_add]; ring
  have h7 : (7.29 : ℝ) < Real.exp 2 := by
    rw [he2]; nlinarith [he1, Real.exp_pos 1]
  nlinarith [Real.pi_lt_d2, h7]

/-- Induction step: `(2m+2)^{2m} ≤ (4m²-1)·(2m)^{2m-2}·e²` for `m ≥ 1`. -/
lemma core_ineq (m : ℕ) (hm : 1 ≤ m) :
    (2*(m:ℝ)+2)^(2*m) ≤ (4*(m:ℝ)^2 - 1)*(2*(m:ℝ))^(2*(m-1))*Real.exp 2 := by
  have hn1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have hmpos : (0:ℝ) < (m:ℝ) := by linarith
  have hcast2 : ((2*m : ℕ) : ℝ) = 2*(m:ℝ) := by push_cast; ring
  have h4 : (0:ℝ) < 4*(m:ℝ)^2 - 1 := by nlinarith [hn1, sq_nonneg ((m:ℝ)-1)]
  have h4ne : (4*(m:ℝ)^2 - 1) ≠ 0 := ne_of_gt h4
  have h1m : (0:ℝ) < 1 - 1/(4*(m:ℝ)^2) := by
    rw [sub_pos, div_lt_one (by positivity)]
    nlinarith [hn1, sq_nonneg ((m:ℝ)-1)]
  have hlog1 : Real.log (1 + (m:ℝ)⁻¹) ≤ (m:ℝ)⁻¹ - ((m:ℝ)⁻¹)^2/2 + ((m:ℝ)⁻¹)^3/3 :=
    log_one_add_le_cubic (by positivity)
  have hlog2 : -(1/(4*(m:ℝ)^2 - 1)) ≤ Real.log (1 - 1/(4*(m:ℝ)^2)) := by
    have h := Real.one_sub_inv_le_log_of_pos h1m
    have heq : (1:ℝ) - (1 - 1/(4*(m:ℝ)^2))⁻¹ = -(1/(4*(m:ℝ)^2 - 1)) := by
      field_simp <;> ring_nf
    rwa [heq] at h
  have hpoly : (1:ℝ)/(m:ℝ) - 2/(3*(m:ℝ)^2) ≥ 1/(4*(m:ℝ)^2 - 1) := by
    have hnum : (0:ℝ) ≤ 12*(m:ℝ)^3 - 11*(m:ℝ)^2 - 3*(m:ℝ) + 2 := by
      have hfac : 12*(m:ℝ)^3 - 11*(m:ℝ)^2 - 3*(m:ℝ) + 2
          = ((m:ℝ)-1)*(12*(m:ℝ)^2 + (m:ℝ) - 2) := by ring
      rw [hfac]
      apply mul_nonneg (by linarith)
      nlinarith [hn1]
    have h3m2 : (0:ℝ) < 3*(m:ℝ)^2 := by positivity
    have hL : (1:ℝ)/(m:ℝ) - 2/(3*(m:ℝ)^2) = (3*(m:ℝ) - 2)/(3*(m:ℝ)^2) := by
      field_simp <;> ring
    rw [ge_iff_le, hL, div_le_div_iff₀ h4 h3m2]
    nlinarith [hnum]
  have hkey : (2*(m:ℝ)) * Real.log (1 + (m:ℝ)⁻¹) ≤ 2 + Real.log (1 - 1/(4*(m:ℝ)^2)) := by
    have step1 : (2*(m:ℝ)) * Real.log (1 + (m:ℝ)⁻¹) ≤ 2 - 1/(m:ℝ) + 2/(3*(m:ℝ)^2) := by
      refine (mul_le_mul_of_nonneg_left hlog1 (by positivity)).trans (le_of_eq ?_)
      field_simp <;> ring_nf
    linarith [step1, hpoly, hlog2]
  have hcore : (1 + (m:ℝ)⁻¹)^(2*m) ≤ Real.exp 2 * (1 - 1/(4*(m:ℝ)^2)) := by
    have hA : (1 + (m:ℝ)⁻¹)^(2*m)
        = Real.exp ((2*(m:ℝ)) * Real.log (1 + (m:ℝ)⁻¹)) := by
      rw [← Real.exp_log (pow_pos (by positivity) _), Real.log_pow, hcast2]
    have hB : Real.exp 2 * (1 - 1/(4*(m:ℝ)^2))
        = Real.exp (2 + Real.log (1 - 1/(4*(m:ℝ)^2))) := by
      rw [Real.exp_add, Real.exp_log h1m]
    rw [hA, hB, Real.exp_le_exp]
    exact hkey
  calc (2*(m:ℝ)+2)^(2*m)
      = (2*(m:ℝ))^(2*m) * (1 + (m:ℝ)⁻¹)^(2*m) := by
        rw [← mul_pow]
        congr 1
        field_simp <;> ring_nf
    _ = (2*(m:ℝ))^(2*(m-1)) * (2*(m:ℝ))^2 * (1 + (m:ℝ)⁻¹)^(2*m) := by
        rw [show 2*m = 2*(m-1)+2 by omega, pow_add]
    _ ≤ (2*(m:ℝ))^(2*(m-1)) * (2*(m:ℝ))^2 * (Real.exp 2 * (1 - 1/(4*(m:ℝ)^2))) := by
        apply mul_le_mul_of_nonneg_left hcore
        positivity
    _ = (4*(m:ℝ)^2 - 1)*(2*(m:ℝ))^(2*(m-1))*Real.exp 2 := by
        field_simp <;> ring_nf

/-- Double-factorial growth used by BW (25): for `X = 2m`, `2·(2m−3)!!(2m−1)!! ≥ 4πX^{X−2}/e^X`,
checked numerically for all `m ≥ 1` (worst margin `e²/(2π) ≈ 1.176`, at `m = 1`; growing in `m`).
Notice `(2m−3)!!(2m−1)!! = ∏_{t=1}^{m−1}(4t²−1) = ∏_{t=0}^{m−2}((2t+1)(2t+3))`. -/
theorem num25_even (m : ℕ) (hm : 1 ≤ m) :
    4 * Real.pi * (2 * m : ℝ) ^ (2 * m - 2) / Real.exp (2 * m : ℝ)
      ≤ 2 * ∏ t ∈ Finset.range (m - 1), ((2 * (t : ℝ) + 1) * (2 * (t : ℝ) + 3)) := by
  have key : ∀ k : ℕ, 1 ≤ k →
      4 * Real.pi * (2*(k:ℝ))^(2*(k-1)) / Real.exp (2*(k:ℝ))
        ≤ 2 * ∏ t ∈ Finset.range (k - 1), ((2*(t:ℝ)+1)*(2*(t:ℝ)+3)) := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => simpa using base_ineq
    | succ n hn ih =>
      have hstep := core_ineq n hn
      have hsucc : (∏ t ∈ Finset.range n, ((2*(t:ℝ)+1)*(2*(t:ℝ)+3)))
          = (∏ t ∈ Finset.range (n - 1), ((2*(t:ℝ)+1)*(2*(t:ℝ)+3)))
            * ((2*((n-1:ℕ):ℝ)+1)*(2*((n-1:ℕ):ℝ)+3)) := by
        nth_rewrite 1 [show n = (n-1)+1 by omega]
        rw [Finset.prod_range_succ]
      have hc : ((n-1:ℕ):ℝ) = (n:ℝ) - 1 := by rw [Nat.cast_sub hn]; norm_num
      have hf : (2*((n-1:ℕ):ℝ)+1)*(2*((n-1:ℕ):ℝ)+3) = 4*(n:ℝ)^2 - 1 := by
        rw [hc]; ring
      have hRn : (2 * ∏ t ∈ Finset.range ((n+1) - 1), ((2*(t:ℝ)+1)*(2*(t:ℝ)+3)))
          = (2 * ∏ t ∈ Finset.range (n - 1), ((2*(t:ℝ)+1)*(2*(t:ℝ)+3))) * (4*(n:ℝ)^2 - 1) := by
        rw [show (n+1)-1 = n by omega, hsucc, hf]
        ring
      have hb : (0:ℝ) ≤ 4*(n:ℝ)^2 - 1 := by
        have h : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
        nlinarith [sq_nonneg ((n:ℝ) - 1), h]
      have hLstep : 4*Real.pi*(2*(n:ℝ)+2)^(2*n)/Real.exp (2*(n:ℝ)+2)
          ≤ (4*(n:ℝ)^2 - 1) * (4*Real.pi*(2*(n:ℝ))^(2*(n-1))/Real.exp (2*(n:ℝ))) := by
        have h1 : 4*Real.pi*(2*(n:ℝ)+2)^(2*n)/Real.exp (2*(n:ℝ)+2)
            ≤ 4*Real.pi*((4*(n:ℝ)^2-1)*(2*(n:ℝ))^(2*(n-1))*Real.exp 2)/Real.exp (2*(n:ℝ)+2) := by
          apply div_le_div_of_nonneg_right
          · exact mul_le_mul_of_nonneg_left hstep (by positivity)
          · exact (Real.exp_pos _).le
        refine h1.trans (le_of_eq ?_)
        rw [show (2*(n:ℝ)+2) = 2*(n:ℝ) + 2 by ring, Real.exp_add]
        field_simp
      have hcast : ((n+1:ℕ):ℝ) = (n:ℝ)+1 := by push_cast; ring
      have he : 2*((n+1)-1) = 2*n := by omega
      have hb2 : (2:ℝ)*((n:ℝ)+1) = 2*(n:ℝ)+2 := by ring
      have h2 : 4*Real.pi*(2*((n+1:ℕ):ℝ))^(2*((n+1)-1))/Real.exp (2*((n+1:ℕ):ℝ))
          = 4*Real.pi*(2*(n:ℝ)+2)^(2*n)/Real.exp (2*(n:ℝ)+2) := by
        rw [hcast, he, hb2]
      rw [h2, hRn]
      calc 4*Real.pi*(2*(n:ℝ)+2)^(2*n)/Real.exp (2*(n:ℝ)+2)
          ≤ (4*(n:ℝ)^2 - 1) * (4*Real.pi*(2*(n:ℝ))^(2*(n-1))/Real.exp (2*(n:ℝ))) := hLstep
        _ ≤ (4*(n:ℝ)^2 - 1) * (2 * ∏ t ∈ Finset.range (n - 1), ((2*(t:ℝ)+1)*(2*(t:ℝ)+3))) := by
              apply mul_le_mul_of_nonneg_left ih hb
        _ = (2 * ∏ t ∈ Finset.range (n - 1), ((2*(t:ℝ)+1)*(2*(t:ℝ)+3))) * (4*(n:ℝ)^2 - 1) := by ring
  have h2 : 2*m - 2 = 2*(m-1) := by omega
  rw [h2]
  exact key m hm

end Work.BW
