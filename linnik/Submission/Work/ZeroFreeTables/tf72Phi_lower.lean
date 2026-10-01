/-
# ZeroFreeTables — `tf72Phi_lower`

`tf72PhiLB y ≤ tf72Phi y` for `0 ≤ y`, i.e. the rational (degree-8 alternating Taylor)
lower approximant of the Laplace transform `tf72Phi y = (1/30)∫₀² e^{-ys}(2-s)³(4+6s+s²)ds`
of Heath-Brown's Lemma 7.2 test function really is a lower bound.

The proof is a single Taylor expansion of `e^{-ys}` in the second variable.  Writing

  `tf72Phi y = (1/30) ∫₀² e^{-ys} body(s) ds`,
  `tf72PhiLB y = (1/30) ( Σ_{m<9} (-y)^m M_m/m! - 2 y⁹ M₉/9! )`,  `M_m = ∫₀² s^m body(s) ds`,

we split the integral at the degree-8 Taylor polynomial `Σ_{m<9} (-ys)^m/m!` of the
Laplace kernel:

* the polynomial part integrates to `Σ_{m<9} (-y)^m M_m/m!` (`tf72_phi_sum_integral_aux`,
  using `tf72M_eq_integral`), and
* the remainder `e^{-ys} - Σ_{m<9}(-ys)^m/m!` is `-e^{-ξ}(ys)⁹/9! ≥ -(ys)⁹/9! ≥ -2y⁹s⁹/9!`
  by the Lagrange form of Taylor's theorem (`tf72_exp_taylor_lower_aux`), so its integral
  against the non-negative `body` is at least `-2y⁹M₉/9!` (`tf72_phi_rem_lower_aux`).

The factor `2` in `tf72PhiLB` is slack: the sharp bound `-y⁹M₉/9!` holds as well. -/
import Mathlib
import Submission.Work.ZeroFreeTables.tf72Phi_defs

noncomputable section
open scoped Real
open MeasureTheory

namespace Work.ZeroFreeTables

/-- Pointwise Taylor lower bound for `exp (-t)`: for `t ≥ 0` the degree-8 Taylor partial
sum of `e^{-t}` at `0` overshoots `e^{-t}` by at most `t⁹/9!`.

This is the Lagrange form of Taylor's theorem for `f u = e^{-u}` at `x₀ = 0`, `n = 8`,
`x = t`: for some `ξ ∈ (0,t)`,
`e^{-t} - Σ_{m<9} (-t)^m/m! = f^{(9)}(ξ) t⁹/9! = -e^{-ξ} t⁹/9! ≥ -t⁹/9!`. -/
theorem tf72_exp_taylor_lower_aux (t : ℝ) (ht : 0 ≤ t) :
    -(t ^ 9 / ((Nat.factorial 9 : ℕ) : ℝ)) ≤
      Real.exp (-t) - ∑ m ∈ Finset.range 9, (-t) ^ m / (m.factorial : ℝ) := by
  rcases eq_or_lt_of_le ht with h0 | ht
  · subst h0
    norm_num [Finset.sum_range_succ]
  · obtain ⟨x', hx', hrem⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
      (f := fun u : ℝ => Real.exp (-u)) (x := t) (x₀ := 0) (n := 8) (by linarith) (by fun_prop)
    have hderiv : iteratedDeriv 9 (fun u : ℝ => Real.exp (-u)) x' = -(Real.exp (-x')) := by
      have h1 : (fun u : ℝ => Real.exp (-u)) = (fun u : ℝ => Real.exp ((-1 : ℝ) * u)) := by
        funext u; congr 1; ring
      rw [h1, iteratedDeriv_exp_const_mul]
      norm_num
    rw [hderiv, sub_zero] at hrem
    have hsum : taylorWithinEval (fun u : ℝ => Real.exp (-u)) 8 (Set.uIcc 0 t) 0 t
        = ∑ m ∈ Finset.range 9, (-t) ^ m / (m.factorial : ℝ) := by
      rw [taylor_within_apply]
      refine Finset.sum_congr rfl ?_
      intro m hm
      have h0mem : (0:ℝ) ∈ Set.uIcc 0 t := by
        rw [Set.uIcc_of_le ht.le]; exact ⟨le_refl 0, ht.le⟩
      have hd : iteratedDerivWithin m (fun u : ℝ => Real.exp (-u)) (Set.uIcc 0 t) 0
          = (-1) ^ m := by
        rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc (by linarith : (0:ℝ) ≠ t))
          (by fun_prop) h0mem]
        have h1 : (fun u : ℝ => Real.exp (-u)) = (fun u : ℝ => Real.exp ((-1 : ℝ) * u)) := by
          funext u; congr 1; ring
        rw [h1, iteratedDeriv_exp_const_mul]
        norm_num
      rw [hd, smul_eq_mul]
      rw [sub_zero, mul_assoc, ← mul_pow, show t * (-1:ℝ) = -t by ring, div_eq_inv_mul]
    rw [hsum] at hrem
    have hx'nn : 0 ≤ x' := by
      have h1 : min (0:ℝ) t = 0 := min_eq_left ht.le
      linarith [hx'.1, h1]
    have hexp1 : Real.exp (-x') ≤ 1 := by
      rw [Real.exp_le_one_iff]; linarith
    have ht9 : 0 ≤ t ^ 9 := by positivity
    have h9 : (0:ℝ) < ((Nat.factorial 9 : ℕ) : ℝ) := by norm_num [Nat.factorial]
    rw [hrem]
    nlinarith [hexp1, ht9, h9, Real.exp_pos (-x')]

/-- The degree-8 Taylor polynomial of the Laplace kernel `e^{-ys}`,
`Σ_{m<9} (-ys)^m/m!`, integrates against `tf72Body` to the alternating moment sum
`Σ_{m<9} (-y)^m M_m/m!` with `M_m = ∫₀² s^m tf72Body = tf72M m`. -/
theorem tf72_phi_sum_integral_aux (y : ℝ) :
    (∫ s in (0:ℝ)..2, (∑ m ∈ Finset.range 9, (-(y * s)) ^ m / (m.factorial : ℝ)) * tf72Body s)
      = ∑ m ∈ Finset.range 9, (-y) ^ m * tf72M m / (m.factorial : ℝ) := by
  have hbody : Continuous tf72Body := by unfold tf72Body; fun_prop
  have h1 : (∫ s in (0:ℝ)..2,
        (∑ m ∈ Finset.range 9, (-(y * s)) ^ m / (m.factorial : ℝ)) * tf72Body s)
      = ∑ m ∈ Finset.range 9,
          ∫ s in (0:ℝ)..2, (-(y * s)) ^ m / (m.factorial : ℝ) * tf72Body s := by
    rw [show (fun s : ℝ => (∑ m ∈ Finset.range 9, (-(y * s)) ^ m / (m.factorial : ℝ))
            * tf72Body s)
        = (fun s : ℝ => ∑ m ∈ Finset.range 9,
            (-(y * s)) ^ m / (m.factorial : ℝ) * tf72Body s) from by
          funext s; rw [Finset.sum_mul]]
    exact intervalIntegral.integral_finsetSum (fun m _ =>
      ((by fun_prop : Continuous (fun s : ℝ => (-(y * s)) ^ m / (m.factorial : ℝ))).mul
        hbody).intervalIntegrable 0 2)
  rw [h1]
  refine Finset.sum_congr rfl ?_
  intro m hm
  have hpt : ∀ s : ℝ, (-(y * s)) ^ m / (m.factorial : ℝ) * tf72Body s
      = ((-y) ^ m / (m.factorial : ℝ)) * (s ^ m * tf72Body s) := by
    intro s
    rw [show -(y * s) = (-y) * s by ring, mul_pow]
    ring
  rw [intervalIntegral.integral_congr (fun s _ => hpt s), intervalIntegral.integral_const_mul,
      tf72M_eq_integral m]
  ring

/-- Lower bound for the integrated Taylor remainder: the degree-8 Taylor remainder of the
Laplace kernel `e^{-ys}`, integrated against `tf72Body` on `[0,2]`, is at least
`-2 y⁹ (∫₀² s⁹ tf72Body)/9! = -2y⁹M₉/9!` for `y ≥ 0`. -/
theorem tf72_phi_rem_lower_aux (y : ℝ) (hy0 : 0 ≤ y) :
    -(2 * y ^ 9 * tf72M 9 / ((Nat.factorial 9 : ℕ) : ℝ)) ≤
      ∫ s in (0:ℝ)..2,
        (Real.exp (-(y * s)) - ∑ m ∈ Finset.range 9, (-(y * s)) ^ m / (m.factorial : ℝ))
          * tf72Body s := by
  have hCpos : (0:ℝ) < ((Nat.factorial 9 : ℕ) : ℝ) := by norm_num [Nat.factorial]
  have hbody_cont : Continuous tf72Body := by unfold tf72Body; fun_prop
  have hG_cont : Continuous (fun s : ℝ =>
      (Real.exp (-(y * s)) - ∑ m ∈ Finset.range 9, (-(y * s)) ^ m / (m.factorial : ℝ))
        * tf72Body s) := by
    have h1 : Continuous (fun s : ℝ => Real.exp (-(y * s))) := by fun_prop
    have h2 : Continuous (fun s : ℝ =>
        ∑ m ∈ Finset.range 9, (-(y * s)) ^ m / (m.factorial : ℝ)) := by fun_prop
    exact (h1.sub h2).mul hbody_cont
  have hH_cont : Continuous (fun s : ℝ =>
      -(2 * y ^ 9 * s ^ 9 / ((Nat.factorial 9 : ℕ) : ℝ)) * tf72Body s) := by
    have h1 : Continuous (fun s : ℝ => -(2 * y ^ 9 * s ^ 9 / ((Nat.factorial 9 : ℕ) : ℝ))) := by
      fun_prop
    exact h1.mul hbody_cont
  have hpt : ∀ s ∈ Set.Icc (0:ℝ) 2,
      -(2 * y ^ 9 * s ^ 9 / ((Nat.factorial 9 : ℕ) : ℝ)) * tf72Body s
        ≤ (Real.exp (-(y * s)) - ∑ m ∈ Finset.range 9, (-(y * s)) ^ m / (m.factorial : ℝ))
            * tf72Body s := by
    intro s hs
    have hs0 : 0 ≤ s := hs.1
    have hbody : 0 ≤ tf72Body s := by
      unfold tf72Body
      have h1 : 0 ≤ (2 - s) ^ 3 := by
        have : 0 ≤ 2 - s := by linarith [hs.2]
        positivity
      have h2 : 0 ≤ 4 + 6 * s + s ^ 2 := by nlinarith [sq_nonneg (s + 3)]
      positivity
    have hA := tf72_exp_taylor_lower_aux (y * s) (mul_nonneg hy0 hs0)
    have hpow : (y * s) ^ 9 = y ^ 9 * s ^ 9 := by ring
    rw [hpow] at hA
    have hle : -(2 * y ^ 9 * s ^ 9 / ((Nat.factorial 9 : ℕ) : ℝ))
        ≤ -(y ^ 9 * s ^ 9 / ((Nat.factorial 9 : ℕ) : ℝ)) := by
      have hnn : 0 ≤ y ^ 9 * s ^ 9 / ((Nat.factorial 9 : ℕ) : ℝ) :=
        div_nonneg (mul_nonneg (pow_nonneg hy0 9) (pow_nonneg hs0 9)) hCpos.le
      linarith
    exact mul_le_mul_of_nonneg_right (le_trans hle hA) hbody
  have hmono := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume)
    (by norm_num : (0:ℝ) ≤ 2)
    (hH_cont.intervalIntegrable (μ := MeasureTheory.volume) 0 2)
    (hG_cont.intervalIntegrable (μ := MeasureTheory.volume) 0 2) hpt
  have hHcal : (∫ s in (0:ℝ)..2,
        -(2 * y ^ 9 * s ^ 9 / ((Nat.factorial 9 : ℕ) : ℝ)) * tf72Body s)
      = -(2 * y ^ 9 * tf72M 9 / ((Nat.factorial 9 : ℕ) : ℝ)) := by
    rw [show (fun s : ℝ => -(2 * y ^ 9 * s ^ 9 / ((Nat.factorial 9 : ℕ) : ℝ)) * tf72Body s)
        = (fun s : ℝ => (-(2 * y ^ 9 / ((Nat.factorial 9 : ℕ) : ℝ)))
            * (s ^ 9 * tf72Body s)) from by
          funext s; ring]
    rw [intervalIntegral.integral_const_mul, tf72M_eq_integral 9]
    ring
  rw [hHcal] at hmono
  linarith [hmono]

theorem tf72Phi_lower (y : ℝ) (hy0 : 0 ≤ y) (hy2 : y ≤ 2) :
    tf72PhiLB y ≤ tf72Phi y := by
  set S : ℝ := ∑ m ∈ Finset.range 9, (-y) ^ m * tf72M m / (m.factorial : ℝ) with hSdef
  set C : ℝ := ((Nat.factorial 9 : ℕ) : ℝ) with hCdef
  set B : ℝ := ∫ s in (0:ℝ)..2, Real.exp (-(y * s)) * tf72Body s with hBdef
  set J : ℝ := ∫ s in (0:ℝ)..2,
      (∑ m ∈ Finset.range 9, (-(y * s)) ^ m / (m.factorial : ℝ)) * tf72Body s with hJdef
  set R : ℝ := ∫ s in (0:ℝ)..2,
      (Real.exp (-(y * s)) - ∑ m ∈ Finset.range 9, (-(y * s)) ^ m / (m.factorial : ℝ))
        * tf72Body s with hRdef
  have hcbody : Continuous tf72Body := by unfold tf72Body; fun_prop
  have hcsum : Continuous (fun s : ℝ =>
      ∑ m ∈ Finset.range 9, (-(y * s)) ^ m / (m.factorial : ℝ)) := by fun_prop
  have hc1 : Continuous (fun s : ℝ =>
      (∑ m ∈ Finset.range 9, (-(y * s)) ^ m / (m.factorial : ℝ)) * tf72Body s) :=
    hcsum.mul hcbody
  have hc2 : Continuous (fun s : ℝ =>
      (Real.exp (-(y * s)) - ∑ m ∈ Finset.range 9, (-(y * s)) ^ m / (m.factorial : ℝ))
        * tf72Body s) :=
    ((by fun_prop : Continuous (fun s : ℝ => Real.exp (-(y * s)))).sub hcsum).mul hcbody
  have hsplit : B = J + R := by
    rw [hBdef, hJdef, hRdef,
      ← intervalIntegral.integral_add (hc1.intervalIntegrable 0 2) (hc2.intervalIntegrable 0 2)]
    apply intervalIntegral.integral_congr
    intro s _
    ring
  have hJS : J = S := by
    rw [hJdef, hSdef]
    exact tf72_phi_sum_integral_aux y
  have hRem : -(2 * y ^ 9 * tf72M 9 / C) ≤ R := by
    rw [hRdef, hCdef]
    exact tf72_phi_rem_lower_aux y hy0
  rw [tf72PhiLB, tf72Phi, ← hSdef, ← hCdef, ← hBdef]
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 1/30)
  rw [hsplit, hJS]
  linarith

end Work.ZeroFreeTables
