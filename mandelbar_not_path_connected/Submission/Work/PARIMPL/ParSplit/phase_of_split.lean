/-
Copyright: subproject `Submission/Work/PARIMPL/ParSplit/` of `mandelbar_not_path_connected`.

# `Work.PARIMPL.ParSplit.phase_of_split` — the phase conditions of the splitting

Hubbard–Schleicher, *Multicorns are not Path Connected*, §4: the two fixed points `m c ± E c/2`
of the second return map `F c = (T_c)^{10}` inside the dynamical disc split off the parabolic
point `z₁`, and the *phase* of the splitting is constrained: at a parameter where the
antiholomorphic square root `g c = (T_c)^{5}` **swaps** the two points, the quantity

`W c = 2 (m c - F c (m c)) / E c`

is almost purely imaginary; where `g c` **fixes** them, `W c` is almost real.  Quantitatively,
`7‖W‖ ≤ 8|Im W|` resp. `7‖W‖ ≤ 8|Re W|` on a small ball of parameters.

Mathematical content of the present module.

* `iteratedDeriv_poly_eval`, `poly_derivative_iterate_eval_zero`, `poly_coeff_norm_le`,
  `poly_taylor_norm_le`, `poly_eval_sub_eval_zero` — the Taylor/Cauchy toolkit for polynomials:
  the `n`-th derivative of a polynomial function at `0` is `n!` times the `n`-th coefficient,
  Cauchy's estimate gives `‖p.coeff n‖ ≤ C/σ^n`, and hence
  `‖p.eval w - p.eval 0‖ ≤ C‖w‖/(σ - ‖w‖)`.
* `polyF`, `Gshift` — `F c` as a polynomial function, and the shifted difference
  (`Gshift c m` is the *binary* version of the file `ParWall`'s *unary* `Gpoly`; the two are
  different objects, and the name clash between the two modules was resolved by calling this one
  `Gshift` — a file that needs both the wall data `ParWall` and the phase conditions must import
  both, which is only possible with distinct names)
  `G(t) = F c (m+t) - (m+t)` whose roots at `t = ±E/2` are the two split fixed points.
* `exists_factor_quadratic` — `G = (X² - w²)·ψ` when `G (±w) = 0` and `w ≠ 0`.
* `phase_of_split` — the phase conditions, from the second-order expansion of `G` around `0`
  and the multiplier relations coming from the antiholomorphic square root.
-/
import Mathlib
import Submission.Work.PARIMPL.ParSplit.Split
import Submission.Work.PARIMPL.ParSplit.exists_germ_quotient
import Submission.Work.PARIMPL.ParSplit.deriv_eq_normalForm
import Submission.Work.PARIMPL.ParSplit.deriv_conj_of_swap
import Submission.Work.PARIMPL.ParSplit.deriv_star_self_of_fix
import Submission.Work.PARIMPL.ParSplit.exists_uniform_bounds
import Submission.Work.PARIMPL.ParSplit.g_mem_of_split
import Submission.Work.PARIMPL.ParSplit.deriv_star_comp_sq
import Submission.Work.PARIMPL.ParSplit.continuous_localData

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedVariables false

open Classical Filter Set Metric
open scoped Topology

noncomputable section

namespace Work.PARIMPL.ParSplit

/-! ## The polynomial Taylor/Cauchy toolkit -/

/-- The `n`-th derivative of the polynomial function `z ↦ p.eval z` is the evaluation of the
`n`-th formal derivative. -/
theorem iteratedDeriv_poly_eval (p : Polynomial ℂ) (n : ℕ) (x : ℂ) :
    iteratedDeriv n (fun z => p.eval z) x = ((Polynomial.derivative^[n]) p).eval x := by
  have hfun : iteratedDeriv n (fun z => p.eval z) =
      fun y => ((Polynomial.derivative^[n]) p).eval y := by
    induction n with
    | zero => funext x; simp
    | succ n ih =>
      funext x
      rw [iteratedDeriv_succ, ih, Polynomial.deriv]
      rw [Function.iterate_succ_apply']
  exact congrFun hfun x

/-- The `n`-th coefficient of a polynomial is the `n`-th derivative of its polynomial function
at `0`, divided by `n!`. -/
theorem poly_derivative_iterate_eval_zero (p : Polynomial ℂ) (n : ℕ) :
    ((Polynomial.derivative^[n]) p).eval 0 = (n.factorial : ℂ) * p.coeff n := by
  rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_iterate_derivative]
  simp [Nat.descFactorial_self, nsmul_eq_mul]

/-- **Cauchy's estimate for the coefficients of a polynomial**: if `‖p‖ ≤ C` on the circle of
radius `σ > 0` around `0`, then `‖p.coeff n‖ ≤ C/σ^n`. -/
theorem poly_coeff_norm_le (p : Polynomial ℂ) {σ C : ℝ} (hσ : 0 < σ)
    (hC : ∀ z : ℂ, ‖z‖ = σ → ‖p.eval z‖ ≤ C) (n : ℕ) :
    ‖p.coeff n‖ ≤ C / σ ^ n := by
  have hdiff : DiffContOnCl ℂ (fun z => p.eval z) (Metric.ball 0 σ) :=
    (Polynomial.differentiable p).diffContOnCl
  have hbound : ∀ z ∈ Metric.sphere (0:ℂ) σ, ‖(fun z => p.eval z) z‖ ≤ C := by
    intro z hz
    rw [Metric.mem_sphere, dist_zero_right] at hz
    exact hC z hz
  have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hσ hdiff hbound
  have hfac : (0:ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hcoeff : p.coeff n = iteratedDeriv n (fun z => p.eval z) 0 / (n.factorial : ℂ) := by
    rw [iteratedDeriv_poly_eval, poly_derivative_iterate_eval_zero]
    rw [show (n.factorial : ℂ) * p.coeff n = p.coeff n * (n.factorial : ℂ) by ring]
    exact (mul_div_cancel_right₀ _ (by exact_mod_cast Nat.factorial_ne_zero n)).symm
  rw [hcoeff, norm_div, Complex.norm_natCast, div_le_iff₀ hfac]
  calc ‖iteratedDeriv n (fun z => p.eval z) 0‖ ≤ (n.factorial : ℝ) * C / σ ^ n := hcauchy
    _ = C / σ ^ n * (n.factorial : ℝ) := by ring

/-- The geometric series bound `∑_{i<N} r^i ≤ 1/(1-r)` for `0 ≤ r < 1`. -/
theorem geom_sum_range_le {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) (N : ℕ) :
    ∑ i ∈ Finset.range N, r ^ i ≤ 1 / (1 - r) := by
  have hpos : 0 < 1 - r := by linarith
  rw [le_div_iff₀ hpos]
  have h := geom_sum_mul r N
  have h2 : (∑ i ∈ Finset.range N, r ^ i) * (1 - r) = 1 - r^N := by
    have : (1 - r) = -(r - 1) := by ring
    rw [this, mul_neg, h]; ring
  have hrN : 0 ≤ r^N := pow_nonneg h0 N
  nlinarith [h2, hrN]

/-- The value of a polynomial minus its value at `0` is the sum of the non-constant terms. -/
theorem poly_eval_sub_eval_zero (p : Polynomial ℂ) (w : ℂ) :
    p.eval w - p.eval 0 = ∑ i ∈ Finset.range p.natDegree, p.coeff (i+1) * w^(i+1) := by
  rw [Polynomial.eval_eq_sum_range, Finset.sum_range_succ']
  rw [← Polynomial.coeff_zero_eq_eval_zero]
  simp only [pow_zero, mul_one]
  ring

/-- **Taylor's bound for a polynomial**: if `‖p‖ ≤ C` on the circle of radius `σ > 0` around
`0`, then `‖p.eval w - p.eval 0‖ ≤ C‖w‖/(σ - ‖w‖)` for `‖w‖ < σ`. -/
theorem poly_taylor_norm_le (p : Polynomial ℂ) {σ C : ℝ} (hσ : 0 < σ) (hC0 : 0 ≤ C)
    (hC : ∀ z : ℂ, ‖z‖ = σ → ‖p.eval z‖ ≤ C) {w : ℂ} (hw : ‖w‖ < σ) :
    ‖p.eval w - p.eval 0‖ ≤ C * ‖w‖ / (σ - ‖w‖) := by
  have hw0 : 0 ≤ ‖w‖ := norm_nonneg w
  have hσpos : 0 < σ - ‖w‖ := by linarith
  set r := ‖w‖ / σ with hr
  have hr0 : 0 ≤ r := div_nonneg hw0 hσ.le
  have hr1 : r < 1 := by rw [hr]; rw [div_lt_one hσ]; exact hw
  rw [poly_eval_sub_eval_zero]
  calc ‖∑ i ∈ Finset.range p.natDegree, p.coeff (i+1) * w^(i+1)‖
      ≤ ∑ i ∈ Finset.range p.natDegree, ‖p.coeff (i+1) * w^(i+1)‖ := norm_sum_le _ _
    _ = ∑ i ∈ Finset.range p.natDegree, ‖p.coeff (i+1)‖ * ‖w‖^(i+1) := by
        apply Finset.sum_congr rfl; intro i _; rw [norm_mul, norm_pow]
    _ ≤ ∑ i ∈ Finset.range p.natDegree, (C / σ^(i+1)) * ‖w‖^(i+1) := by
        apply Finset.sum_le_sum; intro i _
        exact mul_le_mul_of_nonneg_right (poly_coeff_norm_le p hσ hC (i+1)) (by positivity)
    _ = ∑ i ∈ Finset.range p.natDegree, C * r^(i+1) := by
        apply Finset.sum_congr rfl; intro i _
        rw [hr, div_pow]
        field_simp
    _ = C * ∑ i ∈ Finset.range p.natDegree, r^(i+1) := by rw [Finset.mul_sum]
    _ = C * (r * ∑ i ∈ Finset.range p.natDegree, r^i) := by
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro i _; rw [pow_succ]; ring
    _ ≤ C * (r * (1/(1-r))) := by
        apply mul_le_mul_of_nonneg_left _ hC0
        exact mul_le_mul_of_nonneg_left (geom_sum_range_le hr0 hr1 _) hr0
    _ = C * ‖w‖ / (σ - ‖w‖) := by
        rw [hr]
        field_simp

/-- **The quadratic factor of a polynomial with two symmetric roots**: if `G w = G (-w) = 0`
and `w ≠ 0`, then `X² - w²` divides `G`. -/
theorem exists_factor_quadratic (G : Polynomial ℂ) {w : ℂ} (hw : w ≠ 0)
    (h1 : G.eval w = 0) (h2 : G.eval (-w) = 0) :
    ∃ ψ : Polynomial ℂ, G = (Polynomial.X^2 - Polynomial.C (w^2)) * ψ := by
  obtain ⟨ψ1, hψ1⟩ := Polynomial.dvd_iff_isRoot.mpr h1
  have hψ1eval : ψ1.eval (-w) = 0 := by
    have := congrArg (fun p : Polynomial ℂ => p.eval (-w)) hψ1
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
      at this
    rw [h2] at this
    have hne : (-w) - w ≠ 0 := by
      intro hc; apply hw; linear_combination (-1/2 : ℂ) * hc
    exact (mul_eq_zero.mp this.symm).resolve_left hne
  obtain ⟨ψ, hψ⟩ := Polynomial.dvd_iff_isRoot.mpr hψ1eval
  refine ⟨ψ, ?_⟩
  rw [hψ1, hψ]
  have : Polynomial.C (-w) = -Polynomial.C w := by simp
  rw [show Polynomial.X - Polynomial.C (-w) = Polynomial.X + Polynomial.C w by rw [this]; ring]
  rw [Polynomial.C_pow]
  ring

/-- The second coefficient of `(X² - w²)·ψ`. -/
theorem coeff_two_factor (ψ : Polynomial ℂ) (w : ℂ) :
    ((Polynomial.X^2 - Polynomial.C (w^2)) * ψ).coeff 2 = ψ.coeff 0 - w^2 * ψ.coeff 2 := by
  rw [sub_mul, Polynomial.coeff_sub, Polynomial.coeff_C_mul]
  congr 1
  rw [Polynomial.coeff_mul]
  norm_num [Finset.HasAntidiagonal.antidiagonal, Polynomial.coeff_X_pow]

/-! ## `F c` as a polynomial function -/

/-- The `n`-fold composition of a polynomial with itself. -/
noncomputable def compIter (q : Polynomial ℂ) : ℕ → Polynomial ℂ
  | 0 => Polynomial.X
  | n + 1 => (compIter q n).comp q

theorem compIter_eval (q : Polynomial ℂ) (n : ℕ) (z : ℂ) :
    (compIter q n).eval z = (fun w => q.eval w)^[n] z := by
  induction n generalizing z with
  | zero => simp [compIter]
  | succ n ih =>
      simp only [compIter, Polynomial.eval_comp, ih]
      exact (Function.iterate_succ_apply (fun w => q.eval w) n z).symm

theorem Tsq_poly_eval (c z : ℂ) :
    ((Polynomial.X^2 + Polynomial.C (star c))^2 + Polynomial.C c).eval z =
      Work.Landing.Tsq c z := by
  simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
  rfl

/-- The polynomial whose value at `z` is `Work.EL.F c z`. -/
noncomputable def polyF (c : ℂ) : Polynomial ℂ :=
  compIter ((Polynomial.X^2 + Polynomial.C (star c))^2 + Polynomial.C c) 5

theorem polyF_eval (c z : ℂ) : (polyF c).eval z = Work.EL.F c z := by
  rw [polyF, compIter_eval]
  have hQ : (fun w => ((Polynomial.X^2 + Polynomial.C (star c))^2 + Polynomial.C c).eval w)
      = Work.Landing.Tsq c := funext (Tsq_poly_eval c)
  rw [hQ]
  rfl

/-- The shifted difference `t ↦ F c (m+t) - (m+t)` as a polynomial. -/
noncomputable def Gshift (c m : ℂ) : Polynomial ℂ :=
  (polyF c).comp (Polynomial.X + Polynomial.C m) - (Polynomial.X + Polynomial.C m)

theorem Gshift_eval (c m t : ℂ) :
    (Gshift c m).eval t = Work.EL.F c (m + t) - (m + t) := by
  simp only [Gshift, Polynomial.eval_sub, Polynomial.eval_comp, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_C]
  rw [polyF_eval, add_comm t m]

theorem differentiable_F (c : ℂ) : Differentiable ℂ (Work.EL.F c) := by
  rw [show Work.EL.F c = fun z => (polyF c).eval z
      from funext (fun z => (polyF_eval c z).symm)]
  exact Polynomial.differentiable (polyF c)

/-- The derivative of `F c` at `m + w` in terms of the polynomial `Gshift c m`. -/
theorem deriv_Fm (c m w : ℂ) :
    deriv (Work.EL.F c) (m + w) = (Gshift c m).derivative.eval w + 1 := by
  have h1 : deriv (fun t : ℂ => (Gshift c m).eval t) w = (Gshift c m).derivative.eval w :=
    Polynomial.deriv _
  have h2 : (fun t : ℂ => (Gshift c m).eval t) =
      fun t : ℂ => Work.EL.F c (m + t) - (m + t) :=
    funext (Gshift_eval c m)
  have h3 : deriv (fun t : ℂ => Work.EL.F c (m + t) - (m + t)) w =
      deriv (Work.EL.F c) (m + w) - 1 := by
    have hA : HasDerivAt (fun t : ℂ => Work.EL.F c (m + t)) (deriv (Work.EL.F c) (m + w)) w := by
      have h1 : HasDerivAt (fun t : ℂ => m + t) 1 w := by
        simpa using (hasDerivAt_id w).const_add m
      have h2 : HasDerivAt (Work.EL.F c) (deriv (Work.EL.F c) (m + w)) (m + w) :=
        (differentiable_F c).differentiableAt.hasDerivAt
      simpa [Function.comp_def] using h2.comp w h1
    have hB : HasDerivAt (fun t : ℂ => (m + t)) 1 w := by
      simpa using (hasDerivAt_id w).const_add m
    have hsub := hA.sub hB
    have : (fun t : ℂ => Work.EL.F c (m + t) - (m + t))
        = (fun t : ℂ => Work.EL.F c (m + t)) - (fun t : ℂ => m + t) := by
      funext t; simp
    rw [this]
    exact hsub.deriv
  rw [h2, h3] at h1
  exact eq_add_of_sub_eq h1

theorem poly_phase_core (G ψ : Polynomial ℂ) {w : ℂ} {ρ K : ℝ}
    (hρ : 0 < ρ) (hK : 0 ≤ K) (hw0 : w ≠ 0) (hw : 2 * ‖w‖ ≤ ρ)
    (hfac : ∀ z : ℂ, G.eval z = (z^2 - w^2) * ψ.eval z)
    (hbound : ∀ z : ℂ, ‖z‖ = ρ → ‖G.eval z‖ ≤ K) :
    ‖G.derivative.eval w + 2 * (G.eval 0) / w‖ ≤ 6 * K * ‖w‖^2 / ρ^3 ∧
      ‖G.derivative.eval (-w) - 2 * (G.eval 0) / w‖ ≤ 6 * K * ‖w‖^2 / ρ^3 ∧
      ‖ψ.eval 0 - G.coeff 2‖ ≤ 2 * K * ‖w‖^2 / ρ^4 := by
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  have hwnn : 0 ≤ ‖w‖ := norm_nonneg w
  have hρw : ‖w‖ ≤ ρ / 2 := by linarith
  have hρw2pos : 0 < ρ - ‖w‖ := by linarith
  have hden_pos : 0 < ρ^2 - ‖w‖^2 := by nlinarith
  set C : ℝ := K / (ρ^2 - ‖w‖^2) with hCdef
  have hCnn : 0 ≤ C := by rw [hCdef]; positivity
  -- the sup bound for ψ on the circle of radius ρ
  have hpsi_bound : ∀ z : ℂ, ‖z‖ = ρ → ‖ψ.eval z‖ ≤ C := by
    intro z hz
    have hne : z^2 - w^2 ≠ 0 := by
      intro hc
      have hzw : ρ^2 = ‖w‖^2 := by
        have h1 : z^2 = w^2 := by linear_combination hc
        have h2 : ‖z^2‖ = ‖w^2‖ := by rw [h1]
        rw [norm_pow, norm_pow, hz] at h2
        exact h2
      nlinarith [hzw, hw, hρ, hwpos]
    have hdiv : ψ.eval z = G.eval z / (z^2 - w^2) := by
      rw [hfac z]; field_simp
    have hlow : ρ^2 - ‖w‖^2 ≤ ‖z^2 - w^2‖ := by
      have h1 : |‖z^2‖ - ‖w^2‖| ≤ ‖z^2 - w^2‖ := abs_norm_sub_norm_le _ _
      rw [norm_pow, norm_pow, hz] at h1
      have h2 : |ρ^2 - ‖w‖^2| = ρ^2 - ‖w‖^2 := abs_of_nonneg (le_of_lt hden_pos)
      rwa [h2] at h1
    have hCmul : C * (ρ^2 - ‖w‖^2) = K := by
      rw [hCdef]; field_simp
    rw [hdiv, norm_div, div_le_iff₀ (norm_pos_iff.mpr hne)]
    calc ‖G.eval z‖ ≤ K := hbound z hz
      _ = C * (ρ^2 - ‖w‖^2) := hCmul.symm
      _ ≤ C * ‖z^2 - w^2‖ := mul_le_mul_of_nonneg_left hlow hCnn
  have hCbound : C ≤ 4 * K / (3 * ρ^2) := by
    rw [hCdef, div_le_div_iff₀ hden_pos (by positivity)]
    have h1 : 4 * ‖w‖^2 ≤ ρ^2 := by nlinarith [hwnn, hρw, hρ]
    nlinarith [hK, h1, sq_nonneg ρ]
  have hCbound' : 3 * (C * ρ^2) ≤ 4 * K := by
    have h := hCbound
    rw [le_div_iff₀ (by positivity : (0:ℝ) < 3 * ρ^2)] at h
    nlinarith [h]
  -- Taylor difference for ψ
  have hpsi_taylor : ‖ψ.eval w - ψ.eval 0‖ ≤ C * ‖w‖ / (ρ - ‖w‖) :=
    poly_taylor_norm_le ψ hρ hCnn hpsi_bound (w := w) (by linarith)
  have hpsi_taylor_neg : ‖ψ.eval (-w) - ψ.eval 0‖ ≤ C * ‖w‖ / (ρ - ‖w‖) := by
    have h := poly_taylor_norm_le ψ hρ hCnn hpsi_bound (w := -w) (by rw [norm_neg]; linarith)
    rwa [norm_neg] at h
  -- derivative relations
  have hderiv_w : G.derivative.eval w = 2 * w * ψ.eval w := by
    rw [show G.derivative.eval w = deriv (fun z => G.eval z) w from (Polynomial.deriv G).symm]
    rw [show (fun z => G.eval z) = fun z => (z^2 - w^2) * ψ.eval z from funext hfac]
    have hd := ((hasDerivAt_pow 2 w).sub_const (w^2)).mul
      ((Polynomial.differentiable ψ).differentiableAt.hasDerivAt)
    have hfun : (fun z : ℂ => (z^2 - w^2) * ψ.eval z)
        = (fun x => x^2 - w^2) * (fun x => ψ.eval x) := by funext z; rfl
    rw [hfun, hd.deriv]; ring
  have hderiv_nw : G.derivative.eval (-w) = -2 * w * ψ.eval (-w) := by
    rw [show G.derivative.eval (-w) = deriv (fun z => G.eval z) (-w) from (Polynomial.deriv G).symm]
    rw [show (fun z => G.eval z) = fun z => (z^2 - w^2) * ψ.eval z from funext hfac]
    have hd := ((hasDerivAt_pow 2 (-w)).sub_const (w^2)).mul
      ((Polynomial.differentiable ψ).differentiableAt.hasDerivAt)
    have hfun : (fun z : ℂ => (z^2 - w^2) * ψ.eval z)
        = (fun x => x^2 - w^2) * (fun x => ψ.eval x) := by funext z; rfl
    rw [hfun, hd.deriv]; ring
  have hG0 : G.eval 0 = -(w^2) * ψ.eval 0 := by simpa using hfac 0
  have hfirst : G.derivative.eval w + 2 * (G.eval 0) / w = 2 * w * (ψ.eval w - ψ.eval 0) := by
    rw [hderiv_w, hG0]; field_simp; ring
  have hsecond : G.derivative.eval (-w) - 2 * (G.eval 0) / w = 2 * w * (ψ.eval 0 - ψ.eval (-w)) := by
    rw [hderiv_nw, hG0]; field_simp; ring
  have hpoly : G = (Polynomial.X^2 - Polynomial.C (w^2)) * ψ := by
    apply Polynomial.funext
    intro z
    rw [hfac z]
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C]
  have hthird : ψ.eval 0 - G.coeff 2 = w^2 * ψ.coeff 2 := by
    have h := coeff_two_factor ψ w
    rw [← hpoly] at h
    rw [Polynomial.coeff_zero_eq_eval_zero] at h
    rw [h]; ring
  have hkey : 2 * ‖w‖ * (C * ‖w‖ / (ρ - ‖w‖)) ≤ 6 * K * ‖w‖^2 / ρ^3 := by
    have h2 : C * ‖w‖ / (ρ - ‖w‖) ≤ 2 * C * ‖w‖ / ρ := by
      rw [div_le_div_iff₀ hρw2pos hρ]
      nlinarith [mul_nonneg (mul_nonneg hCnn hwnn) (by linarith : (0:ℝ) ≤ ρ - 2 * ‖w‖)]
    have h4 : 2 * ‖w‖ * (2 * C * ‖w‖ / ρ) ≤ 6 * K * ‖w‖^2 / ρ^3 := by
      have heq : 2 * ‖w‖ * (2 * C * ‖w‖ / ρ) = 4 * C * ‖w‖^2 / ρ := by ring
      rw [heq, div_le_div_iff₀ hρ (pow_pos hρ 3)]
      have h6 : 0 ≤ (‖w‖^2) * ρ * (6 * K - 4 * (C * ρ^2)) :=
        mul_nonneg (mul_nonneg (sq_nonneg ‖w‖) hρ.le) (by nlinarith [hCbound', hK])
      nlinarith [h6]
    calc 2 * ‖w‖ * (C * ‖w‖ / (ρ - ‖w‖)) ≤ 2 * ‖w‖ * (2 * C * ‖w‖ / ρ) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ 6 * K * ‖w‖^2 / ρ^3 := h4
  refine ⟨?_, ?_, ?_⟩
  · have : ‖2 * w * (ψ.eval w - ψ.eval 0)‖ = 2 * ‖w‖ * ‖ψ.eval w - ψ.eval 0‖ := by
      rw [norm_mul, norm_mul, Complex.norm_ofNat]
    rw [hfirst, this]
    calc 2 * ‖w‖ * ‖ψ.eval w - ψ.eval 0‖ ≤ 2 * ‖w‖ * (C * ‖w‖ / (ρ - ‖w‖)) :=
          mul_le_mul_of_nonneg_left hpsi_taylor (by positivity)
      _ ≤ 6 * K * ‖w‖^2 / ρ^3 := hkey
  · have : ‖2 * w * (ψ.eval 0 - ψ.eval (-w))‖ = 2 * ‖w‖ * ‖ψ.eval 0 - ψ.eval (-w)‖ := by
      rw [norm_mul, norm_mul, Complex.norm_ofNat]
    rw [hsecond, this]
    have hneg : ‖ψ.eval 0 - ψ.eval (-w)‖ ≤ C * ‖w‖ / (ρ - ‖w‖) := by
      rw [← neg_sub, norm_neg]; exact hpsi_taylor_neg
    calc 2 * ‖w‖ * ‖ψ.eval 0 - ψ.eval (-w)‖ ≤ 2 * ‖w‖ * (C * ‖w‖ / (ρ - ‖w‖)) :=
          mul_le_mul_of_nonneg_left hneg (by positivity)
      _ ≤ 6 * K * ‖w‖^2 / ρ^3 := hkey
  · rw [hthird]
    have : ‖w^2 * ψ.coeff 2‖ = ‖w‖^2 * ‖ψ.coeff 2‖ := by rw [norm_mul, norm_pow]
    rw [this]
    have hc := poly_coeff_norm_le ψ hρ hpsi_bound 2
    calc ‖w‖^2 * ‖ψ.coeff 2‖ ≤ ‖w‖^2 * (C / ρ^2) :=
          mul_le_mul_of_nonneg_left hc (sq_nonneg ‖w‖)
      _ ≤ 2 * K * ‖w‖^2 / ρ^4 := by
          have heq : ‖w‖^2 * (C / ρ^2) = C * ‖w‖^2 / ρ^2 := by ring
          rw [heq, div_le_div_iff₀ (by positivity) (pow_pos hρ 4)]
          have h2' : 0 ≤ ‖w‖^2 * (2 * K - C * ρ^2) :=
            mul_nonneg (sq_nonneg ‖w‖) (by nlinarith [hCbound', hK])
          nlinarith [h2']

open LeanEval.ComplexAnalysis (Tantibar)

theorem star_gtc_eq (c z : ℂ) :
    star (gtc c z) = ((Work.Landing.Tsq c)^[2] z)^2 + star c := by
  have h4 : (Tantibar c)^[4] = (Work.Landing.Tsq c)^[2] := by
    rw [show (4:ℕ) = 2 * 2 from rfl, Function.iterate_mul, ← Work.EL.Tsq_eq_comp]
  calc star (gtc c z) = star (Tantibar c ((Tantibar c)^[4] z)) := by
        rw [gtc, show (5:ℕ) = 4 + 1 from rfl, Function.iterate_succ_apply']
    _ = ((Tantibar c)^[4] z)^2 + star c := by
        simp only [Tantibar, star_add, star_pow, starRingEnd_apply, star_star]
    _ = ((Work.Landing.Tsq c)^[2] z)^2 + star c := by rw [h4]

theorem differentiable_gtc_star (c : ℂ) : Differentiable ℂ (fun z => star (gtc c z)) := by
  rw [show (fun z => star (gtc c z)) = fun z => ((Work.Landing.Tsq c)^[2] z)^2 + star c
      from funext (star_gtc_eq c)]
  have h1 : Differentiable ℂ (Work.Landing.Tsq c) := by
    have : Work.Landing.Tsq c
        = fun z => Polynomial.eval z ((Polynomial.X^2 + Polynomial.C (star c))^2 + Polynomial.C c) :=
      funext (fun z => (Tsq_poly_eval c z).symm)
    rw [this]; exact Polynomial.differentiable _
  exact ((h1.iterate 2).pow 2).add_const _

theorem deriv_gtc_star (c z : ℂ) :
    deriv (fun x => star (gtc c x)) z
      = 2 * ((Work.Landing.Tsq c)^[2] z) * deriv ((Work.Landing.Tsq c)^[2]) z := by
  rw [show (fun x => star (gtc c x)) = fun x => ((Work.Landing.Tsq c)^[2] x)^2 + star c
      from funext (star_gtc_eq c)]
  have h1 : Differentiable ℂ (Work.Landing.Tsq c) := by
    have : Work.Landing.Tsq c
        = fun z => Polynomial.eval z ((Polynomial.X^2 + Polynomial.C (star c))^2 + Polynomial.C c) :=
      funext (fun z => (Tsq_poly_eval c z).symm)
    rw [this]; exact Polynomial.differentiable _
  have hbase : HasDerivAt ((Work.Landing.Tsq c)^[2]) (deriv ((Work.Landing.Tsq c)^[2]) z) z :=
    ((h1.iterate 2).differentiableAt).hasDerivAt
  have hpow : HasDerivAt (fun x : ℂ => ((Work.Landing.Tsq c)^[2] x)^2)
      (2 * ((Work.Landing.Tsq c)^[2] z) * deriv ((Work.Landing.Tsq c)^[2]) z) z := by
    convert hbase.pow 2 using 2 <;> ring
  rw [(hpow.add_const (star c)).deriv]

theorem deriv_F_gtc (c z : ℂ) :
    deriv (Work.EL.F c) z
      = deriv (fun x => star (gtc c x)) z * star (deriv (fun x => star (gtc c x)) (gtc c z)) := by
  have hF : Work.EL.F c
      = fun x => star ((fun y => star (gtc c y)) (star ((fun y => star (gtc c y)) x))) := by
    rw [show Work.EL.F c = gtc c ∘ gtc c from Ft_eq_g_comp c]
    funext x
    simp only [Function.comp_apply, star_star]
  rw [hF, deriv_star_comp_sq (differentiable_gtc_star c) z]
  simp only [star_star]

theorem deriv_F_of_gtc_swap {c u v : ℂ} (h1 : gtc c u = v) (h2 : gtc c v = u) :
    deriv (Work.EL.F c) u = star (deriv (Work.EL.F c) v) := by
  rw [deriv_F_gtc c u, deriv_F_gtc c v, h1, h2, star_mul, star_star]

theorem deriv_F_of_gtc_fix {c u : ℂ} (h : gtc c u = u) :
    ∃ r : ℝ, 0 ≤ r ∧ deriv (Work.EL.F c) u = (r : ℂ) := by
  refine ⟨‖deriv (fun x => star (gtc c x)) u‖^2, sq_nonneg _, ?_⟩
  rw [deriv_F_gtc c u, h]
  have hc : deriv (fun x => star (gtc c x)) u * star (deriv (fun x => star (gtc c x)) u)
      = ((Complex.normSq (deriv (fun x => star (gtc c x)) u) : ℝ) : ℂ) := by
    simpa only [starRingEnd_apply] using Complex.mul_conj (deriv (fun x => star (gtc c x)) u)
  rw [hc, Complex.normSq_eq_norm_sq]

theorem Gshift_coeff_two (c m : ℂ) :
    (Gshift c m).coeff 2 = iteratedDeriv 2 (Work.EL.F c) m / 2 := by
  have h1 : ((Polynomial.derivative^[2]) (Gshift c m)).eval 0 = 2 * (Gshift c m).coeff 2 := by
    simpa using poly_derivative_iterate_eval_zero (Gshift c m) 2
  have h2 : iteratedDeriv 2 (fun z => (Gshift c m).eval z) 0
      = ((Polynomial.derivative^[2]) (Gshift c m)).eval 0 := iteratedDeriv_poly_eval _ 2 0
  have h3 : iteratedDeriv 2 (fun z => (Gshift c m).eval z) 0
      = iteratedDeriv 2 (Work.EL.F c) m := by
    have hfun : (fun z => (Gshift c m).eval z)
        = fun z => Work.EL.F c (m + z) - (m + z) := funext (Gshift_eval c m)
    rw [hfun]
    rw [iteratedDeriv_fun_sub]
    · rw [iteratedDeriv_comp_const_add 2 (Work.EL.F c) m]
      have hz : iteratedDeriv 2 (fun z : ℂ => m + z) 0 = 0 := by
        rw [show (fun z : ℂ => m + z) = fun z => m + id z from rfl,
            iteratedDeriv_const_add (by norm_num : (0:ℕ) < 2), iteratedDeriv_id]
        norm_num
      simp [hz]
    · exact (differentiable_F c).contDiff.contDiffAt.comp 0 (by fun_prop)
    · fun_prop
  have hkey : 2 * (Gshift c m).coeff 2 = iteratedDeriv 2 (Work.EL.F c) m := by
    rw [← h1, ← h2, h3]
  rw [← hkey]; ring

theorem phase_abs_le_of_re (W : ℂ) (h : |W.re| ≤ 15/32 * ‖W‖) : 7 * ‖W‖ ≤ 8 * |W.im| := by
  have hnorm2 : ‖W‖^2 = W.re^2 + W.im^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have h2 : W.re^2 ≤ (15/32)^2 * ‖W‖^2 := by
    nlinarith [h, sq_abs W.re, abs_nonneg W.re, norm_nonneg W, sq_nonneg ‖W‖]
  have h1 : (7 * ‖W‖)^2 ≤ (8 * |W.im|)^2 := by
    rw [mul_pow, mul_pow, sq_abs]
    nlinarith [hnorm2, h2, sq_nonneg W.im, norm_nonneg W]
  have := sq_le_sq.mp h1
  rwa [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)] at this

theorem phase_abs_le_of_im (W : ℂ) (h : |W.im| ≤ 15/32 * ‖W‖) : 7 * ‖W‖ ≤ 8 * |W.re| := by
  have hnorm2 : ‖W‖^2 = W.re^2 + W.im^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have h2 : W.im^2 ≤ (15/32)^2 * ‖W‖^2 := by
    nlinarith [h, sq_abs W.im, abs_nonneg W.im, norm_nonneg W, sq_nonneg ‖W‖]
  have h1 : (7 * ‖W‖)^2 ≤ (8 * |W.re|)^2 := by
    rw [mul_pow, mul_pow, sq_abs]
    nlinarith [hnorm2, h2, sq_nonneg W.re, norm_nonneg W]
  have := sq_le_sq.mp h1
  rwa [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)] at this

theorem phase_local {c₀ : ℂ} {d : Work.EL.RootParabolic c₀} (S : SplitData d) {c : ℂ} {σ K γ : ℝ}
    (hσ : 0 < σ) (hK : 0 ≤ K) (hγ : 0 < γ)
    (hS : c ∈ ball c₀ S.ρ) (hE : S.E c ≠ 0)
    (hbound : ∀ z : ℂ, ‖z‖ = σ → ‖(Gshift c (S.m c)).eval z‖ ≤ K)
    (hF2 : γ / 2 ≤ ‖iteratedDeriv 2 (Work.EL.F c) (S.m c)‖)
    (hwσ : 2 * ‖S.E c / 2‖ ≤ σ)
    (hw1 : 2 * K * ‖S.E c / 2‖^2 / σ^4 ≤ γ / 8)
    (hw2 : 6 * K * ‖S.E c / 2‖^2 / σ^3 ≤ 15 * γ * ‖S.E c / 2‖ / 128) :
    (gtc c (S.m c + S.E c / 2) = S.m c - S.E c / 2 →
        7 * ‖2 * (S.m c - Work.EL.F c (S.m c)) / S.E c‖
          ≤ 8 * |(2 * (S.m c - Work.EL.F c (S.m c)) / S.E c).im|) ∧
      (gtc c (S.m c + S.E c / 2) = S.m c + S.E c / 2 →
        7 * ‖2 * (S.m c - Work.EL.F c (S.m c)) / S.E c‖
          ≤ 8 * |(2 * (S.m c - Work.EL.F c (S.m c)) / S.E c).re|) := by
  set w : ℂ := S.E c / 2 with hwdef
  have hEw : S.E c = 2 * w := by rw [hwdef]; ring
  have hw0 : w ≠ 0 := by rw [hwdef]; exact div_ne_zero hE two_ne_zero
  have hw'σ : 2 * ‖w‖ ≤ σ := by rw [hwdef]; exact hwσ
  have hw'1 : 2 * K * ‖w‖^2 / σ^4 ≤ γ / 8 := by rw [hwdef]; exact hw1
  have hw'2 : 6 * K * ‖w‖^2 / σ^3 ≤ 15 * γ * ‖w‖ / 128 := by rw [hwdef]; exact hw2
  have hU : S.m c + w = S.m c + S.E c / 2 := by rw [hwdef]
  have hV : S.m c + (-w) = S.m c - S.E c / 2 := by rw [hwdef]; ring
  have hroot1 : (Gshift c (S.m c)).eval w = 0 := by
    rw [Gshift_eval, hU, S.fixed_add c hS]; ring
  have hroot2 : (Gshift c (S.m c)).eval (-w) = 0 := by
    rw [Gshift_eval, hV, S.fixed_sub c hS]; ring
  obtain ⟨ψ, hψ⟩ := exists_factor_quadratic (Gshift c (S.m c)) hw0 hroot1 hroot2
  have hfac : ∀ z : ℂ, (Gshift c (S.m c)).eval z = (z^2 - w^2) * ψ.eval z := by
    intro z
    rw [hψ]
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C]
  obtain ⟨hcore1, hcore2, hcore3⟩ :=
    poly_phase_core (Gshift c (S.m c)) ψ hσ hK hw0 hw'σ hfac hbound
  set E1 : ℂ := (Gshift c (S.m c)).derivative.eval w + 2 * (Gshift c (S.m c)).eval 0 / w with hE1
  set E2 : ℂ := (Gshift c (S.m c)).derivative.eval (-w) - 2 * (Gshift c (S.m c)).eval 0 / w with hE2
  set Wst : ℂ := 2 * (S.m c - Work.EL.F c (S.m c)) / S.E c with hWdef
  have hW_eq : Wst = -((Gshift c (S.m c)).eval 0) / w := by
    rw [hWdef, hEw, Gshift_eval]
    simp only [add_zero]
    field_simp
    ring
  have hGew : 2 * (Gshift c (S.m c)).eval 0 / w = -2 * Wst := by
    rw [hW_eq]; ring
  have hW_psi : Wst = w * ψ.eval 0 := by
    rw [hW_eq, hfac 0]; field_simp; ring
  have hderivw : (Gshift c (S.m c)).derivative.eval w = deriv (Work.EL.F c) (S.m c + w) - 1 := by
    rw [eq_sub_iff_add_eq]; exact (deriv_Fm c (S.m c) w).symm
  have hderivnw : (Gshift c (S.m c)).derivative.eval (-w)
      = deriv (Work.EL.F c) (S.m c + (-w)) - 1 := by
    rw [eq_sub_iff_add_eq]; exact (deriv_Fm c (S.m c) (-w)).symm
  have heps1 : E1 = deriv (Work.EL.F c) (S.m c + w) - 1 - 2 * Wst := by
    rw [hE1, hderivw, hGew]; ring
  have heps2 : E2 = deriv (Work.EL.F c) (S.m c + (-w)) - 1 + 2 * Wst := by
    rw [hE2, hderivnw, hGew]; ring
  have hc2 : γ / 4 ≤ ‖(Gshift c (S.m c)).coeff 2‖ := by
    rw [Gshift_coeff_two, norm_div, Complex.norm_ofNat]
    linarith [hF2]
  have hpsi0 : γ / 8 ≤ ‖ψ.eval 0‖ := by
    have hnorm : ‖(Gshift c (S.m c)).coeff 2‖ - 2 * K * ‖w‖^2 / σ^4 ≤ ‖ψ.eval 0‖ := by
      have h := norm_add_le (ψ.eval 0) ((Gshift c (S.m c)).coeff 2 - ψ.eval 0)
      rw [show ψ.eval 0 + ((Gshift c (S.m c)).coeff 2 - ψ.eval 0) = (Gshift c (S.m c)).coeff 2
        by ring] at h
      have h2 : ‖(Gshift c (S.m c)).coeff 2 - ψ.eval 0‖
          = ‖ψ.eval 0 - (Gshift c (S.m c)).coeff 2‖ := norm_sub_rev _ _
      rw [h2] at h
      linarith [h, hcore3]
    linarith [hnorm, hc2, hw'1]
  have hWlower : γ * ‖w‖ / 8 ≤ ‖Wst‖ := by
    rw [hW_psi, norm_mul]
    nlinarith [hpsi0, norm_nonneg w]
  have hphase : (6 * K * ‖w‖^2 / σ^3) / 2 ≤ 15/32 * ‖Wst‖ := by
    have h1 : 6 * K * ‖w‖^2 / σ^3 / 2 ≤ 15 * γ * ‖w‖ / 256 := by linarith [hw'2]
    have h2 : 15 * γ * ‖w‖ / 256 = 15/32 * (γ * ‖w‖ / 8) := by ring
    have h3 : 15/32 * (γ * ‖w‖ / 8) ≤ 15/32 * ‖Wst‖ :=
      mul_le_mul_of_nonneg_left hWlower (by norm_num)
    linarith [h1, h2, h3]
  refine ⟨?_, ?_⟩
  · intro hswap
    have h1 : gtc c (gtc c (S.m c + S.E c / 2)) = Work.EL.F c (S.m c + S.E c / 2) :=
      (congrFun (Ft_eq_g_comp c) (S.m c + S.E c / 2)).symm
    have h2 : gtc c (S.m c - S.E c / 2) = S.m c + S.E c / 2 := by
      rw [← hswap, h1]
      exact S.fixed_add c hS
    have hFu : deriv (Work.EL.F c) (S.m c + w) = star (deriv (Work.EL.F c) (S.m c + (-w))) := by
      rw [hU, hV]
      exact deriv_F_of_gtc_swap hswap h2
    have h1d : star (deriv (Work.EL.F c) (S.m c + (-w)) - 1 + 2 * Wst)
        - (deriv (Work.EL.F c) (S.m c + w) - 1 - 2 * Wst) = ((4 * Wst.re : ℝ) : ℂ) := by
      have hs : star (deriv (Work.EL.F c) (S.m c + (-w)) - 1 + 2 * Wst)
          = star (deriv (Work.EL.F c) (S.m c + (-w))) - 1 + 2 * star Wst := by
        simp only [star_add, star_sub, star_mul, star_one, star_ofNat]
        ring
      rw [hs, ← hFu]
      have hadd : Wst + star Wst = ((2 * Wst.re : ℝ) : ℂ) := by
        rw [Complex.star_def]
        exact Complex.add_conj Wst
      have hsimp : deriv (Work.EL.F c) (S.m c + w) - 1 + 2 * star Wst
          - (deriv (Work.EL.F c) (S.m c + w) - 1 - 2 * Wst)
          = 2 * (Wst + star Wst) := by ring
      rw [hsimp, hadd]; push_cast; ring
    have h1c : star E2 - E1 = ((4 * Wst.re : ℝ) : ℂ) := by
      rw [heps1, heps2]; exact h1d
    have h4 : 4 * Wst.re = E2.re - E1.re := by
      have hh := congrArg Complex.re h1c
      rw [Complex.sub_re, Complex.ofReal_re, Complex.star_def, Complex.conj_re] at hh
      exact hh.symm
    have hb : |Wst.re| ≤ (6 * K * ‖w‖^2 / σ^3) / 2 := by
      have hb1 : ‖E1‖ ≤ 6 * K * ‖w‖^2 / σ^3 := hcore1
      have hb2 : ‖E2‖ ≤ 6 * K * ‖w‖^2 / σ^3 := hcore2
      have h4' : |4 * Wst.re| ≤ 2 * (6 * K * ‖w‖^2 / σ^3) := by
        rw [h4]
        calc |E2.re - E1.re| ≤ |E2.re| + |E1.re| := abs_sub _ _
          _ ≤ ‖E2‖ + ‖E1‖ := add_le_add (Complex.abs_re_le_norm _) (Complex.abs_re_le_norm _)
          _ ≤ 6 * K * ‖w‖^2 / σ^3 + 6 * K * ‖w‖^2 / σ^3 := add_le_add hb2 hb1
          _ = 2 * (6 * K * ‖w‖^2 / σ^3) := by ring
      have : |4 * Wst.re| = 4 * |Wst.re| := by rw [abs_mul]; norm_num
      rw [this] at h4'
      linarith
    have h15 : |Wst.re| ≤ 15/32 * ‖Wst‖ := le_trans hb hphase
    exact phase_abs_le_of_re Wst h15
  · intro hfix
    obtain ⟨r, hr, hFr⟩ := deriv_F_of_gtc_fix hfix
    have heps1' : E1 = ((r : ℂ) - 1) - 2 * Wst := by
      rw [heps1, hU, hFr]
    have him : (deriv (Work.EL.F c) (S.m c + w) - 1 - 2 * Wst).im = -2 * Wst.im := by
      rw [← heps1, heps1']
      simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
        Complex.one_re, Complex.one_im]
      norm_num
    have hb : |Wst.im| ≤ (6 * K * ‖w‖^2 / σ^3) / 2 := by
      have hb1 : ‖E1‖ ≤ 6 * K * ‖w‖^2 / σ^3 := hcore1
      have h2 : 2 * Wst.im = -E1.im := by
        rw [heps1, him]; ring
      have hkey : 2 * |Wst.im| ≤ 6 * K * ‖w‖^2 / σ^3 := by
        have h2' : |2 * Wst.im| = 2 * |Wst.im| := by rw [abs_mul]; norm_num
        rw [← h2', h2, abs_neg]
        exact le_trans (Complex.abs_im_le_norm _) hb1
      linarith
    have h15 : |Wst.im| ≤ 15/32 * ‖Wst‖ := le_trans hb hphase
    exact phase_abs_le_of_im Wst h15

theorem phase_of_split {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    (S : Work.PARIMPL.ParSplit.SplitData d) :
    ∃ ρ' : ℝ, 0 < ρ' ∧ ρ' ≤ S.ρ ∧
      ∀ c ∈ Metric.ball c₀ ρ', S.E c ≠ 0 →
        (gtc c (S.m c + S.E c / 2) = S.m c - S.E c / 2 →
          7 * ‖2 * (S.m c - Work.EL.F c (S.m c)) / S.E c‖
            ≤ 8 * |(2 * (S.m c - Work.EL.F c (S.m c)) / S.E c).im|) ∧
        (gtc c (S.m c + S.E c / 2) = S.m c + S.E c / 2 →
          7 * ‖2 * (S.m c - Work.EL.F c (S.m c)) / S.E c‖
            ≤ 8 * |(2 * (S.m c - Work.EL.F c (S.m c)) / S.E c).re|) := by
  obtain ⟨ρu, R, M, hρu, hR, hM, hbnd, hcont⟩ := exists_uniform_bounds d
  set σ : ℝ := R / 4 with hσdef
  have hσ : 0 < σ := by rw [hσdef]; linarith
  set K : ℝ := M + ‖d.z₁‖ + 2 * σ with hKdef
  have hKpos : 0 < K := by rw [hKdef]; linarith [hM, norm_nonneg d.z₁, hσ]
  have hK : 0 ≤ K := le_of_lt hKpos
  set γ : ℝ := ‖iteratedDeriv 2 (Work.EL.F c₀) d.z₁‖ with hγdef
  have hγ : 0 < γ := by rw [hγdef]; exact norm_pos_iff.mpr d.simple
  set δw : ℝ := min (σ/2) (min (Real.sqrt (γ * σ^4 / (16 * K))) (15 * γ * σ^3 / (768 * K)))
    with hδwdef
  have hδwpos : 0 < δw := by
    rw [hδwdef]
    refine lt_min (by linarith) (lt_min ?_ ?_)
    · exact Real.sqrt_pos.mpr (by positivity)
    · positivity
  have hδ0 : δw ≤ σ/2 := by rw [hδwdef]; exact min_le_left _ _
  have hδ1 : δw ≤ Real.sqrt (γ * σ^4 / (16 * K)) := by
    rw [hδwdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hδ2 : δw ≤ 15 * γ * σ^3 / (768 * K) := by
    rw [hδwdef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  obtain ⟨ρm, hρm, hm_ball⟩ : ∃ ρ > 0, ∀ c ∈ ball c₀ ρ, dist (S.m c) d.z₁ ≤ σ := by
    have hcontm : ContinuousAt S.m c₀ :=
      S.cont_m.continuousAt (isOpen_ball.mem_nhds (mem_ball_self S.hρ))
    have hmem : S.m c₀ ∈ ball d.z₁ σ := by rw [S.m₀]; simpa using hσ
    obtain ⟨ε, hε, hεb⟩ := Metric.mem_nhds_iff.mp (hcontm.preimage_mem_nhds (isOpen_ball.mem_nhds hmem))
    exact ⟨ε, hε, fun c hc => le_of_lt (hεb hc)⟩
  obtain ⟨ρw, hρw, hw_ball⟩ : ∃ ρ > 0, ∀ c ∈ ball c₀ ρ, ‖S.E c / 2‖ ≤ δw := by
    have hcontE : ContinuousAt S.E c₀ :=
      S.cont_E.continuousAt (isOpen_ball.mem_nhds (mem_ball_self S.hρ))
    have hmem : S.E c₀ ∈ ball (0:ℂ) δw := by rw [S.E₀]; simpa using hδwpos
    obtain ⟨ε, hε, hεb⟩ := Metric.mem_nhds_iff.mp (hcontE.preimage_mem_nhds (isOpen_ball.mem_nhds hmem))
    refine ⟨ε, hε, fun c hc => ?_⟩
    have h1 := hεb hc
    rw [Set.mem_preimage] at h1
    rw [mem_ball, dist_eq_norm, sub_zero] at h1
    have h2 : ‖S.E c / 2‖ ≤ ‖S.E c‖ := by
      rw [norm_div, Complex.norm_ofNat]; linarith [norm_nonneg (S.E c)]
    linarith
  obtain ⟨ρF, hρF, hF_ball⟩ : ∃ ρ > 0,
      ∀ c ∈ ball c₀ ρ, γ / 2 ≤ ‖iteratedDeriv 2 (Work.EL.F c) (S.m c)‖ := by
    have hcontm : ContinuousAt S.m c₀ :=
      S.cont_m.continuousAt (isOpen_ball.mem_nhds (mem_ball_self S.hρ))
    have hpair : ContinuousAt (fun c : ℂ => (c, S.m c)) c₀ := continuousAt_id.prodMk hcontm
    have h2cont : ContinuousAt (fun p : ℂ × ℂ => iteratedDeriv 2 (Work.EL.F p.1) p.2) (c₀, S.m c₀) := by
      rw [S.m₀]; exact (continuous_localData d).2.2.1
    have h3cont : ContinuousAt (fun c : ℂ => iteratedDeriv 2 (Work.EL.F c) (S.m c)) c₀ :=
      ContinuousAt.comp (x := c₀) (f := fun c : ℂ => (c, S.m c))
        (g := fun p : ℂ × ℂ => iteratedDeriv 2 (Work.EL.F p.1) p.2) h2cont hpair
    obtain ⟨ε, hε, hεb⟩ := Metric.mem_nhds_iff.mp
      (h3cont.preimage_mem_nhds (isOpen_ball.mem_nhds (mem_ball_self (by linarith : (0:ℝ) < γ/2))))
    refine ⟨ε, hε, fun c hc => ?_⟩
    have h1 : iteratedDeriv 2 (Work.EL.F c) (S.m c) ∈
        ball (iteratedDeriv 2 (Work.EL.F c₀) (S.m c₀)) (γ/2) := hεb hc
    rw [mem_ball, dist_eq_norm] at h1
    have h2 : ‖iteratedDeriv 2 (Work.EL.F c₀) (S.m c₀)‖
        ≤ ‖iteratedDeriv 2 (Work.EL.F c) (S.m c)‖
          + ‖iteratedDeriv 2 (Work.EL.F c₀) (S.m c₀)
              - iteratedDeriv 2 (Work.EL.F c) (S.m c)‖ := by
      calc ‖iteratedDeriv 2 (Work.EL.F c₀) (S.m c₀)‖
          = ‖iteratedDeriv 2 (Work.EL.F c) (S.m c)
              + (iteratedDeriv 2 (Work.EL.F c₀) (S.m c₀)
                - iteratedDeriv 2 (Work.EL.F c) (S.m c))‖ := by
            congr 1
            ring
        _ ≤ _ := norm_add_le _ _
    have h3 : ‖iteratedDeriv 2 (Work.EL.F c₀) (S.m c₀) - iteratedDeriv 2 (Work.EL.F c) (S.m c)‖
        < γ / 2 := by
      rw [norm_sub_rev]; exact h1
    have hγ' : ‖iteratedDeriv 2 (Work.EL.F c₀) (S.m c₀)‖ = γ := by
      simpa only [S.m₀] using hγdef.symm
    linarith
  set ρa : ℝ := min ρu (min ρm (min ρw ρF)) with hρa
  have hρapos : 0 < ρa := by rw [hρa]; exact lt_min hρu (lt_min hρm (lt_min hρw hρF))
  refine ⟨min S.ρ ρa, lt_min S.hρ hρapos, min_le_left _ _, ?_⟩
  intro c hc hE
  have hcm := mem_ball.mp hc
  have hS : c ∈ ball c₀ S.ρ := mem_ball.mpr (lt_of_lt_of_le hcm (min_le_left _ _))
  have ha : c ∈ ball c₀ ρa := mem_ball.mpr (lt_of_lt_of_le hcm (min_le_right _ _))
  have ha_u : ρa ≤ ρu := by rw [hρa]; exact min_le_left _ _
  have ha_2 : ρa ≤ min ρm (min ρw ρF) := by rw [hρa]; exact min_le_right _ _
  have ha_m : ρa ≤ ρm := le_trans ha_2 (min_le_left _ _)
  have ha_3 : ρa ≤ min ρw ρF := le_trans ha_2 (min_le_right _ _)
  have ha_w : ρa ≤ ρw := le_trans ha_3 (min_le_left _ _)
  have ha_F : ρa ≤ ρF := le_trans ha_3 (min_le_right _ _)
  have ham := mem_ball.mp ha
  have hcu : c ∈ ball c₀ ρu := mem_ball.mpr (lt_of_lt_of_le ham ha_u)
  have hcm' : c ∈ ball c₀ ρm := mem_ball.mpr (lt_of_lt_of_le ham ha_m)
  have hcw : c ∈ ball c₀ ρw := mem_ball.mpr (lt_of_lt_of_le ham ha_w)
  have hcF : c ∈ ball c₀ ρF := mem_ball.mpr (lt_of_lt_of_le ham ha_F)
  have hdistm : dist (S.m c) d.z₁ ≤ σ := hm_ball c hcm'
  have hwle : ‖S.E c / 2‖ ≤ δw := hw_ball c hcw
  have hF2 : γ / 2 ≤ ‖iteratedDeriv 2 (Work.EL.F c) (S.m c)‖ := hF_ball c hcF
  have hbound : ∀ z : ℂ, ‖z‖ = σ → ‖(Gshift c (S.m c)).eval z‖ ≤ K := by
    intro z hz
    rw [Gshift_eval]
    have hzm : dist (S.m c + z) d.z₁ < R := by
      have h1 : dist (S.m c + z) d.z₁ ≤ dist (S.m c + z) (S.m c) + dist (S.m c) d.z₁ :=
        dist_triangle _ _ _
      have h2 : dist (S.m c + z) (S.m c) = ‖z‖ := by
        rw [dist_eq_norm]
        congr 1
        ring
      rw [h2, hz] at h1
      have h3 : σ + σ = R / 2 := by rw [hσdef]; ring
      linarith [h1, hdistm, h3, hR]
    have hMz := (hbnd c hcu (S.m c + z) hzm).1
    have h2 : ‖S.m c + z‖ ≤ ‖d.z₁‖ + 2 * σ := by
      have h3 : ‖S.m c + z‖ ≤ ‖S.m c‖ + ‖z‖ := norm_add_le _ _
      have h4 : ‖S.m c‖ ≤ ‖d.z₁‖ + σ := by
        have h5 : ‖S.m c‖ = ‖(S.m c - d.z₁) + d.z₁‖ := by ring_nf
        rw [h5]
        have := norm_add_le (S.m c - d.z₁) d.z₁
        rw [dist_eq_norm] at hdistm
        linarith
      rw [hz] at h3
      linarith
    calc ‖Work.EL.F c (S.m c + z) - (S.m c + z)‖
        ≤ ‖Work.EL.F c (S.m c + z)‖ + ‖S.m c + z‖ := norm_sub_le _ _
      _ ≤ M + ‖S.m c + z‖ := by linarith
      _ ≤ M + (‖d.z₁‖ + 2 * σ) := by linarith
      _ = K := by rw [hKdef]; ring
  have hwσ : 2 * ‖S.E c / 2‖ ≤ σ := by linarith
  have hw1 : 2 * K * ‖S.E c / 2‖^2 / σ^4 ≤ γ / 8 := by
    have hle := le_trans hwle hδ1
    have hsq : ‖S.E c / 2‖^2 ≤ γ * σ^4 / (16 * K) := by
      calc ‖S.E c / 2‖^2 ≤ (Real.sqrt (γ * σ^4 / (16 * K)))^2 :=
            pow_le_pow_left₀ (norm_nonneg _) hle 2
        _ = γ * σ^4 / (16 * K) := Real.sq_sqrt (by positivity)
    have hsq' : ‖S.E c / 2‖^2 * (16 * K) ≤ γ * σ^4 :=
      (le_div_iff₀ (by positivity : (0:ℝ) < 16 * K)).mp hsq
    rw [div_le_iff₀ (pow_pos hσ 4)]
    nlinarith [hsq', hKpos, hγ, pow_pos hσ 4]
  have hw2 : 6 * K * ‖S.E c / 2‖^2 / σ^3 ≤ 15 * γ * ‖S.E c / 2‖ / 128 := by
    have hle := le_trans hwle hδ2
    have hle' : ‖S.E c / 2‖ * (768 * K) ≤ 15 * γ * σ^3 :=
      (le_div_iff₀ (by positivity : (0:ℝ) < 768 * K)).mp hle
    rw [div_le_div_iff₀ (pow_pos hσ 3) (by norm_num : (0:ℝ) < 128)]
    have hmult := mul_le_mul_of_nonneg_left hle' (norm_nonneg (S.E c / 2))
    nlinarith [hmult, hKpos, hγ, pow_pos hσ 3, norm_nonneg (S.E c / 2)]
  exact phase_local S hσ hK hγ hS hE hbound hF2 hwσ hw1 hw2

end Work.PARIMPL.ParSplit
