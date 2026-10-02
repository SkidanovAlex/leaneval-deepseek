/-
Copyright: subproject `Submission/Work/PARIMPL/ParSplit/` of `mandelbar_not_path_connected`.

# The value of the chart constant on the wall: `parU0 S c = 1` where `S.E c = 0`

This module proves `Work.PARIMPL.ParSplit.parU0_eq_one_of_wall`, the one piece of the assembly of
`ParNormal` that is **not** covered by the phase inequalities of `phase_of_split` (see
`NOTES_WALL.md`): the value of the normal-form constant on the *collision locus*

    Z = {c : S.E c = 0} = {c : Gc S c = 0}

where the two split fixed points of the second return map `F c = (T_c)^[10]` collide.

## The mathematics

Write `m := S.m c`, `𝔤 := gam S c 1 = G_c'(m)` for `G_c = Gpoly c` the holomorphic partner of the
antiholomorphic square root `g = (T_c)^5`, and `γ := gam S c 2 = G_c''(m)/2`.

* **(a)** On the wall the midpoint `m` is a fixed point of `g`: `g m` is one of the two split fixed
  points (`g_mem_of_split` + `SplitData.swap_or_fix_of_split`), and both equal `m` there.
  Consequently `G_c(m) = conj (g m) = conj m`.

* **(b)** At a wall parameter `parRho S c = [w²] Q_c(m + w) = F''(m)/2` (only the `j = 0` term of the
  defining sum of `psi` survives, since `Gc S c = 0`).

* **(c)** Since `g` is antiholomorphic, `F = g ∘ g = P ∘ G_c` with `P = G_{conj c}`, and both are
  polynomials; hence the second order chain rule for `P ∘ G_c` at `m` (using `G_c(m) = conj m` and
  `P = conj ∘ G_c ∘ conj`, so that `P' (conj m) = conj (G_c'(m))` and likewise at order two) gives

      F''(m) = 2·(γ · conj 𝔤 + conj γ · 𝔤²).                                    (★)

* **(d)** The hypothesis `(Qpoly c).derivative.eval m = 0` says `F'(m) = 1`; differentiating the
  identity `conj (G_c (conj (G_c u))) = F u` (`deriv_star_comp_sq`) at `u = m`, where
  `conj (G_c m) = m`, gives `𝔤 · conj 𝔤 = 1`, i.e. `|𝔤| = 1`.

* **(e)** With `parLam S c = conj (parH S c) = conj 𝔤` (`parH_eq_gam_one_of_E_eq_zero`) and
  `parRho S c = γ · conj 𝔤 + conj γ · 𝔤²` from (b)+(c), the two-line computation

      parLam · parRho = conj 𝔤 · (γ conj 𝔤 + conj γ 𝔤²) = γ (conj 𝔤)² + conj γ · 𝔤
      conj (parRho)   = conj γ · 𝔤 + γ conj(𝔤²)        = conj γ · 𝔤 + γ (conj 𝔤)²

  (using `conj 𝔤 · 𝔤 = 1`) gives `parLam S c * parRho S c = conj (parRho S c)`.

* **(f)** `parRho S c ≠ 0` on a small ball, so

      parU0 S c = sqrt (parLam · ρ² / ‖ρ‖²) = sqrt (ρ conj ρ / (ρ conj ρ)) = sqrt 1 = 1 .

All of this uses only `ParWall` (definitions), `parH_ne_zero`, `deriv_star_comp_sq`,
`g_mem_of_split`, `parRho_ne_zero`, `two_mul_coeff_comp_X_add_C` and Mathlib's polynomial chain
rule `Polynomial.derivative_comp`.
-/
import Mathlib
import Submission.Work.PARIMPL.ParSplit.ParWall
import Submission.Work.PARIMPL.ParSplit.parLam_eq
import Submission.Work.PARIMPL.ParSplit.parH_ne_zero
import Submission.Work.PARIMPL.ParSplit.deriv_star_comp_sq
import Submission.Work.PARIMPL.ParSplit.g_mem_of_split
import Submission.Work.PARIMPL.ParSplit.parRho_ne_zero
import Submission.Work.PARIMPL.ParSplit.parChart_algebra

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open LeanEval.ComplexAnalysis (Tantibar)

namespace Work.PARIMPL.ParSplit

variable {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}

/-! ## `T_c` and its iterates commute with complex conjugation -/

/-- Conjugation intertwines the two antiholomorphic quadratics: `T_{c̄}(z̄) = conj (T_c z)`. -/
theorem Tantibar_star (c u : ℂ) : Tantibar (star c) (star u) = star (Tantibar c u) := by
  simp [Tantibar]

/-- `(T_{c̄})^n (z̄) = conj ((T_c)^n z)`. -/
theorem iterate_Tantibar_star (c : ℂ) (n : ℕ) (w : ℂ) :
    (Tantibar (star c))^[n] (star w) = star ((Tantibar c)^[n] w) := by
  induction n generalizing w with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, Tantibar_star]

/-- The same for the fifth iterate `gtc c = (T_c)^[5]`. -/
theorem gtc_star_star (c w : ℂ) : gtc (star c) (star w) = star (gtc c w) :=
  iterate_Tantibar_star c 5 w

/-- The holomorphic partner of the square root of `F c` is the *composition* of the two
antiholomorphic halves: `F c = G_{c̄} ∘ G_c`. -/
theorem Ft_eq_Gpoly_comp (c z : ℂ) :
    Ft c z = (Gpoly (star c)).eval ((Gpoly c).eval z) := by
  rw [eval_Gpoly_eq_star_gtc, eval_Gpoly_eq_star_gtc, gtc_star_star, star_star, gtc_comp_apply]

/-! ## The two polynomials `G_{c̄}` and `G_c` are conjugate to each other -/

/-- As functions of `u`, `G_{c̄} = conj ∘ G_c ∘ conj`. -/
theorem Gpoly_star_eval_eq_conj_comp (c : ℂ) :
    (fun u => (Gpoly (star c)).eval u)
      = starRingEnd ℂ ∘ (fun u => (Gpoly c).eval u) ∘ starRingEnd ℂ := by
  funext u
  simp only [Function.comp_apply, starRingEnd_apply]
  rw [eval_Gpoly_eq_star_gtc, eval_Gpoly_eq_star_gtc, ← gtc_star_star c (star u), star_star]

/-- The derivatives are conjugate: `deriv G_{c̄} = conj ∘ deriv G_c ∘ conj`. -/
theorem deriv_Gpoly_star (c : ℂ) :
    deriv (fun u => (Gpoly (star c)).eval u)
      = starRingEnd ℂ ∘ deriv (fun u => (Gpoly c).eval u) ∘ starRingEnd ℂ := by
  rw [Gpoly_star_eval_eq_conj_comp]
  exact deriv_conj_conj

/-- ... and so are the second derivatives. -/
theorem deriv_deriv_Gpoly_star (c : ℂ) :
    deriv (deriv (fun u => (Gpoly (star c)).eval u))
      = starRingEnd ℂ ∘ deriv (deriv (fun u => (Gpoly c).eval u)) ∘ starRingEnd ℂ := by
  rw [deriv_Gpoly_star]
  exact deriv_conj_conj

/-- At conjugates, `(G_{c̄})'' = conj ∘ (G_c)''`, in `iteratedDeriv` form. -/
theorem iteratedDeriv_Gpoly_star (c u : ℂ) :
    iteratedDeriv 2 (fun y => (Gpoly (star c)).eval y) (star u)
      = star (iteratedDeriv 2 (fun y => (Gpoly c).eval y) u) := by
  have h1 : iteratedDeriv 2 (fun y => (Gpoly (star c)).eval y)
      = deriv (deriv (fun y => (Gpoly (star c)).eval y)) := by
    simp [iteratedDeriv_succ, iteratedDeriv_zero]
  have h2 : iteratedDeriv 2 (fun y => (Gpoly c).eval y)
      = deriv (deriv (fun y => (Gpoly c).eval y)) := by
    simp [iteratedDeriv_succ, iteratedDeriv_zero]
  rw [h1, h2]
  have h := congrFun (deriv_deriv_Gpoly_star c) (star u)
  simpa only [Function.comp_apply, starRingEnd_apply, star_star] using h

/-- At conjugates, `(G_{c̄})'(z̄) = conj ((G_c)'(z))`. -/
theorem eval_derivative_Gpoly_star (c u : ℂ) :
    (Gpoly (star c)).derivative.eval (star u) = star ((Gpoly c).derivative.eval u) := by
  have h := congrFun (deriv_Gpoly_star c) (star u)
  simp only [Function.comp_apply, starRingEnd_apply, star_star] at h
  rw [← Polynomial.deriv, ← Polynomial.deriv]
  exact h

/-- At conjugates, `(G_{c̄})''(z̄) = conj ((G_c)''(z))`. -/
theorem eval_derivative2_Gpoly_star (c u : ℂ) :
    (Gpoly (star c)).derivative.derivative.eval (star u)
      = star ((Gpoly c).derivative.derivative.eval u) := by
  rw [← iteratedDeriv_two_poly (Gpoly (star c)) (star u),
      ← iteratedDeriv_two_poly (Gpoly c) u]
  exact iteratedDeriv_Gpoly_star c u

/-! ## The second order chain rule for polynomials -/

/-- Second order chain rule for polynomials:
`(p ∘ q)'' = (p'' ∘ q)·(q')² + (p' ∘ q)·q''`. -/
theorem derivative2_comp (p q : Polynomial ℂ) :
    Polynomial.derivative (Polynomial.derivative (p.comp q))
      = ((Polynomial.derivative (Polynomial.derivative p)).comp q) * (Polynomial.derivative q) ^ 2
        + ((Polynomial.derivative p).comp q) * Polynomial.derivative (Polynomial.derivative q) := by
  rw [Polynomial.derivative_comp, Polynomial.derivative_mul, Polynomial.derivative_comp]
  ring

/-! ## The second derivative of `F c` at a wall point -/

/-- **(★)** At a parameter `c` where the midpoint `S.m c` is fixed by `g = (T_c)^5` (i.e. on the
collision locus `Z`), the second derivative of the second return map is

    `F''(m) = 2·(γ·conj 𝔤 + conj γ·𝔤²)`,   `𝔤 = gam S c 1 = G_c'(m)`, `γ = gam S c 2 = G_c''(m)/2`.

Indeed `F = P ∘ G_c` with `P = G_{c̄}` (`Ft_eq_Gpoly_comp`), `G_c(m) = conj (g m) = conj m`, and
`P = conj ∘ G_c ∘ conj` relates the derivatives of `P` at `conj m` to those of `G_c` at `m`. -/
theorem wall_iteratedDeriv_two (S : SplitData d) {c : ℂ} (hwall : gtc c (S.m c) = S.m c) :
    iteratedDeriv 2 (Ft c) (S.m c)
      = 2 * (gam S c 2 * star (gam S c 1) + star (gam S c 2) * (gam S c 1) ^ 2) := by
  have hfun : (fun z => ((Gpoly (star c)).comp (Gpoly c)).eval z) = Ft c := by
    funext z
    rw [Polynomial.eval_comp]
    exact (Ft_eq_Gpoly_comp c z).symm
  have hqm : (Gpoly c).eval (S.m c) = star (S.m c) := by
    rw [eval_Gpoly_eq_star_gtc, hwall]
  have hp1 : (Gpoly (star c)).derivative.eval (star (S.m c))
      = star ((Gpoly c).derivative.eval (S.m c)) := eval_derivative_Gpoly_star c (S.m c)
  have hp2 : (Gpoly (star c)).derivative.derivative.eval (star (S.m c))
      = star ((Gpoly c).derivative.derivative.eval (S.m c)) :=
    eval_derivative2_Gpoly_star c (S.m c)
  have hq1 : (Gpoly c).derivative.eval (S.m c) = gam S c 1 := by
    rw [← Polynomial.deriv (p := Gpoly c) (x := S.m c), ← gam_one_eq_deriv S c]
  have hq2 : (Gpoly c).derivative.derivative.eval (S.m c) = 2 * gam S c 2 :=
    (two_mul_coeff_comp_X_add_C (Gpoly c) (S.m c)).symm
  rw [← hfun]
  rw [iteratedDeriv_two_poly, derivative2_comp]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_comp]
  rw [hqm, hp1, hp2, hq1, hq2, star_mul]
  norm_num
  ring

/-! ## `parRho` on the wall -/

/-- `2 · phi S c 2 = F''(S.m c)`: `phi S c 2` is the coefficient of `w²` in `Q_c (m + w)`, and
twice it is the second derivative of the fixed point equation `Q_c = F c - id`. -/
theorem two_mul_phi_eq_iteratedDeriv (S : SplitData d) (c : ℂ) :
    2 * phi S c 2 = iteratedDeriv 2 (Ft c) (S.m c) := by
  have hQ : 2 * ((Qpoly c).comp (Polynomial.X + Polynomial.C (S.m c))).coeff 2
      = (Polynomial.derivative (Polynomial.derivative (Qpoly c))).eval (S.m c) :=
    two_mul_coeff_comp_X_add_C (Qpoly c) (S.m c)
  have hd : Polynomial.derivative (Polynomial.derivative (Qpoly c))
      = Polynomial.derivative (Polynomial.derivative (Fpoly c)) := by
    rw [show Qpoly c = Fpoly c - Polynomial.X from rfl, Polynomial.derivative_sub,
      Polynomial.derivative_X, Polynomial.derivative_sub, Polynomial.derivative_one, sub_zero]
  have hiter : (Polynomial.derivative (Polynomial.derivative (Fpoly c))).eval (S.m c)
      = iteratedDeriv 2 (fun y => (Fpoly c).eval y) (S.m c) :=
    (iteratedDeriv_two_poly (Fpoly c) (S.m c)).symm
  have hF : (fun y => (Fpoly c).eval y) = Ft c := by funext y; exact Fpoly_eval c y
  unfold phi Phi
  rw [hQ, hd, hiter, hF]

/-- On the collision locus `Gc = (E/2)² = 0`, only the `j = 0` term of the defining sum of `psi`
survives, so `parRho S c = phi S c 2`. -/
theorem parRho_eq_phi_of_Gc_eq_zero (S : SplitData d) {c : ℂ} (hGc : Gc S c = 0) :
    parRho S c = phi S c 2 := by
  unfold parRho psi
  rw [hGc, Finset.sum_eq_single 0]
  · simp
  · intro j _ hne
    rw [zero_pow hne, zero_mul]
  · intro h0
    exact absurd (Finset.mem_range.mpr (by norm_num [wallN])) h0

/-- **(b)+(c)** On the wall, `parRho S c = γ·conj 𝔤 + conj γ·𝔤²`. -/
theorem parRho_of_wall (S : SplitData d) {c : ℂ} (hE : S.E c = 0)
    (hwall : gtc c (S.m c) = S.m c) :
    parRho S c = gam S c 2 * star (gam S c 1) + star (gam S c 2) * (gam S c 1) ^ 2 := by
  have hGc : Gc S c = 0 := by rw [Gc, hE]; simp
  have hp : parRho S c = phi S c 2 := parRho_eq_phi_of_Gc_eq_zero S hGc
  have h1 : 2 * phi S c 2 = iteratedDeriv 2 (Ft c) (S.m c) := two_mul_phi_eq_iteratedDeriv S c
  have h2 : iteratedDeriv 2 (Ft c) (S.m c)
      = 2 * (gam S c 2 * star (gam S c 1) + star (gam S c 2) * (gam S c 1) ^ 2) :=
    wall_iteratedDeriv_two S hwall
  rw [hp]
  linear_combination (2 : ℂ)⁻¹ * (h1.trans h2)

/-! ## `|𝔤| = 1` from the double-root hypothesis -/

/-- **(d)** At a wall parameter at which `S.m c` is a *double* root of `Q_c` (i.e.
`(Qpoly c).derivative.eval (S.m c) = 0`, so `F'(S.m c) = 1`), the derivative
`𝔤 = gam S c 1 = G_c'(S.m c)` is a unit complex number: `𝔤 · conj 𝔤 = 1`.

Indeed `conj (G_c (conj (G_c u))) = F u`, so differentiating at `u = m` — where
`conj (G_c m) = conj (conj m) = m` — gives `G_c'(m) · conj (G_c'(m)) = F'(m) = 1`. -/
theorem gam_one_mul_star_eq_one (S : SplitData d) {c : ℂ} (hwall : gtc c (S.m c) = S.m c)
    (hderiv : (Qpoly c).derivative.eval (S.m c) = 0) :
    gam S c 1 * star (gam S c 1) = 1 := by
  have h1 : deriv (Ft c) (S.m c) = 1 := by
    have hkey : (Fpoly c).derivative.eval (S.m c) = 1 := by
      have hd : (Qpoly c).derivative.eval (S.m c) = (Fpoly c).derivative.eval (S.m c) - 1 := by
        rw [show Qpoly c = Fpoly c - Polynomial.X from rfl, Polynomial.derivative_sub,
          Polynomial.derivative_X]
        simp
      rw [hd, sub_eq_zero] at hderiv
      exact hderiv
    rw [← hkey, ← Polynomial.deriv (p := Fpoly c) (x := S.m c)]
    have hFF : (fun x => (Fpoly c).eval x) = Ft c := by funext z; exact Fpoly_eval c z
    rw [hFF]
  have hdiff : Differentiable ℂ (fun u => (Gpoly c).eval u) := Polynomial.differentiable _
  have hsq := deriv_star_comp_sq hdiff (S.m c)
  have hfun : (fun x => star ((fun u => (Gpoly c).eval u)
      (star ((fun u => (Gpoly c).eval u) x)))) = Ft c := by
    funext x
    show star ((Gpoly c).eval (star ((Gpoly c).eval x))) = Ft c x
    rw [eval_Gpoly_eq_star_gtc c x, star_star, eval_Gpoly_eq_star_gtc c (gtc c x),
      gtc_comp_apply, star_star]
  rw [hfun] at hsq
  have hhm : star ((fun u => (Gpoly c).eval u) (S.m c)) = S.m c := by
    show star ((Gpoly c).eval (S.m c)) = S.m c
    rw [eval_Gpoly_eq_star_gtc, hwall, star_star]
  rw [hhm] at hsq
  have hd : deriv (fun u => (Gpoly c).eval u) (S.m c) = gam S c 1 :=
    (gam_one_eq_deriv S c).symm
  rw [hd] at hsq
  rw [h1] at hsq
  exact hsq.symm

/-! ## The key relation `parLam · parRho = conj (parRho)` on the wall -/

/-- **(e)** On the collision locus, `parLam S c * parRho S c = conj (parRho S c)`.  With
`parRho = γ·conj 𝔤 + conj γ·𝔤²`, `parLam = conj 𝔤` and `conj 𝔤 · 𝔤 = 1` this is a two-line
computation. -/
theorem parLam_mul_parRho_of_wall (S : SplitData d) {c : ℂ} (hE : S.E c = 0)
    (hwall : gtc c (S.m c) = S.m c) (hderiv : (Qpoly c).derivative.eval (S.m c) = 0) :
    parLam S c * parRho S c = star (parRho S c) := by
  have hgam : gam S c 1 * star (gam S c 1) = 1 := gam_one_mul_star_eq_one S hwall hderiv
  have hgam' : star (gam S c 1) * gam S c 1 = 1 := by rw [mul_comm, hgam]
  have hr := parRho_of_wall S hE hwall
  have hl : parLam S c = star (gam S c 1) := by
    rw [parLam, parH_eq_gam_one_of_E_eq_zero S hE]
  rw [hr, hl]
  simp only [star_add, star_mul, star_star, star_pow]
  linear_combination (star (gam S c 2) * gam S c 1) * hgam'

/-! ## The target -/

/-- **The chart constant on the wall.**  On a small parameter ball around `c₀`, at every
parameter `c` of the collision locus `S.E c = 0` at which the midpoint is a double root of the
fixed-point polynomial (`(Qpoly c).derivative.eval (S.m c) = 0`), the normal-form constant
`parU0 S c` equals `1`.  Hence `‖h c 0‖ = 1` and `‖h c 0 - 1‖ = 0 ≤ 1/2` there, which is the
`ParNormal.bounds` clause on the wall (the off-wall case is `phase_of_split`). -/
theorem parU0_eq_one_of_wall {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    (S : Work.PARIMPL.ParSplit.SplitData d) :
    ∃ ρ' > 0, ρ' ≤ S.ρ ∧ ∀ c ∈ Metric.ball c₀ ρ',
      S.E c = 0 → (Work.PARIMPL.ParSplit.Qpoly c).derivative.eval (S.m c) = 0 →
      Work.PARIMPL.ParSplit.parU0 S c = 1 := by
  obtain ⟨ρ₁, hρ₁0, hρ₁ρ, hmem⟩ := g_mem_of_split S
  obtain ⟨ρ₂, hρ₂0, hρ₂ρ, hρ₂ne⟩ := parRho_ne_zero S
  refine ⟨min ρ₁ ρ₂, lt_min hρ₁0 hρ₂0, le_trans (min_le_left _ _) hρ₁ρ, ?_⟩
  intro c hc hE hderiv
  have hc₁ : c ∈ Metric.ball c₀ ρ₁ := Metric.ball_subset_ball (min_le_left _ _) hc
  have hc₂ : c ∈ Metric.ball c₀ ρ₂ := Metric.ball_subset_ball (min_le_right _ _) hc
  have hcρ : c ∈ Metric.ball c₀ S.ρ :=
    Metric.ball_subset_ball (le_trans (min_le_left _ _) hρ₁ρ) hc
  have hρ : parRho S c ≠ 0 := hρ₂ne c hc₂
  -- (a) on the wall the midpoint is fixed by `g`
  have hdich := S.swap_or_fix_of_split hcρ (hmem c hc₁)
  rw [hE] at hdich
  simp only [zero_div, add_zero, sub_zero] at hdich
  have hwall : gtc c (S.m c) = S.m c := by rcases hdich with h | h <;> exact h
  have hkey : parLam S c * parRho S c = star (parRho S c) :=
    parLam_mul_parRho_of_wall S hE hwall hderiv
  -- (f) the argument of the square root is `1`
  have harg : parLam S c * (parRho S c) ^ 2 / (↑‖parRho S c‖ : ℂ) ^ 2 = 1 := by
    have hnorm : (↑‖parRho S c‖ : ℂ) ^ 2 = parRho S c * star (parRho S c) := by
      rw [← Complex.ofReal_pow]
      have h := Complex.mul_conj' (parRho S c)
      rw [← Complex.ofReal_pow, starRingEnd_apply] at h
      exact h.symm
    rw [hnorm]
    have h1 : parLam S c * (parRho S c) ^ 2 = star (parRho S c) * parRho S c := by
      rw [sq, ← mul_assoc, hkey]
    rw [h1, mul_comm (star (parRho S c)) (parRho S c),
      div_self (mul_ne_zero hρ (star_ne_zero.mpr hρ))]
  unfold parU0
  rw [harg]
  exact Complex.sqrt_one

end Work.PARIMPL.ParSplit
