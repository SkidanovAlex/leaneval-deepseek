import Mathlib
import Submission.Work.LinnikContract.Defs

namespace Work.A7

open Set

/-!
# Antitonicity of `Bfun K`

`Work.LinnikContract.Bfun K` is the per-character bound `B(λ)` of HB Lemma 13.3.  For
`λ > 0` it equals

  `B(λ) = (1 - e^{-2Kλ})/(6 K² λ) + (2Kλ - 1 + e^{-2Kλ})/(2 K² λ²)`,

and substituting `t = 2Kλ` (so `Kλ = t/2`) this is

  `B(λ) = (1/(3K)) · f(t) + 2 · g(t)`,   where
  `f(t) = (1 - e^{-t})/t`  and  `g(t) = (t - 1 + e^{-t})/t²`.

Both `f` and `g` are antitone on `(0, ∞)` (each is a Laplace transform of a nonnegative
kernel), and `λ ↦ t = 2Kλ` is strictly increasing for `K > 0`; hence `B` is antitone on
`(0, ∞)`, which is the statement below.  The `λ = 0` branch of `Bfun` is never reached
because the hypothesis gives `0 < x ≤ y`.
-/

/-- `f(t) = (1 - e^{-t})/t`, the Laplace transform of the constant `1` on `[0,1]`. -/
private noncomputable def fAux (t : ℝ) : ℝ := (1 - Real.exp (-t)) / t

/-- `g(t) = (t - 1 + e^{-t})/t²`, the Laplace transform of `1 - u` on `[0,1]`. -/
private noncomputable def gAux (t : ℝ) : ℝ := (t - 1 + Real.exp (-t)) / t^2

/-- The decreasing function `N(t) = 2 - t - (t + 2) e^{-t}`, whose sign controls `g'`. -/
private noncomputable def Nfun (t : ℝ) : ℝ := 2 - t - (t + 2) * Real.exp (-t)

/-- The elementary inequality `(x + 1) e^{-x} ≤ 1`, from `1 + x ≤ e^x`. -/
private lemma one_sub_mul_exp_neg_nonneg (x : ℝ) : 0 ≤ 1 - (x + 1) * Real.exp (-x) := by
  have h1 : x + 1 ≤ Real.exp x := Real.add_one_le_exp x
  have h2 : (x + 1) * Real.exp (-x) ≤ 1 := by
    have h3 : (x + 1) * Real.exp (-x) ≤ Real.exp x * Real.exp (-x) :=
      mul_le_mul_of_nonneg_right h1 (Real.exp_pos (-x)).le
    have h4 : Real.exp x * Real.exp (-x) = 1 := by
      rw [← Real.exp_add]; simp
    linarith
  linarith

private lemma hasDerivAt_fAux {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt fAux (((x + 1) * Real.exp (-x) - 1) / x^2) x := by
  have hnum : HasDerivAt (fun t : ℝ => 1 - Real.exp (-t)) (Real.exp (-x)) x := by
    have h := HasDerivAt.exp (hasDerivAt_neg x)
    have h' := HasDerivAt.const_sub (1 : ℝ) h
    simpa using h'
  have hden : HasDerivAt (fun t : ℝ => t) 1 x := hasDerivAt_id x
  have h := hnum.div hden hx
  have heq : (Real.exp (-x) * x - (1 - Real.exp (-x)) * 1) / x ^ 2
      = ((x + 1) * Real.exp (-x) - 1) / x^2 := by ring
  rw [heq] at h
  exact h

private lemma hasDerivAt_gAux {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt gAux ((2 - x - (x + 2) * Real.exp (-x)) / x^3) x := by
  have hnum : HasDerivAt (fun t : ℝ => t - 1 + Real.exp (-t))
      (1 + Real.exp (-x) * (-1)) x := by
    have h1 : HasDerivAt (fun t : ℝ => t - 1) 1 x := by
      simpa using (hasDerivAt_id x).sub_const 1
    have h2 : HasDerivAt (fun t : ℝ => Real.exp (-t)) (Real.exp (-x) * (-1)) x :=
      HasDerivAt.exp (hasDerivAt_neg x)
    exact h1.add h2
  have hden : HasDerivAt (fun t : ℝ => t^2) (2 * x) x := by
    simpa using hasDerivAt_pow 2 x
  have hdenne : x^2 ≠ 0 := pow_ne_zero 2 hx
  have h := hnum.div hden hdenne
  have heq : ((1 + Real.exp (-x) * (-1)) * x ^ 2 - (x - 1 + Real.exp (-x)) * (2 * x))
        / (x^2)^2
      = (2 - x - (x + 2) * Real.exp (-x)) / x^3 := by
    field_simp
    ring
  rw [heq] at h
  exact h

private lemma hasDerivAt_Nfun (x : ℝ) : HasDerivAt Nfun ((x + 1) * Real.exp (-x) - 1) x := by
  have h1 : HasDerivAt (fun t : ℝ => 2 - t) (-1) x := by
    simpa using (hasDerivAt_id x).const_sub 2
  have h2 : HasDerivAt (fun t : ℝ => (t + 2) * Real.exp (-t))
      (1 * Real.exp (-x) + (x + 2) * (Real.exp (-x) * (-1))) x := by
    exact ((hasDerivAt_id x).add_const 2).mul (HasDerivAt.exp (hasDerivAt_neg x))
  have h := h1.sub h2
  have heq : (-1 - (1 * Real.exp (-x) + (x + 2) * (Real.exp (-x) * (-1))))
      = (x + 1) * Real.exp (-x) - 1 := by ring
  rw [heq] at h
  exact h

/-- `N` is antitone on `[0, ∞)`: its derivative `(x+1)e^{-x} - 1` is `≤ 0`. -/
private lemma Nfun_antitone : AntitoneOn Nfun (Set.Ici 0) := by
  refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0) (f := Nfun)
    (f' := fun x => (x + 1) * Real.exp (-x) - 1) ?_ ?_ ?_
  · intro x _
    exact (hasDerivAt_Nfun x).continuousAt.continuousWithinAt
  · intro x _
    exact (hasDerivAt_Nfun x).hasDerivWithinAt
  · intro x _
    have := one_sub_mul_exp_neg_nonneg x
    linarith

/-- `f(t) = (1 - e^{-t})/t` is antitone on `(0, ∞)`; derivative `((t+1)e^{-t} - 1)/t² ≤ 0`. -/
private lemma fAux_antitone : AntitoneOn fAux (Set.Ioi 0) := by
  refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioi 0) (f := fAux)
    (f' := fun x => ((x + 1) * Real.exp (-x) - 1) / x^2) ?_ ?_ ?_
  · intro x hx
    exact (hasDerivAt_fAux (ne_of_gt hx)).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    exact (hasDerivAt_fAux (ne_of_gt hx)).hasDerivWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    have hnum : (x + 1) * Real.exp (-x) - 1 ≤ 0 := by
      have := one_sub_mul_exp_neg_nonneg x
      linarith
    exact div_nonpos_of_nonpos_of_nonneg hnum (pow_pos hx 2).le

/-- `g(t) = (t - 1 + e^{-t})/t²` is antitone on `(0, ∞)`; its derivative numerator is `N(t) ≤ 0`. -/
private lemma gAux_antitone : AntitoneOn gAux (Set.Ioi 0) := by
  refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioi 0) (f := gAux)
    (f' := fun x => (2 - x - (x + 2) * Real.exp (-x)) / x^3) ?_ ?_ ?_
  · intro x hx
    exact (hasDerivAt_gAux (ne_of_gt hx)).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    exact (hasDerivAt_gAux (ne_of_gt hx)).hasDerivWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    have hN : Nfun x ≤ Nfun 0 :=
      Nfun_antitone (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx.le) hx.le
    have hnum : 2 - x - (x + 2) * Real.exp (-x) ≤ 0 := by
      simpa [Nfun] using hN
    exact div_nonpos_of_nonpos_of_nonneg hnum (pow_pos hx 3).le

/-- For `λ ≠ 0`, `Bfun` rewrites in terms of `fAux` and `gAux` at `t = 2Kλ`. -/
private lemma Bfun_eq {K lam : ℝ} (hK : K ≠ 0) (hlam : lam ≠ 0) :
    Work.LinnikContract.Bfun K lam
      = (1 / (3 * K)) * fAux (2 * K * lam) + 2 * gAux (2 * K * lam) := by
  rw [Work.LinnikContract.Bfun, if_neg hlam]
  unfold fAux gAux
  have h2 : (2 : ℝ) * K * lam ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) hK) hlam
  field_simp
  ring_nf

theorem Bfun_antitone {K : ℝ} (hK : 0 < K) :
    ∀ {x y : ℝ}, 0 < x → x ≤ y → Work.LinnikContract.Bfun K y ≤ Work.LinnikContract.Bfun K x := by
  intro x y hx hxy
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  have hne : K ≠ 0 := ne_of_gt hK
  have htx : 0 < 2 * K * x := by positivity
  have hty : 0 < 2 * K * y := by positivity
  have htxle : 2 * K * x ≤ 2 * K * y := by nlinarith
  have hf : fAux (2 * K * y) ≤ fAux (2 * K * x) := fAux_antitone htx hty htxle
  have hg : gAux (2 * K * y) ≤ gAux (2 * K * x) := gAux_antitone htx hty htxle
  rw [Bfun_eq hne (ne_of_gt hx), Bfun_eq hne (ne_of_gt hy)]
  have h1 : (1 / (3 * K)) * fAux (2 * K * y) ≤ (1 / (3 * K)) * fAux (2 * K * x) :=
    mul_le_mul_of_nonneg_left hf (by positivity)
  have h2 : (2 : ℝ) * gAux (2 * K * y) ≤ 2 * gAux (2 * K * x) :=
    mul_le_mul_of_nonneg_left hg (by norm_num)
  exact add_le_add h1 h2

end Work.A7
