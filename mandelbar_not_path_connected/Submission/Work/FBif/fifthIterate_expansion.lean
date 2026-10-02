import Mathlib
import Submission.Work.FBif.Defs
import Submission.Work.FBif.Cycle
import Submission.Work.FBif.IterPoly
import Submission.Work.FBif.poly_taylor_two_bound
import Submission.Work.FBif.iterP_ten_derivs
import Submission.Work.FBif.deriv_tsq_five
import Submission.Work.FBif.quadratic_coeff_re_ne_zero

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FBif

open LeanEval.ComplexAnalysis (Tantibar)

/-- **The expansion of the unperturbed fifth iterate at a simple parabolic point.**

Let `c` be a root-parabolic parameter with parabolic point `z₁` (exact period `5`, multiplier `1`,
simple).  Then `Tantibar c^[5]` has at `z₁` the expansion
`z₁ + lam * (z-z₁)‾ + A₂ * ((z-z₁)‾)^2 + O(‖z-z₁‖³)` where the conjugate-linear multiplier `lam`
is a unit complex number, and the quadratic coefficient `A₂` is *not* orthogonal to `lam`: for
every square root `s` of `lam` the real part of `A₂/(lam * s)` is nonzero.

The last clause is exactly the simplicity of the parabolic point: the holomorphic second return
`T_c^10 = Tsq^5` has quadratic coefficient `lam * Ā₂ + A₂ * lam̄^2 = 2 * s̄ * Re(A₂/(lam s))` at
`z₁`, and `Work.EL.RootParabolic.simple` says that coefficient is nonzero. -/
theorem fifthIterate_expansion (c : ℂ) (d : Work.EL.RootParabolic c) :
    ∃ lam A₂ : ℂ, ‖lam‖ = 1 ∧ ∃ δ > 0, ∃ C : ℝ, 0 ≤ C ∧
      (∀ w : ℂ, ‖w‖ ≤ δ →
        ‖(LeanEval.ComplexAnalysis.Tantibar c)^[5] (d.z₁ + w) - d.z₁ - lam * star w - A₂ * (star w) ^ 2‖ ≤ C * ‖w‖ ^ 3) ∧
      (∀ s : ℂ, s ^ 2 = lam → (A₂ / (lam * s)).re ≠ 0) := by
  have hper : (Tantibar c)^[5] d.z₁ = d.z₁ := d.per_half
  -- the conjugate-linear multiplier and the quadratic coefficient of `T_c^[5]` at `z₁`,
  -- read off the antipolynomial `iterP c 5` (`(iterP c 5).eval (star z) = (T_c)^[5] z`)
  set lam : ℂ := (iterP c 5).derivative.eval (star d.z₁) with hlam
  set A₂ : ℂ := (iterP c 5).derivative.derivative.eval (star d.z₁) / 2 with hA₂
  have hd1 := (iterP_ten_derivs c d.z₁ hper).1
  have hd2 := (iterP_ten_derivs c d.z₁ hper).2
  -- the tenth iterate `(T_c)^[10] = (Tsq c)^[5]` is `iterP c 10`; its derivative at `z₁` is `1`
  have hmult : (iterP c 10).derivative.eval d.z₁ = 1 := by
    rw [← (deriv_tsq_five c d.z₁).1]
    exact d.mult
  -- hence `lam * star lam = 1` and `‖lam‖ = 1`
  have hlamnorm : ‖lam‖ = 1 := by
    rw [hlam]
    have h1 : (iterP c 5).derivative.eval (star d.z₁) *
        star ((iterP c 5).derivative.eval (star d.z₁)) = 1 := by
      rw [← hd1]; exact hmult
    have h2 : Complex.normSq ((iterP c 5).derivative.eval (star d.z₁)) = 1 := by
      apply Complex.ofReal_injective
      rw [← Complex.mul_conj]
      exact h1
    have h3 : ‖(iterP c 5).derivative.eval (star d.z₁)‖ ^ 2 = 1 := by
      rw [Complex.sq_norm]; exact h2
    nlinarith [norm_nonneg ((iterP c 5).derivative.eval (star d.z₁))]
  -- the simplicity of the parabolic point: the second derivative of `(T_c)^[10]` at `z₁` is
  -- `2 * (lam * star A₂ + A₂ * (star lam)^2)`, and it does not vanish
  have hsimple : iteratedDeriv 2 ((Work.Landing.Tsq c)^[5]) d.z₁ ≠ 0 := d.simple
  have hB : lam * star A₂ + A₂ * (star lam) ^ 2 ≠ 0 := by
    rw [hlam, hA₂]
    intro hzero
    apply hsimple
    rw [(deriv_tsq_five c d.z₁).2, hd2, hzero]
    ring
  -- the cubic Taylor bound for the antipolynomial `iterP c 5`
  obtain ⟨C, hC, hbound⟩ := poly_taylor_two_bound (iterP c 5) (star d.z₁) 1 (by norm_num)
  have hQa : (iterP c 5).eval (star d.z₁) = d.z₁ := by
    rw [iterP_five_eval_star]; exact hper
  refine ⟨lam, A₂, hlamnorm, 1, one_pos, C, hC, ?_, ?_⟩
  · intro w hw
    have h := hbound (star w) (by simpa using hw)
    rw [norm_star] at h
    rw [hQa] at h
    have h1 : (Tantibar c)^[5] (d.z₁ + w)
        = Polynomial.eval (star d.z₁ + star w) (iterP c 5) := by
      rw [← iterP_five_eval_star c (d.z₁ + w), star_add]
    rw [h1, hlam, hA₂]
    exact h
  · intro s hs
    exact quadratic_coeff_re_ne_zero hlamnorm hs hB

end Work.FBif
