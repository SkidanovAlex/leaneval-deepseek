/-
# The `r`-derivatives of the layer integrand `sinSq · e^{-π r² t}` as a sum of Gaussians

This file records the elementary *algebraic* fact that makes the `r`-seminorms of the CKMRV
layer computable: the `l`-th `r`-derivative of `sinSq r · e^{-π r² t}` is a fixed linear
combination of *three* complex Gaussians, whose parameters are the affine functions

  `a₀ = π t`,      `a₁ = π t - iπ`,      `a₂ = π t + iπ`

of `t`, each multiplied by a polynomial in `r` of degree at most `l` (the polynomials
`Work.Asymptotics.gaussPoly a l` of `Submission/Work/Asymptotics/gaussian_bound.lean`).

The three parameters come from the classical identity `4 sin²(π r²/2) = 2 - e^{iπr²} - e^{-iπr²}`
(`Work.Asymptotics.sinSq_eq_complex`), whose terms merge with the Gaussian `e^{-π r² t}` into
`e^{-a r²}`.  In the notation of the statement the shifts are collected in `δ`, so that the
parameters are `π t + δ j` with `δ = (0, -iπ, iπ)`, and the coefficients in `c = (2, -1, -1)`.

The proof is pure algebra: `iteratedDeriv` is linear on sums, and the `l`-th derivative of the
complex Gaussian `r ↦ e^{-a r²}` is `gaussPoly a l` times that Gaussian
(`Work.Asymptotics.iteratedDeriv_gaussPoly`).
-/
import Mathlib
import Submission.Work.Asymptotics.gaussian_bound
import Submission.Work.Asymptotics.sinSq_seminorm

noncomputable section

open scoped Topology

namespace Work.Asymptotics.Tile

/-- `ContDiffAt` of the coercion `ℝ → ℂ`.  (Recorded separately because `fun_prop` in this
Mathlib does not know the `Complex.ofReal` coercion.) -/
lemma contDiffAt_ofReal_c (l : ℕ) (r : ℝ) :
    ContDiffAt ℝ (↑l : ℕ∞) (fun s : ℝ => (s : ℂ)) r :=
  Complex.ofRealCLM.contDiff.contDiffAt.of_le le_top

/-- The complex Gaussian `s ↦ e^{-a s²}` restricted to `ℝ` is `C^l` at every point. -/
lemma contDiffAt_gaussExp (l : ℕ) (a : ℂ) (r : ℝ) :
    ContDiffAt ℝ (↑l : ℕ∞) (fun s : ℝ => Complex.exp (-(a * (s : ℂ) ^ 2))) r := by
  have hof := contDiffAt_ofReal_c l r
  have hz : ContDiffAt ℝ (↑l : ℕ∞) (fun z : ℂ => Complex.exp (-(a * z ^ 2))) ((r : ℂ)) := by
    fun_prop
  exact hz.comp r hof

/-- A constant multiple of a complex Gaussian restricted to `ℝ` is `C^l` at every point. -/
lemma contDiffAt_gaussExp_mul (l : ℕ) (c a : ℂ) (r : ℝ) :
    ContDiffAt ℝ (↑l : ℕ∞) (fun s : ℝ => c * Complex.exp (-(a * (s : ℂ) ^ 2))) r := by
  have hof := contDiffAt_ofReal_c l r
  have hz : ContDiffAt ℝ (↑l : ℕ∞) (fun z : ℂ => c * Complex.exp (-(a * z ^ 2))) ((r : ℂ)) := by
    fun_prop
  exact hz.comp r hof

/-- **The three-Gaussian decomposition of the layer integrand.**
`sinSq s · e^{-π s² t} = 2 e^{-(πt) s²} - e^{-(πt - iπ) s²} - e^{-(πt + iπ) s²}`. -/
lemma sinSq_mul_exp_decomp (t : ℝ) :
    (fun s : ℝ => Work.Asymptotics.sinSq s * Complex.exp (-(Real.pi * (s : ℂ) ^ 2 * (t : ℂ))))
      = fun s : ℝ =>
          2 * Complex.exp (-(((Real.pi : ℂ) * (t : ℂ)) * (s : ℂ) ^ 2))
            - Complex.exp (-((((Real.pi : ℂ) * (t : ℂ)) - (Real.pi : ℂ) * Complex.I) * (s : ℂ) ^ 2))
            - Complex.exp (-((((Real.pi : ℂ) * (t : ℂ)) + (Real.pi : ℂ) * Complex.I) * (s : ℂ) ^ 2)) := by
  funext s
  rw [Work.Asymptotics.sinSq_eq_complex]
  have h1 : Complex.exp (-(Real.pi * (s : ℂ) ^ 2 * (t : ℂ)))
      = Complex.exp (-(((Real.pi : ℂ) * (t : ℂ)) * (s : ℂ) ^ 2)) := by congr 1; ring
  have hA : Complex.exp (-(-Complex.I * Real.pi * (s : ℂ) ^ 2))
        * Complex.exp (-(((Real.pi : ℂ) * (t : ℂ)) * (s : ℂ) ^ 2))
      = Complex.exp (-((((Real.pi : ℂ) * (t : ℂ)) - (Real.pi : ℂ) * Complex.I) * (s : ℂ) ^ 2)) := by
    rw [← Complex.exp_add]; congr 1; ring
  have hB : Complex.exp (-(Complex.I * Real.pi * (s : ℂ) ^ 2))
        * Complex.exp (-(((Real.pi : ℂ) * (t : ℂ)) * (s : ℂ) ^ 2))
      = Complex.exp (-((((Real.pi : ℂ) * (t : ℂ)) + (Real.pi : ℂ) * Complex.I) * (s : ℂ) ^ 2)) := by
    rw [← Complex.exp_add]; congr 1; ring
  rw [h1, ← hA, ← hB]; ring

theorem layerDeriv_gauss_decomp (l : ℕ) :
    ∃ (c : Fin 3 → ℂ) (δ : Fin 3 → ℂ),
      ∀ (r t : ℝ), iteratedDeriv l (fun x : ℝ => Work.Asymptotics.sinSq x *
        Complex.exp (-(Real.pi * (x : ℂ) ^ 2 * (t : ℂ)))) r
      = ∑ j : Fin 3, c j * (Work.Asymptotics.gaussPoly ((Real.pi : ℂ) * (t : ℂ) + δ j) l).eval (r : ℂ)
          * Complex.exp (-(((Real.pi : ℂ) * (t : ℂ) + δ j) * (r : ℂ) ^ 2)) := by
  refine ⟨![2, -1, -1], ![0, -(Real.pi * Complex.I), Real.pi * Complex.I], ?_⟩
  intro r t
  -- split the integrand into three complex Gaussians
  rw [sinSq_mul_exp_decomp t]
  -- name the three parameters
  set A : ℂ := (Real.pi : ℂ) * (t : ℂ) with hA
  set B : ℂ := A - (Real.pi : ℂ) * Complex.I with hB
  set C : ℂ := A + (Real.pi : ℂ) * Complex.I with hC
  have hc1 : ContDiffAt ℝ (↑l : ℕ∞) (fun s : ℝ => Complex.exp (-(A * (s : ℂ) ^ 2))) r :=
    contDiffAt_gaussExp l A r
  have hc2 : ContDiffAt ℝ (↑l : ℕ∞) (fun s : ℝ => Complex.exp (-(B * (s : ℂ) ^ 2))) r :=
    contDiffAt_gaussExp l B r
  have hc3 : ContDiffAt ℝ (↑l : ℕ∞) (fun s : ℝ => Complex.exp (-(C * (s : ℂ) ^ 2))) r :=
    contDiffAt_gaussExp l C r
  have hc4 : ContDiffAt ℝ (↑l : ℕ∞) (fun s : ℝ => 2 * Complex.exp (-(A * (s : ℂ) ^ 2))) r :=
    contDiffAt_gaussExp_mul l 2 A r
  -- linearity of `iteratedDeriv` on the sum of the three Gaussians
  have step1 : iteratedDeriv l (((fun s : ℝ => 2 * Complex.exp (-(A * (s : ℂ) ^ 2)))
        - (fun s : ℝ => Complex.exp (-(B * (s : ℂ) ^ 2))))
        - (fun s : ℝ => Complex.exp (-(C * (s : ℂ) ^ 2)))) r
      = iteratedDeriv l ((fun s : ℝ => 2 * Complex.exp (-(A * (s : ℂ) ^ 2)))
          - (fun s : ℝ => Complex.exp (-(B * (s : ℂ) ^ 2)))) r
        - iteratedDeriv l (fun s : ℝ => Complex.exp (-(C * (s : ℂ) ^ 2))) r :=
    iteratedDeriv_sub (hc4.sub hc2) hc3
  have step2 : iteratedDeriv l ((fun s : ℝ => 2 * Complex.exp (-(A * (s : ℂ) ^ 2)))
          - (fun s : ℝ => Complex.exp (-(B * (s : ℂ) ^ 2)))) r
      = iteratedDeriv l (fun s : ℝ => 2 * Complex.exp (-(A * (s : ℂ) ^ 2))) r
        - iteratedDeriv l (fun s : ℝ => Complex.exp (-(B * (s : ℂ) ^ 2))) r :=
    iteratedDeriv_sub hc4 hc2
  have step3 : iteratedDeriv l (fun s : ℝ => 2 * Complex.exp (-(A * (s : ℂ) ^ 2))) r
      = 2 * iteratedDeriv l (fun s : ℝ => Complex.exp (-(A * (s : ℂ) ^ 2))) r :=
    iteratedDeriv_const_mul 2 hc1
  change iteratedDeriv l (((fun s : ℝ => 2 * Complex.exp (-(A * (s : ℂ) ^ 2)))
        - (fun s : ℝ => Complex.exp (-(B * (s : ℂ) ^ 2))))
        - (fun s : ℝ => Complex.exp (-(C * (s : ℂ) ^ 2)))) r = _
  rw [step1, step2, step3]
  -- the `l`-th derivative of a Gaussian is `gaussPoly` times the Gaussian
  rw [Work.Asymptotics.iteratedDeriv_gaussPoly A l,
      Work.Asymptotics.iteratedDeriv_gaussPoly B l,
      Work.Asymptotics.iteratedDeriv_gaussPoly C l]
  simp only []
  -- expand the three-term sum of the statement
  rw [Fin.sum_univ_three]
  have h0 : A + ![0, -(Real.pi * Complex.I), Real.pi * Complex.I] (0 : Fin 3) = A := by simp
  have h1 : A + ![0, -(Real.pi * Complex.I), Real.pi * Complex.I] (1 : Fin 3) = B := by
    rw [hB, sub_eq_add_neg]; simp
  have h2 : A + ![0, -(Real.pi * Complex.I), Real.pi * Complex.I] (2 : Fin 3) = C := by
    rw [hC]; simp
  rw [h0, h1, h2]
  rw [show (![2, -1, -1] (0 : Fin 3) : ℂ) = 2 from rfl,
      show (![2, -1, -1] (1 : Fin 3) : ℂ) = -1 from rfl,
      show (![2, -1, -1] (2 : Fin 3) : ℂ) = -1 from rfl]
  ring

end Work.Asymptotics.Tile
