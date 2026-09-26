/-
# The `j`-invariant separates `SL(2,ℤ)`-orbits

The modular `j`-invariant `j = E₄³/Δ = Work.Kernels.jInvariantFun` is a Hauptmodul for the
full modular group `SL(2,ℤ)`: it identifies `SL(2,ℤ)\ℍ` with `ℂ`.  In particular two points of
`ℍ` have the same `j`-value exactly when they are conjugate under `SL(2,ℤ)`.

The proof here uses the modular `lambda` function, for which the corresponding statement for
the level-`2` group `Γ(2)` is already available (`Work.Rigidity.lambda_fiber_orbit`):

* `j` is the degree-`6` rational function `256 (λ²-λ+1)³ / (λ²(1-λ)²)` of `λ = θ₁₀⁴/θ₀₀⁴`,
  obtained from `E₄ = (U²+V²+W²)/2`, `Δ = U²V²W²/256` and Jacobi's quartic identity `U = V+W`
  (here `U = θ₀₀⁴`, `V = θ₁₀⁴`, `W = θ₀₁⁴`);
* the fibres of that rational function are the orbits of the anharmonic group
  `{x, 1-x, x/(x-1), 1/(1-x), (x-1)/x, 1/x}` (`Work.Rigidity.anh`), each of whose elements is
  realised by an explicit element of `SL(2,ℤ)` (`Work.Rigidity.exists_lambdaFun_smul_eq_anh`);
* the fibre of `λ` over a value is a single `Γ(2)`-orbit (`Work.Rigidity.lambda_fiber_orbit`).
-/
import Mathlib
import Submission.Work.Kernels.Classical
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Kernels.TildeFacts.theta_quartic
import Submission.Work.Residues.KMinusClear_T
import Submission.Work.Rigidity.LambdaBasic
import Submission.Work.Rigidity.LambdaAnharmonic
import Submission.Work.Rigidity.lambda_fiber_orbit

namespace Work.Asymptotics

open UpperHalfPlane Work.Kernels

/-- Purely algebraic identity: `((a²+b²+c²)/2)³/(a²b²c²/256) = 256(b/a)²-…` for `a = b + c`. -/
private lemma alg_theta (a b c : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hq : a = c + b) :
    ((a ^ 2 + b ^ 2 + c ^ 2) / 2) ^ 3 / (a ^ 2 * b ^ 2 * c ^ 2 / 256)
      = 256 * ((b / a) ^ 2 - (b / a) + 1) ^ 3 / ((b / a) ^ 2 * (1 - b / a) ^ 2) := by
  subst hq
  have h1 : ((c + b) ^ 2 + b ^ 2 + c ^ 2) / 2 = (c + b) ^ 2 - (c + b) * b + b ^ 2 := by ring
  have h2 : (b / (c + b)) ^ 2 - b / (c + b) + 1
      = ((c + b) ^ 2 - (c + b) * b + b ^ 2) / (c + b) ^ 2 := by
    field_simp
    ring
  have h3 : 1 - b / (c + b) = c / (c + b) := by
    field_simp
    ring
  rw [h1, h2, h3]
  field_simp

/-- The `j`-invariant is the degree-six rational function `256 (λ²-λ+1)³/(λ²(1-λ)²)` of `λ`. -/
private lemma jInvariantFun_eq_lambda (τ : ℍ) :
    jInvariantFun τ = 256 * (lambdaFun τ ^ 2 - lambdaFun τ + 1) ^ 3 /
      (lambdaFun τ ^ 2 * (1 - lambdaFun τ) ^ 2) := by
  have hE4 := Work.Residues.KMinusT_E4Fun_eq_theta τ
  have hD := Work.Residues.KMinusT_DeltaFun_eq_theta τ
  have hq := Work.Kernels.TildeFacts.theta_quartic τ
  have ha : UFun τ ≠ 0 := Work.Rigidity.UFun_ne_zero τ
  have hb : VFun τ ≠ 0 := Work.Rigidity.VFun_ne_zero τ
  have hc : WFun τ ≠ 0 := Work.Rigidity.WFun_ne_zero τ
  have hmain := alg_theta (UFun τ) (VFun τ) (WFun τ) ha hb hc hq
  rw [show jInvariantFun τ
      = ((UFun τ ^ 2 + VFun τ ^ 2 + WFun τ ^ 2) / 2) ^ 3
        / (UFun τ ^ 2 * VFun τ ^ 2 * WFun τ ^ 2 / 256) by
    rw [jInvariantFun, hE4, hD]]
  rw [hmain]

/-- The fibres of `P(x) = 256 (x²-x+1)³/(x²(1-x)²)` are the anharmonic orbits. -/
private lemma eq_anh_of_P_eq (x y : ℂ) (hx0 : x ≠ 0) (hx1 : x ≠ 1)
    (h : (x ^ 2 - x + 1) ^ 3 * y ^ 2 * (1 - y) ^ 2
        = (y ^ 2 - y + 1) ^ 3 * x ^ 2 * (1 - x) ^ 2) :
    ∃ i : Fin 6, y = Work.Rigidity.anh i x := by
  have hN : (x ^ 2 - x + 1) ^ 3 * y ^ 2 * (1 - y) ^ 2
      - (y ^ 2 - y + 1) ^ 3 * x ^ 2 * (1 - x) ^ 2 = 0 := by
    rw [h]; ring
  have hfact : (x ^ 2 - x + 1) ^ 3 * y ^ 2 * (1 - y) ^ 2
      - (y ^ 2 - y + 1) ^ 3 * x ^ 2 * (1 - x) ^ 2
      = (y - x) * (y - 1 + x) * (y * (x - 1) - x) * (y * (1 - x) - 1)
        * (y * x - x + 1) * (y * x - 1) := by
    ring
  rw [hfact] at hN
  simp only [mul_eq_zero] at hN
  rcases hN with ((((h | h) | h) | h) | h) | h
  · refine ⟨0, ?_⟩; simp only [Work.Rigidity.anh]; linear_combination h
  · refine ⟨1, ?_⟩; simp only [Work.Rigidity.anh]; linear_combination h
  · refine ⟨2, ?_⟩; simp only [Work.Rigidity.anh]
    rw [eq_div_iff (sub_ne_zero.mpr hx1)]; linear_combination h
  · refine ⟨3, ?_⟩; simp only [Work.Rigidity.anh]
    rw [eq_div_iff (sub_ne_zero.mpr hx1.symm)]; linear_combination h
  · refine ⟨4, ?_⟩; simp only [Work.Rigidity.anh]
    rw [eq_div_iff hx0]; linear_combination h
  · refine ⟨5, ?_⟩; simp only [Work.Rigidity.anh]
    rw [eq_div_iff hx0]; linear_combination h

/-- Field identity: `256 A / B = 256 C / D` with `B, D ≠ 0` gives `A D = C B`. -/
private lemma div_cross (A B C D : ℂ) (hB : B ≠ 0) (hD : D ≠ 0)
    (hh : 256 * A / B = 256 * C / D) : A * D = C * B := by
  field_simp at hh
  linear_combination hh

theorem jInvariantFun_eq_smul_of_eq {τ w : UpperHalfPlane}
    (h : Work.Kernels.jInvariantFun τ = Work.Kernels.jInvariantFun w) :
    ∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, γ • w = τ := by
  have hτ := jInvariantFun_eq_lambda τ
  have hw := jInvariantFun_eq_lambda w
  have hx0 : lambdaFun w ≠ 0 := Work.Rigidity.lambdaFun_ne_zero w
  have hx1 : lambdaFun w ≠ 1 := Work.Rigidity.lambdaFun_ne_one w
  have hτ0 : lambdaFun τ ≠ 0 := Work.Rigidity.lambdaFun_ne_zero τ
  have hτ1 : lambdaFun τ ≠ 1 := Work.Rigidity.lambdaFun_ne_one τ
  -- the polynomial relation `P (λ w) = P (λ τ)`
  have hP : (lambdaFun w ^ 2 - lambdaFun w + 1) ^ 3 * lambdaFun τ ^ 2
        * (1 - lambdaFun τ) ^ 2
      = (lambdaFun τ ^ 2 - lambdaFun τ + 1) ^ 3 * lambdaFun w ^ 2
        * (1 - lambdaFun w) ^ 2 := by
    have h0 : (lambdaFun w ^ 2 - lambdaFun w + 1) ^ 3
          * (lambdaFun τ ^ 2 * (1 - lambdaFun τ) ^ 2)
        = (lambdaFun τ ^ 2 - lambdaFun τ + 1) ^ 3
          * (lambdaFun w ^ 2 * (1 - lambdaFun w) ^ 2) := by
      refine (div_cross ((lambdaFun τ ^ 2 - lambdaFun τ + 1) ^ 3)
        (lambdaFun τ ^ 2 * (1 - lambdaFun τ) ^ 2)
        ((lambdaFun w ^ 2 - lambdaFun w + 1) ^ 3)
        (lambdaFun w ^ 2 * (1 - lambdaFun w) ^ 2) ?_ ?_ ?_).symm
      · exact mul_ne_zero (pow_ne_zero 2 hτ0) (pow_ne_zero 2 (sub_ne_zero.mpr hτ1.symm))
      · exact mul_ne_zero (pow_ne_zero 2 hx0) (pow_ne_zero 2 (sub_ne_zero.mpr hx1.symm))
      · rw [hτ, hw] at h
        exact h
    simpa only [mul_assoc] using h0
  obtain ⟨i, hi⟩ := eq_anh_of_P_eq (lambdaFun w) (lambdaFun τ) hx0 hx1 hP
  obtain ⟨γ₁, hγ₁⟩ := Work.Rigidity.exists_lambdaFun_smul_eq_anh i
  have h1 : lambdaFun (γ₁ • w) = lambdaFun τ := by rw [hγ₁ w, hi]
  obtain ⟨γ₂, -, hγ₂⟩ := Work.Rigidity.fiberGood_all (lambdaFun τ) (γ₁ • w) τ h1 rfl
  exact ⟨γ₂ * γ₁, by rw [mul_smul, hγ₂]⟩

end Work.Asymptotics
