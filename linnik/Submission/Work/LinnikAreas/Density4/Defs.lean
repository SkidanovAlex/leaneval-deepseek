/-
# Area 4 / HB §11–§12 — shared definitions and bookkeeping lemmas

Namespace `Work.LinnikAreas.Density4`.  This file is the vocabulary in which the delegated pieces of
HB §11 (`Submission/Work/LinnikAreas/Density4/*`) are stated: the mollifiers `psiM`, `thetaM`
(HB (11.6), (11.7)), the general density weight `wGen` (HB (11.3)), and the bookkeeping lemmas of
steps (II)–(VI) of HB §11.  It is sorry-free.
-/
import Mathlib
import Submission.Work.LinnikContract.Areas
import Submission.Work.LinnikContract.API.isZ_lambda_nonneg

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.LinnikAreas.Density4

open Work.LinnikContract

/-! ## HB's mollifiers (11.6), (11.7) -/

/-- HB (11.6): the Selberg-type mollifier `ψ_d`, with real cut-offs `U ≤ V` (`U = q^u`, `V = q^v`). -/
def psiM (U V : ℝ) (d : ℕ) : ℝ :=
  if (d:ℝ) ≤ U then (ArithmeticFunction.moebius d : ℝ)
  else if (d:ℝ) ≤ V then
    (ArithmeticFunction.moebius d : ℝ) * Real.log (V / (d:ℝ)) / Real.log (V / U)
  else 0

/-- HB (11.7): the mollifier `θ_d`, with real cut-off `W` (`W = q^w`). -/
def thetaM (W : ℝ) (d : ℕ) : ℝ :=
  if (d:ℝ) ≤ W then (ArithmeticFunction.moebius d : ℝ) * Real.log (W / (d:ℝ)) / Real.log W
  else 0

/-! ## The density weight of HB §11 -/

/-- The weight of HB (11.3): `λ ↦ λ/(e^{(4φ+6c₁+2c₂)λ} - e^{(2φ+4c₁)λ})`. -/
def wGen (phi c1 c2 x : ℝ) : ℝ :=
  x / (Real.exp ((4*phi + 6*c1 + 2*c2)*x) - Real.exp ((2*phi + 4*c1)*x))

/-- **Bookkeeping step (VI) of HB §11.**  With `φ = 1/3`, `c₁ = 1/10`, `c₂ = 1/4` the general
weight of HB (11.3) *is* the weight `wHB` of the contract (`73/30 = 4φ+6c₁+2c₂`,
`16/15 = 2φ+4c₁`). -/
lemma wGen_spec : wGen (1/3) (1/10) (1/4) = wHB := by
  funext x
  rw [wGen, wHB]
  norm_num

/-- `wHB` is non-negative (the denominator is `x · ∫_{16/15}^{73/30} e^{tx} dt`, so it has the sign
of `x`). -/
lemma wHB_nonneg (x : ℝ) : 0 ≤ wHB x := by
  rw [wHB]
  rcases lt_or_ge x 0 with hx | hx
  · have hden : Real.exp (73/30 * x) - Real.exp (16/15 * x) ≤ 0 := by
      have : (73/30:ℝ) * x ≤ (16/15) * x := by nlinarith
      linarith [Real.exp_le_exp.mpr this]
    rw [div_nonneg_iff]
    exact Or.inr ⟨hx.le, hden⟩
  · have hden : 0 ≤ Real.exp (73/30 * x) - Real.exp (16/15 * x) := by
      have : (16/15:ℝ) * x ≤ (73/30) * x := by nlinarith
      linarith [Real.exp_le_exp.mpr this]
    exact div_nonneg hx hden

/-! ## The finitely many weights of HB §11 are exactly the `wHB (λ^{(χ)})` -/

/-- If a character has a zero in the working region then `λ^{(χ)} = lamChar χ` is non-negative. -/
lemma lamChar_nonneg {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hq : 2 ≤ q)
    (h : ∃ ρ, IsZ χ ρ) : 0 ≤ lamChar χ := by
  obtain ⟨ρ, hρ⟩ := h
  have hS : (0:ℝ) ≤ sInf {x : ℝ | ∃ ρ, IsZ χ ρ ∧ lamOf q ρ = x} := by
    refine le_csInf ⟨lamOf q ρ, ρ, hρ, rfl⟩ ?_
    rintro x ⟨ρ', hρ', rfl⟩
    exact Work.LinnikContract.API.isZ_lambda_nonneg hq hρ'
  simpa [lamChar] using hS

/-- `lamChar` is a lower bound for the `λ` of any zero in the working region. -/
lemma lamChar_le_of_isZ {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q} {ρ : ℂ}
    (h : IsZ χ ρ) : lamChar χ ≤ lamOf q ρ := by
  have hbdd : BddBelow {x : ℝ | ∃ ρ, IsZ χ ρ ∧ lamOf q ρ = x} := by
    refine ⟨0, ?_⟩
    rintro x ⟨ρ', hρ', rfl⟩
    exact Work.LinnikContract.API.isZ_lambda_nonneg hq hρ'
  exact csInf_le hbdd ⟨ρ, h, rfl⟩

/-- **The closing bookkeeping of HB §11 (step (VI)).**  Suppose the general weighted estimate has
been proved for the parameters `φ = 1/3, c₁ = 1/10, c₂ = 1/4` in the "unnormalised" form of
(11.18), i.e. `Σ_χ 2w · wHB(λ^{(χ)}) ≤ (1+δ)(2x-u-v)/(2(v-u))` with `w = c₁ - ε₁`, `u = φ+2c₁`,
`v = u + c₂`, `x = 2φ+3c₁+c₂`.  Since `2x-u-v = 67/60` and `v-u = 1/4` this reads
`2w Σ_χ wHB(λ^{(χ)}) ≤ (1+δ)·67/30`, and the contract's bound `67/6 + ε` follows from the stated
arithmetic side condition on `δ, ε₁`. -/
lemma hb11_final_step {ε δ ε₁ : ℝ} (hε₁ : 0 < ε₁) (hε₁' : ε₁ < 1/10)
    (hsmall : 67/6 * ((1 + δ) / (1 - 10*ε₁)) ≤ 67/6 + ε) {S : Finset ℝ}
    (h : ∑ x ∈ S, 2*(1/10 - ε₁) * wHB x ≤ (1 + δ) * (67/30)) :
    ∑ x ∈ S, wHB x ≤ 67/6 + ε := by
  have hw : 0 < 2*(1/10 - ε₁) := by linarith
  have hsum : (∑ x ∈ S, wHB x) * (2*(1/10 - ε₁)) ≤ (1 + δ) * (67/30) := by
    have : (∑ x ∈ S, wHB x) * (2*(1/10 - ε₁)) = ∑ x ∈ S, 2*(1/10 - ε₁) * wHB x := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun x _ => by ring)
    rw [this]; exact h
  have h2 : ∑ x ∈ S, wHB x ≤ (1 + δ) * (67/30) / (2*(1/10 - ε₁)) :=
    (le_div_iff₀ hw).mpr hsum
  have h3 : (1 + δ) * (67/30) / (2*(1/10 - ε₁)) = 67/6 * ((1 + δ) / (1 - 10*ε₁)) := by
    field_simp
    ring
  rw [h3] at h2
  linarith

/-! ## The quantities of HB §11 (`detSum`) and §12 (`Kf`, `Lapl`) -/

/-- **HB (11.8)–(11.11): the "zero detector" sum.**  For a character `χ` with a zero `ρ` (in the
working region) and the cut-offs `U = q^u ≤ V = q^v`, `W = q^w`, `X = q^x` (`L = log q`),
`Σ_n (Σ_{d|n}ψ_d)(Σ_{d|n}θ_d) χ(n) n^{-ρ} (e^{-n/X} - e^{-nL²/U})`.  HB shows this has modulus
`≥ 1 - O(1/𝓛)` for every character `χ = χ^{(k)}` carrying a zero with `λ(ρ) ≤ λ₀`. -/
def detSum (q : ℕ) [NeZero q] (U V W X L : ℝ) (χ : DirichletCharacter ℂ q) (ρ : ℂ) : ℂ :=
  ∑' n : ℕ, ((∑ d ∈ n.divisors, psiM U V d : ℝ) : ℂ) * ((∑ d ∈ n.divisors, thetaM W d : ℝ) : ℂ)
    * χ (n : ZMod q) * ((n : ℂ) ^ (-ρ))
    * ((Real.exp (-(n:ℝ)/X) - Real.exp (-(n:ℝ)*L^2/U) : ℝ) : ℂ)

/-- **HB §6: the `K`-sum** `K(β,χ) = Σ_n Λ(n) Re(χ(n) n^{-β}) f(log n / 𝓛)` (same shape as the
hypothesis of `Commons.NumberTheory.Linnik.lemma5_2_of_logDeriv_bound`). -/
def Kf (q : ℕ) [NeZero q] (L β : ℝ) (f : ℝ → ℝ) (χ : DirichletCharacter ℂ q) : ℝ :=
  ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ)
    * ((χ (n : ZMod q) / (n : ℂ) ^ (β : ℂ)).re) * f (Real.log n / L)

/-- **HB §6: the `K`-sum with a complex shift**, `K(β+it,χ) = Σ_n Λ(n) Re(χ(n) n^{-β-it}) f(log n / 𝓛)`.
This is exactly the sum appearing in the conclusion of
`Commons.NumberTheory.Linnik.lemma5_2_of_logDeriv_bound` (with `𝓛 = log q`, `s = β+it`). -/
def Kgen (q : ℕ) [NeZero q] (L β t : ℝ) (f : ℝ → ℝ) (χ : DirichletCharacter ℂ q) : ℝ :=
  ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ)
    * ((χ (n : ZMod q) * (n : ℂ) ^ (-(β : ℂ) - (t : ℂ) * Complex.I)).re) * f (Real.log n / L)

/-- The Laplace transform of a function supported in `[0, x₀]`, at a **real** argument `z`:
`F(z) = ∫_0^{x₀} e^{-zt} f(t) dt`.  (HB §7 needs `F(-λ₁)` and `F(λ-λ₁)`.) -/
def Lapl (x₀ : ℝ) (f : ℝ → ℝ) (z : ℝ) : ℝ := ∫ t in (0:ℝ)..x₀, Real.exp (-(z*t)) * f t

end Work.LinnikAreas.Density4
