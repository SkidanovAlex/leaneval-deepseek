/-
# Definitions for the `high` part of the CKMRV layer: shapes in the `λ` variable

`Work.Asymptotics.highPart G τ r` is the explicit closed form

  `λ·psi1 λ·e^{-λ}·G₀₀ + i·psi1 λ·(λ+1)e^{-λ}·G₀₁ + μ·psi1 μ·e^{-μ}·G₁₀ + i·psi1 μ·(μ+1)e^{-μ}·G₁₁`

with `λ = π r²`, `μ = π r² - 2π` and `psi1 x = 2 ∫₀¹ (1-s)cos(sx) ds`.  Its `τ`-dependence enters
only through the four constants `G i j τ`, so the `r`-seminorms of `highPart` factor into

* a universal bound `|r|^k ‖∂_r^l (J ∘ (π·²)) r‖ ≤ K_J` for each of the four *fixed* functions
  `J : ℝ → ℂ` of the variable `λ`, and
* the moderate growth of the constants `‖G i j τ‖ ≤ α (scale τ)^N` on `𝒟`.

This file sets up those fixed functions and the identity expressing `highPart` through them.

## Main definitions

* `Work.Asymptotics.psiC` — the complexified regularising factor;
* `Work.Asymptotics.ExpBdd c N f` — `f` is smooth and `‖f^{(j)}(λ)‖ ≤ C_j (1+|λ|)^N e^{-cλ}`;
* `Work.Asymptotics.hiA λ = λ ψ(λ) e^{-λ}`, `Work.Asymptotics.hiB λ = ψ(λ)(λ+1) e^{-λ}`.

## Main results

* `Work.Asymptotics.highPart_eq_sum` — the four-term decomposition of `highPart`.
-/
import Mathlib
import Submission.Work.Asymptotics.F2LayerDefs

noncomputable section

open MeasureTheory UpperHalfPlane
open scoped Topology

namespace Work.Asymptotics

/-- The complexified regularising factor `psi1 x = 2 ∫₀¹ (1-s)cos(sx) ds`. -/
def psiC (x : ℝ) : ℂ := ((psi1 x : ℝ) : ℂ)

/-- `ExpBdd c N f` records that the smooth function `f : ℝ → ℂ` has every iterated derivative
dominated by a *fixed* polynomial `(1+|λ|)^N` times the decaying exponential `e^{-cλ}`.  The two
parameters are additive under multiplication of functions, which is exactly what the Leibniz rule
for `iteratedDeriv` needs. -/
def ExpBdd (c : ℝ) (N : ℕ) (f : ℝ → ℂ) : Prop :=
  ContDiff ℝ ⊤ f ∧ ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ,
    ‖iteratedDeriv j f x‖ ≤ C * (1 + |x|) ^ N * Real.exp (-(c * x))

/-- The shape `hiA λ = λ ψ(λ) e^{-λ}` (the `λ`-variable version of the `(0,0)` and, after a shift
by `2π`, the `(1,0)` coefficient of `highPart`). -/
def hiA (x : ℝ) : ℂ := (x : ℂ) * psiC x * Complex.exp (-(x : ℂ))

/-- The shape `hiB λ = ψ(λ)(λ+1) e^{-λ}` (the `λ`-variable version of the `(0,1)` and, after a
shift by `2π`, the `(1,1)` coefficient of `highPart`). -/
def hiB (x : ℝ) : ℂ := psiC x * ((x : ℂ) + 1) * Complex.exp (-(x : ℂ))

/-- **The four-term decomposition of `highPart`** into the fixed `λ`-shapes `hiA`, `hiB` (and
their shifts by `2π`) times the constants `G i j τ`. -/
theorem highPart_eq_sum (G : Fin 2 → Fin 2 → ℍ → ℂ) (τ : ℍ) (r : ℝ) :
    highPart G τ r =
      hiA (Real.pi * r ^ 2) * G 0 0 τ + Complex.I * hiB (Real.pi * r ^ 2) * G 0 1 τ
        + hiA (Real.pi * r ^ 2 - 2 * Real.pi) * G 1 0 τ
        + Complex.I * hiB (Real.pi * r ^ 2 - 2 * Real.pi) * G 1 1 τ := by
  simp only [highPart, hiA, hiB, psiC]
  ring

/-! ## The four `r`-shapes of `highPart`

`highPart G τ r = T₀₀(r) G₀₀(τ) + T₀₁(r) G₀₁(τ) + T₁₀(r) G₁₀(τ) + T₁₁(r) G₁₁(τ)` with the four
fixed functions `T_{i j} = hiT0 … hiT3` below, which are the shapes `hiA`, `hiB` (and their shifts
by `2π`) composed with `r ↦ λ = πr²`. -/

/-- The `(0,0)` shape `λ ψ(λ) e^{-λ}` as a function of `r`, `λ = πr²`. -/
def hiT0 : ℝ → ℂ := fun r => hiA (Real.pi * r ^ 2)

/-- The `(0,1)` shape `i ψ(λ)(λ+1) e^{-λ}` as a function of `r`, `λ = πr²`. -/
def hiT1 : ℝ → ℂ := fun r => Complex.I * hiB (Real.pi * r ^ 2)

/-- The `(1,0)` shape `μ ψ(μ) e^{-μ}` as a function of `r`, `μ = πr² - 2π`. -/
def hiT2 : ℝ → ℂ := fun r => hiA (Real.pi * r ^ 2 - 2 * Real.pi)

/-- The `(1,1)` shape `i ψ(μ)(μ+1) e^{-μ}` as a function of `r`, `μ = πr² - 2π`. -/
def hiT3 : ℝ → ℂ := fun r => Complex.I * hiB (Real.pi * r ^ 2 - 2 * Real.pi)

theorem highPart_eq_T (G : Fin 2 → Fin 2 → ℍ → ℂ) (τ : ℍ) (r : ℝ) :
    highPart G τ r =
      hiT0 r * G 0 0 τ + hiT1 r * G 0 1 τ + hiT2 r * G 1 0 τ + hiT3 r * G 1 1 τ := by
  rw [highPart_eq_sum]
  simp only [hiT0, hiT1, hiT2, hiT3]

/-! ## Elementary tools -/

/-- Composition of a smooth `ℝ → ℂ` function with the quadratic change of variable `r ↦ πr²`. -/
lemma contDiff_quad_comp {f : ℝ → ℂ} (hf : ContDiff ℝ ⊤ f) :
    ContDiff ℝ ⊤ (fun r : ℝ => f (Real.pi * r ^ 2)) :=
  hf.comp (contDiff_const.mul (contDiff_id.pow 2))

lemma contDiff_hiT0 (h : ContDiff ℝ ⊤ hiA) : ContDiff ℝ ⊤ hiT0 :=
  contDiff_quad_comp h

lemma contDiff_hiT2 (h : ContDiff ℝ ⊤ (fun x : ℝ => hiA (x - 2 * Real.pi))) :
    ContDiff ℝ ⊤ hiT2 :=
  contDiff_quad_comp h

lemma contDiff_hiT1 (h : ContDiff ℝ ⊤ hiB) : ContDiff ℝ ⊤ hiT1 := by
  have hq : ContDiff ℝ ⊤ (fun s : ℝ => hiB (Real.pi * s ^ 2)) := contDiff_quad_comp h
  have hc : ContDiff ℝ ⊤ (fun _ : ℝ => (Complex.I : ℂ)) := contDiff_const
  exact hc.mul hq

lemma contDiff_hiT3 (h : ContDiff ℝ ⊤ (fun x : ℝ => hiB (x - 2 * Real.pi))) :
    ContDiff ℝ ⊤ hiT3 := by
  have hq : ContDiff ℝ ⊤ (fun s : ℝ => (fun x : ℝ => hiB (x - 2 * Real.pi)) (Real.pi * s ^ 2)) :=
    contDiff_quad_comp h
  have hc : ContDiff ℝ ⊤ (fun _ : ℝ => (Complex.I : ℂ)) := contDiff_const
  exact hc.mul hq

/-- `iteratedDeriv` is additive over four summands. -/
lemma iteratedDeriv_sum4 {f0 f1 f2 f3 : ℝ → ℂ} {x : ℝ} {n : ℕ}
    (h0 : ContDiffAt ℝ (n : WithTop ℕ∞) f0 x) (h1 : ContDiffAt ℝ (n : WithTop ℕ∞) f1 x)
    (h2 : ContDiffAt ℝ (n : WithTop ℕ∞) f2 x) (h3 : ContDiffAt ℝ (n : WithTop ℕ∞) f3 x) :
    iteratedDeriv n (fun z => f0 z + f1 z + f2 z + f3 z) x
      = iteratedDeriv n f0 x + iteratedDeriv n f1 x + iteratedDeriv n f2 x
        + iteratedDeriv n f3 x := by
  rw [iteratedDeriv_fun_add ((h0.add h1).add h2) h3, iteratedDeriv_fun_add (h0.add h1) h2,
      iteratedDeriv_fun_add h0 h1]

/-- `ExpBdd` is invariant under shifting the argument. -/
lemma ExpBdd.sub_const {c : ℝ} {N : ℕ} {f : ℝ → ℂ} (hf : ExpBdd c N f) (a : ℝ) :
    ExpBdd c N (fun x => f (x - a)) := by
  have hcont : ContDiff ℝ ⊤ (fun x : ℝ => f (x - a)) :=
    hf.1.comp (contDiff_id.sub contDiff_const)
  refine ⟨hcont, fun j => ?_⟩
  obtain ⟨C, hC0, hC⟩ := hf.2 j
  refine ⟨C * (1 + |a|) ^ N * Real.exp (c * a), by positivity, fun x => ?_⟩
  have hrw : iteratedDeriv j (fun x : ℝ => f (x - a)) x = iteratedDeriv j f (x - a) :=
    congrFun (iteratedDeriv_comp_sub_const j f a) x
  rw [hrw]
  refine le_trans (hC (x - a)) ?_
  have hxa : (1 + |x - a|) ≤ (1 + |a|) * (1 + |x|) := by
    have h1 : |x - a| ≤ |x| + |a| := by
      rw [abs_sub_le_iff]
      constructor <;> linarith [le_abs_self x, neg_abs_le x, le_abs_self a, neg_abs_le a]
    nlinarith [abs_nonneg x, abs_nonneg a]
  have hxa' : (1 + |x - a|) ^ N ≤ (1 + |a|) ^ N * (1 + |x|) ^ N := by
    calc (1 + |x - a|) ^ N ≤ ((1 + |a|) * (1 + |x|)) ^ N :=
          pow_le_pow_left₀ (by positivity) hxa N
      _ = (1 + |a|) ^ N * (1 + |x|) ^ N := mul_pow _ _ _
  have hexp : Real.exp (-(c * (x - a))) = Real.exp (c * a) * Real.exp (-(c * x)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc C * (1 + |x - a|) ^ N * Real.exp (-(c * (x - a)))
      ≤ C * ((1 + |a|) ^ N * (1 + |x|) ^ N) * (Real.exp (c * a) * Real.exp (-(c * x))) := by
        rw [hexp]
        gcongr
    _ = C * (1 + |a|) ^ N * Real.exp (c * a) * (1 + |x|) ^ N * Real.exp (-(c * x)) := by
        ring

end Work.Asymptotics
