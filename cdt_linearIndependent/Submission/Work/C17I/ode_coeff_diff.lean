import Mathlib
import Submission.Work.C17I.defs

/-!
# Differentiability of the companion-system coefficients `A2`, `B2`

The companion first-order system of the pulled-back equation
`u'' + odP·u' + odQ·u = odR` (see `Submission.Work.C17I.defs`)

`Y' = A2 · Y + B2`,  `Y = (u, u')`,

has coefficients `A2` built from `odP`, `odQ` and `B2` built from `odR`.  Each of
`odP, odQ, odR` is a rational expression in `z` whose only singularities come from
`z = 1` and the zeros of the pull-back `pp2` of the leading coefficient `P₂`; the
numerator is a polynomial in `sw z` and hence holomorphic.  This file records that
all three are differentiable (indeed holomorphic) wherever `z ≠ 1` and `pp2 ≠ 0`,
and deduces the differentiability of the matrix-valued `A2` and vector-valued `B2`.
-/

namespace Work.C17I

open Polynomial

noncomputable section

/-- The Möbius involution `φ z = z/(z-1)` is differentiable at every `z ≠ 1`. -/
lemma differentiableAt_sw {z : ℂ} (hz : z ≠ 1) : DifferentiableAt ℂ sw z := by
  unfold sw
  exact DifferentiableAt.div differentiableAt_id (by fun_prop) (sub_ne_zero.mpr hz)

/-- The pull-back `z ↦ p(φ z)` of a rational polynomial `p` is differentiable at every
`z ≠ 1`. -/
lemma differentiableAt_polyEval_sw (p : Polynomial ℚ) {z : ℂ} (hz : z ≠ 1) :
    DifferentiableAt ℂ (fun z => p.eval₂ (algebraMap ℚ ℂ) (sw z)) z := by
  have h := (Polynomial.differentiableAt (p.map (algebraMap ℚ ℂ))).comp z (differentiableAt_sw hz)
  simpa only [Polynomial.eval₂_eq_eval_map, Function.comp_def] using h

/-- `odQ` is differentiable wherever `z ≠ 1` and `pp2 ≠ 0`. -/
lemma differentiableAt_odQ (a b : ℚ) {z : ℂ} (hz1 : z ≠ 1) (hz2 : pp2 a b z ≠ 0) :
    DifferentiableAt ℂ (odQ a b) z := by
  have h0 : DifferentiableAt ℂ (pp0 a b) z := differentiableAt_polyEval_sw (Work.C17.P0x a b) hz1
  have h2' : DifferentiableAt ℂ (pp2 a b) z :=
    differentiableAt_polyEval_sw (Work.C17.P2x a b) hz1
  have htz : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
  have hden : DifferentiableAt ℂ (fun z => pp2 a b z * (z - 1) ^ 4) z := h2'.mul (by fun_prop)
  have hne : pp2 a b z * (z - 1) ^ 4 ≠ 0 := mul_ne_zero hz2 (pow_ne_zero _ htz)
  change DifferentiableAt ℂ (fun z => pp0 a b z / (pp2 a b z * (z - 1) ^ 4)) z
  exact h0.div hden hne

/-- `odP` is differentiable wherever `z ≠ 1` and `pp2 ≠ 0`. -/
lemma differentiableAt_odP (a b : ℚ) {z : ℂ} (hz1 : z ≠ 1) (hz2 : pp2 a b z ≠ 0) :
    DifferentiableAt ℂ (odP a b) z := by
  have h1' : DifferentiableAt ℂ (pp1 a b) z :=
    differentiableAt_polyEval_sw (Work.C17.P1x a b) hz1
  have h2' : DifferentiableAt ℂ (pp2 a b) z :=
    differentiableAt_polyEval_sw (Work.C17.P2x a b) hz1
  have htz : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
  have hfirst : DifferentiableAt ℂ (fun z : ℂ => (2:ℂ) / (z - 1)) z :=
    (differentiableAt_const (2:ℂ)).div (by fun_prop) htz
  have hden : DifferentiableAt ℂ (fun z => pp2 a b z * (z - 1) ^ 2) z := h2'.mul (by fun_prop)
  have hne : pp2 a b z * (z - 1) ^ 2 ≠ 0 := mul_ne_zero hz2 (pow_ne_zero _ htz)
  have hsecond : DifferentiableAt ℂ (fun z => pp1 a b z / (pp2 a b z * (z - 1) ^ 2)) z :=
    h1'.div hden hne
  change DifferentiableAt ℂ
    (fun z => (2:ℂ) / (z - 1) - pp1 a b z / (pp2 a b z * (z - 1) ^ 2)) z
  exact hfirst.sub hsecond

/-- `odR` is differentiable wherever `z ≠ 1` and `pp2 ≠ 0`. -/
lemma differentiableAt_odR (a b : ℚ) (ra rb rab : ℤ) {z : ℂ}
    (hz1 : z ≠ 1) (hz2 : pp2 a b z ≠ 0) :
    DifferentiableAt ℂ (odR a b ra rb rab) z := by
  have h0 : DifferentiableAt ℂ (prh a b ra rb rab) z :=
    differentiableAt_polyEval_sw (Work.C17.rhoMx a b ra rb rab) hz1
  have h2' : DifferentiableAt ℂ (pp2 a b) z :=
    differentiableAt_polyEval_sw (Work.C17.P2x a b) hz1
  have htz : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
  have hden : DifferentiableAt ℂ (fun z => pp2 a b z * (z - 1) ^ 4) z := h2'.mul (by fun_prop)
  have hne : pp2 a b z * (z - 1) ^ 4 ≠ 0 := mul_ne_zero hz2 (pow_ne_zero _ htz)
  change DifferentiableAt ℂ (fun z => prh a b ra rb rab z / (pp2 a b z * (z - 1) ^ 4)) z
  exact h0.div hden hne

lemma differentiableOn_odP (a b : ℚ) {S : Set ℂ} (h1 : ∀ z ∈ S, z ≠ 1)
    (h2 : ∀ z ∈ S, pp2 a b z ≠ 0) : DifferentiableOn ℂ (odP a b) S :=
  fun z hz => (differentiableAt_odP a b (h1 z hz) (h2 z hz)).differentiableWithinAt

lemma differentiableOn_odQ (a b : ℚ) {S : Set ℂ} (h1 : ∀ z ∈ S, z ≠ 1)
    (h2 : ∀ z ∈ S, pp2 a b z ≠ 0) : DifferentiableOn ℂ (odQ a b) S :=
  fun z hz => (differentiableAt_odQ a b (h1 z hz) (h2 z hz)).differentiableWithinAt

lemma differentiableOn_odR (a b : ℚ) (ra rb rab : ℤ) {S : Set ℂ} (h1 : ∀ z ∈ S, z ≠ 1)
    (h2 : ∀ z ∈ S, pp2 a b z ≠ 0) : DifferentiableOn ℂ (odR a b ra rb rab) S :=
  fun z hz => (differentiableAt_odR a b ra rb rab (h1 z hz) (h2 z hz)).differentiableWithinAt

set_option linter.unusedVariables false in
theorem ode_coeff_diff (m n : ℕ) (ra rb rab : ℤ) {S : Set ℂ} (hSo : IsOpen S)
    (h1 : ∀ z ∈ S, z ≠ 1)
    (h2 : ∀ z ∈ S, Work.C17I.pp2 (Work.C17.aOf m) (Work.C17.aOf n) z ≠ 0) :
    DifferentiableOn ℂ (Work.C17I.A2 (Work.C17.aOf m) (Work.C17.aOf n)) S ∧
    DifferentiableOn ℂ (Work.C17I.B2 (Work.C17.aOf m) (Work.C17.aOf n) ra rb rab) S := by
  have hP := differentiableOn_odP (Work.C17.aOf m) (Work.C17.aOf n) h1 h2
  have hQ := differentiableOn_odQ (Work.C17.aOf m) (Work.C17.aOf n) h1 h2
  have hR := differentiableOn_odR (Work.C17.aOf m) (Work.C17.aOf n) ra rb rab h1 h2
  constructor
  · rw [differentiableOn_pi]
    intro i
    rw [differentiableOn_pi]
    intro j
    fin_cases i <;> fin_cases j <;>
      simp only [A2, Fin.isValue, Fin.zero_eta, Fin.mk_one, ↓reduceIte]
    · exact differentiableOn_const 0
    · exact differentiableOn_const 1
    · exact hQ.neg
    · exact hP.neg
  · rw [differentiableOn_pi]
    intro i
    fin_cases i <;> simp only [B2, Fin.isValue, Fin.zero_eta, Fin.mk_one, ↓reduceIte]
    · exact differentiableOn_const 0
    · exact hR

end

end Work.C17I
