import Mathlib
import Submission.Work.WilE9.Defs
import Submission.Work.WilE9.Psi.deriv_psiInv
import Submission.Work.WilE9.Psi.hasDerivAt_psig
import Submission.Work.WilE9.Psi.psi_psig_algebra

open Topology Filter

namespace Work.WilE9.Psi

open MvPolynomial

/-! ### The algebraic jet of `ψ⁻¹`

Everything is measured against the two functions `a z = psiInv z` and `w z = psig (psiInv z)`.
On `|y| < 1` the pair `(a, w)` satisfies `w ^ 2 * (1 + a ^ 2) = 1`, whence `w ^ (-1) = (1 + a^2) w`
and every negative power of `w` becomes a polynomial in `(a, w)`.  Concretely:

* `(a)' = w⁻³ = ((1 + a^2) * w)^3`, a polynomial `Pa`,
* `(w)' = -a`, the polynomial `Pw`.

The derivation `step Q = ∂₀Q * Pa + ∂₁Q * Pw` is therefore the correct "coordinate derivative":
on `|y| < 1` the function `z ↦ eval (a z, w z) Q` has derivative `eval (a y, w y) (step Q)`. -/

/-- The polynomial `((1 + X₀²) * X₁)³` representing `(psiInv)'` in the coordinates
`(psiInv y, psig (psiInv y))`. -/
noncomputable def Pa : MvPolynomial (Fin 2) ℝ := ((1 + X 0 ^ 2) * X 1) ^ 3

/-- The polynomial `-X₀` representing `(psig ∘ psiInv)'` in the coordinates
`(psiInv y, psig (psiInv y))`. -/
noncomputable def Pw : MvPolynomial (Fin 2) ℝ := -X 0

/-- The formal derivation of `ℝ[X₀, X₁]` induced by the vector field
`(a, w) ↦ (Pa, Pw)`; iterating it produces the polynomials of the whole jet of `psiInv`. -/
noncomputable def step (Q : MvPolynomial (Fin 2) ℝ) : MvPolynomial (Fin 2) ℝ :=
  pderiv 0 Q * Pa + pderiv 1 Q * Pw

/-- The evaluation point `(psiInv z, psig (psiInv z))`. -/
noncomputable def pair (z : ℝ) : Fin 2 → ℝ := ![psiInv z, psig (psiInv z)]

theorem key_C (c : ℝ) :
    ∀ y : ℝ, |y| < 1 → HasDerivAt (fun z : ℝ => MvPolynomial.eval (pair z) (MvPolynomial.C c))
        (MvPolynomial.eval (pair y) (step (MvPolynomial.C c))) y := by
  intro y hy
  rw [show (fun z : ℝ => MvPolynomial.eval (pair z) (MvPolynomial.C c)) = fun _ => c by
    funext z; simp]
  rw [show MvPolynomial.eval (pair y) (step (MvPolynomial.C c)) = 0 by simp [step]]
  exact hasDerivAt_const y c

/-- `HasDerivAt` of `psiInv` with the polynomial value `Pa`. -/
theorem hasDerivAt_psiInv' (y : ℝ) (hy : |y| < 1) :
    HasDerivAt psiInv (MvPolynomial.eval (pair y) Pa) y := by
  have hWne : psig (psiInv y) ≠ 0 := ne_of_gt (psig_pos _)
  have hrel : psig (psiInv y) ^ 2 * (1 + psiInv y ^ 2) = 1 := (psi_psig_algebra (psiInv y)).2.1
  have hev : MvPolynomial.eval (pair y) Pa = (psig (psiInv y) ^ 3)⁻¹ := by
    rw [show MvPolynomial.eval (pair y) Pa = ((1 + psiInv y ^ 2) * psig (psiInv y)) ^ 3 by
      simp [Pa, pair]]
    have h : (1 + psiInv y ^ 2) * psig (psiInv y) = (psig (psiInv y))⁻¹ := by
      field_simp
      nlinarith [hrel]
    rw [h, inv_pow]
  rw [hev]
  exact deriv_psiInv y hy

/-- `HasDerivAt` of `psig ∘ psiInv` with the polynomial value `Pw`. -/
theorem hasDerivAt_psig_psiInv (y : ℝ) (hy : |y| < 1) :
    HasDerivAt (fun z => psig (psiInv z)) (MvPolynomial.eval (pair y) Pw) y := by
  rw [show MvPolynomial.eval (pair y) Pw = -psiInv y by simp [Pw, pair]]
  have hder := deriv_psiInv y hy
  have hcomp := (hasDerivAt_psig (psiInv y)).comp y hder
  have hval : (-(WilkiesDesign.E.psi (psiInv y)) * psig (psiInv y) ^ 2) *
      (psig (psiInv y) ^ 3)⁻¹ = -psiInv y := by
    have hWne : psig (psiInv y) ≠ 0 := ne_of_gt (psig_pos _)
    rw [(psi_psig_algebra (psiInv y)).1]
    field_simp
  rw [hval] at hcomp
  simpa [Function.comp_def] using hcomp

theorem key_X0 :
    ∀ y : ℝ, |y| < 1 → HasDerivAt (fun z : ℝ => MvPolynomial.eval (pair z) (MvPolynomial.X 0))
        (MvPolynomial.eval (pair y) (step (MvPolynomial.X 0))) y := by
  intro y hy
  rw [show (fun z : ℝ => MvPolynomial.eval (pair z) (MvPolynomial.X 0)) = psiInv by
    funext z; simp [pair]]
  rw [show MvPolynomial.eval (pair y) (step (MvPolynomial.X 0)) = MvPolynomial.eval (pair y) Pa by
    simp [step]]
  exact hasDerivAt_psiInv' y hy

theorem key_X1 :
    ∀ y : ℝ, |y| < 1 → HasDerivAt (fun z : ℝ => MvPolynomial.eval (pair z) (MvPolynomial.X 1))
        (MvPolynomial.eval (pair y) (step (MvPolynomial.X 1))) y := by
  intro y hy
  rw [show (fun z : ℝ => MvPolynomial.eval (pair z) (MvPolynomial.X 1)) = fun z => psig (psiInv z) by
    funext z; simp [pair]]
  rw [show MvPolynomial.eval (pair y) (step (MvPolynomial.X 1)) = MvPolynomial.eval (pair y) Pw by
    simp [step]]
  exact hasDerivAt_psig_psiInv y hy

theorem key_X (n : Fin 2) :
    ∀ y : ℝ, |y| < 1 → HasDerivAt (fun z : ℝ => MvPolynomial.eval (pair z) (MvPolynomial.X n))
        (MvPolynomial.eval (pair y) (step (MvPolynomial.X n))) y := by
  have hn : n = 0 ∨ n = 1 := by
    fin_cases n
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hn with h | h
  · rw [h]; exact key_X0
  · rw [h]; exact key_X1

theorem key_add (p q : MvPolynomial (Fin 2) ℝ)
    (hp : ∀ y : ℝ, |y| < 1 → HasDerivAt (fun z : ℝ => MvPolynomial.eval (pair z) p)
        (MvPolynomial.eval (pair y) (step p)) y)
    (hq : ∀ y : ℝ, |y| < 1 → HasDerivAt (fun z : ℝ => MvPolynomial.eval (pair z) q)
        (MvPolynomial.eval (pair y) (step q)) y) :
    ∀ y : ℝ, |y| < 1 → HasDerivAt (fun z : ℝ => MvPolynomial.eval (pair z) (p + q))
        (MvPolynomial.eval (pair y) (step (p + q))) y := by
  intro y hy
  have hstep : step (p + q) = step p + step q := by simp only [step, map_add]; ring
  rw [show (fun z : ℝ => MvPolynomial.eval (pair z) (p + q)) =
      fun z => MvPolynomial.eval (pair z) p + MvPolynomial.eval (pair z) q by
    funext z; simp]
  rw [show MvPolynomial.eval (pair y) (step (p + q)) =
      MvPolynomial.eval (pair y) (step p) + MvPolynomial.eval (pair y) (step q) by
    rw [hstep, map_add]]
  exact (hp y hy).add (hq y hy)

theorem key_mul (p q : MvPolynomial (Fin 2) ℝ)
    (hp : ∀ y : ℝ, |y| < 1 → HasDerivAt (fun z : ℝ => MvPolynomial.eval (pair z) p)
        (MvPolynomial.eval (pair y) (step p)) y)
    (hq : ∀ y : ℝ, |y| < 1 → HasDerivAt (fun z : ℝ => MvPolynomial.eval (pair z) q)
        (MvPolynomial.eval (pair y) (step q)) y) :
    ∀ y : ℝ, |y| < 1 → HasDerivAt (fun z : ℝ => MvPolynomial.eval (pair z) (p * q))
        (MvPolynomial.eval (pair y) (step (p * q))) y := by
  intro y hy
  have hstep : step (p * q) = step p * q + p * step q := by
    simp only [step, pderiv_mul]; ring
  rw [show (fun z : ℝ => MvPolynomial.eval (pair z) (p * q)) =
      fun z => MvPolynomial.eval (pair z) p * MvPolynomial.eval (pair z) q by
    funext z; simp]
  rw [show MvPolynomial.eval (pair y) (step (p * q)) =
      MvPolynomial.eval (pair y) (step p) * MvPolynomial.eval (pair y) q +
        MvPolynomial.eval (pair y) p * MvPolynomial.eval (pair y) (step q) by
    rw [hstep]; simp]
  exact (hp y hy).mul (hq y hy)

/-- The coordinate derivative, polynomial in `Q`: on `|y| < 1` the function
`z ↦ eval (psiInv z, psig (psiInv z)) Q` has derivative `eval (psiInv y, psig (psiInv y)) (step Q)`.
Proved by the algebra induction `C`/`add`/`mul`. -/
theorem key (Q : MvPolynomial (Fin 2) ℝ) :
    ∀ y : ℝ, |y| < 1 → HasDerivAt (fun z : ℝ => MvPolynomial.eval (pair z) Q)
        (MvPolynomial.eval (pair y) (step Q)) y :=
  MvPolynomial.induction_on Q key_C key_add
    (fun p n hp => key_mul p (MvPolynomial.X n) hp (key_X n))

/-- Iterating the coordinate derivative: every iterated derivative of
`z ↦ eval (psiInv z, psig (psiInv z)) Q` is again of the same shape. -/
theorem iter (Q : MvPolynomial (Fin 2) ℝ) (j : ℕ) :
    ∃ Qj : MvPolynomial (Fin 2) ℝ, ∀ y : ℝ, |y| < 1 →
      iteratedDeriv j (fun z : ℝ => MvPolynomial.eval (pair z) Q) y =
        MvPolynomial.eval (pair y) Qj := by
  induction j with
  | zero => exact ⟨Q, fun y hy => by simp [iteratedDeriv_zero]⟩
  | succ j ih =>
    obtain ⟨Qj, hQj⟩ := ih
    refine ⟨step Qj, fun y hy => ?_⟩
    rw [iteratedDeriv_succ]
    have hmem : ({z : ℝ | |z| < 1} : Set ℝ) ∈ 𝓝 y :=
      (isOpen_Iio.preimage continuous_abs).mem_nhds hy
    have heq : (fun z : ℝ => iteratedDeriv j (fun z : ℝ => MvPolynomial.eval (pair z) Q) z)
        =ᶠ[𝓝 y] (fun z : ℝ => MvPolynomial.eval (pair z) Qj) :=
      Filter.eventually_of_mem hmem (fun z hz => hQj z hz)
    rw [heq.deriv_eq]
    exact (key Qj y hy).deriv

/-- **Every iterated derivative of `psiInv` is a polynomial in `(psiInv y, psig (psiInv y))`.**
Same induction as `psi_iteratedDeriv_poly`.  The reciprocal in `deriv_psiInv` is harmless: from
`psi_psig_algebra`, `psig a ^ 2 * (1 + a ^ 2) = 1` gives `(psig a)⁻¹ = (1 + a^2) * psig a`, so
the whole jet of `psiInv` lies in `ℝ[psiInv y, psig (psiInv y)]`.  This is the Faà di Bruno input
for the outer `ψ⁻¹` of the transport `f = ψ⁻¹ ∘ H ∘ ψ`. -/
theorem psiInv_iteratedDeriv_poly (j : ℕ) :
    ∃ P : MvPolynomial (Fin 2) ℝ, ∀ y : ℝ, |y| < 1 →
      iteratedDeriv j Work.WilE9.psiInv y =
        MvPolynomial.eval ![Work.WilE9.psiInv y, Work.WilE9.psig (Work.WilE9.psiInv y)] P := by
  obtain ⟨P, hP⟩ := iter (MvPolynomial.X 0) j
  refine ⟨P, fun y hy => ?_⟩
  have hg : (fun z : ℝ => MvPolynomial.eval (pair z) (MvPolynomial.X 0)) = Work.WilE9.psiInv := by
    funext z; simp [pair]
  have hiter : iteratedDeriv j Work.WilE9.psiInv
      = iteratedDeriv j (fun z : ℝ => MvPolynomial.eval (pair z) (MvPolynomial.X 0)) := by
    rw [hg]
  rw [hiter]
  exact hP y hy

end Work.WilE9.Psi
