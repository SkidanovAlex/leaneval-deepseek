/-
  WilE4 / CAD — vocabulary for the fibrewise CAD ("type localisation") development.

  A family of polynomials `P i ∈ ℝ[X₀,…,X_m]` (indexed by `Fin k`) is specialised to a family of
  univariate polynomials `q (P i) x` by evaluating the first `m` variables (`finSuccEquiv` makes the
  variable `X 0` the polynomial variable and `X (j+1)` the coefficient variable `X j`).  The
  realised-sign-vector set of the specialised family is `realized P x ·`.
-/
import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical
namespace Work.WilE4.CAD

open MvPolynomial Polynomial

variable {m k : ℕ}

/-- Specialisation of `P` to a univariate polynomial: the `finSuccEquiv` variable is kept, the
other `m` variables are evaluated at `x`. -/
def q (P : MvPolynomial (Fin (m+1)) ℝ) (x : Fin m → ℝ) : Polynomial ℝ :=
  (MvPolynomial.finSuccEquiv ℝ m P).map (MvPolynomial.eval x)

/-- Evaluation of the specialised polynomial is evaluation of `P` at `Fin.cons y x`. -/
theorem q_eval (P : MvPolynomial (Fin (m+1)) ℝ) (x : Fin m → ℝ) (y : ℝ) :
    (q P x).eval y = MvPolynomial.eval (Fin.cons y x) P := by
  rw [q, Polynomial.eval_map]
  have key : Polynomial.eval₂ (MvPolynomial.eval x) y ((MvPolynomial.finSuccEquiv ℝ m) P)
      = (MvPolynomial.eval x)
          (Polynomial.eval (MvPolynomial.C y) ((MvPolynomial.finSuccEquiv ℝ m) P)) := by
    conv_lhs => rw [show y = (MvPolynomial.eval x) (MvPolynomial.C y) from by simp]
    rw [Polynomial.eval₂_hom]
  rw [key]
  rw [MvPolynomial.eval_polynomial_eval_finSuccEquiv (x := x) P (MvPolynomial.C y)]
  simp only [MvPolynomial.eval_C]
  rw [show (fun i => Fin.cases y x i) = Fin.cons y x from by
        funext i; refine Fin.cases ?_ ?_ i <;> simp [Fin.cons]]

/-- Joint continuity of `(x, y) ↦ (q P x).eval y`. -/
theorem continuous_q_eval (P : MvPolynomial (Fin (m+1)) ℝ) :
    Continuous fun p : (Fin m → ℝ) × ℝ => (q P p.1).eval p.2 := by
  simp only [q_eval]
  have h1 : Continuous fun p : (Fin m → ℝ) × ℝ => (Fin.cons p.2 p.1 : Fin (m+1) → ℝ) := by
    rw [continuous_pi_iff]
    intro i
    refine Fin.cases ?_ ?_ i
    · exact continuous_snd
    · intro j
      exact (continuous_apply j).comp continuous_fst
  exact (MvPolynomial.continuous_eval P).comp h1

/-- Each coefficient of `q P x` is a continuous function of `x`. -/
theorem continuous_q_coeff (P : MvPolynomial (Fin (m+1)) ℝ) (j : ℕ) :
    Continuous fun x : Fin m → ℝ => (q P x).coeff j := by
  simp only [q, Polynomial.coeff_map]
  exact MvPolynomial.continuous_eval _

/-- Continuity of `x ↦ (q P x).eval y` for fixed `y`. -/
theorem continuous_q_eval_fixed (P : MvPolynomial (Fin (m+1)) ℝ) (y : ℝ) :
    Continuous fun x : Fin m → ℝ => (q P x).eval y := by
  have h1 : Continuous fun x : Fin m → ℝ => (Fin.cons y x : Fin (m+1) → ℝ) := by
    rw [continuous_pi_iff]
    intro i
    refine Fin.cases ?_ ?_ i
    · exact continuous_const
    · intro j
      exact continuous_apply j
  have h2 := (MvPolynomial.continuous_eval P).comp h1
  convert h2 using 1
  funext x
  exact q_eval P x y

/-- The non-degeneracy conditions of the fibrewise type-locality statement, at a single
parameter value `x`. -/
def Good (P : Fin k → MvPolynomial (Fin (m+1)) ℝ) (d : Fin k → ℕ) (x : Fin m → ℝ) : Prop :=
  (∀ i, (q (P i) x).natDegree = d i) ∧
    (∀ i j, i ≠ j → IsCoprime (q (P i) x) (q (P j) x)) ∧
      (∀ i, IsCoprime (q (P i) x) ((q (P i) x).derivative))

/-- `v` is a realised sign vector of the specialised family at `x`. -/
def realized (P : Fin k → MvPolynomial (Fin (m+1)) ℝ) (x : Fin m → ℝ)
    (v : Fin k → SignType) : Prop :=
  ∃ y, ∀ i, SignType.sign ((q (P i) x).eval y) = v i

/-- `Good` is (definitionally) a conjunction of the three hypotheses of the theorem. -/
theorem good_iff_eventual {P : Fin k → MvPolynomial (Fin (m+1)) ℝ} {d : Fin k → ℕ}
    {x₀ : Fin m → ℝ} :
    (∀ᶠ x in nhds x₀, Good P d x) ↔
      (∀ᶠ x in nhds x₀, ∀ i, (q (P i) x).natDegree = d i) ∧
      (∀ᶠ x in nhds x₀, ∀ i j, i ≠ j → IsCoprime (q (P i) x) (q (P j) x)) ∧
      (∀ᶠ x in nhds x₀, ∀ i, IsCoprime (q (P i) x) ((q (P i) x).derivative)) := by
  constructor
  · intro h
    exact ⟨h.mono (fun x hx => hx.1), h.mono (fun x hx => hx.2.1), h.mono (fun x hx => hx.2.2)⟩
  · rintro ⟨h1, h2, h3⟩
    exact (h1.and (h2.and h3)).mono (fun x hx => ⟨hx.1, hx.2.1, hx.2.2⟩)

end Work.WilE4.CAD
