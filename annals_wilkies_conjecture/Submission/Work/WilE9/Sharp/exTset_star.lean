import Mathlib
import Submission.Work.WilE9.Sharp.Vocab
import Submission.Work.WilE9.Sharp.exSemiPf_bounds
import Submission.Work.WilE9.Ift.OneShot.poly_eval_le
import Submission.Work.WilE8.StarOfSemipfLe.star_of_semipf_le

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace Work.WilE9.Sharp
open WilkiesDesign WilkiesDesign.E

/-! ## Packaging the extended set as a `*`-set

`exTset E L` is the projection of the extended semi-Pfaffian set `exSemiPf n m E L` to its first
`n + 1` coordinates, so the component bound `hE2` applies to it directly: the pieces of the
resulting `Star`-presentation are the `StarPiece` of the projected components, exactly as in
`Work.WilE8.StarOfSemipfLe.star_of_semipf_le`.  The only extra ingredient is the *degree*
bookkeeping: the extended system's format is bounded by `Next n a₀ + a₀` uniformly in `m ≤ a₀`
and its degree by the polynomial `b₀` of `exSemiPf_bounds`, so the `Star`-degree
`(hE2 a).choose.eval X.deg * X.deg` is bounded by the *two-variable* polynomial
`b := eval₂ C b₀ (q * X)` (the monomial `q.eval d · d` of the component bound, substituted along
`b₀`), evaluated at `(E.deg, |L|)`. -/

/-- Substituting a multivariate polynomial into a univariate polynomial with nonnegative integer
coefficients commutes with evaluation.  (`OneShot.mvpoly_eval_eval2` with the number of variables
left arbitrary, which lets `b₀ : MvPolynomial (Fin 3) ℕ` be substituted.) -/
theorem mvpoly_eval_eval₂_C {σ : Type*} (v : σ → ℕ) (d : MvPolynomial σ ℕ) (p : Polynomial ℕ) :
    MvPolynomial.eval v (Polynomial.eval₂ MvPolynomial.C d p) =
      p.eval (MvPolynomial.eval v d) := by
  rw [Polynomial.hom_eval₂]
  have h : (MvPolynomial.eval v).comp MvPolynomial.C = RingHom.id ℕ := by
    ext n
    simp
  rw [h, Polynomial.eval₂_id]

theorem exTset_star (hE2 : ∀ F : ℕ, ∃ p : Polynomial ℕ, ∀ (k : ℕ) (X : WilkiesDesign.E.SemiPf k),
      X.fmt ≤ F →
      ∃ s : Finset (Fin k → ℝ), s.card ≤ p.eval X.deg ∧ ↑s ⊆ X.set ∧
        ∀ x ∈ X.set, ∃ y ∈ s,
          connectedComponentIn X.set x = connectedComponentIn X.set y)
    (n a₀ : ℕ) : ∃ (a : ℕ) (b : MvPolynomial (Fin 3) ℕ),
    ∀ (m : ℕ) (E : Work.WilE9.Sharp.EffStratum n m) (L : List (Fin n)),
      m ≤ a₀ → E.X.fmt ≤ a₀ → E.X.basics.length ≤ E.X.deg + 1 →
      WilkiesDesign.E.Star a (MvPolynomial.eval ![E.deg, L.length, a₀] b) (n + 1)
        (Work.WilE9.Sharp.exTset E L) := by
  classical
  obtain ⟨b₀, hb₀⟩ := exSemiPf_bounds n a₀
  refine ⟨Next n a₀ + a₀,
    Polynomial.eval₂ MvPolynomial.C b₀ ((hE2 (Next n a₀ + a₀)).choose * Polynomial.X), ?_⟩
  intro m E L hm hfmt hlen
  -- the format of the extended system is bounded by the fixed budget `Next n a₀ + a₀`
  have hfmt' : (exSemiPf n m E L).fmt ≤ Next n a₀ + a₀ := by
    have h1 : Next n m ≤ Next n a₀ := by simp [Next]; omega
    have h2 : E.X.r ≤ a₀ := by
      have h := hfmt
      simp only [SemiPf.fmt] at h
      omega
    show Next n m + E.X.r ≤ Next n a₀ + a₀
    omega
  obtain ⟨-, hdeg_b⟩ := hb₀ m E L hm hfmt hlen
  -- the component bound for the extended system
  have hstar := Work.WilE8.StarOfSemipfLe.star_of_semipf_le hE2 (n + 1) (n + m + 3)
    (Next n a₀ + a₀) (exSemiPf n m E L) hfmt'
  -- and its degree, substituted into the monomial `q.eval d · d`
  have hmul : (hE2 (Next n a₀ + a₀)).choose.eval (exSemiPf n m E L).deg *
        (exSemiPf n m E L).deg ≤
      MvPolynomial.eval ![E.deg, L.length, a₀]
        (Polynomial.eval₂ MvPolynomial.C b₀
          ((hE2 (Next n a₀ + a₀)).choose * Polynomial.X)) := by
    rw [mvpoly_eval_eval₂_C, Polynomial.eval_mul, Polynomial.eval_X]
    exact Nat.mul_le_mul (Work.WilE9.Ift.OneShot.poly_eval_le hdeg_b) hdeg_b
  have hstar' : Star (Next n a₀ + a₀)
      ((hE2 (Next n a₀ + a₀)).choose.eval (exSemiPf n m E L).deg *
        (exSemiPf n m E L).deg) (n + 1) (exTset E L) := hstar
  exact Work.WilE8.Star.mono hstar' le_rfl hmul

end Work.WilE9.Sharp
