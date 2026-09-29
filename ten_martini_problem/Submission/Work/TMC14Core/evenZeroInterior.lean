import Mathlib
import Submission.Work.TMC14Core.Assembly
import Submission.Work.TMC14Core.discEven
import Submission.Work.TMC14Core.discRootsReal
import Submission.Work.TMC14Core.disc_im_eq_zero
import Submission.Work.TMC14Core.evenRootSign
import Submission.Work.TMC14Core.evenLocalBound

/-!
# TMC14Core: `0` is an interior point of the union spectrum for even denominator

For `q = 2m+2` (even `q`) and `gcd(p,q) = 1`, the discriminant `disc p q lam` is even, monic,
has all its roots real, and does not vanish at `0`.  Writing its positive roots as
`0 < a_1 < ... ` (with multiplicities), one has

  `disc p q lam = ∏_j (X² - a_j²)`,

so `disc(0) = (-1)^n ∏ a_j²` while `disc''(0) = 2 · disc(0) · f'(0)` with
`f = ∏_j (X - a_j²)`, giving `disc(0) · disc''(0) < 0`.  Consequently `0` is a point where
`‖disc‖` attains a local maximum, and since `‖disc(0)‖ = 2 + 2λ^q`, a whole neighbourhood of
`0` satisfies `‖disc(E)‖ ≤ 2 + 2λ^q`: the two central bands touch at `0`, so `0` lies in the
interior of the union spectrum of the rational approximant.

The two analytic/algebraic ingredients are proved separately in the modules
`Submission.Work.TMC14Core.evenRootSign` (the sign at `0`) and
`Submission.Work.TMC14Core.evenLocalBound` (the local bound from the sign).
-/

namespace Work.TMC14Core

/-- `disc p q lam` is monic (it is the characteristic polynomial of the `q × q` Bloch
matrix plus the constant `2`, and `charpoly` has degree `q ≥ 1 > 0`). -/
theorem disc_monic (p : ℤ) (q m : ℕ) (_hm : q = 2 * m + 2) (lam : ℝ) :
    (disc p q lam).Monic := by
  have hq : 1 ≤ q := by omega
  rw [disc]
  refine Polynomial.Monic.add_of_left (Matrix.charpoly_monic _) ?_
  rw [Polynomial.degree_C (by norm_num : (2:ℂ) ≠ 0), Matrix.charpoly_degree_eq_dim]
  simp
  omega

/-- The degree of `disc p q lam` is `q`. -/
theorem disc_natDegree (p : ℤ) (q m : ℕ) (_hm : q = 2 * m + 2) (lam : ℝ) :
    (disc p q lam).natDegree = q := by
  have hq : 1 ≤ q := by omega
  rw [disc]
  rw [Polynomial.natDegree_add_eq_left_of_degree_lt]
  · rw [Matrix.charpoly_natDegree_eq_dim]; simp
  · rw [Polynomial.degree_C (by norm_num : (2:ℂ) ≠ 0), Matrix.charpoly_degree_eq_dim]
    simp
    omega

/-- All roots of `disc p q lam` (for a reduced `p/q`) are real. -/
theorem disc_roots_real_le (p : ℤ) (q m : ℕ) (hm : q = 2 * m + 2) (hpq : Nat.Coprime p.natAbs q)
    (lam : ℝ) (hlam : 0 < lam) :
    ∀ z : ℂ, (disc p q lam).eval z = 0 → z.im = 0 := by
  have hq : 1 ≤ q := by omega
  intro z hz
  obtain ⟨x, hx⟩ := discRootsReal p q lam hpq hq hlam 0 (by simp; positivity) hz
  rw [hx]
  simp

/-- `disc p q lam` evaluated at `0` is nonzero under `hVal`. -/
theorem disc_eval_zero_ne_zero (p : ℤ) (q m : ℕ) (lam : ℝ) (_hlam : 0 < lam)
    (hVal : ‖(disc p q lam).eval (0 : ℂ)‖ = 2 + 2 * lam ^ q) :
    (disc p q lam).eval (0 : ℂ) ≠ 0 := by
  intro h
  rw [h, norm_zero] at hVal
  have : 0 < 2 + 2 * lam ^ q := by positivity
  linarith

theorem evenZeroInterior (p : ℤ) (q m : ℕ) (hm : q = 2 * m + 2) (hpq : Nat.Coprime p.natAbs q)
    (lam : ℝ) (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (hVal : ‖(disc p q lam).eval (0 : ℂ)‖ = 2 + 2 * lam ^ q) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ E : ℝ, |E| < δ → ‖(disc p q lam).eval (E : ℂ)‖ ≤ 2 + 2 * lam ^ q := by
  have hq : 1 ≤ q := by omega
  set P : Polynomial ℂ := disc p q lam with hP
  have hmonic : P.Monic := by rw [hP]; exact disc_monic p q m hm lam
  have hdeg : P.natDegree ≠ 0 := by
    rw [show P.natDegree = q from by rw [hP]; exact disc_natDegree p q m hm lam]; omega
  have heven : ∀ z : ℂ, P.eval (-z) = P.eval z := by
    intro z; rw [hP]; exact discEven p q m hm hpq lam z
  have hreal : ∀ z : ℂ, P.eval z = 0 → z.im = 0 := by
    intro z hz; rw [hP] at hz; exact disc_roots_real_le p q m hm hpq lam hlam z hz
  have h0 : P.eval 0 ≠ 0 := by
    rw [hP]; exact disc_eval_zero_ne_zero p q m lam hlam hVal
  have hsign := evenRootSign P hmonic hdeg heven hreal h0
  obtain ⟨him0, him2, hprod⟩ := hsign
  set c0 : ℝ := (P.eval 0).re with hc0def
  set c2 : ℝ := ((Polynomial.derivative (Polynomial.derivative P)).eval 0).re with hc2def
  have hc0 : P.eval 0 = (c0 : ℂ) := by
    apply Complex.ext
    · simp [hc0def]
    · simpa [hc0def] using him0
  have hc2 : (Polynomial.derivative (Polynomial.derivative P)).eval 0 = (c2 : ℂ) := by
    apply Complex.ext
    · simp [hc2def]
    · simpa [hc2def] using him2
  have hrealE : ∀ E : ℝ, (P.eval (E : ℂ)).im = 0 := by
    intro E; rw [hP]; exact disc_im_eq_zero p q lam E
  have hprod' : c0 * c2 < 0 := hprod
  obtain ⟨δ, hδpos, hδ⟩ := evenLocalBound P heven hrealE c0 c2 hc0 hc2 hprod'
  refine ⟨δ, hδpos, fun E hE => ?_⟩
  have h1 := hδ E hE
  rw [hP] at h1
  rw [hVal] at h1
  exact h1

end Work.TMC14Core
