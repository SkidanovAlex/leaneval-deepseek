/-
Copyright: subproject `Submission/Work/FatouDeg/` of `mandelbar_not_path_connected`.

# The normal form `N_{m,G}(w) = w - w^m + w^(m+1) G(w)` as a polynomial map

The output of `Work.FatouDeg.normalizeDeg` is a polynomial `N_{m,G}`; this file records the three
elementary facts about it that the assembly of `fatouParabolicInput_degenerate` consumes:

* `nf_isPoly` — `N_{m,G}` is a polynomial map of degree `≥ 2` (so that the Liouville/covering step
  `Work.MultiPetal.criticalOrbitInPetalNoPre` applies to it);
* `nf_zero` — `N_{m,G} 0 = 0`;
* `nf_deriv_zero` — `deriv N_{m,G} 0 = 1`.

All three need only `3 ≤ m`; the sharp case is `G = 0`, `m = 3`, where `N = X - X^3`.
-/
import Mathlib
import Submission.Work.FatouParabolic.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Polynomial

namespace Work.FatouDeg

noncomputable section

/-- The normal form polynomial `X - X^m + X^(m+1) * G`. -/
def nfPoly (m : ℕ) (G : Polynomial ℂ) : Polynomial ℂ :=
  Polynomial.X - Polynomial.X ^ m + Polynomial.X ^ (m + 1) * G

/-- The normal form map `w ↦ w - w^m + w^(m+1) G(w)`. -/
def nf (m : ℕ) (G : Polynomial ℂ) : ℂ → ℂ := fun w => (nfPoly m G).eval w

/-- `nf` is the evaluation of `nfPoly`, i.e. of the polynomial written out in the statement of
`Work.FatouDeg.normalizeDeg`. -/
theorem nf_apply (m : ℕ) (G : Polynomial ℂ) (w : ℂ) :
    nf m G w = (Polynomial.X - Polynomial.X ^ m + Polynomial.X ^ (m + 1) * G).eval w := rfl

/-- The polynomial `nfPoly m G` has degree at least two, hence at least three: its `m`-th
coefficient is `-1` and `m ≥ 3`. -/
theorem nfPoly_coeff_m (m : ℕ) (hm : 3 ≤ m) (G : Polynomial ℂ) : (nfPoly m G).coeff m = -1 := by
  have hdiv : (Polynomial.X ^ (m + 1) * G : Polynomial ℂ).coeff m = 0 :=
    (Polynomial.X_pow_dvd_iff.mp (dvd_mul_right _ _)) m (by omega)
  rw [nfPoly, Polynomial.coeff_add, Polynomial.coeff_sub, hdiv, Polynomial.coeff_X,
    Polynomial.coeff_X_pow]
  simp only [ite_eq_right (by omega : ¬ (1 = m))]
  norm_num

theorem nfPoly_natDegree (m : ℕ) (hm : 3 ≤ m) (G : Polynomial ℂ) : 2 ≤ (nfPoly m G).natDegree := by
  have hne : (nfPoly m G).coeff m ≠ 0 := by rw [nfPoly_coeff_m m hm G]; norm_num
  have := Polynomial.le_natDegree_of_ne_zero hne
  omega

/-- **The normal form is a polynomial map of degree at least two.** -/
theorem nf_isPoly (m : ℕ) (hm : 3 ≤ m) (G : Polynomial ℂ) :
    Work.FatouParabolic.IsPolynomialMapOfDegreeAtLeastTwo (nf m G) :=
  ⟨nfPoly m G, nfPoly_natDegree m hm G, fun _ => rfl⟩

theorem nf_zero (m : ℕ) (hm : 3 ≤ m) (G : Polynomial ℂ) : nf m G 0 = 0 := by
  rw [nf_apply]
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_pow]
  rw [zero_pow (by omega : m ≠ 0), zero_pow (by omega : m + 1 ≠ 0)]
  ring

theorem nf_deriv_zero (m : ℕ) (hm : 3 ≤ m) (G : Polynomial ℂ) : deriv (nf m G) 0 = 1 := by
  have heval : ∀ w : ℂ, nf m G w = (nfPoly m G).eval w := fun _ => rfl
  rw [show deriv (nf m G) 0 = deriv (fun w => (nfPoly m G).eval w) 0 from rfl]
  rw [(Polynomial.hasDerivAt (nfPoly m G) 0).deriv, nfPoly]
  simp only [Polynomial.derivative_add, Polynomial.derivative_sub, Polynomial.derivative_X_pow,
    Polynomial.derivative_mul, Polynomial.derivative_X]
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_one, Polynomial.eval_X, Polynomial.eval_pow]
  rw [zero_pow (by omega : m - 1 ≠ 0), zero_pow (by omega : m + 1 - 1 ≠ 0),
    zero_pow (by omega : m + 1 ≠ 0)]
  ring

end

end Work.FatouDeg
