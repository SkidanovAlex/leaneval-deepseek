/-
Copyright: subproject `Submission/Work/FBif/` of `mandelbar_not_path_connected`.

# `Work.FBif` — the algebra of antipolynomials (FBif, part 0b)

Basic closure properties of `Antipoly` (functions of the form `z ↦ P(z̄)`), used to see that the
iterates of `Tantibar c` and the perturbed maps `perturb c q ε` are again antipolynomials (of
bounded antidegree).
-/
import Submission.Work.FBif.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set Function
open scoped Topology

noncomputable section

namespace Work.FBif

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

theorem antipoly_conj : Antipoly (star : ℂ → ℂ) := ⟨Polynomial.X, by intro z; simp⟩

theorem Antipoly.const (c : ℂ) : Antipoly (fun _ : ℂ => c) :=
  ⟨Polynomial.C c, by intro z; simp⟩

theorem Antipoly.add {q r : ℂ → ℂ} (hq : Antipoly q) (hr : Antipoly r) : Antipoly (q + r) := by
  obtain ⟨P, hP⟩ := hq
  obtain ⟨Q, hQ⟩ := hr
  refine ⟨P + Q, fun z => ?_⟩
  show q z + r z = (P + Q).eval (star z)
  rw [hP z, hQ z, Polynomial.eval_add]

theorem Antipoly.mul {q r : ℂ → ℂ} (hq : Antipoly q) (hr : Antipoly r) : Antipoly (q * r) := by
  obtain ⟨P, hP⟩ := hq
  obtain ⟨Q, hQ⟩ := hr
  refine ⟨P * Q, fun z => ?_⟩
  show q z * r z = (P * Q).eval (star z)
  rw [hP z, hQ z, Polynomial.eval_mul]

theorem Antipoly.neg {q : ℂ → ℂ} (hq : Antipoly q) : Antipoly (-q) := by
  obtain ⟨P, hP⟩ := hq
  refine ⟨-P, fun z => ?_⟩
  show -q z = (-P).eval (star z)
  rw [hP z, Polynomial.eval_neg]

theorem Antipoly.sub {q r : ℂ → ℂ} (hq : Antipoly q) (hr : Antipoly r) : Antipoly (q - r) := by
  simpa [sub_eq_add_neg] using hq.add hr.neg

theorem Antipoly.smul {q : ℂ → ℂ} (hq : Antipoly q) (a : ℂ) : Antipoly (a • q) := by
  obtain ⟨P, hP⟩ := hq
  refine ⟨Polynomial.C a * P, fun z => ?_⟩
  show a * q z = (Polynomial.C a * P).eval (star z)
  rw [hP z, Polynomial.eval_mul, Polynomial.eval_C]

theorem antipoly_tantibar (c : ℂ) : Antipoly (Tantibar c) := by
  refine ⟨Polynomial.X ^ 2 + Polynomial.C c, fun z => ?_⟩
  show (star z) ^ 2 + c = (Polynomial.X ^ 2 + Polynomial.C c).eval (star z)
  rw [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]

/-- A *single* antipolynomial is antiholomorphic, so its square is holomorphic: `q^[2]` is a
polynomial function.  (The odd iterates of `q` are again antipolynomials; we record only the
case needed downstream.) -/
theorem Antipoly.sq_holomorphic {q : ℂ → ℂ} (hq : Antipoly q) :
    ∃ H : Polynomial ℂ, ∀ z : ℂ, (q^[2]) z = H.eval z := by
  obtain ⟨P, hP⟩ := hq
  refine ⟨P.comp (P.map (starRingEnd ℂ)), fun z => ?_⟩
  have h1 : (q^[2]) z = q (q z) := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_succ_apply', Function.iterate_one]
  rw [h1, hP, hP, Polynomial.eval_comp, Polynomial.eval_map]
  congr 1
  simpa using (Polynomial.eval₂_at_apply (starRingEnd ℂ) (star z) (p := P)).symm

/-- The perturbed map of HS Lemma 3.4 is an antipolynomial. -/
theorem antipoly_perturb {c : ℂ} {q : ℂ → ℂ} (hq : Antipoly q) (ε : ℝ) :
    Antipoly (perturb c q ε) := by
  have h : perturb c q ε = Tantibar c + fun z : ℂ => (ε : ℂ) * q z := by
    funext z; simp [perturb]
  rw [h]
  exact (antipoly_tantibar c).add ((Antipoly.const (ε : ℂ)).mul hq)

end Work.FBif

end
