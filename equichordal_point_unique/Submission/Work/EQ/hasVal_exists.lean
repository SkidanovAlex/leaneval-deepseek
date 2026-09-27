import Mathlib
import Submission.Work.EQ.germ_value_defs

namespace Work.EQ

open Polynomial

/-- If `A` vanishes at `w` to at least the order of vanishing of `C` at `w` (`C ≠ 0`), then the
rational function `A/C` has a value `L` at `w` in the sense of `HasVal`: after cancelling the
common factor `(X - C w)^(ord_w C)`, the reduced numerator takes a well-defined value at `w`
because the reduced denominator does not vanish there. -/
theorem hasVal_exists {A C : Polynomial ℂ} {w : ℂ} (hC : C ≠ 0)
    (h : (Polynomial.X - Polynomial.C w) ^ (C.rootMultiplicity w) ∣ A) :
    ∃ L, Work.EQ.HasVal A C w L := by
  set n := C.rootMultiplicity w with hn
  obtain ⟨B, hB⟩ := h
  obtain ⟨D, hD⟩ := Polynomial.pow_rootMultiplicity_dvd C w
  rw [← hn] at hD
  -- `C = (X - C w)^n * D` with `D w ≠ 0` (maximality of the root multiplicity).
  have hDval : D.eval w ≠ 0 := by
    intro hzero
    have hdvdD : (Polynomial.X - Polynomial.C w) ∣ D := by
      rw [Polynomial.dvd_iff_isRoot]; exact hzero
    obtain ⟨D', hD'⟩ := hdvdD
    have hdiv : (Polynomial.X - Polynomial.C w) ^ (n + 1) ∣ C := by
      refine ⟨D', ?_⟩
      rw [hD, hD', pow_succ]; ring
    exact (Polynomial.pow_rootMultiplicity_not_dvd hC w) (by rw [← hn]; exact hdiv)
  refine ⟨B.eval w / D.eval w, ?_⟩
  unfold Work.EQ.HasVal
  -- the reduced numerator `B - L*D` vanishes at `w` for `L = B w / D w`.
  have heval : (B - Polynomial.C (B.eval w / D.eval w) * D).eval w = 0 := by
    rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, div_mul_cancel₀ _ hDval,
      sub_self]
  have hdvd : (Polynomial.X - Polynomial.C w) ∣
      (B - Polynomial.C (B.eval w / D.eval w) * D) := by
    rw [Polynomial.dvd_iff_isRoot]; exact heval
  obtain ⟨R, hR⟩ := hdvd
  refine ⟨R, ?_⟩
  have step1 : A - Polynomial.C (B.eval w / D.eval w) * C
      = (Polynomial.X - Polynomial.C w) ^ n *
        (B - Polynomial.C (B.eval w / D.eval w) * D) := by
    rw [hB, hD]; ring
  rw [step1, hR, pow_succ]
  ring

end Work.EQ
