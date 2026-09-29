import Mathlib
import Submission.Work.ADcl.asym_setup
import Submission.Work.CDcl.g_ode
import Submission.Work.CDcl.invsum
import Submission.Work.CDcl.order_raise
import Submission.Work.CDcl.xco_iter

namespace Work.ADcl

/-! Guidance (area ADcl of `cdt_linearIndependent`, Theorem A template).  This file should be in
`namespace Work.ADcl`.

`Work.ADcl.Gz a b c = Sym⁺(ZagierH a b c)` is the Theorem-A function `G(y)` of `defG`
(`sympSym = Sym⁺`), and `Work.ADcl.Tz a b c k = ((d/dy)^[k] G) ∘ y` its pullbacks along
`y = x²/(x-1)` (`Submission.CDT.sympY`).  Given a nontrivial `ℚ[x]`-relation among the five
pullbacks `Tz a b c 0, …, Tz a b c 4` (hypothesis `hrel`), produce an inhomogeneous order-four
`y`-ODE for `G` with polynomial coefficients and polynomial inhomogeneity.

This is exactly the second half of `Work.CDcl.g_ode` (`Submission/Work/CDcl/g_ode.lean`), which
does the same for Theorem C's `G = Sym⁺(logP …)`; here `G` is an arbitrary power series, so the
argument transfers verbatim.  The ingredients are:

* each `Tz a b c k` is fixed by the substitution `sympPhi` (`x ↦ x/(x-1)`), since
  `sympY.subst sympPhi = sympY` (`Submission.CDT.symp_y_invariant`; use
  `PowerSeries.subst_comp_subst_apply` with `sympPhi_hasSubst`, `sympY_hasSubst`) — this is
  `Work.CDcl.gode_T_invariant` verbatim;
* apply `PowerSeries.subst sympPhi` to both sides of `hrel` and add the result to `hrel`
  (`Work.CDcl.gode_subst_sum_phi` distributes the substitution over a finite sum);
* `Work.CDcl.inv_sum_aux` rewrites `P + P.subst sympPhi = ((P.sum (fun j c => C c * symPoly j)) :
  ℚ[y]) ∘ y` for every `P ∈ ℚ[x]`, so the symmetrised relation reads, with
  `D k = (Q k).sum (fun j c => Polynomial.C c * symPoly j) ∈ ℚ[y]`,
  `∑ k (D k)(y) * Tz a b c k = (c ∘ y)` as series in `x`;
* `Submission.CDT.symp_subst_y_injective` (injectivity of substitution by `sympY`) then gives
  `∑ k (D k)(y) * (d/dy)^[k] G = c` in `ℚ⟦y⟧` (use `Work.CDcl.gode_subst_sum_y` for the sum);
* `D ≠ 0` because `D = 0` forces `Q = 0` (`Work.CDcl.sympoly_map_eq_zero`), so the triviality
  case of the symmetrisation never happens;
* finally `Work.CDcl.order_raise` raises a nonzero relation of order `≤ 4` to a genuine order-four
  relation with nonzero leading coefficient (take `cc` to be the raised inhomogeneity). -/

open Polynomial PowerSeries

open scoped BigOperators

/-- `Tz a b c k` is fixed by the substitution `x ↦ x/(x-1)` (this is
`Work.CDcl.gode_T_invariant` verbatim, for the pullbacks `Tz` along `y`). -/
theorem Tz_invariant (a b c : ℚ) (k : ℕ) :
    (Tz a b c k).subst Submission.CDT.sympPhi = Tz a b c k := by
  unfold Tz
  rw [PowerSeries.subst_comp_subst_apply (R := ℚ) Submission.CDT.sympY_hasSubst
    Submission.CDT.sympPhi_hasSubst]
  rw [Submission.CDT.symp_y_invariant]

theorem y_ode_of_xrel (a b c : ℚ)
    (hrel : ∃ (Q : Fin 5 → Polynomial ℚ) (r : Polynomial ℚ), Q ≠ 0 ∧
      ∑ k : Fin 5, (Q k : PowerSeries ℚ) * Work.ADcl.Tz a b c k = (r : PowerSeries ℚ)) :
    ∃ (q : Polynomial ℚ) (A : Fin 4 → Polynomial ℚ) (cc : Polynomial ℚ), q ≠ 0 ∧
      (q : PowerSeries ℚ) * (PowerSeries.derivative (R := ℚ))^[4] (Work.ADcl.Gz a b c)
        = (∑ k : Fin 4, (A k : PowerSeries ℚ)
            * (PowerSeries.derivative (R := ℚ))^[k] (Work.ADcl.Gz a b c))
          + (cc : PowerSeries ℚ) := by
  obtain ⟨Q, r, hQ, hrel⟩ := hrel
  set D : Fin 5 → Polynomial ℚ :=
    fun k => (Q k).sum (fun j x => Polynomial.C x * Work.CDcl.symPoly j) with hDdef
  set cc : Polynomial ℚ := r.sum (fun j x => Polynomial.C x * Work.CDcl.symPoly j) with hcdef
  have hDne : D ≠ 0 := by
    intro h0
    apply hQ
    funext k
    have hk : (Q k).sum (fun j x => Polynomial.C x * Work.CDcl.symPoly j) = 0 := by
      have h1 : D k = 0 := by simp [h0]
      simpa [hDdef] using h1
    exact Work.CDcl.sympoly_map_eq_zero.mp hk
  have key : (∑ k : Fin 5, (D k : PowerSeries ℚ)
        * (PowerSeries.derivative (R := ℚ))^[k] (Gz a b c)) = (cc : PowerSeries ℚ) := by
    have hconj : (∑ k : Fin 5, (Q k : PowerSeries ℚ).subst Submission.CDT.sympPhi
          * Tz a b c k) = (r : PowerSeries ℚ).subst Submission.CDT.sympPhi := by
      have h1 := congrArg (fun z : PowerSeries ℚ => z.subst Submission.CDT.sympPhi) hrel
      rw [Work.CDcl.gode_subst_sum_phi] at h1
      have hterm : ∀ k : Fin 5,
          PowerSeries.subst Submission.CDT.sympPhi ((Q k : PowerSeries ℚ) * Tz a b c k)
            = (Q k : PowerSeries ℚ).subst Submission.CDT.sympPhi * Tz a b c k := by
        intro k
        rw [PowerSeries.subst_mul Submission.CDT.sympPhi_hasSubst, Tz_invariant]
      simpa only [hterm] using h1
    have hQk : ∀ k : Fin 5, ((Q k : PowerSeries ℚ)
          + (Q k : PowerSeries ℚ).subst Submission.CDT.sympPhi)
        = (D k : PowerSeries ℚ).subst Submission.CDT.sympY := by
      intro k
      simpa [hDdef] using Work.CDcl.inv_sum_aux (Q k)
    have hr : ((r : PowerSeries ℚ) + (r : PowerSeries ℚ).subst Submission.CDT.sympPhi)
        = (cc : PowerSeries ℚ).subst Submission.CDT.sympY := by
      simpa [hcdef] using Work.CDcl.inv_sum_aux r
    have hsum : (∑ k : Fin 5, ((Q k : PowerSeries ℚ)
            + (Q k : PowerSeries ℚ).subst Submission.CDT.sympPhi) * Tz a b c k)
        = (r : PowerSeries ℚ) + (r : PowerSeries ℚ).subst Submission.CDT.sympPhi := by
      have h : (∑ k : Fin 5, (Q k : PowerSeries ℚ) * Tz a b c k)
            + (∑ k : Fin 5, (Q k : PowerSeries ℚ).subst Submission.CDT.sympPhi
                * Tz a b c k)
          = (r : PowerSeries ℚ) + (r : PowerSeries ℚ).subst Submission.CDT.sympPhi := by
        rw [hrel, hconj]
      rw [← Finset.sum_add_distrib] at h
      have h2 : ∀ k : Fin 5, (Q k : PowerSeries ℚ) * Tz a b c k
              + (Q k : PowerSeries ℚ).subst Submission.CDT.sympPhi * Tz a b c k
            = ((Q k : PowerSeries ℚ) + (Q k : PowerSeries ℚ).subst Submission.CDT.sympPhi)
              * Tz a b c k := fun k => by ring
      simpa only [h2] using h
    have h4 : (∑ k : Fin 5, ((D k : PowerSeries ℚ).subst Submission.CDT.sympY)
          * Tz a b c k) = (cc : PowerSeries ℚ).subst Submission.CDT.sympY := by
      simpa only [hQk, hr] using hsum
    have hT : ∀ k : ℕ, Tz a b c k
        = ((PowerSeries.derivative (R := ℚ))^[k] (Gz a b c)).subst Submission.CDT.sympY :=
      fun k => rfl
    have h5 : (∑ k : Fin 5, (((D k : Polynomial ℚ) : PowerSeries ℚ)
            * (PowerSeries.derivative (R := ℚ))^[k] (Gz a b c)).subst Submission.CDT.sympY)
        = (cc : PowerSeries ℚ).subst Submission.CDT.sympY := by
      have hterm : ∀ k : Fin 5, ((D k : PowerSeries ℚ).subst Submission.CDT.sympY)
            * Tz a b c k
          = (((D k : Polynomial ℚ) : PowerSeries ℚ)
              * (PowerSeries.derivative (R := ℚ))^[k] (Gz a b c)).subst Submission.CDT.sympY := by
        intro k
        rw [hT, ← PowerSeries.subst_mul Submission.CDT.sympY_hasSubst]
      simpa only [hterm] using h4
    have h6 : ((∑ k : Fin 5, (D k : PowerSeries ℚ)
            * (PowerSeries.derivative (R := ℚ))^[k] (Gz a b c))).subst Submission.CDT.sympY
        = (cc : PowerSeries ℚ).subst Submission.CDT.sympY := by
      rw [← Work.CDcl.gode_subst_sum_y] at h5
      exact h5
    have h7 : (∑ k : Fin 5, (D k : PowerSeries ℚ)
            * (PowerSeries.derivative (R := ℚ))^[k] (Gz a b c)) - (cc : PowerSeries ℚ) = 0 := by
      apply Submission.CDT.symp_subst_y_injective
      rw [PowerSeries.subst_sub Submission.CDT.sympY_hasSubst, h6]
      ring
    exact sub_eq_zero.mp h7
  exact Work.CDcl.order_raise (Gz a b c) D cc hDne key

end Work.ADcl
