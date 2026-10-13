import Mathlib
import Submission.Work.DSSER.Basic
import Submission.Work.DSSER.moduleFinite_serRing
import Submission.Work.DSEQP.BoxDefs
import Submission.Work.DSEQP.StdBasic
import Submission.Work.DSEQP.std_ker
import Submission.Work.DSEQP.boxMono_span

/-!
# `R[Z]/(Z_i^p - z_i)` is a free `R`-module

Let `B = MvPolynomial (Fin d) R`, `I = serRel R p z = (X_i ^ p - z_i)_i ⊆ B` and
`R' = serRing R p z = B ⧸ I`.  We show that `R'` is a free `R`-module, with basis the "box"
monomials `Z^u = ∏ i, Z i ^ (u i)`, `u : Fin d → Fin p` (the standard monomials of the ideal
`(X_i^p - z_i)`).

The two halves of the basis statement are

* `boxMono_span` (proved in `DSEQP/boxMono_span.lean`): the box monomials span `R'` over `R`,
  because `Z_i ^ p = z_i` rewrites every monomial into the box;
* `boxMono_linearIndependent` below: the box monomials are `R`-linearly independent.  This is
  proved with the `R`-linear "standard form" map `std` of `DSEQP/BoxDefs.lean`, which is a
  retraction: `std (X^u) = e_u` for box `u` (`std_boxIdx`) and `std` vanishes on `serRel`
  (`std_ker`).  Hence a relation `∑ u, c u • Z^u = 0` in `R'` lifts to an element
  `P = ∑ u, c u • X^u ∈ I`, on which `std` gives back `c`, so all `c u` vanish.

The main theorem is `serRing_free` at the bottom.
-/

namespace Work.DSEQP

open MvPolynomial

/-- The box monomials `Z^u`, `u : Fin d → Fin p`, are `R`-linearly independent in
`R[Z]/(Z_i^p - z_i)`. -/
theorem boxMono_linearIndependent (R : Type*) [CommRing R] (p : ℕ) (hp : 0 < p) {d : ℕ}
    (z : Fin d → R) : LinearIndependent R (boxMono R p z) := by
  have hker : ∀ x ∈ Work.DSSER.serRel R p z, std R p z x = 0 := fun x hx => std_ker R p hp z hx
  rw [Fintype.linearIndependent_iff]
  intro g hg u
  let mkL : MvPolynomial (Fin d) R →ₗ[R] Work.DSSER.serRing R p z :=
    (Ideal.Quotient.mkₐ R (Work.DSSER.serRel R p z)).toLinearMap
  have hmk : ∀ y : MvPolynomial (Fin d) R,
      mkL y = (Ideal.Quotient.mk (Work.DSSER.serRel R p z) y : Work.DSSER.serRing R p z) :=
    fun y => rfl
  have hbm : ∀ v : Fin d → Fin p,
      (Ideal.Quotient.mk (Work.DSSER.serRel R p z)
        (MvPolynomial.monomial (boxIdx v) 1) : Work.DSSER.serRing R p z)
        = boxMono R p z v := fun v => (boxMono_eq_mk R p z v).symm
  set P : MvPolynomial (Fin d) R := ∑ v, g v • MvPolynomial.monomial (boxIdx v) 1 with hP
  have hstd_sum : std R p z P =
      ∑ v : Fin d → Fin p, g v • Pi.single v (1 : R) := by
    rw [hP, map_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [map_smul, std_boxIdx]
  have hP0 : mkL P = 0 := by
    rw [hP, map_sum]
    have hterm : ∀ v : Fin d → Fin p, mkL (g v • MvPolynomial.monomial (boxIdx v) 1)
        = g v • boxMono R p z v := fun v => by rw [map_smul, hmk, hbm v]
    rw [Finset.sum_congr rfl (fun v _ => hterm v)]
    exact hg
  have hPmem : P ∈ Work.DSSER.serRel R p z := by
    rw [hmk] at hP0
    exact Ideal.Quotient.eq_zero_iff_mem.mp hP0
  have hstd : std R p z P = 0 := hker P hPmem
  have hsum_eval : (∑ v : Fin d → Fin p, g v • Pi.single v (1 : R)) u = g u := by
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq, Finset.mem_univ, reduceIte]
  calc g u = (∑ v : Fin d → Fin p, g v • Pi.single v (1 : R)) u := hsum_eval.symm
    _ = (std R p z P) u := by rw [← hstd_sum]
    _ = 0 := by rw [hstd]; rfl

theorem serRing_free (R : Type*) [CommRing R] (p : ℕ) (hp : 0 < p) {d : ℕ} (z : Fin d → R) :
    Module.Free R (Work.DSSER.serRing R p z) := by
  refine Module.Free.of_basis (Module.Basis.mk (boxMono_linearIndependent R p hp z) ?_)
  exact (boxMono_span R p hp z).ge

end Work.DSEQP
