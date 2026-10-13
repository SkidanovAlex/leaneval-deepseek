/-
DSEQP: the box monomials `Z^u = ∏ i, Z i ^ (u i : ℕ)` (`u : Fin d → Fin p`) span the
`R`-algebra `R' = R[Z]/(Z_i ^ p - z_i) = Work.DSSER.serRing R p z` as an `R`-module.

The argument is the division algorithm for the monic relations `Z_i ^ p - z_i`: writing
`s i = p * (s i / p) + s i % p` and using `Z_i ^ p = z_i`, the image of any monomial `X^s` is

  `z ^ (s / p) · Z ^ (s % p)`,

a scalar multiple of a box monomial (`mk_monomial_mem_span`).  Since the monomials form an
`R`-basis of `MvPolynomial (Fin d) R` and the quotient map is surjective and `R`-linear, every
element of `R'` is an `R`-linear combination of box monomials.
-/
import Mathlib
import Submission.Work.DSEQP.BoxDefs
import Submission.Work.DSEQP.StdBasic
import Submission.Work.DSSER.Basic

universe u

namespace Work.DSEQP

open MvPolynomial

/-- The quotient map `R[X_1,…,X_d] → R' = R[Z]/(Z_i ^ p - z_i)`, as an `R`-linear map. -/
noncomputable def serMkQ (R : Type u) [CommRing R] (p : ℕ) {d : ℕ} (z : Fin d → R) :
    MvPolynomial (Fin d) R →ₗ[R] Work.DSSER.serRing R p z :=
  (Ideal.Quotient.mkₐ R (Work.DSSER.serRel R p z)).toLinearMap

theorem serMkQ_apply (R : Type u) [CommRing R] (p : ℕ) {d : ℕ} (z : Fin d → R)
    (f : MvPolynomial (Fin d) R) :
    serMkQ R p z f =
      (Ideal.Quotient.mk (Work.DSSER.serRel R p z) f : Work.DSSER.serRing R p z) :=
  rfl

/-- Scalar multiplication in `R' = R[Z]/(Z_i ^ p - z_i)` is multiplication by the image of the
scalar.  (The `R`-module structure on the quotient ring is the one induced by the quotient of the
`R`-module `R[X]`, which is *definitionally* the one coming from the algebra structure.) -/
theorem serRing_smul_def (R : Type u) [CommRing R] (p : ℕ) {d : ℕ} (z : Fin d → R) (r : R)
    (x : Work.DSSER.serRing R p z) :
    r • x = algebraMap R (Work.DSSER.serRing R p z) r * x :=
  Algebra.smul_def r x

/-- Division of a monomial by the relations: in `R' = R[Z]/(Z_i ^ p - z_i)` the image of `X^s`
is the scalar `z ^ (s / p)` times the box monomial `Z ^ (s % p)`.  In particular it lies in the
`R`-span of the box monomials. -/
theorem mk_monomial_mem_span {R : Type u} [CommRing R] {p : ℕ} (hp : 0 < p) {d : ℕ}
    {z : Fin d → R} (s : Fin d →₀ ℕ) :
    ((Ideal.Quotient.mk (Work.DSSER.serRel R p z) (MvPolynomial.monomial s 1) :
        Work.DSSER.serRing R p z)) ∈ Submodule.span R (Set.range (boxMono R p z)) := by
  have h1 : ((Ideal.Quotient.mk (Work.DSSER.serRel R p z) (MvPolynomial.monomial s 1) :
        Work.DSSER.serRing R p z)) = Work.DSSER.serZpow p z s :=
    mk_monomial R p z s
  have h2 : Work.DSSER.serZpow p z s =
      (Work.DSSER.zMono z (fun i => s i / p)) •
        boxMono R p z (fun i => (⟨s i % p, Nat.mod_lt _ hp⟩ : Fin p)) := by
    rw [Work.DSSER.serZpow_div_mod (w := s)]
    rw [show Work.DSSER.serZpow p z (fun i => s i % p)
        = boxMono R p z (fun i => (⟨s i % p, Nat.mod_lt _ hp⟩ : Fin p)) from rfl]
    rw [mul_comm]
    exact (serRing_smul_def R p z _ _).symm
  rw [h1, h2]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

theorem boxMono_span (R : Type*) [CommRing R] (p : ℕ) (hp : 0 < p) {d : ℕ} (z : Fin d → R) :
    Submodule.span R (Set.range (Work.DSEQP.boxMono R p z)) = ⊤ := by
  -- the quotient map is surjective, so it maps `⊤` onto `⊤`
  have htop : Submodule.map (serMkQ R p z) ⊤ = ⊤ := by
    rw [Submodule.map_top, LinearMap.range_eq_top]
    intro y
    obtain ⟨f, hf⟩ := Ideal.Quotient.mkₐ_surjective R (Work.DSSER.serRel R p z) y
    exact ⟨f, hf⟩
  refine le_antisymm le_top ?_
  rw [← htop, ← Module.Basis.span_eq (MvPolynomial.basisMonomials (Fin d) R),
    Submodule.map_span, Submodule.span_le]
  rintro y ⟨s, ⟨t, rfl⟩, rfl⟩
  exact mk_monomial_mem_span (R := R) (p := p) hp (z := z) t

end Work.DSEQP
