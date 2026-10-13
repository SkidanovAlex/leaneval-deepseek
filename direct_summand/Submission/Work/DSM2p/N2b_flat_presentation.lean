import Mathlib
import Submission.Work.DSM2p.LamOne
import Submission.Work.DSM2p.ureg_isSMulRegular
import Submission.Work.DSM2p.N1_monic_isSMulRegular_quot
import Submission.Work.DSM2p.rootClosure_flat
import Submission.Work.DSM2p.N2a_flat_quot_span_singleton_of_regular
import Submission.Work.DSM2p.N2b_regular_mod_ideals

/-!
# Node N2b: `Λ[X]/(π^e X - q)` is `A`-flat (UREG flatness)

Let `A` be a commutative ring, `p` a prime, `Λ = Lam1 A p = A[T^{1/p^∞}]` the one-variable
root-system ring, `π ∈ A`, `e ∈ ℕ`, `q ∈ Λ`, and let `g ∈ A[X]` be monic with

`q - g(T^{1/p^n}) ∈ (π)  ⊆ Λ`.

Then the `Λ`-algebra `Λ[X]/(π^e X - q)` is **flat over `A`**.

This is node `N2b` of the design `sources/dsmap/direct_summand_m2p_h2_design.md`; it produces
the flat pieces `Λ[q_j/ϖ_j^m]` that `pIntClosure_iSup`/`N7` glue into `A'_F`, hence into
`CSCompletionPos_faithfullyFlat` (H2) and, ultimately, the direct summand theorem.

## The argument

1. `Λ` is `A`-flat (`rootClosure_flat`), and `Λ[X]` is free over `Λ`, hence `A`-flat
   (`Module.Flat.trans`, `flat_polynomial_lam1`).
2. Put `f = C(π^e)·X - C q ∈ Λ[X]`.  `f` is a non-zero-divisor *modulo every ideal* `I·Λ[X]`:
   reduce modulo `I·Λ[X]`, i.e. pass to `(Λ/IΛ)[X]` along
   `Ideal.polynomialQuotientEquivQuotientPolynomial`.  There `f` becomes `C(π̄^e)·X - C q̄` with
   `q̄ - g(T^{1/p^n})‾ ∈ (π̄)`, while `g(T^{1/p^n})‾` is a non-zero-divisor (`N1`, supplied here as
   the explicit hypothesis `hmr` of `N2b_regular_mod_ideals`); thus `ureg_isSMulRegular` applies.
   This is `Work.DSM2p.N2b_regular_mod_ideals`.
3. `C` flat over `A` together with that regularity gives flatness of `Λ[X]/(f)`:
   `Work.DSM2p.flat_quot_span_singleton_of_regular` (node `N2a`), whose proof is the purity
   criterion `flat_of_ker_inf_smul_top_eq_smul`.
-/

namespace Work.DSM2p

/-- `Λ[X] = Polynomial (Lam1 A p)` is flat over `A`: it is free over `Λ`, and `Λ` is `A`-flat. -/
theorem flat_polynomial_lam1 (A : Type*) [CommRing A] (p : ℕ) :
    Module.Flat A (Polynomial (Lam1 A p)) := by
  haveI : Module.Flat A (Lam1 A p) := rootClosure_flat A p PUnit
  exact Module.Flat.trans A (Lam1 A p) (Polynomial (Lam1 A p))

theorem N2b_flat_presentation (A : Type*) [CommRing A] (p : ℕ) [Fact p.Prime]
    (π : A) (e : ℕ) (q : Lam1 A p) (n : ℕ) (g : Polynomial A) (hg : g.Monic)
    (hq : q - Polynomial.aeval (T1 A p n) g ∈ Ideal.span {algebraMap A (Lam1 A p) π}) :
    Module.Flat A (Polynomial (Lam1 A p) ⧸ Ideal.span
      {Polynomial.C (algebraMap A (Lam1 A p) π ^ e) * Polynomial.X - Polynomial.C q}) := by
  haveI : Module.Flat A (Polynomial (Lam1 A p)) := flat_polynomial_lam1 A p
  -- `f = π^e X - q` is a non-zero-divisor modulo every `I·Λ[X]`; the regularity of
  -- `g(T^{1/p^n})` modulo every `I·Λ` is node `N1`.
  have hreg := N2b_regular_mod_ideals A p π e q n g hq
    (fun I => N1_monic_isSMulRegular_quot A p I n g hg)
  exact flat_quot_span_singleton_of_regular (R := A) (C := Polynomial (Lam1 A p))
    (Polynomial.C (algebraMap A (Lam1 A p) π ^ e) * Polynomial.X - Polynomial.C q) hreg

end Work.DSM2p
