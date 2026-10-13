import Mathlib
import Submission.Work.DSM2p.LamOne
import Submission.Work.DSM2p.Basic
import Submission.Work.DSM2p.PERFD_T
import Submission.Work.DSM2p.rootClosure_algEquiv_monoidAlgebra

/-!
# Frobenius injectivity for the root ring `Λ = A[T^{1/p^∞}]`

`Λ = Lam1 A p = rootClosure A p PUnit` is the root-system ring `A[T^{1/p^∞}]`.  The target is

`Lam1_frobInj`: if `P : PerfectoidData p A` and `y ^ p ∈ (p)` in `Λ`, then
`y ∈ (ϖ) Λ`, where `ϖ = P.ϖ 0` and `(p) = (ϖ ^ p)`.

The proof is the same transfer used for the root algebra `RootAlg A p` in `PERFD_T.lean`
(`rootAlg_frobInj`), specialised to the one-variable index set `PUnit`:

* `Λ = rootClosure A p ι ≃ₐ[A] A[M]` is the monoid algebra of its monoid of root monomials
  `M = rootClosureMonoid p ι` (`rootClosure_algEquiv_monoidAlgebra`);
* `MonoidAlgebra_frobInjMod` (already proved in `PERFD_T.lean`) transfers Frobenius injectivity
  modulo `p` from `A` to `A[M]`, using that `m ↦ m ^ p` is injective on `M`; the latter is
  `rootClosureMonoid_pow_injective`, since the shift `x_{i,n} ↦ x_{i,n+1}` is a left inverse of
  the `p`-th power map;
* the `A`-algebra equivalence transports the hypothesis `y ^ p ∈ (p)` to `e y` and the conclusion
  back, using `P.frobInj` for `A`.
-/

open scoped Classical

namespace Work.DSM2p

universe u

/-- The root-system ring `Λ = A[T^{1/p^∞}]` as the monoid algebra of its monoid of root
monomials.  (This is `rootClosure_algEquiv_monoidAlgebra` at the one-point index set, packaged as
a computable choice so that it can be named inside the target statement where `A`'s universe is
implicit.) -/
noncomputable def lam1EquivMonoidAlgebra (A : Type u) [CommRing A] (p : ℕ) :
    Lam1 A p ≃ₐ[A] MonoidAlgebra A (rootClosureMonoid p (PUnit.{u + 1})) :=
  Classical.choice (rootClosure_algEquiv_monoidAlgebra A p PUnit.{u + 1})

/-- **Frobenius injectivity modulo `p` for `Λ = A[T^{1/p^∞}]`.**  If `y ^ p` is divisible by `p`
in `Λ` then `y` is divisible by `ϖ = P.ϖ 0`. -/
theorem Lam1_frobInj (A : Type*) [CommRing A] (p : ℕ) [Fact p.Prime]
    (P : DSMap.PerfectoidData p A) (y : Lam1 A p)
    (hy : y ^ p ∈ Ideal.span {(p : Lam1 A p)}) :
    y ∈ Ideal.span {algebraMap A (Lam1 A p) (P.ϖ 0)} := by
  classical
  let e := lam1EquivMonoidAlgebra A p
  -- transfer `y ^ p ∈ (p)` to the monoid-algebra model
  have hy' : (e y) ^ p ∈ Ideal.span {(p : MonoidAlgebra A (rootClosureMonoid p PUnit))} := by
    obtain ⟨u, hu⟩ := Ideal.mem_span_singleton.mp hy
    refine Ideal.mem_span_singleton.mpr ⟨e u, ?_⟩
    rw [show (e y) ^ p = e (y ^ p) from (map_pow e y p).symm, hu, map_mul]
    congr 1
    exact map_natCast e p
  -- Frobenius injectivity in the monoid algebra
  have hw : e y ∈
      Ideal.span {algebraMap A (MonoidAlgebra A (rootClosureMonoid p PUnit)) (P.ϖ 0)} :=
    MonoidAlgebra_frobInjMod (Fact.out : p.Prime)
      (rootClosureMonoid_pow_injective p (Fact.out : p.Prime).pos PUnit)
      (P.ϖ 0) (fun a ha => P.frobInj a ha) (e y) hy'
  -- transfer the conclusion back along `e`
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton.mp hw
  refine Ideal.mem_span_singleton.mpr ⟨e.symm u, ?_⟩
  have h2 := congrArg e.symm hu
  rw [map_mul, AlgEquiv.symm_apply_apply, AlgEquiv.commutes e.symm (P.ϖ 0)] at h2
  exact h2

end Work.DSM2p
