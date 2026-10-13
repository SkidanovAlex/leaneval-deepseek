import Mathlib
import Submission.Work.DSM2p.LamOne
import Submission.Work.DSM2p.PERFD_T
import Submission.Work.DSM2p.Lam1_frobInj
import Submission.Work.DSM2p.rootClosure_isSMulRegular

/-!
# The `p`-adic completion of `Λ = A[T^{1/p^∞}]` is perfectoid

This is node `N5a` of the M2p design, in the one-variable form: for a perfectoid ring `A` (given
by `DSMap.PerfectoidData p A`) the `p`-adic completion of `Λ = Lam1 A p = A[T^{1/p^∞}]` carries a
`DSMap.PerfectoidData p`-structure whose `ϖ`-system is the image of that of `A`.

The proof is the one-variable specialisation of the argument already used for the multi-variable
root algebra `RootAlg A p` in `PERFD_T` (module `Submission.Work.DSM2p.PERFD_T`):

* `p` is a nonzerodivisor on `Λ` (`rootClosure_isSMulRegular`, `p = 0` included), hence on its
  `p`-adic completion (`adicCompletion_isSMulRegular`);
* the completion is `(p)`-adically complete (`AdicCompletion.isAdicComplete`);
* Frobenius is an isomorphism mod `p`: surjectivity is `Lam1_frobSurj` below (transferred from
  `A` along `Λ ≃ₐ[A] A[M]`, `M` the monoid of root monomials, where `m ↦ m ^ p` is invertible),
  injectivity is `Lam1_frobInj` (`Submission.Work.DSM2p.Lam1_frobInj`); both survive `p`-adic
  completion (`adicCompletion_frobSurj`, `adicCompletion_frobInj`).
-/

open scoped Classical

namespace Work.DSM2p

universe u

/-- **Frobenius surjectivity modulo `p` for `Λ = A[T^{1/p^∞}]`.**  Every element of `Λ` is a
`p`-th power modulo `p`.  This is `rootAlg_frobSurj` (`PERFD_T`) at the one-point index set: under
`Λ ≃ₐ[A] A[M]` (`M` the monoid of root monomials, on which `m ↦ m ^ p` is inverted by the shift),
`MonoidAlgebra_frobSurjMod` transfers Frobenius surjectivity from `A`. -/
theorem Lam1_frobSurj (A : Type u) [CommRing A] (p : ℕ) [Fact p.Prime]
    (P : DSMap.PerfectoidData p A) :
    ∀ x : Lam1 A p, ∃ y : Lam1 A p, x - y ^ p ∈ Ideal.span {(p : Lam1 A p)} := by
  classical
  intro x
  let e := lam1EquivMonoidAlgebra A p
  obtain ⟨σ, hσ⟩ := rootClosureMonoid_shift p (Fact.out : p.Prime).pos PUnit.{u + 1}
  obtain ⟨w, hw⟩ :=
    MonoidAlgebra_frobSurjMod (Fact.out : p.Prime) (fun a => P.frobSurj a) σ hσ (e x)
  obtain ⟨c, hc⟩ := (Ideal.mem_span_singleton' (x := e x - w ^ p)
      (y := (p : MonoidAlgebra A (rootClosureMonoid p PUnit.{u + 1})))).mp hw
  refine ⟨e.symm w, ?_⟩
  have hx : x - (e.symm w) ^ p
      = e.symm (c * (p : MonoidAlgebra A (rootClosureMonoid p PUnit.{u + 1}))) := by
    rw [show x - (e.symm w) ^ p = e.symm (e x - w ^ p) from by
      simp only [map_sub, map_pow, AlgEquiv.symm_apply_apply], ← hc]
  rw [hx, map_mul, map_natCast]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

/-- **`N5a`, one-variable form.**  The `p`-adic completion `Λ̂` of `Λ = A[T^{1/p^∞}]` is
perfectoid, with a compatible `ϖ`-system given by the image of that of `A`. -/
theorem N5a_PERFD_Lam1_Q (A : Type*) [CommRing A] (p : ℕ) [Fact p.Prime]
    (P : DSMap.PerfectoidData p A) :
    ∃ Q : DSMap.PerfectoidData p
        (AdicCompletion (Ideal.span {(p : Lam1 A p)}) (Lam1 A p)),
      ∀ k, Q.ϖ k = algebraMap A
        (AdicCompletion (Ideal.span {(p : Lam1 A p)}) (Lam1 A p)) (P.ϖ k) := by
  classical
  set B := AdicCompletion (Ideal.span {(p : Lam1 A p)}) (Lam1 A p) with hB
  have htors : IsSMulRegular (Lam1 A p) (p : Lam1 A p) :=
    rootClosure_isSMulRegular A p _ P.torsionFree
  have hc : IsSMulRegular B (p : B) := adicCompletion_isSMulRegular htors
  have hcomplete : IsAdicComplete (Ideal.span {(p : B)}) B := by
    have hmap : (Ideal.span {(p : Lam1 A p)}).map (algebraMap (Lam1 A p) B)
        = Ideal.span {(p : B)} := by
      rw [Ideal.map_span, Set.image_singleton, map_natCast]
    rw [← hmap]
    exact (IsAdicComplete.map_algebraMap_iff (Ideal.span {(p : Lam1 A p)}) B).mpr
      (AdicCompletion.isAdicComplete (Submodule.fg_span_singleton (p : Lam1 A p)))
  have hunit : ∃ v : (Lam1 A p)ˣ, (algebraMap A (Lam1 A p) (P.ϖ 0)) ^ p
      = (p : Lam1 A p) * v := by
    obtain ⟨v, hv⟩ := P.unit
    refine ⟨Units.map (algebraMap A (Lam1 A p)) v, ?_⟩
    show (algebraMap A (Lam1 A p) (P.ϖ 0)) ^ p
      = (p : Lam1 A p) * algebraMap A (Lam1 A p) (v : A)
    rw [← map_pow, hv, map_mul, map_natCast]
  have hsurj := adicCompletion_frobSurj htors (Lam1_frobSurj A p P)
  have hinj := adicCompletion_frobInj (algebraMap A (Lam1 A p) (P.ϖ 0)) htors
    (Fact.out : p.Prime).pos hunit (Lam1_frobInj A p P)
  have hcompat : ∀ a : A, algebraMap (Lam1 A p) B (algebraMap A (Lam1 A p) a)
      = algebraMap A B a := by
    intro a
    rw [AdicCompletion.algebraMap_apply, AdicCompletion.algebraMap_apply,
      Algebra.algebraMap_self_apply]
  refine ⟨{
    ϖ := fun k => algebraMap A B (P.ϖ k)
    root := ?_
    unit := ?_
    torsionFree := hc
    complete := hcomplete
    frobSurj := hsurj
    frobInj := ?_ }, ?_⟩
  · intro k
    show (algebraMap A B (P.ϖ (k + 1))) ^ p = algebraMap A B (P.ϖ k)
    rw [← map_pow, P.root k]
  · obtain ⟨v, hv⟩ := P.unit
    refine ⟨Units.map (algebraMap A B) v, ?_⟩
    show (algebraMap A B (P.ϖ 0)) ^ p = (p : B) * algebraMap A B (↑v : A)
    rw [← map_pow, hv, map_mul, map_natCast]
  · intro y hy
    rw [show Ideal.span {algebraMap A B (P.ϖ 0)}
        = Ideal.span {algebraMap (Lam1 A p) B (algebraMap A (Lam1 A p) (P.ϖ 0))} from by
      rw [hcompat]]
    exact hinj y hy
  · intro k
    rfl

end Work.DSM2p
