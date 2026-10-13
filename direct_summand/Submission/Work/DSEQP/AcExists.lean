import Mathlib
import Submission.Work.DSEQP.AcDefs

open CategoryTheory AlgebraicGeometry Limits Opposite
open scoped Simplicial BigOperators

namespace Work.DSEQP

universe u

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- Finitely many elements of a perfection admit a common level: for a finite family
`z : α → Perf R p hp` there is a single level `e` and lifts `x a ∈ R` with
`of e (x a) = z a` for all `a`. -/
theorem Perf.exists_common_level {R : Type u} [CommRing R] {p : ℕ} [Fact p.Prime]
    (hp : (p : R) = 0) {α : Type u} [Finite α] (z : α → Perf R p hp) :
    ∃ (e : ℕ) (x : α → R), ∀ a, Perf.of R p hp e (x a) = z a := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  choose e xe hxe using fun a => Perf.exists_of (R := R) (p := p) (hp := hp) (z a)
  refine ⟨Finset.univ.sup e, fun a => xe a ^ p ^ (Finset.univ.sup e - e a), fun a => ?_⟩
  exact (Perf.of_f (R := R) (p := p) (hp := hp) (i := e a) (j := Finset.univ.sup e)
    (Finset.le_sup (Finset.mem_univ a)) (xe a)).trans (hxe a)

open PerfSetup

theorem AcExists {A : Type} [CommRing A] {p : ℕ} [Fact p.Prime] {X : AlgebraicGeometry.Scheme}
    [AlgebraicGeometry.IsIntegral X] {f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A)}
    {ι : Type} [Finite ι] (S : Work.DSEQP.PerfSetup A p X f) (U : ι → X.Opens) (n : ℕ)
    (z : (S.K U).X n) :
    ∃ (e : ℕ) (x : (DSMap.cech A X f U).X n), S.ofLvl U n e x = z := by
  classical
  -- the Čech index type in degree `n` is `Fin (n+1) → ι`; instance search does not see through
  -- the `FormalCoproduct`-abbreviations, so we install the (classically obtained) `Fintype`
  -- instance for that type directly.
  haveI : Fintype (CechIdx U n).I := Fintype.ofFinite (Fin (n + 1) → ι)
  have key : ∀ a : (CechIdx U n).I,
      ∃ (e : ℕ) (x : Γ(X, CechOp U n a)),
        Perf.of (Γ(X, CechOp U n a)) p (S.hpU (CechOp U n a)) e x = S.kunpack U n z a :=
    fun a => Perf.exists_of (R := Γ(X, CechOp U n a)) (p := p)
      (hp := S.hpU (CechOp U n a)) (S.kunpack U n z a)
  choose E xE hxE using key
  refine ⟨Finset.univ.sup E,
    cpack (A := A) (X := X) (f := f) U n (fun a => xE a ^ p ^ (Finset.univ.sup E - E a)), ?_⟩
  have hmain : S.kunpack U n (S.ofLvl U n (Finset.univ.sup E)
      (cpack (A := A) (X := X) (f := f) U n
        (fun a => xE a ^ p ^ (Finset.univ.sup E - E a)))) = S.kunpack U n z := by
    rw [S.kunpack_ofLvl]
    funext a
    have hca : cunpack U n (cpack (A := A) (X := X) (f := f) U n
        (fun a => xE a ^ p ^ (Finset.univ.sup E - E a))) a
        = xE a ^ p ^ (Finset.univ.sup E - E a) := by
      simp only [cunpack_cpack]
    rw [hca]
    exact (Perf.of_f (R := Γ(X, CechOp U n a)) (p := p) (hp := S.hpU (CechOp U n a))
      (i := E a) (j := Finset.univ.sup E)
      (Finset.le_sup (Finset.mem_univ a)) (xE a)).trans (hxE a)
  have h2 := congrArg (S.kpack U n) hmain
  rwa [S.kpack_kunpack, S.kpack_kunpack] at h2

end Work.DSEQP
