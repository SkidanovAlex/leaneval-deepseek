/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Almost acyclicity of the perfected Čech complex, positive degrees (node PERF)

The third (and last) clause of `DSMap.Mix2.AlmostAcyc` for the perfected Čech complex `K` of
`Submission/Work/DSEQP/PerfCech.lean`: for the ideal `⊥` and the root tower
`ϖ k = g^(1/p^k)`, every cocycle `z` of `K` in degree `q+1` is a coboundary after multiplication
by `ϖ k`, i.e. `ϖ_k · H^{q+1}(K) = 0`.

The proof is the "Frobenius trick" on the Čech complex.  The perfected complex `K` is the Čech
complex of the perfected structure presheaf `𝒪_X^{1/p^∞}`; the level-`e` maps
`ofLvl U n e : Čⁿ → Kⁿ` (`Submission/Work/DSEQP/AcDefs.lean`), given componentwise by the
perfection maps `Perf.of _ p _ e`, are surjective, injective (sections of an integral scheme over
an open are reduced), and are chain maps; and `ϖ_k = g^{1/p^k}` acts on a level-`E`
representative by `g^{p^(E-k)}`, for `k ≤ E`.

Consequently, given a cocycle `z ∈ K^{q+1}` and a level `e` with `z = ofLvl e x`, one pushes `x`
to the level `E = max e k + N` (`N` from the torsion hypothesis `htors`), so that `z` is still
represented at level `E` and the acting scalar `g^{p^(E-k)}` is divisible by `g^N`; the torsion
hypothesis applied to the `E`-level representative then exhibits `z` as a `ϖ_k`-multiple of a
coboundary.

The building blocks are proved in the modules `AcExists`, `AcShift`, `AcInj`, `AcDiff` and
`AcSmul`; the copies below are the universe-polymorphic forms of those statements needed for the
statement of `almostAcyc_succ` in its own universe.
-/
import Mathlib
import Submission.Work.DSEQP.PerfAlmost
import Submission.Work.DSEQP.AcDefs
import Submission.Work.DSEQP.AcExists
import Submission.Work.DSEQP.AcShift
import Submission.Work.DSEQP.AcInj
import Submission.Work.DSEQP.AcDiff
import Submission.Work.DSEQP.AcSmul

open CategoryTheory AlgebraicGeometry Limits Opposite
open scoped Simplicial BigOperators AlgebraicGeometry

namespace Work.DSEQP

universe u

set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000

namespace PerfSetup

variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime] {X : Scheme.{u}} [IsIntegral X]
  {f : X ⟶ Spec (.of A)} {ι : Type u} [Finite ι]

/-- **Every element of a perfected Čech term has a level.**  (Universe-polymorphic form of
`Work.DSEQP.AcExists`.) -/
theorem uExists (S : PerfSetup A p X f) (U : ι → X.Opens) (n : ℕ)
    (z : (S.K U).X n) :
    ∃ (e : ℕ) (x : (DSMap.cech A X f U).X n), S.ofLvl U n e x = z := by
  classical
  haveI hι : Fintype ι := Fintype.ofFinite ι
  haveI : Fintype (CechIdx U n).I := inferInstanceAs (Fintype (Fin (n + 1) → ι))
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

/-- **Changing the level.**  (Universe-polymorphic form of `Work.DSEQP.AcShift`.) -/
theorem uShift (S : PerfSetup A p X f) (U : ι → X.Opens) (n : ℕ) {e j : ℕ} (h : e ≤ j)
    (x : (DSMap.cech A X f U).X n) :
    S.ofLvl U n j ((frobC p U n)^[j - e] x) = S.ofLvl U n e x := by
  rw [ofLvl, ofLvl]
  congr 1
  funext a
  rw [cunpack_frobC_iter]
  exact Perf.of_f (R := Γ(X, CechOp U n a)) (p := p) (hp := S.hpU _) h (cunpack U n x a)

/-- **The level maps are injective.**  (Universe-polymorphic form of `Work.DSEQP.AcInj`.) -/
theorem uInj (S : PerfSetup A p X f) (U : ι → X.Opens) (n e : ℕ)
    (x : (DSMap.cech A X f U).X n) (h : S.ofLvl U n e x = 0) : x = 0 := by
  have hstep : ∀ a, Perf.of (Γ(X, CechOp U n a)) p (S.hpU _) e
      (cunpack U n x a) = 0 := by
    intro a
    have hk := congrFun (congrArg (S.kunpack U n) h) a
    rw [kunpack_ofLvl] at hk
    rw [kunpack_apply] at hk
    exact hk.trans (map_zero _)
  have hcu : ∀ a, cunpack U n x a = 0 := fun a =>
    Perf.of_injective_of_isReduced (S.hpU _) e (by rw [hstep a, map_zero])
  have hy : cunpack U n x = 0 := funext hcu
  have hzero : cunpack U n (0 : (DSMap.cech A X f U).X n) = 0 := by
    funext a
    rw [cunpack_apply]
    exact map_zero _
  calc x = cpack (A := A) (X := X) (f := f) U n (cunpack U n x) :=
        (cpack_cunpack U n x).symm
    _ = cpack (A := A) (X := X) (f := f) U n 0 := by rw [hy]
    _ = cpack (A := A) (X := X) (f := f) U n
          (cunpack U n (0 : (DSMap.cech A X f U).X n)) := by rw [hzero]
    _ = 0 := cpack_cunpack U n 0

/-- **The level maps are chain maps.**  (Universe-polymorphic form of `Work.DSEQP.AcDiff`.) -/
theorem uDiff (S : PerfSetup A p X f) (U : ι → X.Opens) (n e : ℕ)
    (x : (DSMap.cech A X f U).X n) :
    (S.K U).d n (n + 1) (S.ofLvl U n e x) =
      S.ofLvl U (n + 1) e ((DSMap.cech A X f U).d n (n + 1) x) := by
  classical
  refine pi_elem_ext (β := (CechIdx U (n + 1)).I) (S.kobj U (n + 1)) (fun a => ?_)
  exact (π_K_d S U n e x a).trans
    (π_ofLvl S U (n + 1) e ((DSMap.cech A X f U).d n (n + 1) x) a).symm

/-- **The root tower acts on level maps by a power of `g`.**  (Universe-polymorphic form of
`Work.DSEQP.AcSmul`.) -/
theorem uSmul (S : PerfSetup A p X f) [CharP S.W p] [PerfectRing S.W p]
    (U : ι → X.Opens) (n k E : ℕ) (hk : k ≤ E) (g : A) (x : (DSMap.cech A X f U).X n) :
    S.varpi g k • S.ofLvl U n E x = S.ofLvl U n E (g ^ p ^ (E - k) • x) := by
  refine kobj_ext S U n (fun a => ?_)
  exact kobj_π_smul_ofLvl S U n k E hk g x a

end PerfSetup

theorem almostAcyc_succ (A : Type u) [CommRing A] (p : ℕ) [Fact p.Prime]
    (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsIntegral X]
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A))
    (S : Work.DSEQP.PerfSetup A p X f) [CharP (Work.DSEQP.PerfSetup.W S) p]
    [PerfectRing (Work.DSEQP.PerfSetup.W S) p] {ι : Type u} [Finite ι] (U : ι → X.Opens) (g : A)
    (htors : ∀ q : ℕ, ∃ N : ℕ, ∀ z : (DSMap.cech A X f U).X (q + 1),
      ((DSMap.cech A X f U).d (q + 1) (q + 2)).hom z = 0 →
        ∃ y : (DSMap.cech A X f U).X q,
          ((DSMap.cech A X f U).d q (q + 1)).hom y = g ^ N • z)
    (q : ℕ) (k : ℕ) (z : (S.K U).X (q + 1))
    (hz : ((S.K U).d (q + 1) (q + 2)).hom z = 0) :
    ∃ y : (S.K U).X q, (S.varpi g k) • z = ((S.K U).d q (q + 1)).hom y := by
  obtain ⟨N, hN⟩ := htors q
  obtain ⟨e, x, hx⟩ := PerfSetup.uExists S U (q + 1) z
  -- Push the representative of `z` up to the level `E = max e k + N`.
  set xE : (DSMap.cech A X f U).X (q + 1) := (PerfSetup.frobC p U (q + 1))^[max e k + N - e] x
    with hxEdef
  have heE : e ≤ max e k + N := by omega
  have hkE : k ≤ max e k + N := by omega
  have hNle : N ≤ p ^ (max e k + N - k) := by
    refine (Nat.le_of_lt N.lt_two_pow_self).trans ?_
    refine (pow_le_pow_left' (Fact.out : p.Prime).two_le N).trans ?_
    exact pow_le_pow_right' (Fact.out : p.Prime).one_le (by omega)
  have hxE : S.ofLvl U (q + 1) (max e k + N) xE = z := by
    rw [hxEdef, PerfSetup.uShift S U (q + 1) heE x, hx]
  -- The `E`-level representative is a cocycle, so `htors` applies to it.
  have hd : (DSMap.cech A X f U).d (q + 1) (q + 2) xE = 0 := by
    refine PerfSetup.uInj S U (q + 2) (max e k + N)
      ((DSMap.cech A X f U).d (q + 1) (q + 2) xE) ?_
    rw [← PerfSetup.uDiff S U (q + 1) (max e k + N) xE, hxE]
    exact hz
  obtain ⟨y0, hy0⟩ := hN xE hd
  refine ⟨S.ofLvl U q (max e k + N) (g ^ (p ^ (max e k + N - k) - N) • y0), ?_⟩
  -- At level `E = max e k + N`, the root `ϖ_k = g^(1/p^k)` acts by `g^(p^(E-k))`, which is a
  -- `g^N`-multiple, hence a coboundary by `htors`.
  have key : g ^ (p ^ (max e k + N - k)) • xE =
      (DSMap.cech A X f U).d q (q + 1)
        (g ^ (p ^ (max e k + N - k) - N) • y0) := by
    rw [map_smul, hy0, ← mul_smul, ← pow_add]
    rw [show p ^ (max e k + N - k) - N + N = p ^ (max e k + N - k) by omega]
  rw [← hxE, PerfSetup.uSmul S U (q + 1) k (max e k + N) hkE g xE, key,
    PerfSetup.uDiff S U q (max e k + N) _]

end Work.DSEQP
