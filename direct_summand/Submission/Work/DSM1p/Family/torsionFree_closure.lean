import Mathlib
import Submission.Work.DSM1p.Family
import Submission.Work.DSM1p.Family.flat_closure

/-!
# `p`-torsion-freeness of the multi-parameter root closure `R[x₁^{1/p^∞},…,x_d^{1/p^∞}]`

If `p : ℕ` is a non-zero-divisor of a commutative ring `R`, then the element `p` of the
multi-parameter root closure

`FamClosure R p x = R[x₁^{1/p^∞}, …, x_d^{1/p^∞}]`
(`Submission/Work/DSM1p/Family.lean`, the filtered colimit of the stages
`FamTower R p x n = R[Z] ⧸ (Z_i ^ (p ^ n) - x i)`)

is again a non-zero-divisor.  This is the `p`-torsion-freeness input of Bhatt's flatness
criterion in the multi-parameter case (the one-parameter case is
`Work.DSM1p.Root.torsionFree_closure`).

## Proof

The closure is *flat* over `R` (`Family.flat_closure`, proved by the equational criterion: the
stages are free `R`-modules, so the filtered colimit of the stages is flat).  On a flat module a
non-zero-divisor of the base stays a non-zero-divisor
(`Module.Flat.isSMulRegular_of_isRegular`), and the `R`-scalar `((p : ℕ) : R)` acts on the closure
by multiplication with `(p : FamClosure R p x)` (`map_natCast`,
`isSMulRegular_algebraMap_iff`).

The degenerate case `p = 0` needs no flatness: `IsSMulRegular R 0` forces `R` to be a
subsingleton, hence so is every stage of the tower and hence the closure, so every element of the
closure is `0`.
-/

namespace Work.DSM1p.Family

universe u

open Work.DSM1p

theorem torsionFree_closure (R : Type*) [CommRing R] (p : ℕ) {d : ℕ} (x : Fin d → R)
    (hp : IsSMulRegular R p) :
    IsSMulRegular (Work.DSM1p.FamClosure R p x) (p : Work.DSM1p.FamClosure R p x) := by
  by_cases hp0 : p = 0
  · -- `p = 0` forces `R`, hence every stage of the tower, hence the closure, to be a subsingleton
    subst hp0
    haveI : Subsingleton R := ⟨fun a b => hp (by simp)⟩
    refine IsSMulRegular.of_right_eq_zero_of_smul fun z _ => ?_
    obtain ⟨i, y, rfl⟩ := Ring.DirectLimit.exists_of z
    haveI : Subsingleton (Work.DSM1p.FamTower R 0 x i) := inferInstance
    have hy : y = 0 := Subsingleton.elim y 0
    rw [hy, map_zero]
  · -- `p ≠ 0`: the closure is flat, and on a flat module a non-zero-divisor of the base is regular
    haveI : Module.Flat R (Work.DSM1p.FamClosure R p x) := flat_closure R p x hp0
    have h1 : IsSMulRegular (Work.DSM1p.FamClosure R p x) ((p : ℕ) : R) :=
      Module.Flat.isSMulRegular_of_isRegular (isRegular_natCast.mpr hp)
    have h2 : IsSMulRegular (Work.DSM1p.FamClosure R p x)
        (algebraMap R (Work.DSM1p.FamClosure R p x) ((p : ℕ) : R)) :=
      (isSMulRegular_algebraMap_iff (M := Work.DSM1p.FamClosure R p x)
        (A := Work.DSM1p.FamClosure R p x)).mpr h1
    rwa [map_natCast] at h2

end Work.DSM1p.Family
