import Mathlib
import Submission.Work.DSM1p.Basic
import Submission.Work.DSM1p.Root.stepMap_alg

/-!
# `p`-torsion-freeness of the root closure `R[a^{1/p^∞}]`

If `p : ℕ` is a non-zero-divisor of `R` (i.e. `IsSMulRegular R p`) then the ring element
`(p : RootClosure R p a)` is a non-zero-divisor of the root closure
`RootClosure R p a = R[a^{1/p^∞}]` (`Work.DSM1p.RootClosure`, the filtered colimit of the tower
`R[x]/(x^{p^m} - a)`, `m : ℕ`).

This is the `p`-torsion-freeness input of Bhatt's flatness criterion
(`Work.DSM1p.Criterion.flat_of_flat_mod_pi`).

## Proof

The colimit is the union of its stages, and every element of it is of the form
`RootClosure.of R p a i z` with `z : RootTower R p a i`.  Each stage is a free `R`-module
(`AdjoinRoot` of the monic polynomial `X ^ (p^m) - C a`, `Work.DSM1p.RootTower.monic`), hence is
`p`-torsion-free as soon as `R` is (`rootTower_smulRegular`, below; the degenerate case `p = 0`
makes `R` a subsingleton ring, whence so is every stage).

If then `p * z = 0` in the colimit and `z = of i z_i`, the relation `(p : _) * of i z_i =
of i ((p : _) * z_i)` together with the colimit zero-exactness
(`Ring.DirectLimit.of.zero_exact`, available because the transition maps form a `DirectedSystem`,
`Work.DSM1p.Root.stepMap_directedSystem`) produces `j ≥ i` with
`stepMap i j h (↑p * z_i) = 0`; the stage `j` is `p`-torsion-free, so `stepMap i j h z_i = 0` and
therefore `z = of i z_i = of j (stepMap i j h z_i) = 0`.
-/

set_option linter.style.haveILetI false

open Polynomial

namespace Work.DSM1p.Root

open Work.DSM1p

/-- **Every stage of the root tower is `p`-torsion-free.**  If `p : ℕ` is a non-zero-divisor of
`R` then `(p : RootTower R p a m)` is a non-zero-divisor of the stage
`RootTower R p a m = R[x]/(x^{p^m} - a)`.

For `p ≠ 0` the polynomial `X ^ (p^m) - C a` is monic, so `AdjoinRoot` of it is a free `R`-module
and `Module.IsTorsionFree R` applies; for `p = 0` the hypothesis `IsSMulRegular R p` forces
`R` (and hence every quotient of `R[X]`, in particular the stage) to be a subsingleton. -/
theorem rootTower_smulRegular (R : Type*) [CommRing R] (p : ℕ) (a : R)
    (hp : IsSMulRegular R p) (m : ℕ) :
    IsSMulRegular (RootTower R p a m) ((p : ℕ) : RootTower R p a m) := by
  by_cases hp0 : p = 0
  · -- `p = 0`: the hypothesis forces `R` to be the zero ring.
    subst hp0
    haveI : Subsingleton R := ⟨fun x y => hp (by simp)⟩
    haveI : Subsingleton (RootTower R 0 a m) := by
      have h : Subsingleton
          (Polynomial R ⧸ (Ideal.span {X ^ (0 ^ m) - C a} : Ideal (Polynomial R))) :=
        inferInstance
      exact h
    intro x y _
    exact Subsingleton.elim x y
  · -- `p ≠ 0`: the stage is free over `R`, hence `R`-torsion-free.
    haveI : Module.Free R (RootTower R p a m) := (RootTower.monic p a hp0 m).free_adjoinRoot
    haveI : Module.IsTorsionFree R (RootTower R p a m) := inferInstance
    have hR : IsSMulRegular (RootTower R p a m) ((p : ℕ) : R) :=
      (isRegular_natCast.mpr hp).isSMulRegular
    have h2 : IsSMulRegular (RootTower R p a m)
        (algebraMap R (RootTower R p a m) ((p : ℕ) : R)) :=
      (isSMulRegular_algebraMap_iff (A := RootTower R p a m) (M := RootTower R p a m)).mpr hR
    rwa [map_natCast] at h2

theorem torsionFree_closure (R : Type*) [CommRing R] (p : ℕ) (a : R) (hp : IsSMulRegular R p) :
    IsSMulRegular (Work.DSM1p.RootClosure R p a) (p : Work.DSM1p.RootClosure R p a) := by
  refine IsSMulRegular.of_right_eq_zero_of_smul fun z hz => ?_
  have hz' : (p : RootClosure R p a) * z = 0 := by simpa only [smul_eq_mul] using hz
  -- every element of the colimit is represented in some stage
  obtain ⟨i, z_i, rfl⟩ := Ring.DirectLimit.exists_of z
  -- `(p : _) * of i z_i = of i ((p : _) * z_i)`
  have hsplit : (p : RootClosure R p a) * RootClosure.of R p a i z_i
      = RootClosure.of R p a i ((p : RootTower R p a i) * z_i) := by
    rw [← map_natCast (RootClosure.of R p a i) p, map_mul]
  rw [hsplit] at hz'
  -- zero-exactness of the colimit: some transition map kills `(p : _) * z_i`
  obtain ⟨j, hij, hj⟩ := Ring.DirectLimit.of.zero_exact (G := RootTower R p a)
    (f' := RootTower.stepMap R p a) hz'
  have hmap : RootTower.stepMap R p a i j hij ((p : RootTower R p a i) * z_i)
      = (p : RootTower R p a j) * RootTower.stepMap R p a i j hij z_i := by
    rw [← map_natCast (RootTower.stepMap R p a i j hij) p, map_mul]
  rw [hmap] at hj
  -- the stage `j` is `p`-torsion-free
  have h2 : RootTower.stepMap R p a i j hij z_i = 0 := by
    refine (rootTower_smulRegular R p a hp j).right_eq_zero_of_smul ?_
    simpa only [smul_eq_mul] using hj
  rw [← Ring.DirectLimit.of_f (G := RootTower R p a) hij z_i, h2]
  exact map_zero _

end Work.DSM1p.Root
