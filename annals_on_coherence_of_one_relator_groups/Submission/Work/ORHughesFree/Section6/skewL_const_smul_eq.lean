import Mathlib
import Submission.Work.ORHughesFree.NaturalExtension.envelopeDefs
import Submission.Work.ORHughesFree.SkewLaurentSeriesInstances
import Submission.Work.ORHughesFree.SkewLaurentSeries.exists_injective_ringHom_skewMonoidAlgebra
import Submission.Work.ORHughesFree.Section6.skewL_single_one_smul
import Submission.Work.ORHughesFree.Section6.toRingHom_skewLaurentT_pow

namespace Work.ORHughesFree.Section6

open Work.ORHughesFree

/-- The monomials `single m 1` of the skew monoid algebra `A[t;τ]` are units, and they assemble
into a monoid homomorphism `Multiplicative ℤ →* (A[t;τ])ˣ`.  This is what lets us make sense of the
integer power `tᵏ` inside the group of units, where `zpow` is available. -/
noncomputable def singleUnitHom {A : Type} [Ring A] [MulSemiringAction (Multiplicative ℤ) A] :
    Multiplicative ℤ →* (SkewMonoidAlgebra A (Multiplicative ℤ))ˣ where
  toFun m := Units.mk (SkewMonoidAlgebra.single m (1 : A))
    (SkewMonoidAlgebra.single m⁻¹ (1 : A))
    (by rw [SkewMonoidAlgebra.single_mul_single]; simp)
    (by rw [SkewMonoidAlgebra.single_mul_single]; simp)
  map_one' := by
    apply Units.ext
    rw [Units.val_one]
    exact SkewMonoidAlgebra.single_one_one
  map_mul' := by
    intro a b
    apply Units.ext
    show SkewMonoidAlgebra.single (a * b) (1 : A) =
      SkewMonoidAlgebra.single a (1:A) * SkewMonoidAlgebra.single b (1:A)
    rw [SkewMonoidAlgebra.single_mul_single]
    simp

/-- If `↑lam = fω (single (ofAdd 1) 1)` for a unit `lam : Pˣ`, then `fω` sends the monomial
`single (ofAdd k) 1` to the `k`-th power of `lam`, for every integer `k`. -/
theorem fω_single_ofAdd_eq_zpow {A P : Type} [Ring A] [MulSemiringAction (Multiplicative ℤ) A]
    [Ring P]
    (fω : SkewMonoidAlgebra A (Multiplicative ℤ) →+* P)
    (lam : Pˣ)
    (hlam : ((lam : Pˣ) : P) = fω (SkewMonoidAlgebra.single (Multiplicative.ofAdd 1) (1 : A)))
    (k : ℤ) :
    fω (SkewMonoidAlgebra.single (Multiplicative.ofAdd k) (1 : A)) = ((lam ^ k : Pˣ) : P) := by
  let F : Multiplicative ℤ →* Pˣ := (Units.map fω).comp (singleUnitHom (A := A))
  have hbase : F (Multiplicative.ofAdd (1:ℤ)) = lam := by
    apply Units.ext
    simpa [F, MonoidHom.comp_apply, Units.coe_map, singleUnitHom] using hlam.symm
  have he : Multiplicative.ofAdd k = (Multiplicative.ofAdd (1:ℤ)) ^ k := by
    simpa using (ofAdd_zsmul k (1:ℤ))
  have hkey : F (Multiplicative.ofAdd k) = lam ^ k := by
    rw [he, MonoidHom.map_zpow, hbase]
  have hc := congrArg (fun u : Pˣ => (u : P)) hkey
  simpa [F, MonoidHom.comp_apply, Units.coe_map, singleUnitHom] using hc

theorem skewL_const_smul_eq {A P : Type} [Ring A] [MulSemiringAction (Multiplicative ℤ) A] [Ring P]
    (fω : SkewMonoidAlgebra A (Multiplicative ℤ) →+* P) (Ψ : Work.ORHughesFree.SkewLaurentSeries A →+* P)
    (hΨ : ∀ p : SkewMonoidAlgebra A (Multiplicative ℤ),
      Ψ (Work.ORHughesFree.SkewLaurentSeries.toRingHom p) = fω p)
    (lam : Pˣ)
    (hlam : ((lam : Pˣ) : P) =
      fω (SkewMonoidAlgebra.single (Multiplicative.ofAdd 1) (1 : A)))
    (k : ℤ) (x : A) :
    fω (SkewMonoidAlgebra.single (1 : Multiplicative ℤ) ((Multiplicative.ofAdd k) • x)) =
      ((lam ^ k : Pˣ) : P) * fω (SkewMonoidAlgebra.single (1 : Multiplicative ℤ) x) *
        (((lam ^ (-k) : Pˣ)) : P) := by
  rw [skewL_single_one_smul (Multiplicative.ofAdd k) x, map_mul, map_mul]
  rw [show (Multiplicative.ofAdd k)⁻¹ = Multiplicative.ofAdd (-k) from (ofAdd_neg k).symm]
  rw [fω_single_ofAdd_eq_zpow fω lam hlam k, fω_single_ofAdd_eq_zpow fω lam hlam (-k)]

end Work.ORHughesFree.Section6
