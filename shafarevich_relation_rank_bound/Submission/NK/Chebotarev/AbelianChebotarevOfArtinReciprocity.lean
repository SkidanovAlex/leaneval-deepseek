import Mathlib
import Submission.NK.Chebotarev.ArtinReciprocity
import Submission.NK.Chebotarev.HasDirichletDensitySensitivity
import Submission.NK.Chebotarev.AbelianChebotarevOfLFunctions

/-!
# Čebotarev for an abelian extension, from the Artin-reciprocity input

`NK.Chebotarev.hasDirichletDensity_frobClass_of_artinReciprocity` gives the density of the full
conjugacy class of a prescribed element.  When the extension is abelian, every conjugacy class is a
singleton, so `IsConj x σ ↔ x = σ` and the class of `σ` has density `1/|Gal(L/K)|`.  The set that
actually occurs in `NK.Chebotarev.AbelianChebotarevOfLFunctions` is `{p | IsFrobAtPrime p σ}`
rather than `{p | IsConj (frobAtPrime p) σ}`; the two differ only at the finitely many ramified
primes, so `NK.Chebotarev.HasDirichletDensitySensitivity` transfers the density.
-/

set_option linter.unusedSectionVars false

namespace NK.Chebotarev

theorem AbelianChebotarevOfArtinReciprocity {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (h : NK.Chebotarev.ArtinReciprocityInput K L)
    (hcomm : ∀ a b : Gal(L/K), a * b = b * a) (σ : Gal(L/K)) :
    NumberField.Set.HasDirichletDensity
      {p : NK.Chebotarev.PrimeIdeal K |
        NK.Chebotarev.IsFrobAtPrime (K := K) (L := L) p σ}
      (1 / (Nat.card (Gal(L/K)) : ℝ)) := by
  have hconj_iff : ∀ x : Gal(L/K), IsConj x σ ↔ x = σ := by
    intro x
    constructor
    · rintro ⟨c, hc⟩
      have h2 : (c : Gal(L/K)) * x = (c : Gal(L/K)) * σ := by
        rw [hc, hcomm σ (c : Gal(L/K))]
      exact mul_left_cancel h2
    · rintro rfl
      exact IsConj.refl _
  have hcard : Nat.card {x : Gal(L/K) // IsConj x σ} = 1 := by
    rw [Nat.card_eq_one_iff_exists]
    exact ⟨⟨σ, IsConj.refl σ⟩, fun y => Subtype.ext ((hconj_iff y.1).mp y.2)⟩
  have hfin : (({p : PrimeIdeal K | IsConj (frobAtPrime (K := K) (L := L) p) σ} \
        {p : PrimeIdeal K | IsFrobAtPrime (K := K) (L := L) p σ}) ∪
      ({p : PrimeIdeal K | IsFrobAtPrime (K := K) (L := L) p σ} \
        {p : PrimeIdeal K | IsConj (frobAtPrime (K := K) (L := L) p) σ})).Finite := by
    refine (finite_ramifiedPrimes (K := K) (L := L)).subset ?_
    rintro p (hp | hp)
    · exact fun hunr => hp.2 ((isFrobAtPrime_iff_frobAtPrime_eq hcomm p hunr σ).mpr
        ((hconj_iff (frobAtPrime (K := K) (L := L) p)).mp hp.1))
    · exact fun hunr => hp.2 ((hconj_iff (frobAtPrime (K := K) (L := L) p)).mpr
        ((isFrobAtPrime_iff_frobAtPrime_eq hcomm p hunr σ).mp hp.1))
  have hbase := hasDirichletDensity_frobClass_of_artinReciprocity (K := K) (L := L) h σ
  rw [hcard] at hbase
  simp only [Nat.cast_one] at hbase
  exact HasDirichletDensitySensitivity (S := {p : PrimeIdeal K |
      IsConj (frobAtPrime (K := K) (L := L) p) σ})
    (T := {p : PrimeIdeal K | IsFrobAtPrime (K := K) (L := L) p σ})
    (δ := 1 / (Nat.card (Gal(L/K)) : ℝ)) hfin hbase

end NK.Chebotarev
