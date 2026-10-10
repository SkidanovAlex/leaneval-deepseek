import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Submission.Work.Kummer.exists_algEquiv_apply_eq_mul_of_pow_eq
import Submission.Work.Kummer.norm_eq_primRoot_pow_mul_of_kummer_generator
import Submission.Work.SSGRoute.GrunwaldEscapeCore.mem_localNormSubgroup_algebra_norm
import Submission.Work.SSGRoute.ZDataMup.ideleArtin_ideleOfPrime_of_unramified
import Submission.Work.SSGRoute.ZDataMup.ideleArtin_restrictNormalHom
import Submission.Work.SSGRoute.ZDataMup.localFactorProductFormulaAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The product formula, as a vanishing sum of local pairings

`NOTE_orthogonality_route.md` §2 (ii).  For an idèlic Artin map `Φ` of a finite abelian extension
`L/K` which kills the principal idèles and the idèlic norms, and any multiplicative character
`χ : Gal(L/K) →* Multiplicative (ZMod p)`, Hilbert reciprocity in the form
`ZDataMup.cprod_localFactor_eq_one` (`∏_v θ_v(x_v) = 1` for `x ∈ Kˣ`, the product taken over a finite
set containing every place where the local factor is non-trivial) becomes, after applying `χ`,

  `∑_{v ∈ s} (χ (θ_v x_v)).toAdd = 0`.

This is the `ZMod p` form in which the orthogonality of the Grünwald escape consumes
reciprocity — for the pair `(F_c, a)` and for the pair `(F_{b_g}, c)`.
-/

open scoped NumberField
open NumberField IsDedekindDomain
open NK.GlobalCFT

namespace Work.SSGRoute.GrunwaldEscapeCore

/-- **A monoid hom maps a `cprod` to a `Finset.prod`** (the target only needs a commutative
monoid, so that this applies to `Multiplicative (ZMod p)`, which is not a group). -/
theorem cprod_map_prod {ι : Type*} {G : Type} [Group G] {H : Type} [CommMonoid H]
    (hcomm : ∀ x y : G, x * y = y * x) (χ : G →* H) (s : Finset ι) (g : ι → G) :
    χ (NK.CFTLib.IdeleHasse.cprod hcomm s g) = ∏ i ∈ s, χ (g i) := by
  letI : CommMonoid G := { ‹Group G› with mul_comm := hcomm }
  simp only [NK.CFTLib.IdeleHasse.cprod]
  exact map_prod χ g s

/-- **The `toAdd` of a product is the sum of the `toAdd`s.** -/
theorem toAdd_prod_eq_sum (p : ℕ) {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (g : ι → Multiplicative (ZMod p)) :
    (∏ i ∈ s, g i).toAdd = ∑ i ∈ s, (g i).toAdd := by
  have hmul : ∀ a b : Multiplicative (ZMod p), (a * b).toAdd = a.toAdd + b.toAdd := by
    intro a b
    simpa using (Multiplicative.ofAdd_add (a.toAdd) (b.toAdd)).symm
  induction s using Finset.induction with
  | empty => simp
  | insert a t ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, hmul, ih]

/-- **The product formula as a vanishing sum.** -/
theorem localFactor_sum_eq_zero
    (p : ℕ) [Fact p.Prime]
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (hcomm : ∀ a b : Gal(L/K), a * b = b * a)
    (Φ : Idele K →* (L ≃ₐ[K] L))
    (hprin : ∀ a : Kˣ, Φ (Idele.principalIdele K a) = 1)
    (hnorm : ∀ y : Idele L, Φ (Idele.normIdeleHom K L y) = 1)
    (χ : Gal(L/K) →* Multiplicative (ZMod p))
    (x : Kˣ) (s : Finset (Place K))
    (hs : ∀ v, v ∉ s →
      Φ (NK.HassePrinciple.onePlace v (NK.CFTLib.IdeleHasse.localImageAt v x)) = 1) :
    ∑ v ∈ s, (χ (Φ (NK.HassePrinciple.onePlace v
        (NK.CFTLib.IdeleHasse.localImageAt v x)))).toAdd = 0 := by
  classical
  have h := Work.SSGRoute.ZDataMup.cprod_localFactor_eq_one (K := K) (L := L) hcomm Φ hprin hnorm
    x s hs
  have h1 : ∏ v ∈ s, χ (Φ (NK.HassePrinciple.onePlace v
      (NK.CFTLib.IdeleHasse.localImageAt v x))) = 1 := by
    rw [← cprod_map_prod hcomm χ s
      (fun v => Φ (NK.HassePrinciple.onePlace v (NK.CFTLib.IdeleHasse.localImageAt v x))), h,
      map_one]
  rw [← toAdd_prod_eq_sum p s
    (fun v => χ (Φ (NK.HassePrinciple.onePlace v (NK.CFTLib.IdeleHasse.localImageAt v x)))), h1]
  simp

end Work.SSGRoute.GrunwaldEscapeCore
