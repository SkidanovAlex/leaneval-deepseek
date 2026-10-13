import Mathlib
import Submission.Work.DSM5b.PerfComplexDefs
import Submission.Work.DSM5b.H0Defs

/-!
# `Submission.Work.DSM5b.awayComplex`

The *localisation at `T`* of the honest chart Čech complex, in coordinates.

`R` is a ring, `t : ι → R` a finite family, `T ∈ R` and `t j₀ = T ^ e`.  The honest chart
Čech complex (`Work.DSM5b.HCX`/`HCd`) has terms `chartRing t (tupRng τ) ⊆ R_{t_τ}`.  After
inverting `T` (or, equivalently, any of the `t j₀ = T ^ e`) the family `(t i)` generates the unit
ideal, so the localised complex

  `AWX t T m = ∀ τ : Fin (m+1) → ι, Localization.Away (T * tS t (tupRng τ))`

is exact in positive degrees.  This file sets up the complex and the comparison map
`HCX t m → AWX t T m`; the exactness is `Work.DSM5b.awayCycleBoundary`.
-/

namespace Work.DSM5b

open CategoryTheory DSMap DSMap.Mix DSMap.Mix2

universe a

section LiftAway

variable {R : Type a} [CommRing R]

/-- The localisation map `R_s → R_{s'}` for `s ∣ s'` (as a `LinearMap`-friendly `AlgHom`). -/
noncomputable def liftAway {s s' : R} (h : s ∣ s') :
    Localization.Away s →ₐ[R] Localization.Away s' :=
  IsLocalization.Away.liftAlgHom s (f := Algebra.ofId R _)
    (isUnit_of_dvd_unit (map_dvd (algebraMap R _) h)
      (IsLocalization.Away.algebraMap_isUnit s'))

@[simp] lemma liftAway_algebraMap {s s' : R} (h : s ∣ s') (r : R) :
    liftAway h (algebraMap R (Localization.Away s) r) =
      algebraMap R (Localization.Away s') r :=
  IsLocalization.Away.lift_eq s
    (isUnit_of_dvd_unit (map_dvd (algebraMap R _) h)
      (IsLocalization.Away.algebraMap_isUnit s')) r

/-- Uniqueness of `R`-algebra maps out of `Localization.Away s`. -/
lemma liftAway_unique {s : R} {P : Type a} [CommRing P] [Algebra R P]
    (φ ψ : Localization.Away s →ₐ[R] P)
    (h : ∀ r : R, φ (algebraMap R _ r) = ψ (algebraMap R _ r)) : φ = ψ := by
  haveI : Subsingleton (Localization.Away s →ₐ[R] P) :=
    IsLocalization.algHom_subsingleton (Submonoid.powers s)
  exact Subsingleton.elim φ ψ

end LiftAway

section AwayT

variable {R : Type a} [CommRing R] {ι : Type a} [DecidableEq ι]

/-- The localisation map `R_{t_S} → R_{t_S}[1/T] = R[1/(T · t_S)]`. -/
noncomputable def awayIn (t : ι → R) (T : R) (S : Finset ι) :
    Localization.Away (tS t S) →ₐ[R] Localization.Away (T * tS t S) :=
  liftAway (dvd_mul_left (tS t S) T)

/-- The localisation map between the `T`-localised chart rings, for `S ⊆ S'`. -/
noncomputable def awayT (t : ι → R) (T : R) {S S' : Finset ι} (h : S ⊆ S') :
    Localization.Away (T * tS t S) →ₐ[R] Localization.Away (T * tS t S') :=
  liftAway (mul_dvd_mul_left T (tS_dvd t h))

section AwayD

variable (t : ι → R) (T : R)

/-- Terms of the `T`-localised chart Čech complex. -/
noncomputable abbrev AWX (m : ℕ) : Type a :=
  ∀ τ : Fin (m + 1) → ι, Localization.Away (T * tS t (tupRng τ))

/-- The alternating coface differential of `AWX`. -/
noncomputable def AWd (m : ℕ) : AWX t T m →ₗ[R] AWX t T (m + 1) where
  toFun z := fun τ => ∑ i : Fin (m + 2),
    ((-1 : R) ^ ((i : ℕ))) • awayT t T (tupRng_del_subset i τ) (z (tupDel i τ))
  map_add' z z' := by
    funext τ
    simp only [Pi.add_apply, map_add, smul_add, Finset.sum_add_distrib]
  map_smul' r z := by
    funext τ
    simp only [Pi.smul_apply, RingHom.id_apply, map_smul, smul_comm _ r, Finset.smul_sum]

@[simp] lemma AWd_apply (m : ℕ) (z : AWX t T m) (τ : Fin (m + 2) → ι) :
    AWd t T m z τ = ∑ i : Fin (m + 2),
      ((-1 : R) ^ ((i : ℕ))) • awayT t T (tupRng_del_subset i τ) (z (tupDel i τ)) := rfl

end AwayD

section IotaL

variable (t : ι → R) (T : R)

/-- The coercion of a finite sum in a `Subalgebra`. -/
lemma coe_sum_subalgebra {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    {S : Subalgebra R A} {ι' : Type*} (s : Finset ι') (f : ι' → ↥S) :
    ((∑ i ∈ s, f i : ↥S) : A) = ∑ i ∈ s, (f i : A) :=
  map_sum (Subalgebra.val S) f s

/-- The comparison (localisation) map from the honest chart Čech complex to its `T`-localisation. -/
noncomputable def iotaL (m : ℕ) : HCX t m →ₗ[R] AWX t T m where
  toFun z := fun τ => awayIn t T (tupRng τ) (z τ)
  map_add' z z' := by
    funext τ
    show awayIn t T (tupRng τ) ↑((z + z') τ)
        = awayIn t T (tupRng τ) ↑(z τ) + awayIn t T (tupRng τ) ↑(z' τ)
    simp only [Pi.add_apply, Subalgebra.coe_add, map_add]
  map_smul' r z := by
    funext τ
    show awayIn t T (tupRng τ) ↑((r • z) τ)
        = r • (awayIn t T (tupRng τ) ↑(z τ))
    simp only [Pi.smul_apply, RingHom.id_apply, Subalgebra.coe_smul, map_smul]

@[simp] lemma iotaL_apply (m : ℕ) (z : HCX t m) (τ : Fin (m + 1) → ι) :
    iotaL t T m z τ = awayIn t T (tupRng τ) (z τ) := rfl

/-- `iotaL` is a chain map. -/
lemma iotaL_HCd (m : ℕ) (z : HCX t m) :
    iotaL t T (m + 1) (HCd t m z) = AWd t T m (iotaL t T m z) := by
  funext τ
  simp only [iotaL_apply, HCd_apply, AWd_apply]
  rw [coe_sum_subalgebra]
  rw [map_sum (awayIn t T (tupRng τ))]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Subalgebra.coe_smul, map_smul]
  congr 1
  rw [rhoH_coe]
  have hcomp : (awayIn t T (tupRng τ)).comp (locRes t (tupRng_del_subset i τ)) =
      (awayT t T (tupRng_del_subset i τ)).comp (awayIn t T (tupRng (tupDel i τ))) := by
    haveI : Subsingleton (Localization.Away (tS t (tupRng (tupDel i τ))) →ₐ[R]
        Localization.Away (T * tS t (tupRng τ))) :=
      IsLocalization.algHom_subsingleton (Submonoid.powers (tS t (tupRng (tupDel i τ))))
    exact Subsingleton.elim _ _
  exact AlgHom.congr_fun hcomp
    (z (tupDel i τ) : Localization.Away (tS t (tupRng (tupDel i τ))))

end IotaL

end AwayT

end Work.DSM5b
