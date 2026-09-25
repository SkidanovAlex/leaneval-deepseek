import Mathlib
import Submission.Work.ShafarevichKoch.KummerPairing
import Submission.Work.ClassFieldTower.Defs
import Submission.Work.ClassFieldTower.ProTwoDefs

/-!
# `Work.ShafarevichKoch.towerUnit_fixed_mem_base`

Let `F` be a number field and `M : MaximalUnramifiedProP F 2`, so that `M.K` is the maximal
unramified pro-`2` extension `F_∅` of `F` and `Gal(M.K/F) = galoisGroup M`.  Since `M.K/F` is
Galois, the elements of `M.K` fixed by *all* of `Gal(M.K/F)` are exactly the elements of the
base field `F`, and if such a fixed element is moreover integral over the ring of integers
`𝓞 F` (e.g. a unit of the integral closure of `𝓞 F` in `M.K`), then it comes from `𝓞 F` itself.

The main theorem states the unit form of this: a unit `u` of `integralClosure (𝓞 F) M.K` which
is fixed by the whole Galois group is the image of a unit `v` of `𝓞 F`.  This is the elementary
"descent of units" used in the Shafarevich--Koch / Kummer-pairing analysis of `G_∅`: the
fixed points `F_∅^{G_∅} = F` (an infinite Galois extension has no more fixed points than the
base) and integrality over `𝓞 F` combine to force base-field units.

The proof is in three steps, all from Mathlib:

* `InfiniteGalois.mem_range_algebraMap_iff_fixed`: an element of `M.K` fixed by every
  `F`-automorphism lies in the image of `algebraMap F M.K`;
* `IsIntegral.tower_bot_of_field`: integrality over `𝓞 F` descends along the injective map
  `F → M.K`;
* `IsIntegrallyClosed.algebraMap_eq_of_integral`: `𝓞 F` is integrally closed in `F`.

-/

set_option linter.unusedVariables false

open scoped Classical
open scoped NumberField
open NumberField

noncomputable section

namespace Work.ShafarevichKoch

/-- **Fixed elements of `F_∅` integral over `𝓞 F` come from `𝓞 F`.**

If `x : M.K` is integral over `𝓞 F` and fixed by every element of `Gal(M.K/F)`, then
`x = algebraMap (𝓞 F) M.K b` for some `b : 𝓞 F`. -/
theorem exists_ringOfIntegers_of_fixed (F : Type*) [Field F] [NumberField F]
    (M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} F 2) (x : M.K)
    (hint : IsIntegral (𝓞 F) x)
    (hx : ∀ σ : Work.ClassFieldTower.galoisGroup M, σ x = x) :
    ∃ b : 𝓞 F, algebraMap (𝓞 F) M.K b = x := by
  -- `M.K/F` is Galois, so the fixed field of `Gal(M.K/F)` is `F`: `x` comes from `F`.
  obtain ⟨a, ha⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed x).mpr hx
  -- integrality over `𝓞 F` descends to `F` along the injective `F → M.K`
  have h1 : IsIntegral (𝓞 F) (algebraMap F M.K a) := by rw [ha]; exact hint
  have h2 : IsIntegral (𝓞 F) a := IsIntegral.tower_bot_of_field h1
  -- `𝓞 F` is integrally closed in `F`
  obtain ⟨b, hb⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral h2
  exact ⟨b, by rw [IsScalarTower.algebraMap_apply (𝓞 F) F M.K, hb, ha]⟩

theorem towerUnit_fixed_mem_base (F : Type*) [Field F] [NumberField F]
    (M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} F 2)
    (u : (integralClosure (NumberField.RingOfIntegers F) M.K)ˣ)
    (hu : ∀ σ : Work.ClassFieldTower.galoisGroup M,
        σ ((u : integralClosure (NumberField.RingOfIntegers F) M.K) : M.K)
          = ((u : integralClosure (NumberField.RingOfIntegers F) M.K) : M.K)) :
    ∃ v : (NumberField.RingOfIntegers F)ˣ,
      algebraMap (NumberField.RingOfIntegers F) M.K (v : NumberField.RingOfIntegers F)
        = ((u : integralClosure (NumberField.RingOfIntegers F) M.K) : M.K) := by
  -- `u` itself, coerced to `M.K`, comes from `𝓞 F`
  obtain ⟨b, hb⟩ := exists_ringOfIntegers_of_fixed F M ((u : integralClosure (𝓞 F) M.K) : M.K)
    (IsIntegral.algebraMap
      (Algebra.IsIntegral.isIntegral (u : integralClosure (𝓞 F) M.K))) hu
  -- the same holds for the inverse `u⁻¹` (which is again fixed, being the inverse of a fixed unit)
  have hzy : ((u⁻¹ : (integralClosure (𝓞 F) M.K)ˣ) : M.K)
      * ((u : (integralClosure (𝓞 F) M.K)ˣ) : M.K) = 1 :=
    congrArg (fun z : integralClosure (𝓞 F) M.K => (z : M.K)) (Units.inv_mul u)
  have hyz : ((u : (integralClosure (𝓞 F) M.K)ˣ) : M.K)
      * ((u⁻¹ : (integralClosure (𝓞 F) M.K)ˣ) : M.K) = 1 :=
    congrArg (fun z : integralClosure (𝓞 F) M.K => (z : M.K)) (Units.mul_inv u)
  obtain ⟨c, hc⟩ := exists_ringOfIntegers_of_fixed F M
    ((u⁻¹ : (integralClosure (𝓞 F) M.K)ˣ) : M.K)
    (IsIntegral.algebraMap (Algebra.IsIntegral.isIntegral
      ((u⁻¹ : (integralClosure (𝓞 F) M.K)ˣ) : integralClosure (𝓞 F) M.K)))
    (fun σ => by
      have h1 : σ (((u⁻¹ : (integralClosure (𝓞 F) M.K)ˣ) : M.K))
          * ((u : (integralClosure (𝓞 F) M.K)ˣ) : M.K) = 1 := by
        rw [← hu σ, ← map_mul, hzy, map_one]
      rw [eq_inv_of_mul_eq_one_left h1, eq_inv_of_mul_eq_one_left hzy])
  -- `algebraMap (𝓞 F) M.K` is injective, so `b` is a unit with inverse `c`
  have hinj : Function.Injective (algebraMap (𝓞 F) M.K) := by
    intro p q h
    rw [IsScalarTower.algebraMap_apply (𝓞 F) F M.K p,
      IsScalarTower.algebraMap_apply (𝓞 F) F M.K q] at h
    exact IsIntegralClosure.algebraMap_injective (𝓞 F) ℤ F ((algebraMap F M.K).injective h)
  have hbc : b * c = 1 := by
    apply hinj
    rw [map_mul, hb, hc, map_one, hyz]
  refine ⟨Units.mkOfMulEqOne b c hbc, ?_⟩
  rw [Units.val_mkOfMulEqOne, hb]

end Work.ShafarevichKoch
