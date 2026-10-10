import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Submission.Work.Kummer.exists_algEquiv_apply_eq_mul_of_pow_eq
import Submission.Work.Kummer.norm_eq_primRoot_pow_mul_of_kummer_generator
import Submission.Work.SSGRoute.GrunwaldEscapeCore.mem_localNormSubgroup_algebra_norm
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The corrected diagonal of the local Kummer pairing (`p = 2` included)

`Work.SSGRoute.GrunwaldEscapeCore.mem_localNormSubgroup_of_kummerRoot` shows that for an *odd* prime
`p` the Kummer element `x` is a local norm from the Kummer extension `K(x^{1/p})`.  For `p = 2` the
norm of the Kummer root `α` (with `α ^ 2 = x`) is `-x`, not `x`, and the correct statement is:

  `ζ ^ (p * (p - 1) / 2) * x` is a local norm,

where `ζ` is the primitive `p`-th root of unity.  For odd `p` the correction is `1`
(`Work.Kummer.primRoot_pow_half_mul_self_sub_one_eq_one`), and for `p = 2` it is `-1 = ζ`; in both
cases the norm of `α` is `ζ ^ (p (p-1)/2) x`
(`Work.Kummer.norm_eq_primRoot_pow_mul_of_kummer_generator`), which is the content of the lemma.
-/

open scoped NumberField

namespace Work.SSGRoute.N2v2

open NumberField IsDedekindDomain

/-- **The corrected diagonal of the local Kummer pairing.**  For *every* prime `p`, the element
`ζ ^ (p * (p - 1) / 2) * x` lies in the local norm subgroup of the Kummer extension
`L = K(α)`, `α ^ p = x`. -/
theorem mem_localNormSubgroup_of_kummerRoot_correction
    (p : ℕ) [Fact p.Prime] {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (ζ : K) (hζ : IsPrimitiveRoot ζ p) (x : Kˣ) (α : L)
    (hα : α ^ p = algebraMap K L (x : K))
    (hgen : IntermediateField.adjoin K ({α} : Set L) = ⊤)
    (hdeg : Module.finrank K L = p)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    NK.CFTLib.IdeleHasse.localImageAt (K := K) (NK.GlobalCFT.Place.ofFinite 𝔭)
        (Units.mk0 (ζ ^ (p * (p - 1) / 2))
          (pow_ne_zero _ (hζ.ne_zero (Fact.out : p.Prime).ne_zero)) * x) ∈
      NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L)
        (NK.GlobalCFT.Place.ofFinite 𝔭) := by
  classical
  have hpne : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hpne
  have hx0 : (x : K) ≠ 0 := x.ne_zero
  -- the automorphism `α ↦ ζ α`
  let μ : rootsOfUnity p K :=
    ⟨Work.Kummer.primRootUnit hζ, by
      rw [mem_rootsOfUnity', Work.Kummer.primRootUnit_coe hζ]
      exact hζ.pow_eq_one⟩
  have hμcoe : (((μ : rootsOfUnity p K) : Kˣ) : K) = ζ := Work.Kummer.primRootUnit_coe hζ
  obtain ⟨σ, hσmul⟩ :=
    Work.Kummer.exists_algEquiv_apply_eq_mul_of_pow_eq (K := K) (L := L) hζ hα hgen hdeg μ
  rw [hμcoe] at hσmul
  have hα0 : α ≠ 0 := by
    intro h
    have hmap : algebraMap K L (x : K) ≠ 0 := (map_ne_zero (algebraMap K L)).mpr hx0
    rw [h, zero_pow hpne] at hα
    exact hmap hα.symm
  -- `σ` generates `Gal(L/K)`
  have hcard : Nat.card Gal(L/K) = p := (IsGalois.card_aut_eq_finrank K L).trans hdeg
  have hσpow : ∀ k : ℕ, ((σ : L ≃ₐ[K] L) ^ k) α = (algebraMap K L ζ) ^ k * α := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', AlgEquiv.mul_apply, ih, map_mul, map_pow, AlgEquiv.commutes, hσmul,
        ← mul_assoc, pow_succ]
  have hσp : σ ^ p = 1 := by
    have := pow_card_eq_one' (G := Gal(L/K)) (x := σ)
    rwa [hcard] at this
  have hdvd1 : orderOf σ ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hσp
  have hdvd2 : p ∣ orderOf σ := by
    have hfix : (algebraMap K L ζ) ^ orderOf σ * α = α := by
      have h := hσpow (orderOf σ)
      rw [pow_orderOf_eq_one, AlgEquiv.one_apply] at h
      exact h.symm
    have hζpow : (algebraMap K L ζ) ^ orderOf σ = 1 :=
      mul_right_cancel₀ hα0 (by rw [hfix, one_mul])
    have hζpow' : ζ ^ orderOf σ = 1 :=
      (algebraMap K L).injective (by rw [map_pow, map_one]; exact hζpow)
    exact (hζ.pow_eq_one_iff_dvd (orderOf σ)).mp hζpow'
  have hσorder : orderOf σ = p := Nat.dvd_antisymm hdvd1 hdvd2
  have hgen' : Subgroup.zpowers σ = ⊤ := by
    rw [← Subgroup.card_eq_iff_eq_top, Nat.card_zpowers, hσorder, hcard]
  -- the norm of the Kummer root
  have hnorm : Algebra.norm K α = ζ ^ (p * (p - 1) / 2) * (x : K) :=
    Work.Kummer.norm_eq_primRoot_pow_mul_of_kummer_generator hζ hdeg hα
      (fun g => by rw [hgen']; exact Subgroup.mem_top g) hσmul
  -- hence the unit `ζ ^ (p*(p-1)/2) * x` is the global norm of `α`
  have hunit : Units.map (Algebra.norm K) (Units.mk0 α hα0) =
      Units.mk0 (ζ ^ (p * (p - 1) / 2))
        (pow_ne_zero _ hζ0) * x := by
    refine Units.ext ?_
    show Algebra.norm K α = (Units.mk0 (ζ ^ (p * (p - 1) / 2)) (pow_ne_zero _ hζ0) * x : Kˣ)
    rw [hnorm]
    rfl
  rw [← hunit]
  exact Work.SSGRoute.GrunwaldEscapeCore.mem_localNormSubgroup_algebra_norm 𝔭 (Units.mk0 α hα0)

end Work.SSGRoute.N2v2
