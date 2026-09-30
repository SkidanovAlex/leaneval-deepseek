import Mathlib
import Submission.Work.SpecLin.Alt.conservationNumber
import Submission.Work.SpecLin.Alt.normal_eq_iInter_localizations_height_one

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Work.SpecLin.Alt

open scoped Classical

/-! ## Two bridging lemmas

The normality input `Work.SpecLin.Alt.normal_eq_iInter_localizations_height_one`
(`Submission/Work/SpecLin/Alt/normal_eq_iInter_localizations_height_one.lean`) is stated for an
abstract Noetherian normal domain `A` with fraction field `K`.  To feed it the local ring
`B_𝔫` — realised as the subalgebra `Localization.subalgebra.ofField (FractionRing B) 𝔫.primeCompl`
of `FractionRing B` — we need to translate the localisation vocabulary `InLocalization` of
`Submission/Work/SpecLin/Alt/conservationNumber.lean` into membership in that subalgebra. -/

/-- `InLocalization x I` is exactly membership of `x` in the localisation subalgebra of
`FractionRing B` at the prime `I`. -/
theorem InLocalization_iff_mem_ofField (B : Type*) [CommRing B] [IsDomain B] (I : Ideal B)
    [I.IsPrime] (x : FractionRing B) :
    InLocalization x I ↔ x ∈ Localization.subalgebra.ofField (FractionRing B) I.primeCompl
      (Ideal.primeCompl_le_nonZeroDivisors I) := by
  constructor
  · rintro ⟨b, s, hs, hx⟩
    rw [mem_subalgebra_ofField_iff]
    refine ⟨b, s, hs, ?_⟩
    have hs0 : (algebraMap B (FractionRing B)) s ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
        (Ideal.primeCompl_le_nonZeroDivisors I hs)
    exact (eq_mul_inv_iff_mul_eq₀ hs0).2 hx
  · intro hx
    rw [mem_subalgebra_ofField_iff] at hx
    obtain ⟨a, s, hs, hxs⟩ := hx
    refine ⟨a, s, hs, ?_⟩
    have hs0 : (algebraMap B (FractionRing B)) s ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
        (Ideal.primeCompl_le_nonZeroDivisors I hs)
    rw [hxs, mul_assoc, inv_mul_cancel₀ hs0, mul_one]

/-- **The normality input `hnormal` of `conservationNumber_unit`, made unconditional.**

For a Noetherian normal domain `B`, a maximal ideal `𝔫` and `x : FractionRing B`: if `x` lies in
the localisation `B_p` at every height-one prime `p ≤ 𝔫`, then `x` lies in `B_𝔫`.

Proof: `R := B_𝔫` (as a subalgebra of `FractionRing B`) is a Noetherian normal domain with
fraction field `FractionRing B`; the height-one primes `q` of `R` are the `p·R` with `p ≤ 𝔫`
prime of height one (heights are preserved under localisation,
`IsLocalization.height_map_of_disjoint`, and `IsLocalization.map_under`), and `R_q = B_p`.  Then
`normal_eq_iInter_localizations_height_one` applied at `R` to `x` gives `x ∈ R`. -/
theorem InLocalization_of_forall_heightOne {B : Type*} [CommRing B] [IsDomain B]
    [IsNoetherianRing B] [IsIntegrallyClosed B]
    (𝔫 : Ideal B) [𝔫.IsMaximal] (x : FractionRing B)
    (h : ∀ p : Ideal B, p.IsPrime → p.height = 1 → p ≤ 𝔫 → InLocalization x p) :
    InLocalization x 𝔫 := by
  classical
  haveI h𝔫p : 𝔫.IsPrime := (inferInstance : 𝔫.IsMaximal).isPrime
  have hS : 𝔫.primeCompl ≤ nonZeroDivisors B := Ideal.primeCompl_le_nonZeroDivisors 𝔫
  let R : Subalgebra B (FractionRing B) :=
    Localization.subalgebra.ofField (FractionRing B) 𝔫.primeCompl hS
  haveI hloc : IsLocalization 𝔫.primeCompl R :=
    Localization.subalgebra.isLocalization_ofField (FractionRing B) 𝔫.primeCompl hS
  haveI hnoeth : IsNoetherianRing R :=
    IsLocalization.isNoetherianRing 𝔫.primeCompl R inferInstance
  haveI hint : IsIntegrallyClosed R := isIntegrallyClosed_of_isLocalization R 𝔫.primeCompl hS
  obtain ⟨a, ha⟩ := normal_eq_iInter_localizations_height_one (A := R) (K := FractionRing B) x (by
    intro q hq hq1
    haveI : q.IsPrime := hq
    let p : Ideal B := Ideal.under B q
    have hp_prime : p.IsPrime := Ideal.IsPrime.comap (algebraMap B R)
    haveI : p.IsPrime := hp_prime
    -- `p = q ∩ B` is contained in `𝔫`: otherwise `b ∉ 𝔫` would map to a unit of `R` lying in `q`.
    have hp_le : p ≤ 𝔫 := by
      intro b hb
      by_contra hb𝔫
      have hbS : b ∈ 𝔫.primeCompl := hb𝔫
      have hunit : IsUnit (algebraMap B R b) := IsLocalization.map_units R ⟨b, hbS⟩
      have hbq : algebraMap B R b ∈ q := Ideal.mem_comap.mp hb
      exact hq.ne_top (Ideal.eq_top_of_isUnit_mem q hbq hunit)
    -- `q = p·R`, so `ht p = ht q = 1`.
    have hp_ht : p.height = 1 := by
      have hdisj : Disjoint (𝔫.primeCompl : Set B) (p : Set B) := by
        rw [Set.disjoint_left]
        intro s hsS hsp
        exact hsS (hp_le hsp)
      have h1 : (p.map (algebraMap B R)).height = p.height :=
        IsLocalization.height_map_of_disjoint 𝔫.primeCompl p hdisj
      have h2 : p.map (algebraMap B R) = q := IsLocalization.map_under 𝔫.primeCompl R q
      rw [← h1, h2, hq1]
    -- `x ∈ B_p = R_q`, transported along `B → R → FractionRing B`.
    have hxin : InLocalization x p := h p hp_prime hp_ht hp_le
    rw [InLocalization_iff_mem_ofField B p x, mem_subalgebra_ofField_iff] at hxin
    obtain ⟨b, s, hs, hxs⟩ := hxin
    refine ⟨algebraMap B R b, algebraMap B R s, ?_, ?_⟩
    · intro hmem
      exact hs (Ideal.mem_comap.mpr hmem)
    · have hs0 : (algebraMap B (FractionRing B)) s ≠ 0 :=
        IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
          (Ideal.primeCompl_le_nonZeroDivisors p hs)
      have hst : ∀ t : B, (algebraMap R (FractionRing B)) (algebraMap B R t)
          = (algebraMap B (FractionRing B)) t :=
        fun t => (IsScalarTower.algebraMap_apply B R (FractionRing B) t).symm
      rw [hst, hst, hxs, mul_assoc, inv_mul_cancel₀ hs0, mul_one])
  rw [InLocalization_iff_mem_ofField B 𝔫 x, ha]
  exact a.2

-- Assembly step for the conservation-of-number argument.
-- `Work.SpecLin.Alt.conservationNumber_unit` (`Submission/Work/SpecLin/Alt/conservationNumber.lean`)
-- concludes `IsUnitAt x 𝔫` from two normality inputs on the local ring `B_𝔫`:
--   hnormal : a Noetherian normal domain is the intersection of its height-one localisations
--             (proved: `Work.SpecLin.Alt.normal_eq_iInter_localizations_height_one`),
--   hprime  : a non-zero non-unit of a local Noetherian domain lies in a height-one prime
--             (proved: `Work.SpecLin.Alt.height_one_prime_of_not_isUnit`).
-- This goal carries out that instantiation, making the step unconditional for a Noetherian
-- integrally closed base.  Route: apply the two inputs at `A := Localization.AtPrime 𝔫`
-- (`IsNoetherianRing`, `IsLocalRing`, `IsIntegrallyClosed`) and hand the results to
-- `conservationNumber_unit`; height-one primes of `B_𝔫` are the `p·B_𝔫` with `p ≤ 𝔫` of
-- height one, and `(B_𝔫)_{p B_𝔫} = B_p`.
theorem conservationNumber_noetherian {B : Type*} [CommRing B] [IsDomain B] [IsNoetherianRing B]
    [IsIntegrallyClosed B] (P 𝔫 : Ideal B) [P.IsPrime] [𝔫.IsMaximal] (hP𝔫 : P ≤ 𝔫)
    (x : FractionRing B) (hP : IsUnitAt x P)
    (hgen : ∀ p : Ideal B, p.IsPrime → p.height = 1 → p ≤ 𝔫 → IsUnitAt x p) :
    IsUnitAt x 𝔫 := by
  show InLocalization x 𝔫 ∧ InLocalization x⁻¹ 𝔫
  exact ⟨InLocalization_of_forall_heightOne 𝔫 x
            (fun p hp hp1 hp𝔫 => (hgen p hp hp1 hp𝔫).1),
         InLocalization_of_forall_heightOne 𝔫 x⁻¹
            (fun p hp hp1 hp𝔫 => (hgen p hp hp1 hp𝔫).2)⟩

end Work.SpecLin.Alt
