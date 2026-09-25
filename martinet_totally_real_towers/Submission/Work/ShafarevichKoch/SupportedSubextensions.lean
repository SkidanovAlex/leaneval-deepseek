import Mathlib
import Submission.NumberField.MaximalProPOutsideS
import Submission.Work.ShafarevichKoch.SupportedTower
import Submission.Commons.NumberTheory.NumberField.differentIdeal_supp_le_iSup_finset
import Submission.Commons.FieldTheory.Galois.isPGroup_aut_of_le_iSup_finite_galois_pGroup

/-!
# `Work.ShafarevichKoch.SupportedSubextensions` -- the finite subextensions of `k_S`

The two facts about finite Galois subextensions of the maximal pro-`p` extension `k_S` unramified
outside `S` (`Work.ShafarevichKoch.kSupported`) that the *finite-level bookkeeping* of the counting
route needs:

* `kSupported_supp_and_pGroup` -- every finite-dimensional Galois subextension `L ≤ k_S` is pro-`p`
  with **`S`-supported relative different** (this is the second half of the seed's
  `exists_maximal_proP_field_unramifiedOutside`, transported to the spelling `kSupported = ⨆ i.L`);
* `le_kSupported_of_unramified_proP` -- conversely every finite Galois **unramified** pro-`p`
  extension is inside `k_S` (a `SupportedPField` is exactly such an extension, so it lies in the
  supremum), and in particular inside `k_∅`.

These are what allow a finite Galois level `L ⊆ k_S` to be fed to
`Work.ShafarevichKoch.fixingSubgroup_eq_iSup_inertia` / `InertiaCount` (`hsupp`), and what makes
`L ⊓ k_∅` the *maximal* unramified subextension of `L` (`hmax`).
-/

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped Classical
open scoped NumberField

noncomputable section

namespace Work.ShafarevichKoch

/-- **Every finite Galois subextension of `k_S` is pro-`p` with `S`-supported different.** -/
theorem kSupported_supp_and_pGroup {F : Type} [Field F] [NumberField F] {p : ℕ} [Fact p.Prime]
    (S : Finset ℕ) {L : IntermediateField F (AlgebraicClosure F)}
    [FiniteDimensional F L] [IsGalois F L] [NumberField ↥L] (hL : L ≤ kSupported F p S) :
    IsPGroup p (L ≃ₐ[F] L) ∧
      (∀ (P : Ideal (NumberField.RingOfIntegers ↥L)), P.IsPrime → P ≠ ⊥ →
        P ∣ differentIdeal (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers ↥L) →
          ∃ q ∈ S, P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ))) := by
  classical
  let ι := Submission.NumberField.SupportedPField F p S
  let f : ι → IntermediateField F (AlgebraicClosure F) := fun i => i.L
  have hfd_f : ∀ i : ι, FiniteDimensional F ↥(f i) := fun i => i.hfd
  have hgal_f : ∀ i : ι, IsGalois F ↥(f i) := fun i => i.hgal
  have hnum_f : ∀ i : ι, NumberField ↥(f i) := fun i => i.hnum
  have hpg_f : ∀ i : ι, IsPGroup p (↥(f i) ≃ₐ[F] ↥(f i)) := fun i => i.hpg
  have hsupp_f : ∀ i : ι, ∀ (P : Ideal (NumberField.RingOfIntegers ↥(f i))), P.IsPrime →
      P ≠ ⊥ →
      P ∣ differentIdeal (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers ↥(f i)) →
        ∃ q ∈ S, P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ)) := fun i => i.hsupp
  haveI hfdI : ∀ i : ι, FiniteDimensional F ↥(f i) := hfd_f
  haveI hgalI : ∀ i : ι, IsGalois F ↥(f i) := hgal_f
  haveI hnumI : ∀ i : ι, NumberField ↥(f i) := hnum_f
  have hle : L ≤ ⨆ i, f i := hL
  refine ⟨Commons.FieldTheory.Galois.isPGroup_aut_of_le_iSup_finite_galois_pGroup
    (F := F) (K := AlgebraicClosure F) (p := p) (f := f) hfd_f hgal_f hpg_f hle, ?_⟩
  exact Commons.NumberTheory.NumberField.differentIdeal_supp_le_iSup_finset (F := F) S
    hfd_f hgal_f hsupp_f hle

/-- **A finite Galois extension with `S`-supported different and pro-`p` Galois group is inside
`k_S`** (it is a `SupportedPField`, and `k_S` is the supremum of those). -/
theorem le_kSupported_of_supp_proP {F : Type} [Field F] [NumberField F] {p : ℕ} [Fact p.Prime]
    (S : Finset ℕ) {L : IntermediateField F (AlgebraicClosure F)}
    [FiniteDimensional F L] [IsGalois F L] [NumberField ↥L]
    (hpg : IsPGroup p (L ≃ₐ[F] L))
    (hsupp : ∀ (P : Ideal (NumberField.RingOfIntegers ↥L)), P.IsPrime → P ≠ ⊥ →
      P ∣ differentIdeal (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers ↥L) →
        ∃ q ∈ S, P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ))) :
    L ≤ kSupported F p S :=
  le_kSupported ⟨L, hpg, hsupp⟩

/-- **The maximal unramified finite Galois subextension of `k_S` is `k_∅`**: every finite Galois
unramified pro-`p` extension of `F` lies in `k_∅`. -/
theorem le_kSupported_empty_of_unramified {F : Type} [Field F] [NumberField F] {p : ℕ}
    [Fact p.Prime] {L : IntermediateField F (AlgebraicClosure F)}
    [FiniteDimensional F L] [IsGalois F L] [NumberField ↥L]
    (hpg : IsPGroup p (L ≃ₐ[F] L))
    (hunr : differentIdeal (NumberField.RingOfIntegers F)
      (NumberField.RingOfIntegers ↥L) = ⊤) :
    L ≤ kSupported F p (∅ : Finset ℕ) := by
  refine le_kSupported_of_supp_proP (p := p) (∅ : Finset ℕ) hpg ?_
  intro P hP hPne hPdvd
  rw [hunr] at hPdvd
  obtain ⟨J, hJ⟩ := hPdvd
  have htop : (⊤ : Ideal (NumberField.RingOfIntegers ↥L)) ≤ P := by
    calc (⊤ : Ideal (NumberField.RingOfIntegers ↥L)) = P * J := hJ
      _ ≤ P * ⊤ := by exact Ideal.mul_mono_right le_top
      _ = P := Ideal.mul_top P
  exact absurd (top_le_iff.mp htop) hP.ne_top

end Work.ShafarevichKoch
