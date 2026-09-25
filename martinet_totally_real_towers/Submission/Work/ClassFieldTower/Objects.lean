import Mathlib
import Submission.Work.ClassFieldTower.Defs

/-!
# `Work.ClassFieldTower.Objects` -- API for the maximal unramified pro-`p` extension

Basic consequences of the definition `Work.ClassFieldTower.MaximalUnramifiedProP`:

* `isPGroup_galoisGroup_of_finite`: if `G_∅` happens to be **finite**, then it is a finite
  `p`-group (this is the `hpro` hypothesis of the Golod--Shafarevich criterion
  `Work.ClassFieldTower.infinite_of_hasMinimalPresentation`); it is derived from the
  `proP` clause applied to `⊤ ≤ F_∅`, using Mathlib's `IsGalois.finiteDimensional_of_finite`;
* `exists_finite_galois_subfield_finrank_ge`: infinite `G_∅` gives finite dimensional Galois
  subextensions of `F_∅/F` of arbitrarily large `F`-degree (universe-general version of the
  Commons lemma `exists_finite_galois_finrank_ge_of_infinite_gal`);
* `differentIdeal_eq_top_of_finite_galois_subfield`: every finite dimensional Galois
  subextension of `F_∅/F` is unramified over `F`, i.e. has trivial relative different (this
  is the `unramified` clause, and it is what makes the root discriminant constant along the
  tower);
* `infinite_galoisGroup_iff_unbounded_subfields`: `G_∅` is infinite iff the finite
  dimensional Galois subextensions of `F_∅/F` have unbounded degree.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open scoped Classical
open scoped NumberField
open NumberField

noncomputable section

namespace Work.ClassFieldTower

/-- **Unbounded finite Galois levels in an infinite Galois extension** (universe-general form
of `Commons.FieldTheory.Galois.exists_finite_galois_finrank_ge_of_infinite_gal`). -/
theorem exists_finite_galois_finrank_ge_of_infinite {F K : Type*} [Field F] [Field K]
    [Algebra F K] [IsGalois F K] (h : Infinite Gal(K/F)) (n : ℕ) :
    ∃ L : IntermediateField F K, FiniteDimensional F L ∧ IsGalois F L ∧
      n ≤ Module.finrank F ↥L := by
  have hfd : ¬ FiniteDimensional F K := by
    intro hfd
    letI : FiniteDimensional F K := hfd
    haveI : Finite Gal(K/F) := by
      haveI : Fintype Gal(K/F) := AlgEquiv.fintype F K
      infer_instance
    exact not_finite (Gal(K/F))
  haveI : Algebra.IsAlgebraic F K := inferInstance
  obtain ⟨E, hEfd, hn⟩ := IntermediateField.exists_lt_finrank_of_infinite_dimensional hfd n
  refine ⟨IntermediateField.normalClosure F E K, ?_, ?_, ?_⟩
  · infer_instance
  · infer_instance
  · exact hn.le.trans (IntermediateField.finrank_le_of_le_right (IntermediateField.le_normalClosure E))

namespace MaximalUnramifiedProP

variable {F : Type*} [Field F] [NumberField F] {p : ℕ} [Fact p.Prime]

/-- **A finite `G_∅` is a finite `p`-group.**  This is the only place where the `proP` clause
of `MaximalUnramifiedProP` is used: it says `Gal(⊤/F) = Gal(F_∅/F)` is a `p`-group, and if
`G_∅` is finite then `F_∅` is finite dimensional over `F` (Mathlib's
`IsGalois.finiteDimensional_of_finite`), so `⊤ : IntermediateField F F_∅` is an admissible
`L` in the `proP` clause. -/
theorem isPGroup_galoisGroup_of_finite (M : MaximalUnramifiedProP F p)
    (hfin : Finite (galoisGroup M)) : IsPGroup p (galoisGroup M) := by
  haveI : Finite (M.K ≃ₐ[F] M.K) := hfin
  haveI : FiniteDimensional F M.K := IsGalois.finiteDimensional_of_finite (F := F) (E := M.K)
  haveI : FiniteDimensional F (⊤ : IntermediateField F M.K) := inferInstance
  haveI : IsGalois F (⊤ : IntermediateField F M.K) :=
    IsGalois.of_algEquiv (IntermediateField.topEquiv (F := F) (E := M.K)).symm
  have h := M.proP (⊤ : IntermediateField F M.K) inferInstance inferInstance
  exact h.of_equiv (AlgEquiv.autCongr (IntermediateField.topEquiv (F := F) (E := M.K)))

/-- **Every finite dimensional Galois subextension of `F_∅/F` is unramified over `F`.** -/
theorem differentIdeal_eq_top_of_finite_galois_subfield (M : MaximalUnramifiedProP F p)
    (L : IntermediateField F M.K) [NumberField ↥L] (hfd : FiniteDimensional F L)
    (hgal : IsGalois F L) : differentIdeal (𝓞 F) (𝓞 ↥L) = ⊤ :=
  M.unramified L hfd hgal

/-- **Infinitely many levels.**  If `G_∅` is infinite, then `F_∅/F` has finite dimensional
Galois subextensions of arbitrarily large `F`-degree. -/
theorem exists_finite_galois_subfield_finrank_ge (M : MaximalUnramifiedProP F p)
    (hinf : Infinite (galoisGroup M)) (N : ℕ) :
    ∃ L : IntermediateField F M.K, FiniteDimensional F L ∧ IsGalois F L ∧
      N ≤ Module.finrank F ↥L :=
  exists_finite_galois_finrank_ge_of_infinite (F := F) (K := M.K) hinf N

/-- **`G_∅` is infinite iff the finite levels have unbounded degree.** -/
theorem infinite_galoisGroup_iff_unbounded_subfields (M : MaximalUnramifiedProP F p) :
    Infinite (galoisGroup M) ↔
      ∀ N : ℕ, ∃ L : IntermediateField F M.K, FiniteDimensional F L ∧ IsGalois F L ∧
        N ≤ Module.finrank F ↥L := by
  constructor
  · intro hinf N
    exact M.exists_finite_galois_subfield_finrank_ge hinf N
  · intro h
    rw [← not_finite_iff_infinite]
    intro hfin
    obtain ⟨L, hfd, hgal, hdeg⟩ := h (Nat.card (M.K ≃ₐ[F] M.K) + 1)
    haveI : FiniteDimensional F L := hfd
    haveI : IsGalois F L := hgal
    have hsurj : Function.Surjective
        (AlgEquiv.restrictNormalHom (E := ↥L) (K₁ := M.K) :
          (M.K ≃ₐ[F] M.K) → (↥L ≃ₐ[F] ↥L)) :=
      AlgEquiv.restrictNormalHom_surjective (K₁ := ↥L) (E := M.K)
    have hle : Nat.card (↥L ≃ₐ[F] ↥L) ≤ Nat.card (M.K ≃ₐ[F] M.K) :=
      Nat.card_le_card_of_surjective _ hsurj
    rw [IsGalois.card_aut_eq_finrank F ↥L] at hle
    omega

end MaximalUnramifiedProP

end Work.ClassFieldTower
