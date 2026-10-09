import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.overK
import Submission.Work.SSGRoute.overK_finiteDimensional_and_isGalois
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Base-change plumbing `ℚ ↔ ↥K` for the "distinct primes of `K`" Grünwald statement

The Grünwald surjectivity theorem of `Work.SSGRoute.grunwald_surjective_E` prescribes local data on
the decomposition groups `D_A` of a finite set `T` of finite places of `ℚ̄` which are pairwise
*non-conjugate* over `ℚ`, i.e. one place per rational prime.  When `T` contains several places over
the same rational prime `ℓ` (the typical situation of Step 4, where `T` consists of the conjugates
of a completely split prime of `K`), the correct hypothesis is that distinct places of `T` have
distinct restrictions to `K`, and the natural way to exploit it is to apply the *same* Grünwald
theorem with the base field `↥K`: over `↥K`, "same restriction to `K`" is exactly
`Gal(ℚ̄/↥K)`-conjugacy (`Work.SSGRoute.isConjPlace_over_K_iff_comap_eq`).

This module provides the plumbing for that base change:

* `smul_congr` — an element of `Gal(ℚ̄/↥K)` and the corresponding element of `G_ℚ` (same underlying
  function) act in the same way on a valuation subring;
* `decompDownHom`, `decompUpHom` — for a place `A` split in `K` (`D_A ≤ G_K`), the identification of
  the decomposition groups `D_A ≤ G_ℚ` and `D_A ≤ Gal(ℚ̄/↥K)`, which are equal as sets of
  functions; `decompDownHom_comp_decompUpHom` records that they are mutually inverse on
  underlying functions;
* `patchFun` — the extension of a function on `Gal(ℚ̄/↥K)` to `G_ℚ` by `0` outside `G_K`;
* `mem_fixingSubgroup_bot` — every element of `Gal(ℚ̄/↥K)` fixes `⊥ ≤ ℚ̄`.
-/

open scoped Pointwise

namespace Work.SSGRoute

open SSGRoute

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

section Defs

variable (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K]

/-- Two `AlgEquiv`s, one over `↥K` and one over `ℚ`, with the same underlying function act in the
same way on a valuation subring. -/
lemma smul_congr {A : ValuationSubring SSGRoute.QBar}
    {x : SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar} {σ : SSGRoute.GalQ} (h : ⇑x = ⇑σ) :
    x • A = σ • A := by
  apply ValuationSubring.ext
  intro y
  rw [ValuationSubring.mem_smul_pointwise_iff_exists,
    ValuationSubring.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨s, hs, hx⟩
    exact ⟨s, hs, by rw [← hx, AlgEquiv.smul_def, AlgEquiv.smul_def, h]⟩
  · rintro ⟨s, hs, hx⟩
    exact ⟨s, hs, by rw [← hx, AlgEquiv.smul_def, AlgEquiv.smul_def, h]⟩

/-- The element of `G_ℚ` underlying `(fixingSubgroupEquiv K).symm x`. -/
lemma coe_symm_fixingSubgroupEquiv (x : SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar) :
    ⇑(((((IntermediateField.fixingSubgroupEquiv K).symm x : ↥(K.fixingSubgroup)) :
      SSGRoute.GalQ))) = ⇑x := rfl

/-- The element of `Gal(ℚ̄/↥K)` underlying `(fixingSubgroupEquiv K) ⟨σ, hσ⟩`. -/
lemma coe_fixingSubgroupEquiv (σ : SSGRoute.GalQ) (hσ : σ ∈ K.fixingSubgroup) :
    ⇑((IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ⟩) = ⇑σ := rfl

/-- Every element of `Gal(ℚ̄/↥K)` fixes the bottom field. -/
lemma mem_fixingSubgroup_bot {x : SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar} :
    x ∈ (⊥ : IntermediateField ↥K SSGRoute.QBar).fixingSubgroup := by
  rw [IntermediateField.fixingSubgroup_bot]
  exact Subgroup.mem_top x

/-- The restriction to `ℚ` of an element of `Gal(ℚ̄/↥K)` stabilising a place `A` over `↥K`. -/
noncomputable def decompDownHom (A : ValuationSubring SSGRoute.QBar)
    (hsplit : SSGRoute.decomp ℚ A ≤ K.fixingSubgroup) :
    ↥(SSGRoute.decomp ↥K A) →* ↥(SSGRoute.decomp ℚ A) :=
  MonoidHom.codRestrict
    (((K.fixingSubgroup).subtype.comp
        (IntermediateField.fixingSubgroupEquiv K).symm.toMonoidHom).comp
      (SSGRoute.decomp ↥K A).subtype)
    (SSGRoute.decomp ℚ A)
    (fun x => by
      have hx : x.1 • A = A := MulAction.mem_stabilizer_iff.mp x.2
      rw [SSGRoute.decomp, MulAction.mem_stabilizer_iff]
      rw [← smul_congr K (coe_symm_fixingSubgroupEquiv K x.1)]
      exact hx)

/-- The inclusion of `D_A ≤ G_ℚ` into `D_A ≤ Gal(ℚ̄/↥K)`, for a place `A` split in `K`. -/
noncomputable def decompUpHom (A : ValuationSubring SSGRoute.QBar)
    (hsplit : SSGRoute.decomp ℚ A ≤ K.fixingSubgroup) :
    ↥(SSGRoute.decomp ℚ A) →* ↥(SSGRoute.decomp ↥K A) :=
  MonoidHom.codRestrict
    ((IntermediateField.fixingSubgroupEquiv K).toMonoidHom.comp (Subgroup.inclusion hsplit))
    (SSGRoute.decomp ↥K A)
    (fun x => by
      have hx : (x : SSGRoute.GalQ) • A = A := MulAction.mem_stabilizer_iff.mp x.2
      rw [SSGRoute.decomp, MulAction.mem_stabilizer_iff]
      change ((IntermediateField.fixingSubgroupEquiv K) ((Subgroup.inclusion hsplit) x)) • A = A
      rw [smul_congr K (coe_fixingSubgroupEquiv K (Subgroup.inclusion hsplit x).1
        ((Subgroup.inclusion hsplit) x).2)]
      exact hx)

/-- `decompDownHom` inverts `decompUpHom`. -/
lemma decompDownHom_comp_decompUpHom (A : ValuationSubring SSGRoute.QBar)
    (hsplit : SSGRoute.decomp ℚ A ≤ K.fixingSubgroup) (x : ↥(SSGRoute.decomp ℚ A)) :
    decompDownHom K A hsplit (decompUpHom K A hsplit x) = x := by
  apply Subtype.ext
  apply AlgEquiv.ext
  intro y
  rfl

/-- The extension of a function on `Gal(ℚ̄/↥K)` to `G_ℚ`, by `0` outside `G_K`. -/
noncomputable def patchFun {M : Type} [Zero M]
    (z : (SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar) → M) : SSGRoute.GalQ → M :=
  fun σ => by
    classical
    exact if h : σ ∈ K.fixingSubgroup then
      z ((IntermediateField.fixingSubgroupEquiv K) ⟨σ, h⟩) else 0

/-- The value of `patchFun` on `K.fixingSubgroup`. -/
lemma patchFun_of_mem {M : Type} [Zero M] (z : (SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar) → M)
    (σ : SSGRoute.GalQ) (hσ : σ ∈ K.fixingSubgroup) :
    patchFun K z σ = z ((IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ⟩) := by
  classical
  simp only [patchFun, dif_pos hσ]

/-- The coercion of `decompDownHom K A hsplit x` to `G_ℚ` is the underlying function of `x`. -/
lemma coe_decompDownHom {A : ValuationSubring SSGRoute.QBar}
    (hsplit : SSGRoute.decomp ℚ A ≤ K.fixingSubgroup) (x : ↥(SSGRoute.decomp ↥K A)) :
    ⇑((decompDownHom K A hsplit x : ↥(SSGRoute.decomp ℚ A)) : SSGRoute.GalQ) = ⇑x.1 := rfl

/-- Finiteness of `overK K N` over `↥K`, without the (unused) Galois hypothesis of
`Work.SSGRoute.finiteDimensional_overK`. -/
theorem finiteDimensional_overK_of_finite (N : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ N] (hKN : K ≤ N) :
    FiniteDimensional ↥K (overK K N hKN) := by
  have : FiniteDimensional ℚ ↥(overK K N hKN) := (inferInstance : FiniteDimensional ℚ ↥N)
  have h := Module.finrank_mul_finrank ℚ ↥K ↥(overK K N hKN)
  have h2 : 0 < Module.finrank ℚ ↥K * Module.finrank ↥K ↥(overK K N hKN) := by
    rw [h]; exact Module.finrank_pos
  exact FiniteDimensional.of_finrank_pos (Nat.pos_of_mul_pos_left h2)

end Defs

end Work.SSGRoute
