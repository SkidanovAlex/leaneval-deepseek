import Mathlib
import Submission.Work.Tower.Unramified.Basic
import Submission.Work.Tower.Unramified.MaxElemAb
import Submission.Work.Tower.Unramified.Compositum
import Submission.Work.Tower.Unramified.isUnramifiedExtensionForallPrimes_sup

/-!
# `maxElemAbUnram3 F` is an unramified elementary abelian `3`-extension of `F`

`Work.Tower.maxElemAbUnram3 F` is the compositum (inside `AlgebraicClosure F`) of all finite
everywhere-unramified elementary abelian `3`-extensions of `F`.  In this file we show that,
whenever this compositum happens to be finite dimensional over `F`, it is *itself* a finite
everywhere-unramified elementary abelian `3`-extension of `F`; in particular
`maxElemAbUnram3 F / F` is everywhere unramified.

The proof proceeds in three steps.

* The base field `⊥ ≅ F` is a finite unramified elementary abelian `3`-extension of itself
  (`bot_isUnramified`, `bot_isElementaryAbelianThreeExtension`), so the defining family `S` of
  `maxElemAbUnram3 F` is nonempty.
* The family `S` is *closed under `⊔`*: the compositum of two finite unramified elementary abelian
  `3`-extensions is again one.  Unramifiedness of a compositum is
  `Work.Tower.isUnramifiedExtension_sup`; for the group-theoretic part we use that the restriction
  map `Gal(K ⊔ L / F) →* Gal(K/F) × Gal(L/F)` is injective
  (`IntermediateField.restrictNormalHomSupProd_injective`), so the exponent-`3` condition of the
  factors passes to the compositum.
* Finally, in a *directed* (`⊔`-closed) family of intermediate fields whose supremum is finite
  dimensional over `F`, the supremum is attained by a member of the family
  (`exists_eq_sSup_of_isSupClosed`): take a member of maximal `F`-dimension.

Since `maxElemAbUnram3 F = sSup S`, the last point exhibits `maxElemAbUnram3 F` as a member of
`S`, so all the defining properties transfer to it.

## Main results

* `Work.Tower.Unramified.maxElemAbUnram3_isUnramified`;
* `Work.Tower.Unramified.maxElemAbUnram3_isElementaryAbelianThreeExtension`.
-/

open NumberField
open scoped Classical nonZeroDivisors

namespace Work.Tower.Unramified

/-! ### The base field -/

/-- The trivial extension `⊥ ≅ F` of `F` is everywhere unramified: the canonical map
`𝓞 F → 𝓞 ↥⊥` is surjective, so the extension of rings of integers is formally unramified. -/
theorem bot_isUnramified (F : Type*) [Field F] [NumberField F] :
    Work.Tower.IsUnramifiedExtension F ↥(⊥ : IntermediateField F (AlgebraicClosure F)) := by
  let A := ↥(⊥ : IntermediateField F (AlgebraicClosure F))
  let e : A ≃ₐ[F] F := IntermediateField.botEquiv F (AlgebraicClosure F)
  have key : ∀ z : A, algebraMap F A (e z) = z := by
    intro z
    exact e.injective (by simpa using e.commutes (e z))
  refine Work.Tower.IsUnramifiedExtension.of_forallPrimes ?_
  rw [isUnramifiedExtensionForallPrimes_iff_formallyUnramified
    (E := (⊥ : IntermediateField F (AlgebraicClosure F)))]
  refine Algebra.FormallyUnramified.of_surjective (Algebra.ofId (𝓞 F) (𝓞 A)) ?_
  intro x
  refine ⟨RingOfIntegers.mapRingHom (e : A →+* F) x, ?_⟩
  apply RingOfIntegers.ext
  change (algebraMap F A) ((RingOfIntegers.mapRingHom (e : A →+* F) x : 𝓞 F) : F) = (x : A)
  rw [RingOfIntegers.mapRingHom_apply]
  exact key (x : A)

/-- The trivial extension `⊥ ≅ F` of `F` is an elementary abelian `3`-extension of `F`: its
Galois group is trivial, hence of exponent dividing `3`. -/
theorem bot_isElementaryAbelianThreeExtension (F : Type*) [Field F] [NumberField F] :
    Work.Tower.IsElementaryAbelianThreeExtension F (⊥ : IntermediateField F (AlgebraicClosure F)) := by
  refine ⟨inferInstance, fun σ => ?_⟩
  have h1 : σ = 1 := by
    apply AlgEquiv.ext
    intro x
    obtain ⟨y, hy⟩ := (IntermediateField.mem_bot (F := F) (E := AlgebraicClosure F)).mp x.2
    have hx : x = algebraMap F ↥(⊥ : IntermediateField F (AlgebraicClosure F)) y :=
      Subtype.ext (by simpa using hy.symm)
    rw [hx, AlgEquiv.commutes, AlgEquiv.one_apply]
  rw [h1]
  simp

/-! ### The defining family of `maxElemAbUnram3` -/

/-- The defining family of `Work.Tower.maxElemAbUnram3`: the finite everywhere unramified
elementary abelian `3`-extensions of `F` inside `AlgebraicClosure F`. -/
def unramifiedElemAbThreeSet (F : Type*) [Field F] [NumberField F] :
    Set (IntermediateField F (AlgebraicClosure F)) :=
  {E | FiniteDimensional F E ∧ Work.Tower.IsUnramifiedExtension F E ∧
    Work.Tower.IsElementaryAbelianThreeExtension F E}

/-- `maxElemAbUnram3 F` is the supremum of its defining family. -/
theorem maxElemAbUnram3_eq_sSup (F : Type*) [Field F] [NumberField F] :
    Work.Tower.maxElemAbUnram3 F = sSup (unramifiedElemAbThreeSet F) := rfl

/-! ### Closure under composita -/

/-- **The compositum of two elementary abelian `3`-extensions is elementary abelian of
exponent three.**  The compositum of two Galois extensions is Galois, and restriction of an
automorphism of the compositum to the two factors is injective
(`IntermediateField.restrictNormalHomSupProd_injective`); since both factors have exponent
dividing `3`, so does the compositum. -/
theorem isElementaryAbelianThreeExtension_sup {F L : Type*} [Field F] [Field L] [Algebra F L]
    {E₁ E₂ : IntermediateField F L}
    (h₁ : Work.Tower.IsElementaryAbelianThreeExtension F E₁)
    (h₂ : Work.Tower.IsElementaryAbelianThreeExtension F E₂) :
    Work.Tower.IsElementaryAbelianThreeExtension F (E₁ ⊔ E₂) := by
  haveI : IsGalois F ↥E₁ := h₁.1
  haveI : IsGalois F ↥E₂ := h₂.1
  haveI : Normal F ↥E₁ := h₁.1.to_normal
  haveI : Normal F ↥E₂ := h₂.1.to_normal
  refine ⟨inferInstance, fun σ => ?_⟩
  have hker : (IntermediateField.restrictNormalHomSupProd E₁ E₂).ker = ⊥ :=
    (MonoidHom.ker_eq_bot_iff _).mpr (IntermediateField.restrictNormalHomSupProd_injective E₁ E₂)
  have hmem : σ ^ 3 ∈ (IntermediateField.restrictNormalHomSupProd E₁ E₂).ker := by
    rw [MonoidHom.mem_ker, map_pow]
    exact Prod.ext (by simpa using h₁.2 _) (by simpa using h₂.2 _)
  rw [hker] at hmem
  simpa using hmem

/-- The defining family of `maxElemAbUnram3` is closed under composita. -/
theorem unramifiedElemAbThreeSet_sup_mem (F : Type*) [Field F] [NumberField F]
    {E₁ E₂ : IntermediateField F (AlgebraicClosure F)}
    (h₁ : E₁ ∈ unramifiedElemAbThreeSet F) (h₂ : E₂ ∈ unramifiedElemAbThreeSet F) :
    E₁ ⊔ E₂ ∈ unramifiedElemAbThreeSet F := by
  obtain ⟨h₁fin, h₁unr, h₁el⟩ := h₁
  obtain ⟨h₂fin, h₂unr, h₂el⟩ := h₂
  haveI : FiniteDimensional F ↥E₁ := h₁fin
  haveI : FiniteDimensional F ↥E₂ := h₂fin
  haveI : IsGalois F ↥E₁ := h₁el.1
  haveI : IsGalois F ↥E₂ := h₂el.1
  exact ⟨inferInstance, Work.Tower.isUnramifiedExtension_sup h₁unr h₂unr,
    isElementaryAbelianThreeExtension_sup h₁el h₂el⟩

/-! ### The supremum of a directed family is attained -/

/-- **A sup-closed family of finite dimensional intermediate fields with finite dimensional
supremum has a greatest member.**  If `S` is nonempty, closed under `⊔`, all of whose members are
finite dimensional over `F`, and `sSup S` is finite dimensional over `F`, then `sSup S ∈ S`
(and `sSup S` is the greatest element of `S`).

Indeed, the `F`-dimensions of the members of `S` are natural numbers bounded by
`[sSup S : F]`; let `E₀ ∈ S` have maximal dimension.  For any `E ∈ S` also `E ⊔ E₀ ∈ S`, and
`[E ⊔ E₀ : F] ≤ [E₀ : F]` by maximality while `[E₀ : F] ≤ [E ⊔ E₀ : F]` by monotonicity, so
`E ⊔ E₀ = E₀` and `E ≤ E₀`. -/
theorem exists_eq_sSup_of_isSupClosed {F L : Type*} [Field F] [Field L] [Algebra F L]
    (S : Set (IntermediateField F L)) (hne : S.Nonempty)
    (hdir : ∀ E ∈ S, ∀ E' ∈ S, E ⊔ E' ∈ S)
    (hfin : ∀ E ∈ S, FiniteDimensional F E)
    (hK : FiniteDimensional F ↥(sSup S)) :
    ∃ E ∈ S, sSup S = E := by
  let T : Set ℕ := {n | ∃ E ∈ S, Module.finrank F ↥E = n}
  have hTne : T.Nonempty := ⟨_, hne.some, hne.some_mem, rfl⟩
  have hbdd : BddAbove T := by
    refine ⟨Module.finrank F ↥(sSup S), ?_⟩
    rintro n ⟨E, hE, rfl⟩
    haveI := hfin E hE
    exact IntermediateField.finrank_le_of_le_right (le_sSup hE)
  obtain ⟨E₀, hE₀S, hE₀fin⟩ := Nat.sSup_mem hTne hbdd
  refine ⟨E₀, hE₀S, le_antisymm (sSup_le ?_) (le_sSup hE₀S)⟩
  intro E hE
  haveI := hfin E hE
  haveI := hfin E₀ hE₀S
  haveI := hfin (E ⊔ E₀) (hdir E hE E₀ hE₀S)
  have h1 : Module.finrank F ↥E₀ ≤ Module.finrank F ↥(E ⊔ E₀) :=
    IntermediateField.finrank_le_of_le_right (le_sup_right : E₀ ≤ E ⊔ E₀)
  have h2 : Module.finrank F ↥(E ⊔ E₀) ≤ sSup T :=
    le_csSup hbdd ⟨E ⊔ E₀, hdir E hE E₀ hE₀S, rfl⟩
  rw [← hE₀fin] at h2
  have h4 : E₀ = E ⊔ E₀ :=
    IntermediateField.eq_of_le_of_finrank_eq (le_sup_right : E₀ ≤ E ⊔ E₀) (le_antisymm h1 h2)
  rw [h4]
  exact le_sup_left

/-- **If `maxElemAbUnram3 F` is finite over `F`, it is a member of its own defining family.**
Equivalently, it is a *finite* everywhere unramified elementary abelian `3`-extension of `F`,
and it is the greatest such. -/
theorem exists_mem_unramifiedElemAbThreeSet_eq_maxElemAbUnram3 (F : Type*) [Field F]
    [NumberField F] (h : FiniteDimensional F ↥(Work.Tower.maxElemAbUnram3 F)) :
    ∃ E ∈ unramifiedElemAbThreeSet F, Work.Tower.maxElemAbUnram3 F = E := by
  have hfin : ∀ E ∈ unramifiedElemAbThreeSet F, FiniteDimensional F E := fun _ hE => hE.1
  have hne : (unramifiedElemAbThreeSet F).Nonempty :=
    ⟨⊥, inferInstance, bot_isUnramified F, bot_isElementaryAbelianThreeExtension F⟩
  rw [maxElemAbUnram3_eq_sSup]
  exact exists_eq_sSup_of_isSupClosed _ hne
    (fun E hE E' hE' => unramifiedElemAbThreeSet_sup_mem F hE hE') hfin h

/-! ### The main result -/

/-- **`maxElemAbUnram3 F` is unramified over `F`** (assuming it is finite over `F`). -/
theorem maxElemAbUnram3_isUnramified (F : Type*) [Field F] [NumberField F]
    (h : FiniteDimensional F ↥(Work.Tower.maxElemAbUnram3 F)) :
    Work.Tower.IsUnramifiedExtension F ↥(Work.Tower.maxElemAbUnram3 F) := by
  obtain ⟨E, hE, hEq⟩ := exists_mem_unramifiedElemAbThreeSet_eq_maxElemAbUnram3 F h
  rw [hEq]
  exact hE.2.1

/-- **`maxElemAbUnram3 F` is an elementary abelian `3`-extension of `F`** (assuming it is finite
over `F`): it is Galois over `F` with every automorphism of order dividing `3`. -/
theorem maxElemAbUnram3_isElementaryAbelianThreeExtension (F : Type*) [Field F] [NumberField F]
    (h : FiniteDimensional F ↥(Work.Tower.maxElemAbUnram3 F)) :
    Work.Tower.IsElementaryAbelianThreeExtension F (Work.Tower.maxElemAbUnram3 F) := by
  obtain ⟨E, hE, hEq⟩ := exists_mem_unramifiedElemAbThreeSet_eq_maxElemAbUnram3 F h
  rw [hEq]
  exact hE.2.2

end Work.Tower.Unramified
