import Submission.Work.SSGRoute.PTDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Poitou–Tate `Ext` core — levels inside a fixed algebraic closure (DEFINITIONS ONLY)

Addendum to `PTDefs` (ssg5 repair, see `requests/ssg5/DESIGN_FIX.md`).  To be created as
`Submission/Work/SSGRoute/PTDefsOmega.lean`; append-only, `PTDefs` is unchanged.

`PhiOneVanishes` quantifies over *all types* `L`.  A compatible family of functionals indexed by all
types cannot be built by a choice on a colimit (the index is not a set).  Here the levels are the
finite Galois intermediate fields `L` of a fixed `Ω ⊇ K`, a set, directed by `≤`, so direct limits
over levels exist and choices can be made once on the limit.
-/

open CategoryTheory

noncomputable section

namespace SSGRoute.PTExt

section OmegaLevels

variable {k K Ω : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [Field Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]

/-- Inflation `H^n(Gal(L/k), C_L) → H^n(Gal(L'/k), C_{L'})` along an inclusion of levels
`L ≤ L'` of `Ω`. -/
def inflCIn {L L' : IntermediateField K Ω} (h : L ≤ L') [NumberField L] [NumberField L']
    [FiniteDimensional k L] [IsGalois k L] {n : ℕ} (y : extH (classesK k L) n) :
    extH (classesK k L') n :=
  letI : Algebra L L' := (IntermediateField.inclusion h).toAlgebra
  haveI : IsScalarTower k L L' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  inflC (k := k) (K := L) (L := L') y

/-- Inflation of `H^n(Gal(L/k), V)` to `L' ≥ L` for a trivial module `V`. -/
def inflTrivIn {L L' : IntermediateField K Ω} (h : L ≤ L') [FiniteDimensional k L] [IsGalois k L]
    (V : Type) [AddCommGroup V] [Module Coeff V] {n : ℕ}
    (y : extH (Rep.trivial Coeff (L ≃ₐ[k] L) V) n) : extH (Rep.trivial Coeff (L' ≃ₐ[k] L') V) n :=
  letI : Algebra L L' := (IntermediateField.inclusion h).toAlgebra
  haveI : IsScalarTower k L L' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  inflTriv (k := k) (K := L) (L := L') V y

/-- Inflation `H^n(Gal(L/k), M) → H^n(Gal(L'/k), M)` for a `Gal(K/k)`-module `M`. -/
def inflHIn [IsGalois k K] {L L' : IntermediateField K Ω} (h : L ≤ L') [IsGalois k L]
    {M : Rep Coeff (K ≃ₐ[k] K)} {n : ℕ}
    (y : extH (Rep.res (galRes k K L) M) n) : extH (Rep.res (galRes k K L') M) n :=
  letI : Algebra L L' := (IntermediateField.inclusion h).toAlgebra
  haveI : IsScalarTower k L L' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower K L L' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  inflHLevel (k := k) (K := K) (L := L) (L' := L') y

variable (Ω) in
/-- **`φ¹` vanishes at `x` on the levels of `Ω`**: `x ∈ Ext¹_{Gal(K/k)}(M, C_K)` pairs to zero
with every `h ∈ H¹(Gal(L/k), M)` for every finite Galois level `K ≤ L ≤ Ω`.  (Implied by
`PhiOneVanishes k K x`.) -/
def PhiOneVanishesIn [FiniteDimensional k K] [IsGalois k K] {M : Rep Coeff (K ≃ₐ[k] K)}
    (x : Abelian.Ext.{0} M (classesK k K) 1) : Prop :=
  ∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
    (h : extH (Rep.res (galRes k K L) M) 1), phiAt (k := k) (K := K) (L := L) x h = 0

end OmegaLevels

end SSGRoute.PTExt
