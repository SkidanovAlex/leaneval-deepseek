import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.NK.CFTLib.ARL.AuxField
import Submission.NK.CFTLib.ARLAlt.AuxLocal
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Base change of intermediate fields, and the field-theoretic setup of the transfer

The transfer argument of Artin's lemma (Lang, *Algebraic Number Theory*, X §2, Theorem 2;
Childress, *Class Field Theory*, Prop. 2.2) applies the cyclotomic cell
(`NK.CFTLib.ARL.cyclotomicCellKernelLe_B`) to the field `LE𝔭 = E𝔭·L` inside the cyclotomic
field `Ω = L(ζ_M)`, with the *auxiliary field* `E𝔭` as the base.  Since Mathlib's
`IntermediateField` API has no base change along an inclusion of intermediate fields, we provide
it here:

* `NK.CFTLib.ARLAlt.ofLe E F h` — for `K`-intermediate fields `E ≤ F` of `Ω`, the field `F` as an
  `↥E`-intermediate field of `Ω` (its carrier is `F`, so the underlying type is `↥F`);
* the identification of `LΩ = (⊥ : IntermediateField L Ω).restrictScalars K` with `L` over `K`, and
  the resulting `IsGalois`/`FiniteDimensional` instances;
* `IsGalois`, `IsMulCommutative` and `IsCyclotomicExtension` for the base-changed fields.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open NumberField IsDedekindDomain
open scoped NumberField

noncomputable section

namespace NK.CFTLib.ARLAlt

/-- Base change of a `K`-intermediate field `F ⊇ E` of `Ω` to an intermediate field of `Ω` over
`↥E`.  The carrier is `F`, so that the underlying type of `ofLe E F h` is (definitionally) `↥F`,
while the algebra structure is the one over `↥E`. -/
def ofLe {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
    (E F : IntermediateField K Ω) (h : E ≤ F) : IntermediateField ↥E Ω where
  carrier := F
  mul_mem' := F.mul_mem
  one_mem' := F.one_mem
  add_mem' := F.add_mem
  zero_mem' := F.zero_mem
  algebraMap_mem' := fun (e : ↥E) => h e.2
  inv_mem' := by intro x hx; exact F.inv_mem hx

@[simp] lemma coe_ofLe {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
    (E F : IntermediateField K Ω) (h : E ≤ F) :
    ((ofLe E F h : IntermediateField ↥E Ω) : Set Ω) = (F : Set Ω) := rfl

@[simp] lemma mem_ofLe {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
    (E F : IntermediateField K Ω) (h : E ≤ F) (x : Ω) :
    x ∈ ofLe E F h ↔ x ∈ F := Iff.rfl

lemma ofLe_le {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
    (E F F' : IntermediateField K Ω) (h : E ≤ F) (h' : E ≤ F') (hFF' : F ≤ F') :
    ofLe E F h ≤ ofLe E F' h' := hFF'

section LImage

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- The image of `L` in `Ω = CyclotomicField M L`, as a `K`-intermediate field. -/
abbrev LImage (M : ℕ) : IntermediateField K (CyclotomicField M L) :=
  (⊥ : IntermediateField L (CyclotomicField M L)).restrictScalars K

/-- `L`, viewed inside `Ω = CyclotomicField M L` (`K`-algebra map onto `LImage`). -/
def toLImage (M : ℕ) : L →ₐ[K] ↥(LImage (K := K) (L := L) M) where
  toFun x := ⟨algebraMap L (CyclotomicField M L) x, IntermediateField.mem_bot.mpr ⟨x, rfl⟩⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp
  map_add' x y := by ext; simp
  map_zero' := by ext; simp
  commutes' k := by
    ext
    exact (IsScalarTower.algebraMap_apply K L (CyclotomicField M L) k).symm

lemma toLImage_injective (M : ℕ) : Function.Injective (toLImage (K := K) (L := L) M) := by
  intro x y h
  have h1 : algebraMap L (CyclotomicField M L) x = algebraMap L (CyclotomicField M L) y := by
    have := congrArg (fun z : ↥(LImage (K := K) (L := L) M) => (z : CyclotomicField M L)) h
    simpa [toLImage] using this
  exact FaithfulSMul.algebraMap_injective L (CyclotomicField M L) h1

lemma toLImage_surjective (M : ℕ) : Function.Surjective (toLImage (K := K) (L := L) M) := by
  intro y
  obtain ⟨x, hx⟩ := IntermediateField.mem_bot.mp y.2
  exact ⟨x, Subtype.ext hx⟩

/-- **The identification of the image of `L` in `Ω = CyclotomicField M L` with `L`**, over `K`. -/
noncomputable def LImageEquiv (M : ℕ) : ↥(LImage (K := K) (L := L) M) ≃ₐ[K] L :=
  (AlgEquiv.ofBijective (toLImage (K := K) (L := L) M)
    ⟨toLImage_injective M, toLImage_surjective M⟩).symm

instance isGalois_LImage (M : ℕ) : IsGalois K ↥(LImage (K := K) (L := L) M) :=
  IsGalois.of_algEquiv (LImageEquiv (K := K) (L := L) M).symm

end LImage

section CellSetup

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- **The composite `E·L` is Galois over the auxiliary field `E`** (inside `Ω = L(ζ_M)`). -/
theorem isGalois_ofLe_sup (M : ℕ) (E : IntermediateField K (CyclotomicField M L)) :
    IsGalois ↥E
      ↥(ofLe E (E ⊔ LImage (K := K) (L := L) M) (le_sup_left)) := by
  classical
  set LΩ := LImage (K := K) (L := L) M with hLΩdef
  set C := E ⊔ LΩ with hCdef
  have hEC : E ≤ C := le_sup_left
  have hLC : LΩ ≤ C := le_sup_right
  letI : Algebra ↥E ↥C := inferInstanceAs (Algebra ↥E ↥(ofLe E C hEC))
  let E' : IntermediateField K ↥C := E.restrict hEC
  let L' : IntermediateField K ↥C := LΩ.restrict hLC
  have hsup : L' ⊔ E' = ⊤ := by
    refine IntermediateField.lift_injective (K := K) (L := CyclotomicField M L) C ?_
    rw [IntermediateField.lift_sup, IntermediateField.lift_top,
      IntermediateField.lift_restrict, IntermediateField.lift_restrict]
    exact (sup_comm (a := LΩ) (b := E)).trans hCdef.symm
  haveI hgalL' : IsGalois K ↥L' := by
    haveI : IsGalois K ↥(IntermediateField.lift (F := C) L') := by
      rw [IntermediateField.lift_restrict]
      exact isGalois_LImage (K := K) (L := L) M
    exact IsGalois.of_algEquiv (IntermediateField.liftAlgEquiv L').symm
  haveI hgalC : IsGalois ↥E' ↥C := IsGalois.sup_right (F := K) L' E' hsup
  let f : ↥E' ≃+* ↥E :=
    { toFun := fun x => ⟨x.1.1, (IntermediateField.mem_restrict hEC x.1).mp x.2⟩
      invFun := fun y => ⟨⟨y.1, hEC y.2⟩,
        (IntermediateField.mem_restrict hEC ⟨y.1, hEC y.2⟩).mpr y.2⟩
      left_inv := fun x => by ext; rfl
      right_inv := fun y => by ext; rfl
      map_mul' := fun x y => by ext; rfl
      map_add' := fun x y => by ext; rfl }
  refine IsGalois.of_equiv_equiv (F := ↥E') (E := ↥C) (M := ↥E) (N := ↥C)
    (f := f) (g := RingEquiv.refl ↥C) ?_
  ext x
  rfl

/-- **The cyclotomic structure of `Ω = L(ζ_M)` over the auxiliary field `E`**, from the
`ℚ`-form of the join hypothesis of `NK.CFTLib.ARL.AuxFieldHyp`:
`E ⊔ ℚ(ζ_M) = Ω`. -/
theorem isCyclotomicExtension_of_sup_adjoin_zeta (M : ℕ) [NeZero M]
    (E : IntermediateField K (CyclotomicField M L))
    (h : (E.restrictScalars ℚ) ⊔ (IntermediateField.adjoin ℚ
      ({IsCyclotomicExtension.zeta M L (CyclotomicField M L)} : Set (CyclotomicField M L))) = ⊤) :
    IsCyclotomicExtension {M} ↥E (CyclotomicField M L) := by
  classical
  refine isCyclotomicExtension_of_adjoin_eq_top (n := M)
    (IsCyclotomicExtension.zeta_spec M L (CyclotomicField M L)) (eq_top_iff.mpr ?_)
  intro x _
  have hx : x ∈ (E.restrictScalars ℚ) ⊔ (IntermediateField.adjoin ℚ
      ({IsCyclotomicExtension.zeta M L (CyclotomicField M L)} : Set (CyclotomicField M L))) := by
    rw [h]; exact IntermediateField.mem_top
  have hle : (E.restrictScalars ℚ) ⊔ (IntermediateField.adjoin ℚ
      ({IsCyclotomicExtension.zeta M L (CyclotomicField M L)} : Set (CyclotomicField M L)))
      ≤ (IntermediateField.adjoin ↥E
        ({IsCyclotomicExtension.zeta M L (CyclotomicField M L)} : Set (CyclotomicField M L))).restrictScalars ℚ := by
    refine sup_le ?_ ?_
    · intro y hy
      exact (IntermediateField.adjoin ↥E
        ({IsCyclotomicExtension.zeta M L (CyclotomicField M L)} : Set (CyclotomicField M L))).algebraMap_mem
        (⟨y, hy⟩ : ↥E)
    · refine IntermediateField.adjoin_le_iff.mpr ?_
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact IntermediateField.subset_adjoin ↥E _ (Set.mem_singleton _)
  exact hle hx

/-- **The composite `E·L` has commutative Galois group over `E`.** -/
theorem isMulCommutative_ofLe_sup (M : ℕ) [NeZero M]
    (E : IntermediateField K (CyclotomicField M L))
    (h : (E.restrictScalars ℚ) ⊔ (IntermediateField.adjoin ℚ
      ({IsCyclotomicExtension.zeta M L (CyclotomicField M L)} : Set (CyclotomicField M L))) = ⊤) :
    IsMulCommutative
      (↥(ofLe E (E ⊔ LImage (K := K) (L := L) M) (le_sup_left)) ≃ₐ[↥E]
        ↥(ofLe E (E ⊔ LImage (K := K) (L := L) M) (le_sup_left))) := by
  classical
  haveI hcyc : IsCyclotomicExtension {M} ↥E (CyclotomicField M L) :=
    isCyclotomicExtension_of_sup_adjoin_zeta (K := K) (L := L) M E h
  haveI hab : IsAbelianGalois ↥E (CyclotomicField M L) :=
    IsCyclotomicExtension.isAbelianGalois {M} ↥E (CyclotomicField M L)
  haveI hcomm : IsMulCommutative (Gal((CyclotomicField M L)/↥E)) := hab.toIsMulCommutative
  haveI hgalC : IsGalois ↥E ↥(ofLe E (E ⊔ LImage (K := K) (L := L) M) (le_sup_left)) :=
    isGalois_ofLe_sup (K := K) (L := L) M E
  let Φ : Gal((CyclotomicField M L)/↥E) →*
      Gal(↥(ofLe E (E ⊔ LImage (K := K) (L := L) M) (le_sup_left))/↥E) :=
    AlgEquiv.restrictNormalHom (F := ↥E)
      (E := ↥(ofLe E (E ⊔ LImage (K := K) (L := L) M) (le_sup_left)))
      (K₁ := CyclotomicField M L)
  have hsurj : Function.Surjective Φ :=
    AlgEquiv.restrictNormalHom_surjective (F := ↥E)
      (K₁ := ↥(ofLe E (E ⊔ LImage (K := K) (L := L) M) (le_sup_left)))
      (E := CyclotomicField M L)
  refine { is_comm.comm := fun a b => ?_ }
  obtain ⟨x, rfl⟩ := hsurj a
  obtain ⟨y, rfl⟩ := hsurj b
  rw [← map_mul, ← map_mul, IsMulCommutative.is_comm.comm x y]

end CellSetup

end NK.CFTLib.ARLAlt
