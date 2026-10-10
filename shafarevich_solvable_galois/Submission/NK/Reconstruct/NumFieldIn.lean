import Mathlib.FieldTheory.Galois.GaloisClosure
import Mathlib.NumberTheory.NumberField.Basic
import Submission.NK.Reconstruct.Gamma
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Number fields inside `Ω`: the general base field of Shimizu's §4

Shimizu's Proposition 4f.3, Theorem 4.0 and Proposition 4f.5 are stated for **arbitrary** number
fields `K₁`, `K₂` inside a common separable closure `Ω`, with an auxiliary field `L` that is finite
Galois *over `ℚ`* and contains `K₁K₂`.  The chain of this area (`prop4f3.lean`, `hausPi.lean`,
`hausRank.lean`, `fourf5Rank.lean`, `exists_isomorphism_of_prop4f3_data.lean`, …) was originally
stated with the *base fields themselves* required to be finite Galois over `ℚ` (i.e. as
`FrobLevel ℚ Ω`), which is stronger than Shimizu's hypothesis and is exactly what prevents applying
the assembly to the level pairs `(L, levelMap ϕ L)` of the reconstruction step.

This file supplies the missing vocabulary:

* `NK.Reconstruct.NumFieldIn K K'` — a finite number-field level of `K'/K`: an intermediate field
  together with its `FiniteDimensional` and `NumberField` instances, carried as fields of the
  structure (the `FrobLevel` trick).  `NumFieldIn ℚ Ω` is the general base field of §4: an arbitrary
  number field inside `Ω`, with no normality assumption;
* `NK.Reconstruct.NumFieldIn.ofFrobLevel : FrobLevel ℚ Ω → NumFieldIn ℚ Ω` — an `abbrev`, so that
  `(NumFieldIn.ofFrobLevel K).L` is definitionally `K.L`; it lets every statement of the chain whose
  base fields were `FrobLevel ℚ Ω` be used with the general base fields;
* `NK.Reconstruct.NumFieldIn.ofIntermediateField`, `NK.Reconstruct.NumFieldIn.inf` (with
  `inf_L`, `inf_le_left`, `inf_le_right`; the `NumberField` instance is transferred along an
  explicit `RingEquiv` from the subfield of `↥K.L` with the same carrier),
  `NK.Reconstruct.NumFieldIn.map` and `NK.Reconstruct.numberField_map` (the image of a number
  field under a `ℚ`-automorphism of `Ω`);
* `NK.Reconstruct.levelExtendGen` — **the relative level**: for a number field `K ⊆ Ω` and a finite
  Galois level `L/ℚ` containing `K`, the field `L` viewed over `↥K.L`
  (`IntermediateField.extendScalars`), packaged as a `FrobLevel ↥K.L Ω`; with `levelExtendGen_L` and
  `levelExtendGen_mono`.

## The instance diamonds, and how they are handled

`IntermediateField.extendScalars` produces an intermediate field whose *carrier* is that of the
original level, but whose `Field`/`Algebra`/`Module` instances on the subtype are different *terms*
from those of the original, so the `Normal` field of `FrobLevel ↥K.L Ω` cannot be transported by
definitional equality, and an explicit-instance proof is blocked as well because instance search
prefers `DivisionRing.toRatAlgebra` over `IntermediateField.algebra'` for `Algebra ℚ _`.  The fix is
to *characterise* normality by stability under the Galois action
(`IntermediateField.normal_iff_forall_map_le'`), which is a statement about the *carrier* only: the
level `L.L` is stable under `Gal(Ω/↥K.L) ⊆ Gal(Ω/ℚ)` because it is stable under `Gal(Ω/ℚ)`
(`L.normal`).  See `NK.Reconstruct.normal_relLevel`.

## References

S. Shimizu, *On the Neukirch–Uchida theorem for small sets of primes*, arXiv:2009.10431, §4.
-/

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace NK.Reconstruct

open scoped Pointwise

/-- **A finite number-field level**: an intermediate field of `K'/K` together with its
`FiniteDimensional` and `NumberField` instances, carried as fields of the structure so that producer
and consumer agree on the same instance terms.  `NumFieldIn ℚ Ω` is Shimizu's `K₁`, `K₂` in §4,
without the (mathematically unnecessary) requirement that they be Galois over `ℚ`. -/
structure NumFieldIn (K : Type*) [Field K] (K' : Type*) [Field K'] [Algebra K K'] where
  /-- the field -/
  L : IntermediateField K K'
  /-- it is finite over `K` -/
  finite : FiniteDimensional K L
  /-- it is a number field -/
  numberField : NumberField ↥L

attribute [local instance] NumFieldIn.finite NumFieldIn.numberField

variable {Ω : Type*} [Field Ω] [Algebra ℚ Ω]

/-- A finite Galois level over `ℚ` is in particular a finite number-field level over `ℚ`. -/
abbrev NumFieldIn.ofFrobLevel (K : FrobLevel ℚ Ω) : NumFieldIn ℚ Ω :=
  { L := K.L, finite := K.finite, numberField := K.numberField }

@[simp] theorem NumFieldIn.ofFrobLevel_L (K : FrobLevel ℚ Ω) :
    (NumFieldIn.ofFrobLevel K).L = K.L := rfl


/-- The finite number-field level determined by an intermediate field carrying the two instances. -/
noncomputable def NumFieldIn.ofIntermediateField (K : IntermediateField ℚ Ω)
    [FiniteDimensional ℚ K] [NumberField ↥K] : NumFieldIn ℚ Ω := ⟨K, ‹FiniteDimensional ℚ K›, ‹NumberField ↥K›⟩

@[simp] theorem NumFieldIn.ofIntermediateField_L (K : IntermediateField ℚ Ω)
    [FiniteDimensional ℚ K] [NumberField ↥K] :
    (NumFieldIn.ofIntermediateField K).L = K := rfl

/-! ## The compositum and the meet -/

/-- **The meet of two finite number-field levels over `ℚ`** (Shimizu's `K₁ ∩ K₂` in Proposition
4f.5).  The `NumberField` (and hence the `FiniteDimensional`) instance is transferred from the
subfield of `↥K.L` with the same carrier. -/
noncomputable def NumFieldIn.inf (K M : NumFieldIn ℚ Ω) : NumFieldIn ℚ Ω where
  L := K.L ⊓ M.L
  finite := by
    haveI : NumberField ↥(K.L ⊓ M.L) := by
      haveI hK : NumberField ↥K.L := inferInstanceAs (NumberField ↥K.L)
      let E : Subfield ↥K.L := Subfield.comap (algebraMap ↥K.L Ω) M.L.toSubfield
      haveI hE : NumberField ↥E := NumberField.of_subfield (K := ↥K.L) E
      refine NumberField.of_ringEquiv (K := ↥E) (L := ↥(K.L ⊓ M.L)) ?_
      refine
        { toFun := fun x => ⟨(x.1 : Ω), x.1.2, x.2⟩
          invFun := fun y => ⟨⟨(y.1 : Ω), y.2.1⟩, y.2.2⟩
          left_inv := fun x => Subtype.ext (Subtype.ext rfl)
          right_inv := fun y => Subtype.ext rfl
          map_mul' := fun x y => Subtype.ext rfl
          map_add' := fun x y => Subtype.ext rfl }
    infer_instance
  numberField := by
    haveI hK : NumberField ↥K.L := inferInstanceAs (NumberField ↥K.L)
    let E : Subfield ↥K.L := Subfield.comap (algebraMap ↥K.L Ω) M.L.toSubfield
    haveI hE : NumberField ↥E := NumberField.of_subfield (K := ↥K.L) E
    refine NumberField.of_ringEquiv (K := ↥E) (L := ↥(K.L ⊓ M.L)) ?_
    refine
      { toFun := fun x => ⟨(x.1 : Ω), x.1.2, x.2⟩
        invFun := fun y => ⟨⟨(y.1 : Ω), y.2.1⟩, y.2.2⟩
        left_inv := fun x => Subtype.ext (Subtype.ext rfl)
        right_inv := fun y => Subtype.ext rfl
        map_mul' := fun x y => Subtype.ext rfl
        map_add' := fun x y => Subtype.ext rfl }

@[simp] theorem NumFieldIn.inf_L (K M : NumFieldIn ℚ Ω) : (K.inf M).L = K.L ⊓ M.L := rfl

theorem NumFieldIn.inf_le_left (K M : NumFieldIn ℚ Ω) : (K.inf M).L ≤ K.L := _root_.inf_le_left
theorem NumFieldIn.inf_le_right (K M : NumFieldIn ℚ Ω) : (K.inf M).L ≤ M.L := _root_.inf_le_right

/-! ## The relative level -/

variable [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]

/-- **The level `L` of `Ω/ℚ` viewed over the number field `K ⊆ L`** is normal over `↥K.L`: it is
stable under `Gal(Ω/↥K.L)`, because it is stable under `Gal(Ω/ℚ)` (`L.normal`, read through
`IntermediateField.normal_iff_forall_map_le'`) and `Gal(Ω/↥K.L) ⊆ Gal(Ω/ℚ)`. -/
theorem normal_relLevel (K : NumFieldIn ℚ Ω) (L : FrobLevel ℚ Ω) (h : K.L ≤ L.L) :
    Normal ↥K.L (IntermediateField.extendScalars (F := K.L) (E := L.L) h) := by
  refine (IntermediateField.normal_iff_forall_map_le' (F := ↥K.L) (L := Ω)).mpr ?_
  intro σ
  have hσℚ : ∀ x : Ω, x ∈ L.L → σ x ∈ L.L := by
    have h := (IntermediateField.normal_iff_forall_map_le' (F := ℚ) (L := Ω)).mp L.normal
      (σ.restrictScalars ℚ)
    intro x hx
    exact h ((IntermediateField.mem_map (S := L.L)).mpr ⟨x, hx, rfl⟩)
  intro y hy
  obtain ⟨z, hz, rfl⟩ :=
    (IntermediateField.mem_map (S := IntermediateField.extendScalars (F := K.L) (E := L.L) h)).mp hy
  exact hσℚ z hz

/-- **The relative level**: for a number field `K ⊆ Ω` and a finite Galois level `L/ℚ` containing
`K`, the field `L` viewed over `↥K.L`, packaged as a level over the base field `↥K.L`.  This is the
`K`-level of Shimizu's Proposition 4f.3, where `K` need not be Galois over `ℚ`. -/
noncomputable def levelExtendGen (K : NumFieldIn ℚ Ω) (L : FrobLevel ℚ Ω) (h : K.L ≤ L.L) :
    FrobLevel ↥K.L Ω where
  L := IntermediateField.extendScalars (F := K.L) (E := L.L) h
  finite := by
    haveI : NumberField ↥(IntermediateField.extendScalars (F := K.L) (E := L.L) h) :=
      inferInstanceAs (NumberField ↥L.L)
    infer_instance
  normal := normal_relLevel K L h
  numberField := inferInstanceAs (NumberField ↥L.L)

@[simp] theorem levelExtendGen_L (K : NumFieldIn ℚ Ω) (L : FrobLevel ℚ Ω) (h : K.L ≤ L.L) :
    (levelExtendGen K L h).L = IntermediateField.extendScalars (F := K.L) (E := L.L) h := rfl

/-- The order relation transports to the relative levels. -/
theorem levelExtendGen_mono (K : NumFieldIn ℚ Ω) (A B : FrobLevel ℚ Ω) (hA : K.L ≤ A.L)
    (hB : K.L ≤ B.L) (hAB : A.L ≤ B.L) :
    (levelExtendGen K A hA).L ≤ (levelExtendGen K B hB).L := hAB

/-! ## Transport of number fields along automorphisms of `Ω` -/

/-- **The image of a number field under a `ℚ`-automorphism of `Ω` is a number field.** -/
theorem numberField_map (K : NumFieldIn ℚ Ω) (θ : Ω ≃ₐ[ℚ] Ω) :
    NumberField ↥(K.L.map θ.symm.toAlgHom) := by
  haveI hK : NumberField ↥K.L := inferInstanceAs (NumberField ↥K.L)
  refine NumberField.of_ringEquiv (K := ↥K.L) (L := ↥(K.L.map θ.symm.toAlgHom)) ?_
  refine
    { toFun := fun x => ⟨θ.symm x.1, ⟨x.1, x.2, rfl⟩⟩
      invFun := fun y => ⟨θ y.1, by
        obtain ⟨z, hz, hzy⟩ := (IntermediateField.mem_map (S := K.L) (f := θ.symm.toAlgHom)).mp y.2
        have hy : θ y.1 = z := by rw [← hzy]; simp
        rw [hy]; exact hz⟩
      left_inv := fun x => Subtype.ext (by simp)
      right_inv := fun y => Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp)
      map_add' := fun x y => Subtype.ext (by simp) }

/-- The image of a finite number-field level under a `ℚ`-automorphism of `Ω`. -/
noncomputable def NumFieldIn.map (K : NumFieldIn ℚ Ω) (θ : Ω ≃ₐ[ℚ] Ω) : NumFieldIn ℚ Ω where
  L := K.L.map θ.symm.toAlgHom
  finite := by
    haveI : FiniteDimensional ℚ ↥K.L := K.finite
    exact IntermediateField.finiteDimensional_map θ.symm.toAlgHom
  numberField := numberField_map K θ

@[simp] theorem NumFieldIn.map_L (K : NumFieldIn ℚ Ω) (θ : Ω ≃ₐ[ℚ] Ω) :
    (K.map θ).L = K.L.map θ.symm.toAlgHom := rfl

end NK.Reconstruct
