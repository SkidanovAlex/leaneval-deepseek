import Mathlib
import Submission.Work.Tower.Defs

/-!
# Unramified extensions: the basic API

This file builds the basic API for `Work.Tower.IsUnramifiedExtension` (defined in
`Submission/Work/Tower/Defs.lean` as "every prime of `𝓞 L` lying over a prime `𝔭` of `𝓞 F`
has `Ideal.ramificationIdxIn 𝔭 (𝓞 L) = 1`").

`Ideal.ramificationIdxIn` is defined by *choosing* a prime over `𝔭`, so for a non-Galois
extension the given predicate only records the ramification index of one prime over each `𝔭`.
The mathematically robust predicate is that **every** prime of `𝓞 L` has ramification index `1`
over `𝓞 F`; we call it `IsUnramifiedExtensionForallPrimes`.  For Galois extensions (the only case
in the class-field tower construction) the two agree, and we prove this:

* `isUnramifiedExtension_iff_forallPrimes`;
* the equivalent formulations in terms of `Algebra.IsUnramifiedIn` and `Algebra.IsUnramifiedAt`
  (`IsUnramifiedExtensionForallPrimes_iff_isUnramifiedIn`,
  `IsUnramifiedExtensionForallPrimes_iff_forall_isUnramifiedAt`);
* the local-in-the-tower property `IsUnramifiedExtensionForallPrimes.tower` / `.of_tower`.

## Main definitions

* `Work.Tower.IsUnramifiedExtensionForallPrimes`.
-/

open NumberField
open scoped Classical nonZeroDivisors

namespace Work
namespace Tower

/-! ### The strong predicate -/

/-- `L/F` is unramified at every prime (strong form): every prime ideal `𝔓` of `𝓞 L` has
ramification index `1` over `𝓞 F`.  This is equivalent to `IsUnramifiedExtension F L` when `L/F`
is Galois, and is the form in which the tower and compositum properties are cleanest. -/
def IsUnramifiedExtensionForallPrimes (F L : Type*) [Field F] [Field L] [Algebra F L] : Prop :=
  ∀ (𝔓 : Ideal (𝓞 L)), 𝔓.IsPrime → 𝔓.ramificationIdx (𝓞 F) = 1

variable {F L : Type*}

section MinAssumptions

variable [Field F] [Field L] [Algebra F L]

/-- The strong form implies the weak (given) form, with no further hypotheses: `ramificationIdxIn`
is by definition the ramification index of *some* prime over `𝔭`. -/
theorem IsUnramifiedExtension.of_forallPrimes
    (h : IsUnramifiedExtensionForallPrimes F L) : IsUnramifiedExtension F L := by
  intro 𝔓 h𝔓 𝔭 hlie
  have hex : ∃ P : Ideal (𝓞 L), P.IsPrime ∧ P.LiesOver 𝔭 := ⟨𝔓, h𝔓, hlie⟩
  simp only [Ideal.ramificationIdxIn, dite_eq_left hex]
  exact h _ hex.choose_spec.1

end MinAssumptions

section NumberField

variable [Field F] [Field L] [NumberField F] [NumberField L] [Algebra F L]
    [FiniteDimensional F L]

/-- For a **Galois** extension, the weak (given) predicate and the strong predicate agree. -/
theorem IsUnramifiedExtension.forallPrimes [IsGalois F L]
    (h : IsUnramifiedExtension F L) : IsUnramifiedExtensionForallPrimes F L := by
  intro 𝔓 h𝔓
  have h1 : Ideal.ramificationIdxIn (𝔓.under (𝓞 F)) (𝓞 L) = 1 :=
    h 𝔓 h𝔓 (𝔓.under (𝓞 F)) (Ideal.over_under 𝔓)
  rwa [Ideal.ramificationIdxIn_eq_ramificationIdx (𝔓.under (𝓞 F)) 𝔓 Gal(L/F)] at h1

/-- **Equivalent formulations of unramifiedness (Galois case).** -/
theorem isUnramifiedExtension_iff_forallPrimes [IsGalois F L] :
    IsUnramifiedExtension F L ↔ IsUnramifiedExtensionForallPrimes F L :=
  ⟨IsUnramifiedExtension.forallPrimes, IsUnramifiedExtension.of_forallPrimes⟩

/-- The strong predicate, phrased with `Algebra.IsUnramifiedAt`. -/
theorem IsUnramifiedExtensionForallPrimes_iff_forall_isUnramifiedAt :
    IsUnramifiedExtensionForallPrimes F L ↔
      ∀ (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime], Algebra.IsUnramifiedAt (𝓞 F) 𝔓 := by
  constructor
  · intro h 𝔓 h𝔓
    exact (Ideal.ramificationIdx_eq_one_iff (R := 𝓞 F) (q := 𝔓)).mp (h 𝔓 h𝔓)
  · intro h 𝔓 h𝔓
    exact (Ideal.ramificationIdx_eq_one_iff (R := 𝓞 F) (q := 𝔓)).mpr (h 𝔓)

/-- The strong predicate, phrased with `Algebra.IsUnramifiedIn` (Mathlib's predicate that every
prime over a given prime of the base is unramified). -/
theorem IsUnramifiedExtensionForallPrimes_iff_isUnramifiedIn :
    IsUnramifiedExtensionForallPrimes F L ↔
      ∀ (𝔭 : Ideal (𝓞 F)), 𝔭.IsPrime → Algebra.IsUnramifiedIn (𝓞 L) 𝔭 := by
  constructor
  · intro h 𝔭 h𝔭
    rw [Algebra.isUnramifiedIn_iff_forall_ramificationIdx_eq_one]
    intro 𝔓 h𝔓 _
    exact h 𝔓 h𝔓
  · intro h 𝔓 h𝔓
    have h𝔭 : (𝔓.under (𝓞 F)).IsPrime := inferInstance
    have hmain : Algebra.IsUnramifiedIn (𝓞 L) (𝔓.under (𝓞 F)) := h _ h𝔭
    rw [Algebra.isUnramifiedIn_iff_forall_ramificationIdx_eq_one] at hmain
    exact hmain 𝔓 (Ideal.over_under 𝔓)

/-- `IsUnramifiedExtension F L`, phrased with `Algebra.IsUnramifiedIn` (Galois case). -/
theorem isUnramifiedExtension_iff_isUnramifiedIn [IsGalois F L] :
    IsUnramifiedExtension F L ↔
      ∀ (𝔭 : Ideal (𝓞 F)), 𝔭.IsPrime → Algebra.IsUnramifiedIn (𝓞 L) 𝔭 :=
  isUnramifiedExtension_iff_forallPrimes.trans
    IsUnramifiedExtensionForallPrimes_iff_isUnramifiedIn

end NumberField

/-! ### The tower property -/

section Tower

variable [Field F] [Field L] [NumberField F] [NumberField L] [Algebra F L]
    [FiniteDimensional F L]

/-- **Unramifiedness is local in the tower (forward direction).**  If `L/F` is unramified at
every prime and `F ⊆ E ⊆ L`, then `E/F` and `L/E` are unramified at every prime. -/
theorem IsUnramifiedExtensionForallPrimes.tower {E : IntermediateField F L}
    (h : IsUnramifiedExtensionForallPrimes F L) :
    IsUnramifiedExtensionForallPrimes F E ∧ IsUnramifiedExtensionForallPrimes E L := by
  constructor
  · intro 𝔓 h𝔓
    haveI := h𝔓
    obtain ⟨𝔔⟩ := (inferInstance : Nonempty (𝔓.primesOver (𝓞 L)))
    have h1 : 𝔔.1.ramificationIdx (𝓞 F) = 1 := h 𝔔.1 𝔔.2.1
    rw [Ideal.ramificationIdx_tower (R := 𝓞 F) (S := 𝓞 E) (T := 𝓞 L)
      (q := 𝔓) (r := 𝔔.1)] at h1
    exact Nat.dvd_one.mp ⟨_, h1.symm⟩
  · intro 𝔔 h𝔔
    have h1 : 𝔔.ramificationIdx (𝓞 F) = 1 := h 𝔔 h𝔔
    rw [Ideal.ramificationIdx_tower (R := 𝓞 F) (S := 𝓞 E) (T := 𝓞 L)
      (q := 𝔔.under (𝓞 E)) (r := 𝔔)] at h1
    exact Nat.dvd_one.mp ⟨_, by rw [mul_comm]; exact h1.symm⟩

/-- **Unramifiedness is local in the tower (converse).**  If `E/F` and `L/E` are unramified at
every prime and `F ⊆ E ⊆ L`, then so is `L/F`. -/
theorem IsUnramifiedExtensionForallPrimes.of_tower {E : IntermediateField F L}
    (hE : IsUnramifiedExtensionForallPrimes F E)
    (hL : IsUnramifiedExtensionForallPrimes E L) :
    IsUnramifiedExtensionForallPrimes F L := by
  intro 𝔔 h𝔔
  haveI := h𝔔
  have h1 : 𝔔.ramificationIdx (𝓞 F) =
      (𝔔.under (𝓞 E)).ramificationIdx (𝓞 F) * 𝔔.ramificationIdx (𝓞 E) :=
    Ideal.ramificationIdx_tower (R := 𝓞 F) (S := 𝓞 E) (T := 𝓞 L)
      (q := 𝔔.under (𝓞 E)) (r := 𝔔)
  rw [h1, hE _ (inferInstance : (𝔔.under (𝓞 E)).IsPrime), hL 𝔔 h𝔔, one_mul]

/-- The tower property for the given predicate, in the Galois case. -/
theorem IsUnramifiedExtension.tower [IsGalois F L] {E : IntermediateField F L}
    (h : IsUnramifiedExtension F L) :
    IsUnramifiedExtension F E ∧ IsUnramifiedExtension E L := by
  obtain ⟨h1, h2⟩ := h.forallPrimes.tower (E := E)
  exact ⟨IsUnramifiedExtension.of_forallPrimes h1,
    IsUnramifiedExtension.of_forallPrimes h2⟩

/-- The converse tower property for the given predicate, in the Galois case. -/
theorem IsUnramifiedExtension.of_tower {E : IntermediateField F L} [IsGalois F L] [IsGalois F E]
    (hE : IsUnramifiedExtension F E) (hL : IsUnramifiedExtension E L) :
    IsUnramifiedExtension F L :=
  IsUnramifiedExtension.of_forallPrimes
    (IsUnramifiedExtensionForallPrimes.of_tower hE.forallPrimes hL.forallPrimes)

/-- **Unramifiedness is local in the tower**, for the given predicate: for `L/F` Galois and
`F ⊆ E ⊆ L`, `L/F` is unramified iff both steps are. -/
theorem isUnramifiedExtension_iff_tower {E : IntermediateField F L} [IsGalois F L] [IsGalois F E] :
    IsUnramifiedExtension F L ↔ IsUnramifiedExtension F E ∧ IsUnramifiedExtension E L :=
  ⟨fun h ↦ h.tower, fun h ↦ h.1.of_tower h.2⟩

end Tower

end Tower
end Work
