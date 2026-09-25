import Mathlib
import Submission.Work.Tower.CyclotomicBase.Defs
import Submission.Work.Tower.CyclotomicBase.Basic
import Submission.Work.Tower.CyclotomicBase.exists_mulEquiv_Mfield_gal

/-!
# The extension `M/F` of the tower is abelian Galois

The Galois group `Gal(M/ℚ)` of the field `M = Mfield` cut out by the `ℓ` cubic characters is
isomorphic to `(ℤ/3)^ℓ` (`exists_mulEquiv_Mfield_gal`), hence commutative.  Therefore `M/ℚ` is
abelian Galois, and so is the extension `M/F` over any intermediate field, in particular over
`F = FMfield`.

## Main results

* `Work.Tower.CyclotomicBase.isMulCommutative_gal_Mfield`: `Gal(M/ℚ)` is commutative.
* `Work.Tower.CyclotomicBase.isAbelianGalois_Mfield`: `M/ℚ` is abelian Galois.
* `Work.Tower.CyclotomicBase.isAbelianGalois_FMfield_Mfield`: `M/F` is abelian Galois.
-/

set_option linter.style.haveILetI false
set_option autoImplicit false

open scoped Classical

namespace Work.Tower.CyclotomicBase

/-- `Gal(M/ℚ)` is commutative: it is isomorphic to the commutative group `(ℤ/3)^ℓ`. -/
theorem isMulCommutative_gal_Mfield {ℓ : ℕ} (r : Fin ℓ → ℕ) (hr : ∀ i, Nat.Prime (r i))
    (hr3 : ∀ i, r i % 3 = 1) (hrinj : Function.Injective r) [NeZero (D r)] :
    IsMulCommutative Gal(↥(Mfield r hr hr3)/ℚ) := by
  obtain ⟨e⟩ := exists_mulEquiv_Mfield_gal r hr hr3 hrinj
  exact IsMulCommutative.of_comm fun a b =>
    e.injective (by rw [map_mul, map_mul]; exact mul_comm _ _)

/-- `M/ℚ` is an abelian Galois extension. -/
theorem isAbelianGalois_Mfield {ℓ : ℕ} (r : Fin ℓ → ℕ) (hr : ∀ i, Nat.Prime (r i))
    (hr3 : ∀ i, r i % 3 = 1) (hrinj : Function.Injective r) [NeZero (D r)] :
    IsAbelianGalois ℚ ↥(Mfield r hr hr3) := by
  haveI := isGalois_Mfield r hr hr3
  haveI := isMulCommutative_gal_Mfield r hr hr3 hrinj
  exact { }

theorem isAbelianGalois_FMfield_Mfield {ℓ : ℕ} (r : Fin ℓ → ℕ) (hr : ∀ i, Nat.Prime (r i))
    (hr3 : ∀ i, r i % 3 = 1) (hrinj : Function.Injective r) [NeZero (D r)] :
    IsAbelianGalois ↥(FMfield r hr hr3) ↥(Mfield r hr hr3) := by
  haveI := isAbelianGalois_Mfield r hr hr3 hrinj
  infer_instance

end Work.Tower.CyclotomicBase
