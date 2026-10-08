import Mathlib
import Submission.Work.A7.Defs

namespace Work.AUTA7.A7

open Equiv Equiv.Perm

/-!
# A Sylow 2-subgroup of `A₇` is dihedral of order `8`

`|A₇| = 2520 = 8 · 315`, so the Sylow `2`-subgroups of `A₇` have order `8`, and they are
dihedral.  Concretely, with

* `R = (0 1 2 3)(4 5)`  (an even permutation of order `4`),
* `S = (0 2)(4 5)`      (an even involution),

one has `S * R * S = R⁻¹` and `S ∉ ⟨R⟩`, so `⟨R, S⟩` has order `4 · 2 = 8` and is a semidirect
product of `⟨R⟩ ≅ ℤ/4` by `⟨S⟩ ≅ ℤ/2` acting by inversion, i.e. is isomorphic to the dihedral
group of order `8`.

Rather than compute the subgroup `⟨R, S⟩` by hand we exhibit an injective homomorphism
`DihedralGroup 4 →* A₇` (sending `r i ↦ R ^ i` and `sr i ↦ S * R ^ i`) and take its range.
All the finite verifications are done by `decide`, after splitting the `ZMod 4`-indices with
`fin_cases`.
-/

/-- `R = (0 1 2 3)(4 5)`: the product of the `4`-cycle `(0 1 2 3)` and the transposition
`(4 5)`, an even permutation of order `4`. -/
def sylowR : Perm (Fin 7) :=
  Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 4 5

/-- `S = (0 2)(4 5)`: a double transposition, i.e. an even involution. -/
def sylowS : Perm (Fin 7) :=
  Equiv.swap 0 2 * Equiv.swap 4 5

@[simp]
theorem sign_sylowR : Equiv.Perm.sign sylowR = 1 := by decide

@[simp]
theorem sign_sylowS : Equiv.Perm.sign sylowS = 1 := by decide

/-- `R = (0 1 2 3)(4 5)` as an element of the alternating group `A₇`. -/
def a7R : alternatingGroup (Fin 7) :=
  ⟨sylowR, by rw [Equiv.Perm.mem_alternatingGroup, sign_sylowR]⟩

/-- `S = (0 2)(4 5)` as an element of the alternating group `A₇`. -/
def a7S : alternatingGroup (Fin 7) :=
  ⟨sylowS, by rw [Equiv.Perm.mem_alternatingGroup, sign_sylowS]⟩

@[simp]
theorem coe_a7R : ((a7R : alternatingGroup (Fin 7)) : Perm (Fin 7)) = sylowR := rfl

@[simp]
theorem coe_a7S : ((a7S : alternatingGroup (Fin 7)) : Perm (Fin 7)) = sylowS := rfl

/-- The underlying function of the identification of `DihedralGroup 4` with `⟨R, S⟩ ≤ A₇`:
`r i ↦ R ^ i`, `sr i ↦ S * R ^ i`, for the cyclic index `i : ZMod 4`. -/
def dihToPermFun : DihedralGroup 4 → Perm (Fin 7)
  | .r i => sylowR ^ ((i.val : ℤ))
  | .sr i => sylowS * sylowR ^ ((i.val : ℤ))

/-- `dihToPermFun` is multiplicative.  Both the source (`ZMod 4` indices) and the target (`S₇`) are
finite and the operations are computable, so we split the four constructor combinations and the
four residues of each index and let `decide` run. -/
theorem dihToPermFun_mul (a b : DihedralGroup 4) :
    dihToPermFun (a * b) = dihToPermFun a * dihToPermFun b := by
  rcases a with i | i <;> rcases b with j | j <;>
    fin_cases i <;> fin_cases j <;> decide

/-- The homomorphism `DihedralGroup 4 →* S₇` given by `r i ↦ R ^ i`, `sr i ↦ S * R ^ i`. -/
def dihToPerm : DihedralGroup 4 →* Perm (Fin 7) :=
  MonoidHom.mk' dihToPermFun dihToPermFun_mul

@[simp]
theorem dihToPerm_apply (g : DihedralGroup 4) : dihToPerm g = dihToPermFun g :=
  rfl

/-- `dihToPerm` is injective.  Again this is a finite computation: `ψ (r i) = R ^ i` is never `1`
for `i ≠ 0`, and `ψ (sr i) = S * R ^ i` is never `1` because `S ∉ ⟨R⟩`. -/
theorem dihToPerm_injective : Function.Injective dihToPerm := by
  change Function.Injective dihToPermFun
  rintro (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;> decide

/-- Every value of `dihToPerm` is an even permutation, so `dihToPerm` lands in `A₇`. -/
theorem dihToPerm_mem (g : DihedralGroup 4) : dihToPerm g ∈ alternatingGroup (Fin 7) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  change Equiv.Perm.sign (dihToPermFun g) = 1
  rcases g with i | i <;> fin_cases i <;> decide

/-- The homomorphism `DihedralGroup 4 →* A₇` given by `r i ↦ R ^ i`, `sr i ↦ S * R ^ i`. -/
def dihToA7 : DihedralGroup 4 →* alternatingGroup (Fin 7) :=
  dihToPerm.codRestrict (alternatingGroup (Fin 7)) dihToPerm_mem

@[simp]
theorem coe_dihToA7 (g : DihedralGroup 4) :
    ((dihToA7 g : alternatingGroup (Fin 7)) : Perm (Fin 7)) = dihToPerm g := rfl

theorem dihToA7_injective : Function.Injective dihToA7 := by
  intro a b hab
  apply dihToPerm_injective
  simpa using congrArg (fun x : alternatingGroup (Fin 7) => (x : Perm (Fin 7))) hab

/- Hint: exhibit `r = (0 1 2 3)(4 5)` and `s = (0 2)(4 5)` in `Equiv.Perm (Fin 7)`; both are even,
`r` has order 4, `s` has order 2 with `s * r * s = r⁻¹` and `s ∉ Subgroup.zpowers r`. Then
`Subgroup.closure {r, s}` is a candidate `K`. -/
theorem SylowTwoSubgroup :
    ∃ K : Subgroup (alternatingGroup (Fin 7)), Nonempty (K ≃* DihedralGroup 4) :=
  ⟨dihToA7.range, ⟨(MonoidHom.ofInjective dihToA7_injective).symm⟩⟩

end Work.AUTA7.A7
