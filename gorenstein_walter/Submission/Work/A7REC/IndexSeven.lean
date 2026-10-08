/-
Area A7REC: the "index `7` ⇒ `A₇`" step, adapted to Lean v4.35.

`Submission/Work/A7/IndexSeven.lean` (the old area `A7`) does **not** compile on this toolchain
(`Subgroup.normal` is no longer a projection, `congrArg (⇑)` needs an explicit function, and
`injective_iff_surjective_of_equiv` moved to the `Finite` namespace).  The mathematics is
unchanged; the file below is the corrected copy, in this area's namespace.

The mathematical content is standard:

* the action on the `7` cosets of `H` is faithful (its kernel is normal and contained in `H`),
  so `G` embeds in `Sym(7)`;
* the image lies in `A₇`, since otherwise `sign ∘ φ` would be a surjection of `G` onto `ℤˣ`
  (so `2520 ≤ 2`);
* `|G| = 2520 = |A₇|` forces the image to be everything.
-/
import Submission.Work.A7REC.Defs

open scoped MatrixGroups

namespace Work.A7REC

open Equiv Equiv.Perm

/-- A finite simple group which acts faithfully on `7` points and has `2520` elements is
isomorphic to `A₇`. -/
theorem exists_mulEquiv_alternating_of_injective_perm (G : Type*) [Group G] [Finite G]
    [IsSimpleGroup G] (hcard : Nat.card G = 2520) (φ : G →* Equiv.Perm (Fin 7))
    (hφ : Function.Injective φ) : Nonempty (G ≃* alternatingGroup (Fin 7)) := by
  haveI : Fintype G := Fintype.ofFinite G
  -- `sign ∘ φ` is trivial: its kernel is normal, and `G` is simple of order `2520 > 2`.
  have hsign : ∀ g : G, Equiv.Perm.sign (φ g) = 1 := by
    have hker : ((Equiv.Perm.sign : Equiv.Perm (Fin 7) →* ℤˣ).comp φ).ker = ⊤ := by
      rcases Subgroup.Normal.eq_bot_or_eq_top
        ((Equiv.Perm.sign : Equiv.Perm (Fin 7) →* ℤˣ).comp φ).ker with h | h
      · exfalso
        have hinj : Function.Injective
            ((Equiv.Perm.sign : Equiv.Perm (Fin 7) →* ℤˣ).comp φ) := by
          intro a b hab
          have hmem : a * b⁻¹ ∈
              ((Equiv.Perm.sign : Equiv.Perm (Fin 7) →* ℤˣ).comp φ).ker := by
            rw [MonoidHom.mem_ker]
            simp only [map_mul, map_inv, hab, mul_inv_cancel]
          rw [h, Subgroup.mem_bot] at hmem
          exact mul_inv_eq_one.mp hmem
        have hle : Fintype.card G ≤ Fintype.card ℤˣ :=
          Fintype.card_le_of_injective _ hinj
        rw [Fintype.card_units_int] at hle
        have hG : Fintype.card G = 2520 := by
          rw [← Nat.card_eq_fintype_card]; exact hcard
        omega
      · exact h
    intro g
    have hmem : g ∈ ((Equiv.Perm.sign : Equiv.Perm (Fin 7) →* ℤˣ).comp φ).ker :=
      hker ▸ Subgroup.mem_top g
    simpa using hmem
  -- hence the image lies in `A₇`
  let φ' : G →* alternatingGroup (Fin 7) :=
    φ.codRestrict (alternatingGroup (Fin 7)) fun g => by
      rw [Equiv.Perm.mem_alternatingGroup]; exact hsign g
  have hφ' : Function.Injective φ' := by
    intro a b hab
    exact hφ (Subtype.ext_iff.mp hab)
  refine ⟨MulEquiv.ofBijective φ' ⟨hφ', ?_⟩⟩
  -- cardinalities agree, so injectivity implies surjectivity
  have hcard' : Nat.card G = Nat.card (alternatingGroup (Fin 7)) := by
    rw [hcard, Work.A7.card_alternatingGroup_seven]
  haveI : Fintype (alternatingGroup (Fin 7)) := Fintype.ofFinite _
  have hc : Fintype.card G = Fintype.card (alternatingGroup (Fin 7)) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact hcard'
  exact (Finite.injective_iff_surjective_of_equiv (Fintype.equivOfCardEq hc)).mp hφ'

/-- **A simple group of order `2520` with a subgroup of index `7` is isomorphic to `A₇`.**

This is the recognition statement for the exceptional case of the Gorenstein--Walter theorem:
once the `A₇` case has been narrowed down to `|G| = 2520` together with an index-`7` subgroup,
the coset action identifies `G` with `A₇`. -/
theorem mulEquiv_A7_of_index_seven (G : Type*) [Group G] [Finite G] [IsSimpleGroup G]
    (hcard : Nat.card G = 2520) (H : Subgroup G) (hH : H.index = 7) :
    Nonempty (G ≃* alternatingGroup (Fin 7)) := by
  have hHne : H ≠ ⊤ := by
    intro h
    rw [h, Subgroup.index_top] at hH
    omega
  -- the kernel of the action on the cosets of `H` is contained in `H`
  have hker_le : (MulAction.toPermHom G (G ⧸ H)).ker ≤ H := by
    rw [← Subgroup.normalCore_eq_ker]
    exact Subgroup.normalCore_le H
  haveI : ((MulAction.toPermHom G (G ⧸ H)).ker).Normal :=
    MonoidHom.normal_ker _
  -- `G` is simple, so this kernel is trivial
  have hker : (MulAction.toPermHom G (G ⧸ H)).ker = ⊥ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top (MulAction.toPermHom G (G ⧸ H)).ker with h | h
    · exact h
    · exact absurd (le_antisymm (h ▸ hker_le) le_top) (fun ht => hHne ht.symm)
  have hinj : Function.Injective (MulAction.toPermHom G (G ⧸ H)) :=
    (MonoidHom.ker_eq_bot_iff _).mp hker
  -- identify the seven cosets with `Fin 7`
  haveI : Finite (G ⧸ H) := Quotient.finite _
  have hcardq : Nat.card (G ⧸ H) = 7 := hH
  cases nonempty_fintype (G ⧸ H)
  let e : G ⧸ H ≃ Fin 7 :=
    Fintype.equivFinOfCardEq (by rw [← Nat.card_eq_fintype_card]; exact hcardq)
  let ψ : G →* Equiv.Perm (Fin 7) :=
    (Equiv.permCongrHom e).toMonoidHom.comp (MulAction.toPermHom G (G ⧸ H))
  exact exists_mulEquiv_alternating_of_injective_perm G hcard ψ
    fun a b hab => hinj ((Equiv.permCongrHom e).injective hab)

end Work.A7REC
