import Mathlib

set_option linter.style.haveILetI false

namespace Work.BG

/-! ## Preparatory group theory

We prove the general fact that for any group `M` with exactly four elements, `MulAut M` embeds
faithfully into the permutations of the three nonidentity elements of `M`; consequently
`Nat.card (MulAut M) ∣ 6`.  This is the numerical input for `nOrbIndexDvdSix`.
-/

/-- The action of `MulAut ↥V` on the type of nonidentity elements of `V`: an automorphism `e`
sends the nonidentity element `w` to the nonidentity element `e w`.

This is the faithful permutation representation used in `nOrbIndexDvdSix`. -/
def mulAutNonidHom {G : Type} [Group G] (V : Subgroup G) :
    MulAut ↥V →* Equiv.Perm {v : ↥V // v ≠ 1} where
  toFun e :=
    { toFun := fun w => ⟨e w.1, fun h => w.2 ((MulEquiv.map_eq_one_iff e).mp h)⟩
      invFun := fun w => ⟨e.symm w.1, fun h => w.2 ((MulEquiv.map_eq_one_iff e.symm).mp h)⟩
      left_inv := fun w => by ext; simp
      right_inv := fun w => by ext; simp }
  map_one' := by ext w; rfl
  map_mul' := fun a b => by ext w; rfl

/-- `mulAutNonidHom` is faithful: an automorphism of `V` fixing every nonidentity element fixes
`1` as well, hence is the identity. -/
theorem mulAutNonidHom_ker {G : Type} [Group G] (V : Subgroup G) :
    (mulAutNonidHom V).ker = ⊥ := by
  ext e
  simp only [MonoidHom.mem_ker, Subgroup.mem_bot]
  constructor
  · intro h
    ext v
    by_cases hv : v = 1
    · subst hv; simp
    · have h1 := congrArg (fun (p : Equiv.Perm {v : ↥V // v ≠ 1}) =>
        ((p ⟨v, hv⟩ : {v : ↥V // v ≠ 1}) : ↥V)) h
      simpa [mulAutNonidHom] using h1
  · intro h; subst h; simp

/-- If `V` is a subgroup with exactly four elements, then `Nat.card (MulAut ↥V) ∣ 6`.

`MulAut ↥V` acts faithfully (`mulAutNonidHom_ker`) on the three-element type
`Ω := {v : ↥V // v ≠ 1}`, so `Nat.card (MulAut ↥V)` divides `Nat.card (Equiv.Perm Ω)`, and the
latter is `(Nat.card Ω)! = 3! = 6` by `Nat.card_perm` with `Nat.card Ω = 3`. -/
theorem cardMulAutDvdSix {G : Type} [Group G] [Finite G] (V : Subgroup G)
    (hV : Nat.card ↥V = 4) : Nat.card (MulAut ↥V) ∣ 6 := by
  haveI : Fintype ↥V := Fintype.ofFinite ↥V
  have hΩ : Nat.card {v : ↥V // v ≠ 1} = 3 := by
    haveI : Fintype {v : ↥V // v ≠ 1} := Fintype.ofFinite _
    haveI : Fintype {v : ↥V // v = 1} := Fintype.ofFinite _
    have hV' : Fintype.card ↥V = 4 := by rw [← Nat.card_eq_fintype_card]; exact hV
    have hone : Fintype.card {v : ↥V // v = 1} = 1 := by
      haveI : Unique {v : ↥V // v = 1} :=
        { default := ⟨1, rfl⟩, uniq := fun a => Subtype.ext a.2 }
      exact Fintype.card_unique
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl (fun v : ↥V => v = 1),
      hone, hV']
  have hker : (mulAutNonidHom V).ker = ⊥ := mulAutNonidHom_ker V
  have h1 : Nat.card (MulAut ↥V) = Nat.card ↥((mulAutNonidHom V).range) := by
    rw [← Subgroup.index_bot, ← hker, Subgroup.index_ker]
  have h2 : Nat.card ↥((mulAutNonidHom V).range) ∣ Nat.card (Equiv.Perm {v : ↥V // v ≠ 1}) :=
    Subgroup.card_subgroup_dvd_card _
  have h3 : Nat.card (Equiv.Perm {v : ↥V // v ≠ 1}) = 6 := by
    rw [Nat.card_perm, hΩ]
    norm_num
  rw [h1]
  exact dvd_trans h2 (by rw [h3])

/-- Group-theoretic input for `Work.BG.nOrbCosets`: if `V ≤ G` is a subgroup with exactly four
elements, then the index `|N_G(V) : C_G(V)|` divides `6`.

Route: the conjugation map `φ := V.normalizerMonoidHom : N_G(V) →* MulAut V` has kernel
`C_G(V)` (`Subgroup.normalizerMonoidHom_ker`), so `Nat.card (N_G(V) ⧸ C_G(V))` equals
`Nat.card φ.range` (`Subgroup.index_ker`), which divides `Nat.card (MulAut V)`
(`Subgroup.card_subgroup_dvd_card`).  `MulAut V` acts faithfully on the three-element type
`Ω := {v : ↥V // v ≠ 1}` (`hV` gives `Nat.card Ω = 3`, e.g. via `Fintype.card_subtype_compl`;
the action is faithful because an automorphism of `V` fixing every `v ≠ 1` also fixes `1`), so
`Nat.card (MulAut V) ∣ Nat.card (Equiv.Perm Ω) = (Nat.card Ω)! = 6` (`Nat.card_perm`).
Chaining the divisibilities gives the claim.  Note `Subgroup.relIndex H K` is by definition
`(H.subgroupOf K).index`. -/
theorem nOrbIndexDvdSix {G : Type} [Group G] [Finite G] (V : Subgroup G)
    (hV : Nat.card ↥V = 4) :
    (Subgroup.centralizer (V : Set G)).relIndex (Subgroup.normalizer (V : Set G)) ∣ 6 := by
  rw [Subgroup.relIndex, ← Subgroup.normalizerMonoidHom_ker V, Subgroup.index_ker]
  exact dvd_trans (Subgroup.card_subgroup_dvd_card _) (cardMulAutDvdSix V hV)

end Work.BG
