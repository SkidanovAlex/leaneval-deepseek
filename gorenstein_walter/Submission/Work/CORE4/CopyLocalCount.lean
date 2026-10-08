import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.ConjSubOrbitNcard

/-!
# `Work.CORE4.CopyLocalCount`

The counting step of Bender's "copy" argument (`CopyLocalProp`, design pass 27): if `X ≤ D` is a
subgroup of order `p` (`p` an odd prime), every subgroup of `D` of order `p` is a `K`-conjugate of
`X` for some subgroup `K` of **odd** order, and `X` normalises no other such subgroup (`hfix`),
then the number of subgroups of `D` of order `p` is `≡ 1 (mod 2p)`.

Two inputs:

* the `p`-group `X` acts on the set `S` of subgroups of `D` of order `p`; the fixed points are
  (by `hfix`) exactly `{X}`, so `|S| ≡ 1 [MOD p]` (`IsPGroup.card_modEq_card_fixedPoints`);
* `S = X^K`, so `|S| = [K : K ⊓ N_G(X)]` divides the odd number `|K|`, whence `|S|` is odd.

`2p = 2 · p` with `2` and `p` coprime then gives `|S| % (2p) = 1`.
-/

namespace Work.CORE4

open Subgroup

set_option linter.style.haveILetI false

/-! ## 0. The `p`-group fixed-point congruence for an invariant subset -/

/-- For a set with finitely many elements, `Set.ncard` is the `Nat.card` of the subtype. -/
lemma ncard_eq_natCard {α : Type*} (s : Set α) [Fintype ↥s] : s.ncard = Nat.card ↥s := by
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_card, Nat.card_eq_fintype_card]

/-- **The `p`-group fixed-point congruence.**  If a `p`-group `M` acts on a finite type `α` and
`s ⊆ α` is `M`-invariant, then the number of elements of `s` is congruent modulo `p` to the number
of elements of `s` that are fixed by the whole action of `M`. -/
lemma ncard_modEq_ncard_fixedPoints {M α : Type*} [Group M] [MulAction M α] {p : ℕ}
    [Fact p.Prime] (hM : IsPGroup p M) [Finite α] (s : Set α)
    (hs : ∀ (m : M) {x : α}, x ∈ s → m • x ∈ s) :
    s.ncard ≡ {x : α | x ∈ s ∧ ∀ m : M, m • x = x}.ncard [MOD p] := by
  let sa : SubMulAction M α := SubMulAction.mk s (fun m x hx => hs m hx)
  haveI : Finite ↥sa := Subtype.finite
  haveI : Fintype ↥s := Fintype.ofFinite ↥s
  have h1 : Nat.card ↥sa = s.ncard := (ncard_eq_natCard s).symm
  have h2 : Nat.card ↑(MulAction.fixedPoints M ↥sa)
      = {x : α | x ∈ s ∧ ∀ m : M, m • x = x}.ncard := by
    haveI : Fintype ↑(MulAction.fixedPoints M ↥sa) := Fintype.ofFinite _
    haveI : Fintype ↑{x : α | x ∈ s ∧ ∀ m : M, m • x = x} := Fintype.ofFinite _
    rw [← ncard_eq_natCard (MulAction.fixedPoints M ↥sa)]
    refine Set.ncard_congr (fun y _ => (y : α)) ?_ ?_ ?_
    · intro y hy
      refine ⟨y.2, fun m => ?_⟩
      have h := hy m
      rw [Subtype.ext_iff] at h
      simpa [SubMulAction.val_smul] using h
    · intro y z _ _ hyz
      exact Subtype.ext hyz
    · intro x hx
      refine ⟨⟨x, hx.1⟩, ?_, rfl⟩
      intro m
      exact Subtype.ext (by simpa [SubMulAction.val_smul] using hx.2 m)
  have key := hM.card_modEq_card_fixedPoints ↥sa
  rw [h1, h2] at key
  exact key

/-! ## 1. The conjugation action of a subgroup on subgroups (universe-polymorphic) -/

open scoped Pointwise

/-- **The conjugation action of a subgroup `H ≤ G` on the subgroups of `G`**: `h • P = h P h⁻¹`.
With this action `h • P` is definitionally `Work.GW2.conjSub h P`.  (This is the
universe-polymorphic version of `Work.CORE4.conjSubMulAction`.) -/
@[instance_reducible] def conjSubMulActionG {G : Type*} [Group G] (H : Subgroup G) :
    MulAction H (Subgroup G) :=
  MulAction.compHom (Subgroup G) ((MulAut.conj : G →* MulAut G).comp H.subtype)

attribute [local instance] conjSubMulActionG

/-- Under `conjSubMulActionG`, `h • P` is `Work.GW2.conjSub h P`. -/
theorem conjSubMulActionG_smul {G : Type*} [Group G] (H P : Subgroup G) (h : H) :
    h • P = Work.GW2.conjSub (h : G) P := rfl

/-- Orbit–stabiliser for the conjugation action of a subgroup `H ≤ G` on the subgroups of `G`:
the number of distinct `H`-conjugates `h P h⁻¹` (`h ∈ H`) of `P` is the index in `H` of the
stabiliser `H ⊓ N_G(P)`. -/
theorem ncard_conjSubOrbit {G : Type*} [Group G] [Finite G] (H P : Subgroup G) :
    {X : Subgroup G | ∃ h ∈ H, X = Work.GW2.conjSub h P}.ncard
      = (H ⊓ Subgroup.normalizer (P : Set G)).relIndex H := by
  have horb : {X : Subgroup G | ∃ h ∈ H, X = Work.GW2.conjSub h P}
      = MulAction.orbit H P := by
    ext X
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨h, hh, rfl⟩
      exact ⟨⟨h, hh⟩, rfl⟩
    · rintro ⟨h, rfl⟩
      exact ⟨h.1, h.2, rfl⟩
  have hstab : MulAction.stabilizer H P
      = (H ⊓ Subgroup.normalizer (P : Set G)).subgroupOf H := by
    ext x
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_normalizer_iff_map_conj_eq]
    constructor
    · intro h
      refine ⟨x.2, ?_⟩
      change Work.GW2.conjSub (↑x) P = P
      rw [← conjSubMulActionG_smul H P x]
      exact h
    · rintro ⟨-, h⟩
      rw [conjSubMulActionG_smul]
      exact h
  rw [horb, ← MulAction.index_stabilizer H P, hstab]
  rfl

/-- Conjugation preserves the cardinality of a subgroup. -/
lemma card_conjSub' {G : Type*} [Group G] (g : G) (P : Subgroup G) :
    Nat.card (Work.GW2.conjSub g P) = Nat.card P := by
  rw [Work.GW2.conjSub]
  exact Subgroup.card_map_of_injective (MulAut.conj g).injective

/-! ## 2. The main count -/

theorem CopyLocalCount {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) (hpodd : Odd p)
    {D X : Subgroup G} (hXcard : Nat.card X = p) (hXD : X ≤ D)
    (K : Subgroup G) (hKodd : Odd (Nat.card K))
    (hS : {Z : Subgroup G | Z ≤ D ∧ Nat.card Z = p} = {Z : Subgroup G | ∃ c ∈ K, Z = Work.GW2.conjSub c X})
    (hfix : ∀ Z : Subgroup G, Z ≤ D → Nat.card Z = p → X ≤ Subgroup.normalizer (Z : Set G) → Z = X) :
    {Z : Subgroup G | Z ≤ D ∧ Nat.card Z = p}.ncard % (2 * p) = 1 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set S : Set (Subgroup G) := {Z : Subgroup G | Z ≤ D ∧ Nat.card Z = p} with hSdef
  have hS' : S = {Z : Subgroup G | ∃ c ∈ K, Z = Work.GW2.conjSub c X} := by
    rw [hSdef]; exact hS
  -- ### Part A: `S.ncard ≡ 1 [MOD p]`, from the action of the `p`-group `X` on `S`.
  have hmodp : S.ncard ≡ 1 [MOD p] := by
    have hXinv : ∀ (x : ↥X) {Z : Subgroup G}, Z ∈ S → x • Z ∈ S := by
      intro x Z hZ
      rw [conjSubMulActionG_smul]
      refine ⟨fun y hy => ?_, by rw [card_conjSub']; exact hZ.2⟩
      obtain ⟨z, hz, rfl⟩ := hy
      exact D.mul_mem (D.mul_mem (hXD x.2) (hZ.1 hz)) (D.inv_mem (hXD x.2))
    -- the fixed points of the action of `X` on `S` are exactly `{X}`
    have hfp : {Z : Subgroup G | Z ∈ S ∧ ∀ x : ↥X, x • Z = Z} = {X} := by
      ext Z
      constructor
      · rintro ⟨hZD, hZfix⟩
        refine hfix Z hZD.1 hZD.2 ?_
        intro x hx
        have h := hZfix ⟨x, hx⟩
        rw [conjSubMulActionG_smul] at h
        exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h
      · rintro rfl
        refine ⟨⟨hXD, hXcard⟩, fun x => ?_⟩
        rw [conjSubMulActionG_smul]
        exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer x.2)
    have hXpg : IsPGroup p ↥X := IsPGroup.of_card (n := 1) (by simpa [pow_one] using hXcard)
    have key := ncard_modEq_ncard_fixedPoints (p := p) hXpg S (fun x Z hZ => hXinv x hZ)
    rw [hfp] at key
    simpa using key
  -- ### Part B: `S.ncard ≡ 1 [MOD 2]`, since `S = X^K` and `|K|` is odd.
  have hmod2 : S.ncard ≡ 1 [MOD 2] := by
    have hoddS : Odd S.ncard := by
      rw [hS', ncard_conjSubOrbit K X]
      exact Nat.not_even_iff_odd.mp fun he =>
        (Nat.not_even_iff_odd.mpr hKodd)
          (even_iff_two_dvd.mpr (dvd_trans (even_iff_two_dvd.mp he)
            (Subgroup.relIndex_dvd_card _ K)))
    show S.ncard % 2 = 1 % 2
    rw [Nat.odd_iff.mp hoddS]
  -- ### Combine by CRT (`p` is odd, so `2` and `p` are coprime).
  have hcop : Nat.Coprime 2 p := Nat.coprime_two_left.mpr hpodd
  have hmul : S.ncard ≡ 1 [MOD 2 * p] := by
    rw [← Nat.modEq_and_modEq_iff_modEq_mul hcop]
    exact ⟨hmod2, hmodp⟩
  have h1 : 1 % (2 * p) = 1 := Nat.mod_eq_of_lt (by nlinarith [hp.two_le])
  rw [Nat.ModEq, h1] at hmul
  exact hmul

end Work.CORE4
