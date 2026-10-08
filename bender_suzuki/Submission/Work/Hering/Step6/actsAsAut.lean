import Mathlib
import Submission.Work.Hering.Config
import Submission.Work.Hering.Wagner.Defs
import Submission.Work.Hering.InvSubgroup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `G` acts on `V = Inv(G) ∪ {1}` as its full automorphism group

Peterfalvi I §2 Proposition (p. 191), the reduction step: for a finite group `G` of 2-rank `≥ 2`
acting doubly transitively on its involutions, with `V = Inv(G) ∪ {1}` of order `8`, the
conjugation action of `G` on `V` realises *every* automorphism of `V`, i.e. `G/C_G(V) ≅ Aut(V)`.

This is an immediate application of **Wagner's proposition** (`Work.Hering.WagnerProp`,
`Work.Hering.Wagner.wagner_prop`): `V` is a finite abelian group of exponent `2`
(`Work.Hering.invSubgroup_comm`, `Work.Hering.pow_two_eq_one_of_mem_invSubgroup`), the image of
`G` in `MulAut V` is doubly transitive on `V \ {1}` (`hDT`), and `|V| = 8`, so `U = V` is a
subgroup of order `8`, every automorphism of which is induced by an element of the image.

## Universe bookkeeping

The hypothesis `hWagner : WagnerProp` carries an *independent* universe parameter (`WagnerProp` is
universe polymorphic).  Since the theorem must hold for arbitrary universes, the first lemma below
moves a proof of `WagnerProp` between universes: `Work.Hering.Step6.wagnerProp_univ`.  It uses the
standard small-model replacement `Finite.exists_type_univ_nonempty_mulEquiv` (every finite group in
universe `u` is isomorphic to a finite group in universe `v`) and `MulAut.congr` to transport the
acting group.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Work.Hering.Step6

open Work.Hering

/-- **Universe transfer for Wagner's proposition.** Wagner's proposition is stated for a group in
an arbitrary universe; a proof at one universe gives a proof at any other, by replacing the group
with an isomorphic small model (`Finite.exists_type_univ_nonempty_mulEquiv`) and transporting the
acting group of automorphisms along the isomorphism (`MulAut.congr`). -/
theorem wagnerProp_univ.{u,v} (h : WagnerProp.{u}) : WagnerProp.{v} := by
  intro V _instG _instF habel hexp Gm h2 U hU φ
  obtain ⟨V', instV', finV', ⟨e⟩⟩ := Finite.exists_type_univ_nonempty_mulEquiv.{v,u} V
  letI : Group V' := instV'
  letI : Fintype V' := finV'
  -- commutativity and exponent two are preserved by the isomorphism
  have habel' : ∀ x y : V', x * y = y * x := fun x y => by
    have hc := habel (e.symm x) (e.symm y)
    have : e (e.symm x * e.symm y) = e (e.symm y * e.symm x) := by rw [hc]
    simpa using this
  have hexp' : ∀ x : V', x * x = 1 := fun x => by
    have hc := hexp (e.symm x)
    have : e (e.symm x * e.symm x) = e 1 := by rw [hc]
    simpa using this
  -- the acting group, transported to `V'`
  let Gm' : Subgroup (MulAut V') := Gm.map (MulAut.congr e).toMonoidHom
  have h2' : ∀ a b c d : V', a ≠ 1 → b ≠ 1 → c ≠ 1 → d ≠ 1 → a ≠ b → c ≠ d →
      ∃ g ∈ Gm', g a = c ∧ g b = d := by
    intro a b c d ha hb hc hd hab hcd
    have ha' : e.symm a ≠ 1 := fun hh => ha (by simpa using congrArg e hh)
    have hb' : e.symm b ≠ 1 := fun hh => hb (by simpa using congrArg e hh)
    have hc' : e.symm c ≠ 1 := fun hh => hc (by simpa using congrArg e hh)
    have hd' : e.symm d ≠ 1 := fun hh => hd (by simpa using congrArg e hh)
    have hab' : e.symm a ≠ e.symm b := fun hh => hab (e.symm.injective hh)
    have hcd' : e.symm c ≠ e.symm d := fun hh => hcd (e.symm.injective hh)
    obtain ⟨g, hg, hga, hgb⟩ :=
      h2 (e.symm a) (e.symm b) (e.symm c) (e.symm d) ha' hb' hc' hd' hab' hcd'
    refine ⟨(MulAut.congr e) g, Subgroup.mem_map_of_mem _ hg, ?_, ?_⟩
    · rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, hga,
        e.apply_symm_apply]
    · rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, hgb,
        e.apply_symm_apply]
  have hU' : Nat.card ↥(U.map (e : V →* V')) = 8 := by
    rw [Subgroup.card_map_of_injective e.injective]
    exact hU
  -- apply Wagner at the universe of `h` to the transported configuration
  obtain ⟨g', hg', hg'prop⟩ :=
    h habel' hexp' Gm' h2' (U.map (e : V →* V')) hU' (MulAut.congr (e.subgroupMap U) φ)
  dsimp only [Gm'] at hg'
  rw [Subgroup.mem_map] at hg'
  obtain ⟨g, hg, hgg'⟩ := hg'
  have hgg2 : (MulAut.congr e) g = g' := hgg'
  refine ⟨g, hg, ?_⟩
  intro u
  have hmain : e (g (u : V)) = e ((φ u : U) : V) := by
    have h1 := hg'prop (e.subgroupMap U u)
    rw [← hgg2] at h1
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.coe_subgroupMap_apply,
      MulEquiv.symm_apply_apply] at h1
    exact h1
  exact e.injective hmain

/-- **Peterfalvi I §2 (reduction step).** If `G` is a finite group of 2-rank `≥ 2` acting doubly
transitively by conjugation on its involutions and `V = Inv(G) ∪ {1}` has order `8`, then the
conjugation action of `G` on `V` induces every automorphism of `V`: `G/C_G(V) ≅ Aut(V)`. -/
theorem actsAsAut {G : Type*} [Group G] [Finite G] {hDT : DTInv G} {h4 : HasFourGroup G}
    (hWagner : WagnerProp) (h8 : Nat.card ↥(invSubgroup hDT h4) = 8) :
    ActsAsAut (invSubgroup hDT h4) (invSubgroup_normal hDT h4) := by
  classical
  set V : Subgroup G := invSubgroup hDT h4 with hVdef
  haveI hVn : V.Normal := invSubgroup_normal hDT h4
  -- an element of `V` different from `1` is an involution
  have key : ∀ x : ↥V, x ≠ 1 → orderOf ((x : G)) = 2 := by
    intro x hx
    rcases (mem_invSubgroup hDT h4).mp x.2 with h | h
    · exact h
    · exact absurd (Subtype.ext (by simpa using h)) hx
  -- `V` is abelian of exponent two
  have habel : ∀ x y : ↥V, x * y = y * x := fun x y =>
    Subtype.ext (by
      show (x : G) * (y : G) = (y : G) * (x : G)
      exact invSubgroup_comm hDT h4 x.2 y.2)
  have hexp : ∀ x : ↥V, x * x = 1 := fun x =>
    Subtype.ext (by
      show (x : G) * (x : G) = (1 : G)
      simpa using pow_two_eq_one_of_mem_invSubgroup hDT h4 x.2)
  intro φ
  -- Wagner is applied with `U = ⊤` (recall `|V| = 8`); `φtop` is `φ` transported across
  -- the canonical isomorphism `⊤ ≃ V`.
  let e : ↥(⊤ : Subgroup ↥V) ≃* ↥V := Subgroup.topEquiv
  let φtop : MulAut ↥(⊤ : Subgroup ↥V) := e.trans (φ.trans e.symm)
  -- the acting group: the image of `G` in `MulAut V` under conjugation
  let Gm : Subgroup (MulAut ↥V) := (MulAut.conjNormal (H := V)).range
  have hU : Nat.card ↥(⊤ : Subgroup ↥V) = 8 := by
    rw [Subgroup.card_top]
    simpa using h8
  -- `Gm` is doubly transitive on `V \ {1}`, by `hDT`
  have h2 : ∀ a b c d : ↥V, a ≠ 1 → b ≠ 1 → c ≠ 1 → d ≠ 1 → a ≠ b → c ≠ d →
      ∃ g ∈ Gm, g a = c ∧ g b = d := by
    intro a b c d ha hb hc hd hab hcd
    have ha2 := key a ha
    have hb2 := key b hb
    have hc2 := key c hc
    have hd2 := key d hd
    have hab' : (a : G) ≠ (b : G) := fun h => hab (Subtype.ext h)
    have hcd' : (c : G) ≠ (d : G) := fun h => hcd (Subtype.ext h)
    obtain ⟨g0, hg0a, hg0b⟩ :=
      hDT (a : G) (b : G) (c : G) (d : G) ha2 hb2 hc2 hd2 hab' hcd'
    refine ⟨MulAut.conjNormal g0, ?_, ?_, ?_⟩
    · simp only [Gm, MonoidHom.mem_range]
      exact ⟨g0, rfl⟩
    · apply Subtype.ext
      rw [MulAut.conjNormal_apply]
      exact hg0a
    · apply Subtype.ext
      rw [MulAut.conjNormal_apply]
      exact hg0b
  obtain ⟨g, hg, hgprop⟩ :=
    (wagnerProp_univ hWagner) habel hexp Gm h2 (⊤ : Subgroup ↥V) hU φtop
  simp only [Gm, MonoidHom.mem_range] at hg
  obtain ⟨g0, hg0⟩ := hg
  refine ⟨g0, ?_⟩
  intro v
  have h := hgprop ⟨v, Subgroup.mem_top v⟩
  have hφtop : ((φtop ⟨v, Subgroup.mem_top v⟩ : ↥(⊤ : Subgroup ↥V)) : ↥V) = φ v := by
    simp only [φtop, MulEquiv.trans_apply]
    congr 1
  have hmain : g v = φ v := h.trans hφtop
  rw [← hg0] at hmain
  exact hmain.symm

end Work.Hering.Step6
