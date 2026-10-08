import Mathlib
import Submission.Work.ThreePoints.ThmC.Baer
import Submission.Work.Coprime.abelian_split
import Submission.Work.Coprime.Internal
import Submission.Work.Coprime.fixedPoints_ne_bot_of_isPGroup
import Submission.Work.PGroup.Omega1
import Submission.Work.ThreePoints.ThmC.exists_orderOf_prime_mem_commutator_fixed
import Submission.Work.ThreePoints.ThmC.exists_not_commute_of_baer

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open scoped commutatorElement Pointwise
open Subgroup

namespace Work.ThreePoints.ThmC

/-- Peterfalvi I App. IV, Lemma 4, final step (the Baer/Blackburn argument, pp. 209-210).

Let `p` be an odd prime, `Q` a finite `p`-group of nilpotency class at most two
(`⁅⊤,⊤⁆ ≤ Z(Q)` inside `↥Q`), `X` a `p'`-subgroup and `P` a `p`-subgroup of `Γ` with
`X ≤ N(Q)`, `P ≤ N(Q)` and `P ≤ N(X)`. If `X` does not centralise `Q`, then `X` does not
centralise `Ω₁(C_Q(P))`.

Route: put `U := X ⊔ P ≤ N(Q)` (so `X ⊴ U`, using `P ≤ N(X)`) and let `↥U` act on `↥Q` by
conjugation; apply `baer_group_exists` (`Submission/Work/ThreePoints/ThmC/Baer.lean`) to the
class-two odd-order group `↥Q` with this action, getting an abelian group `G` with a `↥U`-action
and an equivariant bijection `e : ↥Q ≃ G` preserving `orderOf`. Transport the action along
`Subgroup.inclusion le_sup_left : ↥X →* ↥U` to get an action of `↥X` on `G`
(`MulDistribMulAction.compHom`). By `Work.Coprime.abelian_split` (coprime: `|X|` is coprime to `p`
and `|G| = |Q|` is a power of `p`), `G = C_G(X) · [G,X]` is a complement pair, so
`C_G(X) ⊓ [G,X] = ⊥`. Since `e` intertwines the actions and `X` does not centralise `Q`, `[G,X]`
is nontrivial, hence (as `|G|` is a `p`-power) a nontrivial `p`-group. It is `↥P`-invariant
because `X ⊴ U` (`u • [G,X] = [u • G, u • X] = [G,X]` for `u : ↥U`), so restricting the action
first to `↥P` (`MulDistribMulAction.compHom` along `Subgroup.inclusion le_sup_right`) and then to
the invariant subgroup `[G,X]` (`FT.instSubgroupMulDistribMulAction`),
`Work.Coprime.fixedPoints_ne_bot_of_isPGroup` yields a nontrivial `P`-fixed element of `[G,X]`, a
suitable power of which has order exactly `p`. It lies in `[G,X]`, hence outside `C_G(X)`; pulling
back along `e` gives an element of `Q` of order `p` commuting with `P` but not with `X`, so
`⁅X, Ω₁(Q ⊓ C_Γ(P))⁆ ≠ ⊥`. -/
theorem app4_blackburn_step {Γ : Type} [Group Γ] [Finite Γ] {p : ℕ} (hp : p.Prime) (hpodd : p ≠ 2)
    {Q X P : Subgroup Γ} (hQp : IsPGroup p Q) (hXp : Nat.Coprime (Nat.card X) p)
    (hPp : IsPGroup p P) (hXQ : X ≤ Subgroup.normalizer (Q : Set Γ))
    (hPQ : P ≤ Subgroup.normalizer (Q : Set Γ))
    (hPX : P ≤ Subgroup.normalizer (X : Set Γ))
    (hclass : ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ ≤ Subgroup.center Q)
    (hne : ⁅X, Q⁆ ≠ ⊥) :
    ⁅X, Work.PGroup.omega1 Γ p (Q ⊓ Subgroup.centralizer (P : Set Γ))⁆ ≠ ⊥ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  -- the subgroup `U = X ⊔ P`, which normalises `Q`, and in which `X` is normal
  set U : Subgroup Γ := X ⊔ P with hUdef
  have hXU : X ≤ U := le_sup_left
  have hPU : P ≤ U := le_sup_right
  have hUQ : U ≤ Subgroup.normalizer (Q : Set Γ) := sup_le hXQ hPQ
  have hUX : U ≤ Subgroup.normalizer (X : Set Γ) := sup_le Subgroup.le_normalizer hPX
  haveI hnorm : FT.Normalizes U Q := ⟨hUQ⟩
  -- Baer's construction
  have hodd : Odd (Nat.card Q) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQp
    rw [hk]
    exact Odd.pow (n := k) (hp.odd_of_ne_two hpodd)
  obtain ⟨G, instG, instComm, instAct, e, he_ord, he_eq⟩ :=
    baer_group_exists ↥Q hodd hclass ↥U
  letI := instG
  letI := instComm
  letI := instAct
  haveI : Finite G := Finite.of_equiv (↥Q) e
  -- coprimality and `p`-group facts transported to `U`
  have hcardX : Nat.card (X.subgroupOf U) = Nat.card X :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXU).toEquiv
  have hXp' : Nat.Coprime (Nat.card (X.subgroupOf U)) p := by rw [hcardX]; exact hXp
  have hPp' : IsPGroup p (P.subgroupOf U) :=
    hPp.of_equiv (Subgroup.subgroupOfEquivOfLe hPU).symm
  have hGp : IsPGroup p G := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQp
    refine IsPGroup.of_card (n := k) ?_
    rw [← Nat.card_congr e]
    exact hk
  -- `X` is normal in `U`
  have hXn : (⊤ : Subgroup ↥U) ≤ Subgroup.normalizer (X.subgroupOf U : Set ↥U) := by
    intro u _
    rw [Subgroup.mem_normalizer_iff]
    intro a
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    rw [show ((u * a * u⁻¹ : ↥U) : Γ) = (u : Γ) * (a : Γ) * (u : Γ)⁻¹ from by simp]
    exact Subgroup.mem_normalizer_iff.mp (hUX u.2) (a : Γ)
  -- the induced action of `X` on `G`
  letI instXG : MulDistribMulAction (X.subgroupOf U) G :=
    MulDistribMulAction.compHom G (Subgroup.subtype (X.subgroupOf U))
  -- `X` acts nontrivially on `G`:  otherwise it would centralise `Q`
  have hneG : FT.commutator (X.subgroupOf U) (⊤ : Subgroup G) ≠ ⊥ := by
    intro hbot
    have htriv : FT.IsTrivialOn (X.subgroupOf U) G := FT.commutator_eq_bot_iff.mp hbot
    obtain ⟨x₀, hx₀, q₀, hq₀, hxq₀⟩ : ∃ x ∈ X, ∃ q ∈ Q, x * q ≠ q * x := by
      by_contra h
      push Not at h
      refine hne ?_
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      exact (h x hx q hq).symm
    set xX : X.subgroupOf U := ⟨⟨x₀, hXU hx₀⟩, hx₀⟩ with hxXdef
    set qQ : ↥Q := ⟨q₀, hq₀⟩ with hqQdef
    have h1 : e (Subgroup.subtype (X.subgroupOf U) xX • qQ) =
        Subgroup.subtype (X.subgroupOf U) xX • e qQ := he_eq _ _
    have h2 : Subgroup.subtype (X.subgroupOf U) xX • e qQ = e qQ := htriv xX (e qQ)
    have h3 : Subgroup.subtype (X.subgroupOf U) xX • qQ = qQ := e.injective (by rw [h1, h2])
    have h4 : ((Subgroup.subtype (X.subgroupOf U) xX • qQ : ↥Q) : Γ) = q₀ := by
      rw [h3]
    have h5 : ((Subgroup.subtype (X.subgroupOf U) xX • qQ : ↥Q) : Γ) = x₀ * q₀ * x₀⁻¹ := by
      rw [FT.conj_smul_coe]
      rfl
    refine hxq₀ ?_
    have h6 : x₀ * q₀ * x₀⁻¹ = q₀ := by rw [← h5, h4]
    calc x₀ * q₀ = x₀ * q₀ * x₀⁻¹ * x₀ := by group
      _ = q₀ * x₀ := by rw [h6]
  -- the core coprime-action argument
  have hcore := exists_orderOf_prime_mem_commutator_fixed (U := ↥U) (G := G) hp
    (X := X.subgroupOf U) (P := P.subgroupOf U) hXn hXp' hPp' hGp
  obtain ⟨g, _hgmem, hgord, hgfix, hgnot⟩ := hcore hneG
  -- transport back to `Γ`
  have hPfix : ∀ q : P, Subgroup.inclusion hPU q • g = g := by
    intro q
    exact hgfix ⟨Subgroup.inclusion hPU q, by rw [Subgroup.mem_subgroupOf]; exact q.2⟩
  have hXne : ∃ x : X, Subgroup.inclusion hXU x • g ≠ g := by
    by_contra h
    push Not at h
    refine hgnot ?_
    rw [FT.mem_fixedPoints]
    intro a
    show Subgroup.subtype (X.subgroupOf U) a • g = g
    exact h ⟨(a : ↥U).1, a.2⟩
  obtain ⟨q, hqomega, x, hxX, hxq⟩ :=
    exists_not_commute_of_baer (X := X) (P := P) (U := U) hPU hXU e he_ord he_eq g hgord hPfix hXne
  -- conclude
  intro hbot
  have hxcent := (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot) hxX
  exact hxq ((Subgroup.mem_centralizer_iff.mp hxcent) q hqomega).symm

end Work.ThreePoints.ThmC
