import Mathlib
import Submission.Work.ZassenhausPSL2.Defs
import Submission.Work.ZassenhausPSL2.Basic
import Submission.Work.ZassenhausPSL2.Feit.card_G_eq
import Submission.Work.ZassenhausPSL2.FeitCln.ncard_involutions_G
import Submission.Work.ZassenhausPSL2.Feit.mem_same_conj
import Submission.Work.ZassenhausPSL2.Feit.centralizer_eq_Q
import Submission.Work.ZassenhausPSL2.Feit.odd_index_Q
import Submission.Work.ZassenhausPSL2.ZData.FeitBoundAux
import Submission.Work.ZassenhausPSL2.ZData.card_dStab_eq_card_involutions
import Submission.Work.ZassenhausTwoGroup.normalizer_Q_eq
import Submission.Work.ThmG.rankOne_index
import Submission.Work.CharCore.Defs
import Submission.Work.Induction.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Feit's class count `card_conjClasses_ge`

The class count of Feit 1960, §2 (leaf `F1` of
`Submission/Work/ZassenhausPSL2/NOTES_LEAD_bs_psl2core.md`): in a finite group `G` with
split rank-one (Zassenhaus) data `(H, Q, t)`, `Q` an abelian `2`-group,

`#Cl(G) · |D| ≥ |D| + (|Q| - 1) + |D|²`,  where `D = twoPoint H t = H ∩ Hᵗ`.

Outline of the proof (`d = |D|`, `m = |Q|`, `Ω = G ⧸ H`, so `|Ω| = m + 1` and `|G| = (m+1)md`):

* `#Cl(G)·|G| = Σ_{g∈G} |C_G(g)|`, the number of commuting pairs (Mathlib's
  `card_comm_eq_card_conjClasses_mul_card`).
* Split `G` into `{1}`, the nontrivial `2`-elements and the rest.
  * `|C_G(1)| = |G| = (m+1)md`;
  * every nontrivial `2`-element has centraliser of order `m` (`centralizer_eq_Q`), and the
    conjugates of `Q` are the `m+1` pairwise almost disjoint root subgroups, so
    `Σ_{x ∈ 2-elts, x≠1} |C_G(x)| ≥ (m+1)·m·(m-1)`;
  * for `g` not a `2`-element, `|C_G(g)|` is at least the number of involutions inverting `g`,
    and summing over `g` counts pairs `(u,v)` of involutions with `uv` not a `2`-element:
    `= I² - N` where `I = #Inv(G) = (m+1)d` and `N ≤ (m+1)d²` is the number of such pairs with
    `2`-element product (each lies in a common conjugate of `Q`, which contains exactly `d`
    involutions).  So the third part is `≥ ((m+1)d)² - (m+1)d² = (m+1)md²`.
* Adding up: `#Cl(G)·(m+1)md ≥ (m+1)m·(d + (m-1) + d²)`; cancel `(m+1)m`.

The vocabulary used by the counting is `TwoElts` (the `2`-elements) and `Qomega` (the
conjugate of `Q` indexed by a point of `Ω = G ⧸ H`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.ZassenhausPSL2.FeitCln

open Work.ZassenhausPSL2.Feit

/-- The `2`-elements of a group, together with the identity (`orderOf g` a power of `2`). -/
def TwoElts (G : Type*) [Group G] : Set G := {g : G | ∃ n : ℕ, orderOf g = 2 ^ n}

/-- The conjugate of the root group `Q` attached to the point `ω` of `Ω = G ⧸ H`: the
conjugate by the representative `Quotient.out ω` of the coset. -/
noncomputable def Qomega {G : Type*} [Group G] (H Q : Subgroup G) (ω : G ⧸ H) : Subgroup G :=
  Submission.Blueprint.conj (Quotient.out ω) Q

/-- The counting structure of the root group conjugates: the subgroups `Qomega H Q ω`,
`ω ∈ Ω = G ⧸ H`, are all conjugate to `Q` (so have `|Q|` elements, `|D|` involutions, are
abelian `2`-groups), they cover every conjugacy class of root subgroups, and two distinct
conjugates meet only in the identity. -/
structure QomegaData {G : Type} [Group G] [Finite G] (H Q : Subgroup G) (t : G) where
  /-- a split rank-one root group is self-normalising: `N_G(Q) = H`. -/
  normalizer_eq : Subgroup.normalizer (Q : Set G) = H
  /-- every conjugate has the same order as `Q`. -/
  card : ∀ ω : G ⧸ H, Nat.card (Qomega H Q ω) = Nat.card Q
  /-- conjugates of an abelian subgroup are abelian. -/
  abelian : ∀ ω : G ⧸ H, IsAbelianSubgroup (Qomega H Q ω)
  /-- conjugates of a `2`-group are `2`-groups. -/
  isPGroup : ∀ ω : G ⧸ H, IsPGroup 2 (Qomega H Q ω)
  /-- every element of a conjugate is a `2`-element. -/
  twoElt : ∀ (ω : G ⧸ H) (x : G), x ∈ Qomega H Q ω → ∃ n : ℕ, orderOf x = 2 ^ n
  /-- every conjugate contains exactly `|D|` involutions. -/
  invcard : ∀ ω : G ⧸ H,
    (Submission.Blueprint.involutions (Qomega H Q ω : Set G)).ncard =
      Nat.card (Submission.Blueprint.twoPoint H t)
  /-- the conjugates are indexed correctly: conjugation by `g` gives the `⟦g⟧`-th one. -/
  cover : ∀ g : G, Submission.Blueprint.conj g Q = Qomega H Q (QuotientGroup.mk g)
  /-- two distinct conjugates meet only in `1`. -/
  inj : ∀ (ω ω' : G ⧸ H) (x : G), x ∈ Qomega H Q ω → x ∈ Qomega H Q ω' → x ≠ 1 → ω = ω'

/-!
## The counting inputs

Everything in this section is `Intern` (private to the file): it is written so that no name
here can clash with the sibling modules of the workspace that import this file.  The four
lemmas `card_conjClasses_mul_card_eq_sigma`, `qomegaData_nonempty`,
`sum_centralizer_twoElts_ge`, `sum_centralizer_compl_ge` and `natCard_cent_eq_split` are the
counting inputs of Feit's class count, proved here and assembled at the end of the file.
-/

namespace Intern

/-! ### The commuting-pair count -/

/-- The sigma type of centralisers `Σ g : G, ↥(Subgroup.centralizer {g})` is equivalent to the
type of commuting pairs `{p : G × G // Commute p.1 p.2}`: the forward map sends `⟨g, x⟩` to the
pair `(g, x)` with the commuting proof obtained from `x ∈ C_G(g)`, and conversely. -/
def sigmaCentralizerEquivCommute (G : Type) [Group G] :
    (Sigma (fun g : G => Subgroup.centralizer ({g} : Set G))) ≃
      { p : G × G // Commute p.1 p.2 } where
  toFun p := ⟨(p.1, p.2.1), (Subgroup.mem_centralizer_singleton_iff.mp p.2.2).symm⟩
  invFun q := ⟨q.1.1, ⟨q.1.2, Subgroup.mem_centralizer_singleton_iff.mpr q.2.symm⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- `#Cl(G) · |G| = Σ_{g∈G} |C_G(g)|` (Mathlib's `card_comm_eq_card_conjClasses_mul_card`). -/
theorem card_conjClasses_mul_card_eq_sigma {G : Type} [Group G] [Finite G] :
    Nat.card (ConjClasses G) * Nat.card G =
      Nat.card (Sigma (fun g : G => Subgroup.centralizer ({g} : Set G))) := by
  rw [← card_comm_eq_card_conjClasses_mul_card G]
  exact Nat.card_congr (sigmaCentralizerEquivCommute G).symm

/-! ### The root-group conjugates -/

variable {G : Type} [Group G]

/-- Elementwise description of `Submission.Blueprint.conj`. -/
lemma mem_conj_gs {H : Subgroup G} {g x : G} :
    x ∈ Submission.Blueprint.conj g H ↔ ∃ h ∈ H, g * h * g⁻¹ = x := by
  rw [Submission.Blueprint.conj, Subgroup.mem_map]
  constructor
  · rintro ⟨h, hh, hhx⟩
    exact ⟨h, hh, by rw [← hhx]; exact MulAut.conj_apply g h⟩
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h, hh, by simpa using MulAut.conj_apply g h⟩

/-- `Q` is non-trivial in a split rank-one datum: `Q = ⊥` would force `D = H`, whose order
would then be both even (strong embedding) and odd (`dStab_odd`). -/
lemma Q_ne_bot_of_split {H Q : Subgroup G} {t : G}
    (h : IsSplitRankOne H Q t) : Q ≠ ⊥ := by
  intro hbot
  have htwo : twoPoint H t = H := by
    have hs : Q ⊔ twoPoint H t = H := h.sup_eq
    rw [hbot, bot_sup_eq] at hs
    exact hs
  have hodd : Odd (Nat.card (twoPoint H t)) :=
    Work.ZassenhausPSL2.dStab_odd H t h.stronglyEmbedded h.not_mem
  rw [htwo] at hodd
  exact (Nat.not_odd_iff_even.mpr h.stronglyEmbedded.2.1) hodd

/-- Conjugation by a fixed group element preserves the number of involutions of a subgroup. -/
lemma ncard_involutions_conj (Q : Subgroup G) (g : G) :
    (involutions (Submission.Blueprint.conj g Q : Set G)).ncard =
      (involutions (Q : Set G)).ncard := by
  have hset : involutions (Submission.Blueprint.conj g Q : Set G) =
      (MulAut.conj g : G → G) '' involutions (Q : Set G) := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxQ, hx2⟩ := hx
      have hxQ' : x ∈ Submission.Blueprint.conj g Q := hxQ
      rw [mem_conj_gs] at hxQ'
      obtain ⟨q, hq, hqx⟩ := hxQ'
      refine ⟨q, ⟨hq, ?_⟩, ?_⟩
      · have h1 : orderOf (MulAut.conj g q) = orderOf q :=
          orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective q
        rw [← h1, MulAut.conj_apply g q, hqx]
        exact hx2
      · exact (MulAut.conj_apply g q).trans hqx
    · rintro ⟨q, hq, rfl⟩
      refine ⟨Subgroup.mem_map.mpr ⟨q, hq.1, rfl⟩, ?_⟩
      have h1 : orderOf (MulAut.conj g q) = orderOf q :=
        orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective q
      rw [h1]
      exact hq.2
  rw [hset, Set.ncard_image_of_injective _ (MulAut.conj g).injective]

/-- Every element of a conjugate of a `2`-group `Q` has `2`-power order. -/
lemma Qomega_pow_eq_one {H Q : Subgroup G} (h2 : IsPGroup 2 Q) (ω : G ⧸ H)
    {x : G} (hx : x ∈ Qomega H Q ω) : ∃ k : ℕ, x ^ (2 ^ k) = 1 := by
  rw [Qomega] at hx
  rw [mem_conj_gs] at hx
  obtain ⟨q, hq, hqx⟩ := hx
  obtain ⟨k, hk⟩ := h2 ⟨q, hq⟩
  refine ⟨k, ?_⟩
  have hqk : q ^ (2 ^ k) = 1 := by
    have := congrArg (fun z : ↥Q => (z : G)) hk
    simpa using this
  rw [← hqx,
    show Quotient.out ω * q * (Quotient.out ω)⁻¹ = MulAut.conj (Quotient.out ω) q from
      (MulAut.conj_apply (Quotient.out ω) q).symm,
    ← map_pow, hqk, map_one]

/-- Every element of a conjugate of a `2`-group `Q` has order a power of `2`. -/
lemma Qomega_orderOf {H Q : Subgroup G} (h2 : IsPGroup 2 Q) (ω : G ⧸ H)
    {x : G} (hx : x ∈ Qomega H Q ω) : ∃ n : ℕ, orderOf x = 2 ^ n := by
  obtain ⟨k, hk⟩ := Qomega_pow_eq_one h2 ω hx
  have hdvd : orderOf x ∣ 2 ^ k := orderOf_dvd_iff_pow_eq_one.mpr hk
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  exact ⟨j, hj⟩

/-- **The root-group conjugates.**  The subgroups `Qomega H Q ω`, `ω ∈ G ⧸ H`, are all
conjugate to `Q` (hence have `|Q|` elements, `|D|` involutions, and are abelian `2`-groups),
they cover every conjugate of `Q`, and two distinct ones meet only in `1`. -/
theorem qomegaData_nonempty {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) (hz : Submission.Blueprint.IsZassenhaus H)
    (h2 : IsPGroup 2 Q) (hab : Submission.Blueprint.IsAbelianSubgroup Q) :
    Nonempty (Work.ZassenhausPSL2.FeitCln.QomegaData H Q t) := by
  classical
  have hQne : Q ≠ ⊥ := Q_ne_bot_of_split h
  have hN : Subgroup.normalizer (Q : Set G) = H :=
    Work.ZassenhausTwoGroup.normalizer_Q_eq h hQne
  have hD : Nat.card ↥(twoPoint H t) = (involutions (Q : Set G)).ncard :=
    Work.ZassenhausPSL2.ZData.card_dStab_eq_card_involutions H Q t h hz hQne h2
  refine ⟨{ normalizer_eq := hN
            card := ?_
            abelian := ?_
            isPGroup := ?_
            twoElt := ?_
            invcard := ?_
            cover := ?_
            inj := ?_ }⟩
  · intro ω
    show Nat.card ↥(Qomega H Q ω) = Nat.card ↥Q
    rw [Qomega]
    exact Subgroup.card_map_of_injective (MulAut.conj (Quotient.out ω)).injective
  · intro ω
    show ∀ x ∈ Qomega H Q ω, ∀ y ∈ Qomega H Q ω, x * y = y * x
    intro x hx y hy
    rw [Qomega] at hx hy
    rw [mem_conj_gs] at hx hy
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    calc (Quotient.out ω * a * (Quotient.out ω)⁻¹) *
            (Quotient.out ω * b * (Quotient.out ω)⁻¹)
        = Quotient.out ω * (a * b) * (Quotient.out ω)⁻¹ := by group
      _ = Quotient.out ω * (b * a) * (Quotient.out ω)⁻¹ := by rw [hab a ha b hb]
      _ = (Quotient.out ω * b * (Quotient.out ω)⁻¹) *
            (Quotient.out ω * a * (Quotient.out ω)⁻¹) := by group
  · intro ω x
    obtain ⟨k, hk⟩ := Qomega_pow_eq_one h2 ω x.2
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  · intro ω x hx
    exact Qomega_orderOf h2 ω hx
  · intro ω
    have h1 := ncard_involutions_conj Q (Quotient.out ω)
    exact h1.trans hD.symm
  · intro g
    change Submission.Blueprint.conj g Q =
      Submission.Blueprint.conj (Quotient.out ((g : G ⧸ H))) Q
    set a := Quotient.out ((g : G ⧸ H)) with ha
    have hmk : (a : G ⧸ H) = (g : G ⧸ H) := by
      rw [ha]
      exact QuotientGroup.out_eq' _
    have hmem : a⁻¹ * g ∈ H := QuotientGroup.eq.mp hmk
    apply le_antisymm
    · intro x hx
      rw [mem_conj_gs] at hx ⊢
      obtain ⟨q, hq, hqx⟩ := hx
      refine ⟨(a⁻¹ * g) * q * (a⁻¹ * g)⁻¹, ?_, ?_⟩
      · exact (Subgroup.le_normalizer_iff.mp h.normal) (a⁻¹ * g) hmem q hq
      · rw [← hqx]; group
    · intro x hx
      rw [mem_conj_gs] at hx ⊢
      obtain ⟨q, hq, hqx⟩ := hx
      refine ⟨(a⁻¹ * g)⁻¹ * q * (a⁻¹ * g), ?_, ?_⟩
      · simpa using (Subgroup.le_normalizer_iff.mp h.normal) (a⁻¹ * g)⁻¹ (H.inv_mem hmem) q hq
      · rw [← hqx]; group
  · intro ω ω' x hx hx' hx1
    by_contra hne
    rw [Qomega] at hx hx'
    set a := Quotient.out ω with ha
    set b := Quotient.out ω' with hb
    have hab : a⁻¹ * b ∉ H := by
      intro hmem
      apply hne
      have h1 : (a : G ⧸ H) = (b : G ⧸ H) := QuotientGroup.eq.mpr hmem
      have h2 : (a : G ⧸ H) = ω := by rw [ha]; exact QuotientGroup.out_eq' ω
      have h3 : (b : G ⧸ H) = ω' := by rw [hb]; exact QuotientGroup.out_eq' ω'
      exact h2.symm.trans (h1.trans h3)
    have hy : a⁻¹ * x * a ∈ Q := by
      rw [mem_conj_gs] at hx
      obtain ⟨q, hq, hqx⟩ := hx
      rw [← hqx]
      have : a⁻¹ * (a * q * a⁻¹) * a = q := by group
      rw [this]; exact hq
    have hy' : a⁻¹ * x * a ∈ Submission.Blueprint.conj (a⁻¹ * b) Q := by
      rw [mem_conj_gs] at hx'
      rw [mem_conj_gs]
      obtain ⟨q, hq, hqx⟩ := hx'
      refine ⟨q, hq, ?_⟩
      rw [← hqx]; group
    have hbot : a⁻¹ * x * a ∈ (⊥ : Subgroup G) := by
      rw [← Work.ZassenhausTwoGroup.isTI_Q h hz (a⁻¹ * b) hab]
      exact ⟨hy, hy'⟩
    have h1 : a⁻¹ * x * a = 1 := Subgroup.mem_bot.mp hbot
    refine hx1 ?_
    have hx1' : x = a * (a⁻¹ * x * a) * a⁻¹ := by group
    rw [hx1', h1]; group

/-! ### The split of the centraliser sum -/

variable {G : Type} [Group G]

/-- **Cardinality of a sigma type over a decidable sub-predicate.** -/
lemma natCard_sigma_split {α : Type*} [Finite α] (β : α → Type*) [∀ a, Finite (β a)]
    (p : α → Prop) [DecidablePred p] :
    Nat.card (Σ a, β a) =
      Nat.card (Σ a : {a // p a}, β a.1) + Nat.card (Σ a : {a // ¬p a}, β a.1) := by
  classical
  have hα : Fintype α := Fintype.ofFinite α
  have h1 : Nat.card (Σ a, β a) = ∑ a, Nat.card (β a) := Nat.card_sigma
  have h2 : Nat.card (Σ a : {a // p a}, β a.1) = ∑ a : {a // p a}, Nat.card (β a.1) :=
    Nat.card_sigma
  have h3 : Nat.card (Σ a : {a // ¬p a}, β a.1) = ∑ a : {a // ¬p a}, Nat.card (β a.1) :=
    Nat.card_sigma
  rw [h1, h2, h3]
  exact (Fintype.sum_subtype_add_sum_subtype p (fun a => Nat.card (β a))).symm

/-- The part of `Σ g : G, C_G(g)` lying over the single element `g = 1` has cardinality
`Nat.card G`: the centraliser of `1` is `⊤`. -/
lemma natCard_sigma_centralizer_eq_one {G : Type*} [Group G] [Finite G] :
    Nat.card (Σ g : {g : G // g = 1}, Subgroup.centralizer ({g.1} : Set G)) =
      Nat.card G := by
  classical
  have hG : Fintype G := Fintype.ofFinite G
  have h2 : Nat.card (Σ g : {g : G // g = 1}, Subgroup.centralizer ({g.1} : Set G)) =
      ∑ g : {g : G // g = 1}, Nat.card (Subgroup.centralizer ({g.1} : Set G)) :=
    Nat.card_sigma
  rw [h2, Fintype.sum_subsingleton _ (⟨1, rfl⟩ : {g : G // g = 1})]
  have htop : Subgroup.centralizer ({(⟨1, rfl⟩ : {g : G // g = 1}).1} : Set G) = ⊤ := by
    ext x; rw [Subgroup.mem_centralizer_singleton_iff]; simp
  rw [htop, Subgroup.card_top]

/-- The nontrivial `2`-elements inside the non-identity elements are the nontrivial
`2`-elements of `G` (the centraliser fibres match). -/
def sigmaEquivNontrivialTwoElts {G : Type*} [Group G] :
    (Σ g : {g : {g : G // g ≠ 1} // g.1 ∈ TwoElts G},
        Subgroup.centralizer ({g.1.1} : Set G)) ≃
    (Σ x : {x : G // x ∈ TwoElts G ∧ x ≠ 1}, Subgroup.centralizer ({x.1} : Set G)) where
  toFun p := ⟨⟨p.1.1.1, ⟨p.1.2, p.1.1.2⟩⟩, p.2⟩
  invFun q := ⟨⟨⟨q.1.1, q.1.2.2⟩, q.1.2.1⟩, q.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The non-`2`-elements inside the non-identity elements are the non-`2`-elements of `G`. -/
def sigmaEquivNonTwoElts {G : Type*} [Group G] :
    (Σ g : {g : {g : G // g ≠ 1} // g.1 ∉ TwoElts G},
        Subgroup.centralizer ({g.1.1} : Set G)) ≃
    (Σ b : {b : G // b ∉ TwoElts G}, Subgroup.centralizer ({b.1} : Set G)) where
  toFun p := ⟨⟨p.1.1.1, p.1.2⟩, p.2⟩
  invFun q :=
    ⟨⟨⟨q.1.1, fun h => q.1.2 (h.symm ▸ ⟨0, by rw [orderOf_one]; norm_num⟩)⟩, q.1.2⟩, q.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Splitting the centraliser sum.**  `Σ_{g∈G} |C_G(g)|` is the sum over the identity, the
nontrivial `2`-elements, and the elements that are not `2`-elements. -/
theorem natCard_cent_eq_split {G : Type} [Group G] [Finite G] :
    Nat.card (Sigma (fun g : G => Subgroup.centralizer ({g} : Set G))) =
      Nat.card G +
        Nat.card (Sigma (fun x : {x : G // x ∈ Work.ZassenhausPSL2.FeitCln.TwoElts G ∧ x ≠ 1} =>
          Subgroup.centralizer ({x.1} : Set G))) +
        Nat.card (Sigma (fun g : {g : G // g ∉ Work.ZassenhausPSL2.FeitCln.TwoElts G} =>
          Subgroup.centralizer ({g.1} : Set G))) := by
  classical
  have hG : Fintype G := Fintype.ofFinite G
  have h1 : Nat.card (Σ g : G, Subgroup.centralizer ({g} : Set G)) =
      Nat.card (Σ g : {g : G // g = 1}, Subgroup.centralizer ({g.1} : Set G)) +
      Nat.card (Σ g : {g : G // g ≠ 1}, Subgroup.centralizer ({g.1} : Set G)) :=
    natCard_sigma_split (fun g : G => Subgroup.centralizer ({g} : Set G)) (fun g => g = 1)
  have h2 : Nat.card (Σ g : {g : G // g = 1}, Subgroup.centralizer ({g.1} : Set G)) =
      Nat.card G :=
    natCard_sigma_centralizer_eq_one
  have h3 : Nat.card (Σ g : {g : G // g ≠ 1}, Subgroup.centralizer ({g.1} : Set G)) =
      Nat.card (Σ g : {g : {g : G // g ≠ 1} // g.1 ∈ TwoElts G},
        Subgroup.centralizer ({g.1.1} : Set G)) +
      Nat.card (Σ g : {g : {g : G // g ≠ 1} // g.1 ∉ TwoElts G},
        Subgroup.centralizer ({g.1.1} : Set G)) :=
    natCard_sigma_split (fun g : {g : G // g ≠ 1} => Subgroup.centralizer ({g.1} : Set G))
      (fun g => g.1 ∈ TwoElts G)
  have h4 : Nat.card (Σ g : {g : {g : G // g ≠ 1} // g.1 ∈ TwoElts G},
        Subgroup.centralizer ({g.1.1} : Set G)) =
      Nat.card (Σ x : {x : G // x ∈ TwoElts G ∧ x ≠ 1},
        Subgroup.centralizer ({x.1} : Set G)) :=
    Nat.card_congr sigmaEquivNontrivialTwoElts
  have h5 : Nat.card (Σ g : {g : {g : G // g ≠ 1} // g.1 ∉ TwoElts G},
        Subgroup.centralizer ({g.1.1} : Set G)) =
      Nat.card (Σ b : {b : G // b ∉ TwoElts G}, Subgroup.centralizer ({b.1} : Set G)) :=
    Nat.card_congr sigmaEquivNonTwoElts
  rw [h1, h2, h3, h4, h5, Nat.add_assoc]

/-! ### The nontrivial `2`-element part of the centraliser sum -/

/-- `Nat.card {x : α // x ≠ a} = Nat.card α - 1`. -/
lemma natCard_subtype_ne {α : Type*} [Finite α] (a : α) :
    Nat.card {x : α // x ≠ a} = Nat.card α - 1 := by
  haveI : Fintype α := Fintype.ofFinite α
  haveI : Fintype {x : α // x ≠ a} := Fintype.ofFinite _
  haveI : Fintype {x : α // x = a} := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl (fun x : α => x = a),
    Fintype.card_subtype_eq, Fintype.card_eq_nat_card]

/-- **The nontrivial `2`-element part of the centraliser sum.**  The `m + 1` conjugates of the
root group contribute `(m+1)·(m-1)` distinct nontrivial `2`-elements, each with centraliser of
order at least `m`. -/
theorem sum_centralizer_twoElts_ge {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t)
    (Dd : Work.ZassenhausPSL2.FeitCln.QomegaData H Q t) :
    (Nat.card Q + 1) * (Nat.card Q - 1) * Nat.card Q ≤
      Nat.card (Sigma (fun x : {x : G // x ∈ Work.ZassenhausPSL2.FeitCln.TwoElts G ∧ x ≠ 1} =>
        Subgroup.centralizer ({x.1} : Set G))) := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Fintype (G ⧸ H) := Fintype.ofFinite _
  have hcardΩ : Fintype.card (G ⧸ H) = Nat.card Q + 1 := by
    rw [Fintype.card_eq_nat_card, ← Subgroup.index_eq_card]
    exact Work.ThmG.rankOne_index h
  -- the domain of the counting injection
  have hle : Nat.card (Sigma (fun ω : G ⧸ H =>
        {x : ↥(Qomega H Q ω) // x ≠ 1} × ↥(Qomega H Q ω)))
      ≤ Nat.card (Sigma (fun x : {x : G // x ∈ TwoElts G ∧ x ≠ 1} =>
          Subgroup.centralizer ({x.1} : Set G))) := by
    refine Nat.card_le_card_of_injective
      (fun p => ⟨⟨(p.2.1.1.1 : G), ⟨Dd.twoElt p.1 p.2.1.1.1 p.2.1.1.2,
          fun h1 => p.2.1.2 (Subtype.ext h1)⟩⟩,
        ⟨(p.2.2.1 : G), Subgroup.mem_centralizer_singleton_iff.mpr
          (Dd.abelian p.1 p.2.2.1 p.2.2.2 p.2.1.1.1 p.2.1.1.2)⟩⟩) ?_
    rintro ⟨ω, x, y⟩ ⟨ω', x', y'⟩ heq
    have hxval : (x.1.1 : G) = (x'.1.1 : G) := by
      have h1 := congrArg (fun u => (u.1.1 : G)) heq
      simpa using h1
    have hyval : (y.1 : G) = (y'.1 : G) := by
      have h1 := congrArg (fun u => (u.2.1 : G)) heq
      simpa using h1
    have hx1 : (x.1.1 : G) ≠ 1 := fun h1 => x.2 (Subtype.ext h1)
    have hω : ω = ω' := Dd.inj ω ω' (x.1.1) x.1.2 (by rw [hxval]; exact x'.1.2) hx1
    subst hω
    have hx' : x = x' := Subtype.ext (Subtype.ext hxval)
    have hy' : y = y' := Subtype.ext hyval
    rw [hx', hy']
  -- the cardinality of the domain
  have hconst : ∀ ω : G ⧸ H, Nat.card ({x : ↥(Qomega H Q ω) // x ≠ 1} × ↥(Qomega H Q ω))
      = (Nat.card Q - 1) * Nat.card Q := by
    intro ω
    rw [Nat.card_prod, natCard_subtype_ne, Dd.card]
  have hcard : Nat.card (Sigma (fun ω : G ⧸ H =>
        {x : ↥(Qomega H Q ω) // x ≠ 1} × ↥(Qomega H Q ω)))
      = (Nat.card Q + 1) * (Nat.card Q - 1) * Nat.card Q := by
    rw [Nat.card_sigma]
    simp only [hconst]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcardΩ]
    push_cast
    ring
  rw [← hcard]
  exact hle

/-! ### The non-`2`-element part of the centraliser sum -/

/-- An involution has square `1`. -/
lemma sq_eq_one_of_orderOf_eq_two {G : Type} [Group G] {u : G} (hu : orderOf u = 2) :
    u * u = 1 := by
  have h := pow_orderOf_eq_one u
  rwa [hu, pow_two] at h

/-- **Inverting involutions inject into the centraliser.**  For a fixed inverting involution
`u₀` of `g`, the map `u ↦ u * u₀` is injective into `C_G(g)`; if no inverting involution
exists the left hand side is `0`. -/
lemma ncard_inverting_le_card_centralizer {G : Type} [Group G] [Finite G] (g : G) :
    Nat.card {u : G // orderOf u = 2 ∧ u * g * u = g⁻¹} ≤
      Nat.card (Subgroup.centralizer ({g} : Set G)) := by
  classical
  by_cases h : ∃ u₀ : G, orderOf u₀ = 2 ∧ u₀ * g * u₀ = g⁻¹
  · obtain ⟨u₀, hu₀, hu₀g⟩ := h
    have h₀sq : u₀ * u₀ = 1 := sq_eq_one_of_orderOf_eq_two hu₀
    refine Nat.card_le_card_of_injective (fun u => ⟨u.1 * u₀, ?_⟩) ?_
    · rw [Subgroup.mem_centralizer_singleton_iff]
      obtain ⟨hu, hug⟩ := u.2
      have husq : u.1 * u.1 = 1 := sq_eq_one_of_orderOf_eq_two hu
      have h3 : u.1 * g⁻¹ = g * u.1 := by
        calc u.1 * g⁻¹ = u.1 * (u.1 * g * u.1) := by rw [hug]
          _ = (u.1 * u.1) * g * u.1 := by group
          _ = g * u.1 := by rw [husq, one_mul]
      have h4 : u₀ * g = g⁻¹ * u₀ := by
        calc u₀ * g = u₀ * g * (u₀ * u₀) := by rw [h₀sq, mul_one]
          _ = (u₀ * g * u₀) * u₀ := by group
          _ = g⁻¹ * u₀ := by rw [hu₀g]
      calc (u.1 * u₀) * g = u.1 * (u₀ * g) := by group
        _ = u.1 * (g⁻¹ * u₀) := by rw [h4]
        _ = (u.1 * g⁻¹) * u₀ := by group
        _ = (g * u.1) * u₀ := by rw [h3]
        _ = g * (u.1 * u₀) := by group
    · intro u v huv
      exact Subtype.ext (mul_right_cancel (congrArg Subtype.val huv))
  · haveI : IsEmpty {u : G // orderOf u = 2 ∧ u * g * u = g⁻¹} :=
      ⟨fun u => h ⟨u.1, u.2⟩⟩
    haveI : Fintype {u : G // orderOf u = 2 ∧ u * g * u = g⁻¹} := Fintype.ofFinite _
    haveI : Fintype ↥(Subgroup.centralizer ({g} : Set G)) := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_eq_zero]
    exact Nat.zero_le _

/-- Pairs of involutions as a product of the two involution sets. -/
def invPairEquiv (G : Type) [Group G] :
    {q : G × G // orderOf q.1 = 2 ∧ orderOf q.2 = 2} ≃
      {u : G // orderOf u = 2} × {u : G // orderOf u = 2} where
  toFun q := (⟨q.1.1, q.2.1⟩, ⟨q.1.2, q.2.2⟩)
  invFun p := ⟨(p.1.1, p.2.1), p.1.2, p.2.2⟩
  left_inv q := rfl
  right_inv p := rfl

/-- Restriction of a subtype to a sub-predicate. -/
def subSubtypeEquivMem {α : Type} {P : α → Prop} {Q : α → Prop} :
    {a : {x : α // P x} // Q a.1} ≃ {x : α // P x ∧ Q x} where
  toFun a := ⟨a.1.1, a.1.2, a.2⟩
  invFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  left_inv a := rfl
  right_inv x := rfl

/-- Restriction of a subtype to a negated sub-predicate. -/
def subSubtypeEquivNotMem {α : Type} {P : α → Prop} {Q : α → Prop} :
    {a : {x : α // P x} // ¬ Q a.1} ≃ {x : α // P x ∧ ¬ Q x} where
  toFun a := ⟨a.1.1, a.1.2, a.2⟩
  invFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  left_inv a := rfl
  right_inv x := rfl

/-- Reassociation of a triple conjunction inside a subtype. -/
def andAssocEquiv {α : Type} (P Q R : α → Prop) :
    {x : α // (P x ∧ Q x) ∧ R x} ≃ {x : α // P x ∧ Q x ∧ R x} where
  toFun x := ⟨x.1, ⟨x.2.1.1, ⟨x.2.1.2, x.2.2⟩⟩⟩
  invFun x := ⟨x.1, ⟨⟨x.2.1, x.2.2.1⟩, x.2.2.2⟩⟩
  left_inv x := rfl
  right_inv x := rfl

/-- **The number of involution pairs with `2`-element product.**  The pairs of involutions
whose product is a `2`-element all lie in a common conjugate of `Q` (Feit's step
`mem_same_conj`), and each conjugate contains exactly `|D|` involutions, so there are at most
`(|Q| + 1)·|D|²` of them. -/
theorem ncard_invPairs_twoElts_le {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) (hz : Submission.Blueprint.IsZassenhaus H)
    (h2 : IsPGroup 2 Q) (Dd : Work.ZassenhausPSL2.FeitCln.QomegaData H Q t) :
    Nat.card {q : G × G // orderOf q.1 = 2 ∧ orderOf q.2 = 2 ∧ q.1 * q.2 ∈ TwoElts G} ≤
      (Nat.card Q + 1) * Nat.card (Submission.Blueprint.twoPoint H t) *
        Nat.card (Submission.Blueprint.twoPoint H t) := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Fintype (G ⧸ H) := Fintype.ofFinite _
  set d := Nat.card (Submission.Blueprint.twoPoint H t) with hd
  have hcardΩ : Fintype.card (G ⧸ H) = Nat.card Q + 1 := by
    rw [Fintype.card_eq_nat_card, ← Subgroup.index_eq_card]
    exact Work.ThmG.rankOne_index h
  have hcover : ∀ u v : G, orderOf u = 2 → orderOf v = 2 → (∃ n : ℕ, orderOf (u * v) = 2 ^ n) →
      ∃ ω : G ⧸ H, u ∈ Qomega H Q ω ∧ v ∈ Qomega H Q ω := by
    intro u v hu hv huv
    obtain ⟨g, hgu, hgv⟩ := mem_same_conj h h2 hu hv huv
    exact ⟨QuotientGroup.mk g, by rw [← Dd.cover g]; exact hgu,
      by rw [← Dd.cover g]; exact hgv⟩
  have hcardQω : ∀ ω : G ⧸ H, Nat.card {u : G // u ∈ Qomega H Q ω ∧ orderOf u = 2} = d := by
    intro ω
    rw [hd]
    exact (Nat.card_coe_set_eq (Submission.Blueprint.involutions (Qomega H Q ω : Set G))).trans
      (Dd.invcard ω)
  have hle : Nat.card {q : G × G // orderOf q.1 = 2 ∧ orderOf q.2 = 2 ∧ q.1 * q.2 ∈ TwoElts G} ≤
      Nat.card (Sigma (fun ω : G ⧸ H => {u : G // u ∈ Qomega H Q ω ∧ orderOf u = 2} ×
        {u : G // u ∈ Qomega H Q ω ∧ orderOf u = 2})) := by
    refine Nat.card_le_card_of_injective (fun q =>
      ⟨(Classical.choose (hcover q.1.1 q.1.2 q.2.1 q.2.2.1 q.2.2.2)),
        ⟨q.1.1, (Classical.choose_spec (hcover q.1.1 q.1.2 q.2.1 q.2.2.1 q.2.2.2)).1, q.2.1⟩,
        ⟨q.1.2, (Classical.choose_spec (hcover q.1.1 q.1.2 q.2.1 q.2.2.1 q.2.2.2)).2, q.2.2.1⟩⟩) ?_
    intro q q' hq
    have h1 : q.1.1 = q'.1.1 := by
      have := congrArg (fun z => z.2.1.1) hq
      simpa using this
    have h2 : q.1.2 = q'.1.2 := by
      have := congrArg (fun z => z.2.2.1) hq
      simpa using this
    exact Subtype.ext (Prod.ext h1 h2)
  calc Nat.card {q : G × G // orderOf q.1 = 2 ∧ orderOf q.2 = 2 ∧ q.1 * q.2 ∈ TwoElts G}
      ≤ Nat.card (Sigma (fun ω : G ⧸ H => {u : G // u ∈ Qomega H Q ω ∧ orderOf u = 2} ×
          {u : G // u ∈ Qomega H Q ω ∧ orderOf u = 2})) := hle
    _ = ∑ ω : G ⧸ H, Nat.card ({u : G // u ∈ Qomega H Q ω ∧ orderOf u = 2} ×
          {u : G // u ∈ Qomega H Q ω ∧ orderOf u = 2}) := Nat.card_sigma
    _ = ∑ _ω : G ⧸ H, d * d := by
        refine Finset.sum_congr rfl (fun ω _ => ?_)
        rw [Nat.card_prod, hcardQω ω]
    _ = (Nat.card Q + 1) * d * d := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcardΩ]
        push_cast
        ring
    _ = (Nat.card Q + 1) * Nat.card (Submission.Blueprint.twoPoint H t) *
          Nat.card (Submission.Blueprint.twoPoint H t) := by rw [hd]

/-- **The non-`2`-element part of the centraliser sum.**  Pairs of involutions with product
outside the `2`-elements inject into the sum of the centralisers of the non-`2`-elements. -/
theorem sum_centralizer_compl_ge {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) (hz : Submission.Blueprint.IsZassenhaus H)
    (h2 : IsPGroup 2 Q) (Dd : Work.ZassenhausPSL2.FeitCln.QomegaData H Q t) :
    (Nat.card Q + 1) * Nat.card Q * Nat.card (Submission.Blueprint.twoPoint H t) *
        Nat.card (Submission.Blueprint.twoPoint H t) ≤
      Nat.card (Sigma (fun g : {g : G // g ∉ Work.ZassenhausPSL2.FeitCln.TwoElts G} =>
        Subgroup.centralizer ({g.1} : Set G))) := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Fintype (G ⧸ H) := Fintype.ofFinite _
  haveI : Fintype {g : G // g ∉ TwoElts G} := Fintype.ofFinite _
  set d := Nat.card (Submission.Blueprint.twoPoint H t) with hd
  have hInv : Nat.card {u : G // orderOf u = 2} = (Nat.card Q + 1) * d := by
    rw [hd]
    exact (Nat.card_coe_set_eq {g : G | orderOf g = 2}).trans (ncard_involutions_G h hz h2)
  have hAll : Nat.card {q : G × G // orderOf q.1 = 2 ∧ orderOf q.2 = 2} =
      ((Nat.card Q + 1) * d) * ((Nat.card Q + 1) * d) := by
    rw [Nat.card_congr (invPairEquiv G), Nat.card_prod, hInv]
  have hsplitAll : Nat.card {q : G × G // orderOf q.1 = 2 ∧ orderOf q.2 = 2} =
      Nat.card {q : G × G // orderOf q.1 = 2 ∧ orderOf q.2 = 2 ∧ q.1 * q.2 ∈ TwoElts G} +
      Nat.card {q : G × G // orderOf q.1 = 2 ∧ orderOf q.2 = 2 ∧ q.1 * q.2 ∉ TwoElts G} := by
    have hsum : Nat.card ({a : {q : G × G // orderOf q.1 = 2 ∧ orderOf q.2 = 2} //
          a.1.1 * a.1.2 ∈ TwoElts G} ⊕
        {a : {q : G × G // orderOf q.1 = 2 ∧ orderOf q.2 = 2} //
          ¬(a.1.1 * a.1.2 ∈ TwoElts G)}) =
        Nat.card {q : G × G // orderOf q.1 = 2 ∧ orderOf q.2 = 2} :=
      Nat.card_congr (Equiv.sumCompl (fun a : {q : G × G // orderOf q.1 = 2 ∧ orderOf q.2 = 2} =>
        a.1.1 * a.1.2 ∈ TwoElts G))
    have e1 : {a : {q : G × G // orderOf q.1 = 2 ∧ orderOf q.2 = 2} //
          a.1.1 * a.1.2 ∈ TwoElts G} ≃
        {q : G × G // orderOf q.1 = 2 ∧ orderOf q.2 = 2 ∧ q.1 * q.2 ∈ TwoElts G} :=
      (subSubtypeEquivMem (P := fun q : G × G => orderOf q.1 = 2 ∧ orderOf q.2 = 2)
        (Q := fun q : G × G => q.1 * q.2 ∈ TwoElts G)).trans
        (andAssocEquiv (fun q : G × G => orderOf q.1 = 2) (fun q : G × G => orderOf q.2 = 2)
          (fun q : G × G => q.1 * q.2 ∈ TwoElts G))
    have e2 : {a : {q : G × G // orderOf q.1 = 2 ∧ orderOf q.2 = 2} //
          ¬ a.1.1 * a.1.2 ∈ TwoElts G} ≃
        {q : G × G // orderOf q.1 = 2 ∧ orderOf q.2 = 2 ∧ q.1 * q.2 ∉ TwoElts G} :=
      (subSubtypeEquivNotMem (P := fun q : G × G => orderOf q.1 = 2 ∧ orderOf q.2 = 2)
        (Q := fun q : G × G => q.1 * q.2 ∈ TwoElts G)).trans
        (andAssocEquiv (fun q : G × G => orderOf q.1 = 2) (fun q : G × G => orderOf q.2 = 2)
          (fun q : G × G => q.1 * q.2 ∉ TwoElts G))
    rw [← hsum, Nat.card_sum, Nat.card_congr e1, Nat.card_congr e2]
  have hNsum : ((Nat.card Q + 1) * d) * ((Nat.card Q + 1) * d) =
      Nat.card {q : G × G // orderOf q.1 = 2 ∧ orderOf q.2 = 2 ∧ q.1 * q.2 ∈ TwoElts G} +
      Nat.card {q : G × G // orderOf q.1 = 2 ∧ orderOf q.2 = 2 ∧ q.1 * q.2 ∉ TwoElts G} := by
    rw [← hAll, hsplitAll]
  have hN : Nat.card {q : G × G // orderOf q.1 = 2 ∧ orderOf q.2 = 2 ∧ q.1 * q.2 ∈ TwoElts G} ≤
      (Nat.card Q + 1) * d * d := by
    rw [hd]
    exact ncard_invPairs_twoElts_le h hz h2 Dd
  have harith : ((Nat.card Q + 1) * d) * ((Nat.card Q + 1) * d) - (Nat.card Q + 1) * d * d
      = (Nat.card Q + 1) * Nat.card Q * d * d := by
    have h1 : (Nat.card Q + 1) * d - d = Nat.card Q * d := by
      rw [Nat.succ_mul]
      exact Nat.add_sub_cancel _ _
    calc ((Nat.card Q + 1) * d) * ((Nat.card Q + 1) * d) - (Nat.card Q + 1) * d * d
        = (Nat.card Q + 1) * d * (((Nat.card Q + 1) * d) - d) :=
          (Nat.mul_sub_left_distrib _ _ _).symm
      _ = (Nat.card Q + 1) * d * (Nat.card Q * d) := by rw [h1]
      _ = (Nat.card Q + 1) * Nat.card Q * d * d := by ring
  have hQ' : (Nat.card Q + 1) * Nat.card Q * d * d ≤
      Nat.card {q : G × G // orderOf q.1 = 2 ∧ orderOf q.2 = 2 ∧ q.1 * q.2 ∉ TwoElts G} := by
    have h1 : Nat.card {q : G × G // orderOf q.1 = 2 ∧ orderOf q.2 = 2 ∧ q.1 * q.2 ∉ TwoElts G} =
        ((Nat.card Q + 1) * d) * ((Nat.card Q + 1) * d) -
          Nat.card {q : G × G // orderOf q.1 = 2 ∧ orderOf q.2 = 2 ∧ q.1 * q.2 ∈ TwoElts G} := by
      rw [hNsum]
      exact (Nat.add_sub_cancel_left _ _).symm
    rw [h1, ← harith]
    exact Nat.sub_le_sub_left hN _
  have hinj : Nat.card {q : G × G // orderOf q.1 = 2 ∧ orderOf q.2 = 2 ∧ q.1 * q.2 ∉ TwoElts G} ≤
      Nat.card (Sigma (fun g : {g : G // g ∉ TwoElts G} =>
        {u : G // orderOf u = 2 ∧ u * g.1 * u = g.1⁻¹})) := by
    refine Nat.card_le_card_of_injective (fun q =>
      ⟨⟨q.1.1 * q.1.2, q.2.2.2⟩, ⟨q.1.2, q.2.2.1, ?_⟩⟩) ?_
    · have h1 : q.1.1 * q.1.1 = 1 := sq_eq_one_of_orderOf_eq_two q.2.1
      have h2 : q.1.2 * q.1.2 = 1 := sq_eq_one_of_orderOf_eq_two q.2.2.1
      have i1 : q.1.1⁻¹ = q.1.1 := inv_eq_of_mul_eq_one_right h1
      have i2 : q.1.2⁻¹ = q.1.2 := inv_eq_of_mul_eq_one_right h2
      calc q.1.2 * (q.1.1 * q.1.2) * q.1.2 = q.1.2 * q.1.1 := by
            calc q.1.2 * (q.1.1 * q.1.2) * q.1.2
                = (q.1.2 * q.1.1) * (q.1.2 * q.1.2) := by group
              _ = q.1.2 * q.1.1 := by rw [h2, mul_one]
        _ = (q.1.1 * q.1.2)⁻¹ := by rw [mul_inv_rev, i1, i2]
    · intro q q' hq
      have h1 : q.1.1 * q.1.2 = q'.1.1 * q'.1.2 := by
        have := congrArg (fun z => z.1.1) hq
        simpa using this
      have h2 : q.1.2 = q'.1.2 := by
        have := congrArg (fun z => z.2.1) hq
        simpa using this
      have h3 : q.1.1 = q'.1.1 := by
        have h4 : (q.1.1 * q.1.2) * q.1.2 = (q'.1.1 * q'.1.2) * q'.1.2 := by rw [h1, h2]
        have h5 : (q.1.1 * q.1.2) * q.1.2 = q.1.1 := by
          rw [mul_assoc, sq_eq_one_of_orderOf_eq_two q.2.2.1, mul_one]
        have h6 : (q'.1.1 * q'.1.2) * q'.1.2 = q'.1.1 := by
          rw [mul_assoc, sq_eq_one_of_orderOf_eq_two q'.2.2.1, mul_one]
        rw [h5, h6] at h4
        exact h4
      exact Subtype.ext (Prod.ext h3 h2)
  have hsum_le : Nat.card (Sigma (fun g : {g : G // g ∉ TwoElts G} =>
        {u : G // orderOf u = 2 ∧ u * g.1 * u = g.1⁻¹})) ≤
      Nat.card (Sigma (fun g : {g : G // g ∉ TwoElts G} =>
        Subgroup.centralizer ({g.1} : Set G))) := by
    rw [Nat.card_sigma, Nat.card_sigma]
    refine Finset.sum_le_sum (fun g _ => ?_)
    exact ncard_inverting_le_card_centralizer (g.1)
  calc (Nat.card Q + 1) * Nat.card Q * d * d
      ≤ Nat.card {q : G × G // orderOf q.1 = 2 ∧ orderOf q.2 = 2 ∧ q.1 * q.2 ∉ TwoElts G} := hQ'
    _ ≤ Nat.card (Sigma (fun g : {g : G // g ∉ TwoElts G} =>
          {u : G // orderOf u = 2 ∧ u * g.1 * u = g.1⁻¹})) := hinj
    _ ≤ Nat.card (Sigma (fun g : {g : G // g ∉ TwoElts G} =>
          Subgroup.centralizer ({g.1} : Set G))) := hsum_le

end Intern

/-- **Assembly of Feit's class count.**  Given the class-count identity, the split of the
centraliser sum into the identity, the nontrivial `2`-elements and the rest, and the two
partial lower bounds, the class count follows by pure arithmetic. -/
theorem card_conjClasses_ge_of_inputs {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t)
    (hclass : Nat.card (ConjClasses G) * Nat.card G =
      Nat.card (Sigma (fun g : G => Subgroup.centralizer ({g} : Set G))))
    (hsplit : Nat.card (Sigma (fun g : G => Subgroup.centralizer ({g} : Set G))) =
      Nat.card G +
        Nat.card (Sigma (fun x : {x : G // x ∈ TwoElts G ∧ x ≠ 1} =>
          Subgroup.centralizer ({x.1} : Set G))) +
        Nat.card (Sigma (fun g : {g : G // g ∉ TwoElts G} =>
          Subgroup.centralizer ({g.1} : Set G))))
    (htwo : (Nat.card Q + 1) * (Nat.card Q - 1) * Nat.card Q ≤
      Nat.card (Sigma (fun x : {x : G // x ∈ TwoElts G ∧ x ≠ 1} =>
        Subgroup.centralizer ({x.1} : Set G))))
    (hrest : (Nat.card Q + 1) * Nat.card Q * Nat.card (Submission.Blueprint.twoPoint H t) *
        Nat.card (Submission.Blueprint.twoPoint H t) ≤
      Nat.card (Sigma (fun g : {g : G // g ∉ TwoElts G} =>
        Subgroup.centralizer ({g.1} : Set G)))) :
    Nat.card (ConjClasses G) * Nat.card (Submission.Blueprint.twoPoint H t) ≥
      Nat.card (Submission.Blueprint.twoPoint H t) + (Nat.card Q - 1) +
        Nat.card (Submission.Blueprint.twoPoint H t) *
          Nat.card (Submission.Blueprint.twoPoint H t) := by
  have hcardG : Nat.card G =
      (Nat.card Q + 1) * Nat.card Q * Nat.card (Submission.Blueprint.twoPoint H t) :=
    card_G_eq h
  have hmain : Nat.card (ConjClasses G) * Nat.card G ≥
      Nat.card G + (Nat.card Q + 1) * (Nat.card Q - 1) * Nat.card Q +
        (Nat.card Q + 1) * Nat.card Q * Nat.card (Submission.Blueprint.twoPoint H t) *
          Nat.card (Submission.Blueprint.twoPoint H t) := by
    rw [hclass, hsplit]
    gcongr
  have hM : 0 < (Nat.card Q + 1) * Nat.card Q :=
    Nat.mul_pos (Nat.succ_pos _) Nat.card_pos
  refine Nat.le_of_mul_le_mul_left ?_ hM
  calc (Nat.card Q + 1) * Nat.card Q *
        (Nat.card (Submission.Blueprint.twoPoint H t) + (Nat.card Q - 1) +
          Nat.card (Submission.Blueprint.twoPoint H t) *
            Nat.card (Submission.Blueprint.twoPoint H t))
      = Nat.card G + (Nat.card Q + 1) * (Nat.card Q - 1) * Nat.card Q +
          (Nat.card Q + 1) * Nat.card Q * Nat.card (Submission.Blueprint.twoPoint H t) *
            Nat.card (Submission.Blueprint.twoPoint H t) := by
        rw [hcardG]; ring
    _ ≤ Nat.card (ConjClasses G) * Nat.card G := hmain
    _ = (Nat.card Q + 1) * Nat.card Q *
          (Nat.card (ConjClasses G) * Nat.card (Submission.Blueprint.twoPoint H t)) := by
        rw [hcardG]; ring

theorem card_conjClasses_ge {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) (hz : Submission.Blueprint.IsZassenhaus H)
    (h2 : IsPGroup 2 Q) (hab : Submission.Blueprint.IsAbelianSubgroup Q) :
    Nat.card (ConjClasses G) * Nat.card (Submission.Blueprint.twoPoint H t) ≥
      Nat.card (Submission.Blueprint.twoPoint H t) + (Nat.card Q - 1) +
        Nat.card (Submission.Blueprint.twoPoint H t) * Nat.card (Submission.Blueprint.twoPoint H t) := by
  obtain ⟨Dd⟩ := Intern.qomegaData_nonempty h hz h2 hab
  exact card_conjClasses_ge_of_inputs h
    (Intern.card_conjClasses_mul_card_eq_sigma (G := G))
    (Intern.natCard_cent_eq_split (G := G))
    (Intern.sum_centralizer_twoElts_ge h Dd)
    (Intern.sum_centralizer_compl_ge h hz h2 Dd)

end Work.ZassenhausPSL2.FeitCln
