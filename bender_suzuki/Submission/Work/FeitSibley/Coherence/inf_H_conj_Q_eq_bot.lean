import Mathlib
import Submission.Work.FeitSibley.Coherence.Vocab
import Submission.Work.FeitSibley.CharQ.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.FeitSibley.Coherence.inf_H_conj_Q_eq_bot`

`H ∩ Qˣ = 1` for the Feit–Sibley data `h : FSData G` and `x ∉ H`.

This sharpens the T.I. property `Q ∩ Qˣ = 1` (`h.Q_TI`) from `Q` to all of `H`.  It is the
geometric input of the Peterfalvi App. XII two-block argument: the conjugates of `Q` meet a
conjugate of the Borel `H` trivially, so the conjugacy classes of `H` supported on `Q ∖ 1` stay
disjoint across the `H`-conjugates of `Q`.

The proof is a Hall-subgroup uniqueness argument.  Since `H = Q ⋊ D` with `(|Q|,|D|) = 1`, the
normal subgroup `Q` is the unique Hall `π`-subgroup of `H` (`π` = the primes of `|Q|`): a
subgroup `K ≤ H` whose order is coprime to `[H : Q] = |D|` must lie in `Q`.  Applying this to
`K = H ⊓ Qˣ`, whose order divides `|Qˣ| = |Q|`, gives `H ⊓ Qˣ ≤ Q`, and then the T.I. property
`Q ⊓ Qˣ = 1` finishes the argument.

The supporting facts are proved here, above the target:

* `le_of_coprime_card_quotient_subgroupOf` — the Hall-uniqueness criterion (pure group theory:
  a subgroup of `H` of order coprime to `|H ⧸ N|` lies in the normal subgroup `N`);
* `card_H_eq_card_Q_mul_card_D` — `|H| = |Q| · |D|`, from the unique decomposition
  `H = Q ⋊ D` (`FSData.mem_H_decomp`, `FSData.mul_eq_of_decomp`);
* `card_quot_H_Q_eq_card_D` — `|H ⧸ Q| = |D|`, from `|H| = |Q| · |D|` and Lagrange.
-/

noncomputable section

open Classical

namespace Work.FeitSibley.Coherence

/-- **Hall uniqueness, quantitative form.**  If `K ≤ H` and `|K|` is coprime to the order of the
quotient of `H` by a normal subgroup `N`, then `K ≤ N`.

Indeed the image of `K` in `H ⧸ N` has order dividing both `|K|` and `|H ⧸ N|`, hence is
trivial. -/
theorem le_of_coprime_card_quotient_subgroupOf {G : Type} [Group G] [Finite G]
    {H N K : Subgroup G} [(N.subgroupOf H).Normal] (hKH : K ≤ H)
    (hcop : Nat.Coprime (Nat.card K) (Nat.card (↥H ⧸ N.subgroupOf H))) : K ≤ N := by
  intro k hk
  have hφ : orderOf ((QuotientGroup.mk' (N.subgroupOf H)) (⟨k, hKH hk⟩ : ↥H)) ∣ Nat.card ↥K := by
    have h1 := orderOf_map_dvd ((QuotientGroup.mk' (N.subgroupOf H)).comp (Subgroup.inclusion hKH))
      (⟨k, hk⟩ : ↥K)
    have h2 := orderOf_dvd_natCard (⟨k, hk⟩ : ↥K)
    exact dvd_trans h1 h2
  have h2 : orderOf ((QuotientGroup.mk' (N.subgroupOf H)) (⟨k, hKH hk⟩ : ↥H))
      ∣ Nat.card (↥H ⧸ N.subgroupOf H) := orderOf_dvd_natCard _
  have h3 : orderOf ((QuotientGroup.mk' (N.subgroupOf H)) (⟨k, hKH hk⟩ : ↥H)) = 1 := by
    have hg := Nat.dvd_gcd hφ h2
    rw [hcop.gcd_eq_one] at hg
    simpa using hg
  have h4 : ((QuotientGroup.mk' (N.subgroupOf H)) (⟨k, hKH hk⟩ : ↥H) :
      ↥H ⧸ N.subgroupOf H) = 1 := orderOf_eq_one_iff.mp h3
  rw [QuotientGroup.mk'_apply] at h4
  have h5 : (⟨k, hKH hk⟩ : ↥H) ∈ N.subgroupOf H := (QuotientGroup.eq_one_iff _).mp h4
  exact (Subgroup.mem_subgroupOf).mp h5

variable {G : Type} [Group G] [Fintype G]

/-- `|H| = |Q| · |D|`: every element of `H` is uniquely `q * d` with `q ∈ Q`, `d ∈ D`. -/
theorem card_H_eq_card_Q_mul_card_D (h : Work.FeitSibley.FSData G) :
    Nat.card h.H = Nat.card h.Q * Nat.card h.D := by
  have hbij : Function.Bijective (fun p : ↥h.Q × ↥h.D =>
      (⟨(p.1 : G) * (p.2 : G), mul_mem (h.Q_le_H p.1.2) (h.D_le_H p.2.2)⟩ : ↥h.H)) := by
    constructor
    · rintro ⟨⟨q, hq⟩, ⟨d, hd⟩⟩ ⟨⟨q', hq'⟩, ⟨d', hd'⟩⟩ heq
      have heq' : (q : G) * d = (q' : G) * d' := Subtype.ext_iff.mp heq
      obtain ⟨h1, h2⟩ := h.mul_eq_of_decomp hq hq' hd hd' heq'
      simp only [Prod.mk.injEq, Subtype.mk.injEq]
      exact ⟨h1, h2⟩
    · intro y
      obtain ⟨q, hq, d, hd, hqd⟩ := h.mem_H_decomp y.2
      exact ⟨(⟨q, hq⟩, ⟨d, hd⟩), Subtype.ext hqd.symm⟩
  have hc := Nat.card_congr (Equiv.ofBijective _ hbij)
  rw [Nat.card_prod] at hc
  exact hc.symm

/-- `|H ⧸ Q| = |D|`: the relative index of `Q` in `H` is `|D|`. -/
theorem card_quot_H_Q_eq_card_D (h : Work.FeitSibley.FSData G) :
    Nat.card (↥h.H ⧸ (h.Q.subgroupOf h.H)) = Nat.card h.D := by
  haveI hQn : (h.Q.subgroupOf h.H).Normal :=
    (Subgroup.normal_subgroupOf_iff h.Q_le_H).mpr (fun q _ hq hk =>
      (Subgroup.mem_normalizer_iff.mp (h.Q_normal_in_H hk) q).mp hq)
  have hindex := Subgroup.index_mul_card (H := h.Q.subgroupOf h.H)
  have hNcard : Nat.card ↥(h.Q.subgroupOf h.H) = Nat.card h.Q :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.Q_le_H).toEquiv
  have hidx : (h.Q.subgroupOf h.H).index = Nat.card (↥h.H ⧸ (h.Q.subgroupOf h.H)) :=
    Subgroup.index_eq_card _
  rw [hidx, hNcard] at hindex
  have hH : Nat.card ↥h.H = Nat.card h.Q * Nat.card h.D := card_H_eq_card_Q_mul_card_D h
  rw [hH, mul_comm] at hindex
  exact Nat.mul_left_cancel (Nat.card_pos (α := ↥h.Q)) hindex

/-- **`H ∩ Qˣ = 1` for `x ∉ H`**, where `Qˣ = Submission.Blueprint.conj x h.Q`. -/
theorem inf_H_conj_Q_eq_bot {G : Type} [Group G] [Fintype G] (h : Work.FeitSibley.FSData G)
    {x : G} (hx : x ∉ h.H) :
    h.H ⊓ Submission.Blueprint.conj x h.Q = ⊥ := by
  set K : Subgroup G := h.H ⊓ Submission.Blueprint.conj x h.Q with hKdef
  have hKle : K ≤ h.H := by rw [hKdef]; exact inf_le_left
  have hKle' : K ≤ Submission.Blueprint.conj x h.Q := by rw [hKdef]; exact inf_le_right
  haveI hQn : (h.Q.subgroupOf h.H).Normal :=
    (Subgroup.normal_subgroupOf_iff h.Q_le_H).mpr (fun q _ hq hk =>
      (Subgroup.mem_normalizer_iff.mp (h.Q_normal_in_H hk) q).mp hq)
  have hcard_conj : Nat.card ↥(Submission.Blueprint.conj x h.Q) = Nat.card h.Q :=
    Subgroup.card_map_of_injective (MulAut.conj x).injective
  -- `|K|` divides `|Qˣ| = |Q|` (Lagrange, inside `Qˣ`)
  have hdvd : Nat.card ↥K ∣ Nat.card h.Q := by
    have h1 : Nat.card ↥(K.subgroupOf (Submission.Blueprint.conj x h.Q))
        ∣ Nat.card ↥(Submission.Blueprint.conj x h.Q) := Subgroup.card_subgroup_dvd_card _
    have h2 : Nat.card ↥(K.subgroupOf (Submission.Blueprint.conj x h.Q)) = Nat.card ↥K :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKle').toEquiv
    rwa [h2, hcard_conj] at h1
  -- `|K|` is coprime to `|H ⧸ Q| = |D|`, so Hall uniqueness forces `K ≤ Q`
  have hcop : Nat.Coprime (Nat.card ↥K) (Nat.card (↥h.H ⧸ (h.Q.subgroupOf h.H))) := by
    rw [card_quot_H_Q_eq_card_D h]
    exact (h.coprime_D_Q.coprime_dvd_right hdvd).symm
  have hle : K ≤ h.Q :=
    le_of_coprime_card_quotient_subgroupOf (H := h.H) (N := h.Q) (K := K) hKle hcop
  rw [hKdef]
  refine le_antisymm ?_ bot_le
  calc h.H ⊓ Submission.Blueprint.conj x h.Q
      ≤ h.Q ⊓ Submission.Blueprint.conj x h.Q := le_inf hle inf_le_right
    _ = ⊥ := h.Q_TI x hx

end Work.FeitSibley.Coherence
