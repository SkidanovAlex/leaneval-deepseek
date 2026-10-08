import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.ThmF.Setup
import Submission.Work.ThmF.ChV12.Basic
import Submission.Work.ThmF.ChV12.L5Struct
import Submission.Work.ThmF.ChV12.X5RankOneAux
import Submission.Work.ThmF.ChV12.Lemma5Defs
import Submission.Work.RankOneUniqueness.Basic
import Submission.Work.RankOneUniqueness.closure_Q_t_eq_top

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Case a) of Peterfalvi II Ch. VI §1: `Q = Q₀ ⟹ V = C_D(t) = 1`

Peterfalvi, *Le théorème de Bender–Suzuki II*, Ch. VI §1 (the Proposition, case a)) and §3
(the "Réduction", p. 264).

In case a) the unipotent part `Q` of the split rank-one datum `H = Q ⋊ D` collapses to the
involution-generated subgroup `Q₀ = ⟨Inv H⟩`, and the "Réduction" shows that the set

`G₀ = (Q₀ · K) ∪ (Q₀ · K · t · Q₀)`,  `K = J(D,t) = Kset H t`,

is a subgroup of `G`.  Since `G₀` contains `Q = Q₀` and `t`, it equals `⟨Q, t⟩ = ⊤` by
simplicity.

The hypothesis `hset` of the statement below is exactly the resulting *set equality*
`X5 H t = Q₀·K ∪ Q₀·K·t·Q₀` (`X5 H t = ⟨Q₀, K, t⟩`); it is the content of the
"Réduction", and it is what this file consumes.

## The counting argument

Everything else is elementary.  With `D = twoPoint H t`, `V = centD H t = C_D(t)`:

1. `X5 H t = ⊤` (simplicity: `X5 ≥ ⟨Q, t⟩ = ⊤`), so `hset` describes *all* of `G`.
2. Hence every `d ∈ D ≤ G` is either `a * k` (`a ∈ Q₀ = Q`, `k ∈ K`) or `a * k * t * a'`
   with `a, k, a' ∈ H`; the second alternative puts `t = (ak)⁻¹ d (a')⁻¹ ∈ H`, absurd.
   Therefore `D ⊆ Q · K`; and since `H = Q · D` (`fact_exists`), also `H ⊆ Q · K`.
3. So the multiplication map `Q × K → H` is surjective: `|H| ≤ |Q| · |K|`.
4. On the other hand `|H| = |Q| · |D|` (`card_H_eq_mul_of_data`) and
   `|D| = |V| · |K|` (Peterfalvi I App. I (1)(b), `card_centD_mul_card_Kset`), so
   `|Q| · |V| · |K| = |H| ≤ |Q| · |K|`; cancelling `|Q| > 0` and `|K| > 0` gives
   `|V| ≤ 1`, i.e. `V = 1`.

This is the FT-free part of the case-a) analysis: neither `ChIIFourProp`, nor Ch. V §1 Prop. 2,
nor the odd-order theorem is used — only the structure of `D ⊆ Q · K` coming from `hset`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.PSU3.StageA

/-- **Case a) of Ch. VI §1 forces `V = C_D(t) = ⊥`.**

If `Q = Q0sub H = ⟨Inv H⟩` and the "Réduction" set equality
`X5 H t = Q₀·K ∪ Q₀·K·t·Q₀` (here the hypothesis `hset`) holds, then `centD H t = ⊥`.

The proof is the counting argument of Peterfalvi's "Réduction" (Ch. VI §3, p. 264): `X5 = ⊤` by
simplicity, so `D ⊆ Q₀ · K`; as `H = Q · D` and `|D| = |V| · |K|`, the surjection
`Q × K → H` forces `|V| ≤ 1`. -/
theorem centD_eq_bot_of_Q_eq_Q0sub {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hs : s ∈ Q) (hs2 : orderOf s = 2) (hst : t * s * t = s * t * s)
    (hQ : (Q : Set G) = Work.ThmF.Q0sub H)
    (hset : (Work.ThmF.Lemma5.X5 H t : Set G) =
        {x : G | (∃ a ∈ (Work.ThmF.Q0sub H : Set G), ∃ k ∈ Work.ThmF.Kset H t, x = a * k) ∨
          (∃ a ∈ (Work.ThmF.Q0sub H : Set G), ∃ k ∈ Work.ThmF.Kset H t,
            ∃ a' ∈ (Work.ThmF.Q0sub H : Set G), x = a * k * t * a')}) :
    Submission.Blueprint.centD H t = ⊥ := by
  classical
  have hsplit : IsSplitRankOne H Q t := hS.split
  have hdata : Work.ThmF.IsSplitRankOneData G H Q t :=
    Work.ThmF.IsSplitRankOne.toData hsplit
  -- ## Step 0: `Q0sub H = Q`, and `X5 H t = ⊤`
  haveI : IsSimpleGroup G := hS.simple
  have hQ' : ∀ a : G, a ∈ (Work.ThmF.Q0sub H : Set G) → a ∈ Q := by
    intro a ha
    exact (Set.ext_iff.mp hQ a).mpr ha
  have hX5 : Work.ThmF.Lemma5.X5 H t = ⊤ := by
    have hle : Subgroup.closure ((Q : Set G) ∪ {t}) ≤ Work.ThmF.Lemma5.X5 H t := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro x (hx | hx)
      · rw [hQ] at hx
        exact Work.ThmF.L5.Q0sub_le_X5 hx
      · rw [Set.mem_singleton_iff] at hx
        rw [hx]
        exact Work.ThmF.Lemma5.t_mem_X5 H t
    rw [Work.RankOneUniqueness.closure_Q_t_eq_top hsplit] at hle
    exact top_le_iff.mp hle
  -- ## Step 1: `D ⊆ Q · Kset`
  have hKleH : ∀ x : G, x ∈ Work.ThmF.Kset H t → x ∈ H :=
    fun x hx => (Subgroup.mem_inf.mp (Work.ThmF.Kset_subset H t hx)).1
  have hDsub : ∀ d ∈ twoPoint H t, ∃ a ∈ Q, ∃ k ∈ Work.ThmF.Kset H t, d = a * k := by
    intro d hd
    have hdX : d ∈ (Work.ThmF.Lemma5.X5 H t : Set G) := by
      rw [hX5]; exact Subgroup.mem_top d
    have hdX' := hdX
    rw [hset] at hdX'
    rcases hdX' with ⟨a, ha, k, hk, hak⟩ | ⟨a, ha, k, hk, a', ha', hak'⟩
    · exact ⟨a, hQ' a ha, k, hk, hak⟩
    · exfalso
      have hkH : k ∈ H := hKleH k hk
      have hdH : d ∈ H := (Subgroup.mem_inf.mp hd).1
      have htH : t ∈ H := by
        have h2 : t = (a * k)⁻¹ * d * a'⁻¹ := by rw [hak']; group
        rw [h2]
        exact H.mul_mem (H.mul_mem (H.inv_mem (H.mul_mem (hsplit.le (hQ' a ha)) hkH)) hdH)
          (H.inv_mem (hsplit.le (hQ' a' ha')))
      exact hsplit.not_mem htH
  -- ## Step 2: `H ⊆ Q · Kset`, via `H = Q · D` and step 1
  have hHsub : ∀ h : G, h ∈ H → ∃ a ∈ Q, ∃ k ∈ Work.ThmF.Kset H t, h = a * k := by
    intro h hh
    obtain ⟨q, hq, d, hd, hqd⟩ := Work.RankOneUniqueness.fact_exists hsplit hh
    obtain ⟨a, ha, k, hk, hak⟩ := hDsub d hd
    exact ⟨q * a, Q.mul_mem hq ha, k, hk, by rw [hqd, hak]; group⟩
  -- ## Step 3: the multiplication map `Q × K → H` is surjective
  let f : ↥Q × ↥(Work.ThmF.Kset H t) → ↥H :=
    fun p => ⟨(p.1 : G) * (p.2 : G), H.mul_mem (hsplit.le p.1.2) (hKleH p.2 p.2.2)⟩
  have hsurj : Function.Surjective f := by
    intro h
    obtain ⟨a, ha, k, hk, hak⟩ := hHsub (h : G) h.2
    refine ⟨(⟨a, ha⟩, ⟨k, hk⟩), Subtype.ext ?_⟩
    show a * k = (h : G)
    exact hak.symm
  -- ## Step 4: the counting
  have hcardle : Nat.card ↥H ≤ Nat.card ↥Q * Nat.card ↥(Work.ThmF.Kset H t) := by
    have h := Nat.card_le_card_of_surjective f hsurj
    simpa only [Nat.card_prod] using h
  have hHcard : Nat.card ↥H = Nat.card ↥Q * Nat.card ↥(twoPoint H t) :=
    Work.ThmF.card_H_eq_mul_of_data hdata
  have hVDcard : Nat.card ↥(Submission.Blueprint.centD H t) *
      Nat.card ↥(Work.ThmF.Kset H t) = Nat.card ↥(twoPoint H t) := by
    have h := Work.ThmF.card_centD_mul_card_Kset hdata
    rw [← Nat.card_coe_set_eq] at h
    exact h
  have hQpos : 0 < Nat.card ↥Q := by
    haveI : Nonempty ↥Q := ⟨⟨1, Q.one_mem⟩⟩
    exact Nat.card_pos
  have hKpos : 0 < Nat.card ↥(Work.ThmF.Kset H t) := by
    haveI : Nonempty ↥(Work.ThmF.Kset H t) := ⟨⟨1, Work.ThmF.one_mem_Kset H t⟩⟩
    exact Nat.card_pos
  have hmain : Nat.card ↥Q * Nat.card ↥(Submission.Blueprint.centD H t) *
        Nat.card ↥(Work.ThmF.Kset H t)
      ≤ Nat.card ↥Q * Nat.card ↥(Work.ThmF.Kset H t) := by
    calc Nat.card ↥Q * Nat.card ↥(Submission.Blueprint.centD H t) *
            Nat.card ↥(Work.ThmF.Kset H t)
        = Nat.card ↥Q * (Nat.card ↥(Submission.Blueprint.centD H t) *
            Nat.card ↥(Work.ThmF.Kset H t)) := Nat.mul_assoc _ _ _
      _ = Nat.card ↥Q * Nat.card ↥(twoPoint H t) := by rw [hVDcard]
      _ = Nat.card ↥H := hHcard.symm
      _ ≤ Nat.card ↥Q * Nat.card ↥(Work.ThmF.Kset H t) := hcardle
  have hVle : Nat.card ↥(Submission.Blueprint.centD H t) ≤ 1 := by
    have hVK : Nat.card ↥(Submission.Blueprint.centD H t) *
        Nat.card ↥(Work.ThmF.Kset H t) ≤ Nat.card ↥(Work.ThmF.Kset H t) := by
      refine Nat.le_of_mul_le_mul_left ?_ hQpos
      simpa only [Nat.mul_assoc] using hmain
    refine Nat.le_of_mul_le_mul_right ?_ hKpos
    rw [one_mul]
    exact hVK
  -- ## Step 5: `|V| ≤ 1` and `V ≠ ∅` give `V = ⊥`
  have hVpos : 1 ≤ Nat.card ↥(Submission.Blueprint.centD H t) := by
    haveI : Nonempty ↥(Submission.Blueprint.centD H t) :=
      ⟨⟨1, (Submission.Blueprint.centD H t).one_mem⟩⟩
    exact Nat.card_pos
  have hVone : Nat.card ↥(Submission.Blueprint.centD H t) = 1 := le_antisymm hVle hVpos
  haveI : Subsingleton ↥(Submission.Blueprint.centD H t) :=
    (Nat.card_eq_one_iff_unique.mp hVone).1
  rw [Subgroup.eq_bot_iff_forall]
  intro v hv
  have h1 : (⟨v, hv⟩ : ↥(Submission.Blueprint.centD H t)) =
      ⟨1, (Submission.Blueprint.centD H t).one_mem⟩ := Subsingleton.elim _ _
  simpa using congrArg Subtype.val h1

end Work.PSU3.StageA
