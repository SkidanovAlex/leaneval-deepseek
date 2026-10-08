import Mathlib
import Submission.Work.Fitting.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Existence of a chief series for a finite group

A group `G` has a chief series: a maximal chain of normal subgroups
`⊤ = G₀ > G₁ > ⋯ > Gₙ = ⊥` (see `Work.Fitting.ChiefSeries`).  For a finite group this is
constructed by repeatedly taking a maximal proper normal subgroup.

The construction is carried out here by an auxiliary descending chain of normal subgroups
`chiefChain H : ℕ → Subgroup G`, starting at `H` and taking at each step a maximal proper
normal subgroup of the previous term (and fixing `⊥` once it is reached).  Since the group is
finite the chain reaches `⊥` after at most `Nat.card H` steps, and cutting the chain at the
first index where it becomes `⊥` yields the desired chief series.
-/

open Classical

namespace Work.Fitting

variable {G : Type*} [Group G] [Finite G]

/-- `(A, B) ∈ ChiefRel` means that `B` is a maximal proper normal subgroup of `A`:
`B < A` and there is no normal subgroup strictly between them. -/
def ChiefRel : Set (Subgroup G × Subgroup G) :=
  {p | p.1.Normal ∧ p.2.Normal ∧ p.2 < p.1 ∧
    ∀ M : Subgroup G, M.Normal → p.2 ≤ M → M ≤ p.1 → M = p.2 ∨ M = p.1}

/-- A proper subgroup of a finite group has strictly smaller cardinality. -/
private lemma card_lt_card_of_lt {H K : Subgroup G} (h : H < K) :
    Nat.card ↥H < Nat.card ↥K := by
  have hle : H ≤ K := h.le
  have hne : H ≠ K := h.ne
  have hex : ∃ x : G, x ∈ K ∧ x ∉ H := by
    by_contra hc
    push Not at hc
    exact hne (le_antisymm hle fun y hy => hc y hy)
  obtain ⟨x, hxK, hxH⟩ := hex
  haveI : Fintype ↥H := Fintype.ofFinite _
  haveI : Fintype ↥K := Fintype.ofFinite _
  have hinj : Function.Injective (fun y : ↥H => (⟨(y : G), hle y.2⟩ : ↥K)) := by
    intro a b hab
    exact Subtype.ext (congr_arg (fun z : ↥K => (z : G)) hab)
  have hnsurj : ¬ Function.Surjective (fun y : ↥H => (⟨(y : G), hle y.2⟩ : ↥K)) := by
    intro hs
    obtain ⟨y, hy⟩ := hs ⟨x, hxK⟩
    have h2 : (y : G) = x := congr_arg (fun z : ↥K => (z : G)) hy
    exact hxH (by rw [← h2]; exact y.2)
  have := Fintype.card_lt_of_injective_not_surjective _ hinj hnsurj
  rwa [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]

/-- Every nontrivial subgroup of a finite group has a maximal proper normal subgroup. -/
private lemma exists_maximal_normal_below (K : Subgroup G) (hK : K ≠ ⊥) :
    ∃ M : Subgroup G, M.Normal ∧ M < K ∧
      ∀ N : Subgroup G, N.Normal → M ≤ N → N ≤ K → N = M ∨ N = K := by
  let S : Set (Subgroup G) := {M | M.Normal ∧ M < K}
  have hSfin : S.Finite := Set.toFinite S
  have hSne : S.Nonempty := ⟨⊥, by simp [S, bot_lt_iff_ne_bot.mpr hK]⟩
  obtain ⟨M, hMmem, hMmax⟩ := hSfin.exists_maximal hSne
  refine ⟨M, hMmem.1, hMmem.2, fun N hN hMN hNK => ?_⟩
  rcases eq_or_lt_of_le hNK with h | h
  · exact Or.inr h
  · exact Or.inl (le_antisymm (hMmax ⟨hN, h⟩ hMN) hMN)

/-- The descending chain of normal subgroups starting at `H`, each term a maximal proper
normal subgroup of the previous one, stabilising at `⊥`. -/
private noncomputable def chiefChain (H : Subgroup G) : ℕ → Subgroup G :=
  fun k => Nat.rec H (fun _ prev => if h : prev = ⊥ then ⊥
    else Classical.choose (exists_maximal_normal_below prev h)) k

private lemma chiefChain_zero (H : Subgroup G) : chiefChain H 0 = H := rfl

private lemma chiefChain_succ (H : Subgroup G) (k : ℕ) : chiefChain H (k+1) =
    (if h : chiefChain H k = ⊥ then ⊥
     else Classical.choose (exists_maximal_normal_below (chiefChain H k) h)) := rfl

/-- Every term of the chain starting at a normal subgroup is normal. -/
private lemma chiefChain_normal {H : Subgroup G} (hH : H.Normal) :
    ∀ k, (chiefChain H k).Normal
  | 0 => hH
  | (k+1) => by
      rw [chiefChain_succ]
      by_cases h : chiefChain H k = ⊥
      · rw [dif_pos h]; exact Subgroup.normal_bot
      · rw [dif_neg h]
        exact (Classical.choose_spec (exists_maximal_normal_below (chiefChain H k) h)).1

/-- Consecutive terms of the chain are related by `ChiefRel`, as long as the chain has not
already reached `⊥`. -/
private lemma chiefChain_rel {H : Subgroup G} (hH : H.Normal) (k : ℕ)
    (hk : chiefChain H k ≠ ⊥) : (chiefChain H k, chiefChain H (k+1)) ∈ ChiefRel := by
  rw [chiefChain_succ, dif_neg hk]
  obtain ⟨h1, h2, h3⟩ := Classical.choose_spec (exists_maximal_normal_below (chiefChain H k) hk)
  exact ⟨chiefChain_normal hH k, h1, h2, h3⟩

/-- The cardinality of the `k`-th term drops by at least one at each step, so the chain has
cardinality at most `Nat.card H - k` as long as it has not reached `⊥`. -/
private lemma chiefChain_bound {H : Subgroup G} (hH : H.Normal) (k : ℕ)
    (hk : ∀ j < k, chiefChain H j ≠ ⊥) :
    Nat.card ↥(chiefChain H k) + k ≤ Nat.card ↥H := by
  induction k with
  | zero => simp [chiefChain_zero]
  | succ k ih =>
      have hk' : ∀ j < k, chiefChain H j ≠ ⊥ := fun j hj => hk j (Nat.lt_succ_of_lt hj)
      have hkne : chiefChain H k ≠ ⊥ := hk k (Nat.lt_succ_self k)
      have ih' := ih hk'
      have hlt : chiefChain H (k+1) < chiefChain H k := (chiefChain_rel hH k hkne).2.2.1
      have hcardlt : Nat.card ↥(chiefChain H (k+1)) < Nat.card ↥(chiefChain H k) :=
        card_lt_card_of_lt hlt
      omega

/-- The chain reaches `⊥`. -/
private lemma chiefChain_exists_bot {H : Subgroup G} (hH : H.Normal) : ∃ n, chiefChain H n = ⊥ := by
  by_contra h
  push Not at h
  have hbound := chiefChain_bound hH (Nat.card ↥H) (fun j _ => h j)
  haveI : Nonempty ↥(chiefChain H (Nat.card ↥H)) := ⟨⟨1, (chiefChain H _).one_mem⟩⟩
  have hpos : 0 < Nat.card ↥(chiefChain H (Nat.card ↥H)) := Nat.card_pos
  omega

/-- There is a least index at which the chain reaches `⊥`. -/
private lemma chiefChain_min_bot {H : Subgroup G} (hH : H.Normal) :
    ∃ n, chiefChain H n = ⊥ ∧ ∀ j < n, chiefChain H j ≠ ⊥ := by
  obtain ⟨n, hn⟩ := chiefChain_exists_bot hH
  have hp : ∃ j, chiefChain H j = ⊥ := ⟨n, hn⟩
  exact ⟨Nat.find hp, Nat.find_spec hp, fun j hj hc => Nat.find_min hp hj hc⟩

theorem exists_chiefSeries (G : Type*) [Group G] [Finite G] :
    Nonempty (Work.Fitting.ChiefSeries G) := by
  obtain ⟨n, hn, hmin⟩ :=
    chiefChain_min_bot (G := G) (H := (⊤ : Subgroup G)) Subgroup.normal_top
  refine ⟨{ n := n
            G_ := fun i => chiefChain (⊤ : Subgroup G) i.val
            top_eq := ?_
            bot_eq := ?_
            normal := ?_
            lt_prev := ?_
            minimal := ?_ }⟩
  · exact chiefChain_zero (⊤ : Subgroup G)
  · exact hn
  · intro i; exact chiefChain_normal Subgroup.normal_top i.val
  · intro i
    exact (chiefChain_rel Subgroup.normal_top i.val (hmin i.val i.isLt)).2.2.1
  · intro i M hM h1 h2
    exact (chiefChain_rel Subgroup.normal_top i.val (hmin i.val i.isLt)).2.2.2 M hM h1 h2

end Work.Fitting
