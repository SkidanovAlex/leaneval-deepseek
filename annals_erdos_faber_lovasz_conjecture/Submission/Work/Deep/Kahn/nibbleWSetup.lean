import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Kahn.NibbleRoundDefs
import Submission.Work.Deep.Kahn.RoundDefs
import Submission.Work.Deep.Kahn.nibbleSetup

/-!
# The one-round nibble, second generation: the *wasteful* procedure

This module fixes the vocabulary of the one-round step in the form actually proved in
Kang--Kelly--Kühn--Methuku--Osthus, *A special case of Vũ's conjecture* (arXiv:2109.11438),
Lemma `lemma:nibble` and Section `section:nibble`.

The random procedure (paper, proof of Lemma `lemma:nibble`) activates each edge with
probability `p = 1/K` and gives each edge a uniform colour from its list.  Then

* `X = keptSub ω` — the *kept* edges (activated, and no other activated edge meeting them
  carries the same colour) — are coloured by `keptColoring ω` and removed;
* the new list of a remaining edge `e` is `residual ω e = L e \ lost ω e`, where
  `lost ω e` is the set of colours of **activated** edges meeting `e` (the *wasteful*
  procedure of Reed--Sudakov: a colour is dropped as soon as an activated neighbour of `e`
  names it, even if that neighbour is not itself kept).

This is the procedure for which the paper's constants are calibrated:

* `newLambda Λ C D K = Λ (1 - p/Λ)^{CD}` — the expected number of colours left in a list;
* `newDeg Λ C D K = D ((1-p) (1-p/Λ)^{D(C-1)} + p (1 - (1-p/Λ)^{CD}))` — an upper bound on the
  expected colour degree.

## The colour-degree statistic

The colour degree of the pair `(x,γ)` in the new instance is

`#{e ∋ x : ¬ kept ω e, γ ∈ residual ω e}`

and the paper bounds it by the sum of the two random variables (`eqn:degree-overcount`)

* `uncolActCount ω x γ = #{e ∋ x : γ ∈ L e, e activated, ¬ kept ω e}` — the *activated but
  blocked* edges (paper: `uncolActivatedNbrsRV`), whose expectation is
  `p (1 - (1-p/Λ)^{C(D-1)}) D ≤ p (1 - retention) D`;
* `keptUnactCount ω x γ = #{e ∋ x : γ ∈ L e, e *not* activated, and no activated `γ`-edge
  through a vertex of `e` other than `x` meets `e`}` — the *unactivated survivors* (paper:
  `keptUnactColsRV`), whose expectation is `(1-p) (1-p/Λ)^{D(C-1)} D = (1-p) retentionU D`.

Their expectation bounds add up exactly to `newDeg`.  The two are each concentrated (paper,
Lemma `lemma:concentrations`), which is why one splits the count at all: the count itself is
*bimodal* (a single activated `γ`-edge through `x` kills `γ` at all `D` edges of `E(x,γ)`).

## Difference from the first generation

`nibbleSetup` used `Round.usedColours` (the colours of the *kept* edges meeting `e`) as the
new list, i.e. `L' e = L e \ usedColours ω e`.  That construction is *wrong* for the
statement's constants: it keeps too many colours, and the colour-degree estimate then exceeds
`newDeg + ηD` in the regime `C² ≳ K` (e.g. the affine-space instance `AG(k,q)` with equal
lists).  The wasteful procedure drops them too, which is what `newDeg` is calibrated for.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open scoped BigOperators
open Finset

namespace Work.Deep.Kahn

open ErdosFaberLovaszConjecture

noncomputable section

namespace Round

variable {n c : ℕ} {K : ℕ} {𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)}
  {L : 𝓗 → Finset (Fin c)}

/-- The number of *activated* `γ`-edges through `x` that are **not** kept: the "activated but
blocked" contribution to the colour degree of `(x,γ)` after the round (paper:
`uncolActivatedNbrsRV`). -/
def uncolActCount [Fintype 𝓗] [NeZero K] (ω : Space K 𝓗 L) (x : Fin n) (γ : Fin c) : ℕ := by
  classical
  exact (Finset.univ.filter (fun e : 𝓗 => active ω e ∧ ¬ kept ω e ∧
    x ∈ (e : Set (Fin n)) ∧ γ ∈ L e)).card

/-- The number of *unactivated* `γ`-edges through `x` that are not met by any activated
`γ`-edge not through `x`: the "unactivated survivor" contribution to the colour degree of
`(x,γ)` (paper: `keptUnactColsRV`). -/
def keptUnactCount [Fintype 𝓗] [NeZero K] (ω : Space K 𝓗 L) (x : Fin n) (γ : Fin c) : ℕ := by
  classical
  exact (Finset.univ.filter (fun e : 𝓗 => ¬ active ω e ∧ x ∈ (e : Set (Fin n)) ∧ γ ∈ L e ∧
    ∀ f : 𝓗, active ω f → x ∉ (f : Set (Fin n)) → colour ω f = γ →
      ¬ ((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty)).card

/-- The colour degree of the pair `(x,γ)` in the new instance: the number of uncoloured edges
`e ∋ x` whose residual list `L e \ lost ω e` still contains `γ`. -/
def newColDeg [Fintype 𝓗] [NeZero K] (ω : Space K 𝓗 L) (x : Fin n) (γ : Fin c) : ℕ := by
  classical
  exact (Finset.univ.filter (fun e : 𝓗 => ¬ kept ω e ∧ x ∈ (e : Set (Fin n)) ∧
    γ ∈ residual ω e)).card

/-- **The overcount of the colour degree.**  The number of uncoloured `γ`-edges through `x`
that keep `γ` is at most the number of activated-but-blocked such edges plus the number of
unactivated-and-unblocked such edges (paper, `eqn:degree-overcount`). -/
theorem newColDeg_le [Fintype 𝓗] [NeZero K] (ω : Space K 𝓗 L) (x : Fin n) (γ : Fin c) :
    newColDeg ω x γ ≤ uncolActCount ω x γ + keptUnactCount ω x γ := by
  classical
  have hsub :
      (Finset.univ.filter (fun e : 𝓗 => ¬ kept ω e ∧ x ∈ (e : Set (Fin n)) ∧
          γ ∈ residual ω e))
        ⊆ (Finset.univ.filter (fun e : 𝓗 => active ω e ∧ ¬ kept ω e ∧
              x ∈ (e : Set (Fin n)) ∧ γ ∈ L e))
          ∪ (Finset.univ.filter (fun e : 𝓗 => ¬ active ω e ∧ x ∈ (e : Set (Fin n)) ∧
                γ ∈ L e ∧ ∀ f : 𝓗, active ω f → x ∉ (f : Set (Fin n)) → colour ω f = γ →
                  ¬ ((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty)) := by
    intro e he
    rw [Finset.mem_filter] at he
    obtain ⟨-, hk, hxe, hres⟩ := he
    rw [mem_residual] at hres
    obtain ⟨hγL, hno⟩ := hres
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    by_cases ha : active ω e
    · exact Or.inl ⟨Finset.mem_univ _, ha, hk, hxe, hγL⟩
    · exact Or.inr ⟨Finset.mem_univ _, ha, hxe, hγL,
        fun f hf hx hc hint => hno f hf hc hint⟩
  calc newColDeg ω x γ
      = (Finset.univ.filter (fun e : 𝓗 => ¬ kept ω e ∧ x ∈ (e : Set (Fin n)) ∧
          γ ∈ residual ω e)).card := rfl
    _ ≤ ((Finset.univ.filter (fun e : 𝓗 => active ω e ∧ ¬ kept ω e ∧
              x ∈ (e : Set (Fin n)) ∧ γ ∈ L e)).card
          + (Finset.univ.filter (fun e : 𝓗 => ¬ active ω e ∧ x ∈ (e : Set (Fin n)) ∧
                γ ∈ L e ∧ ∀ f : 𝓗, active ω f → x ∉ (f : Set (Fin n)) → colour ω f = γ →
                  ¬ ((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty)).card) :=
        le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
    _ = uncolActCount ω x γ + keptUnactCount ω x γ := rfl

/-! ## The bad events of the Lovász local lemma -/

/-- The bad list event at `e`: `e` loses more than `Λ(1-retention) + ηΛ` colours in the
round, i.e. its residual list is too short. -/
def badListSet [Fintype 𝓗] [NeZero K] (C D Λ : ℕ) (η : ℝ) (e : 𝓗) : Set (Space K 𝓗 L) :=
  {ω | (Λ : ℝ) * (1 - retention Λ C D K) + η * (Λ : ℝ) < ((lost ω e).card : ℝ)}

/-- The bad event at `(x,γ)` for the *activated* part of the colour degree. -/
def badUncolSet [Fintype 𝓗] [NeZero K] (C D Λ : ℕ) (η : ℝ) (x : Fin n) (γ : Fin c) :
    Set (Space K 𝓗 L) :=
  {ω | (1 / (K : ℝ)) * (1 - retention Λ C D K) * (D : ℝ) + η * (D : ℝ) / 4
        < (uncolActCount ω x γ : ℝ)}

/-- The bad event at `(x,γ)` for the *unactivated* part of the colour degree. -/
def badKeptSet [Fintype 𝓗] [NeZero K] (C D Λ : ℕ) (η : ℝ) (x : Fin n) (γ : Fin c) :
    Set (Space K 𝓗 L) :=
  {ω | (1 - 1 / (K : ℝ)) * retentionU Λ C D K * (D : ℝ) + η * (D : ℝ) / 4
        < (keptUnactCount ω x γ : ℝ)}

/-- The bad event at `(x,γ)` for the colour degree itself. -/
def badDegSet [Fintype 𝓗] [NeZero K] (C D Λ : ℕ) (η : ℝ) (x : Fin n) (γ : Fin c) :
    Set (Space K 𝓗 L) :=
  {ω | newDeg Λ C D K + η * (D : ℝ) < (newColDeg ω x γ : ℝ)}

/-- **The colour-degree bad event is contained in the union of the two partial bad events.**
Immediate from the overcount `newColDeg ≤ uncolActCount + keptUnactCount` and the identity
`newDeg = D ((1-1/K) retentionU + (1/K)(1-retention))`. -/
theorem badDegSet_subset [Fintype 𝓗] [NeZero K] (C D Λ : ℕ) (η : ℝ) (hη : 0 ≤ η)
    (x : Fin n) (γ : Fin c) :
    badDegSet (K := K) (L := L) C D Λ η x γ ⊆
      badUncolSet (K := K) (L := L) C D Λ η x γ ∪
        badKeptSet (K := K) (L := L) C D Λ η x γ := by
  classical
  intro ω hω
  by_contra hmem
  rw [Set.mem_union, not_or] at hmem
  obtain ⟨h1, h2⟩ := hmem
  rw [badUncolSet, Set.mem_ofPred_eq, not_lt] at h1
  rw [badKeptSet, Set.mem_ofPred_eq, not_lt] at h2
  rw [badDegSet, Set.mem_ofPred_eq] at hω
  have hover := newColDeg_le (K := K) (L := L) ω x γ
  have hcast : ((newColDeg ω x γ : ℕ) : ℝ)
      ≤ ((uncolActCount ω x γ : ℕ) : ℝ) + ((keptUnactCount ω x γ : ℕ) : ℝ) := by
    exact_mod_cast hover
  have hnewL : newDeg Λ C D K = (1 / (K : ℝ)) * (1 - retention Λ C D K) * (D : ℝ)
      + (1 - 1 / (K : ℝ)) * retentionU Λ C D K * (D : ℝ) := by
    rw [newDeg]; ring
  have hsum : ((uncolActCount ω x γ : ℕ) : ℝ) + ((keptUnactCount ω x γ : ℕ) : ℝ)
      ≤ newDeg Λ C D K + η * (D : ℝ) / 4 + η * (D : ℝ) / 4 := by
    rw [hnewL]; linarith
  have hDnn : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg D
  nlinarith [hω, hcast, hsum, hη, hDnn]

/-- The probability form of `badDegSet_subset`. -/
theorem prob_badDegSet_le [Fintype 𝓗] [NeZero K] (C D Λ : ℕ) (η : ℝ) (hη : 0 ≤ η)
    (x : Fin n) (γ : Fin c) :
    Work.Deep.Conc.prob (badDegSet (K := K) (L := L) C D Λ η x γ)
      ≤ Work.Deep.Conc.prob (badUncolSet (K := K) (L := L) C D Λ η x γ)
        + Work.Deep.Conc.prob (badKeptSet (K := K) (L := L) C D Λ η x γ) :=
  le_trans (Work.Deep.Conc.prob_mono (badDegSet_subset C D Λ η hη x γ))
    (Work.Deep.Conc.prob_union_le _ _)

end Round

end

end Work.Deep.Kahn
