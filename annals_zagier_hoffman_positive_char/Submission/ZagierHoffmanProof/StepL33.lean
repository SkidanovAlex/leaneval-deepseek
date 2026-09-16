import Submission.ZagierHoffmanProof.StepL32
import Submission.ZagierHoffmanProof.StepM2

set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators

/-!
# Step L33: the type-3 Init-growth application at the (2.14) configuration

Prop 3.2's algorithm Step-2 keeps a type-3 output `u = Q.c (inr (inr i))` in play
when `u` is not `k`-admissible and has prefix-`k` sum `= S`; its termination argument
needs `Init(s) ≺ Init(u)` for such outputs — strictly larger initial tuples, bounded
by `q{k}`.  This module proves that comparison at the zeta_214 configuration:

  ★ `type3_Init_gt`: for a type-3 member, `InitLt q s (Q.c (Sum.inr (Sum.inr i)))`
    (i.e. `Init(s)` is lexicographically smaller than `Init(u)`), given the
    `(k−1)`-admissible front `s₁..s_{k−1} ≤ q` (`hsleq`).  The proof instantiates
    `InitLt_of_head_gt` (StepM2) with `u := Q.c p`, `v := s`, `j := j`:
      • `huq` (first `j` entries of the output `≤ q`): below `j−1` they are the
        `s`-entries (`member_prefix_pos`, ≤ q by `hsleq`); at `j−1` it is `s_j+1`
        (`type3_sjadd_one_at`), `≤ q` since `s_j < q` (`hsj`);
      • `hvq` (first `j` entries of `s` `≤ q`): `hsleq` (positions `< j ≤ k−1`);
      • `heq` (fronts agree below `j−1`): `member_prefix_pos`;
      • `hgt` (`s_j < s_j+1` at `j−1`): `type3_sjadd_one_at` + `pad0_of_lt`;
      • depths: `j ≤ r` (`hjk`,`hkr`) and `j ≤ Q.dep p` (`Q_dep_inr_inr`, StepL28).
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- A type-3 member shares the `s`-front below position `j−1`, has value `s_j + 1`
at `j−1`, and is `≤ q` on its first `j` entries (given the `(k−1)`-admissible front
`s₁..s_{k−1} ≤ q` and `s_j < q`):  the two tuple-facts the Init comparison needs. -/
lemma type3_front_eq (r : ℕ) (s : Fin r → ℕ+) (k j : ℕ)
    (hk1 : 1 ≤ k) (hkr : k ≤ r) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F)
    (R0 : BinaryRel F)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1) :
    let D := RelData.BCqIter F (k - j - 1) (toData F R0)
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (k - j - 1) R0 e)
        (RelData.iterate_merge_hv F (k - j - 1) R0 (s ⟨j - 1, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s j (by omega) (by omega))
    ∀ i : D.ιB, ∀ x : ℕ, x < j - 1 →
      pad0 (Q.c (Sum.inr (Sum.inr i))) x = pad0 s x := by
  classical
  intro D Bs Q i x hx
  have hxr : x < r := by
    have : x < j - 1 := hx
    omega
  have hdepQ : j ≤ Q.dep (Sum.inr (Sum.inr i)) :=
    Q_dep_inr_inr F r s k j hk1 hkr hj1 hjk hsj R0 hbhd i
  have hxQ : x < Q.dep (Sum.inr (Sum.inr i)) := by omega
  have hv := member_prefix_pos F r s k j hk1 hkr hj1 hjk hbig hsj R0 hbhd
    (Sum.inr (Sum.inr i)) x hx hxQ
  rw [pad0_of_lt (Q.c (Sum.inr (Sum.inr i))) hxQ]
  rw [pad0_of_lt s hxr]
  exact congrArg (fun t : ℕ+ => (t : ℕ)) hv

/-- A type-3 member's first `j` entries are `≤ q` (front `s`-entries via
`hsleq`, `s_j+1` via `hsj`). -/
lemma type3_front_le (r : ℕ) (s : Fin r → ℕ+) (k j : ℕ)
    (hk1 : 1 ≤ k) (hkr : k ≤ r) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F)
    (hsleq : ∀ x : ℕ, x < k - 1 → pad0 s x ≤ Nat.card F)
    (R0 : BinaryRel F)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1) :
    let D := RelData.BCqIter F (k - j - 1) (toData F R0)
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (k - j - 1) R0 e)
        (RelData.iterate_merge_hv F (k - j - 1) R0 (s ⟨j - 1, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s j (by omega) (by omega))
    ∀ i : D.ιB, ∀ x : ℕ, x < j → pad0 (Q.c (Sum.inr (Sum.inr i))) x ≤ Nat.card F := by
  classical
  intro D Bs Q i x hx
  have hdepQ : j ≤ Q.dep (Sum.inr (Sum.inr i)) :=
    Q_dep_inr_inr F r s k j hk1 hkr hj1 hjk hsj R0 hbhd i
  by_cases hxj : x = j - 1
  · subst x
    have hxQ : j - 1 < Q.dep (Sum.inr (Sum.inr i)) := by omega
    have hv := type3_sjadd_one_at F r s k j hk1 hkr hj1 hjk hbig hsj R0 hbhd i hxQ
    have hp : pad0 (Q.c (Sum.inr (Sum.inr i))) (j - 1) =
        ((Q.c (Sum.inr (Sum.inr i))) ⟨j - 1, hxQ⟩ : ℕ) :=
      pad0_of_lt (Q.c (Sum.inr (Sum.inr i))) hxQ
    rw [hp]
    rw [hv]
    omega
  · have hx1 : x < j - 1 := by omega
    have hfront := type3_front_eq F r s k j hk1 hkr hj1 hjk hbig hsj R0 hbhd i x hx1
    rw [hfront]
    have hxk : x < k - 1 := by omega
    exact hsleq x hxk

/-- ★ The type-3 Init comparison: a type-3 member `u` of the (2.14) chain has a
strictly lexicographically larger initial tuple than `s`, i.e.
`InitLt (Nat.card F) s u` (equivalently `Init(s) ≺ Init(u)` in the paper's
notation), given the `(k−1)`-admissible front `s₁..s_{k−1} ≤ q`.  This is the
termination engine of Prop 3.2 (type-3 outputs strictly increase `Init`, and all
`Init`'s of non-admissible depth-`≥ k` tuples are bounded by `q{k}`). -/
lemma type3_Init_gt (r : ℕ) (s : Fin r → ℕ+) (k j : ℕ)
    (hk1 : 1 ≤ k) (hkr : k ≤ r) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F)
    (hsleq : ∀ x : ℕ, x < k - 1 → pad0 s x ≤ Nat.card F)
    (R0 : BinaryRel F)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1) :
    let D := RelData.BCqIter F (k - j - 1) (toData F R0)
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (k - j - 1) R0 e)
        (RelData.iterate_merge_hv F (k - j - 1) R0 (s ⟨j - 1, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s j (by omega) (by omega))
    ∀ i : D.ιB, InitLt (Nat.card F) s (Q.c (Sum.inr (Sum.inr i))) := by
  classical
  intro D Bs Q i
  let p : D.ιA ⊕ (D.ιB ⊕ D.ιB) := Sum.inr (Sum.inr i)
  have hdepQ : j ≤ Q.dep p := by
    dsimp [p]
    exact Q_dep_inr_inr F r s k j hk1 hkr hj1 hjk hsj R0 hbhd i
  have hjr : j ≤ r := by omega
  have huq : ∀ x : ℕ, x < j → pad0 (Q.c p) x ≤ Nat.card F := by
    dsimp [p]
    exact type3_front_le F r s k j hk1 hkr hj1 hjk hbig hsj hsleq R0 hbhd i
  have hvq : ∀ x : ℕ, x < j → pad0 s x ≤ Nat.card F := by
    intro x hx
    have hxk : x < k - 1 := by omega
    exact hsleq x hxk
  have heq : ∀ x : ℕ, x < j - 1 → pad0 (Q.c p) x = pad0 s x := by
    dsimp [p]
    exact type3_front_eq F r s k j hk1 hkr hj1 hjk hbig hsj R0 hbhd i
  have hxQ : j - 1 < Q.dep p := by omega
  have hxr : j - 1 < r := by omega
  have hv := type3_sjadd_one_at F r s k j hk1 hkr hj1 hjk hbig hsj R0 hbhd i hxQ
  have hgt : pad0 s (j - 1) < pad0 (Q.c p) (j - 1) := by
    dsimp [p]
    have hp1 : pad0 s (j - 1) = (s ⟨j - 1, hxr⟩ : ℕ) := pad0_of_lt s hxr
    have hp2 : pad0 (Q.c (Sum.inr (Sum.inr i))) (j - 1) =
        ((Q.c (Sum.inr (Sum.inr i))) ⟨j - 1, hxQ⟩ : ℕ) :=
      pad0_of_lt (Q.c (Sum.inr (Sum.inr i))) hxQ
    rw [hp1, hp2]
    rw [hv]
    omega
  simpa [p] using InitLt_of_head_gt (Nat.card F) (Q.c p) s j hj1 hdepQ hjr huq hvq heq hgt

end ZagierHoffmanPositiveChar
