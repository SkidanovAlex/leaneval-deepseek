import Submission.ZagierHoffmanProof.StepL17

set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators

/-!
# Step L18: the type-1/2/3 partition of the B*_v level sum

`triple_sum_split` is the generic three-way partition of a sum over
`α ⊕ (β ⊕ γ)` (type 1 = `α`, type 2 = `β`, type 3 = `γ`).
★ `ofBstar_level_parts` applies it to the level value of the B*_v fixed relation
(`FixedRel.ofBstar`, paper (2.13)): the three parts — `a`-side over `D.ιA`
(type 1), `(v :: t)`-`b`-terms over `D.ιB` (type 2), merged `headAdd` terms over
`D.ιB` (type 3) — sum to `0` at every level `d`.
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- ★ Generic three-way partition of a sum over `α ⊕ (β ⊕ γ)`. -/
lemma triple_sum_split {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
    (f : α ⊕ (β ⊕ γ) → RatFunc.CompletionAtInfty F) :
    (∑ p : α ⊕ (β ⊕ γ), f p) =
      (∑ i : α, f (Sum.inl i)) +
      (∑ j : β, f (Sum.inr (Sum.inl j))) +
      (∑ k : γ, f (Sum.inr (Sum.inr k))) := by
  classical
  calc
    (∑ p : α ⊕ (β ⊕ γ), f p)
        = (∑ i : α, f (Sum.inl i)) + (∑ q : β ⊕ γ, f (Sum.inr q)) := by
          rw [Fintype.sum_sum_type]
    _ = (∑ i : α, f (Sum.inl i)) + ((∑ j : β, f (Sum.inr (Sum.inl j))) +
          (∑ k : γ, f (Sum.inr (Sum.inr k)))) := by
          congr 1
          rw [Fintype.sum_sum_type]
    _ = (∑ i : α, f (Sum.inl i)) + (∑ j : β, f (Sum.inr (Sum.inl j))) +
          (∑ k : γ, f (Sum.inr (Sum.inr k))) := by ring

/-- The three type-1/2/3 parts of the B*_v level: type 1 over `D.ιA` (the `a`-side),
type 2 over `D.ιB` (the `(v :: t)` `b`-terms), type 3 over `D.ιB` (the merged
`headAdd` terms). -/
lemma ofBstar_level_parts (D : RelData F) (v : ℕ+)
    (hvalid : ∀ e : ℕ, RelData.level F D e = 0)
    (hv : ∀ p : D.ιB, (v : ℕ) + ((D.cB p) ⟨0, D.hdepB p⟩ : ℕ) ≤ Nat.card F) (d : ℕ) :
    let R := FixedRel.ofBstar F D v hvalid hv
    (∑ i : D.ιA, (((R.a (Sum.inl i) : RatFunc F) : RatFunc.CompletionAtInfty F) *
        S F (R.dep (Sum.inl i)) (R.hdep (Sum.inl i)) (R.c (Sum.inl i)) d)) +
    (∑ j : D.ιB, (((R.a (Sum.inr (Sum.inl j)) : RatFunc F) : RatFunc.CompletionAtInfty F) *
        S F (R.dep (Sum.inr (Sum.inl j))) (R.hdep (Sum.inr (Sum.inl j))) (R.c (Sum.inr (Sum.inl j))) d)) +
    (∑ j : D.ιB, (((R.a (Sum.inr (Sum.inr j)) : RatFunc F) : RatFunc.CompletionAtInfty F) *
        S F (R.dep (Sum.inr (Sum.inr j))) (R.hdep (Sum.inr (Sum.inr j))) (R.c (Sum.inr (Sum.inr j))) d)) = 0 := by
  classical
  intro R
  -- R's level is 0 (ofBstar_valid); split its level-sum three ways
  have h0 : FixedRel.level F R d = 0 := FixedRel.ofBstar_valid F D v hvalid hv d
  dsimp [FixedRel.level] at h0
  -- h0 : (∑ p : R.ι, …) = 0 where R.ι defeq D.ιA ⊕ (D.ιB ⊕ D.ιB) — change the domain
  change (∑ p : D.ιA ⊕ (D.ιB ⊕ D.ιB),
      (((R.a p : RatFunc F) : RatFunc.CompletionAtInfty F) *
        S F (R.dep p) (R.hdep p) (R.c p) d)) = 0 at h0
  -- partition into three
  have hsplit := triple_sum_split F (fun p : D.ιA ⊕ (D.ιB ⊕ D.ιB) =>
      (((R.a p : RatFunc F) : RatFunc.CompletionAtInfty F) * S F (R.dep p) (R.hdep p) (R.c p) d))
  -- hsplit : sum = t1 + t2 + t3
  rw [hsplit] at h0
  exact h0

end ZagierHoffmanPositiveChar
