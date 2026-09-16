import Submission.ZagierHoffmanProof.StepL57
set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators

/-!
# Step L58: MAIN(2) — the CASE-1 j = 1 type-2 and type-3 subcases (SESSION 201)

MAIN(2)'s CASE-1 j = 1 per-member dispatch is now COMPLETE (all three member
families of the Prop-2.12 package at k = 2, j = 1):
  type-1: StepL57 case1_j1_type1_dispatch (a-side i₀ ≠ u);
  ★ type-2: case1_j1_type2_dispatch (D.ιB Sum.inr (Sum.inl i)) — the exact mirror of
    the type-1 script: rcases prop212_step1, intro D Bs Q, per member weight = w
    (ht2 conjunct + hw) and strict prefix-2 drop ⟹ l2_member_lt (first disjunct);
  ★ type-3: case1_j1_type3_dispatch (D.ιB Sum.inr (Sum.inr i)) — weight = w and the
    DISPATCH DISJUNCTION: psum-2 < psum s 2 ∨ (psum-2 = psum s 2 ∧
    headVal q s < headVal q m): the equality case needs the type-3 front growth
    pad0 m 0 = s₁+1 at position 0 (type3_sjadd_one_at at k=2, j=1, index ⟨0, hm⟩
    with hm from Q_dep_inr_inr's j ≤ Q.dep) and pad0 m 0 ≤ q (type3_front_le at
    x = 0 < j), which give headVal q m = pad0 s 0 + 1 > pad0 s 0 = headVal q s.
So the recursion's termination obligation (l2_member_lt, StepL55) is a concrete
lemma for EVERY CASE-1 j = 1 member family; MAIN(2)@w's per-step dispatch is fully
specified and all its ingredient lemmas are sorry-free.

NEXT (SESSION 202): assemble MAIN(2)@w := l2_induction (StepL55) with
P(r s hw) := kAdm q s 1 → ¬kAdm q s 2 → AdmExpT F w 2 s; per step: inDomain2_cases
(StepL56): CASE-2 s₁ < q → A2_case2 (no recursion); CASE-2 s₁ = q / CASE-1 s₁ = q
are the j = 0 G5 chains (separate); CASE-1 j = 1 (s₁ < q < s₂) → rcases
prop212_step1 (via case1_j1_step1 shape): per member m by_cases 2-adm →
admExpT_self, ¬2-adm → recursion (IH at l2μ m < l2μ s, justified by the type-1/2/3
dispatch lemmas) — members are 1-adm (front ≤ q), and splice by admExpT_combine.
Then A(2)@w via A2_with_main2, theorem_A(w) via the StepL54 tail.  j = 0 G5 chains
and the m ≥ 3 β-design remain separate; theorem_B/D ABP-gated.
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- ★ The level-2 CASE-1 j = 1 TYPE-2 dispatch: every type-2 member of the
Prop-2.12 package has weight `w` and strictly smaller level-2 measure — the
recursion's termination obligation (l2_member_lt from the strict prefix-2 drop). -/
theorem case1_j1_type2_dispatch (w : ℕ) (r : ℕ) (s : Fin r → ℕ+) (hw : weight r s = w)
    (hcase : 2 ≤ r) (hbig : (Nat.card F : ℕ) < (s ⟨1, by omega⟩ : ℕ))
    (hs1q : (s ⟨0, by omega⟩ : ℕ) < Nat.card F)
    (h1 : kAdmissible (Nat.card F) s 1) :
    ∃ (R0 : BinaryRel F)
      (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1),
      let D := RelData.BCqIter F 0 (toData F R0)
      let Bs := ofBstarOver F D (s ⟨0, by omega⟩) (fun e => BCqIter_valid F 0 R0 e)
          (RelData.iterate_merge_hv F 0 R0 (s ⟨0, by omega⟩) (by omega) hbhd)
      let Q := FixedOver.prependList F Bs (sPrefix r s 1 (by omega) (by omega))
      ∀ i : D.ιB,
        weight (Q.dep (Sum.inr (Sum.inl i))) (Q.c (Sum.inr (Sum.inl i))) = w ∧
        l2μ (Nat.card F) (Q.c (Sum.inr (Sum.inl i))) < l2μ (Nat.card F) s := by
  classical
  have hP := prop212_step1 F r s 2 1 (by omega : 1 ≤ 2) hcase (by omega : 1 ≤ 1)
    (by omega : 1 ≤ 2 - 1) hbig hs1q
    (fun i hi1 hi0 => by omega)
    (fun x hx => by
      have hx0 : x = 0 := by omega
      subst x
      exact h1.1 0 (by omega))
  rcases hP with ⟨R0, u, hbhd, haa, hdepu, hbstar, hrel, ht1, ht2, ht3⟩
  refine ⟨R0, hbhd, ?_⟩
  intro D Bs Q
  intro i
  have hwmem : weight (Q.dep (Sum.inr (Sum.inl i))) (Q.c (Sum.inr (Sum.inl i))) = weight r s :=
    (ht2 i).1
  have hp2 : psum (Q.c (Sum.inr (Sum.inl i))) 2 < psum s 2 := (ht2 i).2
  constructor
  · rw [hwmem]
    exact hw
  · exact l2_member_lt (q := Nat.card F) s (Q.c (Sum.inr (Sum.inl i))) (Or.inl hp2)

/-- ★ The level-2 CASE-1 j = 1 TYPE-3 dispatch: every type-3 member has weight `w`
and satisfies the measure-dispatch disjunction (strict prefix-2 drop, or equal
prefix-2 with first-initial-entry growth s₁ → s₁+1 at position 0) — the recursion's
termination obligation. -/
theorem case1_j1_type3_dispatch (w : ℕ) (r : ℕ) (s : Fin r → ℕ+) (hw : weight r s = w)
    (hcase : 2 ≤ r) (hbig : (Nat.card F : ℕ) < (s ⟨1, by omega⟩ : ℕ))
    (hs1q : (s ⟨0, by omega⟩ : ℕ) < Nat.card F)
    (h1 : kAdmissible (Nat.card F) s 1) :
    ∃ (R0 : BinaryRel F)
      (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1),
      let D := RelData.BCqIter F 0 (toData F R0)
      let Bs := ofBstarOver F D (s ⟨0, by omega⟩) (fun e => BCqIter_valid F 0 R0 e)
          (RelData.iterate_merge_hv F 0 R0 (s ⟨0, by omega⟩) (by omega) hbhd)
      let Q := FixedOver.prependList F Bs (sPrefix r s 1 (by omega) (by omega))
      ∀ i : D.ιB,
        weight (Q.dep (Sum.inr (Sum.inr i))) (Q.c (Sum.inr (Sum.inr i))) = w ∧
        (psum (Q.c (Sum.inr (Sum.inr i))) 2 < psum s 2 ∨
          (psum (Q.c (Sum.inr (Sum.inr i))) 2 = psum s 2 ∧
            headVal (Nat.card F) s <
              headVal (Nat.card F) (Q.c (Sum.inr (Sum.inr i))))) := by
  classical
  have hk1 : 1 ≤ 2 := by omega
  have hj1 : 1 ≤ 1 := by omega
  have hjk : 1 ≤ 2 - 1 := by omega
  have hsleq : ∀ x : ℕ, x < 2 - 1 → pad0 s x ≤ Nat.card F := by
    intro x hx
    have hx0 : x = 0 := by omega
    subst x
    exact h1.1 0 (by omega)
  have hP := prop212_step1 F r s 2 1 hk1 hcase hj1 hjk hbig hs1q
    (fun i hi1 hi0 => by omega) hsleq
  rcases hP with ⟨R0, u, hbhd, haa, hdepu, hbstar, hrel, ht1, ht2, ht3⟩
  refine ⟨R0, hbhd, ?_⟩
  intro D Bs Q
  intro i
  let m : Fin (Q.dep (Sum.inr (Sum.inr i))) → ℕ+ := Q.c (Sum.inr (Sum.inr i))
  have hwmem : weight (Q.dep (Sum.inr (Sum.inr i))) m = weight r s := (ht3 i).1
  have hle : psum m 2 ≤ psum s 2 := by
    simpa [m] using (ht3 i).2.1
  constructor
  · rw [hwmem]
    exact hw
  · by_cases hlt : psum m 2 < psum s 2
    · exact Or.inl hlt
    · right
      constructor
      · exact le_antisymm hle (le_of_not_gt hlt)
      · have hdep : 1 ≤ Q.dep (Sum.inr (Sum.inr i)) :=
          Q_dep_inr_inr F r s 2 1 hk1 hcase hj1 hjk hs1q R0 hbhd i
        have hm : 0 < Q.dep (Sum.inr (Sum.inr i)) := by omega
        have hfront := type3_sjadd_one_at F r s 2 1 hk1 hcase hj1 hjk hbig hs1q R0 hbhd i hm
        have hfl := type3_front_le F r s 2 1 hk1 hcase hj1 hjk hbig hs1q hsleq R0 hbhd i 0 (by omega : 0 < 1)
        have hsv : headVal (Nat.card F) s = pad0 s 0 := by
          rw [headVal]
          rw [if_pos (h1.1 0 (by omega : 0 < 1))]
        have hmv : headVal (Nat.card F) m = pad0 m 0 := by
          rw [headVal]
          rw [if_pos hfl]
        rw [hsv, hmv]
        have hp0v : pad0 m 0 = (m ⟨0, hm⟩ : ℕ) := pad0_of_lt m hm
        have hs0v : pad0 s 0 = (s ⟨0, by omega⟩ : ℕ) := pad0_of_lt s (by omega : 0 < r)
        rw [hp0v, hs0v]
        have hfront' : (m ⟨0, hm⟩ : ℕ) = (s ⟨0, by omega⟩ : ℕ) + 1 := by
          simpa [m] using hfront
        rw [hfront']
        omega
end ZagierHoffmanPositiveChar
