import Submission.ZagierHoffmanProof.StepL56
set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators

/-!
# Step L57: MAIN(2) — the CASE-1 j = 1 type-1 subcase (SESSION 200, first step)

MAIN(2) goal (PLAN SESSION 199): prove the in-domain handler
`main2 w : ∀ in-domain (1-adm ∧ ¬2-adm) weight-w m, AdmExpT F w 2 m` by
StepL55's `l2_induction`; per-step dispatch (inDomain2_cases, StepL56): CASE-1
j = 1 (s₁ < q < s₂) through prop212_step1 at k = 2, j = 1; CASE-2 s₁ < q through
A2_case2 (no recursion); j = 0 (G5) separate.

THIS MODULE (first subcase, all sorry-free):
  case1_pad0_big_of_value / case1_pad0_head_of_value — convert the in-domain
    (pad0-form) data into the value forms prop212_step1 needs;
  ★ case1_j1_type1_dispatch (w r s hw hcase hbig hs1q h1) — the TYPE-1 subcase:
    rcases prop212_step1 at k = 2, j = 1 and extract, for every guarded a-side
    (type-1) member i₀ ≠ u: weight = w (ht1 conjunct + hw) and the STRICT
    prefix-2 drop ⟹ l2_member_lt (q := Nat.card F) — i.e. the recursion's
    termination obligation for type-1 members is now a concrete sorry-free lemma
    (its proof: `rcases` the package; `intro D Bs Q` to expose the member family;
    per member the two conjuncts from ht1).

NEXT (SESSION 201): the type-2 mirror (case1_j1_type2_dispatch: D.ιB inl members,
weight = w ∧ psum-2 < psum s 2 ⟹ l2_member_lt) and the type-3 subcase
(case1_j1_type3_dispatch: D.ιB inr members, weight = w ∧ psum-2 ≤ psum s 2, with
the = S members' headVal growth s₁ → s₁+1 at position 0 (type3_sjadd_one_at at
j = 1) giving l2_member_lt's second disjunct) — the type-2/type-3 lemmas have the
same local shape and can be delegated in parallel.  Then MAIN(2)@w via
l2_induction with per-step dispatch, A(2)@w via A2_with_main2, theorem_A(w) via
the StepL54 tail.  j = 0 G5 chains and the m ≥ 3 β-design remain separate.
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]


/-- CASE-1 data conversion: from `q < pad0 s 1` (depth ≥ 2) to the value form
`prop212_step1` needs. -/
lemma case1_pad0_big_of_value {r : ℕ} (s : Fin r → ℕ+) (hr : 2 ≤ r)
    (hbig : (Nat.card F : ℕ) < pad0 s 1) : (Nat.card F : ℕ) < (s ⟨1, by omega⟩ : ℕ) := by
  have hp : pad0 s 1 = (s ⟨1, by omega⟩ : ℕ) := pad0_of_lt s (by omega : 1 < r)
  rw [← hp]
  exact hbig

/-- CASE-1 head conversion: from `pad0 s 0 < q` (depth ≥ 1) to the value form. -/
lemma case1_pad0_head_of_value {r : ℕ} (s : Fin r → ℕ+) (hr : 0 < r)
    (hs1q : pad0 s 0 < Nat.card F) : (s ⟨0, by omega⟩ : ℕ) < Nat.card F := by
  have hp : pad0 s 0 = (s ⟨0, by omega⟩ : ℕ) := pad0_of_lt s hr
  rw [← hp]
  exact hs1q

/-- ★ The level-2 CASE-1 j = 1 TYPE-1 dispatch: every guarded a-side (type-1)
member `≠ u` of the Prop-2.12 package has weight `w` and strictly smaller level-2
measure — the recursion's termination obligation (l2_member_lt from the strict
prefix-2 drop). -/
theorem case1_j1_type1_dispatch (w : ℕ) (r : ℕ) (s : Fin r → ℕ+) (hw : weight r s = w)
    (hcase : 2 ≤ r) (hbig : (Nat.card F : ℕ) < (s ⟨1, by omega⟩ : ℕ))
    (hs1q : (s ⟨0, by omega⟩ : ℕ) < Nat.card F)
    (h1 : kAdmissible (Nat.card F) s 1) :
    ∃ (R0 : BinaryRel F) (u : R0.ιA)
      (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1),
      let D := RelData.BCqIter F 0 (toData F R0)
      let Bs := ofBstarOver F D (s ⟨0, by omega⟩) (fun e => BCqIter_valid F 0 R0 e)
          (RelData.iterate_merge_hv F 0 R0 (s ⟨0, by omega⟩) (by omega) hbhd)
      let Q := FixedOver.prependList F Bs (sPrefix r s 1 (by omega) (by omega))
      ∀ i₀ : R0.ιA, i₀ ≠ u →
        weight (Q.dep (Sum.inl (RelData.iterIdx F 0 (toData F R0) i₀)))
            (Q.c (Sum.inl (RelData.iterIdx F 0 (toData F R0) i₀))) = w ∧
        l2μ (Nat.card F) (Q.c (Sum.inl (RelData.iterIdx F 0 (toData F R0) i₀))) <
          l2μ (Nat.card F) s := by
  classical
  have hP := prop212_step1 F r s 2 1 (by omega : 1 ≤ 2) hcase (by omega : 1 ≤ 1)
    (by omega : 1 ≤ 2 - 1) hbig hs1q
    (fun i hi1 hi0 => by omega)
    (fun x hx => by
      have hx0 : x = 0 := by omega
      subst x
      exact h1.1 0 (by omega))
  rcases hP with ⟨R0, u, hbhd, haa, hdepu, hbstar, hrel, ht1, ht2, ht3⟩
  refine ⟨R0, u, hbhd, ?_⟩
  intro D Bs Q
  intro i₀ hi₀
  have hwmem : weight (Q.dep (Sum.inl (RelData.iterIdx F 0 (toData F R0) i₀)))
        (Q.c (Sum.inl (RelData.iterIdx F 0 (toData F R0) i₀))) = weight r s :=
    (ht1 i₀ hi₀).1
  have hp2 : psum (Q.c (Sum.inl (RelData.iterIdx F 0 (toData F R0) i₀))) 2 < psum s 2 :=
    (ht1 i₀ hi₀).2
  constructor
  · rw [hwmem]
    exact hw
  · exact l2_member_lt (q := Nat.card F) s
      (Q.c (Sum.inl (RelData.iterIdx F 0 (toData F R0) i₀))) (Or.inl hp2)
end ZagierHoffmanPositiveChar
