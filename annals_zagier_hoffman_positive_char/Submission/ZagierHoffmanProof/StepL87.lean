import Submission.ZagierHoffmanProof.StepL83
import Submission.ZagierHoffmanProof.StepL84
set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators
/-!
# Step L87: the (k=3, j=1) CASE-1 member 2-adm facts in `_of` form

SESSION 245.  The StepL83/84 theorems are ∃-style (they rcase prop212_step1
internally); main3's CASE-1 j=1 splice must dispatch members of ITS OWN rcases of
prop212 (separate rcases produce non-defeq witnesses).  These `_of` theorems take
the package data (R0, u, hbhd) as parameters and conclude over the (3, j=1) chain
lets (D := BCqIter F 1 (toData F R0), B*_{s₀}, empty front — the StepL71/72 →
StepL73 lesson):
  ★ level3_j1_type1_twoAdm_of : ∀ i₀ ≠ u, the a-side member (inl slot) is 2-adm;
  ★ level3_j1_type2_twoAdm_of : every b-side inl member is 2-adm;
  ★ level3_j1_type3_twoAdm_of : every b-side inr member with weight = weight r s
     (the splice's ht3 conjunct) is 2-adm — the depth-2 (·,q) form is killed by
     weight = w > s₀ + q + 1.
The proofs are the ∃-bodies minus the rcases (the type-1/type-2 member proofs use
only machinery on (R0, hbhd) + the s-shape; the type-3 needs hs1q and the weight
for its cond2).  NEXT: the (k=3, j=2) mirrors (level3_j2_type{1,2,3}_twoAdm_of),
then the j=1/j=2 splices (g53_case1_step's script at prop212-(3,j)) and main3's
CASE-1 assembly.  theorem_B/D remain ABP-gated (no route).
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]



/-! ## SESSION 245 — the j=1 `_of`-form member 2-adm facts (for the main3 CASE-1
j=1 splice).  The StepL83/84 ∃-theorems internally rcase prop212_step1; the
splice needs the SAME-R0 member facts, so these take (R0, u, hbhd) as parameters
and conclude over the (3, j=1) chain lets (D := BCqIter F 1 (toData F R0),
B*_{s₀}, empty front).  Type-1/type-2 proofs are the ∃-bodies minus the rcases;
type-3 additionally takes the per-member weight equality (its depth-2-form kill
used prop212's ht3 weight — supplied by the splice's ht-conjunct). -/

/-- type-1 (a-side, i₀ ≠ u) members of the (k=3, j=1) chain: 2-adm, _of form. -/
theorem level3_j1_type1_twoAdm_of (r : ℕ) (s : Fin r → ℕ+) (hr3 : 3 ≤ r)
    (hbig : (Nat.card F : ℕ) < (s ⟨2, by omega⟩ : ℕ))
    (hs0q : (s ⟨0, by omega⟩ : ℕ) < Nat.card F)
    (R0 : BinaryRel F) (u : R0.ιA)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1) :
    let D := RelData.BCqIter F 1 (toData F R0)
    let Bs := ofBstarOver F D (s ⟨0, by omega⟩) (fun e => BCqIter_valid F 1 R0 e)
        (RelData.iterate_merge_hv F 1 R0 (s ⟨0, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s 1 (by omega) (by omega))
    ∀ i₀ : R0.ιA, i₀ ≠ u →
      kAdmissible (Nat.card F) (Q.c (Sum.inl (RelData.iterIdx F 1 (toData F R0) i₀))) 2 := by
  classical
  intro D Bs Q i₀ hi
  have hdepge : 3 ≤ Q.dep (Sum.inl (RelData.iterIdx F 1 (toData F R0) i₀)) := by
    have hQd : Q.dep (Sum.inl (RelData.iterIdx F 1 (toData F R0) i₀)) =
        D.depA (RelData.iterIdx F 1 (toData F R0) i₀) + 1 + 0 := by
      have h1 := FixedOver.prependList_dep F Bs (sPrefix r s 1 (by omega) (by omega))
        (Sum.inl (RelData.iterIdx F 1 (toData F R0) i₀))
      have h2 : Bs.dep (Sum.inl (RelData.iterIdx F 1 (toData F R0) i₀)) =
          D.depA (RelData.iterIdx F 1 (toData F R0) i₀) + 1 := by
        dsimp [Bs, ofBstarOver]
      have hlen : (sPrefix r s 1 (by omega) (by omega)).length = 0 := by
        rw [sPrefix_length]
      rw [h1, h2, hlen]
    rw [hQd]
    have hd := RelData.BCqIter_depA_at F 1 (toData F R0) i₀
    rw [hd]
    have hda : 0 < (toData F R0).depA i₀ := by
      change 0 < R0.depA i₀
      exact R0.hdepA i₀
    omega
  refine twoAdm_of_pad0_le (Nat.card F)
    (Q.c (Sum.inl (RelData.iterIdx F 1 (toData F R0) i₀))) hdepge ?_ ?_
  · have he0 : pad0 (Q.c (Sum.inl (RelData.iterIdx F 1 (toData F R0) i₀))) 0 =
      (s ⟨0, by omega⟩ : ℕ) := by
      have hQ0 : 0 < Q.dep (Sum.inl (RelData.iterIdx F 1 (toData F R0) i₀)) := by omega
      rw [pad0_of_lt (Q.c (Sum.inl (RelData.iterIdx F 1 (toData F R0) i₀))) hQ0]
      have hv := type1_sj_at_jm1 F r s 3 1 (by omega : 1 ≤ 3) hr3 (by omega : 1 ≤ 1)
        (by omega : 1 ≤ 3 - 1) hbig hs0q R0 hbhd
        (RelData.iterIdx F 1 (toData F R0) i₀)
        (show 1 - 1 < Q.dep (Sum.inl (RelData.iterIdx F 1 (toData F R0) i₀)) by simpa using hQ0)
      simpa using hv
    rw [he0]
    omega
  · have he1 : pad0 (Q.c (Sum.inl (RelData.iterIdx F 1 (toData F R0) i₀))) 1 =
      Nat.card F := by
      have hsh' : pad0 (Q.c (Sum.inl (RelData.iterIdx F 1 (toData F R0) i₀))) 1 =
          pad0 ((RelData.BCqIter F 1 (toData F R0)).cA
            (RelData.iterIdx F 1 (toData F R0) i₀)) 0 := by
        simpa using (type1_pad0_shift F r s 3 1 (by omega : 1 ≤ 3) hr3 (by omega : 1 ≤ 1)
          (by omega : 1 ≤ 3 - 1) hbig hs0q R0 hbhd
          (RelData.iterIdx F 1 (toData F R0) i₀) 1 (by omega))
      rw [hsh']
      have hf := BCqIter_cA_pad0_front F 1 R0 i₀ 0 (by omega)
      rw [hf]
    rw [he1]


/-- type-2 (b-side inl) members of the (k=3, j=1) chain: 2-adm, _of form. -/
theorem level3_j1_type2_twoAdm_of (r : ℕ) (s : Fin r → ℕ+) (hr3 : 3 ≤ r)
    (hbig : (Nat.card F : ℕ) < (s ⟨2, by omega⟩ : ℕ))
    (hs0q : (s ⟨0, by omega⟩ : ℕ) < Nat.card F)
    (R0 : BinaryRel F) (u : R0.ιA)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1) :
    let D := RelData.BCqIter F 1 (toData F R0)
    let Bs := ofBstarOver F D (s ⟨0, by omega⟩) (fun e => BCqIter_valid F 1 R0 e)
        (RelData.iterate_merge_hv F 1 R0 (s ⟨0, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s 1 (by omega) (by omega))
    ∀ i : D.ιB, kAdmissible (Nat.card F) (Q.c (Sum.inr (Sum.inl i))) 2 := by
  classical
  intro D Bs Q i
  have hdepge : 3 ≤ Q.dep (Sum.inr (Sum.inl i)) := by
    have hQd : Q.dep (Sum.inr (Sum.inl i)) = D.depB i + 1 + 0 := by
      have h1 := FixedOver.prependList_dep F Bs (sPrefix r s 1 (by omega) (by omega))
        (Sum.inr (Sum.inl i))
      have h2 : Bs.dep (Sum.inr (Sum.inl i)) = D.depB i + 1 := by
        dsimp [Bs, ofBstarOver]
      have hlen : (sPrefix r s 1 (by omega) (by omega)).length = 0 := by
        rw [sPrefix_length]
      rw [h1, h2, hlen]
    rw [hQd]
    have hb := D.hB2 i
    omega
  refine twoAdm_of_pad0_le (Nat.card F) (Q.c (Sum.inr (Sum.inl i))) hdepge ?_ ?_
  · have he0 : pad0 (Q.c (Sum.inr (Sum.inl i))) 0 = (s ⟨0, by omega⟩ : ℕ) := by
      have hQ0 : 0 < Q.dep (Sum.inr (Sum.inl i)) := by omega
      rw [pad0_of_lt (Q.c (Sum.inr (Sum.inl i))) hQ0]
      have hv := type2_sj_at_jm1 F r s 3 1 (by omega : 1 ≤ 3) hr3 (by omega : 1 ≤ 1)
        (by omega : 1 ≤ 3 - 1) hbig hs0q R0 hbhd i
        (show 1 - 1 < Q.dep (Sum.inr (Sum.inl i)) by simpa using hQ0)
      simpa using hv
    rw [he0]
    omega
  · have he1 : pad0 (Q.c (Sum.inr (Sum.inl i))) 1 = 1 := by
      have hsh' : pad0 (Q.c (Sum.inr (Sum.inl i))) 1 = pad0 (D.cB i) 0 := by
        simpa using (type2_pad0_shift F r s 3 1 (by omega : 1 ≤ 3) hr3 (by omega : 1 ≤ 1)
          (by omega : 1 ≤ 3 - 1) hbig hs0q R0 hbhd i 0)
      rw [hsh']
      have hh := BCqIter_head_one_data F 1 R0 hbhd i
      rw [pad0_of_lt (D.cB i) (D.hdepB i)]
      exact hh
    rw [he1]
    have hq1 : 1 ≤ Nat.card F := by
      have h2 : 2 ≤ Nat.card F := card_ge_two F
      omega
    exact hq1

/-- type-3 (b-side inr) members of the (k=3, j=1) chain: 2-adm, _of form (per-member
weight ⟹ 2-adm; the splice supplies the weight from prop212's ht3 conjunct). -/
theorem level3_j1_type3_twoAdm_of (r : ℕ) (s : Fin r → ℕ+) (hr3 : 3 ≤ r)
    (hbig : (Nat.card F : ℕ) < (s ⟨2, by omega⟩ : ℕ))
    (hs0q : (s ⟨0, by omega⟩ : ℕ) < Nat.card F)
    (hs1q : (s ⟨1, by omega⟩ : ℕ) = Nat.card F)
    (R0 : BinaryRel F) (u : R0.ιA)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1) :
    let D := RelData.BCqIter F 1 (toData F R0)
    let Bs := ofBstarOver F D (s ⟨0, by omega⟩) (fun e => BCqIter_valid F 1 R0 e)
        (RelData.iterate_merge_hv F 1 R0 (s ⟨0, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s 1 (by omega) (by omega))
    ∀ i : D.ιB, weight (Q.dep (Sum.inr (Sum.inr i))) (Q.c (Sum.inr (Sum.inr i))) = weight r s →
      kAdmissible (Nat.card F) (Q.c (Sum.inr (Sum.inr i))) 2 := by
  classical
  intro D Bs Q i hwmem
  constructor
  · intro x hx
    have hx01 : x = 0 ∨ x = 1 := by omega
    rcases hx01 with hx0 | hx1
    · subst x
      exact level3_type3_entry0_le_q F r s hr3 hbig hs0q R0 hbhd i
    · subst x
      exact level3_type3_entry_le_q F r s hr3 hbig hs0q R0 hbhd i
  · intro hform
    rcases hform with ⟨hr1, hdep2, hall, hlast⟩
    have hdepge : 2 ≤ Q.dep (Sum.inr (Sum.inr i)) := by
      have hq : Q.dep (Sum.inr (Sum.inr i)) = D.depB i := by
        dsimp [Q, Bs, D, ofBstarOver]
        rfl
      rw [hq]
      have hb := D.hB2 i
      omega
    have hwsum : weight (Q.dep (Sum.inr (Sum.inr i))) (Q.c (Sum.inr (Sum.inr i))) =
        pad0 (Q.c (Sum.inr (Sum.inr i))) 0 + pad0 (Q.c (Sum.inr (Sum.inr i))) 1 := by
      have hdep2' : Q.dep (Sum.inr (Sum.inr i)) = 2 := by omega
      have hps := psum_self (Q.c (Sum.inr (Sum.inr i)))
      calc
        weight (Q.dep (Sum.inr (Sum.inr i))) (Q.c (Sum.inr (Sum.inr i)))
            = psum (Q.c (Sum.inr (Sum.inr i))) (Q.dep (Sum.inr (Sum.inr i))) := hps.symm
        _ = psum (Q.c (Sum.inr (Sum.inr i))) 2 := by
              exact congrArg (psum (Q.c (Sum.inr (Sum.inr i)))) hdep2'
        _ = pad0 (Q.c (Sum.inr (Sum.inr i))) 0 + pad0 (Q.c (Sum.inr (Sum.inr i))) 1 := by
              rw [psum_succ, psum_succ]
              rw [psum_zero]
              simp
    have hu0 : pad0 (Q.c (Sum.inr (Sum.inr i))) 0 = (s ⟨0, by omega⟩ : ℕ) + 1 :=
      level3_type3_entry0_eq_s0_add_one F r s hr3 hbig hs0q R0 hbhd i
    have hle1 : pad0 (Q.c (Sum.inr (Sum.inr i))) 1 ≤ Nat.card F :=
      level3_type3_entry_le_q F r s hr3 hbig hs0q R0 hbhd i
    have hwle : weight (Q.dep (Sum.inr (Sum.inr i))) (Q.c (Sum.inr (Sum.inr i))) ≤
        (s ⟨0, by omega⟩ : ℕ) + Nat.card F + 1 := by
      rw [hwsum, hu0]
      omega
    have hwlow : (s ⟨0, by omega⟩ : ℕ) + Nat.card F + 1 < weight r s := by
      have hp0 : pad0 s 0 = (s ⟨0, by omega⟩ : ℕ) := pad0_of_lt s (by omega : 0 < r)
      have hp1 : pad0 s 1 = (s ⟨1, by omega⟩ : ℕ) := pad0_of_lt s (by omega : 1 < r)
      have hp2 : pad0 s 2 = (s ⟨2, by omega⟩ : ℕ) := pad0_of_lt s (by omega : 2 < r)
      have hpsle : psum s 3 ≤ weight r s := psum_le_weight s 3
      have hpsum3 : psum s 3 = (s ⟨0, by omega⟩ : ℕ) + (s ⟨1, by omega⟩ : ℕ) + (s ⟨2, by omega⟩ : ℕ) := by
        change (∑ j ∈ Finset.range 3, pad0 s j) =
          (s ⟨0, by omega⟩ : ℕ) + (s ⟨1, by omega⟩ : ℕ) + (s ⟨2, by omega⟩ : ℕ)
        rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
        simp
        rw [hp0, hp1, hp2]
      rw [hpsum3] at hpsle
      rw [hs1q] at hpsle
      have hq2 : 2 ≤ Nat.card F := card_ge_two F
      omega
    omega


/-- type-1 (a-side, i₀ ≠ u) members of the (k=3, j=2) chain: 2-adm, _of form. -/
theorem level3_j2_type1_twoAdm_of (r : ℕ) (s : Fin r → ℕ+) (hr3 : 3 ≤ r)
    (hbig : (Nat.card F : ℕ) < (s ⟨2, by omega⟩ : ℕ))
    (hs0 : (s ⟨0, by omega⟩ : ℕ) ≤ Nat.card F)
    (hs1q : (s ⟨1, by omega⟩ : ℕ) < Nat.card F)
    (R0 : BinaryRel F) (u : R0.ιA)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1) :
    let D := RelData.BCqIter F 0 (toData F R0)
    let Bs := ofBstarOver F D (s ⟨1, by omega⟩) (fun e => BCqIter_valid F 0 R0 e)
        (RelData.iterate_merge_hv F 0 R0 (s ⟨1, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s 2 (by omega) (by omega))
    ∀ i₀ : R0.ιA, i₀ ≠ u →
      kAdmissible (Nat.card F) (Q.c (Sum.inl (RelData.iterIdx F 0 (toData F R0) i₀))) 2 := by
  classical
  intro D Bs Q i₀ hi
  have hdepge : 3 ≤ Q.dep (Sum.inl (RelData.iterIdx F 0 (toData F R0) i₀)) := by
    have hQd : Q.dep (Sum.inl (RelData.iterIdx F 0 (toData F R0) i₀)) =
        D.depA (RelData.iterIdx F 0 (toData F R0) i₀) + 1 + 1 := by
      have h1 := FixedOver.prependList_dep F Bs (sPrefix r s 2 (by omega) (by omega))
        (Sum.inl (RelData.iterIdx F 0 (toData F R0) i₀))
      have h2 : Bs.dep (Sum.inl (RelData.iterIdx F 0 (toData F R0) i₀)) =
          D.depA (RelData.iterIdx F 0 (toData F R0) i₀) + 1 := by
        dsimp [Bs, ofBstarOver]
      have hlen : (sPrefix r s 2 (by omega) (by omega)).length = 1 := by
        rw [sPrefix_length]
      rw [h1, h2, hlen]
    rw [hQd]
    have hd := RelData.BCqIter_depA_at F 0 (toData F R0) i₀
    rw [hd]
    have hda : 0 < (toData F R0).depA i₀ := by
      change 0 < R0.depA i₀
      exact R0.hdepA i₀
    omega
  refine twoAdm_of_pad0_le (Nat.card F)
    (Q.c (Sum.inl (RelData.iterIdx F 0 (toData F R0) i₀))) hdepge ?_ ?_
  · have he0 : pad0 (Q.c (Sum.inl (RelData.iterIdx F 0 (toData F R0) i₀))) 0 =
      (s ⟨0, by omega⟩ : ℕ) := by
      have hQ0 : 0 < Q.dep (Sum.inl (RelData.iterIdx F 0 (toData F R0) i₀)) := by omega
      have hv := member_prefix_pos F r s 3 2 (by omega : 1 ≤ 3) hr3 (by omega : 1 ≤ 2)
        (by omega : 2 ≤ 3 - 1) hbig hs1q R0 hbhd
        (Sum.inl (RelData.iterIdx F 0 (toData F R0) i₀)) 0 (by omega) hQ0
      rw [pad0_of_lt (Q.c (Sum.inl (RelData.iterIdx F 0 (toData F R0) i₀))) hQ0]
      simpa using (congrArg (fun t : ℕ+ => (t : ℕ)) hv)
    rw [he0]
    exact hs0
  · have he1 : pad0 (Q.c (Sum.inl (RelData.iterIdx F 0 (toData F R0) i₀))) 1 =
      (s ⟨1, by omega⟩ : ℕ) := by
      have hQ1 : 1 < Q.dep (Sum.inl (RelData.iterIdx F 0 (toData F R0) i₀)) := by omega
      have hv := type1_sj_at_jm1 F r s 3 2 (by omega : 1 ≤ 3) hr3 (by omega : 1 ≤ 2)
        (by omega : 2 ≤ 3 - 1) hbig hs1q R0 hbhd
        (RelData.iterIdx F 0 (toData F R0) i₀) hQ1
      rw [pad0_of_lt (Q.c (Sum.inl (RelData.iterIdx F 0 (toData F R0) i₀))) hQ1]
      simpa using hv
    rw [he1]
    omega


/-- type-2 (b-side inl) members of the (k=3, j=2) chain: 2-adm, _of form. -/
theorem level3_j2_type2_twoAdm_of (r : ℕ) (s : Fin r → ℕ+) (hr3 : 3 ≤ r)
    (hbig : (Nat.card F : ℕ) < (s ⟨2, by omega⟩ : ℕ))
    (hs0 : (s ⟨0, by omega⟩ : ℕ) ≤ Nat.card F)
    (hs1q : (s ⟨1, by omega⟩ : ℕ) < Nat.card F)
    (R0 : BinaryRel F) (u : R0.ιA)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1) :
    let D := RelData.BCqIter F 0 (toData F R0)
    let Bs := ofBstarOver F D (s ⟨1, by omega⟩) (fun e => BCqIter_valid F 0 R0 e)
        (RelData.iterate_merge_hv F 0 R0 (s ⟨1, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s 2 (by omega) (by omega))
    ∀ i : D.ιB, kAdmissible (Nat.card F) (Q.c (Sum.inr (Sum.inl i))) 2 := by
  classical
  intro D Bs Q i
  have hdepge : 3 ≤ Q.dep (Sum.inr (Sum.inl i)) := by
    have hQd : Q.dep (Sum.inr (Sum.inl i)) = D.depB i + 1 + 1 := by
      have h1 := FixedOver.prependList_dep F Bs (sPrefix r s 2 (by omega) (by omega))
        (Sum.inr (Sum.inl i))
      have h2 : Bs.dep (Sum.inr (Sum.inl i)) = D.depB i + 1 := by
        dsimp [Bs, ofBstarOver]
      have hlen : (sPrefix r s 2 (by omega) (by omega)).length = 1 := by
        rw [sPrefix_length]
      rw [h1, h2, hlen]
    rw [hQd]
    have hb := D.hB2 i
    omega
  refine twoAdm_of_pad0_le (Nat.card F) (Q.c (Sum.inr (Sum.inl i))) hdepge ?_ ?_
  · have he0 : pad0 (Q.c (Sum.inr (Sum.inl i))) 0 = (s ⟨0, by omega⟩ : ℕ) := by
      have hQ0 : 0 < Q.dep (Sum.inr (Sum.inl i)) := by omega
      have hv := member_prefix_pos F r s 3 2 (by omega : 1 ≤ 3) hr3 (by omega : 1 ≤ 2)
        (by omega : 2 ≤ 3 - 1) hbig hs1q R0 hbhd
        (Sum.inr (Sum.inl i)) 0 (by omega) hQ0
      rw [pad0_of_lt (Q.c (Sum.inr (Sum.inl i))) hQ0]
      simpa using (congrArg (fun t : ℕ+ => (t : ℕ)) hv)
    rw [he0]
    exact hs0
  · have he1 : pad0 (Q.c (Sum.inr (Sum.inl i))) 1 = (s ⟨1, by omega⟩ : ℕ) := by
      have hQ1 : 1 < Q.dep (Sum.inr (Sum.inl i)) := by omega
      have hv := type2_sj_at_jm1 F r s 3 2 (by omega : 1 ≤ 3) hr3 (by omega : 1 ≤ 2)
        (by omega : 2 ≤ 3 - 1) hbig hs1q R0 hbhd i hQ1
      rw [pad0_of_lt (Q.c (Sum.inr (Sum.inl i))) hQ1]
      simpa using hv
    rw [he1]
    omega

/-- type-3 (b-side inr) members of the (k=3, j=2) chain: 2-adm, _of form (no weight
needed — depth = 1 + D.depB ≥ 3 kills the depth-2 form structurally). -/
theorem level3_j2_type3_twoAdm_of (r : ℕ) (s : Fin r → ℕ+) (hr3 : 3 ≤ r)
    (hbig : (Nat.card F : ℕ) < (s ⟨2, by omega⟩ : ℕ))
    (hs0 : (s ⟨0, by omega⟩ : ℕ) ≤ Nat.card F)
    (hs1q : (s ⟨1, by omega⟩ : ℕ) < Nat.card F)
    (R0 : BinaryRel F) (u : R0.ιA)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1) :
    let D := RelData.BCqIter F 0 (toData F R0)
    let Bs := ofBstarOver F D (s ⟨1, by omega⟩) (fun e => BCqIter_valid F 0 R0 e)
        (RelData.iterate_merge_hv F 0 R0 (s ⟨1, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s 2 (by omega) (by omega))
    ∀ i : D.ιB, kAdmissible (Nat.card F) (Q.c (Sum.inr (Sum.inr i))) 2 := by
  classical
  intro D Bs Q i
  constructor
  · intro x hx
    have hx01 : x = 0 ∨ x = 1 := by omega
    rcases hx01 with hx0 | hx1
    · subst x
      have heq := level3_j2_type3_entry0_eq F r s hr3 hbig hs1q R0 hbhd i
      rw [heq]
      exact hs0
    · subst x
      have heq := level3_j2_type3_entry1_eq F r s hr3 hbig hs1q R0 hbhd i
      rw [heq]
      omega
  · intro hform
    rcases hform with ⟨hr1, hdep2f, hall, hlast⟩
    have hdge : 3 ≤ Q.dep (Sum.inr (Sum.inr i)) := by
      have hQd : Q.dep (Sum.inr (Sum.inr i)) = D.depB i + 1 := by
        have h1 := FixedOver.prependList_dep F Bs (sPrefix r s 2 (by omega) (by omega))
          (Sum.inr (Sum.inr i))
        have h2 : Bs.dep (Sum.inr (Sum.inr i)) = D.depB i := by
          dsimp [Bs, ofBstarOver]
        have hlen : (sPrefix r s 2 (by omega) (by omega)).length = 1 :=
          sPrefix_length r s 2 (by omega) (by omega)
        rw [h1, h2, hlen]
      rw [hQd]
      have hb := D.hB2 i
      omega
    omega
end ZagierHoffmanPositiveChar
