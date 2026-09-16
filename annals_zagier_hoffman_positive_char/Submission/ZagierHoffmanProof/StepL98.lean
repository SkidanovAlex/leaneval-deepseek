import Submission.ZagierHoffmanProof.StepL73
set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators
/-!
# Step L98: the level-2 per-member T-dispatch lemmas (SESSION 251)

The three strengthened (AdmExpT) per-member dispatch lemmas for the (2,1) CASE-1
chain — the mechanical AdmExp → AdmExpT ports of StepL73's q_type*_member_e_of
(2-adm → admExpT_self; ¬2-adm → 1-adm via q_type*_member_head_le + the
depth-1-form weight exclusion + the l2μ drop → the STRONG ih):
  • q_type3_member_e_T_of (w r s hw hcase hbigv hs1v h1 R0 hbhd ht3 ih) :
      ∀ i : D.ιB, AdmExpT F w 2 (Q.c (Sum.inr (Sum.inr i)))
  • q_type1_member_e_T_of (… R0 u hbhd ht1 ih) : ∀ i₀ ≠ u, AdmExpT F w 2
      (Q.c (Sum.inl (iterIdx … i₀)))
  • q_type2_member_e_T_of (… R0 hbhd ht2 ih) : ∀ i : D.ιB, AdmExpT F w 2
      (Q.c (Sum.inr (Sum.inl i)))
over the (2,1) chain lets D := BCqIter F 0 (toData R0), Bs := ofBstarOver D (s⟨0⟩),
Q := prependList Bs (sPrefix r s 1).  ih is the l2-induction IH restricted to
in-domain (1-adm ∧ ¬2-adm) smaller-l2μ tuples, producing AdmExpT.
These supply the per-member e of main2T_case1_j1 (the strengthened level-2 CASE-1
j=1 splice): its hid fold copies main2_case1_j1/StepL73 lines 380+ (A/B/C
guarded-sum fold) and its horder (ℓ ≥ 2: psum (mc p) ℓ ≤ psum s ℓ) comes from
the generic-k StepL47/48 order lemmas at (2,1) with hbndB/hpref derived in the
splice from a single lemma_2_9_rel rcases at (r−2, w1Of-at-2, sTail-at-2) + the
ζ-identity zeta_214_reindexed at (2,1) (the main3_case1_j1 architecture at k=2).
NEXT: the main2T_case1_j1 splice assembly, then main2T (l2_induction + A2_case2 +
G5T strengthened chains).  theorem_B/D remain ABP-gated (no route).
-/


namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

theorem q_type3_member_e_T_of (w : ℕ) (r : ℕ) (s : Fin r → ℕ+) (hw : weight r s = w)
    (hcase : 2 ≤ r) (hbigv : (Nat.card F : ℕ) < (s ⟨1, by omega⟩ : ℕ))
    (hs1v : (s ⟨0, by omega⟩ : ℕ) + 1 ≤ Nat.card F)
    (h1 : kAdmissible (Nat.card F) s 1)
    (R0 : BinaryRel F)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1)
    (ht3 : let D := RelData.BCqIter F 0 (toData F R0)
      let Bs := ofBstarOver F D (s ⟨0, by omega⟩) (fun e => BCqIter_valid F 0 R0 e)
          (RelData.iterate_merge_hv F 0 R0 (s ⟨0, by omega⟩) (by omega) hbhd)
      let Q := FixedOver.prependList F Bs (sPrefix r s 1 (by omega) (by omega))
      ∀ i : D.ιB,
        weight (Q.dep (Sum.inr (Sum.inr i))) (Q.c (Sum.inr (Sum.inr i))) = weight r s ∧
        psum (Q.c (Sum.inr (Sum.inr i))) 2 ≤ psum s 2 ∧
        InitLt (Nat.card F) s (Q.c (Sum.inr (Sum.inr i))))
    (ih : ∀ (r' : ℕ) (m : Fin r' → ℕ+) (hm : weight r' m = w),
      kAdmissible (Nat.card F) m 1 → ¬ kAdmissible (Nat.card F) m 2 →
      l2μ (Nat.card F) m < l2μ (Nat.card F) s → AdmExpT F w 2 m) :
    let D := RelData.BCqIter F 0 (toData F R0)
    let Bs := ofBstarOver F D (s ⟨0, by omega⟩) (fun e => BCqIter_valid F 0 R0 e)
        (RelData.iterate_merge_hv F 0 R0 (s ⟨0, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s 1 (by omega) (by omega))
    ∀ i : D.ιB, AdmExpT F w 2 (Q.c (Sum.inr (Sum.inr i))) := by
  classical
  have hk1 : 1 ≤ 2 := by omega
  have hj1 : 1 ≤ 1 := by omega
  have hjk : 1 ≤ 2 - 1 := by omega
  have hsj : (s ⟨0, by omega⟩ : ℕ) < Nat.card F := by omega
  have hsleq : ∀ x : ℕ, x < 2 - 1 → pad0 s x ≤ Nat.card F := by
    intro x hx
    have hx0 : x = 0 := by omega
    subst x
    exact h1.1 0 (by omega)
  intro D Bs Q
  intro i
  let m : Fin (Q.dep (Sum.inr (Sum.inr i))) → ℕ+ := Q.c (Sum.inr (Sum.inr i))
  have hwm : weight (Q.dep (Sum.inr (Sum.inr i))) m = weight r s := by
    simpa [m] using (ht3 i).1
  by_cases h2 : kAdmissible (Nat.card F) m 2
  · have hd : 0 < Q.dep (Sum.inr (Sum.inr i)) := Q.hdep (Sum.inr (Sum.inr i))
    have h2' : kAdmissible (Nat.card F) (Q.c (Sum.inr (Sum.inr i))) 2 := by
      simpa [m] using h2
    have hw' : weight (Q.dep (Sum.inr (Sum.inr i))) (Q.c (Sum.inr (Sum.inr i))) = w := by
      rw [hwm]
      exact hw
    exact admExpT_self F w 2 hd (Q.c (Sum.inr (Sum.inr i))) hw' h2'
  · have hf := q_type3_member_head_le F r s hcase hbigv hsj R0 hbhd
    have hm0 : pad0 m 0 ≤ Nat.card F := by
      dsimp [m]
      exact hf i
    have hdepth : Q.dep (Sum.inr (Sum.inr i)) = 1 → pad0 m 0 ≠ Nat.card F := by
      intro hd1 hq0
      have hw1 : weight (Q.dep (Sum.inr (Sum.inr i))) m = pad0 m 0 := by
        simpa [m] using weight_dep_one_eq_pad0 (Q.c (Sum.inr (Sum.inr i))) hd1
      have hbigp : (Nat.card F : ℕ) < pad0 s 1 := by
        rw [pad0_of_lt s (by omega : 1 < r)]
        exact hbigv
      have hwg : Nat.card F + 2 ≤ weight r s := case1_weight_ge_q_add_two F s hcase hbigp
      have hwr : weight r s = Nat.card F := by
        calc weight r s = weight (Q.dep (Sum.inr (Sum.inr i))) m := hwm.symm
             _ = pad0 m 0 := hw1
             _ = Nat.card F := hq0
      omega
    have h1m : kAdmissible (Nat.card F) m 1 :=
      kAdm_one_iff_front (Nat.card F) m hm0 hdepth
    have hdrop : l2μ (Nat.card F) m < l2μ (Nat.card F) s := by
      dsimp [m]
      have hle : psum (Q.c (Sum.inr (Sum.inr i))) 2 ≤ psum s 2 := (ht3 i).2.1
      by_cases hlt : psum (Q.c (Sum.inr (Sum.inr i))) 2 < psum s 2
      · exact l2_member_lt (q := Nat.card F) s (Q.c (Sum.inr (Sum.inr i))) (Or.inl hlt)
      · apply l2_member_lt (q := Nat.card F) s (Q.c (Sum.inr (Sum.inr i)))
        right
        constructor
        · exact le_antisymm hle (le_of_not_gt hlt)
        · have hdep : 1 ≤ Q.dep (Sum.inr (Sum.inr i)) :=
            Q_dep_inr_inr F r s 2 1 hk1 hcase hj1 hjk hsj R0 hbhd i
          have hm : 0 < Q.dep (Sum.inr (Sum.inr i)) := by omega
          have hfront := type3_sjadd_one_at F r s 2 1 hk1 hcase hj1 hjk hbigv hsj R0 hbhd i hm
          have hfl := type3_front_le F r s 2 1 hk1 hcase hj1 hjk hbigv hsj hsleq R0 hbhd i 0 (by omega : 0 < 1)
          have hsv : headVal (Nat.card F) s = pad0 s 0 := by
            rw [headVal]
            rw [if_pos (h1.1 0 (by omega : 0 < 1))]
          have hmv : headVal (Nat.card F) (Q.c (Sum.inr (Sum.inr i))) =
              pad0 (Q.c (Sum.inr (Sum.inr i))) 0 := by
            rw [headVal]
            rw [if_pos hfl]
          have hfront0 : ((Q.c (Sum.inr (Sum.inr i))) ⟨0, hm⟩ : ℕ) =
              (s ⟨0, by omega⟩ : ℕ) + 1 := by
            simpa using hfront
          have hp0v : pad0 (Q.c (Sum.inr (Sum.inr i))) 0 =
              ((Q.c (Sum.inr (Sum.inr i))) ⟨0, hm⟩ : ℕ) := pad0_of_lt (Q.c (Sum.inr (Sum.inr i))) hm
          have hs0v : pad0 s 0 = (s ⟨0, by omega⟩ : ℕ) := pad0_of_lt s (by omega : 0 < r)
          rw [hsv]
          rw [hmv]
          rw [hp0v]
          rw [hs0v]
          rw [hfront0]
          omega
    have hwm' : weight (Q.dep (Sum.inr (Sum.inr i))) m = w := by
      rw [hwm]
      exact hw
    have hres := ih (Q.dep (Sum.inr (Sum.inr i))) m hwm' h1m h2 hdrop
    simpa [m] using hres


/-- Per-member e for the TYPE-1 family from package data (R0 u hbhd ht1). -/


theorem q_type1_member_e_T_of (w : ℕ) (r : ℕ) (s : Fin r → ℕ+) (hw : weight r s = w)
    (hcase : 2 ≤ r) (hbigv : (Nat.card F : ℕ) < (s ⟨1, by omega⟩ : ℕ))
    (hs1v : (s ⟨0, by omega⟩ : ℕ) + 1 ≤ Nat.card F)
    (h1 : kAdmissible (Nat.card F) s 1)
    (R0 : BinaryRel F) (u : R0.ιA)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1)
    (ht1 : let D := RelData.BCqIter F 0 (toData F R0)
      let Bs := ofBstarOver F D (s ⟨0, by omega⟩) (fun e => BCqIter_valid F 0 R0 e)
          (RelData.iterate_merge_hv F 0 R0 (s ⟨0, by omega⟩) (by omega) hbhd)
      let Q := FixedOver.prependList F Bs (sPrefix r s 1 (by omega) (by omega))
      ∀ i₀ : R0.ιA, i₀ ≠ u →
        weight (Q.dep (Sum.inl (RelData.iterIdx F 0 (toData F R0) i₀)))
            (Q.c (Sum.inl (RelData.iterIdx F 0 (toData F R0) i₀))) = weight r s ∧
        psum (Q.c (Sum.inl (RelData.iterIdx F 0 (toData F R0) i₀))) 2 < psum s 2)
    (ih : ∀ (r' : ℕ) (m : Fin r' → ℕ+) (hm : weight r' m = w),
      kAdmissible (Nat.card F) m 1 → ¬ kAdmissible (Nat.card F) m 2 →
      l2μ (Nat.card F) m < l2μ (Nat.card F) s → AdmExpT F w 2 m) :
    let D := RelData.BCqIter F 0 (toData F R0)
    let Bs := ofBstarOver F D (s ⟨0, by omega⟩) (fun e => BCqIter_valid F 0 R0 e)
        (RelData.iterate_merge_hv F 0 R0 (s ⟨0, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s 1 (by omega) (by omega))
    ∀ i₀ : R0.ιA, i₀ ≠ u → AdmExpT F w 2
      (Q.c (Sum.inl (RelData.iterIdx F 0 (toData F R0) i₀))) := by
  classical
  intro D Bs Q
  intro i₀ hi₀
  let m : Fin (Q.dep (Sum.inl (RelData.iterIdx F 0 (toData F R0) i₀))) → ℕ+ :=
    Q.c (Sum.inl (RelData.iterIdx F 0 (toData F R0) i₀))
  have hwm : weight (Q.dep (Sum.inl (RelData.iterIdx F 0 (toData F R0) i₀))) m = weight r s := by
    simpa [m] using (ht1 i₀ hi₀).1
  by_cases h2 : kAdmissible (Nat.card F) m 2
  · have hd : 0 < Q.dep (Sum.inl (RelData.iterIdx F 0 (toData F R0) i₀)) :=
      Q.hdep (Sum.inl (RelData.iterIdx F 0 (toData F R0) i₀))
    have h2' : kAdmissible (Nat.card F)
        (Q.c (Sum.inl (RelData.iterIdx F 0 (toData F R0) i₀))) 2 := by
      simpa [m] using h2
    have hw' : weight (Q.dep (Sum.inl (RelData.iterIdx F 0 (toData F R0) i₀)))
        (Q.c (Sum.inl (RelData.iterIdx F 0 (toData F R0) i₀))) = w := by
      rw [hwm]
      exact hw
    exact admExpT_self F w 2 hd (Q.c (Sum.inl (RelData.iterIdx F 0 (toData F R0) i₀))) hw' h2'
  · have hf := q_type1_member_front_le F r s hcase hs1v h1 R0 hbhd
    have hm0 : pad0 m 0 ≤ Nat.card F := by
      dsimp [m]
      exact hf i₀
    have hdepth : Q.dep (Sum.inl (RelData.iterIdx F 0 (toData F R0) i₀)) = 1 →
        pad0 m 0 ≠ Nat.card F := by
      intro hd1 hq0
      have hw1 : weight (Q.dep (Sum.inl (RelData.iterIdx F 0 (toData F R0) i₀))) m = pad0 m 0 := by
        simpa [m] using weight_dep_one_eq_pad0
          (Q.c (Sum.inl (RelData.iterIdx F 0 (toData F R0) i₀))) hd1
      have hbigp : (Nat.card F : ℕ) < pad0 s 1 := by
        rw [pad0_of_lt s (by omega : 1 < r)]
        exact hbigv
      have hwg : Nat.card F + 2 ≤ weight r s := case1_weight_ge_q_add_two F s hcase hbigp
      have hwr : weight r s = Nat.card F := by
        calc weight r s = weight (Q.dep (Sum.inl (RelData.iterIdx F 0 (toData F R0) i₀))) m := hwm.symm
             _ = pad0 m 0 := hw1
             _ = Nat.card F := hq0
      omega
    have h1m : kAdmissible (Nat.card F) m 1 :=
      kAdm_one_iff_front (Nat.card F) m hm0 hdepth
    have hdrop : l2μ (Nat.card F) m < l2μ (Nat.card F) s := by
      exact l2_member_lt (q := Nat.card F) s m
        (Or.inl (by simpa [m] using (ht1 i₀ hi₀).2))
    have hwm' : weight (Q.dep (Sum.inl (RelData.iterIdx F 0 (toData F R0) i₀))) m = w := by
      rw [hwm]
      exact hw
    have hres := ih (Q.dep (Sum.inl (RelData.iterIdx F 0 (toData F R0) i₀))) m hwm' h1m h2 hdrop
    simpa [m] using hres

/-- Per-member e for the TYPE-2 family from package data (R0 hbhd ht2). -/


theorem q_type2_member_e_T_of (w : ℕ) (r : ℕ) (s : Fin r → ℕ+) (hw : weight r s = w)
    (hcase : 2 ≤ r) (hbigv : (Nat.card F : ℕ) < (s ⟨1, by omega⟩ : ℕ))
    (hs1v : (s ⟨0, by omega⟩ : ℕ) + 1 ≤ Nat.card F)
    (h1 : kAdmissible (Nat.card F) s 1)
    (R0 : BinaryRel F)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1)
    (ht2 : let D := RelData.BCqIter F 0 (toData F R0)
      let Bs := ofBstarOver F D (s ⟨0, by omega⟩) (fun e => BCqIter_valid F 0 R0 e)
          (RelData.iterate_merge_hv F 0 R0 (s ⟨0, by omega⟩) (by omega) hbhd)
      let Q := FixedOver.prependList F Bs (sPrefix r s 1 (by omega) (by omega))
      ∀ i : D.ιB,
        weight (Q.dep (Sum.inr (Sum.inl i))) (Q.c (Sum.inr (Sum.inl i))) = weight r s ∧
        psum (Q.c (Sum.inr (Sum.inl i))) 2 < psum s 2)
    (ih : ∀ (r' : ℕ) (m : Fin r' → ℕ+) (hm : weight r' m = w),
      kAdmissible (Nat.card F) m 1 → ¬ kAdmissible (Nat.card F) m 2 →
      l2μ (Nat.card F) m < l2μ (Nat.card F) s → AdmExpT F w 2 m) :
    let D := RelData.BCqIter F 0 (toData F R0)
    let Bs := ofBstarOver F D (s ⟨0, by omega⟩) (fun e => BCqIter_valid F 0 R0 e)
        (RelData.iterate_merge_hv F 0 R0 (s ⟨0, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s 1 (by omega) (by omega))
    ∀ i : D.ιB, AdmExpT F w 2 (Q.c (Sum.inr (Sum.inl i))) := by
  classical
  intro D Bs Q
  intro i
  let m : Fin (Q.dep (Sum.inr (Sum.inl i))) → ℕ+ := Q.c (Sum.inr (Sum.inl i))
  have hwm : weight (Q.dep (Sum.inr (Sum.inl i))) m = weight r s := by
    simpa [m] using (ht2 i).1
  by_cases h2 : kAdmissible (Nat.card F) m 2
  · have hd : 0 < Q.dep (Sum.inr (Sum.inl i)) := Q.hdep (Sum.inr (Sum.inl i))
    have h2' : kAdmissible (Nat.card F) (Q.c (Sum.inr (Sum.inl i))) 2 := by
      simpa [m] using h2
    have hw' : weight (Q.dep (Sum.inr (Sum.inl i))) (Q.c (Sum.inr (Sum.inl i))) = w := by
      rw [hwm]
      exact hw
    exact admExpT_self F w 2 hd (Q.c (Sum.inr (Sum.inl i))) hw' h2'
  · have hf := q_type2_member_front_le F r s hcase hs1v h1 R0 hbhd
    have hm0 : pad0 m 0 ≤ Nat.card F := by
      dsimp [m]
      exact hf i
    have hdepth : Q.dep (Sum.inr (Sum.inl i)) = 1 → pad0 m 0 ≠ Nat.card F := by
      intro hd1 hq0
      have hw1 : weight (Q.dep (Sum.inr (Sum.inl i))) m = pad0 m 0 := by
        simpa [m] using weight_dep_one_eq_pad0 (Q.c (Sum.inr (Sum.inl i))) hd1
      have hbigp : (Nat.card F : ℕ) < pad0 s 1 := by
        rw [pad0_of_lt s (by omega : 1 < r)]
        exact hbigv
      have hwg : Nat.card F + 2 ≤ weight r s := case1_weight_ge_q_add_two F s hcase hbigp
      have hwr : weight r s = Nat.card F := by
        calc weight r s = weight (Q.dep (Sum.inr (Sum.inl i))) m := hwm.symm
             _ = pad0 m 0 := hw1
             _ = Nat.card F := hq0
      omega
    have h1m : kAdmissible (Nat.card F) m 1 :=
      kAdm_one_iff_front (Nat.card F) m hm0 hdepth
    have hdrop : l2μ (Nat.card F) m < l2μ (Nat.card F) s := by
      exact l2_member_lt (q := Nat.card F) s m
        (Or.inl (by simpa [m] using (ht2 i).2))
    have hwm' : weight (Q.dep (Sum.inr (Sum.inl i))) m = w := by
      rw [hwm]
      exact hw
    have hres := ih (Q.dep (Sum.inr (Sum.inl i))) m hwm' h1m h2 hdrop
    simpa [m] using hres






end ZagierHoffmanPositiveChar
