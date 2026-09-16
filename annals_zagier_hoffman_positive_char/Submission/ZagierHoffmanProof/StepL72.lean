import Submission.ZagierHoffmanProof.StepL71
set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators
/-!
# Step L72: per-member e for the TYPE-1 and TYPE-2 families (SESSION 225)

With StepL71's type-3 per-member e, the CASE-1 j = 1 per-member dispatch of
main2_case1_j1 is complete:
  ★ q_type1_member_e (… ih) : ∃ R0 u hbhd, ∀ i₀ : R0.ιA, i₀ ≠ u →
      AdmExp F w 2 (Q.c (Sum.inl (RelData.iterIdx F 0 (toData F R0) i₀)))
      — the guarded a-side family (weight w via ht1, strict prefix-2 drop via ht1);
  ★ q_type2_member_e (… ih) : ∃ R0 hbhd, ∀ i : D.ιB,
      AdmExp F w 2 (Q.c (Sum.inr (Sum.inl i)))  — the inl b-side family.
Both follow the StepL71 template: by_cases 2-adm (admExp_self) / ¬2-adm
(in-domain: 1-adm via kAdm_one_iff_front from the front pad0 (member) 0 = s₁ ≤ q
(q_type1/2_member_front_le, StepL69); depth-1 exclusion by
weight_dep_one_eq_pad0 (StepL70) + case1_weight_ge_q_add_two (StepL68): dep = 1
would force weight = pad0 = s₁ ≤ q, contradicting weight = w ≥ q+2) with the l2μ
drop from the strict prefix-2 drop (l2_member_lt, Or.inl) → ih.
NEXT: main2_case1_j1 — rcases prop212_step1 once (hrel = the ζ-identity), fold
hrel by S1–S3 (sum_guarded_subtype / neg_coe_mul_zeta / eq_neg_add_add_add /
neg_sum_sum_type, StepL61/62) into ζ(s) = Σ_{i₀≠u ⊕ D.ιB ⊕ D.ιB} (−a)·ζ(c), per
member e via q_type1/2/3_member_e (their R0/u/hbhd agree with the package's by
determinism of lemma_2_9_config_data — proof-irrelevant args), splice by
admExp_combine.  Named gates unchanged: j=0 G5 chains, m≥3 hierarchy, theorem_B/D.
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- Per-member e for the TYPE-1 family (guarded a-side i₀ ≠ u): 2-adm → self;
¬2-adm → in-domain (1-adm via front ≤ q, depth-1 excluded by weight ≥ q+2) with the
strict prefix-2 drop (ht1) → ih. -/
theorem q_type1_member_e (w : ℕ) (r : ℕ) (s : Fin r → ℕ+) (hw : weight r s = w)
    (hcase : 2 ≤ r) (hbigv : (Nat.card F : ℕ) < (s ⟨1, by omega⟩ : ℕ))
    (hs1v : (s ⟨0, by omega⟩ : ℕ) + 1 ≤ Nat.card F)
    (h1 : kAdmissible (Nat.card F) s 1)
    (ih : ∀ (r' : ℕ) (m : Fin r' → ℕ+) (hm : weight r' m = w),
      kAdmissible (Nat.card F) m 1 → ¬ kAdmissible (Nat.card F) m 2 →
      l2μ (Nat.card F) m < l2μ (Nat.card F) s → AdmExp F w 2 m) :
    ∃ (R0 : BinaryRel F) (u : R0.ιA)
      (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1),
      let D := RelData.BCqIter F 0 (toData F R0)
      let Bs := ofBstarOver F D (s ⟨0, by omega⟩) (fun e => BCqIter_valid F 0 R0 e)
          (RelData.iterate_merge_hv F 0 R0 (s ⟨0, by omega⟩) (by omega) hbhd)
      let Q := FixedOver.prependList F Bs (sPrefix r s 1 (by omega) (by omega))
      ∀ i₀ : R0.ιA, i₀ ≠ u → AdmExp F w 2
        (Q.c (Sum.inl (RelData.iterIdx F 0 (toData F R0) i₀))) := by
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
  have hP := prop212_step1 F r s 2 1 hk1 hcase hj1 hjk hbigv hsj
    (fun i hi1 hi0 => by omega) hsleq
  rcases hP with ⟨R0, u, hbhd, haa, hdepu, hbstar, hrel, ht1, ht2, ht3⟩
  refine ⟨R0, u, hbhd, ?_⟩
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
    exact admExp_self F w 2 hd (Q.c (Sum.inl (RelData.iterIdx F 0 (toData F R0) i₀))) hw' h2'
  · -- ¬2-adm: 1-adm + l2μ drop → ih
    have hf := q_type1_member_front_le F r s hcase hs1v h1 R0 hbhd
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

/-- Per-member e for the TYPE-2 family (inl b-side): 2-adm → self; ¬2-adm →
in-domain (1-adm via front ≤ q, depth-1 excluded by weight ≥ q+2) with the strict
prefix-2 drop (ht2) → ih. -/
theorem q_type2_member_e (w : ℕ) (r : ℕ) (s : Fin r → ℕ+) (hw : weight r s = w)
    (hcase : 2 ≤ r) (hbigv : (Nat.card F : ℕ) < (s ⟨1, by omega⟩ : ℕ))
    (hs1v : (s ⟨0, by omega⟩ : ℕ) + 1 ≤ Nat.card F)
    (h1 : kAdmissible (Nat.card F) s 1)
    (ih : ∀ (r' : ℕ) (m : Fin r' → ℕ+) (hm : weight r' m = w),
      kAdmissible (Nat.card F) m 1 → ¬ kAdmissible (Nat.card F) m 2 →
      l2μ (Nat.card F) m < l2μ (Nat.card F) s → AdmExp F w 2 m) :
    ∃ (R0 : BinaryRel F)
      (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1),
      let D := RelData.BCqIter F 0 (toData F R0)
      let Bs := ofBstarOver F D (s ⟨0, by omega⟩) (fun e => BCqIter_valid F 0 R0 e)
          (RelData.iterate_merge_hv F 0 R0 (s ⟨0, by omega⟩) (by omega) hbhd)
      let Q := FixedOver.prependList F Bs (sPrefix r s 1 (by omega) (by omega))
      ∀ i : D.ιB, AdmExp F w 2 (Q.c (Sum.inr (Sum.inl i))) := by
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
  have hP := prop212_step1 F r s 2 1 hk1 hcase hj1 hjk hbigv hsj
    (fun i hi1 hi0 => by omega) hsleq
  rcases hP with ⟨R0, u, hbhd, haa, hdepu, hbstar, hrel, ht1, ht2, ht3⟩
  refine ⟨R0, hbhd, ?_⟩
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
    exact admExp_self F w 2 hd (Q.c (Sum.inr (Sum.inl i))) hw' h2'
  · -- ¬2-adm: 1-adm + l2μ drop → ih
    have hf := q_type2_member_front_le F r s hcase hs1v h1 R0 hbhd
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
