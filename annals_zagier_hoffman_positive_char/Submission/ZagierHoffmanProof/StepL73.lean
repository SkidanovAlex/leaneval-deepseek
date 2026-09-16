import Submission.ZagierHoffmanProof.StepL72
import Submission.ZagierHoffmanProof.StepL61
import Submission.ZagierHoffmanProof.StepL62
/-!
# Step L73: main2_case1_j1 — the CASE-1 j = 1 splice (SESSION 225)

The in-domain (1-adm ∧ ¬2-adm) CASE-1 j = 1 recursion step of MAIN(2)-weak:
  ★ main2_case1_j1 (w s hw h1 hn2 hcase hbigp hs1qp ih) : AdmExp F w 2 s
    — rcases prop212_step1 (k = 2, j = 1) for the ζ-level identity
    ζ(s) + (guarded a-sum) + (type-2 sum) + (type-3 sum) = 0 (hrel); fold it by
    S1–S3 into ζ(s) = Σ_{i₀≠u ⊕ D.ιB ⊕ D.ιB} (−a)·ζ(member) (sum_guarded_subtype',
    eq_neg_add_add_add', neg_sum_sum_type' — universe-polymorphic copies of
    StepL61/62's lemmas, since K∞ outranks Type; neg_coe_mul_zeta for the sign);
    per-member e by the package-data dispatch q_type1/2/3_member_e_of (R0 (u)
    hbhd ht-conjunct as INPUT — the self-contained StepL71/72 versions re-rcase
    prop212 internally, giving R0s that are NOT defeq to the caller's own, so the
    main2 splice passes its own package data: 2-adm → admExp_self, ¬2-adm →
    1-adm (kAdm_one_iff_front) + l2μ drop (front/psum facts) → ih); splice by
    admExp_combine.
Each _of lemma's proof is StepL71/72's e-proof with the rcases replaced by the
given conjunct hypothesis.  NEXT: the j = 0 G5-closure (CASE-2 (q,q) and CASE-1
(q, s₂>q) at the TOP level — inside the recursion members of these forms are
handled by the IH, SESSION 203), then MAIN2-weak via l2_induction, A2-weak via
A2_with_main2, and theorem-A(w ≤ 3) re-check.  Named gates unchanged: m≥3
hierarchy, theorem_B/D.
-/

set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators
namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- S2: sign passes through the completion coefficient. -/
lemma neg_coe_mul_zeta (a : RatFunc F) {r : ℕ} (s : Fin r → ℕ+) :
    (((-a : RatFunc F) : RatFunc.CompletionAtInfty F) * ζ_A F s) =
      -(((a : RatFunc F) : RatFunc.CompletionAtInfty F) * ζ_A F s) := by
  have hc : ((-a : RatFunc F) : RatFunc.CompletionAtInfty F) =
      -((a : RatFunc F) : RatFunc.CompletionAtInfty F) := by
    change (algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F) (-a)) =
      - (algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F) a)
    rw [map_neg]
  rw [hc]
  rw [neg_mul]

/-- Universe-polymorphic copy of StepL62's fold lemmas (K may exceed Type). -/
lemma eq_neg_add_add_add' {K : Type*} [AddCommGroup K] (z A B C : K) (h : z + A + B + C = 0) :
    z = -A + -B + -C := by
  have h' : z + (A + B + C) = 0 := by simpa [add_assoc] using h
  have hz : z = -(A + B + C) := eq_neg_of_add_eq_zero_left h'
  rw [hz]
  abel

open scoped BigOperators
/-- Universe-polymorphic S1 copy (guarded sum → subtype sum). -/
lemma sum_guarded_subtype' {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Type*} [AddCommMonoid M] (u : ι) (f : ι → M) :
    letI : Fintype {i : ι // i ≠ u} :=
      Fintype.subtype ((Finset.univ : Finset ι).filter (fun i => i ≠ u))
        (by intro x; simp [Finset.mem_filter])
    (∑ i : ι, (if i = u then 0 else f i)) = ∑ i : {i : ι // i ≠ u}, f i := by
  classical
  let inst : Fintype {i : ι // i ≠ u} :=
    Fintype.subtype ((Finset.univ : Finset ι).filter (fun i => i ≠ u))
      (by intro x; simp [Finset.mem_filter])
  letI : Fintype {i : ι // i ≠ u} := inst
  let g : ι → M := fun i => if i = u then 0 else f i
  have hs := Finset.sum_erase_add (s := (Finset.univ : Finset ι)) (f := g) (a := u) (Finset.mem_univ u)
  have h2 : (∑ x ∈ (Finset.univ : Finset ι).erase u, g x) =
      ∑ x ∈ (Finset.univ : Finset ι).erase u, f x := by
    apply Finset.sum_congr rfl
    intro x hx
    have hxu : x ≠ u := (Finset.mem_erase.mp hx).1
    simp [g, hxu]
  have h1 : (∑ i : ι, g i) = ∑ i ∈ (Finset.univ : Finset ι).erase u, f i := by
    rw [← hs]
    rw [h2]
    simp [g]
  have hfil : (Finset.univ : Finset ι).filter (fun i => i ≠ u) = (Finset.univ : Finset ι).erase u := by
    ext i
    simp
  have hsum : (∑ x ∈ (Finset.univ : Finset ι).filter (fun i => i ≠ u), f x) =
      ∑ x : {i : ι // i ≠ u}, f x := by
    exact @Finset.sum_subtype ι M _ (fun i : ι => i ≠ u) inst
      ((Finset.univ : Finset ι).filter (fun i => i ≠ u)) (by intro x; simp [Finset.mem_filter]) f
  calc
    (∑ i : ι, (if i = u then 0 else f i)) = ∑ i : ι, g i := by rfl
    _ = ∑ i ∈ (Finset.univ : Finset ι).erase u, f i := h1
    _ = ∑ i ∈ (Finset.univ : Finset ι).filter (fun i => i ≠ u), f i := by
          rw [hfil]
    _ = ∑ i : {i : ι // i ≠ u}, f i := hsum

open scoped BigOperators
/-- Universe-polymorphic S3 assembly (negated three sums → sum-type sum). -/
lemma neg_sum_sum_type' {ι₁ ι₂ ι₃ : Type*} [Fintype ι₁] [Fintype ι₂] [Fintype ι₃]
    {K : Type*} [AddCommGroup K] (x₁ : ι₁ → K) (x₂ : ι₂ → K) (x₃ : ι₃ → K) :
    -(∑ i : ι₁, x₁ i) + -(∑ i : ι₂, x₂ i) + -(∑ i : ι₃, x₃ i) =
      ∑ p : ι₁ ⊕ ι₂ ⊕ ι₃, (match p with
        | Sum.inl a => -x₁ a | Sum.inr (Sum.inl b) => -x₂ b | Sum.inr (Sum.inr c) => -x₃ c) := by
  classical
  rw [Fintype.sum_sum_type]
  rw [Fintype.sum_sum_type]
  simp [Finset.sum_neg_distrib]
  abel

/-- Per-member e for the TYPE-3 family from package data (R0 hbhd ht3): 2-adm →
self; ¬2-adm → in-domain with l2μ drop (front growth) → ih. -/
theorem q_type3_member_e_of (w : ℕ) (r : ℕ) (s : Fin r → ℕ+) (hw : weight r s = w)
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
      l2μ (Nat.card F) m < l2μ (Nat.card F) s → AdmExp F w 2 m) :
    let D := RelData.BCqIter F 0 (toData F R0)
    let Bs := ofBstarOver F D (s ⟨0, by omega⟩) (fun e => BCqIter_valid F 0 R0 e)
        (RelData.iterate_merge_hv F 0 R0 (s ⟨0, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s 1 (by omega) (by omega))
    ∀ i : D.ιB, AdmExp F w 2 (Q.c (Sum.inr (Sum.inr i))) := by
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
    exact admExp_self F w 2 hd (Q.c (Sum.inr (Sum.inr i))) hw' h2'
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
theorem q_type1_member_e_of (w : ℕ) (r : ℕ) (s : Fin r → ℕ+) (hw : weight r s = w)
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
      l2μ (Nat.card F) m < l2μ (Nat.card F) s → AdmExp F w 2 m) :
    let D := RelData.BCqIter F 0 (toData F R0)
    let Bs := ofBstarOver F D (s ⟨0, by omega⟩) (fun e => BCqIter_valid F 0 R0 e)
        (RelData.iterate_merge_hv F 0 R0 (s ⟨0, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s 1 (by omega) (by omega))
    ∀ i₀ : R0.ιA, i₀ ≠ u → AdmExp F w 2
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
    exact admExp_self F w 2 hd (Q.c (Sum.inl (RelData.iterIdx F 0 (toData F R0) i₀))) hw' h2'
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
theorem q_type2_member_e_of (w : ℕ) (r : ℕ) (s : Fin r → ℕ+) (hw : weight r s = w)
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
      l2μ (Nat.card F) m < l2μ (Nat.card F) s → AdmExp F w 2 m) :
    let D := RelData.BCqIter F 0 (toData F R0)
    let Bs := ofBstarOver F D (s ⟨0, by omega⟩) (fun e => BCqIter_valid F 0 R0 e)
        (RelData.iterate_merge_hv F 0 R0 (s ⟨0, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s 1 (by omega) (by omega))
    ∀ i : D.ιB, AdmExp F w 2 (Q.c (Sum.inr (Sum.inl i))) := by
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
    exact admExp_self F w 2 hd (Q.c (Sum.inr (Sum.inl i))) hw' h2'
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





theorem main2_case1_j1 (w : ℕ) {r : ℕ} (s : Fin r → ℕ+) (hw : weight r s = w)
    (h1 : kAdmissible (Nat.card F) s 1) (hn2 : ¬ kAdmissible (Nat.card F) s 2)
    (hcase : 2 ≤ r) (hbigp : (Nat.card F : ℕ) < pad0 s 1) (hs1qp : pad0 s 0 < Nat.card F)
    (ih : ∀ (r' : ℕ) (m : Fin r' → ℕ+) (hm : weight r' m = w),
      kAdmissible (Nat.card F) m 1 → ¬ kAdmissible (Nat.card F) m 2 →
      l2μ (Nat.card F) m < l2μ (Nat.card F) s → AdmExp F w 2 m) :
    AdmExp F w 2 s := by
  classical
  have hbigv : (Nat.card F : ℕ) < (s ⟨1, by omega⟩ : ℕ) := case1_pad0_big_of_value F s hcase hbigp
  have hs1v : (s ⟨0, by omega⟩ : ℕ) < Nat.card F := case1_pad0_head_of_value F s (by omega : 0 < r) hs1qp
  have hs1v' : (s ⟨0, by omega⟩ : ℕ) + 1 ≤ Nat.card F := by omega
  have hP := prop212_step1 F r s 2 1 (by omega : 1 ≤ 2) hcase (by omega : 1 ≤ 1)
    (by omega : 1 ≤ 2 - 1) hbigv hs1v (fun i hi1 hi0 => by omega)
    (fun x hx => by
      have hx0 : x = 0 := by omega
      subst x
      exact h1.1 0 (by omega))
  rcases hP with ⟨R0, u, hbhd, haa, hdepu, hbstar, hrel, ht1, ht2, ht3⟩
  let D := RelData.BCqIter F 0 (toData F R0)
  let Bs := ofBstarOver F D (s ⟨0, by omega⟩) (fun e => BCqIter_valid F 0 R0 e)
        (RelData.iterate_merge_hv F 0 R0 (s ⟨0, by omega⟩) (by omega) hbhd)
  let Q := FixedOver.prependList F Bs (sPrefix r s 1 (by omega) (by omega))
  -- expansion family
  let ι₁ : Type := {i₀ : R0.ιA // i₀ ≠ u}
  let ι₂ : Type := D.ιB
  let ι₃ : Type := D.ιB
  let ι : Type := ι₁ ⊕ (ι₂ ⊕ ι₃)
  let inst₁ : Fintype ι₁ :=
    Fintype.subtype ((Finset.univ : Finset R0.ιA).filter (fun i₀ => i₀ ≠ u))
      (by intro x; simp [Finset.mem_filter])
  letI : Fintype ι₁ := inst₁
  let mdep (p : ι) : ℕ := match p with
    | Sum.inl q => Q.dep (Sum.inl (RelData.iterIdx F 0 (toData F R0) q.1))
    | Sum.inr (Sum.inl i) => Q.dep (Sum.inr (Sum.inl i))
    | Sum.inr (Sum.inr i) => Q.dep (Sum.inr (Sum.inr i))
  let mhdep (p : ι) : 0 < mdep p := by
    dsimp [mdep]
    cases p with
    | inl q => exact Q.hdep (Sum.inl (RelData.iterIdx F 0 (toData F R0) q.1))
    | inr s => cases s with
      | inl i => exact Q.hdep (Sum.inr (Sum.inl i))
      | inr i => exact Q.hdep (Sum.inr (Sum.inr i))
  let mc (p : ι) : Fin (mdep p) → ℕ+ := match p with
    | Sum.inl q => Q.c (Sum.inl (RelData.iterIdx F 0 (toData F R0) q.1))
    | Sum.inr (Sum.inl i) => Q.c (Sum.inr (Sum.inl i))
    | Sum.inr (Sum.inr i) => Q.c (Sum.inr (Sum.inr i))
  let ma (p : ι) : RatFunc F := match p with
    | Sum.inl q => -(Q.a (Sum.inl (RelData.iterIdx F 0 (toData F R0) q.1)))
    | Sum.inr (Sum.inl i) => -(Q.a (Sum.inr (Sum.inl i)))
    | Sum.inr (Sum.inr i) => -(Q.a (Sum.inr (Sum.inr i)))
  -- the three K∞ sums of the identity
  let A : RatFunc.CompletionAtInfty F :=
    ∑ i₀ : R0.ιA, (if i₀ = u then 0 else
      (((Q.a (Sum.inl (RelData.iterIdx F 0 (toData F R0) i₀)) : RatFunc F) : RatFunc.CompletionAtInfty F) *
        ζ_A F (Q.c (Sum.inl (RelData.iterIdx F 0 (toData F R0) i₀)))))
  let B : RatFunc.CompletionAtInfty F :=
    ∑ i : D.ιB, (((Q.a (Sum.inr (Sum.inl i)) : RatFunc F) : RatFunc.CompletionAtInfty F) *
      ζ_A F (Q.c (Sum.inr (Sum.inl i))))
  let C : RatFunc.CompletionAtInfty F :=
    ∑ i : D.ιB, (((Q.a (Sum.inr (Sum.inr i)) : RatFunc F) : RatFunc.CompletionAtInfty F) *
      ζ_A F (Q.c (Sum.inr (Sum.inr i))))
  have hrel' : ζ_A F s + A + B + C = 0 := by
    dsimp [A, B, C, Q, Bs, D]
    exact hrel
  have hid3 : ζ_A F s = -A + -B + -C := eq_neg_add_add_add' (ζ_A F s) A B C hrel'
  let x₁ (p : ι₁) : RatFunc.CompletionAtInfty F :=
    (((Q.a (Sum.inl (RelData.iterIdx F 0 (toData F R0) p.1)) : RatFunc F) : RatFunc.CompletionAtInfty F) *
      ζ_A F (Q.c (Sum.inl (RelData.iterIdx F 0 (toData F R0) p.1))))
  let x₂ (i : ι₂) : RatFunc.CompletionAtInfty F :=
    (((Q.a (Sum.inr (Sum.inl i)) : RatFunc F) : RatFunc.CompletionAtInfty F) * ζ_A F (Q.c (Sum.inr (Sum.inl i))))
  let x₃ (i : ι₃) : RatFunc.CompletionAtInfty F :=
    (((Q.a (Sum.inr (Sum.inr i)) : RatFunc F) : RatFunc.CompletionAtInfty F) * ζ_A F (Q.c (Sum.inr (Sum.inr i))))
  have hA : A = ∑ p : ι₁, x₁ p := by
    dsimp [A, x₁]
    exact sum_guarded_subtype' (u := u)
      (f := fun i₀ : R0.ιA => (((Q.a (Sum.inl (RelData.iterIdx F 0 (toData F R0) i₀)) : RatFunc F) : RatFunc.CompletionAtInfty F) *
        ζ_A F (Q.c (Sum.inl (RelData.iterIdx F 0 (toData F R0) i₀)))))
  rw [hA] at hid3
  have hid3' : ζ_A F s = ∑ p : ι,
      (match p with
       | Sum.inl q => -(x₁ q)
       | Sum.inr (Sum.inl i) => -(x₂ i)
       | Sum.inr (Sum.inr i) => -(x₃ i)) := by
    calc
      ζ_A F s = -(∑ p : ι₁, x₁ p) + -(∑ i : ι₂, x₂ i) + -(∑ i : ι₃, x₃ i) := by
        simpa [x₂, x₃] using hid3
      _ = ∑ p : ι, (match p with
           | Sum.inl q => -(x₁ q)
           | Sum.inr (Sum.inl i) => -(x₂ i)
           | Sum.inr (Sum.inr i) => -(x₃ i)) := by
        exact neg_sum_sum_type' x₁ x₂ x₃
  have hid : ζ_A F s = ∑ p : ι, (((ma p : RatFunc F) : RatFunc.CompletionAtInfty F) * ζ_A F (mc p)) := by
    rw [hid3']
    apply Finset.sum_congr rfl
    intro p hp
    cases p with
    | inl q =>
        dsimp [x₁, ma, mc]
        exact (neg_coe_mul_zeta F (Q.a (Sum.inl (RelData.iterIdx F 0 (toData F R0) q.1)))
          (Q.c (Sum.inl (RelData.iterIdx F 0 (toData F R0) q.1)))).symm
    | inr s =>
        cases s with
        | inl i =>
            dsimp [x₂, ma, mc]
            exact (neg_coe_mul_zeta F (Q.a (Sum.inr (Sum.inl i))) (Q.c (Sum.inr (Sum.inl i)))).symm
        | inr i =>
            dsimp [x₃, ma, mc]
            exact (neg_coe_mul_zeta F (Q.a (Sum.inr (Sum.inr i))) (Q.c (Sum.inr (Sum.inr i)))).symm
  -- per-member expansions from the package data
  have e : ∀ p : ι, AdmExp F w 2 (mc p) := by
    intro p
    cases p with
    | inl q =>
        exact q_type1_member_e_of F w r s hw hcase hbigv hs1v' h1 R0 u hbhd ht1 ih q.1 q.2
    | inr s =>
        cases s with
        | inl i => exact q_type2_member_e_of F w r s hw hcase hbigv hs1v' h1 R0 hbhd ht2 ih i
        | inr i => exact q_type3_member_e_of F w r s hw hcase hbigv hs1v' h1 R0 hbhd ht3 ih i
  exact admExp_combine F w 2 s mdep mhdep mc ma hid e

end ZagierHoffmanPositiveChar
