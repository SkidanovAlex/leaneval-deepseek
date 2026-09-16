import Submission.ZagierHoffmanProof.StepL98
import Submission.ZagierHoffmanProof.StepL56
import Submission.ZagierHoffmanProof.StepL48
import Submission.ZagierHoffmanProof.StepL47
set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators
/-!
# Step L99: ★ main2T_case1_j1 — the strengthened (2,1) CASE-1 splice at level 2

theorem main2T_case1_j1 (w r s hw) (hcase2 : 2 ≤ r) (hbigv : q < s⟨1⟩)
(hs0lt : s₀ < q) (h1 : kAdm q s 1) (hn2 : ¬ kAdm q s 2)
(rec : ∀ r' m hm, l2μ q m < l2μ q s → kAdm q m 1 → ¬ kAdm q m 2 →
  AdmExpT F w 2 m) : AdmExpT F w 2 s
— every level-2 in-domain CASE-1 j=1 tuple (2 ≤ depth, s₁ > q, s₀ < q) expands
at level 2 WITH prefix orders.  main2T_case1_j1 is main3_case1_j1's architecture
transplanted to k=2: ONE rcases of lemma_2_9_rel at (r−2, w1Of-at-2, sTail-at-2)
(keeps hleA/hleB); hwtA/hhead/hXw/hbndB/hpref calcs at k=2 (hnorm s⟨2−1⟩=s⟨1⟩);
the ζ-identity zeta_214_reindexed at (2,1) (hmid vacuous); the 3-family hid fold
(A/B/C guarded sums, eq_neg_add_add_add' + sum_guarded_subtype' +
neg_sum_sum_type' + neg_coe_mul_zeta); the per-member dispatch data ht1/ht2/ht3
(type1/2/3_weight_eq + type1/2_psum_lt_k + type3_psum_k_le_X-with-lemma29_X1_le +
type3_Init_gt, all at (2,1)); per-member e via StepL98's q_type{1,2,3}_member_e_T_of
(2-adm → admExpT_self / ¬2-adm → 1-adm + l2μ drop → rec); horder (ℓ ≥ 2)
via type1_psum_decompose_ge + hpref + lemma29_qExp_telescope (k=2) for type-1,
the ht2 strict drop at ℓ=2 and type2_psum_ge_k_lt for ℓ ≥ 3, and
type3_psum_ge_k_le for type-3; ℓ > r by weight saturation; splice by
admExpT_combine F w 2.  (Adaptation note: the k=3→k=2 text transplant needed
s⟨2⟩→s⟨1⟩, (3−1)→(2−1), r−3→r−2, w1Of_add F r s 3→2,
iterate_merge_hv F 1→F 0, psum s 3→psum s 2; hsleq from h1; hmid vacuous.)
NEXT: main2T = l2_induction + A2_case2 + the strengthened G5T chains.
theorem_B/D remain ABP-gated (no route).
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

theorem main2T_case1_j1 (w : ℕ) (r : ℕ) (s : Fin r → ℕ+) (hw : weight r s = w)
    (hcase2 : 2 ≤ r) (hbigv : (Nat.card F : ℕ) < (s ⟨1, by omega⟩ : ℕ))
    (hs0lt : (s ⟨0, by omega⟩ : ℕ) < Nat.card F)
    (h1 : kAdmissible (Nat.card F) s 1) (hn2 : ¬ kAdmissible (Nat.card F) s 2)
    (rec : ∀ (r' : ℕ) (m : Fin r' → ℕ+) (hm : weight r' m = w),
      l2μ (Nat.card F) m < l2μ (Nat.card F) s → kAdmissible (Nat.card F) m 1 →
      ¬ kAdmissible (Nat.card F) m 2 → AdmExpT F w 2 m) :
    AdmExpT F w 2 s := by
  classical
  have hmid : ∀ i : Fin r, (1 : ℕ) ≤ (i : ℕ) → (i : ℕ) < 1 → (s i : ℕ) = Nat.card F := by
    intro i hi1 hi2
    omega
  have hsleq : ∀ x : ℕ, x < 2 - 1 → pad0 s x ≤ Nat.card F := by
    intro x hx
    have hx0 : x = 0 := by omega
    subst x
    exact h1.1 0 (by omega)
  have hsum : psum s 2 = psum s (2 - 1) + (s ⟨1, by omega⟩ : ℕ) := by
    have hpl := psum_last r s 2 (by omega : 1 ≤ 2) hcase2
    simpa using hpl
  have hmono : psum s 2 ≤ psum s r := psum_mono s hcase2
  have hmono2 : psum s (2 - 1) ≤ psum s r := psum_mono s (by omega : 2 - 1 ≤ r)
  have hq1 : 1 ≤ Nat.card F := by
    have h2 : 2 ≤ Nat.card F := card_ge_two F
    omega
  let w1 : ℕ+ := w1Of F r s 2 (by omega : 1 ≤ 2) hcase2 hbigv
  let B : Fin (r - 2) → ℕ+ := sTail r s 2 hcase2
  rcases lemma_2_9_rel F (r - 2) w1 B with ⟨R0, u, hdep, ha, hc, hleA, hbhd, hleB, hvalid⟩
  have hdepu : R0.depA u = (r - 2) + 1 := hdep
  have hau : R0.aA u = 1 := ha
  have hc0 : ∀ hd : R0.depA u = (r - 2) + 1,
      (fun x : Fin ((r - 2) + 1) => R0.cA u (Fin.cast hd.symm x)) =
        bstarBase F r s 2 (by omega : 1 ≤ 2) hcase2 hbigv := by
    intro hd
    simpa [bstarBase, w1, B] using hc hd
  have hwtA : ∀ i : R0.ιA, i ≠ u → weight (R0.depA i) (R0.cA i) = psum s r - psum s (2 - 1) := by
    intro i hi
    have hL := hleA i hi
    have hw' : (w1 : ℕ) = (s ⟨2 - 1, by omega⟩ : ℕ) - Nat.card F := by
      dsimp [w1]
      rfl
    calc
      weight (R0.depA i) (R0.cA i)
          = weight 1 (single (qExp F)) + weight ((r - 2) + 1) (consVec w1 B) := hL.1.1
      _ = (qExp F : ℕ) + ((w1 : ℕ) + weight (r - 2) B) := by
            rw [weight_single]
            rw [weight_consVec]
      _ = Nat.card F + ((w1 : ℕ) + (psum s r - psum s 2)) := by
            rw [show (qExp F : ℕ) = Nat.card F by rfl]
            rw [weight_sTail r s 2 hcase2]
      _ = psum s r - psum s (2 - 1) := by
            rw [hw']
            have hnorm : (s ⟨2 - 1, by omega⟩ : ℕ) = (s ⟨1, by omega⟩ : ℕ) := by rfl
            rw [hnorm]
            omega
  have hhead : ∀ i : R0.ιA, i ≠ u →
      ((R0.cA i) ⟨0, R0.hdepA i⟩ : ℕ) < (s ⟨2 - 1, by omega⟩ : ℕ) := by
    intro i hi
    have hL2 := (hleA i hi).2
    have hwadd : (qExp F : ℕ) + (w1 : ℕ) = (s ⟨1, by omega⟩ : ℕ) := by
      dsimp [w1]
      exact w1Of_add F r s 2 (by omega : 1 ≤ 2) hcase2 hbigv
    have hL2' : ((R0.cA i) ⟨0, R0.hdepA i⟩ : ℕ) < (s ⟨1, by omega⟩ : ℕ) := by
      simpa [hwadd] using hL2
    have hnorm : (s ⟨2 - 1, by omega⟩ : ℕ) = (s ⟨1, by omega⟩ : ℕ) := by rfl
    rw [hnorm]
    exact hL2'
  have hXw : ∀ j' : R0.ιB, weight (R0.depB j' - 1) (expTail (R0.cB j')) =
      psum s r - psum s (2 - 1) - 1 := by
    intro j'
    have hL := hleB j'
    have hw' : (w1 : ℕ) = (s ⟨2 - 1, by omega⟩ : ℕ) - Nat.card F := by
      dsimp [w1]
      rfl
    calc
      weight (R0.depB j' - 1) (expTail (R0.cB j'))
          = weight 1 (single (qMinusExp F)) + weight ((r - 2) + 1) (consVec w1 B) := hL.1
      _ = (qMinusExp F : ℕ) + ((w1 : ℕ) + weight (r - 2) B) := by
            rw [weight_single]
            rw [weight_consVec]
      _ = (Nat.card F - 1) + ((w1 : ℕ) + (psum s r - psum s 2)) := by
            rw [show (qMinusExp F : ℕ) = Nat.card F - 1 by rfl]
            rw [weight_sTail r s 2 hcase2]
      _ = psum s r - psum s (2 - 1) - 1 := by
            rw [hw']
            have hnorm : (s ⟨2 - 1, by omega⟩ : ℕ) = (s ⟨1, by omega⟩ : ℕ) := by rfl
            rw [hnorm]
            omega
  have hbndB : ∀ j' : R0.ιB, ∀ m : ℕ,
      psum (expTail (R0.cB j')) m ≤ psumSeq (tupPadSum (single (qMinusExp F))
        (consVec (w1Of F r s 2 (by omega : 1 ≤ 2) hcase2 hbigv) (sTail r s 2 hcase2))) m := by
    intro j' m
    have hL := hleB j'
    simpa [w1, B] using (hL.2 m)
  have hpref : ∀ i : R0.ιA, i ≠ u → ∀ m : ℕ,
      psum (R0.cA i) m ≤ psumSeq (tupPadSum (single (qExp F))
        (consVec (w1Of F r s 2 (by omega : 1 ≤ 2) hcase2 hbigv) (sTail r s 2 hcase2))) m := by
    intro i hi m
    have hL := (hleA i hi).1
    simpa [w1, B] using (hL.2 m)
  -- the (2.14) chain ζ-identity at (3, 1) (zeta_214_reindexed packages it)
  have hz := zeta_214_reindexed F r s 2 1 (by omega : 1 ≤ 2) hcase2 (by omega : 1 ≤ 1)
    (by omega : 1 ≤ 2 - 1) hbigv hs0lt hmid R0 u hau hdepu hc0 hbhd

  let D := RelData.BCqIter F 0 (toData F R0)
  let Bs := ofBstarOver F D (s ⟨0, by omega⟩) (fun e => BCqIter_valid F 0 R0 e)
        (RelData.iterate_merge_hv F 0 R0 (s ⟨0, by omega⟩) (by omega) hbhd)
  let Q := FixedOver.prependList F Bs (sPrefix r s 1 (by omega) (by omega))
  have hid0 : ζ_A F s +
      (∑ i₀ : R0.ιA, (if i₀ = u then 0 else
        (((Q.a (Sum.inl (RelData.iterIdx F 0 (toData F R0) i₀)) : RatFunc F) : RatFunc.CompletionAtInfty F) *
          ζ_A F (Q.c (Sum.inl (RelData.iterIdx F 0 (toData F R0) i₀)))))) +
      (∑ i : D.ιB, (((Q.a (Sum.inr (Sum.inl i)) : RatFunc F) : RatFunc.CompletionAtInfty F) *
          ζ_A F (Q.c (Sum.inr (Sum.inl i))))) +
      (∑ i : D.ιB, (((Q.a (Sum.inr (Sum.inr i)) : RatFunc F) : RatFunc.CompletionAtInfty F) *
          ζ_A F (Q.c (Sum.inr (Sum.inr i))))) = 0 := by
    simpa [D, Bs, Q] using hz
  -- expansion family (the main2_case1_j1 3-part fold at level 3)
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
    exact hid0
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
  -- per-member dispatch data (level-2 ht-conjuncts over the rcases'd package)
  have hs1v' : (s ⟨0, by omega⟩ : ℕ) + 1 ≤ Nat.card F := by omega
  have ih : ∀ (r' : ℕ) (m : Fin r' → ℕ+) (hm : weight r' m = w),
      kAdmissible (Nat.card F) m 1 → ¬ kAdmissible (Nat.card F) m 2 →
      l2μ (Nat.card F) m < l2μ (Nat.card F) s → AdmExpT F w 2 m := by
    intro r' m hm h1m h2m hdrop
    exact rec r' m hm hdrop h1m h2m
  have ht1 : let D := RelData.BCqIter F 0 (toData F R0)
      let Bs := ofBstarOver F D (s ⟨0, by omega⟩) (fun e => BCqIter_valid F 0 R0 e)
          (RelData.iterate_merge_hv F 0 R0 (s ⟨0, by omega⟩) (by omega) hbhd)
      let Q := FixedOver.prependList F Bs (sPrefix r s 1 (by omega) (by omega))
      ∀ i₀ : R0.ιA, i₀ ≠ u →
        weight (Q.dep (Sum.inl (RelData.iterIdx F 0 (toData F R0) i₀)))
            (Q.c (Sum.inl (RelData.iterIdx F 0 (toData F R0) i₀))) = weight r s ∧
        psum (Q.c (Sum.inl (RelData.iterIdx F 0 (toData F R0) i₀))) 2 < psum s 2 := by
    intro D Bs Q i₀ hi₀
    have hwq := type1_weight_eq F r s 2 1 (by omega : 1 ≤ 2) hcase2 (by omega : 1 ≤ 1)
      (by omega : 1 ≤ 2 - 1) hbigv hs0lt hmid R0 hbhd i₀ (hwtA i₀ hi₀)
    have hdrop := type1_psum_lt_k F r s 2 1 (by omega : 1 ≤ 2) hcase2 (by omega : 1 ≤ 1)
      (by omega : 1 ≤ 2 - 1) hbigv hs0lt hmid R0 hbhd i₀ (hhead i₀ hi₀)
    constructor
    · exact hwq
    · exact hdrop
  have ht2 : let D := RelData.BCqIter F 0 (toData F R0)
      let Bs := ofBstarOver F D (s ⟨0, by omega⟩) (fun e => BCqIter_valid F 0 R0 e)
          (RelData.iterate_merge_hv F 0 R0 (s ⟨0, by omega⟩) (by omega) hbhd)
      let Q := FixedOver.prependList F Bs (sPrefix r s 1 (by omega) (by omega))
      ∀ i : D.ιB,
        weight (Q.dep (Sum.inr (Sum.inl i))) (Q.c (Sum.inr (Sum.inl i))) = weight r s ∧
        psum (Q.c (Sum.inr (Sum.inl i))) 2 < psum s 2 := by
    intro D Bs Q i
    have hwq := type2_weight_eq F r s 2 1 (by omega : 1 ≤ 2) hcase2 (by omega : 1 ≤ 1)
      (by omega : 1 ≤ 2 - 1) hbigv hs0lt hmid R0 hbhd i hXw
    have hdrop := type2_psum_lt_k F r s 2 1 (by omega : 1 ≤ 2) hcase2 (by omega : 1 ≤ 1)
      (by omega : 1 ≤ 2 - 1) hbigv hs0lt hmid R0 hbhd i
    constructor
    · exact hwq
    · exact hdrop
  have ht3 : let D := RelData.BCqIter F 0 (toData F R0)
      let Bs := ofBstarOver F D (s ⟨0, by omega⟩) (fun e => BCqIter_valid F 0 R0 e)
          (RelData.iterate_merge_hv F 0 R0 (s ⟨0, by omega⟩) (by omega) hbhd)
      let Q := FixedOver.prependList F Bs (sPrefix r s 1 (by omega) (by omega))
      ∀ i : D.ιB,
        weight (Q.dep (Sum.inr (Sum.inr i))) (Q.c (Sum.inr (Sum.inr i))) = weight r s ∧
        psum (Q.c (Sum.inr (Sum.inr i))) 2 ≤ psum s 2 ∧
        InitLt (Nat.card F) s (Q.c (Sum.inr (Sum.inr i))) := by
    intro D Bs Q i
    have hwq := type3_weight_eq F r s 2 1 (by omega : 1 ≤ 2) hcase2 (by omega : 1 ≤ 1)
      (by omega : 1 ≤ 2 - 1) hbigv hs0lt hmid R0 hbhd i hXw
    have hle := type3_psum_k_le_X F r s 2 1 (by omega : 1 ≤ 2) hcase2 (by omega : 1 ≤ 1)
      (by omega : 1 ≤ 2 - 1) hbigv hs0lt hmid R0 hbhd
      (fun mm : ℕ => psumSeq (tupPadSum (single (qMinusExp F))
        (consVec (w1Of F r s 2 (by omega : 1 ≤ 2) hcase2 hbigv) (sTail r s 2 hcase2))) mm)
      hbndB (lemma29_X1_le F r s 2 (by omega : 1 ≤ 2) hcase2 hbigv) i
    have hinit := type3_Init_gt F r s 2 1 (by omega : 1 ≤ 2) hcase2 (by omega : 1 ≤ 1)
      (by omega : 1 ≤ 2 - 1) hbigv hs0lt hsleq R0 hbhd i
    exact ⟨hwq, ⟨hle, hinit⟩⟩
  -- per-member expansions (level-2 dispatch: 2-adm → self / ¬2-adm → 1-adm + drop → rec)
  have e : ∀ p : ι, AdmExpT F w 2 (mc p) := by
    intro p
    cases p with
    | inl q =>
        dsimp [mc]
        exact q_type1_member_e_T_of F w r s hw hcase2 hbigv hs1v' h1 R0 u hbhd ht1 ih q.1 q.2
    | inr s =>
        cases s with
        | inl i =>
            dsimp [mc]
            exact q_type2_member_e_T_of F w r s hw hcase2 hbigv hs1v' h1 R0 hbhd ht2 ih i
        | inr i =>
            dsimp [mc]
            exact q_type3_member_e_T_of F w r s hw hcase2 hbigv hs1v' h1 R0 hbhd ht3 ih i
  -- member orders (ℓ ≥ 2 ≤ r via the generic k=2 prefix lemmas; ℓ > r by saturation)
  have horder : ∀ p : ι, ∀ ℓ : ℕ, 2 ≤ ℓ → psum (mc p) ℓ ≤ psum s ℓ := by
    intro p ℓ hℓ
    by_cases hℓr : ℓ ≤ r
    · cases p with
      | inl q =>
          have hdec0 := type1_psum_decompose_ge F r s 2 1 (by omega : 1 ≤ 2) hcase2 (by omega : 1 ≤ 1)
            (by omega : 1 ≤ 2 - 1) hbigv hs0lt hmid R0 hbhd q.1 ℓ hℓ
          have hdec : psum (Q.c (Sum.inl (RelData.iterIdx F 0 (toData F R0) q.1))) ℓ =
              psum s (2 - 1) + psum (R0.cA q.1) (ℓ - 1) := by
            simpa [show ℓ - 2 + 1 = ℓ - 1 by omega] using hdec0
          have hpre := hpref q.1 q.2 (ℓ - 1)
          have htel := lemma29_qExp_telescope F r s 2 (by omega : 1 ≤ 2) hcase2 hbigv (ℓ - 1) (by omega : 1 ≤ ℓ - 1)
          have htel' : psumSeq (tupPadSum (single (qExp F))
              (consVec (w1Of F r s 2 (by omega : 1 ≤ 2) hcase2 hbigv) (sTail r s 2 hcase2))) (ℓ - 1) ≤
              (s ⟨1, by omega⟩ : ℕ) + (psum s ℓ - psum s 2) := by
            rw [htel]
            congr 1
            have hidx : 2 + (ℓ - 1) - 1 = ℓ := by omega
            rw [hidx]
          have hb : psum (R0.cA q.1) (ℓ - 1) ≤ (s ⟨1, by omega⟩ : ℕ) + (psum s ℓ - psum s 2) := by
            exact le_trans hpre htel'
          have hmono2l : psum s 2 ≤ psum s ℓ := psum_mono s hℓ
          calc
            psum (Q.c (Sum.inl (RelData.iterIdx F 0 (toData F R0) q.1))) ℓ
                = psum s (2 - 1) + psum (R0.cA q.1) (ℓ - 1) := hdec
            _ ≤ psum s (2 - 1) + ((s ⟨1, by omega⟩ : ℕ) + (psum s ℓ - psum s 2)) := by
                  exact Nat.add_le_add_left hb (psum s (2 - 1))
            _ ≤ psum s ℓ := by omega
      | inr s =>
          cases s with
          | inl i =>
              by_cases h2e : ℓ = 2
              · subst ℓ
                have hps : psum (Q.c (Sum.inr (Sum.inl i))) 2 ≤ psum s 2 := by
                  have hlt : psum (Q.c (Sum.inr (Sum.inl i))) 2 < psum s 2 := by
                    exact (ht2 i).2
                  exact le_of_lt hlt
                exact hps
              · have hgt2 : 2 < ℓ := by omega
                have ho := type2_psum_ge_k_lt F r s 2 1 (by omega : 1 ≤ 2) hcase2 (by omega : 1 ≤ 1)
                  (by omega : 1 ≤ 2 - 1) hbigv hs0lt hmid R0 hbhd hbndB i ℓ hgt2 hℓr
                exact le_of_lt ho
          | inr i =>
              have ho := type3_psum_ge_k_le F r s 2 1 (by omega : 1 ≤ 2) hcase2 (by omega : 1 ≤ 1)
                (by omega : 1 ≤ 2 - 1) hbigv hs0lt hmid R0 hbhd hbndB i ℓ hℓ hℓr
              exact ho
    · -- ℓ > r: saturation
      have hgt : r < ℓ := lt_of_not_ge hℓr
      have hwl := psum_le_weight (mc p) ℓ
      have hwm : weight (mdep p) (mc p) = weight r s := by
        cases p with
        | inl q => simpa [mdep, mc] using (ht1 q.1 q.2).1
        | inr s => cases s with
          | inl i => simpa [mdep, mc] using (ht2 i).1
          | inr i => simpa [mdep, mc] using (ht3 i).1
      have hpeq : weight r s = psum s ℓ := (psum_ge_depth s (le_of_lt hgt)).symm
      rw [hwm, hpeq] at hwl
      exact hwl

  exact admExpT_combine F w 2 s mdep mhdep mc ma hid horder e

end ZagierHoffmanPositiveChar
