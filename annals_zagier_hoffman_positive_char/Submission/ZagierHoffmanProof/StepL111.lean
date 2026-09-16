import Submission.ZagierHoffmanProof.StepL110
import Submission.ZagierHoffmanProof.StepL107
import Submission.ZagierHoffmanProof.StepL99
set_option autoImplicit false
set_option maxHeartbeats 200000000
open Polynomial RatFunc
open scoped BigOperators
/-!
# Step L111: ★ maink_case1_kk1 — the generic (k, k−1) CASE-1 splice (SESSION 256)

★ maink_case1_kk1 (w r s hw) (hk1 1≤k) (hk2 2≤k) (hkr k≤r) (hbigv q < s⟨k−1⟩)
(hsjv s⟨k−2⟩ < q) (h1 : (k−1)-adm) (rec : MainkStep → (k−1)-adm → ¬k-adm →
AdmExpT F w k) : AdmExpT F w k s — every weight-w tuple with the (k,k−1) CASE-1
shape (in-domain, k-th entry > q, (k−1)-st entry < q) expands at level k in
ORDERED form.  main(k)'s CASE-1 (k, k−1)-dispatch calls this with rec := the
lk-induction IH.

STRUCTURE (the k-symbolic port of main3_case1_j1 at (k, k−1)): rcases
maink_config_full (StepL108) — the full config (hdepu/hau/hc0/hbhd/hwtA/hhead/
hXw/hbndB/hpref) from ONE lemma_2_9_rel rcases; the (k,k−1) ζ-core hid0 :=
simpa [D, Bs, Q] using (maink_zeta_kk1) (StepL109) with the EXACT symbolic-let
forms; the 3-family fold (ι₁ := {i₀ ≠ u} ⊕ ι₂ ⊕ ι₃, mdep/mc/ma,
eq_neg_add_add_add' + sum_guarded_subtype' + neg_sum_sum_type' +
neg_coe_mul_zeta); per-member e: hw1 via type1/2/3_weight_eq at (k,k−1),
k-adm → admExpT_self / ¬k-adm → (k−1)-adm (maink_kk1_type{1,2,3}_k1adm,
StepL110) + MainkStep (type-1/2: strict psum-k via type1/2_psum_lt_k;
type-3: ≤ S via type3_psum_k_le_X with lemma29_X1_le + InitLt via
type3_Init_gt → mk_member_step) → rec; horder: type-1 via
type1_psum_decompose_ge + hpref + lemma29_qExp_telescope + hsum; type-2 ℓ = k
via the strict drop / ℓ > k via type2_psum_ge_k_lt; type-3 via
type3_psum_ge_k_le; ℓ > r by weight saturation; splice by admExpT_combine.
NEXT: the CASE-2 (depth-k (·, q) form) via prop213_step1 at (k,k−1), then
main(k) = lk_induction + CASE-1 j-splits (k−2..0) + CASE-2, A(k)@w, and
theorem_A's span at weight w.  theorem_B/D remain ABP-gated (no route).
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- ★ The (k, k−1) CASE-1 splice at SYMBOLIC k: every weight-w tuple with the
CASE-1 (k−1, k)-shape (depth ≥ k, k-th entry > q, (k−1)-st entry < q,
(k−1)-admissible) expands at level k in ORDERED form.  The recursion `rec`
dispatches the chain members (each (k−1)-adm with a MainkStep drop). -/
theorem maink_case1_kk1 (w : ℕ) (r : ℕ) (s : Fin r → ℕ+) (hw : weight r s = w)
    (k : ℕ) (hk1 : 1 ≤ k) (hk2 : 2 ≤ k) (hkr : k ≤ r)
    (hbigv : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hsjv : (s ⟨k - 1 - 1, by omega⟩ : ℕ) < Nat.card F)
    (h1 : kAdmissible (Nat.card F) s (k - 1))
    (rec : ∀ (r' : ℕ) (m : Fin r' → ℕ+) (hm : weight r' m = w),
      MainkStep k (Nat.card F) s m → kAdmissible (Nat.card F) m (k - 1) →
      ¬ kAdmissible (Nat.card F) m k → AdmExpT F w k m) :
    AdmExpT F w k s := by
  classical
  have hmid : ∀ i : Fin r, ((k - 1) : ℕ) ≤ (i : ℕ) → (i : ℕ) < k - 1 → (s i : ℕ) = Nat.card F := by
    intro i hi1 hi2
    omega
  have hsum : psum s k = psum s (k - 1) + (s ⟨k - 1, by omega⟩ : ℕ) := by
    have hpl := psum_last r s k hk1 hkr
    simpa using hpl
  have hmono : psum s k ≤ psum s r := psum_mono s hkr
  have hmono2 : psum s (k - 1) ≤ psum s r := psum_mono s (by omega : k - 1 ≤ r)
  have hq1 : 1 ≤ Nat.card F := by
    have h2 : 2 ≤ Nat.card F := card_ge_two F
    omega
  rcases maink_config_full F k r s hk1 hkr hbigv with
    ⟨R0, u, hdepu, hau, hc0, hbhd, hwtA, hhead, hXw, hbndB, hpref, _⟩
  -- the (2.14) chain ζ-identity at (k, k−1) (maink_zeta_kk1 packages it)
  have hz := maink_zeta_kk1 F r k s hk1 hk2 hkr hbigv hsjv R0 u hau hdepu hc0 hbhd

  let D := RelData.BCqIter F (k - (k - 1) - 1) (toData F R0)
  let Bs := ofBstarOver F D (s ⟨k - 1 - 1, by omega⟩) (fun e => BCqIter_valid F (k - (k - 1) - 1) R0 e)
      (RelData.iterate_merge_hv F (k - (k - 1) - 1) R0 (s ⟨k - 1 - 1, by omega⟩) (by omega) hbhd)
  let Q := FixedOver.prependList F Bs (sPrefix r s (k - 1) (by omega) (by omega))
  have hid0 : ζ_A F s +
      (∑ i₀ : R0.ιA, (if i₀ = u then 0 else
        (((Q.a (Sum.inl (RelData.iterIdx F (k - (k - 1) - 1) (toData F R0) i₀)) : RatFunc F) : RatFunc.CompletionAtInfty F) *
          ζ_A F (Q.c (Sum.inl (RelData.iterIdx F (k - (k - 1) - 1) (toData F R0) i₀)))))) +
      (∑ i : D.ιB, (((Q.a (Sum.inr (Sum.inl i)) : RatFunc F) : RatFunc.CompletionAtInfty F) *
          ζ_A F (Q.c (Sum.inr (Sum.inl i))))) +
      (∑ i : D.ιB, (((Q.a (Sum.inr (Sum.inr i)) : RatFunc F) : RatFunc.CompletionAtInfty F) *
          ζ_A F (Q.c (Sum.inr (Sum.inr i))))) = 0 := by
    simpa [D, Bs, Q] using hz
  -- expansion family (the 3-part fold at (k, k−1))
  let ι₁ : Type := {i₀ : R0.ιA // i₀ ≠ u}
  let ι₂ : Type := D.ιB
  let ι₃ : Type := D.ιB
  let ι : Type := ι₁ ⊕ (ι₂ ⊕ ι₃)
  let inst₁ : Fintype ι₁ :=
    Fintype.subtype ((Finset.univ : Finset R0.ιA).filter (fun i₀ => i₀ ≠ u))
      (by intro x; simp [Finset.mem_filter])
  letI : Fintype ι₁ := inst₁
  let mdep (p : ι) : ℕ := match p with
    | Sum.inl q => Q.dep (Sum.inl (RelData.iterIdx F (k - (k - 1) - 1) (toData F R0) q.1))
    | Sum.inr (Sum.inl i) => Q.dep (Sum.inr (Sum.inl i))
    | Sum.inr (Sum.inr i) => Q.dep (Sum.inr (Sum.inr i))
  let mhdep (p : ι) : 0 < mdep p := by
    dsimp [mdep]
    cases p with
    | inl q => exact Q.hdep (Sum.inl (RelData.iterIdx F (k - (k - 1) - 1) (toData F R0) q.1))
    | inr s => cases s with
      | inl i => exact Q.hdep (Sum.inr (Sum.inl i))
      | inr i => exact Q.hdep (Sum.inr (Sum.inr i))
  let mc (p : ι) : Fin (mdep p) → ℕ+ := match p with
    | Sum.inl q => Q.c (Sum.inl (RelData.iterIdx F (k - (k - 1) - 1) (toData F R0) q.1))
    | Sum.inr (Sum.inl i) => Q.c (Sum.inr (Sum.inl i))
    | Sum.inr (Sum.inr i) => Q.c (Sum.inr (Sum.inr i))
  let ma (p : ι) : RatFunc F := match p with
    | Sum.inl q => -(Q.a (Sum.inl (RelData.iterIdx F (k - (k - 1) - 1) (toData F R0) q.1)))
    | Sum.inr (Sum.inl i) => -(Q.a (Sum.inr (Sum.inl i)))
    | Sum.inr (Sum.inr i) => -(Q.a (Sum.inr (Sum.inr i)))
  let A : RatFunc.CompletionAtInfty F :=
    ∑ i₀ : R0.ιA, (if i₀ = u then 0 else
      (((Q.a (Sum.inl (RelData.iterIdx F (k - (k - 1) - 1) (toData F R0) i₀)) : RatFunc F) : RatFunc.CompletionAtInfty F) *
        ζ_A F (Q.c (Sum.inl (RelData.iterIdx F (k - (k - 1) - 1) (toData F R0) i₀)))))
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
    (((Q.a (Sum.inl (RelData.iterIdx F (k - (k - 1) - 1) (toData F R0) p.1)) : RatFunc F) : RatFunc.CompletionAtInfty F) *
      ζ_A F (Q.c (Sum.inl (RelData.iterIdx F (k - (k - 1) - 1) (toData F R0) p.1))))
  let x₂ (i : ι₂) : RatFunc.CompletionAtInfty F :=
    (((Q.a (Sum.inr (Sum.inl i)) : RatFunc F) : RatFunc.CompletionAtInfty F) * ζ_A F (Q.c (Sum.inr (Sum.inl i))))
  let x₃ (i : ι₃) : RatFunc.CompletionAtInfty F :=
    (((Q.a (Sum.inr (Sum.inr i)) : RatFunc F) : RatFunc.CompletionAtInfty F) * ζ_A F (Q.c (Sum.inr (Sum.inr i))))
  have hA : A = ∑ p : ι₁, x₁ p := by
    dsimp [A, x₁]
    exact sum_guarded_subtype' (u := u)
      (f := fun i₀ : R0.ιA => (((Q.a (Sum.inl (RelData.iterIdx F (k - (k - 1) - 1) (toData F R0) i₀)) : RatFunc F) : RatFunc.CompletionAtInfty F) *
        ζ_A F (Q.c (Sum.inl (RelData.iterIdx F (k - (k - 1) - 1) (toData F R0) i₀)))))
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
        exact (neg_coe_mul_zeta F (Q.a (Sum.inl (RelData.iterIdx F (k - (k - 1) - 1) (toData F R0) q.1)))
          (Q.c (Sum.inl (RelData.iterIdx F (k - (k - 1) - 1) (toData F R0) q.1)))).symm
    | inr s =>
        cases s with
        | inl i =>
            dsimp [x₂, ma, mc]
            exact (neg_coe_mul_zeta F (Q.a (Sum.inr (Sum.inl i))) (Q.c (Sum.inr (Sum.inl i)))).symm
        | inr i =>
            dsimp [x₃, ma, mc]
            exact (neg_coe_mul_zeta F (Q.a (Sum.inr (Sum.inr i))) (Q.c (Sum.inr (Sum.inr i)))).symm
  -- per-member dispatch data (the (k,k−1) ht-conjuncts over the rcases'd package)
  have ih : ∀ (r' : ℕ) (m : Fin r' → ℕ+) (hm : weight r' m = w),
      MainkStep k (Nat.card F) s m → kAdmissible (Nat.card F) m (k - 1) →
      ¬ kAdmissible (Nat.card F) m k → AdmExpT F w k m := by
    intro r' m hm hstepm hkm1 hkm
    exact rec r' m hm hstepm hkm1 hkm
  have ht1 : let D := RelData.BCqIter F (k - (k - 1) - 1) (toData F R0)
      let Bs := ofBstarOver F D (s ⟨k - 1 - 1, by omega⟩) (fun e => BCqIter_valid F (k - (k - 1) - 1) R0 e)
          (RelData.iterate_merge_hv F (k - (k - 1) - 1) R0 (s ⟨k - 1 - 1, by omega⟩) (by omega) hbhd)
      let Q := FixedOver.prependList F Bs (sPrefix r s (k - 1) (by omega) (by omega))
      ∀ i₀ : R0.ιA, i₀ ≠ u →
        weight (Q.dep (Sum.inl (RelData.iterIdx F (k - (k - 1) - 1) (toData F R0) i₀)))
            (Q.c (Sum.inl (RelData.iterIdx F (k - (k - 1) - 1) (toData F R0) i₀))) = weight r s ∧
        psum (Q.c (Sum.inl (RelData.iterIdx F (k - (k - 1) - 1) (toData F R0) i₀))) k < psum s k := by
    intro D Bs Q i₀ hi₀
    have hwq := type1_weight_eq F r s k (k - 1) hk1 hkr (by omega : 1 ≤ k - 1)
      (by omega : k - 1 ≤ k - 1) hbigv hsjv hmid R0 hbhd i₀ (hwtA i₀ hi₀)
    have hdrop := type1_psum_lt_k F r s k (k - 1) hk1 hkr (by omega : 1 ≤ k - 1)
      (by omega : k - 1 ≤ k - 1) hbigv hsjv hmid R0 hbhd i₀ (hhead i₀ hi₀)
    constructor
    · exact hwq
    · exact hdrop
  have ht2 : let D := RelData.BCqIter F (k - (k - 1) - 1) (toData F R0)
      let Bs := ofBstarOver F D (s ⟨k - 1 - 1, by omega⟩) (fun e => BCqIter_valid F (k - (k - 1) - 1) R0 e)
          (RelData.iterate_merge_hv F (k - (k - 1) - 1) R0 (s ⟨k - 1 - 1, by omega⟩) (by omega) hbhd)
      let Q := FixedOver.prependList F Bs (sPrefix r s (k - 1) (by omega) (by omega))
      ∀ i : D.ιB,
        weight (Q.dep (Sum.inr (Sum.inl i))) (Q.c (Sum.inr (Sum.inl i))) = weight r s ∧
        psum (Q.c (Sum.inr (Sum.inl i))) k < psum s k := by
    intro D Bs Q i
    have hwq := type2_weight_eq F r s k (k - 1) hk1 hkr (by omega : 1 ≤ k - 1)
      (by omega : k - 1 ≤ k - 1) hbigv hsjv hmid R0 hbhd i hXw
    have hdrop := type2_psum_lt_k F r s k (k - 1) hk1 hkr (by omega : 1 ≤ k - 1)
      (by omega : k - 1 ≤ k - 1) hbigv hsjv hmid R0 hbhd i
    constructor
    · exact hwq
    · exact hdrop
  have ht3 : let D := RelData.BCqIter F (k - (k - 1) - 1) (toData F R0)
      let Bs := ofBstarOver F D (s ⟨k - 1 - 1, by omega⟩) (fun e => BCqIter_valid F (k - (k - 1) - 1) R0 e)
          (RelData.iterate_merge_hv F (k - (k - 1) - 1) R0 (s ⟨k - 1 - 1, by omega⟩) (by omega) hbhd)
      let Q := FixedOver.prependList F Bs (sPrefix r s (k - 1) (by omega) (by omega))
      ∀ i : D.ιB,
        weight (Q.dep (Sum.inr (Sum.inr i))) (Q.c (Sum.inr (Sum.inr i))) = weight r s ∧
        psum (Q.c (Sum.inr (Sum.inr i))) k ≤ psum s k ∧
        InitLt (Nat.card F) s (Q.c (Sum.inr (Sum.inr i))) := by
    intro D Bs Q i
    have hwq := type3_weight_eq F r s k (k - 1) hk1 hkr (by omega : 1 ≤ k - 1)
      (by omega : k - 1 ≤ k - 1) hbigv hsjv hmid R0 hbhd i hXw
    have hle := type3_psum_k_le_X F r s k (k - 1) hk1 hkr (by omega : 1 ≤ k - 1)
      (by omega : k - 1 ≤ k - 1) hbigv hsjv hmid R0 hbhd
      (fun mm : ℕ => psumSeq (tupPadSum (single (qMinusExp F))
        (consVec (w1Of F r s k hk1 hkr hbigv) (sTail r s k hkr))) mm)
      hbndB (lemma29_X1_le F r s k hk1 hkr hbigv) i
    have hinit := type3_Init_gt F r s k (k - 1) hk1 hkr (by omega : 1 ≤ k - 1)
      (by omega : k - 1 ≤ k - 1) hbigv hsjv (h1.1) R0 hbhd i
    exact ⟨hwq, ⟨hle, hinit⟩⟩
  -- per-member expansions (dispatch: k-adm → self / ¬k-adm → (k−1)-adm + MainkStep → rec)
  have e : ∀ p : ι, AdmExpT F w k (mc p) := by
    intro p
    cases p with
    | inl q =>
        let m : Fin (Q.dep (Sum.inl (RelData.iterIdx F (k - (k - 1) - 1) (toData F R0) q.1))) → ℕ+ :=
          Q.c (Sum.inl (RelData.iterIdx F (k - (k - 1) - 1) (toData F R0) q.1))
        have hw1 : weight (Q.dep (Sum.inl (RelData.iterIdx F (k - (k - 1) - 1) (toData F R0) q.1))) m =
            weight r s := by
          simpa [m] using (type1_weight_eq F r s k (k - 1) hk1 hkr (by omega : 1 ≤ k - 1)
            (by omega : k - 1 ≤ k - 1) hbigv hsjv hmid R0 hbhd q.1 (hwtA q.1 q.2))
        by_cases hkm : kAdmissible (Nat.card F) m k
        · have hd : 0 < Q.dep (Sum.inl (RelData.iterIdx F (k - (k - 1) - 1) (toData F R0) q.1)) :=
            Q.hdep (Sum.inl (RelData.iterIdx F (k - (k - 1) - 1) (toData F R0) q.1))
          have hw' : weight (Q.dep (Sum.inl (RelData.iterIdx F (k - (k - 1) - 1) (toData F R0) q.1)))
              (Q.c (Sum.inl (RelData.iterIdx F (k - (k - 1) - 1) (toData F R0) q.1))) = w := by
            rw [hw1]
            exact hw
          have hkm' : kAdmissible (Nat.card F)
              (Q.c (Sum.inl (RelData.iterIdx F (k - (k - 1) - 1) (toData F R0) q.1))) k := by simpa [m] using hkm
          exact admExpT_self F w k hd (Q.c (Sum.inl (RelData.iterIdx F (k - (k - 1) - 1) (toData F R0) q.1))) hw' hkm'
        · have hkm1' : kAdmissible (Nat.card F)
              (Q.c (Sum.inl (RelData.iterIdx F (k - (k - 1) - 1) (toData F R0) q.1))) (k - 1) := by
            simpa [m] using (maink_kk1_type1_k1adm F r s k hk2 hkr hbigv hsjv h1 R0 u hbhd q.1 q.2)
          have hkm1 : kAdmissible (Nat.card F) m (k - 1) := by simpa [m] using hkm1'
          have hstep : MainkStep k (Nat.card F) s m := by
            have hps : psum (Q.c (Sum.inl (RelData.iterIdx F (k - (k - 1) - 1) (toData F R0) q.1))) k < psum s k := by
              simpa [m] using (type1_psum_lt_k F r s k (k - 1) hk1 hkr (by omega : 1 ≤ k - 1)
                (by omega : k - 1 ≤ k - 1) hbigv hsjv hmid R0 hbhd q.1 (hhead q.1 q.2))
            exact Or.inl (by simpa [m] using hps)
          have hwm' : weight (Q.dep (Sum.inl (RelData.iterIdx F (k - (k - 1) - 1) (toData F R0) q.1))) m = w := by
            rw [hw1]
            exact hw
          have hres := rec (Q.dep (Sum.inl (RelData.iterIdx F (k - (k - 1) - 1) (toData F R0) q.1))) m hwm' hstep hkm1 hkm
          simpa [m] using hres
    | inr s =>
        cases s with
        | inl i =>
            let m : Fin (Q.dep (Sum.inr (Sum.inl i))) → ℕ+ := Q.c (Sum.inr (Sum.inl i))
            have hw1 : weight (Q.dep (Sum.inr (Sum.inl i))) m = weight r s := by
              simpa [m] using (type2_weight_eq F r s k (k - 1) hk1 hkr (by omega : 1 ≤ k - 1)
                (by omega : k - 1 ≤ k - 1) hbigv hsjv hmid R0 hbhd i hXw)
            by_cases hkm : kAdmissible (Nat.card F) m k
            · have hd : 0 < Q.dep (Sum.inr (Sum.inl i)) := Q.hdep (Sum.inr (Sum.inl i))
              have hw' : weight (Q.dep (Sum.inr (Sum.inl i))) (Q.c (Sum.inr (Sum.inl i))) = w := by
                rw [hw1]
                exact hw
              have hkm' : kAdmissible (Nat.card F) (Q.c (Sum.inr (Sum.inl i))) k := by simpa [m] using hkm
              exact admExpT_self F w k hd (Q.c (Sum.inr (Sum.inl i))) hw' hkm'
            · have hkm1' : kAdmissible (Nat.card F) (Q.c (Sum.inr (Sum.inl i))) (k - 1) := by
                simpa [m] using (maink_kk1_type2_k1adm F r s k hk2 hkr hbigv hsjv h1 R0 u hbhd i)
              have hkm1 : kAdmissible (Nat.card F) m (k - 1) := by simpa [m] using hkm1'
              have hstep : MainkStep k (Nat.card F) s m := by
                have hps : psum (Q.c (Sum.inr (Sum.inl i))) k < psum s k := by
                  simpa [m] using (type2_psum_lt_k F r s k (k - 1) hk1 hkr (by omega : 1 ≤ k - 1)
                    (by omega : k - 1 ≤ k - 1) hbigv hsjv hmid R0 hbhd i)
                exact Or.inl (by simpa [m] using hps)
              have hwm' : weight (Q.dep (Sum.inr (Sum.inl i))) m = w := by
                rw [hw1]
                exact hw
              have hres := rec (Q.dep (Sum.inr (Sum.inl i))) m hwm' hstep hkm1 hkm
              simpa [m] using hres
        | inr i =>
            let m : Fin (Q.dep (Sum.inr (Sum.inr i))) → ℕ+ := Q.c (Sum.inr (Sum.inr i))
            have hw1 : weight (Q.dep (Sum.inr (Sum.inr i))) m = weight r s := by
              simpa [m] using (type3_weight_eq F r s k (k - 1) hk1 hkr (by omega : 1 ≤ k - 1)
                (by omega : k - 1 ≤ k - 1) hbigv hsjv hmid R0 hbhd i hXw)
            by_cases hkm : kAdmissible (Nat.card F) m k
            · have hd : 0 < Q.dep (Sum.inr (Sum.inr i)) := Q.hdep (Sum.inr (Sum.inr i))
              have hw' : weight (Q.dep (Sum.inr (Sum.inr i))) (Q.c (Sum.inr (Sum.inr i))) = w := by
                rw [hw1]
                exact hw
              have hkm' : kAdmissible (Nat.card F) (Q.c (Sum.inr (Sum.inr i))) k := by simpa [m] using hkm
              exact admExpT_self F w k hd (Q.c (Sum.inr (Sum.inr i))) hw' hkm'
            · have hkm1' : kAdmissible (Nat.card F) (Q.c (Sum.inr (Sum.inr i))) (k - 1) := by
                simpa [m] using (maink_kk1_type3_k1adm F r s k hk2 hkr hbigv hsjv h1 R0 u hbhd i)
              have hkm1 : kAdmissible (Nat.card F) m (k - 1) := by simpa [m] using hkm1'
              have hstep : MainkStep k (Nat.card F) s m := by
                have hle : psum (Q.c (Sum.inr (Sum.inr i))) k ≤ psum s k := by
                  simpa [m] using (type3_psum_k_le_X F r s k (k - 1) hk1 hkr (by omega : 1 ≤ k - 1)
                    (by omega : k - 1 ≤ k - 1) hbigv hsjv hmid R0 hbhd
                    (fun mm : ℕ => psumSeq (tupPadSum (single (qMinusExp F))
                      (consVec (w1Of F r s k hk1 hkr hbigv) (sTail r s k hkr))) mm)
                    hbndB (lemma29_X1_le F r s k hk1 hkr hbigv) i)
                have hinit : InitLt (Nat.card F) s (Q.c (Sum.inr (Sum.inr i))) := by
                  simpa [m] using (type3_Init_gt F r s k (k - 1) hk1 hkr (by omega : 1 ≤ k - 1)
                    (by omega : k - 1 ≤ k - 1) hbigv hsjv (h1.1) R0 hbhd i)
                exact mk_member_step k (Nat.card F) s (Q.c (Sum.inr (Sum.inr i)))
                  (Or.inr ⟨hle, hinit⟩)
              have hwm' : weight (Q.dep (Sum.inr (Sum.inr i))) m = w := by
                rw [hw1]
                exact hw
              have hres := rec (Q.dep (Sum.inr (Sum.inr i))) m hwm' hstep hkm1 hkm
              simpa [m] using hres
  -- member orders (type-lemmas at (k, k−1) for ℓ ∈ [k, r]; saturation beyond r)
  have horder : ∀ p : ι, ∀ ℓ : ℕ, k ≤ ℓ → psum (mc p) ℓ ≤ psum s ℓ := by
    intro p ℓ hℓ
    by_cases hℓr : ℓ ≤ r
    · cases p with
      | inl q =>
          have hdec := type1_psum_decompose_ge F r s k (k - 1) hk1 hkr (by omega : 1 ≤ k - 1)
            (by omega : k - 1 ≤ k - 1) hbigv hsjv hmid R0 hbhd q.1 ℓ hℓ
          have hpre := hpref q.1 q.2 (ℓ - k + 1)
          have htel := lemma29_qExp_telescope F r s k hk1 hkr hbigv (ℓ - k + 1) (by omega : 1 ≤ ℓ - k + 1)
          have htel' : psumSeq (tupPadSum (single (qExp F))
              (consVec (w1Of F r s k hk1 hkr hbigv) (sTail r s k hkr))) (ℓ - k + 1) ≤
              (s ⟨k - 1, by omega⟩ : ℕ) + (psum s ℓ - psum s k) := by
            rw [htel]
            congr 1
            have hidx : k + (ℓ - k + 1) - 1 = ℓ := by omega
            rw [hidx]
          have hb : psum (R0.cA q.1) (ℓ - k + 1) ≤ (s ⟨k - 1, by omega⟩ : ℕ) + (psum s ℓ - psum s k) := by
            exact le_trans hpre htel'
          have hmono3 : psum s k ≤ psum s ℓ := psum_mono s hℓ
          calc
            psum (Q.c (Sum.inl (RelData.iterIdx F (k - (k - 1) - 1) (toData F R0) q.1))) ℓ
                = psum s (k - 1) + psum (R0.cA q.1) (ℓ - k + 1) := hdec
            _ ≤ psum s (k - 1) + ((s ⟨k - 1, by omega⟩ : ℕ) + (psum s ℓ - psum s k)) := by
                  exact Nat.add_le_add_left hb (psum s (k - 1))
            _ ≤ psum s ℓ := by omega
      | inr s =>
          cases s with
          | inl i =>
              by_cases hke : ℓ = k
              · subst ℓ
                have hps : psum (Q.c (Sum.inr (Sum.inl i))) k ≤ psum s k := by
                  have hlt : psum (Q.c (Sum.inr (Sum.inl i))) k < psum s k := by
                    simpa using (type2_psum_lt_k F r s k (k - 1) hk1 hkr (by omega : 1 ≤ k - 1)
                      (by omega : k - 1 ≤ k - 1) hbigv hsjv hmid R0 hbhd i)
                  exact le_of_lt hlt
                exact hps
              · have hgtk : k < ℓ := by omega
                have ho := type2_psum_ge_k_lt F r s k (k - 1) hk1 hkr (by omega : 1 ≤ k - 1)
                  (by omega : k - 1 ≤ k - 1) hbigv hsjv hmid R0 hbhd hbndB i ℓ hgtk hℓr
                exact le_of_lt ho
          | inr i =>
              have ho := type3_psum_ge_k_le F r s k (k - 1) hk1 hkr (by omega : 1 ≤ k - 1)
                (by omega : k - 1 ≤ k - 1) hbigv hsjv hmid R0 hbhd hbndB i ℓ hℓ hℓr
              exact ho
    · -- ℓ > r: saturation (both psums are the common weight)
      have hgt : r < ℓ := lt_of_not_ge hℓr
      have hwl := psum_le_weight (mc p) ℓ
      have hwm : weight (mdep p) (mc p) = weight r s := by
        cases p with
        | inl q => simpa using (type1_weight_eq F r s k (k - 1) hk1 hkr (by omega : 1 ≤ k - 1)
            (by omega : k - 1 ≤ k - 1) hbigv hsjv hmid R0 hbhd q.1 (hwtA q.1 q.2))
        | inr s => cases s with
          | inl i => simpa using (type2_weight_eq F r s k (k - 1) hk1 hkr (by omega : 1 ≤ k - 1)
              (by omega : k - 1 ≤ k - 1) hbigv hsjv hmid R0 hbhd i hXw)
          | inr i => simpa using (type3_weight_eq F r s k (k - 1) hk1 hkr (by omega : 1 ≤ k - 1)
              (by omega : k - 1 ≤ k - 1) hbigv hsjv hmid R0 hbhd i hXw)
      have hpeq : weight r s = psum s ℓ := (psum_ge_depth s (le_of_lt hgt)).symm
      rw [hwm, hpeq] at hwl
      exact hwl
  exact admExpT_combine F w k s mdep mhdep mc ma hid horder e

end ZagierHoffmanPositiveChar
