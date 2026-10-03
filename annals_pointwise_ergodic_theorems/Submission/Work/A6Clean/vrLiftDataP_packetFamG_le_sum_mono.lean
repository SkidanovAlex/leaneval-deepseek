import Mathlib
import Submission.Work.KMTPlan.A6Clean.packetFamG_aux
import Submission.Port.Aesm

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.A6Clean

open MeasureTheory Finset
open scoped ENNReal NNReal BigOperators

local notation "Circ" => Work.Analysis.IonescuWainger.Circle

/-! ## Elementary tools

The `V^R(ℤ; L²(ZMod Q))`-datum `VrLiftDataP R Q u` of a packet family is the sum of the sup-part
`⨆_n eLpNorm (u n)` and the variation part `⨆_{chains} (∑_i ‖u_jumps‖²)^(1/R)`.  When `u` is a
*finite character combination* `u n θ = ∑_β e_β(θ) · c_β n` with `|e_β| = 1`, the `L²(ZMod Q)`
norms are bounded by the corresponding sums of moduli, and the variation part is bounded by
Minkowski's inequality in `ℓ^R` over the finite family `β`.

The three tools below are `varPart ≤ variationalNorm` (definitional), the domination of a
`Fin (J+1)`-chain term (the chain is extended to a monotone `ℕ → ℕ` chain) by `varPart`, and the
`eLpNorm` bound for a character combination with arbitrary coefficients. -/

/-- The variation part is dominated by the variational norm. -/
private lemma varPart_le_variationalNorm (r : NNReal) (a : ℕ → ℂ) :
    Submission.PointwiseErgodicTheorems.varPart r a
      ≤ PointwiseErgodicTheorems.variationalNorm r a := by
  rw [Submission.PointwiseErgodicTheorems.variationalNorm_eq_add]
  exact le_add_left le_rfl

/-- **A chain term indexed by `Fin (J+1)` is dominated by the variation part.**  The monotone tuple
`k : Fin (J + 1) → ℕ` is extended to `N : ℕ → ℕ` by `N j = k (min j J)`, which is monotone and
coincides with `k` on the differences `(i, i+1)`. -/
private lemma ofReal_toLp_finChain_le_varPart (R : NNReal) (a : ℕ → ℂ) {J : ℕ}
    (k : Fin (J + 1) → ℕ) (hk : Monotone k) :
    ENNReal.ofReal ‖WithLp.toLp (R : ℝ≥0∞)
        (fun i : Fin J => a (k i.succ) - a (k i.castSucc))‖
      ≤ Submission.PointwiseErgodicTheorems.varPart R a := by
  set N : ℕ → ℕ := fun n => k ⟨min n J, Nat.lt_succ_of_le (Nat.min_le_right n J)⟩ with hN
  have hNmono : Monotone N := by
    intro m n hmn
    show k ⟨min m J, _⟩ ≤ k ⟨min n J, _⟩
    exact hk (by simp only [Fin.le_def]; exact min_le_min_right J hmn)
  have hNi : ∀ i : Fin J, N i = k i.castSucc := by
    intro i
    show k ⟨min (i : ℕ) J, _⟩ = k i.castSucc
    congr 1
    exact Fin.ext (Nat.min_eq_left (le_of_lt i.isLt))
  have hNs : ∀ i : Fin J, N ((i : ℕ) + 1) = k i.succ := by
    intro i
    show k ⟨min ((i : ℕ) + 1) J, _⟩ = k i.succ
    congr 1
    exact Fin.ext (Nat.min_eq_left (Nat.succ_le_of_lt i.isLt))
  have hvec : (fun i : Fin J => a (k i.succ) - a (k i.castSucc))
      = (fun i : Fin J => a (N (i + 1)) - a (N i)) := by
    funext i
    rw [hNi i, hNs i]
  rw [hvec]
  exact le_iSup_of_le J (le_iSup_of_le N (le_iSup_of_le hNmono le_rfl))

/-- **Uniqueness of the "mixed" index of a monotone chain.**  If `gs` is an up-set of `ℕ` and
`k : Fin (J + 1) → ℕ` is monotone, there is at most one `i : Fin J` at which `gs (k ·)` passes from
false (at `i.castSucc`) to true (at `i.succ`). -/
private lemma mixedIndex_unique {J : ℕ} (gs : ℕ → Prop)
    (hgs : ∀ n m : ℕ, n ≤ m → gs n → gs m) (k : Fin (J + 1) → ℕ) (hk : Monotone k)
    {i j : Fin J} (hi : ¬ gs (k i.castSucc) ∧ gs (k i.succ))
    (hj : ¬ gs (k j.castSucc) ∧ gs (k j.succ)) : i = j := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact hj.1 (hgs _ _ (hk (Fin.succ_le_castSucc_iff.mpr hlt)) hi.2)
  · exact hi.1 (hgs _ _ (hk (Fin.succ_le_castSucc_iff.mpr hlt)) hj.2)

/-- **The `L²(ZMod Q)`-norm of a character combination is bounded by the sum of the moduli of its
coefficients.** -/
private lemma eLpNorm_arithCharSum_le {Q : ℕ} [NeZero Q] (F : Finset Circ) (C : Circ → ℂ) :
    eLpNorm (fun θ : ZMod Q => ∑ β ∈ F, fourier (T := 1) (-(θ.val : ℤ)) β * C β) 2
        (Work.KMTPlan.A6.zmodProb Q)
      ≤ ∑ β ∈ F, ‖C β‖ₑ := by
  classical
  have hμ : Work.KMTPlan.A6.zmodProb Q ≠ 0 := by
    intro h
    have h1 : (Work.KMTPlan.A6.zmodProb Q) Set.univ
        = (0 : Measure (ZMod Q)) Set.univ := by rw [h]
    rw [Work.KMTPlan.A6.zmodProb_univ] at h1
    simp at h1
  set c : ℝ := ∑ β ∈ F, ‖C β‖ with hc
  have hc0 : 0 ≤ c := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hsum : (∑ β ∈ F, ‖C β‖ₑ) = ENNReal.ofReal c := by
    rw [hc, ENNReal.ofReal_sum_of_nonneg (fun β _ => norm_nonneg (C β))]
    exact Finset.sum_congr rfl (fun β _ => Work.KMTPlan.A6Clean.enorm_complex_eq (C β))
  refine le_trans (eLpNorm_mono (hf := by pw_aesm) (g := fun _ : ZMod Q => (c : ℂ)) (fun θ => ?_)) ?_
  · calc ‖∑ β ∈ F, fourier (T := 1) (-(θ.val : ℤ)) β * C β‖
        ≤ ∑ β ∈ F, ‖fourier (T := 1) (-(θ.val : ℤ)) β * C β‖ := norm_sum_le _ _
      _ = ∑ β ∈ F, ‖C β‖ := by
          refine Finset.sum_congr rfl (fun β _ => ?_)
          rw [norm_mul, Work.KMTAreas.A7.norm_fourier_applyR, one_mul]
      _ = ‖(c : ℂ)‖ := by rw [hc, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc0]
  · rw [eLpNorm_const _ (by norm_num : (2 : ℝ≥0∞) ≠ 0) hμ]
    rw [Work.KMTPlan.A6.zmodProb_univ]
    have hroot : (1 : ℝ≥0∞) ^ (1 / (2 : ℝ≥0∞).toReal) = 1 := by simp
    rw [hroot, mul_one, hsum, Work.KMTPlan.A6Clean.enorm_complex_eq]
    exact ENNReal.ofReal_le_ofReal
      (le_of_eq (by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc0]))

theorem vrLiftDataP_packetFamG_le_sum_mono (ρ : ℝ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ : ℕ)
    (W : ℕ → Work.Analysis.IonescuWainger.Circle → ℝ → ℂ) (R : NNReal) (hR : 1 ≤ R) (X : ℝ)
    (hmono : Monotone (fun n : ℕ => Nat.floor (a n))) :
    Work.KMTPlan.A6.VrLiftDataP (R : ℝ) (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))
        (fun n : ℕ => Work.KMTPlan.A6Clean.packetFamG ρ a l₁ l₂ k₁ k₂ W n X)
      ≤ (↑(3 * ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂).card + 2)) : ENNReal) *
        ∑ β ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂,
          PointwiseErgodicTheorems.variationalNorm R (fun n : ℕ => W n β X) := by
  classical
  set Q : ℕ := Work.KMTAreas.A7.arithQ ρ (max l₁ l₂) with hQ
  set L : ℕ := Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂ with hL
  set F : Finset Circ := Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂ with hF
  haveI : NeZero Q :=
    ⟨Nat.pos_iff_ne_zero.mp (by rw [hQ]; exact Work.KMTAreas.A7.arithQ_pos ρ (max l₁ l₂))⟩
  set gs : ℕ → Prop := fun n => Work.KMTPlan.A6.goodScale Q L (Nat.floor (a n)) with hgs
  set u : ℕ → ZMod Q → ℂ :=
    fun n => Work.KMTPlan.A6Clean.packetFamG ρ a l₁ l₂ k₁ k₂ W n X with hu
  set V : ENNReal := ∑ β ∈ F, PointwiseErgodicTheorems.variationalNorm R (fun n : ℕ => W n β X)
    with hV
  have hgsmono : ∀ n m : ℕ, n ≤ m → gs n → gs m := by
    intro n m hnm hn
    simp only [hgs] at hn ⊢
    simp only [Work.KMTPlan.A6.goodScale] at hn ⊢
    exact le_trans hn (hmono hnm)
  -- ### the sup-part of the `V^R`-datum
  have hT1 : (⨆ n : ℕ, eLpNorm (u n) 2 (Work.KMTPlan.A6.zmodProb Q)) ≤ V := by
    refine iSup_le fun n => ?_
    have h1 : eLpNorm (u n) 2 (Work.KMTPlan.A6.zmodProb Q) ≤ ∑ β ∈ F, ‖W n β X‖ₑ := by
      have h := Work.KMTPlan.A6Clean.eLpNorm_packetFamG_le ρ a l₁ l₂ k₁ k₂ W n X
      show eLpNorm (Work.KMTPlan.A6Clean.packetFamG ρ a l₁ l₂ k₁ k₂ W n X) 2
          (Work.KMTPlan.A6.zmodProb Q) ≤ ∑ β ∈ F, ‖W n β X‖ₑ
      simpa only [hQ, hF] using h
    refine h1.trans ?_
    rw [hV]
    exact Finset.sum_le_sum fun β _ =>
      Work.KMTAreas.A7.enorm_apply_le_variationalNorm (fun n : ℕ => W n β X) n
  -- ### the variation part of the `V^R`-datum
  have hT2 : (⨆ (J : ℕ) (k : Fin (J + 1) → ℕ) (_ : Monotone k),
      ENNReal.rpow (Finset.univ.sum fun i : Fin J => ENNReal.rpow
        (eLpNorm (u (k i.succ) - u (k i.castSucc)) 2 (Work.KMTPlan.A6.zmodProb Q)) (R : ℝ))
        (1 / (R : ℝ))) ≤ 2 * V := by
    refine iSup_le fun J => iSup_le fun k => iSup_le fun hk => ?_
    set mixed : Fin J → Prop := fun i => ¬ gs (k i.castSucc) ∧ gs (k i.succ) with hmixdef
    have hmixcard : ((Finset.univ : Finset (Fin J)).filter mixed).card ≤ 1 := by
      refine Finset.card_le_one.mpr fun a ha b hb => ?_
      exact mixedIndex_unique gs hgsmono k hk (Finset.mem_filter.mp ha).2
        (Finset.mem_filter.mp hb).2
    -- per-index bound
    have hE : ∀ i : Fin J,
        eLpNorm (u (k i.succ) - u (k i.castSucc)) 2 (Work.KMTPlan.A6.zmodProb Q)
          ≤ if mixed i then (∑ β ∈ F, ⨆ n : ℕ, ‖W n β X‖ₑ)
            else (∑ β ∈ F, ‖W (k i.succ) β X - W (k i.castSucc) β X‖ₑ) := by
      intro i
      have hle : k i.castSucc ≤ k i.succ := hk (Fin.castSucc_le_succ i)
      by_cases hn : gs (k i.castSucc)
      · -- both scales are good: the difference is the character combination of the differences
        have hm : gs (k i.succ) := hgsmono _ _ hle hn
        have hnmix : ¬ mixed i := by rw [hmixdef]; exact fun h => h.1 hn
        have hdiff : u (k i.succ) - u (k i.castSucc)
            = fun θ : ZMod Q => ∑ β ∈ F, fourier (T := 1) (-(θ.val : ℤ)) β *
                (W (k i.succ) β X - W (k i.castSucc) β X) := by
          funext θ
          show Work.KMTPlan.A6Clean.packetFamG ρ a l₁ l₂ k₁ k₂ W (k i.succ) X θ
              - Work.KMTPlan.A6Clean.packetFamG ρ a l₁ l₂ k₁ k₂ W (k i.castSucc) X θ = _
          have hm' : Work.KMTPlan.A6.goodScale (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))
              (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) (Nat.floor (a (k i.succ))) := by
            simpa only [hgs, hQ, hL] using hm
          have hn' : Work.KMTPlan.A6.goodScale (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))
              (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) (Nat.floor (a (k i.castSucc))) := by
            simpa only [hgs, hQ, hL] using hn
          rw [Work.KMTPlan.A6Clean.packetFamG_apply, Work.KMTPlan.A6Clean.packetFamG_apply,
            if_pos hm', if_pos hn', hF, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun β _ => by ring
        rw [hdiff, if_neg hnmix]
        exact eLpNorm_arithCharSum_le F
          (fun β => W (k i.succ) β X - W (k i.castSucc) β X)
      · by_cases hm : gs (k i.succ)
        · -- mixed index: the whole difference is the upper packet slice
          have hmix : mixed i := by rw [hmixdef]; exact ⟨hn, hm⟩
          have hun : u (k i.castSucc) = 0 := by
            funext θ
            show Work.KMTPlan.A6Clean.packetFamG ρ a l₁ l₂ k₁ k₂ W (k i.castSucc) X θ = _
            have hn' : ¬ Work.KMTPlan.A6.goodScale (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))
                (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) (Nat.floor (a (k i.castSucc))) := by
              simpa only [hgs, hQ, hL] using hn
            rw [Work.KMTPlan.A6Clean.packetFamG_apply, if_neg hn']
            rfl
          have hum : u (k i.succ) = fun θ : ZMod Q => ∑ β ∈ F,
              fourier (T := 1) (-(θ.val : ℤ)) β * W (k i.succ) β X := by
            funext θ
            show Work.KMTPlan.A6Clean.packetFamG ρ a l₁ l₂ k₁ k₂ W (k i.succ) X θ = _
            have hm' : Work.KMTPlan.A6.goodScale (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))
                (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) (Nat.floor (a (k i.succ))) := by
              simpa only [hgs, hQ, hL] using hm
            rw [Work.KMTPlan.A6Clean.packetFamG_apply, if_pos hm', hF]
          rw [if_pos hmix, hun, sub_zero, hum]
          refine le_trans (eLpNorm_arithCharSum_le F (fun β => W (k i.succ) β X)) ?_
          exact Finset.sum_le_sum fun β _ => le_iSup (fun n : ℕ => ‖W n β X‖ₑ) (k i.succ)
        · -- both scales are bad: the difference vanishes
          have hnmix : ¬ mixed i := by rw [hmixdef]; exact fun h => hm h.2
          rw [if_neg hnmix]
          have hun : u (k i.castSucc) = 0 := by
            funext θ
            show Work.KMTPlan.A6Clean.packetFamG ρ a l₁ l₂ k₁ k₂ W (k i.castSucc) X θ = _
            have hn' : ¬ Work.KMTPlan.A6.goodScale (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))
                (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) (Nat.floor (a (k i.castSucc))) := by
              simpa only [hgs, hQ, hL] using hn
            rw [Work.KMTPlan.A6Clean.packetFamG_apply, if_neg hn']
            rfl
          have hum : u (k i.succ) = 0 := by
            funext θ
            show Work.KMTPlan.A6Clean.packetFamG ρ a l₁ l₂ k₁ k₂ W (k i.succ) X θ = _
            have hm' : ¬ Work.KMTPlan.A6.goodScale (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))
                (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) (Nat.floor (a (k i.succ))) := by
              simpa only [hgs, hQ, hL] using hm
            rw [Work.KMTPlan.A6Clean.packetFamG_apply, if_neg hm']
            rfl
          rw [hum, hun, sub_self, eLpNorm_zero]
          exact bot_le
    -- bound the `ℓ^R`-sum of the per-index bounds
    have hsum : (Finset.univ.sum fun i : Fin J => ENNReal.rpow
          (eLpNorm (u (k i.succ) - u (k i.castSucc)) 2 (Work.KMTPlan.A6.zmodProb Q))
          (R : ℝ))
        ≤ (Finset.univ.sum fun i : Fin J => ENNReal.rpow
              (∑ β ∈ F, ‖W (k i.succ) β X - W (k i.castSucc) β X‖ₑ) (R : ℝ))
          + ENNReal.rpow (∑ β ∈ F, ⨆ n : ℕ, ‖W n β X‖ₑ) (R : ℝ) := by
      refine (Finset.sum_le_sum fun i _ =>
        ENNReal.rpow_le_rpow (hE i) (by positivity)).trans ?_
      have hpt : ∀ i : Fin J, (if mixed i then (∑ β ∈ F, ⨆ n : ℕ, ‖W n β X‖ₑ)
            else (∑ β ∈ F, ‖W (k i.succ) β X - W (k i.castSucc) β X‖ₑ)) ^ (R : ℝ)
          = (if mixed i then (∑ β ∈ F, ⨆ n : ℕ, ‖W n β X‖ₑ) ^ (R : ℝ)
            else (∑ β ∈ F, ‖W (k i.succ) β X - W (k i.castSucc) β X‖ₑ) ^ (R : ℝ)) := by
        intro i
        by_cases h : mixed i
        · simp only [if_pos h]
        · simp only [if_neg h]
      have hsum_eq : (Finset.univ.sum fun i : Fin J => (if mixed i then
              (∑ β ∈ F, ⨆ n : ℕ, ‖W n β X‖ₑ)
            else (∑ β ∈ F, ‖W (k i.succ) β X - W (k i.castSucc) β X‖ₑ)) ^ (R : ℝ))
          = Finset.univ.sum fun i : Fin J => (if mixed i then
              (∑ β ∈ F, ⨆ n : ℕ, ‖W n β X‖ₑ) ^ (R : ℝ)
            else (∑ β ∈ F, ‖W (k i.succ) β X - W (k i.castSucc) β X‖ₑ) ^ (R : ℝ)) :=
        Finset.sum_congr rfl fun i _ => hpt i
      rw [hsum_eq, Finset.sum_ite]
      have hcard : (∑ i ∈ (Finset.univ : Finset (Fin J)).filter mixed,
            ENNReal.rpow (∑ β ∈ F, ⨆ n : ℕ, ‖W n β X‖ₑ) (R : ℝ))
          ≤ ENNReal.rpow (∑ β ∈ F, ⨆ n : ℕ, ‖W n β X‖ₑ) (R : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        calc ((Finset.univ : Finset (Fin J)).filter mixed).card *
              ENNReal.rpow (∑ β ∈ F, ⨆ n : ℕ, ‖W n β X‖ₑ) (R : ℝ)
            ≤ (1 : ENNReal) * ENNReal.rpow (∑ β ∈ F, ⨆ n : ℕ, ‖W n β X‖ₑ) (R : ℝ) :=
              mul_le_mul_left (by rw [← Nat.cast_one]; exact Nat.cast_le.mpr hmixcard) _
          _ = ENNReal.rpow (∑ β ∈ F, ⨆ n : ℕ, ‖W n β X‖ₑ) (R : ℝ) := one_mul _
      rw [add_comm (∑ i : Fin J, ENNReal.rpow
        (∑ β ∈ F, ‖W (k i.succ) β X - W (k i.castSucc) β X‖ₑ) (R : ℝ))
        (ENNReal.rpow (∑ β ∈ F, ⨆ n : ℕ, ‖W n β X‖ₑ) (R : ℝ))]
      exact add_le_add hcard
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun i _ _ => bot_le))
    -- Minkowski in `ℓ^R` over the finite family `β`
    have hMink : ENNReal.rpow (Finset.univ.sum fun i : Fin J => ENNReal.rpow
          (∑ β ∈ F, ‖W (k i.succ) β X - W (k i.castSucc) β X‖ₑ) (R : ℝ)) (1 / (R : ℝ))
        ≤ V := by
      refine (Work.Analysis.Variation.rpow_sum_sum_le (r := (R : ℝ))
        (by exact_mod_cast hR) (Finset.univ : Finset (Fin J)) F
        (fun β i => ‖W (k i.succ) β X - W (k i.castSucc) β X‖ₑ)).trans ?_
      rw [hV]
      refine Finset.sum_le_sum fun β _ => ?_
      have hbridge := Work.KMTAreas.A7.ofReal_norm_toLp_eq_sum R hR
        (fun i : Fin J => W (k i.succ) β X - W (k i.castSucc) β X)
      rw [← hbridge]
      exact le_trans
        (ofReal_toLp_finChain_le_varPart R (fun n : ℕ => W n β X) k hk)
        (varPart_le_variationalNorm R _)
    have hAle : (∑ β ∈ F, ⨆ n : ℕ, ‖W n β X‖ₑ) ≤ V := by
      rw [hV]
      exact Finset.sum_le_sum fun β _ =>
        iSup_le fun n => Work.KMTAreas.A7.enorm_apply_le_variationalNorm (fun n : ℕ => W n β X) n
    have hRinv : 1 / (R : ℝ) ≤ 1 := by
      rw [one_div]
      exact inv_le_one_of_one_le₀ (by exact_mod_cast hR)
    have hRm : (R : ℝ) * (1 / (R : ℝ)) = 1 := by field_simp
    calc ENNReal.rpow (Finset.univ.sum fun i : Fin J => ENNReal.rpow
          (eLpNorm (u (k i.succ) - u (k i.castSucc)) 2 (Work.KMTPlan.A6.zmodProb Q))
          (R : ℝ)) (1 / (R : ℝ))
        ≤ ENNReal.rpow ((Finset.univ.sum fun i : Fin J => ENNReal.rpow
              (∑ β ∈ F, ‖W (k i.succ) β X - W (k i.castSucc) β X‖ₑ) (R : ℝ))
            + ENNReal.rpow (∑ β ∈ F, ⨆ n : ℕ, ‖W n β X‖ₑ) (R : ℝ)) (1 / (R : ℝ)) :=
          ENNReal.rpow_le_rpow hsum (by positivity)
      _ ≤ ENNReal.rpow (Finset.univ.sum fun i : Fin J => ENNReal.rpow
              (∑ β ∈ F, ‖W (k i.succ) β X - W (k i.castSucc) β X‖ₑ) (R : ℝ)) (1 / (R : ℝ))
            + ENNReal.rpow (ENNReal.rpow (∑ β ∈ F, ⨆ n : ℕ, ‖W n β X‖ₑ) (R : ℝ))
                (1 / (R : ℝ)) :=
          ENNReal.rpow_add_le_add_rpow _ _ (by positivity) hRinv
      _ = ENNReal.rpow (Finset.univ.sum fun i : Fin J => ENNReal.rpow
              (∑ β ∈ F, ‖W (k i.succ) β X - W (k i.castSucc) β X‖ₑ) (R : ℝ)) (1 / (R : ℝ))
            + (∑ β ∈ F, ⨆ n : ℕ, ‖W n β X‖ₑ) := by
          have hrw : ENNReal.rpow (ENNReal.rpow (∑ β ∈ F, ⨆ n : ℕ, ‖W n β X‖ₑ) (R : ℝ))
                (1 / (R : ℝ))
              = (∑ β ∈ F, ⨆ n : ℕ, ‖W n β X‖ₑ) ^ ((R : ℝ) * (1 / (R : ℝ))) :=
            (ENNReal.rpow_mul (∑ β ∈ F, ⨆ n : ℕ, ‖W n β X‖ₑ) (R : ℝ) (1 / (R : ℝ))).symm
          rw [hrw, hRm, ENNReal.rpow_one]
      _ ≤ V + V := add_le_add hMink hAle
      _ = 2 * V := by ring
  have hmain : Work.KMTPlan.A6.VrLiftDataP (R : ℝ) Q u ≤ 3 * V := by
    rw [Work.KMTPlan.A6.VrLiftDataP]
    calc (⨆ n : ℕ, eLpNorm (u n) 2 (Work.KMTPlan.A6.zmodProb Q))
          + (⨆ (J : ℕ) (k : Fin (J + 1) → ℕ) (_ : Monotone k), ENNReal.rpow
              (Finset.univ.sum fun i : Fin J => ENNReal.rpow
                (eLpNorm (u (k i.succ) - u (k i.castSucc)) 2 (Work.KMTPlan.A6.zmodProb Q))
                (R : ℝ)) (1 / (R : ℝ)))
        ≤ V + 2 * V := add_le_add hT1 hT2
      _ = 3 * V := by ring
  refine hmain.trans ?_
  have hVle : V ≤ (↑(F.card + 2) : ENNReal) * V := by
    have h1 : (1 : ENNReal) ≤ (↑(F.card + 2) : ENNReal) := by
      exact_mod_cast (by omega : 1 ≤ F.card + 2)
    calc V = 1 * V := (one_mul V).symm
      _ ≤ (↑(F.card + 2) : ENNReal) * V := mul_le_mul_left h1 V
  calc 3 * V ≤ 3 * ((↑(F.card + 2) : ENNReal) * V) := mul_le_mul_right hVle 3
    _ = (↑(3 * (F.card + 2)) : ENNReal) * V := by
        rw [Nat.cast_mul, Nat.cast_ofNat]
        ring

end Work.A6Clean
