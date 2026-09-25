import Mathlib
import Submission.Work.NN.Newton.FTdefs
import Submission.Work.NN.Newton.FTs2.S2_holderNorm_le_expl
import Submission.Work.NN.Newton.FTs2.dbarTransform_Eset_const
import Submission.Work.NN.Newton.FTs2.kappa_holderNorm_bound
import Submission.Work.NN.Newton.FTs2.kappabar_holderNorm_le
import Submission.Work.NN.Newton.FTs2.one_sub_kappa_holderNorm_bound

noncomputable section

namespace Work.NN.Newton.FTs2

open scoped NNReal ENNReal ContDiff
open Set

/-- The main assembly. -/
theorem ftS2_bound {n : ℕ} (hn : 0 < n) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ K : ℝ, 0 < K ∧ ∃ N : ℕ, ∀ (δ : ℝ) (hδ0 : 0 < δ) (hδ4 : δ ≤ 1 / 4)
      (E : Fin n → Fin n → (Fin n → ℂ) → ℂ),
      (∀ i l, ContDiff ℝ 1 (E i l)) → ∀ j : Fin n,
      Work.CR.Flat.holderNorm 1 α
          (Work.NN.Core.TelTwoDF.S2 (Work.NN.Newton.ftG (n := n) δ hδ0 hδ4) E j)
          (Work.CR.Flat.polydisc 0 (fun _ => 1 - δ))
        ≤ ENNReal.ofReal (K / δ ^ N) * ∑ a : Fin n, ∑ b : Fin n,
            Work.CR.Flat.holderNorm 1 α (E a b)
              (Work.CR.Flat.polydisc 0 (fun _ => 1 - 7 * δ / 8)) := by
  obtain ⟨M1, hM1pos, hM1⟩ := kappa_holderNorm_bound (n := n) hα0 hα1
  obtain ⟨M2, hM2pos, hM2⟩ := kappabar_holderNorm_le (n := n) hα0 hα1
  obtain ⟨M3, hM3pos, hM3⟩ := one_sub_kappa_holderNorm_bound (n := n) hα0 hα1
  set M : ℝ := max (max M1 M2) M3 with hMdef
  have hMpos : 0 < M := lt_of_lt_of_le hM1pos (le_trans (le_max_left _ _) (le_max_left _ _))
  have hM1le : M1 ≤ M := le_trans (le_max_left _ _) (le_max_left _ _)
  have hM2le : M2 ≤ M := le_trans (le_max_right _ _) (le_max_left _ _)
  have hM3le : M3 ≤ M := le_max_right _ _
  refine ⟨((n : ℝ) * (8 * (n:ℝ) + 1) * (8 * (n:ℝ) + 3) ^ n + 1) * (8 * M + 1) ^ (n + 1),
    ?_, 6 * (n + 1), ?_⟩
  · have h2 : (0:ℝ) < (8 * (n:ℝ) + 3) ^ n := by positivity
    have h3 : (0:ℝ) < (8 * M + 1) ^ (n + 1) := by positivity
    have h4 : (0:ℝ) < (n : ℝ) * (8 * (n:ℝ) + 1) * (8 * (n:ℝ) + 3) ^ n + 1 := by positivity
    exact mul_pos h4 h3
  · intro δ hδ0 hδ4 E hE j
    set G : Work.NN.Core.TelTwoDF.Geom n := Work.NN.Newton.ftG (n := n) δ hδ0 hδ4 with hGdef
    -- geometric facts
    have hr : ∀ t : Fin n, G.r t = 2 * (1 - 7 * δ / 8) := fun t => by
      rw [hGdef]; exact Work.NN.Newton.ftG_r δ hδ0 hδ4 t
    have hsumr : ∑ t : Fin n, G.r t = (n : ℝ) * (2 * (1 - 7 * δ / 8)) := by
      rw [Finset.sum_congr rfl (fun t _ => hr t), Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
    have hCTle : 4 * (∑ t : Fin n, G.r t) + 1 ≤ 8 * (n : ℝ) + 1 := by
      rw [hsumr]
      have hδnn : (0:ℝ) < δ := hδ0
      have hn0 : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      nlinarith [mul_nonneg hn0 hδnn.le]
    -- the transform bound with the uniform constant CT = 8n+1
    have hT : ∀ (s : Fin n) (g : (Fin n → ℂ) → ℂ), ContDiff ℝ 1 g →
        (∀ y : Fin n → ℂ, G.b s ≤ ‖y s‖ → g y = 0) →
        Work.CR.Flat.holderNorm 1 α (Work.CR.Flat.Cauchy.dbarTransform (G.r s) s g)
            (Work.NN.Core.TelTwoDF.Eset G ((s : ℕ) + 1))
          ≤ ENNReal.ofReal (8 * (n : ℝ) + 1) *
              Work.CR.Flat.holderNorm 1 α g (Work.NN.Core.TelTwoDF.Eset G (s : ℕ)) := by
      intro s g hg hsupp
      refine le_trans (dbarTransform_Eset_const (n := n) hα0 hα1 1 G s g hg hsupp) ?_
      exact mul_le_mul_left (ENNReal.ofReal_le_ofReal hCTle) _
    -- the multiplier bound
    have hcut : ∀ (s : Fin n) (χ : (Fin n → ℂ) → ℂ),
        Work.CR.Flat.holderNorm 1 α χ (Work.NN.Core.TelTwoDF.Eset G (s : ℕ))
            ≤ ENNReal.ofReal (M / δ ^ 6) →
        ContDiffOn ℝ (1 : ℕ∞) χ (Work.NN.Core.TelTwoDF.Eset G (s : ℕ)) →
        ∀ (f : (Fin n → ℂ) → ℂ), ContDiff ℝ 1 f →
        Work.CR.Flat.holderNorm 1 α (fun y => χ y * f y) (Work.NN.Core.TelTwoDF.Eset G (s : ℕ))
          ≤ ENNReal.ofReal (8 * M / δ ^ 6) *
              Work.CR.Flat.holderNorm 1 α f (Work.NN.Core.TelTwoDF.Eset G (s : ℕ)) := by
      intro s χ hχ hχc f hf
      have hξpos : (0:ℝ) < 8 * M / δ ^ 6 := by positivity
      have hξne : ENNReal.ofReal (8 * M / δ ^ 6) ≠ 0 := by
        rw [ENNReal.ofReal_ne_zero_iff]; exact hξpos
      by_cases hftop : Work.CR.Flat.holderNorm 1 α f (Work.NN.Core.TelTwoDF.Eset G (s : ℕ)) = ⊤
      · rw [hftop, ENNReal.mul_top hξne]
        exact le_top
      · have hχne : Work.CR.Flat.holderNorm 1 α χ (Work.NN.Core.TelTwoDF.Eset G (s : ℕ)) ≠ ⊤ :=
          ne_top_of_le_ne_top ENNReal.ofReal_ne_top hχ
        have hb := Work.CR.Flat.Holder.holderNorm_mul_le (k := 1) (α := α) hχc hf.contDiffOn
          (Work.NN.Core.TelTwoDF.isOpen_Eset G (s : ℕ)).uniqueDiffOn hχne hftop
        refine le_trans hb ?_
        have hconst8 : (((1 : ℕ) : ℝ≥0∞) + 1) * 2 ^ ((1 : ℕ) + 1) = (8 : ℝ≥0∞) := by norm_num
        rw [hconst8]
        have h8χ : (8 : ℝ≥0∞) * Work.CR.Flat.holderNorm 1 α χ (Work.NN.Core.TelTwoDF.Eset G (s : ℕ))
            ≤ ENNReal.ofReal (8 * M / δ ^ 6) := by
          calc (8 : ℝ≥0∞) * Work.CR.Flat.holderNorm 1 α χ (Work.NN.Core.TelTwoDF.Eset G (s : ℕ))
              ≤ (8 : ℝ≥0∞) * ENNReal.ofReal (M / δ ^ 6) := mul_le_mul_right hχ 8
            _ = ENNReal.ofReal 8 * ENNReal.ofReal (M / δ ^ 6) := by
                  rw [show (8 : ℝ≥0∞) = ENNReal.ofReal 8 from by norm_num]
            _ = ENNReal.ofReal (8 * (M / δ ^ 6)) := (ENNReal.ofReal_mul (by norm_num)).symm
            _ = ENNReal.ofReal (8 * M / δ ^ 6) := by
                  congr 1
                  ring
        exact mul_le_mul_left h8χ _
    -- the three cutoff bounds
    have hkey1 : ∀ s : Fin n, Work.CR.Flat.holderNorm 1 α (Work.NN.Core.TelTwoDF.kappa G s)
        (Work.NN.Core.TelTwoDF.Eset G (s : ℕ)) ≤ ENNReal.ofReal (M / δ ^ 6) := by
      intro s
      refine le_trans (hM1 δ hδ0 hδ4 s) ?_
      exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hM1le (by positivity))
    have hkey2 : ∀ s : Fin n, Work.CR.Flat.holderNorm 1 α (Work.NN.Core.TelTwoDF.kappabar G s)
        (Work.NN.Core.TelTwoDF.Eset G (s : ℕ)) ≤ ENNReal.ofReal (M / δ ^ 6) := by
      intro s
      refine le_trans (hM2 δ hδ0 hδ4 s) ?_
      exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hM2le (by positivity))
    have hkey3 : ∀ s : Fin n, Work.CR.Flat.holderNorm 1 α
        (fun z => 1 - Work.NN.Core.TelTwoDF.kappa G s z)
        (Work.NN.Core.TelTwoDF.Eset G (s : ℕ)) ≤ ENNReal.ofReal (M / δ ^ 6) := by
      intro s
      refine le_trans (hM3 δ hδ0 hδ4 s) ?_
      exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hM3le (by positivity))
    have hκ : ∀ (s : Fin n) (f : (Fin n → ℂ) → ℂ), ContDiff ℝ 1 f →
        Work.CR.Flat.holderNorm 1 α (fun y => Work.NN.Core.TelTwoDF.kappa G s y * f y)
            (Work.NN.Core.TelTwoDF.Eset G (s : ℕ))
          ≤ ENNReal.ofReal (8 * M / δ ^ 6) *
              Work.CR.Flat.holderNorm 1 α f (Work.NN.Core.TelTwoDF.Eset G (s : ℕ)) :=
      fun s f hf => hcut s _ (hkey1 s)
        ((Work.NN.Core.TelTwoDF.contDiff_kappa G s).of_le (by exact_mod_cast le_top)).contDiffOn f hf
    have hκbar : ∀ (s : Fin n) (f : (Fin n → ℂ) → ℂ), ContDiff ℝ 1 f →
        Work.CR.Flat.holderNorm 1 α (fun y => Work.NN.Core.TelTwoDF.kappabar G s y * f y)
            (Work.NN.Core.TelTwoDF.Eset G (s : ℕ))
          ≤ ENNReal.ofReal (8 * M / δ ^ 6) *
              Work.CR.Flat.holderNorm 1 α f (Work.NN.Core.TelTwoDF.Eset G (s : ℕ)) :=
      fun s f hf => hcut s _ (hkey2 s)
        ((Work.NN.Core.TelTwoDF.contDiff_kappabar G s).of_le (by exact_mod_cast le_top)).contDiffOn f hf
    have hcκ : ∀ (s : Fin n) (f : (Fin n → ℂ) → ℂ), ContDiff ℝ 1 f →
        Work.CR.Flat.holderNorm 1 α
            (fun y => (1 - Work.NN.Core.TelTwoDF.kappa G s y) * f y)
            (Work.NN.Core.TelTwoDF.Eset G (s : ℕ))
          ≤ ENNReal.ofReal (8 * M / δ ^ 6) *
              Work.CR.Flat.holderNorm 1 α f (Work.NN.Core.TelTwoDF.Eset G (s : ℕ)) :=
      fun s f hf => hcut s _ (hkey3 s)
        ((contDiff_const.sub (Work.NN.Core.TelTwoDF.contDiff_kappa G s)).of_le
            (by exact_mod_cast le_top)).contDiffOn f hf
    -- the telescoping estimate
    have hmain := Work.NN.Newton.FTs2.S2_holderNorm_le_expl (n := n) hα0 hα1 1 G
      (CT := 8 * (n:ℝ) + 1) (L := 8 * M / δ ^ 6)
      (by positivity) (by positivity) hT hκ hκbar hcκ E hE j
    -- identify the sets
    have hEn : Work.NN.Core.TelTwoDF.Eset G n = Work.CR.Flat.polydisc 0 (fun _ => 1 - δ) := by
      rw [Work.NN.Core.TelTwoDF.Eset_n]
      congr 1
    have hE0 : Work.NN.Core.TelTwoDF.Eset G 0
        = Work.CR.Flat.polydisc 0 (fun _ => 1 - 7 * δ / 8) := by
      rw [Work.NN.Core.TelTwoDF.Eset_zero]
      congr 1
    rw [hEn] at hmain
    simp only [hE0] at hmain
    -- the constant comparison
    have hconst : ENNReal.ofReal ((n : ℝ) * ((8 * (n:ℝ) + 1) * (8 * M / δ ^ 6)
          * ((8 * M / δ ^ 6) + (8 * (n:ℝ) + 1) * (8 * M / δ ^ 6) + 1) ^ n) + 1)
        ≤ ENNReal.ofReal (((n : ℝ) * (8 * (n:ℝ) + 1) * (8 * (n:ℝ) + 3) ^ n + 1)
            * (8 * M + 1) ^ (n + 1) / δ ^ (6 * (n + 1))) := by
      refine ENNReal.ofReal_le_ofReal ?_
      set L : ℝ := 8 * M / δ ^ 6 with hLdef
      set CT : ℝ := 8 * (n:ℝ) + 1 with hCTdef
      have hCTpos : 0 < CT := by rw [hCTdef]; positivity
      have hCT2pos : 0 < CT + 2 := by linarith
      have hδ6pos : 0 < δ ^ 6 := by positivity
      have hδ6le : δ ^ 6 ≤ 1 := by
        calc δ ^ 6 ≤ 1 ^ 6 := pow_le_pow_left₀ hδ0.le (by linarith) 6
          _ = 1 := one_pow 6
      have hLnn : 0 ≤ L := by rw [hLdef]; positivity
      have hLp1nn : 0 ≤ L + 1 := by linarith
      -- L + 1 ≤ (8M+1)/δ^6
      have hLp1 : L + 1 ≤ (8 * M + 1) / δ ^ 6 := by
        rw [hLdef, div_add' _ _ _ (ne_of_gt hδ6pos)]
        refine div_le_div_of_nonneg_right ?_ hδ6pos.le
        linarith
      -- L + CT*L + 1 ≤ (CT+2)*(L+1)
      have hstep1 : L + CT * L + 1 ≤ (CT + 2) * (L + 1) := by nlinarith [hLnn, hCTpos]
      have hstep2 : (L + CT * L + 1) ^ n ≤ ((CT + 2) * (L + 1)) ^ n :=
        pow_le_pow_left₀ (by positivity) hstep1 n
      rw [mul_pow] at hstep2
      -- assemble
      have hA : (n : ℝ) * (CT * L * (L + CT * L + 1) ^ n) + 1
          ≤ ((n : ℝ) * CT * (CT + 2) ^ n + 1) * (L + 1) ^ (n + 1) := by
        have h1 : CT * L * (L + CT * L + 1) ^ n ≤ CT * (CT + 2) ^ n * (L + 1) ^ (n + 1) := by
          calc CT * L * (L + CT * L + 1) ^ n
              ≤ CT * L * ((CT + 2) ^ n * (L + 1) ^ n) := by
                refine mul_le_mul_of_nonneg_left hstep2 (by positivity)
            _ = CT * (CT + 2) ^ n * (L * (L + 1) ^ n) := by ring
            _ ≤ CT * (CT + 2) ^ n * (L + 1) ^ (n + 1) := by
                refine mul_le_mul_of_nonneg_left ?_ (by positivity)
                calc L * (L + 1) ^ n ≤ (L + 1) * (L + 1) ^ n :=
                      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
                  _ = (L + 1) ^ (n + 1) := by rw [pow_succ']
        have h2 : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        have h3 : (n : ℝ) * (CT * L * (L + CT * L + 1) ^ n)
            ≤ (n : ℝ) * (CT * (CT + 2) ^ n * (L + 1) ^ (n + 1)) :=
          mul_le_mul_of_nonneg_left h1 h2
        have h4 : (1:ℝ) ≤ (L + 1) ^ (n + 1) := one_le_pow₀ (by linarith)
        have h5 : 0 ≤ (n : ℝ) * CT * (CT + 2) ^ n := by positivity
        calc (n : ℝ) * (CT * L * (L + CT * L + 1) ^ n) + 1
            ≤ (n : ℝ) * (CT * (CT + 2) ^ n * (L + 1) ^ (n + 1)) + (L + 1) ^ (n + 1) := by
              linarith
          _ = ((n : ℝ) * CT * (CT + 2) ^ n) * (L + 1) ^ (n + 1) + (L + 1) ^ (n + 1) := by ring
          _ = ((n : ℝ) * CT * (CT + 2) ^ n + 1) * (L + 1) ^ (n + 1) := by ring
      have hB : (L + 1) ^ (n + 1) ≤ (8 * M + 1) ^ (n + 1) / δ ^ (6 * (n + 1)) := by
        have h1 : L + 1 ≤ (8 * M + 1) / δ ^ 6 := hLp1
        calc (L + 1) ^ (n + 1) ≤ ((8 * M + 1) / δ ^ 6) ^ (n + 1) :=
              pow_le_pow_left₀ hLp1nn h1 _
          _ = (8 * M + 1) ^ (n + 1) / δ ^ (6 * (n + 1)) := by
              rw [div_pow, ← pow_mul]
      have hC : ((n : ℝ) * CT * (CT + 2) ^ n + 1) * (L + 1) ^ (n + 1)
          ≤ ((n : ℝ) * CT * (CT + 2) ^ n + 1)
              * ((8 * M + 1) ^ (n + 1) / δ ^ (6 * (n + 1))) :=
        mul_le_mul_of_nonneg_left hB (by positivity)
      calc (n : ℝ) * (CT * L * (L + CT * L + 1) ^ n) + 1
          ≤ ((n : ℝ) * CT * (CT + 2) ^ n + 1) * (L + 1) ^ (n + 1) := hA
        _ ≤ ((n : ℝ) * CT * (CT + 2) ^ n + 1)
              * ((8 * M + 1) ^ (n + 1) / δ ^ (6 * (n + 1))) := hC
        _ = ((n : ℝ) * (8 * (n:ℝ) + 1) * (8 * (n:ℝ) + 3) ^ n + 1)
              * (8 * M + 1) ^ (n + 1) / δ ^ (6 * (n + 1)) := by
              rw [hCTdef]; ring
    exact le_trans hmain (mul_le_mul_left hconst _)



end Work.NN.Newton.FTs2
