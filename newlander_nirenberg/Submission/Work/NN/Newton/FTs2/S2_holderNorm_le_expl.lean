import Mathlib
import Submission.Work.NN.Core.TelTwoDF.S2Bound
import Submission.Work.NN.Core.TelTwoDF.Setup

set_option maxHeartbeats 4000000

noncomputable section

open scoped NNReal ENNReal ContDiff
open Set

namespace Work.NN.Newton.FTs2

open Work.NN.Core.TelTwoDF

theorem S2_holderNorm_le_expl {n : ℕ} {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (k : ℕ)
    (G : Work.NN.Core.TelTwoDF.Geom n) {CT L : ℝ} (hCT : 0 < CT) (hL : 0 < L)
    (hT : ∀ (s : Fin n) (g : (Fin n → ℂ) → ℂ), ContDiff ℝ k g →
      (∀ y : Fin n → ℂ, G.b s ≤ ‖y s‖ → g y = 0) →
      Work.CR.Flat.holderNorm k α (Work.CR.Flat.Cauchy.dbarTransform (G.r s) s g)
          (Work.NN.Core.TelTwoDF.Eset G ((s : ℕ) + 1))
        ≤ ENNReal.ofReal CT * Work.CR.Flat.holderNorm k α g (Work.NN.Core.TelTwoDF.Eset G (s : ℕ)))
    (hκ : ∀ (s : Fin n) (f : (Fin n → ℂ) → ℂ), ContDiff ℝ k f →
      Work.CR.Flat.holderNorm k α (fun y => Work.NN.Core.TelTwoDF.kappa G s y * f y)
          (Work.NN.Core.TelTwoDF.Eset G (s : ℕ))
        ≤ ENNReal.ofReal L * Work.CR.Flat.holderNorm k α f (Work.NN.Core.TelTwoDF.Eset G (s : ℕ)))
    (hκbar : ∀ (s : Fin n) (f : (Fin n → ℂ) → ℂ), ContDiff ℝ k f →
      Work.CR.Flat.holderNorm k α (fun y => Work.NN.Core.TelTwoDF.kappabar G s y * f y)
          (Work.NN.Core.TelTwoDF.Eset G (s : ℕ))
        ≤ ENNReal.ofReal L * Work.CR.Flat.holderNorm k α f (Work.NN.Core.TelTwoDF.Eset G (s : ℕ)))
    (hcκ : ∀ (s : Fin n) (f : (Fin n → ℂ) → ℂ), ContDiff ℝ k f →
      Work.CR.Flat.holderNorm k α (fun y => (1 - Work.NN.Core.TelTwoDF.kappa G s y) * f y)
          (Work.NN.Core.TelTwoDF.Eset G (s : ℕ))
        ≤ ENNReal.ofReal L * Work.CR.Flat.holderNorm k α f (Work.NN.Core.TelTwoDF.Eset G (s : ℕ)))
    (η : Fin n → Fin n → (Fin n → ℂ) → ℂ) (hη : ∀ i l, ContDiff ℝ k (η i l)) (j : Fin n) :
    Work.CR.Flat.holderNorm k α (Work.NN.Core.TelTwoDF.S2 G η j) (Work.NN.Core.TelTwoDF.Eset G n)
      ≤ ENNReal.ofReal ((n : ℝ) * (CT * L * (L + CT * L + 1) ^ n) + 1)
        * ∑ i : Fin n, ∑ l : Fin n,
            Work.CR.Flat.holderNorm k α (η i l) (Work.NN.Core.TelTwoDF.Eset G 0) := by
  -- the one-step constant
  set Kl : ENNReal := ENNReal.ofReal (L + CT * L + 1) with hKldef
  have hKlnn : (0 : ℝ) ≤ L + CT * L + 1 := by nlinarith [hCT, hL]
  have hKlne : Kl ≠ ⊤ := by rw [hKldef]; exact ENNReal.ofReal_ne_top
  have hKl1 : 1 ≤ Kl := by
    rw [hKldef]
    exact ENNReal.one_le_ofReal.mpr (by nlinarith [mul_pos hCT hL])
  have hLKl : ENNReal.ofReal L ≤ Kl := by
    rw [hKldef]
    exact ENNReal.ofReal_le_ofReal (by nlinarith [mul_pos hCT hL])
  have hTLKl : ENNReal.ofReal CT * ENNReal.ofReal L ≤ Kl := by
    rw [hKldef, ← ENNReal.ofReal_mul hCT.le]
    exact ENNReal.ofReal_le_ofReal (by nlinarith [hCT, hL])
  have hsumKl : ENNReal.ofReal L + ENNReal.ofReal CT * ENNReal.ofReal L ≤ Kl := by
    rw [hKldef, ← ENNReal.ofReal_mul hCT.le,
      ← ENNReal.ofReal_add hL.le (mul_nonneg hCT.le hL.le)]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  -- the three multiplier bounds, repackaged in the "finite bound `B`" form
  have hL1 : ∀ (s : Fin n) (f : (Fin n → ℂ) → ℂ), ContDiff ℝ k f → ∀ B : ENNReal, B ≠ ⊤ →
      Work.CR.Flat.holderNorm k α f (Eset G (s : ℕ)) ≤ B →
      Work.CR.Flat.holderNorm k α (fun y => kappa G s y * f y) (Eset G (s : ℕ))
        ≤ ENNReal.ofReal L * B := by
    intro s f hf B hB hBf
    exact le_trans (hκ s f hf) (mul_le_mul_right hBf (ENNReal.ofReal L))
  have hL2 : ∀ (s : Fin n) (f : (Fin n → ℂ) → ℂ), ContDiff ℝ k f → ∀ B : ENNReal, B ≠ ⊤ →
      Work.CR.Flat.holderNorm k α f (Eset G (s : ℕ)) ≤ B →
      Work.CR.Flat.holderNorm k α (fun y => kappabar G s y * f y) (Eset G (s : ℕ))
        ≤ ENNReal.ofReal L * B := by
    intro s f hf B hB hBf
    exact le_trans (hκbar s f hf) (mul_le_mul_right hBf (ENNReal.ofReal L))
  have hL3 : ∀ (s : Fin n) (f : (Fin n → ℂ) → ℂ), ContDiff ℝ k f → ∀ B : ENNReal, B ≠ ⊤ →
      Work.CR.Flat.holderNorm k α f (Eset G (s : ℕ)) ≤ B →
      Work.CR.Flat.holderNorm k α (fun y => (1 - kappa G s y) * f y) (Eset G (s : ℕ))
        ≤ ENNReal.ofReal L * B := by
    intro s f hf B hB hBf
    exact le_trans (hcκ s f hf) (mul_le_mul_right hBf (ENNReal.ofReal L))
  -- the one-step bound
  have hstep : ∀ (s : Fin n) (D : Fin n → Fin n → (Fin n → ℂ) → ℂ),
      (∀ i l, ContDiff ℝ k (D i l)) → ∀ A : ENNReal, A ≠ ⊤ →
      (∀ i l, Work.CR.Flat.holderNorm k α (D i l) (Eset G (s : ℕ)) ≤ A) →
      ∀ i l, Work.CR.Flat.holderNorm k α (uStep G s D i l) (Eset G ((s : ℕ) + 1)) ≤ Kl * A := by
    intro s D hD A hA hAb i l
    have hmono : ∀ {g : (Fin n → ℂ) → ℂ},
        Work.CR.Flat.holderNorm k α g (Eset G ((s : ℕ) + 1))
          ≤ Work.CR.Flat.holderNorm k α g (Eset G (s : ℕ)) := fun {g} =>
      Work.CR.Flat.holderNorm_mono_set (isOpen_Eset G (s : ℕ)) (isOpen_Eset G ((s : ℕ) + 1))
        (Eset_succ_subset G (s : ℕ)) k α g
    have hdir : Work.CR.Flat.holderNorm k α
        (fun z => (1 - kappa G s z) * D i l z) (Eset G ((s : ℕ) + 1)) ≤ ENNReal.ofReal L * A :=
      le_trans hmono (hL3 s (D i l) (hD i l) A hA (hAb i l))
    have hg : ContDiff ℝ k (fun y : Fin n → ℂ => kappabar G s y * D i l y) :=
      ((contDiff_kappabar G s).of_le (by exact_mod_cast le_top)).mul (hD i l)
    have hTLc : ContDiff ℝ k (fun z => TL G s (fun y => kappabar G s y * D i l y) z) := by
      change ContDiff ℝ k (TL G s fun y => kappabar G s y * D i l y)
      rw [TL_eq G s hg.continuous]
      exact contDiff_dbarTransform_univ (G.b_pos s).le s k hg
        (fun y hy => by rw [kappabar_eq_zero_of_ge G s hy, zero_mul])
    have htr : Work.CR.Flat.holderNorm k α
        (fun z => TL G s (fun y => kappabar G s y * D i l y) z) (Eset G ((s : ℕ) + 1))
        ≤ ENNReal.ofReal CT * ENNReal.ofReal L * A := by
      have heq : (fun z => TL G s (fun y => kappabar G s y * D i l y) z)
          = Work.CR.Flat.Cauchy.dbarTransform (G.r s) s
              (fun y => kappabar G s y * D i l y) := by
        rw [show (fun z => TL G s (fun y => kappabar G s y * D i l y) z)
            = TL G s (fun y => kappabar G s y * D i l y) from rfl, TL_eq G s hg.continuous]
      rw [heq]
      have h1 : Work.CR.Flat.holderNorm k α (Work.CR.Flat.Cauchy.dbarTransform (G.r s) s
            (fun y => kappabar G s y * D i l y)) (Eset G ((s : ℕ) + 1))
          ≤ ENNReal.ofReal CT * Work.CR.Flat.holderNorm k α
              (fun y => kappabar G s y * D i l y) (Eset G (s : ℕ)) :=
        hT s (fun y => kappabar G s y * D i l y) hg
          (fun y hy => by rw [kappabar_eq_zero_of_ge G s hy, zero_mul])
      have h2 : Work.CR.Flat.holderNorm k α (fun y => kappabar G s y * D i l y)
          (Eset G (s : ℕ)) ≤ ENNReal.ofReal L * A :=
        hL2 s (D i l) (hD i l) A hA (hAb i l)
      calc Work.CR.Flat.holderNorm k α (Work.CR.Flat.Cauchy.dbarTransform (G.r s) s
              (fun y => kappabar G s y * D i l y)) (Eset G ((s : ℕ) + 1))
          ≤ ENNReal.ofReal CT * Work.CR.Flat.holderNorm k α
              (fun y => kappabar G s y * D i l y) (Eset G (s : ℕ)) := h1
        _ ≤ ENNReal.ofReal CT * (ENNReal.ofReal L * A) := mul_le_mul_right h2 (ENNReal.ofReal CT)
        _ = ENNReal.ofReal CT * ENNReal.ofReal L * A := by rw [mul_assoc]
    by_cases hc : i = s ∨ l = s
    · rw [show uStep G s D i l = fun z => (1 - kappa G s z) * D i l z from by
        funext z; rw [uStep_apply, if_pos hc]; ring]
      exact le_trans hdir (mul_le_mul_left hLKl A)
    · rw [show uStep G s D i l = fun z => (1 - kappa G s z) * D i l z
          + TL G s (fun y => kappabar G s y * D i l y) z from by
        funext z; rw [uStep_apply, if_neg hc]]
      refine le_trans (Work.CR.Flat.Holder.holderNorm_add_le (k := k) (α := α)
        (f := fun z => (1 - kappa G s z) * D i l z)
        (g := fun z => TL G s (fun y => kappabar G s y * D i l y) z)
        (Ω := Eset G ((s : ℕ) + 1))
        ((((contDiff_const.sub (contDiff_kappa G s)).of_le (by exact_mod_cast le_top)).mul
          (hD i l)).contDiffOn) hTLc.contDiffOn
        (isOpen_Eset G ((s : ℕ) + 1)).uniqueDiffOn) ?_
      refine le_trans (add_le_add hdir htr) ?_
      rw [← add_mul]
      exact mul_le_mul_left hsumKl A
  -- the stage bound
  have hiter : ∀ (η : Fin n → Fin n → (Fin n → ℂ) → ℂ), (∀ i l, ContDiff ℝ k (η i l)) →
      datumSum k α G η ≠ ⊤ → ∀ m ≤ n, ∀ i l,
      Work.CR.Flat.holderNorm k α (uD G η m i l) (Eset G m) ≤ Kl ^ m * datumSum k α G η := by
    intro η hη hS m
    induction m with
    | zero =>
        intro _ i l
        rw [uD_zero, pow_zero, one_mul]
        exact le_datumSum i l
    | succ m ih =>
        intro hm i l
        have hm' : m < n := by omega
        have hIH : ∀ i' l', Work.CR.Flat.holderNorm k α (uD G η m i' l') (Eset G m)
            ≤ Kl ^ m * datumSum k α G η := fun i' l' => ih (by omega) i' l'
        have hAne : Kl ^ m * datumSum k α G η ≠ ⊤ :=
          ENNReal.mul_ne_top (ENNReal.pow_ne_top hKlne) hS
        rw [uD_succ_of_lt G η hm']
        refine le_trans (hstep ⟨m, hm'⟩ (uD G η m) (fun i l => uD_contDiff_k G hη m (by omega) i l)
          (Kl ^ m * datumSum k α G η) hAne hIH i l) ?_
        rw [pow_succ]
        exact le_of_eq (by ac_rfl)
  -- the summand bound
  have hpsi : ∀ (η : Fin n → Fin n → (Fin n → ℂ) → ℂ), (∀ i l, ContDiff ℝ k (η i l)) →
      datumSum k α G η ≠ ⊤ → ∀ s l,
      Work.CR.Flat.holderNorm k α (uPsi G η s l) (Eset G n)
        ≤ (ENNReal.ofReal CT * ENNReal.ofReal L * Kl ^ n) * datumSum k α G η := by
    intro η hη hS s l
    have hD : ContDiff ℝ k (uD G η (s : ℕ) s l) :=
      uD_contDiff_k G hη (s : ℕ) (le_of_lt s.isLt) s l
    have hg : ContDiff ℝ k (fun y : Fin n → ℂ => kappa G s y * uD G η (s : ℕ) s l y) :=
      ((contDiff_kappa G s).of_le (by exact_mod_cast le_top)).mul hD
    have heq : uPsi G η s l = Work.CR.Flat.Cauchy.dbarTransform (G.r s) s
        (fun y => kappa G s y * uD G η (s : ℕ) s l y) := by
      rw [show uPsi G η s l = TL G s (fun y => kappa G s y * uD G η (s : ℕ) s l y) from rfl,
        TL_eq G s hg.continuous]
    have hB : Kl ^ (s : ℕ) * datumSum k α G η ≠ ⊤ :=
      ENNReal.mul_ne_top (ENNReal.pow_ne_top hKlne) hS
    have hcut := hL1 s (uD G η (s : ℕ) s l) hD (Kl ^ (s : ℕ) * datumSum k α G η) hB
      (hiter η hη hS (s : ℕ) (le_of_lt s.isLt) s l)
    have hmono : Work.CR.Flat.holderNorm k α (uPsi G η s l) (Eset G n)
        ≤ Work.CR.Flat.holderNorm k α (uPsi G η s l) (Eset G ((s : ℕ) + 1)) :=
      Work.CR.Flat.holderNorm_mono_set (Ω := Eset G ((s : ℕ) + 1)) (Ω' := Eset G n)
        (isOpen_Eset G ((s : ℕ) + 1)) (isOpen_Eset G n)
        (Eset_mono G (by omega : (s : ℕ) + 1 ≤ n)) k α (uPsi G η s l)
    have h1 : Work.CR.Flat.holderNorm k α (uPsi G η s l) (Eset G ((s : ℕ) + 1))
        ≤ ENNReal.ofReal CT * Work.CR.Flat.holderNorm k α
            (fun y => kappa G s y * uD G η (s : ℕ) s l y) (Eset G (s : ℕ)) := by
      rw [heq]
      exact hT s _ hg (fun y hy => by rw [kappa_eq_zero G s hy, zero_mul])
    have h2 : Work.CR.Flat.holderNorm k α (fun y => kappa G s y * uD G η (s : ℕ) s l y)
        (Eset G (s : ℕ)) ≤ ENNReal.ofReal L * (Kl ^ (s : ℕ) * datumSum k α G η) := hcut
    have h3 : Kl ^ (s : ℕ) * datumSum k α G η ≤ Kl ^ n * datumSum k α G η :=
      mul_le_mul_left (pow_le_pow_right₀ hKl1 (le_of_lt s.isLt)) (datumSum k α G η)
    calc Work.CR.Flat.holderNorm k α (uPsi G η s l) (Eset G n)
        ≤ Work.CR.Flat.holderNorm k α (uPsi G η s l) (Eset G ((s : ℕ) + 1)) := hmono
      _ ≤ ENNReal.ofReal CT * Work.CR.Flat.holderNorm k α
            (fun y => kappa G s y * uD G η (s : ℕ) s l y) (Eset G (s : ℕ)) := h1
      _ ≤ ENNReal.ofReal CT * (ENNReal.ofReal L * (Kl ^ (s : ℕ) * datumSum k α G η)) :=
            mul_le_mul_right h2 (ENNReal.ofReal CT)
      _ ≤ ENNReal.ofReal CT * (ENNReal.ofReal L * (Kl ^ n * datumSum k α G η)) :=
            mul_le_mul_right (mul_le_mul_right h3 (ENNReal.ofReal L)) (ENNReal.ofReal CT)
      _ = (ENNReal.ofReal CT * ENNReal.ofReal L * Kl ^ n) * datumSum k α G η := by ac_rfl
  -- the final assembly
  have hfinal : ∀ (η : Fin n → Fin n → (Fin n → ℂ) → ℂ), (∀ i l, ContDiff ℝ k (η i l)) →
      datumSum k α G η ≠ ⊤ → ∀ j : Fin n,
      Work.CR.Flat.holderNorm k α (S2 G η j) (Eset G n)
        ≤ ((n : ENNReal) * (ENNReal.ofReal CT * ENNReal.ofReal L * Kl ^ n)) * datumSum k α G η := by
    intro η hη hS j
    have hS2eq : S2 G η j = fun z => ∑ s ∈ Finset.univ, uPsi G η s j z := by
      funext z
      rw [S2_apply]
    rw [hS2eq]
    refine le_trans (Work.CR.Flat.Holder.holderNorm_sum_le (k := k) (α := α) Finset.univ
      (fun s _ => (uPsi_contDiff_k G hη s j).contDiffOn)
      (isOpen_Eset G n).uniqueDiffOn) ?_
    calc ∑ s ∈ Finset.univ, Work.CR.Flat.holderNorm k α (uPsi G η s j) (Eset G n)
        ≤ ∑ _s ∈ Finset.univ, (ENNReal.ofReal CT * ENNReal.ofReal L * Kl ^ n) * datumSum k α G η :=
          Finset.sum_le_sum fun s _ => hpsi η hη hS s j
      _ = (n : ENNReal) * ((ENNReal.ofReal CT * ENNReal.ofReal L * Kl ^ n) * datumSum k α G η) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = ((n : ENNReal) * (ENNReal.ofReal CT * ENNReal.ofReal L * Kl ^ n)) * datumSum k α G η := by
          ac_rfl
  -- the constant comparison
  have hKlpow : Kl ^ n = ENNReal.ofReal ((L + CT * L + 1) ^ n) := by
    rw [hKldef, ← ENNReal.ofReal_pow hKlnn]
  have hC0eq : (n : ENNReal) * (ENNReal.ofReal CT * ENNReal.ofReal L * Kl ^ n)
      = ENNReal.ofReal ((n : ℝ) * (CT * L * (L + CT * L + 1) ^ n)) := by
    rw [hKlpow, ← ENNReal.ofReal_mul hCT.le,
      ← ENNReal.ofReal_mul (mul_nonneg hCT.le hL.le), ← ENNReal.ofReal_natCast n,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg n)]
  have hC0le : (n : ENNReal) * (ENNReal.ofReal CT * ENNReal.ofReal L * Kl ^ n)
      ≤ ENNReal.ofReal ((n : ℝ) * (CT * L * (L + CT * L + 1) ^ n) + 1) := by
    rw [hC0eq]
    refine ENNReal.ofReal_le_ofReal ?_
    have : (0 : ℝ) ≤ (n : ℝ) * (CT * L * (L + CT * L + 1) ^ n) := by positivity
    linarith
  by_cases hS : datumSum k α G η = ⊤
  · have hS' : (∑ i : Fin n, ∑ l : Fin n,
        Work.CR.Flat.holderNorm k α (η i l) (Eset G 0)) = ⊤ := hS
    rw [hS', ENNReal.mul_top]
    · exact le_top
    · intro h0
      have hKpos : 0 < L + CT * L + 1 := by nlinarith [hCT, hL]
      have hprod : 0 < (n : ℝ) * (CT * L * (L + CT * L + 1) ^ n) + 1 := by
        have hp : 0 < (L + CT * L + 1) ^ n := pow_pos hKpos n
        have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        have hctl : 0 < CT * L := mul_pos hCT hL
        nlinarith [mul_nonneg hn (mul_nonneg hctl.le hp.le)]
      exact absurd h0 (ne_of_gt (ENNReal.ofReal_pos.mpr hprod))
  · refine le_trans (hfinal η hη hS j) ?_
    rw [datumSum]
    exact mul_le_mul_left hC0le _

end Work.NN.Newton.FTs2
