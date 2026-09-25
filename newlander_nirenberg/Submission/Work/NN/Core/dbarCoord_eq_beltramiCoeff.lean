import Mathlib
import Submission.Work.NN.Core.DbarCnPertAux
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.CR.Flat.Holder
import Submission.Work.NN.Core.betaCoef_Bop_contDiff
import Submission.Work.NN.Core.norm_Bop_le
import Submission.Work.NN.Core.isInvertible_one_add_and_inverse_norm_le
import Submission.Work.NN.Core.Bop_map_smul
import Submission.Work.NN.Core.inverse_one_add_map_smul

noncomputable section

open scoped NNReal ENNReal ContDiff
open Set

namespace Work.NN.Core

variable {n : ℕ}

/-- Smallness of `BopBar`: `‖BopBar A z‖ ≤ 1/4` under the standing hypothesis
`‖A z‖ ≤ 1/(2n)`. -/
lemma norm_BopBar_le_quarter (hn : 0 < n) (A : Cn n → Cn n →L[ℝ] Cn n)
    (hsmall : ∀ z, ‖A z‖ ≤ 1 / (2 * (n : ℝ))) (z : Cn n) :
    ‖BopBar A z‖ ≤ 1 / 4 := by
  have h1 : (n : ℝ) * ‖A z‖ / 2 ≤ 1 / 4 := by
    have h2 : (n : ℝ) * (1 / (2 * (n : ℝ))) / 2 = 1 / 4 := by
      field_simp
      ring
    calc (n : ℝ) * ‖A z‖ / 2 ≤ (n : ℝ) * (1 / (2 * (n : ℝ))) / 2 := by
          gcongr
          exact hsmall z
      _ = 1 / 4 := h2
  exact le_trans (norm_Bop_le A z).2 h1

/-- Norm bound for the decoupled Beltrami coefficient. -/
lemma norm_beltramiCoeff_le (hn : 0 < n) (A : Cn n → Cn n →L[ℝ] Cn n)
    (hsmall : ∀ z, ‖A z‖ ≤ 1 / (2 * (n : ℝ))) (z : Cn n) :
    ‖beltramiCoeff A z‖ ≤ (n : ℝ) * ‖A z‖ := by
  have hq : ‖BopBar A z‖ ≤ 1 / 4 := norm_BopBar_le_quarter hn A hsmall z
  have hInvN : ‖ContinuousLinearMap.inverse (1 + BopBar A z)‖ ≤ 2 :=
    (isInvertible_one_add_and_inverse_norm_le hq).2
  have hB : ‖Bop A z‖ ≤ (n : ℝ) * ‖A z‖ / 2 := (norm_Bop_le A z).1
  have h1 : ‖beltramiCoeff A z‖
      ≤ ‖ContinuousLinearMap.inverse (1 + BopBar A z)‖ * ‖Bop A z‖ := by
    rw [beltramiCoeff]
    exact norm_mul_le _ _
  calc ‖beltramiCoeff A z‖
      ≤ ‖ContinuousLinearMap.inverse (1 + BopBar A z)‖ * ‖Bop A z‖ := h1
    _ ≤ 2 * ((n : ℝ) * ‖A z‖ / 2) :=
        mul_le_mul hInvN hB (norm_nonneg _) (by norm_num)
    _ = (n : ℝ) * ‖A z‖ := by ring

/-- Complex-linearity of the decoupled Beltrami coefficient `beltramiCoeff A z`. -/
lemma beltramiCoeff_map_smul (hn : 0 < n) (A : Cn n → Cn n →L[ℝ] Cn n)
    (hsmall : ∀ z, ‖A z‖ ≤ 1 / (2 * (n : ℝ))) (z : Cn n) (c : ℂ) (v : Cn n) :
    beltramiCoeff A z (c • v) = c • beltramiCoeff A z v := by
  have hbar : (1 + BopBar A z).IsInvertible :=
    (isInvertible_one_add_and_inverse_norm_le (norm_BopBar_le_quarter hn A hsmall z)).1
  have hlin : ∀ (c : ℂ) (v : Cn n), BopBar A z (c • v) = c • BopBar A z v :=
    fun c v => (Bop_map_smul A z v c).2
  rw [beltramiCoeff, mul_apply_eq_comp,
    mul_apply_eq_comp, (Bop_map_smul A z v c).1]
  exact inverse_one_add_map_smul hbar hlin c (Bop A z v)

theorem dbarCoord_eq_beltramiCoeff {n : ℕ} (hn : 0 < n) (A : Cn n → Cn n →L[ℝ] Cn n)
    (hA : ∀ m, ContDiff ℝ m A) (hsmall : ∀ z, ‖A z‖ ≤ 1 / (2 * (n : ℝ))) :
    (∀ k j, ContDiff ℝ ⊤ (beltramiCoef A k j)) ∧
    (∀ k j z, ‖beltramiCoef A k j z‖ ≤ (n : ℝ) * ‖A z‖) ∧
    (∀ (u : Cn n → ℂ) (z : Cn n), dbarCn (JstdCn n + A) u z = 0 →
      ∀ k, Work.CR.Flat.dbarCoord k u z
        = ∑ j : Fin n, beltramiCoef A k j z * Work.CR.Flat.dCoord j u z) := by
  have hBop : ContDiff ℝ ⊤ (fun z => Bop A z) := (betaCoef_Bop_contDiff A hA).2.1
  have hBopBar : ContDiff ℝ ⊤ (fun z => BopBar A z) := (betaCoef_Bop_contDiff A hA).2.2
  have hquarter : ∀ z, ‖BopBar A z‖ ≤ 1 / 4 := norm_BopBar_le_quarter hn A hsmall
  have hInv : ∀ z, (1 + BopBar A z).IsInvertible := fun z =>
    (isInvertible_one_add_and_inverse_norm_le (hquarter z)).1
  refine ⟨?_, ?_, ?_⟩
  · intro k j
    have hY : ContDiff ℝ ⊤ (fun z => ContinuousLinearMap.inverse (1 + BopBar A z)) := by
      rw [contDiff_iff_contDiffAt]
      intro z
      have hz : ContDiffAt ℝ ⊤ (fun w => (1 : Cn n →L[ℝ] Cn n) + BopBar A w) z :=
        ((contDiff_const (c := (1 : Cn n →L[ℝ] Cn n))).add hBopBar).contDiffAt
      have h := (ContinuousLinearMap.IsInvertible.contDiffAt_map_inverse (hInv z)).comp z hz
      simpa only [Function.comp_def] using h
    have hY' : ContDiff ℝ ⊤ (fun z : Cn n =>
        (ContinuousLinearMap.inverse (1 + BopBar A z) : Cn n →L[ℝ] Cn n)) := hY
    have hΨ : ContDiff ℝ ⊤ (fun z : Cn n =>
        (ContinuousLinearMap.inverse (1 + BopBar A z) : Cn n →L[ℝ] Cn n) ∘SL Bop A z) :=
      hY'.clm_comp hBop
    have h1 : ContDiff ℝ ⊤ (fun z : Cn n =>
        ((ContinuousLinearMap.inverse (1 + BopBar A z) : Cn n →L[ℝ] Cn n) ∘SL Bop A z)
          (Pi.single j (1 : ℂ) : Cn n)) :=
      hΨ.clm_apply (contDiff_const : ContDiff ℝ ⊤
        (fun _ : Cn n => (Pi.single j (1 : ℂ) : Cn n)))
    have h2 : ContDiff ℝ ⊤ (fun z : Cn n =>
        (ContinuousLinearMap.proj k : Cn n →L[ℝ] ℂ)
          (((ContinuousLinearMap.inverse (1 + BopBar A z) : Cn n →L[ℝ] Cn n) ∘SL Bop A z)
            (Pi.single j (1 : ℂ) : Cn n))) :=
      ((ContinuousLinearMap.proj k : Cn n →L[ℝ] ℂ).contDiff).comp h1
    convert h2 using 1
    ext z
    simp only [beltramiCoef, beltramiCoeff, mul_apply_eq_comp, ContinuousLinearMap.proj_apply,
      ContinuousLinearMap.comp_apply]
  · intro k j z
    calc ‖beltramiCoef A k j z‖
        = ‖beltramiCoeff A z (Pi.single j (1 : ℂ)) k‖ := by
          rw [beltramiCoef]
      _ ≤ ‖beltramiCoeff A z (Pi.single j (1 : ℂ))‖ := norm_le_pi_norm _ k
      _ ≤ ‖beltramiCoeff A z‖ * ‖(Pi.single j (1 : ℂ) : Cn n)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ = ‖beltramiCoeff A z‖ := by rw [Pi.norm_single, norm_one, mul_one]
      _ ≤ (n : ℝ) * ‖A z‖ := norm_beltramiCoeff_le hn A hsmall z
  · intro u z hz k
    have hsys : (1 + BopBar A z) (fun j => Work.CR.Flat.dbarCoord j u z)
        = Bop A z (fun j => Work.CR.Flat.dCoord j u z) := by
      have hcoe : (1 + BopBar A z) (fun j => Work.CR.Flat.dbarCoord j u z)
          = (fun j => Work.CR.Flat.dbarCoord j u z)
            + BopBar A z (fun j => Work.CR.Flat.dbarCoord j u z) := by
        rw [add_apply, one_apply_eq_self]
      ext k
      have hk : Work.CR.Flat.dbarCoord k u z
          = (Bop A z (fun j => Work.CR.Flat.dCoord j u z)) k
            - (BopBar A z (fun j => Work.CR.Flat.dbarCoord j u z)) k := by
        rw [dbarCoord_eq_beltrami_implicit hz k, Bop_apply, BopBar_apply,
          Finset.sum_sub_distrib]
        congr 1
        · exact Finset.sum_congr rfl fun j _ => mul_comm _ _
        · exact Finset.sum_congr rfl fun j _ => mul_comm _ _
      rw [hcoe, Pi.add_apply]
      change Work.CR.Flat.dbarCoord k u z
          + (BopBar A z (fun j => Work.CR.Flat.dbarCoord j u z)) k
        = (Bop A z (fun j => Work.CR.Flat.dCoord j u z)) k
      rw [hk]
      ring
    have hfun : ContinuousLinearMap.inverse (1 + BopBar A z)
        (Bop A z (fun j => Work.CR.Flat.dCoord j u z))
        = (fun j => Work.CR.Flat.dbarCoord j u z) := by
      have h0 : ContinuousLinearMap.inverse (1 + BopBar A z)
          ((1 + BopBar A z) (fun j => Work.CR.Flat.dbarCoord j u z))
          = (fun j => Work.CR.Flat.dbarCoord j u z) :=
        ContinuousLinearMap.IsInvertible.inverse_apply_self (hInv z) _
      rwa [hsys] at h0
    have hlast : (beltramiCoeff A z (fun j => Work.CR.Flat.dCoord j u z)) k
        = ∑ j : Fin n, beltramiCoef A k j z * Work.CR.Flat.dCoord j u z := by
      have hlinμ : ∀ (c : ℂ) (v : Cn n), beltramiCoeff A z (c • v) = c • beltramiCoeff A z v :=
        fun c v => beltramiCoeff_map_smul hn A hsmall z c v
      have hw : (fun j => Work.CR.Flat.dCoord j u z)
          = ∑ j : Fin n, (Work.CR.Flat.dCoord j u z) • (Pi.single j (1 : ℂ) : Cn n) := by
        ext m
        rw [Finset.sum_apply]
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [Finset.sum_eq_single m]
        · simp
        · intro b _ hb
          simp [Pi.single_eq_of_ne (Ne.symm hb)]
        · intro h
          exact absurd (Finset.mem_univ m) h
      rw [hw, map_sum, Finset.sum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hlinμ, Pi.smul_apply, smul_eq_mul, beltramiCoef]
      ring
    calc Work.CR.Flat.dbarCoord k u z
        = (fun j => Work.CR.Flat.dbarCoord j u z) k := rfl
      _ = (beltramiCoeff A z (fun j => Work.CR.Flat.dCoord j u z)) k := by
            rw [beltramiCoeff, mul_apply_eq_comp]
            exact (congrFun hfun k).symm
      _ = ∑ j : Fin n, beltramiCoef A k j z * Work.CR.Flat.dCoord j u z := hlast

end Work.NN.Core
