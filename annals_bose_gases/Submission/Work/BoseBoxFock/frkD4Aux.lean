import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Submission.Work.BoseBoxFock.adm_regime_gate
import Submission.Work.BoseBoxFock.boxSlotSum_rankOne_re_le_fibre
import Submission.Work.BoseBoxFock.frkD4Defs
import Submission.Work.BoseBoxFock.indU_kinFT_winState_fibre_sum_swap
import Submission.Work.BoseBoxFock.kinGroup_slotSum_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.frkD4Aux` — the auxiliary layer of the dictionary `D4`

The dictionary `Work.BoseBoxFock.FRK.FormRowKin4_of_oneBody4` consumes

* the parameter facts of `Adm` (`adm_param_facts`: `0 < ℓ`, `0 < s`, `0 < d ≤ 1`,
  `0 ≤ ε_T ≤ 1`, `0 < b`), whose only non-elementary input is
  `paramsOK_fsParams_le_one` — FS's condition `ε_T ≪ s d K_ℓ` of `sec:params`
  forces the diluteness `μa³ ≤ 1`;
* the identification of the honest environment's fields (`honest_E_tau` etc.);
* the weak `SlotGood` of `boxSlotSum e T` (the *operator*-level analogue of the state-level
  regularity of the slot calculus), which turns the rows of `AVgen` into `IntegrableOn` data on
  the compact box.

Everything here is independent of the row inequalities themselves.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! ## 1. FS's condition `ε_T ≪ s d K_ℓ` forces the diluteness `μa³ ≤ 1` -/

/-- **`ParamsOK (fsParams t) t` forces `t ≤ 1`.**  The conjunct `Con_eTdK` reads
`ε_T ≤ s·d·K_ℓ`, i.e. `t^{23/1292} ≤ t^{22/1292}`; for `t > 1` the map
`c ↦ t^c` is increasing and `22/1292 < 23/1292`, a contradiction. -/
theorem paramsOK_fsParams_le_one {t : ℝ}
    (h : Work.BoseBox.ParamsOK (Work.BoseBox.fsParams t) t) : t ≤ 1 := by
  by_contra hc
  rw [not_le] at hc
  have ht : 0 < t := lt_trans zero_lt_one hc
  have hle : (Work.BoseBox.fsParams t).eT
      ≤ (Work.BoseBox.fsParams t).s * (Work.BoseBox.fsParams t).d
        * (Work.BoseBox.fsParams t).Kl := h.eTdK.2.2
  simp only [Work.BoseBox.fsParams] at hle
  rw [Work.BoseBox.fsXp_mul ht, Work.BoseBox.fsXp_mul ht] at hle
  have hle' : t ^ ((23 : ℝ) / 1292) ≤ t ^ ((11 : ℝ) / 646) := by
    simpa only [Work.BoseBox.fsXp, show ((23 : ℝ) / 4) / 323 = 23 / 1292 by norm_num,
      show ((1 : ℝ) + 6 + -(3 / 2)) / 323 = 11 / 646 by norm_num] using hle
  have hlt : t ^ ((11 : ℝ) / 646) < t ^ ((23 : ℝ) / 1292) :=
    Real.rpow_lt_rpow_of_exponent_lt hc (by norm_num)
  linarith

/-- **The parameter facts of `Adm`**: the box side is positive and FS's parameters satisfy
`s > 0`, `0 < d ≤ 1`, `0 ≤ ε_T ≤ 1`, `b > 0`. -/
theorem adm_param_facts (v : ℝ³ → ℝ) (hav : 0 < BoseGases.a v) {ε₀ μ : ℝ}
    (hAdm : Work.BoseBoxFix.Adm v ε₀ μ) :
    0 < Work.BoseBox.sideAt μ (BoseGases.a v) ∧
      0 < (Work.BoseBox.paramsAt μ (BoseGases.a v)).s ∧
      0 < (Work.BoseBox.paramsAt μ (BoseGases.a v)).d ∧
      (Work.BoseBox.paramsAt μ (BoseGases.a v)).d ≤ 1 ∧
      0 ≤ (Work.BoseBox.paramsAt μ (BoseGases.a v)).eT ∧
      (Work.BoseBox.paramsAt μ (BoseGases.a v)).eT ≤ 1 ∧
      0 < (Work.BoseBox.paramsAt μ (BoseGases.a v)).b := by
  obtain ⟨hμpos, -, hOK⟩ := hAdm
  have ht : 0 < μ * (BoseGases.a v) ^ 3 := by positivity
  have ht1 : μ * (BoseGases.a v) ^ 3 ≤ 1 := paramsOK_fsParams_le_one hOK
  have hP : Work.BoseBox.paramsAt μ (BoseGases.a v)
      = Work.BoseBox.fsParams (μ * (BoseGases.a v) ^ 3) := rfl
  refine ⟨Work.BoseBox.sideAt_pos hμpos hav, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hP]; exact Work.BoseBox.fsXp_pos ht
  · rw [hP]; exact Work.BoseBox.fsXp_pos ht
  · rw [hP]; exact Work.BoseBox.fsXp_le_one ht ht1 (by norm_num)
  · rw [hP]; exact (Work.BoseBox.fsXp_pos ht).le
  · rw [hP]; exact Work.BoseBox.fsXp_le_one ht ht1 (by norm_num)
  · rw [hP]; show (0 : ℝ) < Work.BoseBox.bValue
    norm_num [Work.BoseBox.bValue]

/-! ## 2. The honest environment's fields -/

/-- `E.tau` of the honest family, in the parameters of the box. -/
theorem honest_E_tau (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut)
    (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) (hμ : 0 < Work.BoseBox.sideAt μ (BoseGases.a v))
    (k : Lab (HM μ).N) :
    (HonestBoxFam v h fc fu HM μ).E.tau k
      = tauSm (Work.BoseBox.paramsAt μ (BoseGases.a v)).eT
          (Work.BoseBox.paramsAt μ (BoseGases.a v)).s
          (Work.BoseBox.paramsAt μ (BoseGases.a v)).d
          (Work.BoseBox.sideAt μ (BoseGases.a v))
          (kmomLab (Work.BoseBox.sideAt μ (BoseGases.a v)) (HM μ).N k) := by
  rw [show (HonestBoxFam v h fc fu HM μ).E.tau k
      = tauSm (Work.BoseBox.paramsAt μ (BoseGases.a v)).eT
          (Work.BoseBox.paramsAt μ (BoseGases.a v)).s
          (Work.BoseBox.paramsAt μ (BoseGases.a v)).d
          (Work.BoseBox.sideAt μ (BoseGases.a v))
          (kmomLab (ellH v μ) (HM μ).N k) from rfl]
  rw [ellH_eq_sideAt_asm hμ]

/-- `E.ell` of the honest family. -/
theorem honest_E_ell (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut)
    (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) :
    (HonestBoxFam v h fc fu HM μ).E.ell = Work.BoseBox.sideAt μ (BoseGases.a v) := by
  dsimp only [HonestBoxFam, KzEnvHon, Work.BoseFixR.KzEnvFs]

/-- `E.b` of the honest family. -/
theorem honest_E_b (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut)
    (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) :
    (HonestBoxFam v h fc fu HM μ).E.b = (Work.BoseBox.paramsAt μ (BoseGases.a v)).b := by
  dsimp only [HonestBoxFam, KzEnvHon, Work.BoseFixR.KzEnvFs]

/-- `E.eT` of the honest family. -/
theorem honest_E_eT (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut)
    (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) :
    (HonestBoxFam v h fc fu HM μ).E.eT = (Work.BoseBox.paramsAt μ (BoseGases.a v)).eT := by
  dsimp only [HonestBoxFam, KzEnvHon, Work.BoseFixR.KzEnvFs]

/-- `E.d` of the honest family. -/
theorem honest_E_d (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut)
    (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) :
    (HonestBoxFam v h fc fu HM μ).E.d = (Work.BoseBox.paramsAt μ (BoseGases.a v)).d := by
  dsimp only [HonestBoxFam, KzEnvHon, Work.BoseFixR.KzEnvFs]

/-! ## 3. `SlotGood` of the operator rows -/

/-- The coordinate expansion of `boxSlotSum`, with the operator's matrix elements as the
coefficients. -/
theorem boxSlotSum_eq_expand {m d : ℕ} (e : Fin m → Ω → ℂ)
    (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (Θ : Work.BoseDict.Xn d → ℂ) :
    Work.BoseDict.boxSlotSum e T Θ
      = fun x => ∑ j : Fin d, ∑ l : Fin m, ∑ l' : Fin m,
          ((T (Work.BoseB4.evec m l') l : ℝ) : ℂ)
            * Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ x := by
  funext x
  simp only [Work.BoseDict.boxSlotSum, Finset.sum_apply, Pi.smul_apply, Complex.real_smul]

/-- `boxSlotSum e T` maps good states to good states, as a `RowGood` operator. -/
theorem rowGood_boxSlotSum {m d : ℕ} {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) :
    RowGood (ι := Fin d) (fun Θ : Work.BoseDict.Xn d → ℂ => Work.BoseDict.boxSlotSum e T Θ) := by
  intro Θ hΘ
  change SlotGood (Work.BoseDict.boxSlotSum e T Θ)
  rw [boxSlotSum_eq_expand]
  have hsum : (fun x => ∑ j : Fin d, ∑ l : Fin m, ∑ l' : Fin m,
      ((T (Work.BoseB4.evec m l') l : ℝ) : ℂ)
        * Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ x)
      = ∑ j : Fin d, ∑ l : Fin m, ∑ l' : Fin m, fun x =>
      ((T (Work.BoseB4.evec m l') l : ℝ) : ℂ)
        * Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ x := by
    funext x
    simp only [Finset.sum_apply]
  rw [hsum]
  refine SlotGood.finset_sum Finset.univ (fun j => ?_)
  refine SlotGood.finset_sum Finset.univ (fun l => ?_)
  refine SlotGood.finset_sum Finset.univ (fun l' => ?_)
  obtain ⟨hm, hb⟩ := Work.MB.boxSlotOf_measurable_bounded_weak (d := d) hmeas hbdd hsupp
    (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ hΘ.1 hΘ.2
  exact SlotGood.smul _ ⟨hm, hb⟩

/-- The slot sum of a good state is good. -/
theorem slotGood_boxSlotSum {m d : ℕ} {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) {Θ : Work.BoseDict.Xn d → ℂ} (hΘ : SlotGood Θ) :
    SlotGood (Work.BoseDict.boxSlotSum e T Θ) :=
  rowGood_boxSlotSum hmeas hbdd hsupp T Θ hΘ

/-- `star Θ · F` is integrable on the configuration box as soon as both factors are good: the
box has finite measure and both factors are everywhere bounded. -/
theorem star_mul_integrableOn_abox {n : ℕ} {ℓ : ℝ} (hℓ : 0 ≤ ℓ)
    {Θ F : Work.BoseDict.Xn n → ℂ} (hΘ : SlotGood Θ) (hF : SlotGood F) :
    MeasureTheory.IntegrableOn (fun x => star (Θ x) * F x) (Submission.BoseGases.abox n ℓ) := by
  obtain ⟨hΘm, ⟨CΘ, hCΘ⟩⟩ := hΘ
  obtain ⟨hFm, ⟨CF, hCF⟩⟩ := hF
  refine MeasureTheory.IntegrableOn.of_bound (Submission.BoseGases.abox_lt_top n ℓ hℓ)
    (((continuous_star.measurable.comp hΘm).mul hFm).aestronglyMeasurable.restrict)
    (max CΘ 0 * max CF 0) ?_
  filter_upwards with x
  rw [norm_mul, norm_star]
  exact mul_le_mul (le_trans (hCΘ x) (le_max_left _ _)) (le_trans (hCF x) (le_max_left _ _))
    (norm_nonneg _) (le_max_right _ _)

/-- Two operators with the same matrix elements give the same slot sum. -/
theorem boxSlotSum_eq_of_coeff {m d : ℕ} {e : Fin m → Ω → ℂ}
    {T₁ T₂ : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)} (Θ : Work.BoseDict.Xn d → ℂ)
    (h : ∀ l l' : Fin m, T₁ (Work.BoseB4.evec m l') l = T₂ (Work.BoseB4.evec m l') l) :
    Work.BoseDict.boxSlotSum e T₁ Θ = Work.BoseDict.boxSlotSum e T₂ Θ := by
  rw [boxSlotSum_eq_expand, boxSlotSum_eq_expand]
  funext x
  refine Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => ?_
  rw [h l l']

end Work.BoseBoxFock
