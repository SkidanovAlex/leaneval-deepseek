import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.chiRowDict
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.chiRow_muEvalAux` — shared helpers for the `χ`-row `μ`-evaluation

The target `Work.BoseBoxFock.chiRow_muEval` evaluates the `μ`-line of the FS `Q₁` `χ`-sandwich on
the box: the sum of the two orientations of the first-quantised slot word at the pinned `χ`-mode
equals `muForm n ℓ (chiW ℓ N) Φ`.  Both orientations reduce to the same position-space row

    `∑ j, ∫_{abox n ℓ} (P_jΦ)·Φ·χ_w(x_j)`

and this module collects the *analytic bookkeeping* common to the two reductions:

* global bounds and measurability of the pinned modes (`chiMode`, `chiTail`, `modeVec`, `qVec`);
* measurability and boundedness of the box restriction `boxRestrictC ℓ Φ` of a continuous `Φ`;
* the reduction of the `cIPn` pairing against the box restriction to a real integral over the
  box (`cIPn_boxRestrictC_re`), which consumes the `cIPn`-integrand's integrability on `abox`;
* the integrability on `abox` of the two row integrands (one for each orientation), built from
  `aPC_aesm_aux`/`aPC_ae_bound_aux` (`uSlot_regular.lean`) and the global bound on `chiMode`.

Everything here is `sorry`-free.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

set_option autoImplicit false
set_option maxHeartbeats 800000

local notation "Sp" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. Bounds on the pinned modes -/

/-- The localisation function is bounded by `√(48/π)` (the corpus bump's sup-norm bound, uniform
in the box side `ℓ`). -/
lemma chiLam_abs_le (ℓ : ℝ) (z : Sp) :
    |Work.BoseK15.corpusBox.chiLam ℓ z| ≤ Real.sqrt (48 / Real.pi) := by
  rw [Work.BoseB4.BoxData.chiLam]
  exact abs_chiR_le _

/-- The sharp box indicator has modulus at most `1`. -/
lemma thetaFun_norm_le_one (ℓ : ℝ) (z : Sp) :
    ‖Work.BoseK15.corpusBox.thetaFun ℓ z‖ ≤ 1 := by
  rw [Work.BoseB4.BoxData.thetaFun_apply]
  split <;> simp

/-- **A global bound on the pinned `χ`-mode.**  `chiMode = χ_Λ² − θ_Λ − chiTail` with `χ_Λ`, `θ_Λ`
bounded and the truncation tail bounded uniformly by `chiTail_bound 0`. -/
theorem chiMode_norm_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ℓ : ℝ), 0 < ℓ → ∀ (N : ℕ) (z : Sp), ‖chiMode ℓ N z‖ ≤ C := by
  obtain ⟨Ct, hCt0, hCt⟩ := chiTail_bound 0
  refine ⟨Real.sqrt (48 / Real.pi) ^ 2 + 1 + Ct, by positivity, fun ℓ hℓ N z => ?_⟩
  have h1 : ‖(((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ)) : ℂ) ^ 2‖
      ≤ Real.sqrt (48 / Real.pi) ^ 2 := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (chiLam_abs_le ℓ z) 2
  have h2 : ‖Work.BoseK15.corpusBox.thetaFun ℓ z‖ ≤ 1 := thetaFun_norm_le_one ℓ z
  have h3 : ‖chiTail ℓ N z‖ ≤ Ct := by
    have h := hCt ℓ hℓ N z
    simpa using h
  have hA : ‖(((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ)) : ℂ) ^ 2
      - Work.BoseK15.corpusBox.thetaFun ℓ z‖
      ≤ Real.sqrt (48 / Real.pi) ^ 2 + 1 := by
    calc ‖(((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ)) : ℂ) ^ 2
          - Work.BoseK15.corpusBox.thetaFun ℓ z‖
        ≤ ‖(((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ)) : ℂ) ^ 2‖
            + ‖Work.BoseK15.corpusBox.thetaFun ℓ z‖ := norm_sub_le _ _
      _ ≤ Real.sqrt (48 / Real.pi) ^ 2 + 1 := add_le_add h1 h2
  calc ‖chiMode ℓ N z‖
      = ‖(((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ)) : ℂ) ^ 2
          - Work.BoseK15.corpusBox.thetaFun ℓ z - chiTail ℓ N z‖ := rfl
    _ ≤ ‖(((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ)) : ℂ) ^ 2
          - Work.BoseK15.corpusBox.thetaFun ℓ z‖ + ‖chiTail ℓ N z‖ := norm_sub_le _ _
    _ ≤ Real.sqrt (48 / Real.pi) ^ 2 + 1 + Ct := add_le_add hA h3

/-- **A global bound on the pinned `χ`-weight** `chiW = χ_Λ² − 1 − Re chiTail` (the `-1` is the
cube mean of `χ_Λ²`, so off the cube `chiW` differs from `Re chiMode` by `1`; on the cube — the
only place it is used — the two agree). -/
theorem chiW_norm_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ℓ : ℝ), 0 < ℓ → ∀ (N : ℕ) (z : Sp), |chiW ℓ N z| ≤ C := by
  obtain ⟨Ct, hCt0, hCt⟩ := chiTail_bound 0
  refine ⟨Real.sqrt (48 / Real.pi) ^ 2 + 1 + Ct, by positivity, fun ℓ hℓ N z => ?_⟩
  have h1 : |Work.BoseK15.corpusBox.chiLam ℓ z ^ 2|
      ≤ Real.sqrt (48 / Real.pi) ^ 2 := by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (chiLam_abs_le ℓ z) 2
  have h3 : |(chiTail ℓ N z).re| ≤ Ct := by
    refine (Complex.abs_re_le_norm _).trans ?_
    have h := hCt ℓ hℓ N z
    simpa using h
  have hkey : |chiW ℓ N z|
      = |(Work.BoseK15.corpusBox.chiLam ℓ z ^ 2 - 1) - (chiTail ℓ N z).re| := rfl
  rw [hkey]
  calc |(Work.BoseK15.corpusBox.chiLam ℓ z ^ 2 - 1) - (chiTail ℓ N z).re|
      ≤ |Work.BoseK15.corpusBox.chiLam ℓ z ^ 2 - 1| + |(chiTail ℓ N z).re| := abs_sub _ _
    _ ≤ (Real.sqrt (48 / Real.pi) ^ 2 + 1) + Ct := by
        refine add_le_add ?_ h3
        calc |Work.BoseK15.corpusBox.chiLam ℓ z ^ 2 - 1| ≤ |Work.BoseK15.corpusBox.chiLam ℓ z ^ 2| + |(1 : ℝ)| :=
              abs_sub _ _
          _ ≤ Real.sqrt (48 / Real.pi) ^ 2 + 1 := by
              rw [abs_one]
              exact add_le_add h1 le_rfl
    _ = Real.sqrt (48 / Real.pi) ^ 2 + 1 + Ct := rfl

/-! ## 2. Measurability of the pinned modes -/

/-- The sharp box indicator is measurable. -/
lemma thetaFun_measurable (ℓ : ℝ) : Measurable (Work.BoseK15.corpusBox.thetaFun ℓ) := by
  have h : Work.BoseK15.corpusBox.thetaFun ℓ
      = Set.indicator (Work.BoseK15.corpusBox.boxL ℓ) (fun _ : Sp => (1 : ℂ)) := by
    funext z
    rw [Work.BoseB4.BoxData.thetaFun_apply]
    by_cases hz : z ∈ Work.BoseK15.corpusBox.boxL ℓ <;> simp [hz]
  rw [h]
  exact measurable_const.indicator (Work.BoseB4.BoxData.boxL_measurableSet _ ℓ)

/-- The complexified localisation function is measurable. -/
lemma chiLamC_measurable (ℓ : ℝ) :
    Measurable (fun z : Sp => ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ)) :=
  Complex.continuous_ofReal.measurable.comp
    ((Work.BoseB4.BoxData.chiLam_cont (B := Work.BoseK15.corpusBox) ℓ).measurable)

/-- The localised plane wave `e^{ikx}χ_Λ` is measurable. -/
lemma modeVec_measurable (ℓ : ℝ) (k : Sp) :
    Measurable (Work.BoseK15.corpusBox.modeVec ℓ k) := by
  have h1 : Continuous (fun z : Sp =>
      Complex.exp (Complex.I * ((inner ℝ k z : ℝ) : ℂ))) :=
    Complex.continuous_exp.comp (continuous_const.mul
      (Complex.continuous_ofReal.comp (Continuous.inner continuous_const continuous_id)))
  rw [show Work.BoseK15.corpusBox.modeVec ℓ k
      = fun z : Sp => Complex.exp (Complex.I * ((inner ℝ k z : ℝ) : ℂ)) *
          ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ) from
    funext fun z => Work.BoseB4.BoxData.modeVec_apply _ _ _ _]
  exact h1.measurable.mul (chiLamC_measurable ℓ)

/-- The localised plane wave with the condensate component removed is measurable. -/
lemma qVec_measurable (ℓ : ℝ) (k : Sp) :
    Measurable (Work.BoseK15.corpusBox.qVec ℓ k) := by
  rw [show Work.BoseK15.corpusBox.qVec ℓ k
      = fun z : Sp => Work.BoseK15.corpusBox.modeVec ℓ k z -
          ((Work.BoseK15.corpusBox.hatChi (ℓ • k) : ℝ) : ℂ) *
            Work.BoseK15.corpusBox.thetaFun ℓ z from
    funext fun z => Work.BoseB4.BoxData.qVec_apply _ _ _ _]
  exact (modeVec_measurable ℓ k).sub (measurable_const.mul (thetaFun_measurable ℓ))

/-- The `χ`-row truncation tail is measurable. -/
lemma chiTail_measurable (ℓ : ℝ) (N : ℕ) : Measurable (chiTail ℓ N) := by
  unfold chiTail
  refine (((chiLamC_measurable ℓ).pow_const 2).sub (thetaFun_measurable ℓ)).sub ?_
  exact Finset.measurable_sum (Finset.univ : Finset (Lab N))
    (fun k _ => measurable_const.mul (qVec_measurable ℓ (kmomLab ℓ N k)))

/-- The pinned `χ`-mode is measurable. -/
lemma chiMode_measurable (ℓ : ℝ) (N : ℕ) : Measurable (chiMode ℓ N) :=
  (((chiLamC_measurable ℓ).pow_const 2).sub (thetaFun_measurable ℓ)).sub
    (chiTail_measurable ℓ N)

/-- The pinned `χ`-weight `chiW = χ_Λ² − 1 − Re chiTail` is measurable. -/
lemma chiW_measurable (ℓ : ℝ) (N : ℕ) : Measurable (chiW ℓ N) := by
  have h : chiW ℓ N = fun z : Sp =>
      (Work.BoseK15.corpusBox.chiLam ℓ z ^ 2 - 1) - (chiTail ℓ N z).re := by
    funext z
    rfl
  rw [h]
  exact ((((Work.BoseB4.BoxData.chiLam_cont (B := Work.BoseK15.corpusBox) ℓ).pow 2).sub
    continuous_const).measurable).sub (Complex.continuous_re.measurable.comp (chiTail_measurable ℓ N))

/-! ## 3. The box restriction of a continuous state -/

/-- The complex box restriction of a continuous state is measurable. -/
lemma boxRestrictC_measurable {n : ℕ} (ℓ : ℝ) {Φ : Submission.BoseGases.X n → ℝ}
    (hΦc : Continuous Φ) : Measurable (boxRestrictC ℓ Φ) := by
  have h : boxRestrictC ℓ Φ = fun x : Submission.BoseGases.X n =>
      ((Φ x : ℝ) : ℂ) *
        ((((Submission.BoseGases.abox n ℓ).indicator (fun _ => (1 : ℝ)) x : ℝ)) : ℂ) := rfl
  rw [h]
  exact (Complex.continuous_ofReal.measurable.comp hΦc.measurable).mul
    (Complex.continuous_ofReal.measurable.comp
      (measurable_const.indicator (Submission.BoseGases.abox_measurable n ℓ)))

/-- **The complex box restriction of a continuous state is globally bounded.**  Off the box it
vanishes, on the compact box it is bounded by the sup-norm of `Φ`. -/
theorem boxRestrictC_norm_bound {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Submission.BoseGases.X n, ‖boxRestrictC ℓ Φ x‖ ≤ C := by
  obtain ⟨C, hC⟩ := (Submission.BoseGases.abox_compact n hℓ).exists_bound_of_continuousOn
    hΦc.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  rw [show boxRestrictC ℓ Φ x = ((Φ x : ℝ) : ℂ) *
      ((((Submission.BoseGases.abox n ℓ).indicator (fun _ => (1 : ℝ)) x : ℝ)) : ℂ) from rfl]
  by_cases hx : x ∈ Submission.BoseGases.abox n ℓ
  · rw [Set.indicator_of_mem hx]
    simp only [Complex.ofReal_one, mul_one, Complex.norm_real]
    exact (hC x hx).trans (le_max_left _ _)
  · rw [Set.indicator_of_notMem hx]
    simp

/-- The complex box restriction of a continuous state is supported in the box. -/
lemma boxRestrictC_support_subset {n : ℕ} (ℓ : ℝ) (Φ : Submission.BoseGases.X n → ℝ) :
    Function.support (boxRestrictC ℓ Φ) ⊆ Submission.BoseGases.abox n ℓ := by
  intro x hx
  by_contra h
  exact hx (by
    rw [show boxRestrictC ℓ Φ x = ((Φ x : ℝ) : ℂ) *
      ((((Submission.BoseGases.abox n ℓ).indicator (fun _ => (1 : ℝ)) x : ℝ)) : ℂ) from rfl]
    rw [Set.indicator_of_notMem h]
    simp)

/-! ## 4. The `cIPn` reduction to the box -/

/-- **The `cIPn` pairing against the box restriction is a real integral over the box.**  For any
`G` making the product integrable, `(cIPn n (boxRestrictC ℓ Φ) G).re = ∫_{abox n ℓ} Φ·Re G`. -/
theorem cIPn_boxRestrictC_re {n : ℕ} {ℓ : ℝ} {Φ : Submission.BoseGases.X n → ℝ}
    {G : Submission.BoseGases.X n → ℂ}
    (hG : IntegrableOn (fun x => (((Φ x : ℝ)) : ℂ) * G x) (Submission.BoseGases.abox n ℓ)) :
    (Work.BoseDict.cIPn n (boxRestrictC ℓ Φ) G).re
      = ∫ x in Submission.BoseGases.abox n ℓ, Φ x * (G x).re := by
  have hpt : ∀ x : Submission.BoseGases.X n,
      (starRingEnd ℂ) (boxRestrictC ℓ Φ x) * G x
        = (Submission.BoseGases.abox n ℓ).indicator
            (fun x => (((Φ x : ℝ)) : ℂ) * G x) x := by
    intro x
    rw [show boxRestrictC ℓ Φ x = ((Φ x : ℝ) : ℂ) *
        ((((Submission.BoseGases.abox n ℓ).indicator (fun _ => (1 : ℝ)) x : ℝ)) : ℂ) from rfl]
    by_cases hx : x ∈ Submission.BoseGases.abox n ℓ
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      simp
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
      simp
  have hre : (∫ x in Submission.BoseGases.abox n ℓ, (((Φ x : ℝ)) : ℂ) * G x).re
      = ∫ x in Submission.BoseGases.abox n ℓ, ((((Φ x : ℝ)) : ℂ) * G x).re := by
    have h := integral_re (𝕜 := ℂ)
      (μ := (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
        (Submission.BoseGases.abox n ℓ))
      (f := fun x => (((Φ x : ℝ)) : ℂ) * G x) hG
    simpa using h.symm
  rw [Work.BoseDict.cIPn,
    show (∫ x, (starRingEnd ℂ) (boxRestrictC ℓ Φ x) * G x)
        = ∫ x, (Submission.BoseGases.abox n ℓ).indicator
            (fun x => (((Φ x : ℝ)) : ℂ) * G x) x from
      integral_congr_ae (Filter.Eventually.of_forall hpt),
    MeasureTheory.integral_indicator (Submission.BoseGases.abox_measurable n ℓ), hre]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  simp [Complex.mul_re]

/-! ## 5. Integrability of the two row integrands -/

/-- **The first-orientation row integrand is integrable on the box**: the product of the
continuous `Φ` with the `aPC`-presentation `∑_j chiMode(x_j)·aPC ℓ j (boxRestrictC ℓ Φ)`. -/
theorem integrableOn_rowIntegrand_first {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {N : ℕ}
    {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ) :
    IntegrableOn (fun x : Submission.BoseGases.X n => (((Φ x : ℝ)) : ℂ) *
      (∑ j : Fin n, chiMode ℓ N (x j) * aPC ℓ j (boxRestrictC ℓ Φ) x))
      (Submission.BoseGases.abox n ℓ) := by
  obtain ⟨Cm, hCm0, hCm⟩ := chiMode_norm_bound
  obtain ⟨CΨ, hCΨ0, hCΨ⟩ := boxRestrictC_norm_bound hℓ hΦc
  obtain ⟨CΦ, hCΦ⟩ := (Submission.BoseGases.abox_compact n hℓ).exists_bound_of_continuousOn
    hΦc.continuousOn
  have hfin : (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n))
      (Submission.BoseGases.abox n ℓ) < ⊤ := Submission.BoseGases.abox_lt_top n ℓ hℓ.le
  have hΨm : AEStronglyMeasurable (boxRestrictC ℓ Φ) MeasureTheory.volume :=
    (boxRestrictC_measurable ℓ hΦc).aestronglyMeasurable
  have hsumm : AEStronglyMeasurable (fun x : Submission.BoseGases.X n =>
      ∑ j : Fin n, chiMode ℓ N (x j) * aPC ℓ j (boxRestrictC ℓ Φ) x)
      ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
        (Submission.BoseGases.abox n ℓ)) := by
    have heq : (fun x : Submission.BoseGases.X n =>
        ∑ j : Fin n, chiMode ℓ N (x j) * aPC ℓ j (boxRestrictC ℓ Φ) x)
        = ∑ j : Fin n, (fun x : Submission.BoseGases.X n =>
            chiMode ℓ N (x j) * aPC ℓ j (boxRestrictC ℓ Φ) x) := by
      funext x
      rw [Finset.sum_apply]
    rw [heq]
    exact Finset.aestronglyMeasurable_sum (Finset.univ : Finset (Fin n)) (fun j _ =>
      ((chiMode_measurable ℓ N).comp (measurable_pi_apply j)).aestronglyMeasurable.mul
        (aPC_aesm_aux (ℓ := ℓ) j hΨm))
  have hsm : AEStronglyMeasurable (fun x : Submission.BoseGases.X n => (((Φ x : ℝ)) : ℂ) *
      (∑ j : Fin n, chiMode ℓ N (x j) * aPC ℓ j (boxRestrictC ℓ Φ) x))
      ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
        (Submission.BoseGases.abox n ℓ)) :=
    (Complex.continuous_ofReal.measurable.comp hΦc.measurable).aestronglyMeasurable.mul hsumm
  refine MeasureTheory.IntegrableOn.of_bound hfin hsm (max CΦ 0 * ((n : ℝ) * (Cm * CΨ))) ?_
  have haPC : ∀ᵐ x ∂((MeasureTheory.volume :
      MeasureTheory.Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ)),
      ∀ j : Fin n, ‖aPC ℓ j (boxRestrictC ℓ Φ) x‖ ≤ CΨ :=
    Filter.eventually_all.mpr
      (fun j => aPC_ae_bound_aux hℓ j (Filter.Eventually.of_forall hCΨ))
  filter_upwards [haPC, self_mem_ae_restrict (Submission.BoseGases.abox_measurable n ℓ)]
    with x hbound hxmem
  have hΦx : ‖Φ x‖ ≤ max CΦ 0 := (hCΦ x hxmem).trans (le_max_left _ _)
  have hsum : ‖∑ j : Fin n, chiMode ℓ N (x j) * aPC ℓ j (boxRestrictC ℓ Φ) x‖
      ≤ (n : ℝ) * (Cm * CΨ) := by
    have h1 : ‖∑ j : Fin n, chiMode ℓ N (x j) * aPC ℓ j (boxRestrictC ℓ Φ) x‖
        ≤ ∑ j : Fin n, ‖chiMode ℓ N (x j) * aPC ℓ j (boxRestrictC ℓ Φ) x‖ :=
      norm_sum_le _ _
    have h2 : ∀ j ∈ (Finset.univ : Finset (Fin n)),
        ‖chiMode ℓ N (x j) * aPC ℓ j (boxRestrictC ℓ Φ) x‖ ≤ Cm * CΨ := by
      intro j _
      rw [norm_mul]
      exact mul_le_mul (hCm ℓ hℓ N (x j)) (hbound j) (norm_nonneg _) hCm0
    have h3 : (∑ j : Fin n, ‖chiMode ℓ N (x j) * aPC ℓ j (boxRestrictC ℓ Φ) x‖)
        ≤ (n : ℝ) * (Cm * CΨ) := by
      calc (∑ j : Fin n, ‖chiMode ℓ N (x j) * aPC ℓ j (boxRestrictC ℓ Φ) x‖)
          ≤ ∑ _j : Fin n, Cm * CΨ := Finset.sum_le_sum h2
        _ = (n : ℝ) * (Cm * CΨ) := by
            rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    exact h1.trans h3
  rw [norm_mul, Complex.norm_real]
  exact mul_le_mul hΦx hsum (norm_nonneg _) (le_trans (norm_nonneg _) hΦx)

/-- **The second-orientation row integrand is integrable on the box**: the product of the
continuous `Φ` with the `aPC`-presentation
`∑_j aPC ℓ j (conj(chiMode(·_j))·boxRestrictC ℓ Φ)`. -/
theorem integrableOn_rowIntegrand_second {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {N : ℕ}
    {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ) :
    IntegrableOn (fun x : Submission.BoseGases.X n => (((Φ x : ℝ)) : ℂ) *
      (∑ j : Fin n, aPC ℓ j
        (fun y : Submission.BoseGases.X n =>
          (starRingEnd ℂ) (chiMode ℓ N (y j)) * boxRestrictC ℓ Φ y) x))
      (Submission.BoseGases.abox n ℓ) := by
  obtain ⟨Cm, hCm0, hCm⟩ := chiMode_norm_bound
  obtain ⟨CΨ, hCΨ0, hCΨ⟩ := boxRestrictC_norm_bound hℓ hΦc
  obtain ⟨CΦ, hCΦ⟩ := (Submission.BoseGases.abox_compact n hℓ).exists_bound_of_continuousOn
    hΦc.continuousOn
  have hfin : (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n))
      (Submission.BoseGases.abox n ℓ) < ⊤ := Submission.BoseGases.abox_lt_top n ℓ hℓ.le
  -- the twisted states `F j = conj(chiMode(·_j))·(boxRestrictC ℓ Φ)`
  have hFm : ∀ j : Fin n, AEStronglyMeasurable (fun y : Submission.BoseGases.X n =>
      (starRingEnd ℂ) (chiMode ℓ N (y j)) * boxRestrictC ℓ Φ y) MeasureTheory.volume := by
    intro j
    exact ((Complex.continuous_conj.measurable.comp
        ((chiMode_measurable ℓ N).comp (measurable_pi_apply j))).aestronglyMeasurable.mul
      (boxRestrictC_measurable ℓ hΦc).aestronglyMeasurable)
  have hFb : ∀ j : Fin n, ∀ᵐ y ∂(MeasureTheory.volume :
      MeasureTheory.Measure (Submission.BoseGases.X n)),
      ‖(starRingEnd ℂ) (chiMode ℓ N (y j)) * boxRestrictC ℓ Φ y‖ ≤ Cm * CΨ :=
    fun j => Filter.Eventually.of_forall (fun y => by
      rw [norm_mul, Complex.norm_conj]
      exact mul_le_mul (hCm ℓ hℓ N (y j)) (hCΨ y) (norm_nonneg _) hCm0)
  have hsumm : AEStronglyMeasurable (fun x : Submission.BoseGases.X n =>
      ∑ j : Fin n, aPC ℓ j
        (fun y : Submission.BoseGases.X n =>
          (starRingEnd ℂ) (chiMode ℓ N (y j)) * boxRestrictC ℓ Φ y) x)
      ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
        (Submission.BoseGases.abox n ℓ)) := by
    have heq : (fun x : Submission.BoseGases.X n =>
        ∑ j : Fin n, aPC ℓ j
          (fun y : Submission.BoseGases.X n =>
            (starRingEnd ℂ) (chiMode ℓ N (y j)) * boxRestrictC ℓ Φ y) x)
        = ∑ j : Fin n, (fun x : Submission.BoseGases.X n => aPC ℓ j
            (fun y : Submission.BoseGases.X n =>
              (starRingEnd ℂ) (chiMode ℓ N (y j)) * boxRestrictC ℓ Φ y) x) := by
      funext x
      rw [Finset.sum_apply]
    rw [heq]
    exact Finset.aestronglyMeasurable_sum (Finset.univ : Finset (Fin n))
      (fun j _ => aPC_aesm_aux (ℓ := ℓ) j (hFm j))
  have hsm : AEStronglyMeasurable (fun x : Submission.BoseGases.X n => (((Φ x : ℝ)) : ℂ) *
      (∑ j : Fin n, aPC ℓ j
        (fun y : Submission.BoseGases.X n =>
          (starRingEnd ℂ) (chiMode ℓ N (y j)) * boxRestrictC ℓ Φ y) x))
      ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
        (Submission.BoseGases.abox n ℓ)) :=
    (Complex.continuous_ofReal.measurable.comp hΦc.measurable).aestronglyMeasurable.mul hsumm
  refine MeasureTheory.IntegrableOn.of_bound hfin hsm (max CΦ 0 * ((n : ℝ) * (Cm * CΨ))) ?_
  have haPC : ∀ᵐ x ∂((MeasureTheory.volume :
      MeasureTheory.Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ)),
      ∀ j : Fin n, ‖aPC ℓ j (fun y : Submission.BoseGases.X n =>
        (starRingEnd ℂ) (chiMode ℓ N (y j)) * boxRestrictC ℓ Φ y) x‖ ≤ Cm * CΨ :=
    Filter.eventually_all.mpr (fun j => aPC_ae_bound_aux hℓ j (hFb j))
  filter_upwards [haPC, self_mem_ae_restrict (Submission.BoseGases.abox_measurable n ℓ)]
    with x hbound hxmem
  have hΦx : ‖Φ x‖ ≤ max CΦ 0 := (hCΦ x hxmem).trans (le_max_left _ _)
  have hsum : ‖∑ j : Fin n, aPC ℓ j (fun y : Submission.BoseGases.X n =>
      (starRingEnd ℂ) (chiMode ℓ N (y j)) * boxRestrictC ℓ Φ y) x‖
      ≤ (n : ℝ) * (Cm * CΨ) := by
    have h1 : ‖∑ j : Fin n, aPC ℓ j (fun y : Submission.BoseGases.X n =>
        (starRingEnd ℂ) (chiMode ℓ N (y j)) * boxRestrictC ℓ Φ y) x‖
        ≤ ∑ j : Fin n, ‖aPC ℓ j (fun y : Submission.BoseGases.X n =>
            (starRingEnd ℂ) (chiMode ℓ N (y j)) * boxRestrictC ℓ Φ y) x‖ :=
      norm_sum_le _ _
    have h3 : (∑ j : Fin n, ‖aPC ℓ j (fun y : Submission.BoseGases.X n =>
            (starRingEnd ℂ) (chiMode ℓ N (y j)) * boxRestrictC ℓ Φ y) x‖)
        ≤ (n : ℝ) * (Cm * CΨ) := by
      calc (∑ j : Fin n, ‖aPC ℓ j (fun y : Submission.BoseGases.X n =>
              (starRingEnd ℂ) (chiMode ℓ N (y j)) * boxRestrictC ℓ Φ y) x‖)
          ≤ ∑ _j : Fin n, Cm * CΨ := Finset.sum_le_sum (fun j _ => hbound j)
        _ = (n : ℝ) * (Cm * CΨ) := by
            rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    exact h1.trans h3
  rw [norm_mul, Complex.norm_real]
  exact mul_le_mul hΦx hsum (norm_nonneg _) (le_trans (norm_nonneg _) hΦx)

end Work.BoseBoxFock
