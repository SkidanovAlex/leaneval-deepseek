import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_major_defs
import Submission.Work.BourgainPlan.Maximal.mst_minor_lp_per_n
import Submission.Work.BourgainPlan.Maximal.sigmaN_card_le
import Submission.Work.BourgainPlan.Maximal.iw_superset_bound
import Submission.Work.BourgainPlan.Maximal.mst_iw_lift
import Submission.Work.BourgainPlan.Maximal.mikhlin_conditions_scaled_bump
import Submission.Work.BourgainPlan.Maximal.poly_dilation_lp_shift_const
import Submission.Work.BourgainPlan.Maximal.memLp_mst_symbols
import Submission.Work.BourgainPlan.IonescuWainger.fourierCoeff_arcTranslate
import Submission.Work.BourgainPlan.Maximal.discAvgZC_multiplier_z
import Submission.Work.BourgainPlan.Maximal.minor_arc_lp
import Submission.Work.BourgainPlan.KPWW.opArc_lp_bound_of_coeff
import Submission.Work.BourgainPlan.Maximal.mst_err1_opmul_coeff
import Submission.Work.BourgainPlan.Maximal.mstU_card_le_exp
import Submission.Work.BourgainPlan.Maximal.mst_err1_bump_coeff
import Submission.Work.BourgainPlan.Maximal.mst_err1_prof_coeff

namespace Work.BourgainPlan.Maximal

open MeasureTheory Finset
open scoped BigOperators ENNReal

local notation "haarT" => (AddCircle.haarAddCircle (T := 1))

open Work.BourgainPlan.IonescuWainger

noncomputable section

/-- `fourierCoeff` is the integral of the symbol against `star (fourier m ·)`. -/
lemma fourierCoeff_eq_integral_mul_star (f : Work.BourgainPlan.IonescuWainger.Circle → ℂ)
    (m : ℤ) :
    fourierCoeff f m = ∫ ξ, f ξ * star (fourier m ξ) ∂haarT := by
  unfold fourierCoeff
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  show fourier (-m) ξ • f ξ = f ξ * star (fourier m ξ)
  rw [fourier_neg, starRingEnd_apply, smul_eq_mul, mul_comm]

/-- **The profile-times-bump** `h_n = star (mstProf P (2^n) ·) · mstEta d χ η n`: the (untranslated)
model bump of level `n`, whose translates by the arcs of `𝒰(n)` build up `mstNu`. -/
def mstProfBump (P : Polynomial ℤ) (d : ℕ) (χ : ℝ) (η : ℝ → ℂ) (n : ℕ) :
    Work.BourgainPlan.IonescuWainger.Circle → ℂ :=
  (fun ξ => star (mstProf P (2 ^ n) ξ)) * mstEta d χ η n

lemma memLp_mstProfBumpTriv (P : Polynomial ℤ) (d : ℕ) (χ : ℝ) (η : ℝ → ℂ) (n : ℕ)
    (hηml : MemLp (mstEta d χ η n) ⊤ haarT) : MemLp (mstProfBump P d χ η n) ⊤ haarT := by
  have h1 : MemLp (fun ξ : Work.BourgainPlan.IonescuWainger.Circle =>
      star (mstProf P (2 ^ n) ξ)) ⊤ haarT :=
    (memLp_mst_symbols P (2 ^ n) 1 (fun _ : ℝ => 0) continuous_const).2.1.star
  exact h1.mul hηml

/-- **The Fourier coefficients of the model symbol `ν_{2^n}`**: translating the profile-times-bump
`h_n` by the arc `β` multiplies its `m`-th coefficient by the unimodular factor
`star (fourier m β)`, so

`fourierCoeff (mstNu P l d χ η n) m
   = (Σ_{β ∈ 𝒰(n)} star (G β) · star (fourier m β)) · fourierCoeff (mstProfBump P d χ η n) m`. -/
theorem fourierCoeff_mstNu_eq (P : Polynomial ℤ) (l d : ℕ) (χ : ℝ) (η : ℝ → ℂ) (n : ℕ)
    (hηml : MemLp (mstEta d χ η n) ⊤ haarT) (m : ℤ) :
    fourierCoeff (mstNu P l d χ η n) m
      = (∑ β ∈ mstU l n, star (mstG P β) * star (fourier m β))
          * fourierCoeff (mstProfBump P d χ η n) m := by
  classical
  have hmem : MemLp (mstProfBump P d χ η n) ⊤ haarT := memLp_mstProfBumpTriv P d χ η n hηml
  have hpt : mstNu P l d χ η n =ᵐ[haarT]
      fun ξ => ∑ β ∈ mstU l n, star (mstG P β) * arcTranslate β (mstProfBump P d χ η n) ξ := by
    filter_upwards with ξ
    rw [mstNu_apply]
    refine Finset.sum_congr rfl fun β _ => ?_
    simp only [mstProfBump, arcTranslate, Pi.mul_apply]
  have hint : ∀ β ∈ mstU l n, Integrable (fun ξ : Work.BourgainPlan.IonescuWainger.Circle =>
      star (mstG P β) * arcTranslate β (mstProfBump P d χ η n) ξ) haarT := by
    intro β _
    have h2 : Integrable (mstProfBump P d χ η n) haarT := hmem.integrable le_top
    exact ((memLp_arcTranslate hmem β).integrable le_top).const_mul _
  have hfun : (fun ξ => ∑ β ∈ mstU l n,
        star (mstG P β) * arcTranslate β (mstProfBump P d χ η n) ξ)
      = ∑ β ∈ mstU l n,
        (fun ξ => star (mstG P β) * arcTranslate β (mstProfBump P d χ η n) ξ) := by
    funext ξ; simp
  rw [fourierCoeff_congr_ae hpt, hfun, fourierCoeff.sum _ _ hint]
  simp only [Finset.sum_apply]
  have hterm : ∀ β : Work.BourgainPlan.IonescuWainger.Circle,
      fourierCoeff (fun ξ => star (mstG P β) * arcTranslate β (mstProfBump P d χ η n) ξ) m
        = star (mstG P β) * (star (fourier m β) * fourierCoeff (mstProfBump P d χ η n) m) := by
    intro β
    rw [fourierCoeff.const_mul,
      fourierCoeff_eq_integral_mul_star (arcTranslate β (mstProfBump P d χ η n)) m,
      fourierCoeff_arcTranslate (mstProfBump P d χ η n) hmem β m,
      fourierCoeff_eq_integral_mul_star (mstProfBump P d χ η n) m]
  rw [Finset.sum_congr rfl (fun β _ => hterm β)]
  rw [Finset.sum_congr rfl (fun β _ => (mul_assoc _ _ _).symm), Finset.sum_mul]

/-- **The `ℓ¹` norm of the coefficient kernel of the model symbol `ν_{2^n}`** is at most
`#𝒰(n)` times that of the profile-times-bump `h_n`: by `fourierCoeff_mstNu_eq` each coefficient is
the product of the unimodular weight `Σ_{β} star (G β) star (fourier m β)` (of modulus `≤ #𝒰(n)`)
with `fourierCoeff (mstProfBump …) m`. -/
theorem tsum_fourierCoeff_mstNu_le (P : Polynomial ℤ) (l d : ℕ) (χ : ℝ) (η : ℝ → ℂ) (n : ℕ)
    (hηml : MemLp (mstEta d χ η n) ⊤ haarT) {K : ℝ}
    (hK : Summable (fun m : ℤ => ‖fourierCoeff (mstProfBump P d χ η n) m‖))
    (hKb : (∑' m : ℤ, ‖fourierCoeff (mstProfBump P d χ η n) m‖) ≤ K) :
    Summable (fun m : ℤ => ‖fourierCoeff (mstNu P l d χ η n) m‖) ∧
      (∑' m : ℤ, ‖fourierCoeff (mstNu P l d χ η n) m‖) ≤ ((mstU l n).card : ℝ) * K := by
  have hpt : ∀ m : ℤ, ‖fourierCoeff (mstNu P l d χ η n) m‖
      ≤ ((mstU l n).card : ℝ) * ‖fourierCoeff (mstProfBump P d χ η n) m‖ := by
    intro m
    rw [fourierCoeff_mstNu_eq P l d χ η n hηml m, norm_mul]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    calc ‖∑ β ∈ mstU l n, star (mstG P β) * star (fourier m β)‖
        ≤ ∑ β ∈ mstU l n, ‖star (mstG P β) * star (fourier m β)‖ := norm_sum_le _ _
      _ ≤ ∑ _β ∈ mstU l n, (1 : ℝ) := by
          refine Finset.sum_le_sum fun β _ => ?_
          rw [norm_mul]
          have h2 : ‖star ((fourier m) β)‖ = (1 : ℝ) := by
            simpa using norm_fourier_apply' m β
          rw [h2, mul_one]
          simpa using mstG_norm_le_one P β
      _ = ((mstU l n).card : ℝ) := by simp
  have hsum : Summable (fun m : ℤ => ‖fourierCoeff (mstNu P l d χ η n) m‖) :=
    Summable.of_nonneg_of_le (f := fun m : ℤ =>
        ((mstU l n).card : ℝ) * ‖fourierCoeff (mstProfBump P d χ η n) m‖)
      (g := fun m : ℤ => ‖fourierCoeff (mstNu P l d χ η n) m‖)
      (fun m => norm_nonneg _) (fun m => hpt m) (hK.mul_left _)
  refine ⟨hsum, ?_⟩
  calc (∑' m : ℤ, ‖fourierCoeff (mstNu P l d χ η n) m‖)
      ≤ ∑' m : ℤ, ((mstU l n).card : ℝ) * ‖fourierCoeff (mstProfBump P d χ η n) m‖ :=
        Summable.tsum_le_tsum (fun m => hpt m) hsum (hK.mul_left _)
    _ = ((mstU l n).card : ℝ) * ∑' m : ℤ, ‖fourierCoeff (mstProfBump P d χ η n) m‖ :=
        tsum_mul_left
    _ ≤ ((mstU l n).card : ℝ) * K := mul_le_mul_of_nonneg_left hKb (Nat.cast_nonneg _)

/-- **The `ℓ^q` contraction of the density average in `eLpNorm` form** (`q ≥ 1`), from
`discAvgZC_contraction`. -/
lemma eLpNorm_discAvgZC_le (P : Polynomial ℤ) (N : ℕ) {q : ℝ} (hq : 1 ≤ q) (g : ℤ → ℂ) :
    eLpNorm (discAvgZC P N g) (ENNReal.ofReal q) Measure.count
      ≤ eLpNorm g (ENNReal.ofReal q) Measure.count := by
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le zero_lt_one hq
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_ne_zero_iff.mpr hq0)
        ENNReal.ofReal_ne_top (measurable_of_countable _).aestronglyMeasurable,
      eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_ne_zero_iff.mpr hq0)
        ENNReal.ofReal_ne_top (measurable_of_countable _).aestronglyMeasurable]
  simp only [ENNReal.toReal_ofReal hq0.le]
  exact ENNReal.rpow_le_rpow (discAvgZC_contraction P N hq g) (by positivity)

/-- **The `ℓʳ` bound for the projection symbol `m_{2^n} Ξ_n`**: `opMul (mstProjCls …)` is the
composition of the density average `A_{2^n}` (an `ℓʳ`-contraction, `discAvgZC_contraction`) with the
arc projection `opArc η_n 𝒰(n)` (an `ℓʳ`-multiplier of norm `≤ #𝒰(n) · K`, the landed
`KPWW.opArc_lp_bound_of_coeff` applied to the summable coefficient kernel of the level bump). -/
theorem eLpNorm_opMul_mstProjCls_le (P : Polynomial ℤ) (l d : ℕ) (χ : ℝ) (η : ℝ → ℂ) (n : ℕ)
    (hηml : MemLp (mstEta d χ η n) ⊤ haarT) {r : ℝ} (hr : 1 < r) {K : ℝ}
    (hK : Summable (fun m : ℤ => ‖fourierCoeff (mstEta d χ η n) m‖))
    (hKb : (∑' m : ℤ, ‖fourierCoeff (mstEta d χ η n) m‖) ≤ K)
    (f : ℤ → ℂ) (hf : Memℓp f 2) :
    eLpNorm (opMul (mstProjCls P l d χ η n hηml) f hf) (ENNReal.ofReal r) Measure.count
      ≤ ENNReal.ofReal (((mstU l n).card : ℝ) * K) * eLpNorm f (ENNReal.ofReal r)
          Measure.count := by
  have h1 : opMul (mstProjCls P l d χ η n hηml) f hf
      = discAvgZC P (2 ^ n) (opArc (mstEta d χ η n) hηml (mstU l n) f hf) := by
    rw [mstProjCls]
    exact (discAvgZC_opArc_eq_opMul_smul P (2 ^ n) (mstEta d χ η n) hηml (mstU l n) f hf).symm
  rw [h1]
  calc eLpNorm (discAvgZC P (2 ^ n) (opArc (mstEta d χ η n) hηml (mstU l n) f hf))
        (ENNReal.ofReal r) Measure.count
      ≤ eLpNorm (opArc (mstEta d χ η n) hηml (mstU l n) f hf) (ENNReal.ofReal r)
          Measure.count := eLpNorm_discAvgZC_le P (2 ^ n) hr.le _
    _ ≤ ENNReal.ofReal (((mstU l n).card : ℝ) * K) * eLpNorm f (ENNReal.ofReal r)
          Measure.count :=
        Work.BourgainPlan.KPWW.opArc_lp_bound_of_coeff hr.le hηml hK
          (fun m => (fourierCoeff_eq_integral_mul_star (mstEta d χ η n) m).symm) hKb
          (mstU l n) f hf

/-- **The main assembly** of the trivial `ℓʳ` bound for `m_{2^n} Ξ_n − ν_{2^n}`, given the three
numerical inputs (the `ℓ¹` norms `K₁`, `K₂` of the coefficient kernels of the level bump `η_n` and of
the profile-times-bump `h_n`, and the uniform cardinality bound `Ccard` for `𝒰(n)`).

Route: `opMul (projCls − nuCls) f = opMul projCls f − opMul nuCls f` (`opMul_sub`), the triangle
inequality for `eLpNorm` (`eLpNorm_sub_le`), the projection bound `eLpNorm_opMul_mstProjCls_le`
(`A_{2^n}` contraction + `opArc` bound) and the model bound obtained from
`mst_err1_opmul_coeff` with the kernel `fourierCoeff (mstNu …)` bounded by `#𝒰(n) K₂`
(`tsum_fourierCoeff_mstNu_le`). -/
theorem mst_major_err1_triv_aux (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (hc : 0 < P.leadingCoeff)
    {χ : ℝ} (hχ0 : 0 < χ) (hχ1 : χ < 1 / 10) (η : ℝ → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hηbd : ∀ x : ℝ, ‖η x‖ ≤ M)
    (hη2 : ∀ x : ℝ, 1 / 2 < |x| → η x = 0)
    (l : ℕ) (hl : 1 ≤ l) {r : ℝ} (hr : 1 < r)
    {K₁ K₂ Ccard : ℝ} (hK₁pos : 0 < K₁) (hK₂pos : 0 < K₂) (hCcpos : 0 < Ccard)
    (hK₁ : ∀ n : ℕ, Summable (fun m : ℤ => ‖fourierCoeff (mstEta P.natDegree χ η n) m‖) ∧
      (∑' m : ℤ, ‖fourierCoeff (mstEta P.natDegree χ η n) m‖) ≤ K₁)
    (hK₂ : ∀ n : ℕ, Summable (fun m : ℤ =>
        ‖fourierCoeff (mstProfBump P P.natDegree χ η n) m‖) ∧
      (∑' m : ℤ, ‖fourierCoeff (mstProfBump P P.natDegree χ η n) m‖) ≤ K₂)
    (hCc : ∀ n : ℕ, ((mstU l n).card : ℝ) ≤
      Ccard * Real.exp (((n : ℝ) ^ l) ^ (mstRho l)))
    (hηml : ∀ n : ℕ, MeasureTheory.MemLp
      (Work.BourgainPlan.Maximal.mstEta P.natDegree χ η n) ⊤
      (AddCircle.haarAddCircle (T := 1)))
    (hνml : ∀ n : ℕ, MeasureTheory.MemLp
      (Work.BourgainPlan.Maximal.mstNu P l P.natDegree χ η n) ⊤
      (AddCircle.haarAddCircle (T := 1))) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ (f : ℤ → ℂ) (hf : Memℓp f 2),
        MeasureTheory.eLpNorm (Work.BourgainPlan.IonescuWainger.opMul
            (Work.BourgainPlan.Maximal.mstMajErr1Cls P l P.natDegree χ η n (hηml n) (hνml n))
            f hf) (ENNReal.ofReal r) MeasureTheory.Measure.count
          ≤ ENNReal.ofReal (C * Real.exp (((n : ℝ) ^ l) ^ (Work.BourgainPlan.Maximal.mstRho l)))
              * MeasureTheory.eLpNorm f (ENNReal.ofReal r) MeasureTheory.Measure.count := by
  refine ⟨2 * (K₁ + K₂) * Ccard, by positivity, fun n f hf => ?_⟩
  have hE : (1 : ℝ≥0∞) ≤ ENNReal.ofReal r := ENNReal.one_le_ofReal.mpr hr.le
  set E : ℝ≥0∞ := MeasureTheory.eLpNorm f (ENNReal.ofReal r) MeasureTheory.Measure.count with hEdef
  -- ### the projection half
  have hproj := eLpNorm_opMul_mstProjCls_le P l P.natDegree χ η n (hηml n) hr
    (hK₁ n).1 (hK₁ n).2 f hf
  -- ### the model half
  have hkern : Summable (fun m : ℤ => ‖fourierCoeff (mstNu P l P.natDegree χ η n) m‖) ∧
      (∑' m : ℤ, ‖fourierCoeff (mstNu P l P.natDegree χ η n) m‖)
        ≤ ((mstU l n).card : ℝ) * K₂ :=
    tsum_fourierCoeff_mstNu_le P l P.natDegree χ η n (hηml n) (hK₂ n).1 (hK₂ n).2
  have hcint : ∀ m : ℤ, ∫ θ, ((mstNuCls P l P.natDegree χ η n (hνml n) :
        Work.BourgainPlan.IonescuWainger.Circle → ℂ) θ * star (fourier m θ)) ∂haarT
      = fourierCoeff (mstNu P l P.natDegree χ η n) m := by
    intro m
    rw [mstNuCls, fourierCoeff_eq_integral_mul_star (mstNu P l P.natDegree χ η n) m]
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp (hνml n)] with θ hθ
    rw [hθ]
  have hnu : MeasureTheory.eLpNorm (Work.BourgainPlan.IonescuWainger.opMul
        (mstNuCls P l P.natDegree χ η n (hνml n)) f hf)
        (ENNReal.ofReal r) MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (((mstU l n).card : ℝ) * K₂) * E :=
    mst_err1_opmul_coeff hr.le hkern.1 hcint hkern.2 f hf
  -- ### the triangle inequality and the arithmetic
  have hsub : Work.BourgainPlan.IonescuWainger.opMul
        (mstMajErr1Cls P l P.natDegree χ η n (hηml n) (hνml n)) f hf
      = Work.BourgainPlan.IonescuWainger.opMul
          (mstProjCls P l P.natDegree χ η n (hηml n)) f hf
        - Work.BourgainPlan.IonescuWainger.opMul
          (mstNuCls P l P.natDegree χ η n (hνml n)) f hf := by
    rw [mstMajErr1Cls]
    exact (opMul_sub _ _ f hf).symm
  have hA : (0 : ℝ) ≤ ((mstU l n).card : ℝ) := Nat.cast_nonneg _
  have hKsum : (0 : ℝ) ≤ K₁ + K₂ := by linarith
  have hexp : (0 : ℝ) < Real.exp (((n : ℝ) ^ l) ^ (mstRho l)) := Real.exp_pos _
  have hstep1 : MeasureTheory.eLpNorm (Work.BourgainPlan.IonescuWainger.opMul
        (mstMajErr1Cls P l P.natDegree χ η n (hηml n) (hνml n)) f hf)
        (ENNReal.ofReal r) MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (((mstU l n).card : ℝ) * K₁) * E
        + ENNReal.ofReal (((mstU l n).card : ℝ) * K₂) * E := by
    rw [hsub]
    calc MeasureTheory.eLpNorm (Work.BourgainPlan.IonescuWainger.opMul
          (mstProjCls P l P.natDegree χ η n (hηml n)) f hf
          - Work.BourgainPlan.IonescuWainger.opMul
            (mstNuCls P l P.natDegree χ η n (hνml n)) f hf)
          (ENNReal.ofReal r) MeasureTheory.Measure.count
        ≤ MeasureTheory.eLpNorm (Work.BourgainPlan.IonescuWainger.opMul
            (mstProjCls P l P.natDegree χ η n (hηml n)) f hf)
            (ENNReal.ofReal r) MeasureTheory.Measure.count
          + MeasureTheory.eLpNorm (Work.BourgainPlan.IonescuWainger.opMul
            (mstNuCls P l P.natDegree χ η n (hνml n)) f hf)
            (ENNReal.ofReal r) MeasureTheory.Measure.count :=
          eLpNorm_sub_le hE
      _ ≤ ENNReal.ofReal (((mstU l n).card : ℝ) * K₁) * E
          + ENNReal.ofReal (((mstU l n).card : ℝ) * K₂) * E := add_le_add hproj hnu
  have hstep2 : ENNReal.ofReal (((mstU l n).card : ℝ) * K₁) * E
        + ENNReal.ofReal (((mstU l n).card : ℝ) * K₂) * E
      ≤ ENNReal.ofReal ((2 * (K₁ + K₂) * Ccard)
          * Real.exp (((n : ℝ) ^ l) ^ (mstRho l))) * E := by
    have hreal : ((mstU l n).card : ℝ) * K₁ + ((mstU l n).card : ℝ) * K₂
        ≤ (2 * (K₁ + K₂) * Ccard) * Real.exp (((n : ℝ) ^ l) ^ (mstRho l)) := by
      have h1 : ((mstU l n).card : ℝ) * K₁ + ((mstU l n).card : ℝ) * K₂
          = ((mstU l n).card : ℝ) * (K₁ + K₂) := by ring
      rw [h1]
      have h2 : ((mstU l n).card : ℝ) * (K₁ + K₂)
          ≤ (Ccard * Real.exp (((n : ℝ) ^ l) ^ (mstRho l))) * (K₁ + K₂) :=
        mul_le_mul_of_nonneg_right (hCc n) hKsum
      have h3 : (Ccard * Real.exp (((n : ℝ) ^ l) ^ (mstRho l))) * (K₁ + K₂)
          ≤ (2 * (K₁ + K₂) * Ccard) * Real.exp (((n : ℝ) ^ l) ^ (mstRho l)) := by
        have := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ 2 by norm_num) hKsum
        nlinarith [hCcpos.le, hexp.le, hKsum]
      linarith
    calc ENNReal.ofReal (((mstU l n).card : ℝ) * K₁) * E
          + ENNReal.ofReal (((mstU l n).card : ℝ) * K₂) * E
        = (ENNReal.ofReal (((mstU l n).card : ℝ) * K₁)
            + ENNReal.ofReal (((mstU l n).card : ℝ) * K₂)) * E := by ring
      _ = ENNReal.ofReal (((mstU l n).card : ℝ) * K₁
            + ((mstU l n).card : ℝ) * K₂) * E := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity)]
      _ ≤ ENNReal.ofReal ((2 * (K₁ + K₂) * Ccard)
            * Real.exp (((n : ℝ) ^ l) ^ (mstRho l))) * E :=
          mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hreal) bot_le
  exact hstep1.trans hstep2

/-- Mirek-Stein-Trojan arXiv:1512.07518 §4.2 eq. (72): the trivial `ℓʳ` bound (all `r > 1`) for the first major-arc error `m_{2^n} Ξ_n − ν_{2^n}`, namely `‖opMul (mstMajErr1Cls …) f‖_{ℓʳ} ≤ C exp((n^l)^{1/(10l)}) ‖f‖_{ℓʳ}` uniformly in `n`.

Interpolating this with the `ℓ²` gain `2^{−n/2}` (`mst_major_err1_l2`) at `r = (1+p)/2` yields `2^{−c n}`, which is summable in `n`.

Route:
* `mstProjCls = khatZMult P (2^n) • arcSymbolLp η_n 𝒰(n)` (symbol `m_{2^n} Ξ_n`): `‖F⁻¹(m_{2^n} Ξ_n f̂)‖_{ℓʳ} ≤ ‖A_{2^n} f‖_{ℓʳ} + ‖A_{2^n} Π_n f‖_{ℓʳ} ≤ (1 + C)‖f‖_{ℓʳ}`, where `‖A_{2^n}‖ ≤ 1` is the `ℓʳ` contraction of the average (`discAvgZC_lp_contraction`) and `‖Π_n‖ ≤ C` is the Ionescu–Wainger `ℓʳ` bound over `Σ_{n^l}` (`IWSupersetBoundLift`, available unconditionally as `iwSupersetBoundLift_proof`, applied to the narrow bump `η_n`).  The Mikhlin data `hcd/hbdd/hder/hder2` discharge its hypotheses exactly as in `mst_minor_lp_per_n` (the narrowness is `mstEta_support` from `hη2` for large `n`; small `n` are absorbed into `C`).
* `mstNuCls` (symbol `ν_{2^n}`): a sum of `#𝒰(n)` modulated terms; each term `star (G(β) Φ_{2^n}(·−β)) · η_n(·−β)` is an `ℓʳ`-multiplier of norm `O(1)` uniformly in `(n, β)` — the profile factor is an average of modulated bumps of norm `O(1)` (`poly_dilation_lp_shift_const` / `dilation_const_bound`), and the bump factor is `O(1)` by Wiener + the Mikhlin data (`mikhlin_multiplier_lift`, or Young with summable Fourier coefficients of the scaled bump).  Hence `‖opMul (mstNuCls)‖_{ℓʳ} ≲ #𝒰(n) ≤ exp((n^l)^{1/(10l)})` (`sigmaN_card_le`); the `≤ #𝒰(n)` factor is the point of this bound.
* subtract and use the triangle inequality.

Caution (proof detail): the level bumps are `mstEta` of *varying* scale and the profile is not globally Mikhlin; the per-term `O(1)` bound must be produced from the scaling/`ℓ¹`-kernel of the bump and the dilation bound for the profile, with a constant independent of `n` and `β`. -/
theorem mst_major_err1_triv (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (hc : 0 < P.leadingCoeff)
    {χ : ℝ} (hχ0 : 0 < χ) (hχ1 : χ < 1 / 10) (η : ℝ → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hηbd : ∀ x : ℝ, ‖η x‖ ≤ M)
    (hη1 : ∀ x : ℝ, |x| ≤ 1 / 4 → η x = 1) (hη2 : ∀ x : ℝ, 1 / 2 < |x| → η x = 0)
    (l : ℕ) (hl : 1 ≤ l) {r : ℝ} (hr : 1 < r)
    (A : ℝ) (hA : 0 < A)
    (hcd : ∀ n : ℕ, ContDiff ℝ 2 (Work.BourgainPlan.Thm52.circleLift
      (Work.BourgainPlan.Maximal.mstEta P.natDegree χ η n)))
    (hbdd : ∀ (n : ℕ) (x : ℝ), ‖Work.BourgainPlan.Thm52.circleLift
      (Work.BourgainPlan.Maximal.mstEta P.natDegree χ η n) x‖ ≤ A)
    (hder : ∀ (n : ℕ) (x : ℝ), |x| * ‖deriv (Work.BourgainPlan.Thm52.circleLift
      (Work.BourgainPlan.Maximal.mstEta P.natDegree χ η n)) x‖ ≤ A)
    (hder2 : ∀ (n : ℕ) (x : ℝ), |x| ^ 2 * ‖iteratedDeriv 2 (Work.BourgainPlan.Thm52.circleLift
      (Work.BourgainPlan.Maximal.mstEta P.natDegree χ η n)) x‖ ≤ A)
    (hηml : ∀ n : ℕ, MeasureTheory.MemLp
      (Work.BourgainPlan.Maximal.mstEta P.natDegree χ η n) ⊤
      (AddCircle.haarAddCircle (T := 1)))
    (hνml : ∀ n : ℕ, MeasureTheory.MemLp
      (Work.BourgainPlan.Maximal.mstNu P l P.natDegree χ η n) ⊤
      (AddCircle.haarAddCircle (T := 1))) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ (f : ℤ → ℂ) (hf : Memℓp f 2),
        MeasureTheory.eLpNorm (Work.BourgainPlan.IonescuWainger.opMul
            (Work.BourgainPlan.Maximal.mstMajErr1Cls P l P.natDegree χ η n (hηml n) (hνml n))
            f hf) (ENNReal.ofReal r) MeasureTheory.Measure.count
          ≤ ENNReal.ofReal (C * Real.exp (((n : ℝ) ^ l) ^ (Work.BourgainPlan.Maximal.mstRho l)))
              * MeasureTheory.eLpNorm f (ENNReal.ofReal r) MeasureTheory.Measure.count := by
  have hχ' : χ + 1 ≤ (P.natDegree : ℝ) := by
    have h2 : (2 : ℝ) ≤ (P.natDegree : ℝ) := by exact_mod_cast hd
    linarith
  -- the `ℓ¹` bound for the coefficient kernel of the level bump
  obtain ⟨K₁, hK₁pos, hK₁⟩ := mst_err1_bump_coeff (d := P.natDegree) hχ' η hM hηbd hη2 (hcd 0)
  -- the `ℓ¹` bound for the coefficient kernel of the profile-times-bump
  obtain ⟨K₂, hK₂pos, hK₂raw⟩ := mst_err1_prof_coeff P hd hχ' η hM hηbd hη2 (hcd 0)
  have hK₂ : ∀ n : ℕ, Summable (fun m : ℤ =>
        ‖fourierCoeff (mstProfBump P P.natDegree χ η n) m‖) ∧
      (∑' m : ℤ, ‖fourierCoeff (mstProfBump P P.natDegree χ η n) m‖) ≤ K₂ := by
    intro n
    have hfun : (fun ξ : Work.BourgainPlan.IonescuWainger.Circle =>
          star (mstProf P (2 ^ n) ξ) * mstEta P.natDegree χ η n ξ)
        = mstProfBump P P.natDegree χ η n := by
      funext ξ
      simp only [mstProfBump, Pi.mul_apply]
    simpa only [hfun] using hK₂raw n
  -- the cardinality of the level set
  obtain ⟨Ccard, hCcpos, hCc⟩ := mstU_card_le_exp l hl
  exact mst_major_err1_triv_aux P hd hc hχ0 hχ1 η M hM hηbd hη2 l hl hr
    hK₁pos hK₂pos hCcpos hK₁ hK₂ hCc hηml hνml

end

end Work.BourgainPlan.Maximal
