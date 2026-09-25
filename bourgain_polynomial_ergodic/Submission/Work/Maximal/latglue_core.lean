import Mathlib
import Submission.Work.Maximal.mstWide_defs
import Submission.Work.Maximal.mstNuS_sub_mstWideModel_lr_tail
import Submission.Work.Maximal.latfix_mstWideModel_lr_maximal
import Submission.Work.Maximal.latfix_memLp_mstWideModel
import Submission.Work.Maximal.latglue_basic
import Submission.Work.Maximal.latglue_diff

/-!
# The core of the glue of the large-scale `ℓʳ` level estimate

`glue_core` is the body of `Work.Maximal.mstNuS_lr_large_aux_glue`, with the two ingredients that
live elsewhere left as explicit hypotheses:

* `hAll`, the *all-levels* narrow-to-wide tail bound
  (`Work.Maximal.mstNuS_sub_mstWideModel_lr_tail_all`), used for the finitely many levels below the
  torsion threshold;
* the `MemLp` data `hϱml`, `hΩml` of the wide bump and the wide model.

The argument is the one described in the docstring of the target: the pointwise inequality
`sup_{k ≥ K_s} |A_k g| ≤ sup_{k ≥ K_s} |(A_k − Ω_k) g| + sup_k |Ω_k g|`, the two-term triangle
inequality for `eLpNorm` (`eLpNorm_add_le_enorm_lat`), the landed large-scale tail estimate
`mstNuS_sub_mstWideModel_lr_tail` (uniform constant, valid for `s ≥ s₀`) together with `hAll` for
the finitely many small levels, and the wide-model maximal bound `mstWideModel_lr_maximal_lat` with
the corrected sampling principle.  The finite maximum over `s < s₀` is absorbed into the constant.
-/

open MeasureTheory Finset
open scoped BigOperators ENNReal

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.Maximal

noncomputable section

local notation "Circ" => Work.BourgainPlan.IonescuWainger.Circle
local notation "haarT" => (AddCircle.haarAddCircle (T := 1))

open Work.BourgainPlan.Maximal
open Work.BourgainPlan.IonescuWainger

theorem glue_core
    {r : ℝ}
    (hLattice : ∃ C : ℝ, 0 < C ∧ ∀ (H : ℝ → ℂ) (δ : ℝ), 0 < δ → Continuous H →
      MeasureTheory.Integrable H →
      (∀ ξ : ℝ, δ < |ξ| → FourierTransform.fourier H ξ = 0) →
      ∀ (Q : ℕ), 1 ≤ Q → δ * (Q : ℝ) ≤ 1 / 4 → ∀ (m : ℤ) (c : ℝ),
        (∑' x : ℤ, (Work.Maximal.mstHlMax (fun y : ℝ => ENNReal.ofReal ‖H y‖)
            ((Q : ℝ) * (x : ℝ) + (m : ℝ) - c)) ^ r)
          ≤ ENNReal.ofReal (C ^ r) *
            ∑' x : ℤ, ENNReal.ofReal (‖H ((Q : ℝ) * (x : ℝ) + (m : ℝ))‖ ^ r))
    (hΘ : Work.BourgainPlan.Maximal.MSTThetaBound)
    (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (hc : 0 < P.leadingCoeff)
    (l : ℕ) (hl : 1 ≤ l) {χ : ℝ} (hχ0 : 0 < χ) (hχ1 : χ < 1 / 10)
    (η : ℝ → ℂ) (M : ℝ) (hM : 0 < M) (hηc : ContDiff ℝ 2 η)
    (hηbd : ∀ x : ℝ, ‖η x‖ ≤ M)
    (hder1 : ∀ x : ℝ, |x| * ‖deriv η x‖ ≤ M)
    (hder2 : ∀ x : ℝ, |x| ^ 2 * ‖iteratedDeriv 2 η x‖ ≤ M)
    (hηsup : ∀ x : ℝ, 1 / 2 ≤ |x| → η x = 0)
    {δ : ℝ} (hδ : 0 < δ) (D : ℝ) (hD : 0 < D)
    (hGauss : ∀ (s : ℕ) (β : Work.BourgainPlan.IonescuWainger.Circle),
      β ∈ Work.BourgainPlan.Maximal.mstU l (s + 1) \ Work.BourgainPlan.Maximal.mstU l s →
      ‖Work.BourgainPlan.Maximal.mstG P β‖ ≤ D * ((s : ℝ) + 1) ^ (-(δ * l)))
    (hνsml : ∀ n s : ℕ, MeasureTheory.MemLp
      (Work.BourgainPlan.Maximal.mstNuS P l P.natDegree χ η n s) ⊤
      (AddCircle.haarAddCircle (T := 1)))
    (hϱml : ∀ s : ℕ, MeasureTheory.MemLp (mstWideBump P χ η s) ⊤
      (AddCircle.haarAddCircle (T := 1)))
    (hΩml : ∀ k s : ℕ, MeasureTheory.MemLp (mstWideModel P l χ η k s) ⊤
      (AddCircle.haarAddCircle (T := 1)))
    (hAll : ∃ C : ℕ → ℝ, (∀ s : ℕ, 0 < C s) ∧ ∀ s : ℕ, ∀ g : ℤ →₀ ℂ,
      MeasureTheory.eLpNorm (fun m : ℤ => (⨆ k : ℕ,
          ⨆ (_ : 2 ^ (Work.BourgainPlan.Maximal.mstKappa P s) ≤ k),
          ‖Work.BourgainPlan.IonescuWainger.opMul
              (Work.BourgainPlan.Maximal.mstNuSCls P l P.natDegree χ η k s (hνsml k s))
              (⇑g) (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g) m
            - Work.BourgainPlan.IonescuWainger.opMul
              ((hΩml k s).toLp (mstWideModel P l χ η k s))
              (⇑g) (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g) m‖ₑ))
          (ENNReal.ofReal r) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C s)
          * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal r) MeasureTheory.Measure.count)
    (hr : 1 < r) (hr2 : r < 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℕ, ∀ g : ℤ →₀ ℂ,
      MeasureTheory.eLpNorm (fun m : ℤ => (⨆ k : ℕ,
          ⨆ (_ : 2 ^ (Work.BourgainPlan.Maximal.mstKappa P s) ≤ k),
          ‖Work.BourgainPlan.IonescuWainger.opMul
            (Work.BourgainPlan.Maximal.mstNuSCls P l P.natDegree χ η k s (hνsml k s))
            (⇑g) (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g) m‖ₑ))
          (ENNReal.ofReal r) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C * Real.log ((s : ℝ) + 2))
          * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal r) MeasureTheory.Measure.count := by
  classical
  obtain ⟨Cw, hCwpos, hwide⟩ :=
    mstWideModel_lr_maximal_lat P hd hc l hl hχ0 hχ1 η M hM hηc hηbd hder1 hder2 hηsup
      hϱml hΩml hr hr2 hLattice
  obtain ⟨Ct, hCtpos, s₀, htail⟩ :=
    mstNuS_sub_mstWideModel_lr_tail P hd hc l hl hχ0 hχ1 η hηc hηsup hδ D hD hGauss hνsml
      hΩml hr hr2
  obtain ⟨CΔ, hCΔpos, hΔ⟩ := hAll
  set Ssum : ℝ := ∑ s ∈ Finset.range s₀, CΔ s with hSsumdef
  have hSsumnn : 0 ≤ Ssum := by
    rw [hSsumdef]
    exact Finset.sum_nonneg (fun s _ => (hCΔpos s).le)
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hCpos : 0 < Ssum / Real.log 2 + Ct / Real.log 2 + Cw + 1 := by
    have h1 : 0 ≤ Ssum / Real.log 2 := div_nonneg hSsumnn hlog2.le
    have h2 : 0 ≤ Ct / Real.log 2 := div_nonneg hCtpos.le hlog2.le
    linarith
  refine ⟨Ssum / Real.log 2 + Ct / Real.log 2 + Cw + 1, hCpos, fun s g => ?_⟩
  have hlogpos : 0 < Real.log ((s : ℝ) + 2) :=
    Real.log_pos (by linarith [Nat.cast_nonneg (α := ℝ) s] : (1 : ℝ) < (s : ℝ) + 2)
  have hlog2le : Real.log 2 ≤ Real.log ((s : ℝ) + 2) :=
    Real.log_le_log (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) s])
  -- the two ingredients of the pointwise splitting
  set F : ℤ → ℝ≥0∞ := fun m => ⨆ k : ℕ, ⨆ (_ : 2 ^ (mstKappa P s) ≤ k),
      ‖opMul (mstNuSCls P l P.natDegree χ η k s (hνsml k s)) (⇑g) (memℓp_finsupp g) m
        - opMul ((hΩml k s).toLp (mstWideModel P l χ η k s)) (⇑g) (memℓp_finsupp g) m‖ₑ
    with hFdef
  set G : ℤ → ℝ≥0∞ := fun m => ⨆ k : ℕ,
      ‖opMul (mstWideModelCls P l χ η k s (hΩml k s)) (⇑g) (memℓp_finsupp g) m‖ₑ
    with hGdef
  have hpt : (fun m : ℤ => (⨆ k : ℕ, ⨆ (_ : 2 ^ (mstKappa P s) ≤ k),
        ‖opMul (mstNuSCls P l P.natDegree χ η k s (hνsml k s)) (⇑g)
          (memℓp_finsupp g) m‖ₑ)) ≤ F + G := by
    intro m
    refine iSup_le (fun k => iSup_le (fun hk => ?_))
    have heq : opMul (mstNuSCls P l P.natDegree χ η k s (hνsml k s)) (⇑g)
          (memℓp_finsupp g) m
        = (opMul (mstNuSCls P l P.natDegree χ η k s (hνsml k s)) (⇑g)
              (memℓp_finsupp g) m
            - opMul ((hΩml k s).toLp (mstWideModel P l χ η k s)) (⇑g)
              (memℓp_finsupp g) m)
          + opMul ((hΩml k s).toLp (mstWideModel P l χ η k s)) (⇑g)
              (memℓp_finsupp g) m := by ring
    rw [heq]
    refine le_trans (enorm_add_le _ _) (add_le_add ?_ ?_)
    · exact le_iSup_of_le k (le_iSup_of_le hk le_rfl)
    · exact le_iSup_of_le k le_rfl
  have hmono : MeasureTheory.eLpNorm (fun m : ℤ => (⨆ k : ℕ,
        ⨆ (_ : 2 ^ (mstKappa P s) ≤ k),
        ‖opMul (mstNuSCls P l P.natDegree χ η k s (hνsml k s)) (⇑g)
          (memℓp_finsupp g) m‖ₑ))
      (ENNReal.ofReal r) MeasureTheory.Measure.count
      ≤ MeasureTheory.eLpNorm (F + G) (ENNReal.ofReal r) MeasureTheory.Measure.count :=
    eLpNorm_mono_enorm_lat (p := r) (lt_trans zero_lt_one hr) hpt
  have htri : MeasureTheory.eLpNorm (F + G) (ENNReal.ofReal r) MeasureTheory.Measure.count
      ≤ MeasureTheory.eLpNorm F (ENNReal.ofReal r) MeasureTheory.Measure.count
        + MeasureTheory.eLpNorm G (ENNReal.ofReal r) MeasureTheory.Measure.count :=
    eLpNorm_add_le_enorm_lat hr F G
  have hG : MeasureTheory.eLpNorm G (ENNReal.ofReal r) MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (Cw * Real.log ((s : ℝ) + 2))
        * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal r) MeasureTheory.Measure.count :=
    hwide s g
  -- the common final step, with `K₁` the constant of the difference estimate
  have key : ∀ K₁ : ℝ, 0 ≤ K₁ →
      MeasureTheory.eLpNorm F (ENNReal.ofReal r) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal K₁
          * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal r) MeasureTheory.Measure.count →
      K₁ + Cw * Real.log ((s : ℝ) + 2)
        ≤ (Ssum / Real.log 2 + Ct / Real.log 2 + Cw + 1) * Real.log ((s : ℝ) + 2) →
      MeasureTheory.eLpNorm (fun m : ℤ => (⨆ k : ℕ,
          ⨆ (_ : 2 ^ (mstKappa P s) ≤ k),
          ‖opMul (mstNuSCls P l P.natDegree χ η k s (hνsml k s)) (⇑g)
            (memℓp_finsupp g) m‖ₑ))
          (ENNReal.ofReal r) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal ((Ssum / Real.log 2 + Ct / Real.log 2 + Cw + 1)
            * Real.log ((s : ℝ) + 2))
          * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal r) MeasureTheory.Measure.count := by
    intro K₁ hK₁ hF hconst
    have hCwL : 0 ≤ Cw * Real.log ((s : ℝ) + 2) := mul_nonneg hCwpos.le hlogpos.le
    calc MeasureTheory.eLpNorm (fun m : ℤ => (⨆ k : ℕ,
          ⨆ (_ : 2 ^ (mstKappa P s) ≤ k),
          ‖opMul (mstNuSCls P l P.natDegree χ η k s (hνsml k s)) (⇑g)
            (memℓp_finsupp g) m‖ₑ))
          (ENNReal.ofReal r) MeasureTheory.Measure.count
        ≤ MeasureTheory.eLpNorm F (ENNReal.ofReal r) MeasureTheory.Measure.count
            + MeasureTheory.eLpNorm G (ENNReal.ofReal r) MeasureTheory.Measure.count :=
          le_trans hmono htri
      _ ≤ ENNReal.ofReal K₁
              * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal r) MeasureTheory.Measure.count
            + ENNReal.ofReal (Cw * Real.log ((s : ℝ) + 2))
              * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal r) MeasureTheory.Measure.count :=
          add_le_add hF hG
      _ = ENNReal.ofReal (K₁ + Cw * Real.log ((s : ℝ) + 2))
            * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal r) MeasureTheory.Measure.count := by
          rw [← add_mul, ← ENNReal.ofReal_add hK₁ hCwL]
      _ ≤ ENNReal.ofReal ((Ssum / Real.log 2 + Ct / Real.log 2 + Cw + 1)
            * Real.log ((s : ℝ) + 2))
            * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal r) MeasureTheory.Measure.count :=
          mul_le_mul_left (ENNReal.ofReal_le_ofReal hconst) _
  by_cases hs : s₀ ≤ s
  · -- large levels: the landed tail estimate (constant independent of `s`)
    refine key Ct hCtpos.le (htail s hs g) ?_
    have hCtlog : 0 ≤ Ct / Real.log 2 := div_nonneg hCtpos.le hlog2.le
    have h1 : Ct ≤ (Ct / Real.log 2) * Real.log ((s : ℝ) + 2) := by
      calc Ct = (Ct / Real.log 2) * Real.log 2 := by field_simp
        _ ≤ (Ct / Real.log 2) * Real.log ((s : ℝ) + 2) :=
            mul_le_mul_of_nonneg_left hlog2le hCtlog
    have h2 : 0 ≤ (Ssum / Real.log 2) * Real.log ((s : ℝ) + 2) :=
      mul_nonneg (div_nonneg hSsumnn hlog2.le) hlogpos.le
    nlinarith [h1, h2, hlogpos, hCwpos, hCtpos]
  · -- small levels: the all-levels tail estimate, absorbed into the finite maximum
    have hs' : s < s₀ := not_le.mp hs
    refine key (CΔ s) (hCΔpos s).le (hΔ s g) ?_
    have hCΔle : CΔ s ≤ Ssum := by
      rw [hSsumdef]
      exact Finset.single_le_sum (fun i _ => (hCΔpos i).le) (Finset.mem_range.mpr hs')
    have h1 : CΔ s ≤ (Ssum / Real.log 2) * Real.log ((s : ℝ) + 2) := by
      refine le_trans hCΔle ?_
      calc Ssum = (Ssum / Real.log 2) * Real.log 2 := by field_simp
        _ ≤ (Ssum / Real.log 2) * Real.log ((s : ℝ) + 2) :=
            mul_le_mul_of_nonneg_left hlog2le (div_nonneg hSsumnn hlog2.le)
    have h2 : 0 ≤ (Ct / Real.log 2) * Real.log ((s : ℝ) + 2) :=
      mul_nonneg (div_nonneg hCtpos.le hlog2.le) hlogpos.le
    nlinarith [h1, h2, hlogpos, hCwpos]

end

end Work.Maximal
