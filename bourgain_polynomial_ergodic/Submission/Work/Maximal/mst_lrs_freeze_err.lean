import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_major_defs
import Submission.Work.BourgainPlan.Maximal.mst_scalar_defs
import Submission.Work.BourgainPlan.Maximal.mst_level_defs
import Submission.Work.BourgainPlan.Maximal.mst_lvl_approx_pointwise
import Submission.Work.BourgainPlan.Maximal.khatZMult_coeFn_star_mstWeyl
import Submission.Work.BourgainPlan.Maximal.mstEta_arcSum_le
import Submission.Work.BourgainPlan.Maximal.mstProfBumpS_coeff
import Submission.Work.BourgainPlan.Maximal.mstModelFn_kernel_l1_of_coeff
import Submission.Work.BourgainPlan.Maximal.eLpNorm_two_opMul_le
import Submission.Work.BourgainPlan.Maximal.mst_majErr_interp
import Submission.Work.BourgainPlan.KPWW.opArc_lp_bound_of_coeff
import Submission.Work.BourgainPlan.IonescuWainger.OpArcLinear
import Submission.Work.BourgainPlan.Maximal.mstU_card_le_exp
import Submission.Work.BourgainPlan.Maximal.mikhlin_conditions_scaled_bump
import Submission.Work.BourgainPlan.Maximal.minor_arc_lp
import Submission.Work.Maximal.arcSymbolW_lp_bound_of_coeff

namespace Work.Maximal

open MeasureTheory Finset
open scoped BigOperators ENNReal
open Work.BourgainPlan.IonescuWainger
open Work.BourgainPlan.Maximal

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

local notation "haarT" => (AddCircle.haarAddCircle (T := 1))
local notation "Circ" => Work.BourgainPlan.IonescuWainger.Circle

/-- The strict support condition `1/2 < |x|` follows from the hypothesis `1/2 ≤ |x|`. -/
lemma mstFreeze_supp_lt {η : ℝ → ℂ} (hηsup : ∀ x : ℝ, 1 / 2 ≤ |x| → η x = 0) :
    ∀ x : ℝ, 1 / 2 < |x| → η x = 0 :=
  fun x hx => hηsup x hx.le

/-- **Step (1) of the freezing estimate**: on the annulus `𝒰(s+1) ∖ 𝒰(s)` of level `s`, the
difference `ν^s_{2^k} - star (m_J) · Π^s_{2^k}` of the weighted level symbol and the frozen
weight-free model is a.e. bounded by `C exp(-√(s+1)/2)`. -/
theorem mstFreeze_pointwise
    (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (hc : 0 < P.leadingCoeff)
    (l : ℕ) (hl : 1 ≤ l) {χ : ℝ} (hχ0 : 0 < χ) (hχ1 : χ < 1 / 10)
    (η : ℝ → ℂ) (hηc : ContDiff ℝ 2 η)
    (hηsup : ∀ x : ℝ, 1 / 2 ≤ |x| → η x = 0)
    (hpi : ∀ (N s : ℕ), MeasureTheory.MemLp
      (fun ζ : Circ => star (mstProf P N ζ) * mstEta P.natDegree χ η s ζ) ⊤ haarT)
    (hνsml : ∀ n s : ℕ, MeasureTheory.MemLp
      (mstNuS P l P.natDegree χ η n s) ⊤ haarT) :
    ∃ C : ℝ, 0 < C ∧ ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s → ∀ k : ℕ,
      ∀ᵐ ξ ∂haarT, ‖(((mstNuSCls P l P.natDegree χ η k s (hνsml k s) -
        khatZMult P (⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊) •
          arcSymbolLp (fun ζ : Circ => star (mstProf P (2 ^ k) ζ) *
            mstEta P.natDegree χ η s ζ) (hpi (2 ^ k) s)
          (mstLevel l (s + 1) \ mstLevel l s) : Lp ℂ ⊤ haarT) : Circ → ℂ) ξ)‖
        ≤ C * Real.exp (-(Real.sqrt ((s : ℝ) + 1) / 2)) := by
  classical
  have hd1 : 1 ≤ P.natDegree := by omega
  have hχd : χ < (P.natDegree : ℝ) := by
    have h2 : (2 : ℝ) ≤ (P.natDegree : ℝ) := by exact_mod_cast hd
    linarith
  have hη2 : ∀ x : ℝ, 1 / 2 < |x| → η x = 0 := mstFreeze_supp_lt hηsup
  obtain ⟨C₁, hC₁, N₁, hpt⟩ := mst_lvl_approx_pointwise P hd hc hχ0 hχ1 η hη2 l hl
  obtain ⟨M₂, hM₂0, hM₂⟩ :=
    mstEta_arcSum_le l hl P.natDegree hd1 χ hχ0 hχd η hηc.continuous hηsup
  refine ⟨C₁ * M₂, mul_pos hC₁ hM₂0, max N₁ 1, fun s hs k => ?_⟩
  have hsN₁ : N₁ ≤ s := le_trans (le_max_left _ _) hs
  have hs1 : 1 ≤ s := le_trans (le_max_right _ _) hs
  set J : ℕ := ⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊ with hJdef
  set E : Finset Circ := mstLevel l (s + 1) \ mstLevel l s with hEdef
  have hEeq : E = mstU l (s + 1) \ mstU l s := by
    have hs0 : ¬ (s = 0) := by omega
    rw [hEdef, mstLevel_succ]
    simp only [mstLevel, hs0, if_false]
  set ψ : Circ → ℂ := fun ζ => star (mstProf P (2 ^ k) ζ) * mstEta P.natDegree χ η s ζ with hψdef
  have hsub := Lp.coeFn_sub (mstNuSCls P l P.natDegree χ η k s (hνsml k s))
    (khatZMult P J • arcSymbolLp ψ (hpi (2 ^ k) s) E)
  have hsmul := Lp.coeFn_lpSMul (r := ⊤) (khatZMult P J) (arcSymbolLp ψ (hpi (2 ^ k) s) E)
  have hsmul' : (((khatZMult P J • arcSymbolLp ψ (hpi (2 ^ k) s) E : Lp ℂ ⊤ haarT) :
      Circ → ℂ)) =ᵐ[haarT] fun ξ =>
        (khatZMult P J : Circ → ℂ) ξ * (arcSymbolLp ψ (hpi (2 ^ k) s) E : Circ → ℂ) ξ := by
    filter_upwards [hsmul] with ξ h
    rw [h]; rfl
  have hν := mstNuSCls_coeFn P l P.natDegree χ η k s (hνsml k s)
  have hμ := khatZMult_coeFn_star_mstWeyl P J
  have hΨ := arcSymbolLp_coeFn ψ (hpi (2 ^ k) s) E
  filter_upwards [hsub, hsmul', hν, hμ, hΨ] with ξ h1 h2 h3 h4 h5
  rw [h1, Pi.sub_apply, h2, h3, h4, h5]
  have hψapp : ∀ β : Circ, ψ (ξ - β) = star (mstProf P (2 ^ k) (ξ - β)) *
      mstEta P.natDegree χ η s (ξ - β) := fun β => by rw [hψdef]
  have hsym : mstNuS P l P.natDegree χ η k s ξ - star (mstWeyl P J ξ) * arcSymbol ψ E ξ
      = ∑ β ∈ E, (star (mstG P β) - star (mstWeyl P J ξ)) *
          (star (mstProf P (2 ^ k) (ξ - β)) * mstEta P.natDegree χ η s (ξ - β)) := by
    rw [mstNuS_apply, arcSymbol_apply, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [hψapp β]
    ring
  have hsum_bound : ∑ β ∈ E, ‖mstEta P.natDegree χ η s (ξ - β)‖ ≤ M₂ := by
    rw [hEeq]; exact hM₂ s ξ
  have hterm : ∀ β ∈ E,
      ‖(star (mstG P β) - star (mstWeyl P J ξ)) *
          (star (mstProf P (2 ^ k) (ξ - β)) * mstEta P.natDegree χ η s (ξ - β))‖
        ≤ (C₁ * Real.exp (-(Real.sqrt ((s : ℝ) + 1) / 2))) *
            ‖mstEta P.natDegree χ η s (ξ - β)‖ := by
    intro β hβ
    by_cases hz : mstEta P.natDegree χ η s (ξ - β) = 0
    · rw [hz]
      simp
    · have hβ' : β ∈ mstLevel l (s + 1) \ mstLevel l s := hEdef ▸ hβ
      have hβU : β ∈ mstU l (s + 1) := by
        rw [mstLevel_succ] at hβ'
        exact (Finset.mem_sdiff.mp hβ').1
      have hweyl : ‖mstWeyl P J ξ - mstG P β‖
          ≤ C₁ * Real.exp (-(Real.sqrt ((s : ℝ) + 1) / 2)) := by
        rw [hJdef]
        exact hpt s hsN₁ β ξ hβU hz
      have hG : ‖star (mstG P β) - star (mstWeyl P J ξ)‖
          ≤ C₁ * Real.exp (-(Real.sqrt ((s : ℝ) + 1) / 2)) := by
        have hs1' : star (mstG P β) - star (mstWeyl P J ξ)
            = star (mstG P β - mstWeyl P J ξ) := by
          rw [star_sub]
        rw [hs1', norm_star]
        calc ‖mstG P β - mstWeyl P J ξ‖ = ‖mstWeyl P J ξ - mstG P β‖ := by
              rw [← norm_neg]; congr 1; ring
          _ ≤ C₁ * Real.exp (-(Real.sqrt ((s : ℝ) + 1) / 2)) := hweyl
      have hΦ : ‖star (mstProf P (2 ^ k) (ξ - β))‖ ≤ 1 := by
        rw [norm_star, mstProf_apply]
        exact norm_polyProfile_le_one P (2 ^ k) (iwRep (ξ - β))
      have hinner : ‖star (mstProf P (2 ^ k) (ξ - β)) *
            mstEta P.natDegree χ η s (ξ - β)‖ ≤ ‖mstEta P.natDegree χ η s (ξ - β)‖ := by
        rw [norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) hΦ
      calc ‖(star (mstG P β) - star (mstWeyl P J ξ)) *
              (star (mstProf P (2 ^ k) (ξ - β)) * mstEta P.natDegree χ η s (ξ - β))‖
          = ‖star (mstG P β) - star (mstWeyl P J ξ)‖ *
              ‖star (mstProf P (2 ^ k) (ξ - β)) * mstEta P.natDegree χ η s (ξ - β)‖ :=
            norm_mul _ _
        _ ≤ (C₁ * Real.exp (-(Real.sqrt ((s : ℝ) + 1) / 2))) *
              ‖mstEta P.natDegree χ η s (ξ - β)‖ :=
            mul_le_mul hG hinner (norm_nonneg _) (by positivity)
  calc ‖mstNuS P l P.natDegree χ η k s ξ - star (mstWeyl P J ξ) * arcSymbol ψ E ξ‖
      = ‖∑ β ∈ E, (star (mstG P β) - star (mstWeyl P J ξ)) *
          (star (mstProf P (2 ^ k) (ξ - β)) * mstEta P.natDegree χ η s (ξ - β))‖ := by
        rw [hsym]
    _ ≤ ∑ β ∈ E, ‖(star (mstG P β) - star (mstWeyl P J ξ)) *
          (star (mstProf P (2 ^ k) (ξ - β)) * mstEta P.natDegree χ η s (ξ - β))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ β ∈ E, (C₁ * Real.exp (-(Real.sqrt ((s : ℝ) + 1) / 2))) *
          ‖mstEta P.natDegree χ η s (ξ - β)‖ := Finset.sum_le_sum hterm
    _ = (C₁ * Real.exp (-(Real.sqrt ((s : ℝ) + 1) / 2))) *
          ∑ β ∈ E, ‖mstEta P.natDegree χ η s (ξ - β)‖ := (Finset.mul_sum _ _ _).symm
    _ ≤ (C₁ * Real.exp (-(Real.sqrt ((s : ℝ) + 1) / 2))) * M₂ :=
        mul_le_mul_of_nonneg_left hsum_bound (by positivity)
    _ = (C₁ * M₂) * Real.exp (-(Real.sqrt ((s : ℝ) + 1) / 2)) := by ring

/-- The **freezing-error symbol class** of MST §4.4: `ν^s_{2^k} - m_J • Π^s_{2^k}`, i.e. the
weighted level symbol minus the frozen weight-free model at the level scale `J = ⌊exp √(s+1)⌋`. -/
abbrev mstFreezeCls (P : Polynomial ℤ) (l : ℕ) (χ : ℝ) (η : ℝ → ℂ) (k s : ℕ)
    (hpi : ∀ (N s : ℕ), MeasureTheory.MemLp
      (fun ζ : Circ => star (mstProf P N ζ) * mstEta P.natDegree χ η s ζ) ⊤ haarT)
    (hνsml : ∀ n s : ℕ, MeasureTheory.MemLp (mstNuS P l P.natDegree χ η n s) ⊤ haarT) :
    Lp ℂ ⊤ haarT :=
  mstNuSCls P l P.natDegree χ η k s (hνsml k s) -
    khatZMult P (⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊) •
      arcSymbolLp (fun ζ : Circ => star (mstProf P (2 ^ k) ζ) * mstEta P.natDegree χ η s ζ)
        (hpi (2 ^ k) s) (mstLevel l (s + 1) \ mstLevel l s)

/-- The `eLpNorm` form of the `ℓ^q` contraction of the density average. -/
lemma mstFreeze_discAvgZC_eLpNorm_le (P : Polynomial ℤ) (N : ℕ) {q : ℝ} (hq : 1 ≤ q) (g : ℤ → ℂ) :
    MeasureTheory.eLpNorm (discAvgZC P N g) (ENNReal.ofReal q) MeasureTheory.Measure.count
      ≤ MeasureTheory.eLpNorm g (ENNReal.ofReal q) MeasureTheory.Measure.count := by
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le zero_lt_one hq
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal
        (ENNReal.ofReal_ne_zero_iff.mpr hq0) ENNReal.ofReal_ne_top (measurable_of_countable _).aestronglyMeasurable,
      MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal
        (ENNReal.ofReal_ne_zero_iff.mpr hq0) ENNReal.ofReal_ne_top (measurable_of_countable _).aestronglyMeasurable]
  simp only [ENNReal.toReal_ofReal hq0.le]
  exact ENNReal.rpow_le_rpow (discAvgZC_contraction P N hq g) (by positivity)

/-- **Step (2) of the freezing estimate**: the `ℓ²` endpoint, from the a.e. pointwise bound and
Plancherel. -/
theorem mstFreeze_l2
    (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (hc : 0 < P.leadingCoeff)
    (l : ℕ) (hl : 1 ≤ l) {χ : ℝ} (hχ0 : 0 < χ) (hχ1 : χ < 1 / 10)
    (η : ℝ → ℂ) (hηc : ContDiff ℝ 2 η)
    (hηsup : ∀ x : ℝ, 1 / 2 ≤ |x| → η x = 0)
    (hpi : ∀ (N s : ℕ), MeasureTheory.MemLp
      (fun ζ : Circ => star (mstProf P N ζ) * mstEta P.natDegree χ η s ζ) ⊤ haarT)
    (hνsml : ∀ n s : ℕ, MeasureTheory.MemLp (mstNuS P l P.natDegree χ η n s) ⊤ haarT) :
    ∃ C : ℝ, 0 < C ∧ ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s → ∀ k : ℕ, ∀ g : ℤ →₀ ℂ,
      MeasureTheory.eLpNorm (fun m : ℤ =>
          opMul (mstFreezeCls P l χ η k s hpi hνsml) (⇑g) (memℓp_finsupp g) m)
        (ENNReal.ofReal 2) (MeasureTheory.Measure.count)
        ≤ ENNReal.ofReal (C * Real.exp (-(Real.sqrt ((s : ℝ) + 1) / 2)))
          * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal 2) (MeasureTheory.Measure.count) := by
  obtain ⟨C, hC, s₀, hpt⟩ := mstFreeze_pointwise P hd hc l hl hχ0 hχ1 η hηc hηsup hpi hνsml
  refine ⟨C, hC, s₀, fun s hs k g => ?_⟩
  have hμ : 0 ≤ C * Real.exp (-(Real.sqrt ((s : ℝ) + 1) / 2)) := by positivity
  have h := eLpNorm_two_opMul_le (Φ := mstFreezeCls P l χ η k s hpi hνsml)
    (f := (⇑g : ℤ → ℂ)) (memℓp_finsupp g) hμ (hpt s hs k)
  simpa using h

/-- **Step (3) of the freezing estimate**: the *trivial* `ℓ^q` bound (all real `q > 1`), with the
subexponential loss `exp((s+1)^{1/10})` coming only from the cardinality of the level annulus.  The
two summands of `ν^s_{2^k} - m_J • Π^s_{2^k}` are bounded separately: the weighted arc symbol by the
`ℓ¹`-kernel of `star (mstProf P (2^k) ·) · η_s` (`mstProfBumpS_coeff` + `arcSymbolW_lp_bound_of_coeff`),
and the frozen term by the `ℓ^q` contraction of the density average composed with the unweighted arc
operator (`opArc_lp_bound_of_coeff`). -/
theorem mstFreeze_triv
    (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (hc : 0 < P.leadingCoeff)
    (l : ℕ) (hl : 1 ≤ l) {χ : ℝ} (hχ0 : 0 < χ) (hχ1 : χ < 1 / 10)
    (η : ℝ → ℂ) (M : ℝ) (hM : 0 < M) (hηc : ContDiff ℝ 2 η)
    (hηbd : ∀ x : ℝ, ‖η x‖ ≤ M)
    (hder1 : ∀ x : ℝ, |x| * ‖deriv η x‖ ≤ M)
    (hder2 : ∀ x : ℝ, |x| ^ 2 * ‖iteratedDeriv 2 η x‖ ≤ M)
    (hηsup : ∀ x : ℝ, 1 / 2 ≤ |x| → η x = 0)
    (hpi : ∀ (N s : ℕ), MeasureTheory.MemLp
      (fun ζ : Circ => star (mstProf P N ζ) * mstEta P.natDegree χ η s ζ) ⊤ haarT)
    (hνsml : ∀ n s : ℕ, MeasureTheory.MemLp (mstNuS P l P.natDegree χ η n s) ⊤ haarT)
    {q : ℝ} (hq : 1 < q) :
    ∃ C : ℝ, 0 < C ∧ ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s → ∀ k : ℕ, ∀ g : ℤ →₀ ℂ,
      MeasureTheory.eLpNorm (fun m : ℤ =>
          opMul (mstFreezeCls P l χ η k s hpi hνsml) (⇑g) (memℓp_finsupp g) m)
        (ENNReal.ofReal q) (MeasureTheory.Measure.count)
        ≤ ENNReal.ofReal (C * Real.exp (((s : ℝ) + 1) ^ (1 / 10 : ℝ)))
          * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal q) (MeasureTheory.Measure.count) := by
  classical
  have hd1 : 1 ≤ P.natDegree := by omega
  have hχ : χ + 1 ≤ (P.natDegree : ℝ) := by
    have h2 : (2 : ℝ) ≤ (P.natDegree : ℝ) := by exact_mod_cast hd
    linarith
  have hη2 : ∀ x : ℝ, 1 / 2 < |x| → η x = 0 := mstFreeze_supp_lt hηsup
  have hL : mstEta P.natDegree χ η 0 = fun ξ : Circ => η (1 * iwRep ξ) := by
    funext ξ
    rw [mstEta_apply]
    norm_num
  have hcd0 : ContDiff ℝ 2 (Work.BourgainPlan.Thm52.circleLift (mstEta P.natDegree χ η 0)) := by
    rw [hL]
    exact (mikhlin_conditions_scaled_bump (η := η) (M := M) (c := 1) hM.le
      (by norm_num) hηc hηbd hder1 hder2 hηsup).1
  obtain ⟨K, hKpos, hKB⟩ := mstProfBumpS_coeff P P.natDegree χ η M hM.le hχ hηbd hη2 hcd0
  obtain ⟨Cc, hCcpos, hCc⟩ := mstU_card_le_exp l hl
  refine ⟨2 * K * Cc, by positivity, 1, fun s hs k g => ?_⟩
  have hs1 : 1 ≤ s := hs
  simp only [mstFreezeCls]
  set J : ℕ := ⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊ with hJdef
  set φ : Circ → ℂ := fun ζ => star (mstProf P (2 ^ k) ζ) * mstEta P.natDegree χ η s ζ with hφdef
  set E : Finset Circ := mstLevel l (s + 1) \ mstLevel l s with hEdef
  have hEeq : E = mstU l (s + 1) \ mstU l s := by
    have hs0 : ¬ (s = 0) := by omega
    rw [hEdef, mstLevel_succ]
    simp only [mstLevel, hs0, if_false]
  have hkern : Summable (fun m : ℤ => ‖∫ ξ : Circ, φ ξ * star (fourier m ξ) ∂haarT‖) ∧
      (∑' m : ℤ, ‖∫ ξ : Circ, φ ξ * star (fourier m ξ) ∂haarT‖) ≤ K := by
    simpa only [hφdef] using hKB (2 ^ k) s (Nat.one_le_two_pow)
  have hfirst : MeasureTheory.eLpNorm (fun m : ℤ => opMul
        (mstNuSCls P l P.natDegree χ η k s (hνsml k s)) (⇑g) (memℓp_finsupp g) m)
      (ENNReal.ofReal q) MeasureTheory.Measure.count
      ≤ ENNReal.ofReal ((E.card : ℝ) * K)
        * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal q) MeasureTheory.Measure.count := by
    have hNuS : mstNuS P l P.natDegree χ η k s
        = arcSymbolW (fun β : Circ => β) (fun β => star (mstG P β)) E φ := by
      funext ξ
      rw [hEdef, hφdef]
      simp only [mstNuS, mstModelFn_apply, arcSymbolW_apply]
    have hcls : mstNuSCls P l P.natDegree χ η k s (hνsml k s)
        = arcSymbolWLp (fun β : Circ => β) (fun β => star (mstG P β)) E φ (hpi (2 ^ k) s) := by
      refine Lp.ext ?_
      filter_upwards [mstNuSCls_coeFn P l P.natDegree χ η k s (hνsml k s),
        arcSymbolWLp_coeFn (fun β : Circ => β) (fun β => star (mstG P β)) E φ
          (hpi (2 ^ k) s)] with ξ h1 h2
      rw [h1, h2]
      exact congrFun hNuS ξ
    rw [hcls]
    have hb := arcSymbolW_lp_bound_of_coeff (p := q) (W := 1) hq.le (hpi (2 ^ k) s) hkern.1
      (fun n => rfl) (by norm_num) hkern.2 (fun β => star (mstG P β)) E
      (fun β _ => by rw [norm_star]; exact mstG_norm_le_one P β) g
    simpa only [one_mul, hφdef] using hb
  have hsecond : MeasureTheory.eLpNorm (fun m : ℤ => opMul
        (khatZMult P J • arcSymbolLp φ (hpi (2 ^ k) s) E) (⇑g) (memℓp_finsupp g) m)
      (ENNReal.ofReal q) MeasureTheory.Measure.count
      ≤ ENNReal.ofReal ((E.card : ℝ) * K)
        * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal q) MeasureTheory.Measure.count := by
    rw [← discAvgZC_opArc_eq_opMul_smul P J φ (hpi (2 ^ k) s) E (⇑g) (memℓp_finsupp g)]
    calc MeasureTheory.eLpNorm
          (discAvgZC P J (opArc φ (hpi (2 ^ k) s) E (⇑g) (memℓp_finsupp g)))
          (ENNReal.ofReal q) MeasureTheory.Measure.count
        ≤ MeasureTheory.eLpNorm (opArc φ (hpi (2 ^ k) s) E (⇑g) (memℓp_finsupp g))
            (ENNReal.ofReal q) MeasureTheory.Measure.count := mstFreeze_discAvgZC_eLpNorm_le P J hq.le _
      _ ≤ ENNReal.ofReal ((E.card : ℝ) * K)
            * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal q) MeasureTheory.Measure.count :=
          Work.BourgainPlan.KPWW.opArc_lp_bound_of_coeff hq.le (hpi (2 ^ k) s) hkern.1
            (fun n => rfl) hkern.2 E (⇑g) (memℓp_finsupp g)
  have hsub : opMul (mstNuSCls P l P.natDegree χ η k s (hνsml k s) -
        khatZMult P J • arcSymbolLp φ (hpi (2 ^ k) s) E) (⇑g) (memℓp_finsupp g)
      = opMul (mstNuSCls P l P.natDegree χ η k s (hνsml k s)) (⇑g) (memℓp_finsupp g)
        - opMul (khatZMult P J • arcSymbolLp φ (hpi (2 ^ k) s) E) (⇑g) (memℓp_finsupp g) :=
    (opMul_sub _ _ _ _).symm
  have hfuneq : (fun m : ℤ => opMul (mstNuSCls P l P.natDegree χ η k s (hνsml k s) -
        khatZMult P J • arcSymbolLp φ (hpi (2 ^ k) s) E) (⇑g) (memℓp_finsupp g) m)
      = (opMul (mstNuSCls P l P.natDegree χ η k s (hνsml k s)) (⇑g) (memℓp_finsupp g)
        - opMul (khatZMult P J • arcSymbolLp φ (hpi (2 ^ k) s) E) (⇑g)
            (memℓp_finsupp g)) := by
    funext m
    exact congrFun hsub m
  have hEsub : E ⊆ mstU l (s + 1) := by
    intro β hβ
    have h : β ∈ mstLevel l (s + 1) \ mstLevel l s := hEdef ▸ hβ
    rw [mstLevel_succ] at h
    exact (Finset.mem_sdiff.mp h).1
  have hcard : (E.card : ℝ) ≤ Cc * Real.exp (((s : ℝ) + 1) ^ (1 / 10 : ℝ)) := by
    calc (E.card : ℝ) ≤ ((mstU l (s + 1)).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hEsub
      _ ≤ Cc * Real.exp (((((s + 1 : ℕ)) : ℝ) ^ l) ^ (mstRho l)) := hCc (s + 1)
      _ = Cc * Real.exp (((s : ℝ) + 1) ^ (1 / 10 : ℝ)) := by
          rw [mstRho_pow_eq_real l hl (s + 1) (by omega)]
          push_cast
          ring_nf
  have hreal : (E.card : ℝ) * K + (E.card : ℝ) * K
      ≤ (2 * K * Cc) * Real.exp (((s : ℝ) + 1) ^ (1 / 10 : ℝ)) := by
    have hexp : 0 < Real.exp (((s : ℝ) + 1) ^ (1 / 10 : ℝ)) := Real.exp_pos _
    have h1 : (E.card : ℝ) * K + (E.card : ℝ) * K = 2 * ((E.card : ℝ) * K) := by ring
    have h2 : 2 * ((E.card : ℝ) * K) ≤ 2 * ((Cc * Real.exp (((s : ℝ) + 1) ^ (1 / 10 : ℝ))) * K) := by
      nlinarith [hcard, hKpos, hexp]
    calc (E.card : ℝ) * K + (E.card : ℝ) * K = 2 * ((E.card : ℝ) * K) := h1
      _ ≤ 2 * ((Cc * Real.exp (((s : ℝ) + 1) ^ (1 / 10 : ℝ))) * K) := h2
      _ = (2 * K * Cc) * Real.exp (((s : ℝ) + 1) ^ (1 / 10 : ℝ)) := by ring
  rw [hfuneq]
  calc MeasureTheory.eLpNorm (opMul (mstNuSCls P l P.natDegree χ η k s (hνsml k s))
          (⇑g) (memℓp_finsupp g)
        - opMul (khatZMult P J • arcSymbolLp φ (hpi (2 ^ k) s) E) (⇑g)
            (memℓp_finsupp g)) (ENNReal.ofReal q) MeasureTheory.Measure.count
      ≤ MeasureTheory.eLpNorm (opMul (mstNuSCls P l P.natDegree χ η k s (hνsml k s))
            (⇑g) (memℓp_finsupp g)) (ENNReal.ofReal q) MeasureTheory.Measure.count
        + MeasureTheory.eLpNorm (opMul (khatZMult P J • arcSymbolLp φ (hpi (2 ^ k) s) E)
            (⇑g) (memℓp_finsupp g)) (ENNReal.ofReal q) MeasureTheory.Measure.count :=
        eLpNorm_sub_le (ENNReal.one_le_ofReal.mpr hq.le)
    _ ≤ ENNReal.ofReal ((E.card : ℝ) * K)
            * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal q) MeasureTheory.Measure.count
        + ENNReal.ofReal ((E.card : ℝ) * K)
            * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal q) MeasureTheory.Measure.count :=
        add_le_add hfirst hsecond
    _ ≤ ENNReal.ofReal ((2 * K * Cc) * Real.exp (((s : ℝ) + 1) ^ (1 / 10 : ℝ)))
          * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal q) MeasureTheory.Measure.count := by
        have hc1 : (0 : ℝ) ≤ (E.card : ℝ) * K := by positivity
        calc ENNReal.ofReal ((E.card : ℝ) * K)
              * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal q) MeasureTheory.Measure.count
            + ENNReal.ofReal ((E.card : ℝ) * K)
              * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal q) MeasureTheory.Measure.count
            = (ENNReal.ofReal ((E.card : ℝ) * K) + ENNReal.ofReal ((E.card : ℝ) * K))
              * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal q) MeasureTheory.Measure.count := by
              ring
          _ = ENNReal.ofReal ((E.card : ℝ) * K + (E.card : ℝ) * K)
              * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal q) MeasureTheory.Measure.count := by
              rw [ENNReal.ofReal_add hc1 hc1]
          _ ≤ ENNReal.ofReal ((2 * K * Cc) * Real.exp (((s : ℝ) + 1) ^ (1 / 10 : ℝ)))
              * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal q) MeasureTheory.Measure.count :=
              mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hreal) bot_le

/-- For every `B > 0` and all large `s`, `(s+1)^{1/10} ≤ B √(s+1)`. -/
lemma rpow_ten_add_one_le_sqrt_mul (B : ℝ) (hB : 0 < B) :
    ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s →
      ((s : ℝ) + 1) ^ (1 / 10 : ℝ) ≤ B * Real.sqrt ((s : ℝ) + 1) := by
  refine ⟨⌈B ^ (-(5 / 2) : ℝ)⌉₊, fun s hs => ?_⟩
  have hx : 0 < (s : ℝ) + 1 := by positivity
  have hBs : B ^ (-(5 / 2) : ℝ) ≤ (s : ℝ) + 1 := by
    refine le_trans (Nat.le_ceil _) ?_
    have h1 : (⌈B ^ (-(5 / 2) : ℝ)⌉₊ : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
    linarith
  have hpow : (B ^ (-(5 / 2) : ℝ)) ^ (2 / 5 : ℝ) ≤ ((s : ℝ) + 1) ^ (2 / 5 : ℝ) :=
    Real.rpow_le_rpow (Real.rpow_nonneg hB.le _) hBs (by norm_num)
  have hpoweq : (B ^ (-(5 / 2) : ℝ)) ^ (2 / 5 : ℝ) = B⁻¹ := by
    rw [← Real.rpow_mul hB.le]
    rw [show (-(5 / 2 : ℝ)) * (2 / 5) = -1 by norm_num, Real.rpow_neg_one]
  have hBinv : B⁻¹ ≤ ((s : ℝ) + 1) ^ (2 / 5 : ℝ) := hpoweq ▸ hpow
  have hone : (1 : ℝ) ≤ B * ((s : ℝ) + 1) ^ (2 / 5 : ℝ) := by
    have := mul_le_mul_of_nonneg_left hBinv hB.le
    rwa [mul_inv_cancel₀ hB.ne'] at this
  have hinv : ((s : ℝ) + 1) ^ (-(2 / 5) : ℝ) ≤ B := by
    rw [Real.rpow_neg hx.le, inv_le_iff_one_le_mul₀ (Real.rpow_pos_of_pos hx _)]
    exact hone
  calc ((s : ℝ) + 1) ^ (1 / 10 : ℝ)
      = ((s : ℝ) + 1) ^ (-(2 / 5) : ℝ) * ((s : ℝ) + 1) ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_add hx]; norm_num
    _ = ((s : ℝ) + 1) ^ (-(2 / 5) : ℝ) * Real.sqrt ((s : ℝ) + 1) := by rw [Real.sqrt_eq_rpow]
    _ ≤ B * Real.sqrt ((s : ℝ) + 1) := mul_le_mul_of_nonneg_right hinv (Real.sqrt_nonneg _)

/-- **The interpolation arithmetic of the freezing estimate.**  With `1 < r₀ < r < 2`, `θ` the
Riesz–Thorin exponent `(1/r₀ − 1/r)/(1/r₀ − 1/2)` and `1 ≤ A`, `0 < B`, the subexponential loss
`exp((s+1)^{1/10})` of the trivial `ℓ^{r₀}` bound and the exponential gain `exp(−√(s+1)/2)` of the
`ℓ²` bound combine into a single exponential gain `exp(−c√(s+1))`. -/
lemma mstFreeze_arith {r r₀ : ℝ} (hr : 1 < r) (hr2 : r < 2) (hr₀ : 1 < r₀) (hr₀r : r₀ < r)
    {A B : ℝ} (hA : 1 ≤ A) (hB : 0 < B) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s →
      (A * Real.exp (((s : ℝ) + 1) ^ (1 / 10 : ℝ)))
          ^ (1 - (1 / r₀ - 1 / r) / (1 / r₀ - 1 / 2))
        * (B * Real.exp (-(Real.sqrt ((s : ℝ) + 1) / 2)))
          ^ ((1 / r₀ - 1 / r) / (1 / r₀ - 1 / 2))
      ≤ C * Real.exp (-(c * Real.sqrt ((s : ℝ) + 1))) := by
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  have hr₀0 : 0 < r₀ := lt_trans zero_lt_one hr₀
  have hnum : 0 < 1 / r₀ - 1 / r := by
    have h : 1 / r < 1 / r₀ := one_div_lt_one_div_of_lt hr₀0 hr₀r
    linarith
  have hden : 0 < 1 / r₀ - 1 / 2 := by
    have h : (1 : ℝ) / 2 < 1 / r := one_div_lt_one_div_of_lt hr0 hr2
    linarith
  set θ : ℝ := (1 / r₀ - 1 / r) / (1 / r₀ - 1 / 2) with hθdef
  have hθ0 : 0 < θ := by rw [hθdef]; exact div_pos hnum hden
  have hθ1 : θ < 1 := by
    rw [hθdef, div_lt_one hden]
    have h : (1 : ℝ) / 2 < 1 / r := one_div_lt_one_div_of_lt hr0 hr2
    linarith
  have h1θ : 0 < 1 - θ := by linarith
  obtain ⟨s₀, hs₀⟩ := rpow_ten_add_one_le_sqrt_mul (θ / (4 * (1 - θ))) (by positivity)
  refine ⟨A * max (B ^ θ) 1, θ / 4, by positivity, by positivity, s₀, fun s hs => ?_⟩
  have hA0 : 0 ≤ A := le_trans zero_le_one hA
  have hu : 0 ≤ ((s : ℝ) + 1) ^ (1 / 10 : ℝ) := Real.rpow_nonneg (by positivity) _
  have hAθ : A ^ (1 - θ) ≤ A := Real.rpow_le_self_of_one_le hA (by linarith)
  have hBθ : B ^ θ ≤ max (B ^ θ) 1 := le_max_left _ _
  have huθ : ((s : ℝ) + 1) ^ (1 / 10 : ℝ) * (1 - θ) ≤ θ / 4 * Real.sqrt ((s : ℝ) + 1) := by
    have h := mul_le_mul_of_nonneg_right (hs₀ s hs) h1θ.le
    calc ((s : ℝ) + 1) ^ (1 / 10 : ℝ) * (1 - θ)
        ≤ ((θ / (4 * (1 - θ))) * Real.sqrt ((s : ℝ) + 1)) * (1 - θ) := h
      _ = θ / 4 * Real.sqrt ((s : ℝ) + 1) := by
          field_simp
  have hexpθ : Real.exp (((s : ℝ) + 1) ^ (1 / 10 : ℝ) * (1 - θ))
      ≤ Real.exp (θ / 4 * Real.sqrt ((s : ℝ) + 1)) := Real.exp_le_exp.mpr huθ
  have hLHS : (A * Real.exp (((s : ℝ) + 1) ^ (1 / 10 : ℝ)))
        ^ (1 - θ)
      * (B * Real.exp (-(Real.sqrt ((s : ℝ) + 1) / 2))) ^ θ
      = (A ^ (1 - θ) * B ^ θ) *
        (Real.exp (((s : ℝ) + 1) ^ (1 / 10 : ℝ) * (1 - θ))
          * Real.exp ((-(Real.sqrt ((s : ℝ) + 1) / 2)) * θ)) := by
    rw [Real.mul_rpow hA0 (Real.exp_nonneg _), Real.mul_rpow hB.le (Real.exp_nonneg _),
      (Real.exp_mul (((s : ℝ) + 1) ^ (1 / 10 : ℝ)) (1 - θ)).symm,
      (Real.exp_mul (-(Real.sqrt ((s : ℝ) + 1) / 2)) θ).symm]
    ring
  have hstep1 : (A ^ (1 - θ) * B ^ θ) *
        (Real.exp (((s : ℝ) + 1) ^ (1 / 10 : ℝ) * (1 - θ))
          * Real.exp ((-(Real.sqrt ((s : ℝ) + 1) / 2)) * θ))
      ≤ (A * max (B ^ θ) 1) *
        (Real.exp (θ / 4 * Real.sqrt ((s : ℝ) + 1))
          * Real.exp ((-(Real.sqrt ((s : ℝ) + 1) / 2)) * θ)) :=
    mul_le_mul (mul_le_mul hAθ hBθ (Real.rpow_nonneg hB.le θ) hA0)
      (mul_le_mul hexpθ le_rfl (Real.exp_nonneg _) (Real.exp_nonneg _))
      (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))
      (mul_nonneg hA0 (le_trans (Real.rpow_nonneg hB.le θ) hBθ))
  have hstep2 : Real.exp (θ / 4 * Real.sqrt ((s : ℝ) + 1))
        * Real.exp ((-(Real.sqrt ((s : ℝ) + 1) / 2)) * θ)
      ≤ Real.exp (-(θ / 4 * Real.sqrt ((s : ℝ) + 1))) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (le_of_eq (by ring))
  calc (A * Real.exp (((s : ℝ) + 1) ^ (1 / 10 : ℝ))) ^ (1 - θ)
        * (B * Real.exp (-(Real.sqrt ((s : ℝ) + 1) / 2))) ^ θ
      = (A ^ (1 - θ) * B ^ θ) *
        (Real.exp (((s : ℝ) + 1) ^ (1 / 10 : ℝ) * (1 - θ))
          * Real.exp ((-(Real.sqrt ((s : ℝ) + 1) / 2)) * θ)) := hLHS
    _ ≤ (A * max (B ^ θ) 1) *
        (Real.exp (θ / 4 * Real.sqrt ((s : ℝ) + 1))
          * Real.exp ((-(Real.sqrt ((s : ℝ) + 1) / 2)) * θ)) := hstep1
    _ ≤ (A * max (B ^ θ) 1) * Real.exp (-(θ / 4 * Real.sqrt ((s : ℝ) + 1))) :=
        mul_le_mul_of_nonneg_left hstep2 (by positivity)


/-- MST Theorem 7, step (i) (Mirek–Stein–Trojan, arXiv:1512.07518, §4.4, eqs. (95)–(101)): the *freezing* error in `ℓ^r`, uniformly over the scale index `k` and for large levels `s`.  The weighted level symbol `ν^s_{2^k}` (`mstNuSCls`, the Gauss weights `star (mstG P β)` attached to the arcs `β ∈ 𝒰(s+1) ∖ 𝒰(s)`) is compared with the *frozen* weight-free model `m_J · Π^s_{2^k}`: the β-dependent complete sum is replaced by the global Weyl kernel `m_J = mstWeyl P J` at the level scale `J = ⌊exp √(s+1)⌋` (whose `L^∞`-class is `khatZMult P J`, `khatZMult_coeFn_star_mstWeyl`), and `Π^s_{2^k}` is the unweighted annulus symbol `arcSymbolLp (star (Φ_{2^k}) · η_s) (𝒰(s+1) ∖ 𝒰(s))` (`hpi` supplies its a.e.-boundedness — it is `mstPiCls`).  For every `1 < r < 2` the difference is an `ℓ^r`-operator of norm `≲ exp(-c√(s+1))`.

Route.  (1) *Pointwise*: on the support of the level bump around `β ∈ 𝒰(s+1)` one has `‖mstWeyl P J ξ - mstG P β‖ ≤ C exp(-√(s+1)/2)` (`mst_lvl_approx_pointwise`, proved); hence a.e. `‖ν^s_{2^k}(ξ) - μ(ξ)Π^s_{2^k}(ξ)‖ ≤ C exp(-√(s+1)/2) · Σ_β ‖η_s(ξ-β)‖ ≤ C' exp(-√(s+1)/2)` using `‖mstG‖ ≤ 1` (`mstG_norm_le_one`), `‖mstProf‖ ≤ 1` (`norm_polyProfile_le_one`) and the arc-sum bound `mstEta_arcSum_le`.  (2) *`ℓ²`*: Plancherel, `eLpNorm_two_opMul_le`, with that pointwise bound.  (3) *Trivial `ℓ^{r₀}`* (`1 < r₀ < r`, e.g. `r₀ = (1+r)/2`): split `ν - μ•Π = (ν) - (μ•Π)`: the first term is a *weighted* arc symbol with weights `star (mstG P β)` (modulus `≤ 1`) and `φ = star (mstProf P (2^k) ·) · mstEta d χ η s`, whose summable coefficient kernel is bounded by `mstProfBumpS_coeff` uniformly in `N = 2^k ≥ 1` and `s` (use the companion request `Maximal/arcSymbolW_lp_bound_of_coeff`, the weighted companion of `KPWW/opArc_lp_bound_of_coeff`; note `ν^s_{2^k}`'s class *is* a weighted `arcSymbolWLp` with `θ = id`, `w = star ∘ mstG P`, `Es = 𝒰(s+1) ∖ 𝒰(s)`, by `mstNuS`'s definition as `mstModelFn`); the second is `opMul (khatZMult P J) ∘ (unweighted arc operator)`, bounded by the same `K · #annulus` through `opArc_lp_bound_of_coeff` (the density kernel `khatZMult P J` is an average of `J` shifts, hence an `ℓ^{r₀}` contraction — `discAvgZC_contraction`, `opMul_khatZMult_eq_discAvgZC`, `opMul_mul`).  (4) *Interpolation*: `opMulFinsuppLM_interp` between the `ℓ^{r₀}` and `ℓ²` endpoints, and the arithmetic `(e^{O(s^{1/10})})^{1-θ}(e^{-√(s+1)/2})^{θ} ≤ e^{-c√(s+1)}` for large `s` (the loss is subexponential against the `√s` gain; explicit thresholds are available in `Maximal/mst_lvl_approx_pointwise`, e.g. `rpow_ten_add_one_le_mul`, `sqrt_add_one_le_mul`).  Note that no Gauss *decay* hypothesis is needed: `‖mstG P β‖ ≤ 1` suffices for the trivial bound. -/
theorem mst_lrs_freeze_err
    (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (hc : 0 < P.leadingCoeff)
    (l : ℕ) (hl : 1 ≤ l) {χ : ℝ} (hχ0 : 0 < χ) (hχ1 : χ < 1 / 10)
    (η : ℝ → ℂ) (M : ℝ) (hM : 0 < M) (hηc : ContDiff ℝ 2 η)
    (hηbd : ∀ x : ℝ, ‖η x‖ ≤ M)
    (hder1 : ∀ x : ℝ, |x| * ‖deriv η x‖ ≤ M)
    (hder2 : ∀ x : ℝ, |x| ^ 2 * ‖iteratedDeriv 2 η x‖ ≤ M)
    (hηsup : ∀ x : ℝ, 1 / 2 ≤ |x| → η x = 0)
    (hpi : ∀ (N s : ℕ), MeasureTheory.MemLp
      (fun ζ : Work.BourgainPlan.IonescuWainger.Circle =>
        star (Work.BourgainPlan.Maximal.mstProf P N ζ) *
          Work.BourgainPlan.Maximal.mstEta P.natDegree χ η s ζ) ⊤
      (AddCircle.haarAddCircle (T := 1)))
    (hνsml : ∀ n s : ℕ, MeasureTheory.MemLp
      (Work.BourgainPlan.Maximal.mstNuS P l P.natDegree χ η n s) ⊤
      (AddCircle.haarAddCircle (T := 1)))
    {r : ℝ} (hr : 1 < r) (hr2 : r < 2) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s → ∀ k : ℕ, ∀ g : ℤ →₀ ℂ,
      MeasureTheory.eLpNorm (fun m : ℤ =>
          Work.BourgainPlan.IonescuWainger.opMul
            (Work.BourgainPlan.Maximal.mstNuSCls P l P.natDegree χ η k s (hνsml k s) -
              Work.BourgainPlan.Maximal.khatZMult P (⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊) •
                Work.BourgainPlan.IonescuWainger.arcSymbolLp
                  (fun ζ : Work.BourgainPlan.IonescuWainger.Circle =>
                    star (Work.BourgainPlan.Maximal.mstProf P (2 ^ k) ζ) *
                      Work.BourgainPlan.Maximal.mstEta P.natDegree χ η s ζ)
                  (hpi (2 ^ k) s)
                  (Work.BourgainPlan.Maximal.mstLevel l (s + 1) \
                    Work.BourgainPlan.Maximal.mstLevel l s))
            (⇑g) (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g) m)
        (ENNReal.ofReal r) (MeasureTheory.Measure.count)
        ≤ ENNReal.ofReal (C * Real.exp (-(c * Real.sqrt ((s : ℝ) + 1))))
          * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal r) MeasureTheory.Measure.count := by
  classical
  set r₀ : ℝ := (1 + r) / 2 with hr₀def
  have hr₀1 : 1 < r₀ := by rw [hr₀def]; linarith
  have hr₀r : r₀ < r := by rw [hr₀def]; linarith
  obtain ⟨Cl2, hCl2pos, sl2, hl2⟩ := mstFreeze_l2 P hd hc l hl hχ0 hχ1 η hηc hηsup hpi hνsml
  obtain ⟨Ctr, hCtrpos, str, htr⟩ :=
    mstFreeze_triv P hd hc l hl hχ0 hχ1 η M hM hηc hηbd hder1 hder2 hηsup hpi hνsml
      (q := r₀) hr₀1
  obtain ⟨Ca, ca, hCapos, hcapos, sa, harith⟩ :=
    mstFreeze_arith (r := r) (r₀ := r₀) hr hr2 hr₀1 hr₀r
      (A := max Ctr 1) (B := max Cl2 1) (le_max_right _ _)
      (lt_of_lt_of_le zero_lt_one (le_max_right _ _))
  refine ⟨Ca, ca, hCapos, hcapos, max (max sl2 str) (max sa 1), fun s hs k g => ?_⟩
  have hs_l2 : sl2 ≤ s := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hs)
  have hs_tr : str ≤ s := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hs)
  have hs_sa : sa ≤ s := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hs)
  set A : ℝ := max Ctr 1 * Real.exp (((s : ℝ) + 1) ^ (1 / 10 : ℝ)) with hAdef
  set B : ℝ := max Cl2 1 * Real.exp (-(Real.sqrt ((s : ℝ) + 1) / 2)) with hBdef
  set θ : ℝ := (1 / r₀ - 1 / r) / (1 / r₀ - 1 / 2) with hθdef
  set Φ : Lp ℂ ⊤ haarT := mstFreezeCls P l χ η k s hpi hνsml with hΦdef
  have hApos : 0 < A := by rw [hAdef]; positivity
  have hBpos : 0 < B := by rw [hBdef]; positivity
  have hr₀bound : ∀ f : ℤ →₀ ℂ,
      MeasureTheory.eLpNorm (opMulFinsuppLM Φ f) (ENNReal.ofReal r₀) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal A
          * MeasureTheory.eLpNorm (⇑f) (ENNReal.ofReal r₀) MeasureTheory.Measure.count := by
    intro f
    have h1 : MeasureTheory.eLpNorm (opMulFinsuppLM Φ f) (ENNReal.ofReal r₀)
          MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (Ctr * Real.exp (((s : ℝ) + 1) ^ (1 / 10 : ℝ)))
          * MeasureTheory.eLpNorm (⇑f) (ENNReal.ofReal r₀) MeasureTheory.Measure.count := by
      simpa only [hΦdef, opMulFinsuppLM_apply] using htr s hs_tr k f
    have h2 : ENNReal.ofReal (Ctr * Real.exp (((s : ℝ) + 1) ^ (1 / 10 : ℝ)))
        ≤ ENNReal.ofReal A :=
      ENNReal.ofReal_le_ofReal (by
        rw [hAdef]
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_nonneg _))
    exact h1.trans (mul_le_mul' h2 le_rfl)
  have h2bound : ∀ f : ℤ →₀ ℂ,
      MeasureTheory.eLpNorm (opMulFinsuppLM Φ f) (ENNReal.ofReal 2) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal B
          * MeasureTheory.eLpNorm (⇑f) (ENNReal.ofReal 2) MeasureTheory.Measure.count := by
    intro f
    have h1 : MeasureTheory.eLpNorm (opMulFinsuppLM Φ f) (ENNReal.ofReal 2)
          MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (Cl2 * Real.exp (-(Real.sqrt ((s : ℝ) + 1) / 2)))
          * MeasureTheory.eLpNorm (⇑f) (ENNReal.ofReal 2) MeasureTheory.Measure.count := by
      simpa only [hΦdef, opMulFinsuppLM_apply] using hl2 s hs_l2 k f
    have h2 : ENNReal.ofReal (Cl2 * Real.exp (-(Real.sqrt ((s : ℝ) + 1) / 2)))
        ≤ ENNReal.ofReal B :=
      ENNReal.ofReal_le_ofReal (by
        rw [hBdef]
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_nonneg _))
    exact h1.trans (mul_le_mul' h2 le_rfl)
  have harith' : A ^ (1 - θ) * B ^ θ ≤ Ca * Real.exp (-(ca * Real.sqrt ((s : ℝ) + 1))) := by
    rw [hAdef, hBdef, hθdef]
    exact harith s hs_sa
  have hkey := opMulFinsuppLM_interp Φ (r := r₀) (p := r) (A := A) (B := B)
    hr₀1 hr₀r hr2 hApos hBpos hr₀bound h2bound g
  show MeasureTheory.eLpNorm (opMulFinsuppLM Φ g) (ENNReal.ofReal r) MeasureTheory.Measure.count
    ≤ ENNReal.ofReal (Ca * Real.exp (-(ca * Real.sqrt ((s : ℝ) + 1))))
      * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal r) MeasureTheory.Measure.count
  exact hkey.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal harith') le_rfl)


end

end Work.Maximal
