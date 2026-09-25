import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_major_defs
import Submission.Work.BourgainPlan.Maximal.mst_theta_defs
import Submission.Work.BourgainPlan.Maximal.iwRangeBound_of_endpoint
import Submission.Work.BourgainPlan.Maximal.mst_lvl_approx_pointwise
import Submission.Work.BourgainPlan.Maximal.mstEta_arcSum_le
import Submission.Work.BourgainPlan.Maximal.mstU_annulus_tiling
import Submission.Work.BourgainPlan.Maximal.mst_level_lr_lt
import Submission.Work.BourgainPlan.Maximal.rmELpNormSupLe
import Submission.Work.BourgainPlan.IonescuWainger.khintchine_hilbert
-- additional imports used by the proof below
import Submission.Work.BourgainPlan.Maximal.mst_lvl_defs
import Submission.Work.BourgainPlan.Maximal.memLp_mst_symbols
import Submission.Work.BourgainPlan.Maximal.mikhlin_conditions_scaled_bump
import Submission.Work.BourgainPlan.Maximal.mstProfBumpS_coeff
import Submission.Work.Maximal.arcSymbolW_lp_bound_of_coeff
import Submission.Work.Maximal.mst_lrs_base
import Submission.Work.Maximal.mst_lrs_freeze_err
import Submission.Work.Maximal.mst_lrs_frozen_sup
import Submission.Work.Maximal.kappa_exp_le_inv

/-!
# The small-scale half of the level `ℓʳ` estimate (MST Theorem 7)

`Work.Maximal.mst_level_lr_small` is the estimate for the *small* range of scales
`k ≤ 2^{κ_s}` (`κ_s = mstKappa P s`) of the level-`s` major-arc model `ν^s_{2^k}` of
Mirek–Stein–Trojan, arXiv:1512.07518, Theorem 7: the maximal function is `ℓʳ`-bounded,
`1 < r < 2`, with constant `C (s+1) log(s+2)`, uniformly in `s` and uniformly in the finitely
supported input.

The proof follows MST §4.4:

* **freezing** (`mst_lrs_freeze_err`): the β-dependent Gauss weight `G(β)` of the level symbol is
  replaced by the global Weyl kernel `m_J` (`J = ⌊exp √(s+1)⌋`), at the cost of `≲ e^{-c√(s+1)}`
  per scale (summed over the `2^{κ_s}+1 ≤ e^{o(√s)}` scales, this is absorbed into the constant);
* **pulling the frozen weight out of the supremum** (`mst_lrs_frozen_sup`), since `m_J` is the
  Fourier transform of an average of translations;
* **Rademacher–Menshov** on the weight-free family (`mst_lrs_frozen_bound`, proved here from
  `rmELpNormSupLe` and the level bound `mst_lvl_level_bound`), with the base term supplied by
  `mst_lrs_base`;
* the finitely many *small* levels `s < s₀`, where the freezing machinery is unavailable, are
  estimated by the trivial coefficient-kernel bound `mstNuS_triv_lp_aux` and absorbed into the
  constant (via `kappa_exp_le_inv`).
-/

namespace Work.Maximal

open MeasureTheory Finset
open scoped BigOperators ENNReal
open Work.BourgainPlan.IonescuWainger
open Work.BourgainPlan.Maximal

noncomputable section

set_option maxHeartbeats 4000000

local notation "haarT" => (AddCircle.haarAddCircle (T := 1))
local notation "Circ" => Work.BourgainPlan.IonescuWainger.Circle

/-- The `ContDiff` data of the level-`0` bump's lift, from the Mikhlin data of `η`. -/
private lemma hcd0_of (η : ℝ → ℂ) (M : ℝ) (hM : 0 ≤ M) (hηc : ContDiff ℝ 2 η)
    (hηbd : ∀ x : ℝ, ‖η x‖ ≤ M) (hder1 : ∀ x : ℝ, |x| * ‖deriv η x‖ ≤ M)
    (hder2 : ∀ x : ℝ, |x| ^ 2 * ‖iteratedDeriv 2 η x‖ ≤ M)
    (hηsup : ∀ x : ℝ, 1 / 2 ≤ |x| → η x = 0) (d : ℕ) (χ : ℝ) (hχ : χ + 1 ≤ (d : ℝ)) :
    ContDiff ℝ 2 (Work.BourgainPlan.Thm52.circleLift (mstEta d χ η 0)) := by
  have h1 : (1 : ℝ) ≤ |(2 : ℝ) ^ (((0 : ℕ) : ℝ) * ((d : ℝ) - χ))| := by
    rw [Nat.cast_zero, zero_mul, Real.rpow_zero, abs_one]
  have h := mikhlin_conditions_scaled_bump (η := η) (M := M)
    (c := (2 : ℝ) ^ (((0 : ℕ) : ℝ) * ((d : ℝ) - χ))) hM h1 hηc hηbd hder1 hder2 hηsup
  have hEq : mstEta d χ η 0
      = fun ξ : Work.BourgainPlan.IonescuWainger.Circle =>
          η ((2 : ℝ) ^ (((0 : ℕ) : ℝ) * ((d : ℝ) - χ)) * iwRep ξ) := by
    funext ξ; rw [mstEta_apply]
  rw [hEq]
  exact h.1

/-- **The trivial `ℓʳ` bound for the level model** `ν^s_{2^k}`: a summable coefficient kernel
gives `‖opMul (mstNuSCls … k s) g‖_{ℓʳ} ≤ #annulus · K · ‖g‖_{ℓʳ}` for every `r ≥ 1`, uniformly in
the scale `k` and in the level `s`.  Same statement as the (in-flight) `mstNuS_triv_lp` of
`mst_lvl_defs.lean`, proved here from `mstProfBumpS_coeff` (the non-diagonal coefficient bound of the
profile-times-bump), the weighted Fourier-coefficient computation for `mstNuS`, and the weighted
Young bound `arcSymbolW_lp_bound_of_coeff`. -/
theorem mstNuS_triv_lp_aux (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (hc : 0 < P.leadingCoeff)
    (l : ℕ) (hl : 1 ≤ l) {χ : ℝ} (hχ0 : 0 < χ) (hχ1 : χ < 1 / 10)
    (η : ℝ → ℂ) (M : ℝ) (hM : 0 < M) (hηc : ContDiff ℝ 2 η)
    (hηbd : ∀ x : ℝ, ‖η x‖ ≤ M) (hη0 : ∀ x : ℝ, 1 / 2 ≤ |x| → η x = 0)
    (hder1 : ∀ x : ℝ, |x| * ‖deriv η x‖ ≤ M)
    (hder2 : ∀ x : ℝ, |x| ^ 2 * ‖iteratedDeriv 2 η x‖ ≤ M)
    (hML : ∀ n s : ℕ, MemLp (mstNuS P l P.natDegree χ η n s) ⊤ haarT) :
    ∃ K : ℝ, 0 < K ∧ ∀ (s : ℕ) (k : ℕ) (g : ℤ →₀ ℂ) {r : ℝ}, 1 ≤ r →
      MeasureTheory.eLpNorm (opMulFinsuppLM
          (mstNuSCls P l P.natDegree χ η k s (hML k s)) g)
          (ENNReal.ofReal r) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal ((((mstLevel l (s + 1) \ mstLevel l s).card : ℝ)) * K)
          * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal r) MeasureTheory.Measure.count := by
  have hχd : χ + 1 ≤ (P.natDegree : ℝ) := by
    have h2 : (2 : ℝ) ≤ (P.natDegree : ℝ) := by exact_mod_cast hd
    linarith
  have hcd0 := hcd0_of η M hM.le hηc hηbd hder1 hder2 hη0 P.natDegree χ hχd
  have hη0' : ∀ x : ℝ, 1 / 2 < |x| → η x = 0 := fun x hx => hη0 x (le_of_lt hx)
  have hηml : ∀ s : ℕ, MemLp (mstEta P.natDegree χ η s) ⊤ haarT := fun s =>
    (memLp_mst_symbols (P := (0 : Polynomial ℤ)) 1
      ((2 : ℝ) ^ ((s : ℝ) * ((P.natDegree : ℝ) - χ))) η hηc.continuous).2.2
  obtain ⟨K, hKpos, hK⟩ := mstProfBumpS_coeff P P.natDegree χ η M hM.le hχd hηbd hη0' hcd0
  refine ⟨K, hKpos, fun s k g r hr => ?_⟩
  set φ : Work.BourgainPlan.IonescuWainger.Circle → ℂ :=
    fun ξ => star (mstProf P (2 ^ k) ξ) * mstEta P.natDegree χ η s ξ with hφdef
  have hφ : MemLp φ ⊤ haarT := by
    rw [hφdef]
    exact memLp_mstPiBump P P.natDegree χ η (2 ^ k) s (hηml s)
  have hcoe := hK (2 ^ k) s (Nat.one_le_pow k 2 (by norm_num))
  obtain ⟨hsum, hsumle⟩ := hcoe
  have hsum' : Summable (fun n : ℤ => ‖∫ ξ, φ ξ * star (fourier n ξ) ∂haarT‖) := hsum
  have hsumle' : (∑' n : ℤ, ‖∫ ξ, φ ξ * star (fourier n ξ) ∂haarT‖) ≤ K := hsumle
  have hw : ∀ β ∈ mstLevel l (s + 1) \ mstLevel l s, ‖star (mstG P β)‖ ≤ (1 : ℝ) := by
    intro β _
    rw [norm_star]
    exact mstG_norm_le_one P β
  have hbound := arcSymbolW_lp_bound_of_coeff (p := r) hr (hφ := hφ)
    (c := fun n : ℤ => ∫ ξ, φ ξ * star (fourier n ξ) ∂haarT) hsum' (fun n => rfl)
    (W := 1) (K := K) (by norm_num) hsumle'
    (fun β : Work.BourgainPlan.IonescuWainger.Circle => star (mstG P β))
    (mstLevel l (s + 1) \ mstLevel l s) hw g
  have hcls : mstNuSCls P l P.natDegree χ η k s (hML k s)
      = arcSymbolWLp (fun β : Work.BourgainPlan.IonescuWainger.Circle => β)
          (fun β => star (mstG P β)) (mstLevel l (s + 1) \ mstLevel l s) φ hφ := by
    refine Lp.ext ?_
    filter_upwards [mstNuSCls_coeFn P l P.natDegree χ η k s (hML k s),
      arcSymbolWLp_coeFn (fun β : Work.BourgainPlan.IonescuWainger.Circle => β)
        (fun β => star (mstG P β)) (mstLevel l (s + 1) \ mstLevel l s) φ hφ,
      hφ.coeFn_toLp] with ξ h1 h2 h3
    rw [h1, h2, mstNuS_apply, arcSymbolW_apply]
  rw [opMulFinsuppLM_apply, hcls]
  simpa only [one_mul] using hbound



/-- **The frozen (weight-free) maximal bound of the level-`s` model on the small scales**, MST
Theorem 7 steps (ii)–(iv): the Rademacher–Menshov reduction of the sup over `k ≤ 2^{κ_s}` into the
`κ_s + 1` block-square-function levels, each bounded by `mst_lvl_level_bound`, plus the base term
(passed in as `hbase`). -/
theorem mst_lrs_frozen_bound
    (hΘ : MSTThetaBound) (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (hc : 0 < P.leadingCoeff)
    (l : ℕ) (hl : 1 ≤ l) {χ : ℝ} (hχ0 : 0 < χ) (hχ1 : χ < 1 / 10)
    (η : ℝ → ℂ) (M : ℝ) (hM : 0 < M) (hηc : ContDiff ℝ 2 η)
    (hηbd : ∀ x : ℝ, ‖η x‖ ≤ M) (hη0 : ∀ x : ℝ, 1 / 2 < |x| → η x = 0)
    (hder1 : ∀ x : ℝ, |x| * ‖deriv η x‖ ≤ M)
    (hder2 : ∀ x : ℝ, |x| ^ 2 * ‖iteratedDeriv 2 η x‖ ≤ M)
    (hηml : ∀ s : ℕ, MemLp (mstEta P.natDegree χ η s) ⊤ haarT)
    {r : ℝ} (hr : 1 < r) (hr2 : r < 2)
    {Cbase : ℝ} (hCbase : 0 < Cbase)
    (hbase : ∀ (s : ℕ) (g : ℤ →₀ ℂ),
      MeasureTheory.eLpNorm (fun m : ℤ => ENNReal.ofReal
            ‖opMul (mstPiCls P l P.natDegree χ η s (hηml s) (2 ^ 0)) (⇑g)
              (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g) m‖)
          (ENNReal.ofReal r) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (Cbase * (((s : ℝ) + 1) * Real.log ((s : ℝ) + 2)))
          * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal r) MeasureTheory.Measure.count) :
    ∃ C : ℝ, 0 < C ∧ ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s → ∀ g : ℤ →₀ ℂ,
      MeasureTheory.eLpNorm (fun m : ℤ => (⨆ k ∈ Finset.range (2 ^ (mstKappa P s) + 1),
          ‖opMul (mstPiCls P l P.natDegree χ η s (hηml s) (2 ^ k)) (⇑g)
            (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g) m‖ₑ))
          (ENNReal.ofReal r) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C * (((s : ℝ) + 1) * Real.log ((s : ℝ) + 2)))
          * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal r) MeasureTheory.Measure.count := by
  -- the Ionescu–Wainger endpoint exponent `r₀` for the range `1 < r < 2`
  obtain ⟨r₀, hr₀2, hr₀r, hr₀lo⟩ : ∃ r₀ : ℕ, 2 ≤ r₀ ∧ r ≤ 2 * (r₀ : ℝ) ∧
      (2 * (r₀ : ℝ)) / (2 * (r₀ : ℝ) - 1) ≤ r := by
    refine ⟨max 2 ⌈r / (2 * (r - 1))⌉₊, le_max_left _ _, ?_, ?_⟩
    · have h2R : (2 : ℝ) ≤ ((max 2 ⌈r / (2 * (r - 1))⌉₊ : ℕ) : ℝ) := by
        exact_mod_cast le_max_left (2 : ℕ) _
      linarith
    · have hR2 : (2 : ℝ) ≤ ((max 2 ⌈r / (2 * (r - 1))⌉₊ : ℕ) : ℝ) := by
        exact_mod_cast le_max_left (2 : ℕ) _
      have hR : r / (2 * (r - 1)) ≤ ((max 2 ⌈r / (2 * (r - 1))⌉₊ : ℕ) : ℝ) :=
        le_trans (Nat.le_ceil _) (by exact_mod_cast le_max_right (2 : ℕ) _)
      have hr1 : 0 < r - 1 := by linarith
      have hden : 0 < 2 * ((max 2 ⌈r / (2 * (r - 1))⌉₊ : ℕ) : ℝ) - 1 := by linarith
      rw [div_le_iff₀ hden]
      have hkey := mul_le_mul_of_nonneg_left hR (by linarith : (0 : ℝ) ≤ 2 * (r - 1))
      have hval : 2 * (r - 1) * (r / (2 * (r - 1))) = r := by field_simp
      rw [hval] at hkey
      nlinarith [hkey]
  obtain ⟨Clvl, hClvlpos, slvl, hlvl⟩ := mst_lvl_level_bound hΘ P hd hc l hl hχ0 hχ1 η M hM hηc
    hηbd hη0 hder1 hder2 (p := r) hr r₀ hr₀2 hr₀r hr₀lo hηml
  obtain ⟨Sκ, hSκ⟩ := mstKappa_add_one_le P (by omega : 1 ≤ P.natDegree)
  refine ⟨Cbase + 2 * Clvl, by positivity, max slvl (max Sκ 1), fun s hs g => ?_⟩
  have hslvl : slvl ≤ s := le_trans (le_max_left _ _) hs
  have hSκs : Sκ ≤ s := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hs
  have hlogpos : (0 : ℝ) < Real.log ((s : ℝ) + 2) := Real.log_pos (by linarith)
  have hsr : (1 : ℝ) ≤ (s : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) s]
  have hκ : ((mstKappa P s + 1 : ℕ) : ℝ≥0∞) ≤ ((s + 1 : ℕ) : ℝ≥0∞) := by
    exact_mod_cast hSκ s hSκs
  -- Rademacher–Menshov: `sup ≤ |T 0| + 2 Σ_i (level i)`
  have hrm := rmELpNormSupLe (μ := MeasureTheory.Measure.count) (mstKappa P s) (p := r) hr.le
    (fun j (m : ℤ) => ‖opMul (mstPiCls P l P.natDegree χ η s (hηml s) (2 ^ j)) (⇑g)
      (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g) m‖)
    (fun j => (measurable_of_countable _).aemeasurable) (fun j m => norm_nonneg _)
  -- each level is bounded by `mst_lvl_level_bound`
  have hlev : ∀ i ∈ Finset.range (mstKappa P s + 1),
      MeasureTheory.eLpNorm (fun m : ℤ => ENNReal.ofReal (rmLevel (mstKappa P s) i
          (fun j : ℕ => ‖opMul (mstPiCls P l P.natDegree χ η s (hηml s) (2 ^ j)) (⇑g)
            (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g) m‖)))
          (ENNReal.ofReal r) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (Clvl * Real.log ((s : ℝ) + 2))
          * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal r) MeasureTheory.Measure.count := by
    intro i _
    simpa only [opMulFinsuppLM_apply] using hlvl s hslvl i g
  set B : ℝ≥0∞ := MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal r) MeasureTheory.Measure.count
  set A₁ : ℝ := Cbase * (((s : ℝ) + 1) * Real.log ((s : ℝ) + 2)) with hA₁def
  set A₂ : ℝ := 2 * ((s : ℝ) + 1) * (Clvl * Real.log ((s : ℝ) + 2)) with hA₂def
  have hA₁nn : 0 ≤ A₁ := by rw [hA₁def]; positivity
  have hA₂nn : 0 ≤ A₂ := by rw [hA₂def]; positivity
  have hsum : ∑ i ∈ Finset.range (mstKappa P s + 1),
      MeasureTheory.eLpNorm (fun m : ℤ => ENNReal.ofReal (rmLevel (mstKappa P s) i
        (fun j : ℕ => ‖opMul (mstPiCls P l P.natDegree χ η s (hηml s) (2 ^ j)) (⇑g)
          (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g) m‖)))
        (ENNReal.ofReal r) MeasureTheory.Measure.count
      ≤ ENNReal.ofReal ((s : ℝ) + 1)
          * (ENNReal.ofReal (Clvl * Real.log ((s : ℝ) + 2)) * B) := by
    calc ∑ i ∈ Finset.range (mstKappa P s + 1),
          MeasureTheory.eLpNorm (fun m : ℤ => ENNReal.ofReal (rmLevel (mstKappa P s) i
            (fun j : ℕ => ‖opMul (mstPiCls P l P.natDegree χ η s (hηml s) (2 ^ j)) (⇑g)
              (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g) m‖)))
            (ENNReal.ofReal r) MeasureTheory.Measure.count
        ≤ ∑ _i ∈ Finset.range (mstKappa P s + 1),
            (ENNReal.ofReal (Clvl * Real.log ((s : ℝ) + 2)) * B) :=
          Finset.sum_le_sum (fun i hi => by simpa only [B] using hlev i hi)
      _ = ((mstKappa P s + 1 : ℕ) : ℝ≥0∞)
            * (ENNReal.ofReal (Clvl * Real.log ((s : ℝ) + 2)) * B) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ ENNReal.ofReal ((s : ℝ) + 1) * (ENNReal.ofReal (Clvl * Real.log ((s : ℝ) + 2)) * B) := by
          refine mul_le_mul_of_nonneg_right ?_ (zero_le)
          rw [← ENNReal.ofReal_natCast]
          exact ENNReal.ofReal_le_ofReal (by exact_mod_cast hSκ s hSκs)
  have hlev2 : ENNReal.ofReal 2 * ∑ i ∈ Finset.range (mstKappa P s + 1),
      MeasureTheory.eLpNorm (fun m : ℤ => ENNReal.ofReal (rmLevel (mstKappa P s) i
        (fun j : ℕ => ‖opMul (mstPiCls P l P.natDegree χ η s (hηml s) (2 ^ j)) (⇑g)
          (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g) m‖)))
        (ENNReal.ofReal r) MeasureTheory.Measure.count
      ≤ ENNReal.ofReal A₂ * B := by
    refine (mul_le_mul_of_nonneg_left hsum (by positivity : (0 : ℝ≥0∞) ≤ ENNReal.ofReal 2)).trans ?_
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ← mul_assoc,
      ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * ((s : ℝ) + 1)), hA₂def]
  have hgoal : (fun m : ℤ => (⨆ k ∈ Finset.range (2 ^ (mstKappa P s) + 1),
        ENNReal.ofReal ‖opMul (mstPiCls P l P.natDegree χ η s (hηml s) (2 ^ k)) (⇑g)
          (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g) m‖))
      = (fun m : ℤ => (⨆ k ∈ Finset.range (2 ^ (mstKappa P s) + 1),
        ‖opMul (mstPiCls P l P.natDegree χ η s (hηml s) (2 ^ k)) (⇑g)
          (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g) m‖ₑ)) := by
    funext m
    simp only [ofReal_norm]
  rw [← hgoal]
  refine hrm.trans ?_
  refine (add_le_add (by simpa only [hA₁def] using hbase s g) hlev2).trans ?_
  rw [← add_mul, ← ENNReal.ofReal_add hA₁nn hA₂nn]
  refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_)
    (by positivity : (0 : ℝ≥0∞) ≤ B)
  rw [hA₁def, hA₂def]
  have := mul_nonneg (by positivity : (0 : ℝ) ≤ ((s : ℝ) + 1) * Real.log ((s : ℝ) + 2))
    (le_of_lt (by positivity : (0 : ℝ) < 2 * Clvl))
  nlinarith [this, hCbase, hClvlpos, hlogpos, hsr]
/-- The `mstPiCls` class is the `arcSymbolLp` of the profile-times-bump. -/
lemma mstPiCls_eq_arcSymbolLp (P : Polynomial ℤ) (l d : ℕ) (χ : ℝ) (η : ℝ → ℂ) (s N : ℕ)
    (hηml : MemLp (mstEta d χ η s) ⊤ haarT)
    (hpi : MemLp (fun ζ : Circ => star (mstProf P N ζ) * mstEta d χ η s ζ) ⊤ haarT) :
    mstPiCls P l d χ η s hηml N
      = arcSymbolLp (fun ζ : Circ => star (mstProf P N ζ) * mstEta d χ η s ζ) hpi
          (mstLevel l (s + 1) \ mstLevel l s) := by
  unfold mstPiCls
  refine arcSymbolLp_congr ?_ _ _ _
  funext ζ
  simp only [mstPiBump_apply]


/-- The supremum over a finset of the `enorm`s of two pointwise equal families agree. -/
private lemma iSup_norm_congr {ι : Type*} (S : Finset ι) (F G : ι → ℤ → ℂ)
    (h : ∀ i, F i = G i) :
    (fun m : ℤ => ⨆ i ∈ S, ‖F i m‖ₑ) = (fun m : ℤ => ⨆ i ∈ S, ‖G i m‖ₑ) := by
  funext m
  refine iSup_congr (fun i => iSup_congr (fun _ => ?_))
  rw [h i]

theorem mst_level_lr_small (hΘ : Work.BourgainPlan.Maximal.MSTThetaBound)
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
    {r : ℝ} (hr : 1 < r) (hr2 : r < 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℕ, ∀ g : ℤ →₀ ℂ,
      MeasureTheory.eLpNorm (fun m : ℤ => (⨆ k ∈ Finset.range (2 ^ (Work.BourgainPlan.Maximal.mstKappa P s) + 1),
          ‖Work.BourgainPlan.IonescuWainger.opMul
            (Work.BourgainPlan.Maximal.mstNuSCls P l P.natDegree χ η k s (hνsml k s))
            (⇑g) (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g) m‖ₑ))
          (ENNReal.ofReal r) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C * (((s : ℝ) + 1) * Real.log ((s : ℝ) + 2)))
          * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal r) MeasureTheory.Measure.count
          := by
  have hη0 : ∀ x : ℝ, 1 / 2 < |x| → η x = 0 := fun x hx => hηsup x (le_of_lt hx)
  have hηml : ∀ s : ℕ, MemLp (mstEta P.natDegree χ η s) ⊤ haarT := fun s =>
    (memLp_mst_symbols (P := (0 : Polynomial ℤ)) 1
      ((2 : ℝ) ^ ((s : ℝ) * ((P.natDegree : ℝ) - χ))) η hηc.continuous).2.2
  have hpi : ∀ (N s : ℕ),
      MemLp (fun ζ : Circ => star (mstProf P N ζ) * mstEta P.natDegree χ η s ζ) ⊤ haarT :=
    fun N s => memLp_mstPiBump P P.natDegree χ η N s (hηml s)
  obtain ⟨Ktriv, hKtriv, htriv⟩ :=
    mstNuS_triv_lp_aux P hd hc l hl hχ0 hχ1 η M hM hηc hηbd hηsup hder1 hder2 hνsml
  obtain ⟨Cbase, hCbase, hbase⟩ :=
    mst_lrs_base P hd hc l hl hχ0 hχ1 η M hM hηc hηbd hder1 hder2 hηsup hΘ hpi hr hr2
  obtain ⟨Cerr, cerr, hCerr, hcerr, serr, herr⟩ :=
    mst_lrs_freeze_err P hd hc l hl hχ0 hχ1 η M hM hηc hηbd hder1 hder2 hηsup hpi hνsml hr hr2
  obtain ⟨Sk, hSk⟩ := kappa_exp_le_inv P (by omega : 1 ≤ P.natDegree) hcerr hCerr
  -- the base term in the `mstPiCls` form, as needed by `mst_lrs_frozen_bound`
  have hbase' : ∀ (s : ℕ) (g : ℤ →₀ ℂ),
      MeasureTheory.eLpNorm (fun m : ℤ => ENNReal.ofReal
            ‖opMul (mstPiCls P l P.natDegree χ η s (hηml s) (2 ^ 0)) (⇑g)
              (memℓp_finsupp g) m‖)
          (ENNReal.ofReal r) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (Cbase * (((s : ℝ) + 1) * Real.log ((s : ℝ) + 2)))
          * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal r) MeasureTheory.Measure.count := by
    intro s g
    rw [mstPiCls_eq_arcSymbolLp P l P.natDegree χ η s (2 ^ 0) (hηml s) (hpi (2 ^ 0) s),
      eLpNorm_ofReal_norm]
    exact hbase s g
  obtain ⟨Cfr, hCfr, sfr, hfr⟩ := mst_lrs_frozen_bound hΘ P hd hc l hl hχ0 hχ1 η M hM hηc hηbd
    hη0 hder1 hder2 hηml hr hr2 hCbase hbase'
  -- the freeze error in the `mstPiCls` form
  have herr' : ∀ (s : ℕ), serr ≤ s → ∀ (k : ℕ) (g : ℤ →₀ ℂ),
      MeasureTheory.eLpNorm (fun m : ℤ => ENNReal.ofReal
            ‖opMul (mstNuSCls P l P.natDegree χ η k s (hνsml k s)
                - khatZMult P (⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊)
                  • mstPiCls P l P.natDegree χ η s (hηml s) (2 ^ k))
              (⇑g) (memℓp_finsupp g) m‖)
          (ENNReal.ofReal r) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (Cerr * Real.exp (-(cerr * Real.sqrt ((s : ℝ) + 1))))
          * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal r) MeasureTheory.Measure.count := by
    intro s hs k g
    rw [mstPiCls_eq_arcSymbolLp P l P.natDegree χ η s (2 ^ k) (hηml s) (hpi (2 ^ k) s),
      eLpNorm_ofReal_norm]
    exact herr s hs k g
  set s₀ : ℕ := max (max sfr serr) (max Sk 1) with hs₀def
  set C : ℝ := ((Cfr + 1) + (∑ t ∈ Finset.range s₀, ((2 : ℝ) ^ (mstKappa P t) + 1)
      * (((mstLevel l (t + 1) \ mstLevel l t).card : ℝ)) * Ktriv) + 1) / Real.log 2
    with hCdef
  refine ⟨C, ?_, fun s g => ?_⟩
  · rw [hCdef]
    have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
    have hnn : 0 ≤ (Cfr + 1) + (∑ t ∈ Finset.range s₀, ((2 : ℝ) ^ (mstKappa P t) + 1)
        * (((mstLevel l (t + 1) \ mstLevel l t).card : ℝ)) * Ktriv) + 1 := by positivity
    have hpos : 0 < (Cfr + 1) + (∑ t ∈ Finset.range s₀, ((2 : ℝ) ^ (mstKappa P t) + 1)
        * (((mstLevel l (t + 1) \ mstLevel l t).card : ℝ)) * Ktriv) + 1 := by
      have hsum0 : 0 ≤ ∑ t ∈ Finset.range s₀, ((2 : ℝ) ^ (mstKappa P t) + 1)
          * (((mstLevel l (t + 1) \ mstLevel l t).card : ℝ)) * Ktriv :=
        Finset.sum_nonneg (fun t _ => by positivity)
      linarith [hCfr, hsum0]
    exact div_pos hpos hlog2
  · set K : Finset ℕ := Finset.range (2 ^ (mstKappa P s) + 1) with hKdef
    set B : ℝ≥0∞ := MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal r) MeasureTheory.Measure.count
      with hBdef
    by_cases hcase : s₀ ≤ s
    · -- large levels
      have hs_fr : sfr ≤ s := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hcase
      have hs_err : serr ≤ s := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hcase
      have hs_k : Sk ≤ s := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hcase
      -- ### the pointwise decomposition `|ν| ≤ |μΠ| + |ν - μΠ|`
      have hpt : ∀ m : ℤ,
          (⨆ k ∈ K, ‖opMul (mstNuSCls P l P.natDegree χ η k s (hνsml k s)) (⇑g)
              (memℓp_finsupp g) m‖ₑ)
            ≤ (⨆ k ∈ K, ‖opMul (khatZMult P (⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊)
                  • mstPiCls P l P.natDegree χ η s (hηml s) (2 ^ k)) (⇑g)
                (memℓp_finsupp g) m‖ₑ)
              + ∑ k ∈ K, ‖opMul (mstNuSCls P l P.natDegree χ η k s (hνsml k s)
                  - khatZMult P (⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊)
                    • mstPiCls P l P.natDegree χ η s (hηml s) (2 ^ k)) (⇑g)
                (memℓp_finsupp g) m‖ₑ := by
        intro m
        refine iSup₂_le (fun k hk => ?_)
        have hsplit : opMul (mstNuSCls P l P.natDegree χ η k s (hνsml k s)) (⇑g)
              (memℓp_finsupp g) m
            = opMul (khatZMult P (⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊)
                  • mstPiCls P l P.natDegree χ η s (hηml s) (2 ^ k)) (⇑g)
                (memℓp_finsupp g) m
              + opMul (mstNuSCls P l P.natDegree χ η k s (hνsml k s)
                  - khatZMult P (⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊)
                    • mstPiCls P l P.natDegree χ η s (hηml s) (2 ^ k)) (⇑g)
                (memℓp_finsupp g) m := by
          have hfun : opMul (mstNuSCls P l P.natDegree χ η k s (hνsml k s)) (⇑g)
                (memℓp_finsupp g)
              = opMul (khatZMult P (⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊)
                    • mstPiCls P l P.natDegree χ η s (hηml s) (2 ^ k)) (⇑g)
                  (memℓp_finsupp g)
                + opMul (mstNuSCls P l P.natDegree χ η k s (hνsml k s)
                    - khatZMult P (⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊)
                      • mstPiCls P l P.natDegree χ η s (hηml s) (2 ^ k)) (⇑g)
                  (memℓp_finsupp g) := by
            rw [← opMul_add]
            congr 1
            abel
          exact congrFun hfun m
        calc ‖opMul (mstNuSCls P l P.natDegree χ η k s (hνsml k s)) (⇑g)
                (memℓp_finsupp g) m‖ₑ
            = ‖opMul (khatZMult P (⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊)
                    • mstPiCls P l P.natDegree χ η s (hηml s) (2 ^ k)) (⇑g)
                  (memℓp_finsupp g) m
                + opMul (mstNuSCls P l P.natDegree χ η k s (hνsml k s)
                    - khatZMult P (⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊)
                      • mstPiCls P l P.natDegree χ η s (hηml s) (2 ^ k)) (⇑g)
                  (memℓp_finsupp g) m‖ₑ := by rw [hsplit]
          _ ≤ ‖opMul (khatZMult P (⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊)
                    • mstPiCls P l P.natDegree χ η s (hηml s) (2 ^ k)) (⇑g)
                  (memℓp_finsupp g) m‖ₑ
                + ‖opMul (mstNuSCls P l P.natDegree χ η k s (hνsml k s)
                    - khatZMult P (⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊)
                      • mstPiCls P l P.natDegree χ η s (hηml s) (2 ^ k)) (⇑g)
                  (memℓp_finsupp g) m‖ₑ := enorm_add_le _ _
          _ ≤ (⨆ k ∈ K, ‖opMul (khatZMult P (⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊)
                    • mstPiCls P l P.natDegree χ η s (hηml s) (2 ^ k)) (⇑g)
                  (memℓp_finsupp g) m‖ₑ)
                + ∑ k ∈ K, ‖opMul (mstNuSCls P l P.natDegree χ η k s (hνsml k s)
                    - khatZMult P (⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊)
                      • mstPiCls P l P.natDegree χ η s (hηml s) (2 ^ k)) (⇑g)
                  (memℓp_finsupp g) m‖ₑ := by
              refine add_le_add (le_iSup_of_le k (le_iSup_of_le hk le_rfl)) ?_
              refine Finset.single_le_sum (f := fun k => ‖opMul (mstNuSCls P l P.natDegree χ η k s
                  (hνsml k s) - khatZMult P (⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊)
                    • mstPiCls P l P.natDegree χ η s (hηml s) (2 ^ k)) (⇑g)
                (memℓp_finsupp g) m‖ₑ) ?_ hk
              intro i _
              exact bot_le
      -- ### Minkowski
      have hm1 : MeasureTheory.eLpNorm (fun m : ℤ =>
            (⨆ k ∈ K, ‖opMul (mstNuSCls P l P.natDegree χ η k s (hνsml k s)) (⇑g)
              (memℓp_finsupp g) m‖ₑ)) (ENNReal.ofReal r) MeasureTheory.Measure.count
          ≤ MeasureTheory.eLpNorm (fun m : ℤ =>
              (⨆ k ∈ K, ‖opMul (khatZMult P (⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊)
                    • mstPiCls P l P.natDegree χ η s (hηml s) (2 ^ k)) (⇑g)
                  (memℓp_finsupp g) m‖ₑ)
              + ∑ k ∈ K, ‖opMul (mstNuSCls P l P.natDegree χ η k s (hνsml k s)
                  - khatZMult P (⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊)
                    • mstPiCls P l P.natDegree χ η s (hηml s) (2 ^ k)) (⇑g)
                (memℓp_finsupp g) m‖ₑ) (ENNReal.ofReal r) MeasureTheory.Measure.count :=
        eLpNorm_mono_enorm AEStronglyMeasurable.of_discrete (fun m => hpt m)
      have hm2 : MeasureTheory.eLpNorm (fun m : ℤ =>
              (⨆ k ∈ K, ‖opMul (khatZMult P (⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊)
                    • mstPiCls P l P.natDegree χ η s (hηml s) (2 ^ k)) (⇑g)
                  (memℓp_finsupp g) m‖ₑ)
              + ∑ k ∈ K, ‖opMul (mstNuSCls P l P.natDegree χ η k s (hνsml k s)
                  - khatZMult P (⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊)
                    • mstPiCls P l P.natDegree χ η s (hηml s) (2 ^ k)) (⇑g)
                (memℓp_finsupp g) m‖ₑ) (ENNReal.ofReal r) MeasureTheory.Measure.count
          ≤ MeasureTheory.eLpNorm (fun m : ℤ =>
                (⨆ k ∈ K, ‖opMul (khatZMult P (⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊)
                    • mstPiCls P l P.natDegree χ η s (hηml s) (2 ^ k)) (⇑g)
                  (memℓp_finsupp g) m‖ₑ)) (ENNReal.ofReal r) MeasureTheory.Measure.count
            + MeasureTheory.eLpNorm (fun m : ℤ =>
                ∑ k ∈ K, ‖opMul (mstNuSCls P l P.natDegree χ η k s (hνsml k s)
                  - khatZMult P (⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊)
                    • mstPiCls P l P.natDegree χ η s (hηml s) (2 ^ k)) (⇑g)
                (memℓp_finsupp g) m‖ₑ) (ENNReal.ofReal r) MeasureTheory.Measure.count :=
        eLpNorm_add_le (ENNReal.one_le_ofReal.mpr hr.le)
      have hm3 : MeasureTheory.eLpNorm (fun m : ℤ =>
                ∑ k ∈ K, ‖opMul (mstNuSCls P l P.natDegree χ η k s (hνsml k s)
                  - khatZMult P (⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊)
                    • mstPiCls P l P.natDegree χ η s (hηml s) (2 ^ k)) (⇑g)
                (memℓp_finsupp g) m‖ₑ) (ENNReal.ofReal r) MeasureTheory.Measure.count
          ≤ ∑ k ∈ K, MeasureTheory.eLpNorm (fun m : ℤ =>
                ‖opMul (mstNuSCls P l P.natDegree χ η k s (hνsml k s)
                  - khatZMult P (⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊)
                    • mstPiCls P l P.natDegree χ η s (hηml s) (2 ^ k)) (⇑g)
                (memℓp_finsupp g) m‖ₑ) (ENNReal.ofReal r) MeasureTheory.Measure.count :=
        Commons.MeasureTheory.Lp.eLpNorm_finset_sum_le_ennreal (ENNReal.one_le_ofReal.mpr hr.le)
          (fun k _ => (measurable_of_countable _).aemeasurable)
      -- ### the frozen part: pull out the weight, then Rademacher–Menshov
      have hbridge2 : ∀ k : ℕ, mstPiCls P l P.natDegree χ η s (hηml s) (2 ^ k)
          = arcSymbolLp (fun ζ : Circ => star (mstProf P (2 ^ k) ζ) * mstEta P.natDegree χ η s ζ)
              (hpi (2 ^ k) s) (mstLevel l (s + 1) \ mstLevel l s) :=
        fun k => mstPiCls_eq_arcSymbolLp P l P.natDegree χ η s (2 ^ k) (hηml s) (hpi (2 ^ k) s)
      have hpull' : MeasureTheory.eLpNorm (fun m : ℤ =>
                (⨆ k ∈ K, ‖opMul (khatZMult P (⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊)
                    • mstPiCls P l P.natDegree χ η s (hηml s) (2 ^ k)) (⇑g)
                  (memℓp_finsupp g) m‖ₑ)) (ENNReal.ofReal r) MeasureTheory.Measure.count
          ≤ MeasureTheory.eLpNorm (fun m : ℤ =>
                (⨆ k ∈ K, ‖opMul (mstPiCls P l P.natDegree χ η s (hηml s) (2 ^ k)) (⇑g)
                  (memℓp_finsupp g) m‖ₑ)) (ENNReal.ofReal r) MeasureTheory.Measure.count := by
        have h1 := mst_lrs_frozen_sup P l χ η (⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊) hpi
          hr.le s K g
        have h2 : (fun m : ℤ => (⨆ k ∈ K, ‖opMul (khatZMult P (⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊)
              • mstPiCls P l P.natDegree χ η s (hηml s) (2 ^ k)) (⇑g)
            (memℓp_finsupp g) m‖ₑ))
            = (fun m : ℤ => (⨆ k ∈ K, ‖opMul (khatZMult P (⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊)
              • arcSymbolLp (fun ζ : Circ => star (mstProf P (2 ^ k) ζ) * mstEta P.natDegree χ η s ζ)
                (hpi (2 ^ k) s) (mstLevel l (s + 1) \ mstLevel l s)) (⇑g)
            (memℓp_finsupp g) m‖ₑ)) :=
          iSup_norm_congr K _ _ (fun k => by rw [hbridge2 k])
        have h3 : (fun m : ℤ => (⨆ k ∈ K, ‖opMul (mstPiCls P l P.natDegree χ η s (hηml s) (2 ^ k))
              (⇑g) (memℓp_finsupp g) m‖ₑ))
            = (fun m : ℤ => (⨆ k ∈ K, ‖opMul (arcSymbolLp
                (fun ζ : Circ => star (mstProf P (2 ^ k) ζ) * mstEta P.natDegree χ η s ζ)
                (hpi (2 ^ k) s) (mstLevel l (s + 1) \ mstLevel l s)) (⇑g)
            (memℓp_finsupp g) m‖ₑ)) :=
          iSup_norm_congr K _ _ (fun k => by rw [hbridge2 k])
        rw [h2, h3]
        exact h1
      have hfrozen := hfr s hs_fr g
      have hb1 : MeasureTheory.eLpNorm (fun m : ℤ =>
                (⨆ k ∈ K, ‖opMul (khatZMult P (⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊)
                    • mstPiCls P l P.natDegree χ η s (hηml s) (2 ^ k)) (⇑g)
                  (memℓp_finsupp g) m‖ₑ)) (ENNReal.ofReal r) MeasureTheory.Measure.count
          ≤ ENNReal.ofReal (Cfr * (((s : ℝ) + 1) * Real.log ((s : ℝ) + 2))) * B :=
        hpull'.trans (by simpa only [hBdef] using hfrozen)
      -- ### the error sum
      have hterm : ∀ k ∈ K, MeasureTheory.eLpNorm (fun m : ℤ =>
              ‖opMul (mstNuSCls P l P.natDegree χ η k s (hνsml k s)
                - khatZMult P (⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊)
                  • mstPiCls P l P.natDegree χ η s (hηml s) (2 ^ k)) (⇑g)
              (memℓp_finsupp g) m‖ₑ) (ENNReal.ofReal r) MeasureTheory.Measure.count
          ≤ ENNReal.ofReal (Cerr * Real.exp (-(cerr * Real.sqrt ((s : ℝ) + 1)))) * B := by
        intro k _
        have h := herr' s hs_err k g
        rw [MeasureTheory.eLpNorm_enorm _ AEStronglyMeasurable.of_discrete]
        rwa [eLpNorm_ofReal_norm, ← hBdef] at h
      have hcard : ((K.card : ℕ) : ℝ≥0∞) ≤ ((2 ^ (mstKappa P s) + 1 : ℕ) : ℝ≥0∞) := by
        rw [hKdef, Finset.card_range]
      have hconst : ((2 ^ (mstKappa P s) + 1 : ℕ) : ℝ≥0∞)
          * ENNReal.ofReal (Cerr * Real.exp (-(cerr * Real.sqrt ((s : ℝ) + 1)))) ≤ 1 := by
        rw [show ((2 ^ (mstKappa P s) + 1 : ℕ) : ℝ≥0∞)
            = ENNReal.ofReal (((2 : ℝ) ^ (mstKappa P s) + 1)) from by
          rw [← ENNReal.ofReal_natCast]
          norm_num]
        rw [← ENNReal.ofReal_mul (by positivity), ← mul_assoc]
        simpa using ENNReal.ofReal_le_ofReal (hSk s hs_k)
      have hkey : ((K.card : ℕ) : ℝ≥0∞)
          * ENNReal.ofReal (Cerr * Real.exp (-(cerr * Real.sqrt ((s : ℝ) + 1)))) ≤ 1 :=
        le_trans (mul_le_mul_of_nonneg_right hcard (bot_le)) hconst
      have herrsum : ∑ k ∈ K, MeasureTheory.eLpNorm (fun m : ℤ =>
              ‖opMul (mstNuSCls P l P.natDegree χ η k s (hνsml k s)
                - khatZMult P (⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊)
                  • mstPiCls P l P.natDegree χ η s (hηml s) (2 ^ k)) (⇑g)
              (memℓp_finsupp g) m‖ₑ) (ENNReal.ofReal r) MeasureTheory.Measure.count
          ≤ B := by
        calc ∑ k ∈ K, MeasureTheory.eLpNorm (fun m : ℤ =>
              ‖opMul (mstNuSCls P l P.natDegree χ η k s (hνsml k s)
                - khatZMult P (⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊)
                  • mstPiCls P l P.natDegree χ η s (hηml s) (2 ^ k)) (⇑g)
              (memℓp_finsupp g) m‖ₑ) (ENNReal.ofReal r) MeasureTheory.Measure.count
            ≤ ∑ _k ∈ K, (ENNReal.ofReal (Cerr * Real.exp (-(cerr * Real.sqrt ((s : ℝ) + 1)))) * B) :=
              Finset.sum_le_sum hterm
          _ = ((K.card : ℕ) : ℝ≥0∞)
                * (ENNReal.ofReal (Cerr * Real.exp (-(cerr * Real.sqrt ((s : ℝ) + 1)))) * B) := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ = (((K.card : ℕ) : ℝ≥0∞)
                * ENNReal.ofReal (Cerr * Real.exp (-(cerr * Real.sqrt ((s : ℝ) + 1))))) * B := by
              rw [mul_assoc]
          _ ≤ 1 * B := mul_le_mul_of_nonneg_right hkey (bot_le)
          _ = B := one_mul B
      -- ### combine
      have hmain : MeasureTheory.eLpNorm (fun m : ℤ =>
            (⨆ k ∈ K, ‖opMul (mstNuSCls P l P.natDegree χ η k s (hνsml k s)) (⇑g)
              (memℓp_finsupp g) m‖ₑ)) (ENNReal.ofReal r) MeasureTheory.Measure.count
          ≤ ENNReal.ofReal (Cfr * (((s : ℝ) + 1) * Real.log ((s : ℝ) + 2))) * B + B := by
        refine (hm1.trans (hm2.trans (add_le_add hb1 (hm3.trans herrsum)))).trans ?_
        exact le_of_eq (by rw [add_mul, one_mul])
      -- ### the arithmetic
      have hKsnn : (0 : ℝ) ≤ ((s : ℝ) + 1) * Real.log ((s : ℝ) + 2) :=
        mul_nonneg (by positivity) (Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) s]))
      have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
      have hlogle : Real.log 2 ≤ 1 := le_trans (Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2))
        (by norm_num)
      have hKs : Real.log 2 ≤ ((s : ℝ) + 1) * Real.log ((s : ℝ) + 2) := by
        have h1 : Real.log 2 ≤ Real.log ((s : ℝ) + 2) :=
          Real.log_le_log (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) s])
        have h2 : (1 : ℝ) ≤ (s : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) s]
        nlinarith [Real.log_pos (by linarith : (1:ℝ) < (s : ℝ) + 2)]
      have hCge : (Cfr + 1) / Real.log 2 ≤ C := by
        rw [hCdef]
        refine div_le_div_of_nonneg_right ?_ hlog2.le
        have hsum0 : 0 ≤ ∑ t ∈ Finset.range s₀, ((2 : ℝ) ^ (mstKappa P t) + 1)
            * (((mstLevel l (t + 1) \ mstLevel l t).card : ℝ)) * Ktriv :=
          Finset.sum_nonneg (fun t _ => by positivity)
        linarith
      have hCle2 : Cfr * (((s : ℝ) + 1) * Real.log ((s : ℝ) + 2)) + 1
          ≤ C * (((s : ℝ) + 1) * Real.log ((s : ℝ) + 2)) := by
        have hstep : Cfr * (((s : ℝ) + 1) * Real.log ((s : ℝ) + 2)) + 1
            ≤ ((Cfr + 1) / Real.log 2) * (((s : ℝ) + 1) * Real.log ((s : ℝ) + 2)) := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
          nlinarith [hKs, hKsnn, hCfr, hlogle, mul_nonneg (le_of_lt hCfr) hKsnn]
        exact le_trans hstep (mul_le_mul_of_nonneg_right hCge hKsnn)
      have hconst2 : ENNReal.ofReal (Cfr * (((s : ℝ) + 1) * Real.log ((s : ℝ) + 2))) + 1
          ≤ ENNReal.ofReal (C * (((s : ℝ) + 1) * Real.log ((s : ℝ) + 2))) := by
        rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by positivity) (by norm_num)]
        exact ENNReal.ofReal_le_ofReal hCle2
      refine hmain.trans ?_
      calc ENNReal.ofReal (Cfr * (((s : ℝ) + 1) * Real.log ((s : ℝ) + 2))) * B + B
          = (ENNReal.ofReal (Cfr * (((s : ℝ) + 1) * Real.log ((s : ℝ) + 2))) + 1) * B := by
            ring
        _ ≤ ENNReal.ofReal (C * (((s : ℝ) + 1) * Real.log ((s : ℝ) + 2))) * B :=
            mul_le_mul_of_nonneg_right hconst2 (bot_le)
    · -- small levels: the trivial bound
      have htriv' : ∀ k : ℕ, MeasureTheory.eLpNorm (fun m : ℤ =>
            ‖opMul (mstNuSCls P l P.natDegree χ η k s (hνsml k s)) (⇑g)
              (memℓp_finsupp g) m‖ₑ) (ENNReal.ofReal r) MeasureTheory.Measure.count
          ≤ ENNReal.ofReal ((((mstLevel l (s + 1) \ mstLevel l s).card : ℝ)) * Ktriv) * B := by
        intro k
        have h := htriv s k g (r := r) hr.le
        rw [opMulFinsuppLM_apply] at h
        rw [MeasureTheory.eLpNorm_enorm _ AEStronglyMeasurable.of_discrete]
        exact h
      have hsup : MeasureTheory.eLpNorm (fun m : ℤ => (⨆ k ∈ Finset.range (2 ^ (mstKappa P s) + 1),
            ‖opMul (mstNuSCls P l P.natDegree χ η k s (hνsml k s)) (⇑g)
              (memℓp_finsupp g) m‖ₑ)) (ENNReal.ofReal r) MeasureTheory.Measure.count
          ≤ ∑ k ∈ Finset.range (2 ^ (mstKappa P s) + 1), MeasureTheory.eLpNorm (fun m : ℤ =>
              ‖opMul (mstNuSCls P l P.natDegree χ η k s (hνsml k s)) (⇑g)
                (memℓp_finsupp g) m‖ₑ) (ENNReal.ofReal r) MeasureTheory.Measure.count := by
        refine (eLpNorm_mono_enorm (f := fun m : ℤ => (⨆ k ∈ Finset.range (2 ^ (mstKappa P s) + 1),
              ‖opMul (mstNuSCls P l P.natDegree χ η k s (hνsml k s)) (⇑g)
                (memℓp_finsupp g) m‖ₑ))
            (g := fun m : ℤ => ∑ k ∈ Finset.range (2 ^ (mstKappa P s) + 1),
              ‖opMul (mstNuSCls P l P.natDegree χ η k s (hνsml k s)) (⇑g)
                (memℓp_finsupp g) m‖ₑ) AEStronglyMeasurable.of_discrete ?_).trans ?_
        · intro m
          refine iSup₂_le (fun k hk => ?_)
          exact Finset.single_le_sum (f := fun k => ‖opMul (mstNuSCls P l P.natDegree χ η k s
              (hνsml k s)) (⇑g) (memℓp_finsupp g) m‖ₑ) (fun i _ => bot_le) hk
        · exact Commons.MeasureTheory.Lp.eLpNorm_finset_sum_le_ennreal
            (ENNReal.one_le_ofReal.mpr hr.le)
            (fun k _ => (measurable_of_countable _).aemeasurable)
      have hbound : ∑ k ∈ Finset.range (2 ^ (mstKappa P s) + 1), MeasureTheory.eLpNorm (fun m : ℤ =>
              ‖opMul (mstNuSCls P l P.natDegree χ η k s (hνsml k s)) (⇑g)
                (memℓp_finsupp g) m‖ₑ) (ENNReal.ofReal r) MeasureTheory.Measure.count
          ≤ ENNReal.ofReal (((2 : ℝ) ^ (mstKappa P s) + 1)
              * ((((mstLevel l (s + 1) \ mstLevel l s).card : ℝ)) * Ktriv)) * B := by
        have hsum' : ∑ k ∈ Finset.range (2 ^ (mstKappa P s) + 1), MeasureTheory.eLpNorm (fun m : ℤ =>
                ‖opMul (mstNuSCls P l P.natDegree χ η k s (hνsml k s)) (⇑g)
                  (memℓp_finsupp g) m‖ₑ) (ENNReal.ofReal r) MeasureTheory.Measure.count
            ≤ ∑ _k ∈ Finset.range (2 ^ (mstKappa P s) + 1),
                (ENNReal.ofReal ((((mstLevel l (s + 1) \ mstLevel l s).card : ℝ)) * Ktriv) * B) :=
          Finset.sum_le_sum (fun k _ => htriv' k)
        refine hsum'.trans ?_
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        rw [show ((2 ^ (mstKappa P s) + 1 : ℕ) : ℝ≥0∞)
            = ENNReal.ofReal (((2 : ℝ) ^ (mstKappa P s) + 1)) from by
          rw [← ENNReal.ofReal_natCast]
          push_cast
          rfl]
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
      refine hsup.trans (hbound.trans ?_)
      refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) (bot_le)
      · -- the small-level constant is absorbed into `C`
        have hmem : s ∈ Finset.range s₀ := Finset.mem_range.mpr (lt_of_not_ge hcase)
        have hsingle : ((2 : ℝ) ^ (mstKappa P s) + 1)
            * (((mstLevel l (s + 1) \ mstLevel l s).card : ℝ)) * Ktriv
            ≤ ∑ t ∈ Finset.range s₀, ((2 : ℝ) ^ (mstKappa P t) + 1)
              * (((mstLevel l (t + 1) \ mstLevel l t).card : ℝ)) * Ktriv :=
          Finset.single_le_sum (f := fun t => ((2 : ℝ) ^ (mstKappa P t) + 1)
              * (((mstLevel l (t + 1) \ mstLevel l t).card : ℝ)) * Ktriv)
            (fun t _ => by positivity) hmem
        have hClog2 : ((2 : ℝ) ^ (mstKappa P s) + 1)
            * (((mstLevel l (s + 1) \ mstLevel l s).card : ℝ)) * Ktriv ≤ C * Real.log 2 := by
          rw [hCdef, div_mul_cancel₀ _ (ne_of_gt (Real.log_pos one_lt_two))]
          linarith [hsingle, hCfr]
        have hlog : Real.log 2 ≤ ((s : ℝ) + 1) * Real.log ((s : ℝ) + 2) := by
          have h1 : Real.log 2 ≤ Real.log ((s : ℝ) + 2) :=
            Real.log_le_log (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) s])
          have h3 : (1 : ℝ) ≤ (s : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) s]
          nlinarith [Real.log_pos (by linarith : (1:ℝ) < (s : ℝ) + 2)]
        have hCnn : 0 ≤ C := by
          rw [hCdef]
          refine div_nonneg ?_ (Real.log_pos one_lt_two).le
          have hsum0 : 0 ≤ ∑ t ∈ Finset.range s₀, ((2 : ℝ) ^ (mstKappa P t) + 1)
              * (((mstLevel l (t + 1) \ mstLevel l t).card : ℝ)) * Ktriv :=
            Finset.sum_nonneg (fun t _ => by positivity)
          linarith [hCfr, hsum0]
        rw [show ((2 : ℝ) ^ (mstKappa P s) + 1)
              * ((((mstLevel l (s + 1) \ mstLevel l s).card : ℝ)) * Ktriv)
            = ((2 : ℝ) ^ (mstKappa P s) + 1)
              * (((mstLevel l (s + 1) \ mstLevel l s).card : ℝ)) * Ktriv from by ring]
        calc ((2 : ℝ) ^ (mstKappa P s) + 1)
              * (((mstLevel l (s + 1) \ mstLevel l s).card : ℝ)) * Ktriv
            ≤ C * Real.log 2 := hClog2
          _ ≤ C * (((s : ℝ) + 1) * Real.log ((s : ℝ) + 2)) :=
              mul_le_mul_of_nonneg_left hlog hCnn
end

end Work.Maximal
