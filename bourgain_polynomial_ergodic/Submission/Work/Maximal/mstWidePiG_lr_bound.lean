import Mathlib
import Submission.Work.Maximal.mstWide_defs
import Submission.Work.Maximal.mstWideAux
import Submission.Work.Maximal.mstWideLrBump_fourierCoeff
import Submission.Work.Maximal.mstWideLrBump_coeff_l1
import Submission.Work.Maximal.mstWideLrPi_lr
import Submission.Work.Maximal.mstWideLrPiG_error
import Submission.Work.Maximal.mst_lrs_freeze_err
import Submission.Work.Maximal.arcSymbolW_lp_bound_of_coeff
import Submission.Work.BourgainPlan.KPWW.opArc_lp_bound_of_coeff
import Submission.Work.BourgainPlan.Maximal.eLpNorm_two_opMul_le
import Submission.Work.BourgainPlan.Maximal.mst_majErr_interp
import Submission.Work.BourgainPlan.Maximal.mstHat_decay_of_contDiff
import Submission.Work.BourgainPlan.Maximal.mstHat_bound
import Submission.Work.BourgainPlan.Maximal.mstU_card_le_exp
import Submission.Work.BourgainPlan.Maximal.minor_arc_lp
import Submission.Work.BourgainPlan.Maximal.mstHat_sampling_bound
import Submission.Work.BourgainPlan.Maximal.mst_iw_lift
import Submission.Work.BourgainPlan.Maximal.mst_major_err1_l2

/-!
# The weighted wide multiplier `Π̃^G_s` is `ℓʳ`-bounded with a `log(s+2)` loss

This file proves `Work.Maximal.mstWidePiG_lr_bound` (MST arXiv:1512.07518, eq. (79)) via the
decomposition of MST eqs. (94), (112):

`Π̃^G_s = (khatZMult P J • mstLrPiCls) + (mstLrPiGCls − khatZMult P J • mstLrPiCls)`

with `J = mstLrJ s = ⌊exp √(s+1)⌋`.  The first (frozen) summand is the density average `μ_J`
composed with the *unweighted* wide arc sum `Π̃_s`, bounded by the Ionescu–Wainger estimate
(`Work.Maximal.mstWideLrPi_lr`, imported from `Submission/Work/Maximal/mstWideLrPi_lr.lean`), while
the second (error) summand is `ℓ²`-small (`Work.Maximal.mstWideLrErrCls_ae_bound`, which turns the
pointwise Weyl approximation `mstWideLrPiG_error` into an a.e. bound of its symbol class) and
`ℓʳ`-trivially bounded, hence bounded on `ℓʳ` by Riesz–Thorin (`opMulFinsuppLM_interp`) through the
arithmetic of `mstFreeze_arith` (the subexponential cardinality loss against the exponential gain).
-/

namespace Work.Maximal

open MeasureTheory Finset
open scoped BigOperators ENNReal
set_option autoImplicit false
set_option maxHeartbeats 6000000

local notation "Circ" => Work.BourgainPlan.IonescuWainger.Circle
local notation "haarT" => (AddCircle.haarAddCircle (T := 1))

noncomputable section

open Work.BourgainPlan.Maximal (mstU mstU_apply mstLevel mstLevel_succ sigmaN_nested mstRho
  mstRho_pow_eq_real mstHat mstHat_bound mstHat_decay_of_contDiff khatZMult discAvgZC
  discAvgZC_contraction eLpNorm_two_opMul_le opMulFinsuppLM opMulFinsuppLM_apply
  opMulFinsuppLM_interp arcSymbolWLp arcSymbolWLp_coeFn arcSymbolW
  discAvgZC_opArc_eq_opMul_smul mstU_card_le_exp mstG mstWeyl
  khatZMult_coeFn_star_mstWeyl mstG_norm_le_one)

/-! ## The a.e. pointwise bound for the error class -/

theorem mstWideLrErrCls_ae_bound (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
    (hc : 0 < P.leadingCoeff) (l : ℕ) (hl : 1 ≤ l) {χ : ℝ} (hχ0 : 0 < χ) (hχ1 : χ < 1 / 10)
    (η : ℝ → ℂ) (M : ℝ) (hM : 0 < M) (hηc : ContDiff ℝ 2 η)
    (hηbd : ∀ x : ℝ, ‖η x‖ ≤ M) (hηsup : ∀ x : ℝ, 1 / 2 ≤ |x| → η x = 0) :
    ∃ C : ℝ, 0 < C ∧ ∃ S₀ : ℕ, ∀ s : ℕ, S₀ ≤ s → ∀ᵐ ξ ∂haarT,
      ‖((mstLrPiGCls P l χ η hηc.continuous hηsup s
          - khatZMult P (mstLrJ s) • mstLrPiCls P l χ η hηc.continuous hηsup s :
            Lp ℂ ⊤ haarT) : Circ → ℂ) ξ‖
        ≤ C * Real.exp (-(Real.sqrt ((s : ℝ) + 1) / 2)) := by
  obtain ⟨C, hC, S₀, hpt⟩ := mstWideLrPiG_error P hd hc l hl hχ0 hχ1 η M hM hηc hηbd hηsup
  refine ⟨C, hC, S₀, fun s hs => ?_⟩
  have hsub := Lp.coeFn_sub (mstLrPiGCls P l χ η hηc.continuous hηsup s)
    (khatZMult P (mstLrJ s) • mstLrPiCls P l χ η hηc.continuous hηsup s)
  have hGc := mstLrPiGCls_coeFn P l χ η hηc.continuous hηsup s
  have hW := khatZMult_smul_mstLrPiCls_coeFn P l χ η hηc.continuous hηsup (mstLrJ s) s
  filter_upwards [hsub, hGc, hW] with ξ h1 h2 h3
  rw [h1, Pi.sub_apply, h2, h3]
  exact hpt s hs ξ

/-! ## The main theorem -/

/-- **The single weighted wide multiplier is `ℓʳ`-bounded with only a `log(s+2)` loss** (MST
arXiv:1512.07518, eq. (79) of the proof of Theorem 1): the weighted wide arc sum
`Π̃^G_s = Σ_{β ∈ 𝒰(s+1)∖𝒰(s)} star (G β) ϱ_s(·−β)` defines an `ℓʳ(ℤ)` multiplier with norm
`≤ C log(s+2)`.

Route (MST eqs. (94), (112) and the paragraph after): replace `G β` by the global Weyl kernel
`mstWeyl P J` (`J = ⌊exp √(s+1)⌋`) using the pointwise bound `mst_lvl_approx_pointwise`
(`‖m_J(ξ) − G β‖ ≤ C exp(−√(s+1)/2)` at points `ξ` with `mstEta … s (ξ−β) ≠ 0`); the resulting
unweighted arc sum `Σ_β ϱ_s(·−β)` (`mstWidePi`) is `ℓʳ`-bounded by `C log(s+2)` through the
Ionescu–Wainger range bound `iwRangeBound` (`iwSupersetBoundLift`; the single scaled bump
`η(c_s ·)` has the Mikhlin data of `η` by `mikhlin_conditions_scaled_bump`, and
`mstWideBump_memLp_and_narrow` is the narrowness), while the error `Π̃^G_s − μ_J Π̃_s` is `ℓ²`-small
(`exp(−√(s+1)/2)`, Plancherel) and `ℓʳ`-trivially bounded, hence `≲ 1` after Riesz–Thorin
(`ellp_interpolation`); the discrete averaging operator `μ_J = mstWeyl P J` is an `ℓʳ`-contraction
(it is the average of the `J` shifts `T_{P j}`). -/
theorem mstWidePiG_lr_bound (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (hc : 0 < P.leadingCoeff)
    (l : ℕ) (hl : 1 ≤ l) {χ : ℝ} (hχ0 : 0 < χ) (hχ1 : χ < 1 / 10)
    (η : ℝ → ℂ) (M : ℝ) (hM : 0 < M) (hηc : ContDiff ℝ 2 η)
    (hηbd : ∀ x : ℝ, ‖η x‖ ≤ M)
    (hder1 : ∀ x : ℝ, |x| * ‖deriv η x‖ ≤ M)
    (hder2 : ∀ x : ℝ, |x| ^ 2 * ‖iteratedDeriv 2 η x‖ ≤ M)
    (hηsup : ∀ x : ℝ, 1 / 2 ≤ |x| → η x = 0)
    {r : ℝ} (hr : 1 < r) (hr2 : r < 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : ℕ) (hπ : MeasureTheory.MemLp
        (Work.Maximal.mstWidePiG P l χ η s) ⊤ (AddCircle.haarAddCircle (T := 1)))
      (g : ℤ →₀ ℂ),
      MeasureTheory.eLpNorm (fun m : ℤ => ‖Work.BourgainPlan.IonescuWainger.opMul
          (hπ.toLp (Work.Maximal.mstWidePiG P l χ η s)) (⇑g)
          (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g) m‖ₑ)
          (ENNReal.ofReal r) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C * Real.log ((s : ℝ) + 2))
          * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal r) MeasureTheory.Measure.count := by
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  have hη2 : ∀ x : ℝ, 1 / 2 < |x| → η x = 0 := fun x hx => hηsup x hx.le
  have hηcs : Continuous η := hηc.continuous
  have hχd : χ ≤ (P.natDegree : ℝ) := by
    have h2 : (2 : ℝ) ≤ (P.natDegree : ℝ) := by exact_mod_cast hd
    linarith
  set r₀ : ℝ := (1 + r) / 2 with hr₀def
  have hr₀ : 1 < r₀ := by rw [hr₀def]; linarith
  have hr₀r : r₀ < r := by rw [hr₀def]; linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  -- * the coefficient `ℓ¹`-bound of the wide bump
  have hhid : ∀ (s : ℕ) (m : ℤ),
      (∫ ξ : Circ, mstWideBump P χ η s ξ * star (fourier m ξ) ∂haarT)
        = ((mstWideC P s : ℂ))⁻¹
            * mstHat η ((m : ℝ) / mstWideC P s) := by
    intro s m
    have h := mstWideLrBump_fourierCoeff (c := mstWideC P s) (one_le_mstWideC P s) (η := η) hη2 m
    simpa only [mstWideBump_apply] using h
  have hdec : ∀ t : ℝ, t ≠ 0 →
      ‖mstHat η t‖ ≤ (∫ x, ‖deriv (deriv η) x‖) / (2 * Real.pi) ^ 2 / t ^ 2 :=
    mstHat_decay_of_contDiff η hηc hη2
  have hE0 : 0 ≤ (∫ x, ‖deriv (deriv η) x‖) / (2 * Real.pi) ^ 2 :=
    div_nonneg (integral_nonneg (fun x => norm_nonneg _)) (by positivity)
  obtain ⟨Ccoef, hCcoefpos, hcoef⟩ := mstWideLrBump_coeff_l1 P χ η hM.le hE0
    (fun t => mstHat_bound hM.le hηbd t) hdec hhid
  -- * the IW bound for the unweighted wide arc sum
  obtain ⟨Ciw, hCiwpos, hIw⟩ :=
    mstWideLrPi_lr P hd hc l hl hχ0 hχ1 η M hM hηc hηbd hder1 hder2 hηsup hr
  -- * the pointwise error bound and its a.e. class form
  obtain ⟨Cae, hCaepos, Sae, hAe⟩ :=
    mstWideLrErrCls_ae_bound P hd hc l hl hχ0 hχ1 η M hM hηc hηbd hηsup
  -- * the cardinality of the level sets
  obtain ⟨Ccard, hCcardpos, hcard⟩ := mstU_card_le_exp l hl
  -- * the interpolation arithmetic
  obtain ⟨Carith, carith, hCarithpos, hcarithpos, Sarith, harith⟩ :=
    mstFreeze_arith (r := r) (r₀ := r₀) hr hr2 hr₀ hr₀r
      (A := max (2 * Ccoef * Ccard) 1) (B := max Cae 1)
      (le_max_right _ _) (lt_of_lt_of_le zero_lt_one (le_max_right _ _))
  -- * the global constant
  set S₀ : ℕ := max Sae Sarith with hS₀def
  set Ksmall : ℝ := Ccoef * ((mstU l (S₀ + 1)).card : ℝ) + 1 with hKsmalldef
  set Cfin : ℝ := max (((Carith + Ciw + Ksmall) / Real.log 2)) 1 + 1 with hCfindef
  have hCfinpos : 0 < Cfin := by rw [hCfindef]; positivity
  have hKsmallpos : 0 ≤ Ksmall := by rw [hKsmalldef]; positivity
  have hCfin_big : Carith + Ciw + Ksmall ≤ Cfin * Real.log 2 := by
    rw [hCfindef]
    have h1 : ((Carith + Ciw + Ksmall) / Real.log 2)
        ≤ max ((Carith + Ciw + Ksmall) / Real.log 2) 1 + 1 := by
      linarith [le_max_left ((Carith + Ciw + Ksmall) / Real.log 2) (1 : ℝ)]
    have h2 : Carith + Ciw + Ksmall
        = ((Carith + Ciw + Ksmall) / Real.log 2) * Real.log 2 := by field_simp
    calc Carith + Ciw + Ksmall
        = ((Carith + Ciw + Ksmall) / Real.log 2) * Real.log 2 := h2
      _ ≤ (max ((Carith + Ciw + Ksmall) / Real.log 2) 1 + 1) * Real.log 2 :=
          mul_le_mul_of_nonneg_right h1 hlog2.le
  refine ⟨Cfin, hCfinpos, fun s hπ g => ?_⟩
  have hgf : Memℓp (⇑g : ℤ → ℂ) 2 := Work.BourgainPlan.IonescuWainger.memℓp_finsupp g
  have hEsub : mstAnnulus l s ⊆ mstU l (s + 1) := by
    intro β hβ
    have h : β ∈ mstLevel l (s + 1) \ mstLevel l s := hβ
    rw [mstLevel_succ] at h
    exact (Finset.mem_sdiff.mp h).1
  have hcard_exp : ((mstAnnulus l s).card : ℝ)
      ≤ Ccard * Real.exp (((s : ℝ) + 1) ^ (1 / 10 : ℝ)) := by
    have h1 : (mstAnnulus l s).card ≤ (mstU l (s + 1)).card := Finset.card_le_card hEsub
    have h2 : ((mstU l (s + 1)).card : ℝ)
        ≤ Ccard * Real.exp (((((s + 1 : ℕ)) : ℝ) ^ l) ^ (mstRho l)) := hcard (s + 1)
    have h3 : (((((s + 1 : ℕ)) : ℝ) ^ l) ^ (mstRho l)) = ((s : ℝ) + 1) ^ (1 / 10 : ℝ) := by
      rw [mstRho_pow_eq_real l hl (s + 1) (by omega)]
      push_cast
      ring
    rw [h3] at h2
    calc ((mstAnnulus l s).card : ℝ) ≤ ((mstU l (s + 1)).card : ℝ) := by exact_mod_cast h1
      _ ≤ Ccard * Real.exp (((s : ℝ) + 1) ^ (1 / 10 : ℝ)) := h2
  -- the trivial `ℓᵖ` bound for the weighted symbol
  have htrivG : ∀ {p : ℝ}, 1 ≤ p → ∀ f : ℤ →₀ ℂ,
      MeasureTheory.eLpNorm (fun n : ℤ => Work.BourgainPlan.IonescuWainger.opMul
            (mstLrPiGCls P l χ η hηcs hηsup s) (⇑f)
            (Work.BourgainPlan.IonescuWainger.memℓp_finsupp f) n) (ENNReal.ofReal p)
          MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (((mstAnnulus l s).card : ℝ) * Ccoef)
          * MeasureTheory.eLpNorm (⇑f) (ENNReal.ofReal p) MeasureTheory.Measure.count := by
    intro p hp f
    have h := arcSymbolW_lp_bound_of_coeff (p := p) (W := 1) hp
      (mstLrBump_memLp P χ η hηcs hηsup s) (hcoef s).1 (fun n => rfl) (by norm_num)
      (hcoef s).2 (fun β => star (mstG P β)) (mstAnnulus l s)
      (fun β _ => by rw [norm_star]; exact mstG_norm_le_one P β) f
    simpa only [mstLrPiGCls, one_mul] using h
  -- the trivial `ℓᵖ` bound for the frozen term
  have htrivW : ∀ {p : ℝ}, 1 ≤ p → ∀ f : ℤ →₀ ℂ,
      MeasureTheory.eLpNorm (fun n : ℤ => Work.BourgainPlan.IonescuWainger.opMul
            (khatZMult P (mstLrJ s) • mstLrPiCls P l χ η hηcs hηsup s) (⇑f)
            (Work.BourgainPlan.IonescuWainger.memℓp_finsupp f) n) (ENNReal.ofReal p)
          MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (((mstAnnulus l s).card : ℝ) * Ccoef)
          * MeasureTheory.eLpNorm (⇑f) (ENNReal.ofReal p) MeasureTheory.Measure.count := by
    intro p hp f
    rw [opMul_khatZMult_smul_mstLrPiCls P l χ η hηcs hηsup (mstLrJ s) s (⇑f)
      (Work.BourgainPlan.IonescuWainger.memℓp_finsupp f)]
    refine (mstFreeze_discAvgZC_eLpNorm_le P (mstLrJ s) hp _).trans ?_
    have h := Work.BourgainPlan.KPWW.opArc_lp_bound_of_coeff hp
      (mstLrBump_memLp P χ η hηcs hηsup s) (hcoef s).1 (fun n => rfl) (hcoef s).2
      (mstAnnulus l s) (⇑f) (Work.BourgainPlan.IonescuWainger.memℓp_finsupp f)
    simpa only [mstLrPiCls, Work.BourgainPlan.IonescuWainger.opArc] using h
  by_cases hs : S₀ ≤ s
  · -- ================= large levels =================
    have hsae : Sae ≤ s := le_trans (le_max_left _ _) hs
    have hsarith : Sarith ≤ s := le_trans (le_max_right _ _) hs
    -- the `ℓ²` bound for the error class
    have htwo : ∀ f : ℤ →₀ ℂ,
        MeasureTheory.eLpNorm (fun n : ℤ => Work.BourgainPlan.IonescuWainger.opMul
              (mstLrPiGCls P l χ η hηcs hηsup s
                - khatZMult P (mstLrJ s) • mstLrPiCls P l χ η hηcs hηsup s) (⇑f)
              (Work.BourgainPlan.IonescuWainger.memℓp_finsupp f) n)
            (ENNReal.ofReal 2) MeasureTheory.Measure.count
          ≤ ENNReal.ofReal (max Cae 1 * Real.exp (-(Real.sqrt ((s : ℝ) + 1) / 2)))
            * MeasureTheory.eLpNorm (⇑f) (ENNReal.ofReal 2) MeasureTheory.Measure.count := by
      intro f
      have hμ : 0 ≤ max Cae 1 * Real.exp (-(Real.sqrt ((s : ℝ) + 1) / 2)) := by positivity
      have hae : ∀ᵐ ξ ∂haarT,
          ‖((mstLrPiGCls P l χ η hηcs hηsup s
              - khatZMult P (mstLrJ s) • mstLrPiCls P l χ η hηcs hηsup s :
                Lp ℂ ⊤ haarT) : Circ → ℂ) ξ‖
            ≤ max Cae 1 * Real.exp (-(Real.sqrt ((s : ℝ) + 1) / 2)) := by
        have hbase := hAe s hsae
        filter_upwards [hbase] with ξ hξ
        refine hξ.trans ?_
        exact mul_le_mul_of_nonneg_right (le_max_left Cae (1 : ℝ)) (Real.exp_nonneg _)
      exact eLpNorm_two_opMul_le (Φ := mstLrPiGCls P l χ η hηcs hηsup s
          - khatZMult P (mstLrJ s) • mstLrPiCls P l χ η hηcs hηsup s) (f := ⇑f)
        (Work.BourgainPlan.IonescuWainger.memℓp_finsupp f) hμ hae
    -- the trivial `ℓ^{r₀}` bound for the error class
    have htrivD : ∀ f : ℤ →₀ ℂ,
        MeasureTheory.eLpNorm (fun n : ℤ => Work.BourgainPlan.IonescuWainger.opMul
              (mstLrPiGCls P l χ η hηcs hηsup s
                - khatZMult P (mstLrJ s) • mstLrPiCls P l χ η hηcs hηsup s) (⇑f)
              (Work.BourgainPlan.IonescuWainger.memℓp_finsupp f) n)
            (ENNReal.ofReal r₀) MeasureTheory.Measure.count
          ≤ ENNReal.ofReal (max (2 * Ccoef * Ccard) 1
              * Real.exp (((s : ℝ) + 1) ^ (1 / 10 : ℝ)))
            * MeasureTheory.eLpNorm (⇑f) (ENNReal.ofReal r₀) MeasureTheory.Measure.count := by
      intro f
      have hsub : Work.BourgainPlan.IonescuWainger.opMul
            (mstLrPiGCls P l χ η hηcs hηsup s
              - khatZMult P (mstLrJ s) • mstLrPiCls P l χ η hηcs hηsup s) (⇑f)
            (Work.BourgainPlan.IonescuWainger.memℓp_finsupp f)
          = Work.BourgainPlan.IonescuWainger.opMul (mstLrPiGCls P l χ η hηcs hηsup s)
              (⇑f) (Work.BourgainPlan.IonescuWainger.memℓp_finsupp f)
            - Work.BourgainPlan.IonescuWainger.opMul
                (khatZMult P (mstLrJ s) • mstLrPiCls P l χ η hηcs hηsup s) (⇑f)
                (Work.BourgainPlan.IonescuWainger.memℓp_finsupp f) :=
        (Work.BourgainPlan.IonescuWainger.opMul_sub _ _ _ _).symm
      rw [hsub]
      refine (eLpNorm_sub_le (ENNReal.one_le_ofReal.mpr hr₀.le)).trans ?_
      refine (add_le_add (htrivG hr₀.le f) (htrivW hr₀.le f)).trans ?_
      rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
      refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) bot_le
      have hexp1 : (1 : ℝ) ≤ Real.exp (((s : ℝ) + 1) ^ (1 / 10 : ℝ)) :=
        Real.one_le_exp (by positivity)
      have hrew : (2 : ℝ) * (((mstAnnulus l s).card : ℝ) * Ccoef)
          ≤ 2 * (Ccard * Real.exp (((s : ℝ) + 1) ^ (1 / 10 : ℝ)) * Ccoef) := by
        nlinarith [hcard_exp, hCcoefpos.le]
      have hrew2 : 2 * (Ccard * Real.exp (((s : ℝ) + 1) ^ (1 / 10 : ℝ)) * Ccoef)
          ≤ max (2 * Ccoef * Ccard) 1 * Real.exp (((s : ℝ) + 1) ^ (1 / 10 : ℝ)) := by
        have h2 : 2 * (Ccard * Real.exp (((s : ℝ) + 1) ^ (1 / 10 : ℝ)) * Ccoef)
            = (2 * Ccoef * Ccard) * Real.exp (((s : ℝ) + 1) ^ (1 / 10 : ℝ)) := by ring
        rw [h2]
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) (le_trans zero_le_one hexp1)
      have hsum : ((mstAnnulus l s).card : ℝ) * Ccoef + ((mstAnnulus l s).card : ℝ) * Ccoef
          = 2 * (((mstAnnulus l s).card : ℝ) * Ccoef) := by ring
      rw [hsum]
      linarith [hrew, hrew2]
    -- the interpolated `ℓʳ` bound for the error class
    have hErr : MeasureTheory.eLpNorm (fun n : ℤ => Work.BourgainPlan.IonescuWainger.opMul
          (mstLrPiGCls P l χ η hηcs hηsup s
            - khatZMult P (mstLrJ s) • mstLrPiCls P l χ η hηcs hηsup s) (⇑g)
          (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g) n)
          (ENNReal.ofReal r) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal Carith
          * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal r) MeasureTheory.Measure.count := by
      have hApos : 0 < max (2 * Ccoef * Ccard) 1 * Real.exp (((s : ℝ) + 1) ^ (1 / 10 : ℝ)) := by
        have h1 : (0 : ℝ) < max (2 * Ccoef * Ccard) 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
        positivity
      have hBpos : 0 < max Cae 1 * Real.exp (-(Real.sqrt ((s : ℝ) + 1) / 2)) := by
        have h1 : (0 : ℝ) < max Cae 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
        positivity
      have hkey := opMulFinsuppLM_interp
        (mstLrPiGCls P l χ η hηcs hηsup s
          - khatZMult P (mstLrJ s) • mstLrPiCls P l χ η hηcs hηsup s)
        (r := r₀) (p := r)
        (A := max (2 * Ccoef * Ccard) 1 * Real.exp (((s : ℝ) + 1) ^ (1 / 10 : ℝ)))
        (B := max Cae 1 * Real.exp (-(Real.sqrt ((s : ℝ) + 1) / 2)))
        hr₀ hr₀r hr2 hApos hBpos htrivD htwo g
      have hkey' : MeasureTheory.eLpNorm (fun n : ℤ => Work.BourgainPlan.IonescuWainger.opMul
            (mstLrPiGCls P l χ η hηcs hηsup s
              - khatZMult P (mstLrJ s) • mstLrPiCls P l χ η hηcs hηsup s) (⇑g)
            (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g) n)
            (ENNReal.ofReal r) MeasureTheory.Measure.count
          ≤ ENNReal.ofReal
              ((max (2 * Ccoef * Ccard) 1 * Real.exp (((s : ℝ) + 1) ^ (1 / 10 : ℝ)))
                  ^ (1 - (1 / r₀ - 1 / r) / (1 / r₀ - 1 / 2))
                * (max Cae 1 * Real.exp (-(Real.sqrt ((s : ℝ) + 1) / 2)))
                  ^ ((1 / r₀ - 1 / r) / (1 / r₀ - 1 / 2)))
            * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal r) MeasureTheory.Measure.count := by
        rw [opMulFinsuppLM_apply] at hkey
        exact hkey
      refine hkey'.trans ?_
      refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) bot_le
      have har := harith s hsarith
      have hexp_le : Real.exp (-(carith * Real.sqrt ((s : ℝ) + 1))) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        exact neg_nonpos.mpr (mul_nonneg hcarithpos.le (Real.sqrt_nonneg _))
      calc (max (2 * Ccoef * Ccard) 1 * Real.exp (((s : ℝ) + 1) ^ (1 / 10 : ℝ)))
              ^ (1 - (1 / r₀ - 1 / r) / (1 / r₀ - 1 / 2))
            * (max Cae 1 * Real.exp (-(Real.sqrt ((s : ℝ) + 1) / 2)))
              ^ ((1 / r₀ - 1 / r) / (1 / r₀ - 1 / 2))
          ≤ Carith * Real.exp (-(carith * Real.sqrt ((s : ℝ) + 1))) := har
        _ ≤ Carith * 1 := mul_le_mul_of_nonneg_left hexp_le hCarithpos.le
        _ = Carith := mul_one _
    -- the main (frozen) term
    have hmain : MeasureTheory.eLpNorm (fun n : ℤ => Work.BourgainPlan.IonescuWainger.opMul
          (khatZMult P (mstLrJ s) • mstLrPiCls P l χ η hηcs hηsup s) (⇑g)
          (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g) n)
          (ENNReal.ofReal r) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal Ciw
          * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal r) MeasureTheory.Measure.count := by
      rw [opMul_khatZMult_smul_mstLrPiCls P l χ η hηcs hηsup (mstLrJ s) s (⇑g)
        (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g)]
      refine (mstFreeze_discAvgZC_eLpNorm_le P (mstLrJ s) hr.le _).trans ?_
      have h := hIw s g
      simpa only [mstLrPiCls, Work.BourgainPlan.IonescuWainger.opArc] using h
    -- decompose and combine
    have hdecomp : Work.BourgainPlan.IonescuWainger.opMul (hπ.toLp (mstWidePiG P l χ η s))
          (⇑g) (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g)
        = Work.BourgainPlan.IonescuWainger.opMul
            (mstLrPiGCls P l χ η hηcs hηsup s
              - khatZMult P (mstLrJ s) • mstLrPiCls P l χ η hηcs hηsup s) (⇑g)
            (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g)
          + Work.BourgainPlan.IonescuWainger.opMul
              (khatZMult P (mstLrJ s) • mstLrPiCls P l χ η hηcs hηsup s) (⇑g)
              (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g) := by
      rw [mstWidePiG_toLp_eq P l χ η hηcs hηsup s,
        ← Work.BourgainPlan.IonescuWainger.opMul_sub]
      ring
    have hbound : MeasureTheory.eLpNorm (fun m : ℤ =>
          ‖Work.BourgainPlan.IonescuWainger.opMul (hπ.toLp (mstWidePiG P l χ η s)) (⇑g)
            (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g) m‖ₑ)
          (ENNReal.ofReal r) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (Carith + Ciw)
          * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal r) MeasureTheory.Measure.count := by
      rw [MeasureTheory.eLpNorm_enorm _ (measurable_of_countable _).aestronglyMeasurable, hdecomp]
      refine (eLpNorm_add_le (ENNReal.one_le_ofReal.mpr hr.le)).trans ?_
      refine (add_le_add hErr hmain).trans ?_
      rw [← add_mul, ← ENNReal.ofReal_add hCarithpos.le hCiwpos.le]
    refine hbound.trans ?_
    refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) bot_le
    have hlogmono : Real.log 2 ≤ Real.log ((s : ℝ) + 2) :=
      Real.log_le_log (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) s])
    have h1 : Cfin * Real.log 2 ≤ Cfin * Real.log ((s : ℝ) + 2) :=
      mul_le_mul_of_nonneg_left hlogmono (le_of_lt hCfinpos)
    linarith [hCfin_big, h1, hKsmallpos]
  · -- ================= small levels =================
    have htriv : MeasureTheory.eLpNorm (fun m : ℤ =>
          ‖Work.BourgainPlan.IonescuWainger.opMul (hπ.toLp (mstWidePiG P l χ η s)) (⇑g)
            (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g) m‖ₑ)
          (ENNReal.ofReal r) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal Ksmall
          * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal r) MeasureTheory.Measure.count := by
      rw [MeasureTheory.eLpNorm_enorm _ (measurable_of_countable _).aestronglyMeasurable, mstWidePiG_toLp_eq P l χ η hηcs hηsup s]
      refine (htrivG hr.le g).trans ?_
      refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) bot_le
      have hle : s + 1 ≤ S₀ + 1 := by omega
      have hsub2 : mstU l (s + 1) ⊆ mstU l (S₀ + 1) :=
        sigmaN_nested (mstRho l) (Nat.pow_le_pow_left hle l)
      have hc1 : (mstAnnulus l s).card ≤ (mstU l (S₀ + 1)).card :=
        le_trans (Finset.card_le_card hEsub) (Finset.card_le_card hsub2)
      have hc2 : ((mstAnnulus l s).card : ℝ) ≤ ((mstU l (S₀ + 1)).card : ℝ) := by
        exact_mod_cast hc1
      have hc3 : ((mstAnnulus l s).card : ℝ) * Ccoef ≤ Ksmall := by
        rw [hKsmalldef]
        nlinarith [hc2, hCcoefpos.le]
      linarith [hc3]
    refine htriv.trans ?_
    refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) bot_le
    have hlogmono : Real.log 2 ≤ Real.log ((s : ℝ) + 2) :=
      Real.log_le_log (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) s])
    have h1 : Cfin * Real.log 2 ≤ Cfin * Real.log ((s : ℝ) + 2) :=
      mul_le_mul_of_nonneg_left hlogmono (le_of_lt hCfinpos)
    linarith [hCfin_big, h1, hKsmallpos]


end

end Work.Maximal
