import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_lvl_defs
import Submission.Work.Maximal.mst_lrs_frozen_sup
import Submission.Work.BourgainPlan.Maximal.rmELpNormSupLe
import Submission.Work.BourgainPlan.Maximal.mst_minor_per_n
import Submission.Work.BourgainPlan.IonescuWainger.opMul_mul
import Submission.Work.BourgainPlan.IonescuWainger.opArc_strata_incl_excl
import Submission.Work.BourgainPlan.Maximal.discAvgZC_multiplier_z
import Submission.Commons.MeasureTheory.Lp.eLpNorm_finset_sum_le_ennreal

namespace Work.BourgainPlan.Maximal

open MeasureTheory Finset
open scoped BigOperators ENNReal
open Work.BourgainPlan.IonescuWainger

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

local notation "haarT" => (AddCircle.haarAddCircle (T := 1))

/-- `ENNReal.ofReal` of a sum, distributed over the two factors. -/
private lemma ofReal_mul_add_mul {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (N : ℝ≥0∞) :
    ENNReal.ofReal a * N + ENNReal.ofReal b * N = ENNReal.ofReal (a + b) * N := by
  rw [← add_mul, ← ENNReal.ofReal_add ha hb]

/-- Monotonicity of `ENNReal.ofReal · * N` in the real factor. -/
private lemma ofReal_mul_le_mul {a b : ℝ} (h : a ≤ b) (N : ℝ≥0∞) :
    ENNReal.ofReal a * N ≤ ENNReal.ofReal b * N :=
  mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal h) zero_le

/-- Combining the three `ENNReal.ofReal` factors of a product of `ofReal`s. -/
private lemma ofReal_mul_ofReal_mul_ofReal_mul {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (N : ℝ≥0∞) :
    ENNReal.ofReal a * (ENNReal.ofReal b * (ENNReal.ofReal c * N))
      = ENNReal.ofReal (a * b * c) * N := by
  conv_lhs => rw [← mul_assoc]
  rw [← ENNReal.ofReal_mul ha]
  conv_lhs => rw [← mul_assoc]
  rw [← ENNReal.ofReal_mul (mul_nonneg ha hb)]

/-- **The assembly of MST Theorem 7** from the four analytic pieces. -/
theorem mst_lvl_assembly
    (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (l : ℕ) (χ : ℝ) (η : ℝ → ℂ) (p : ℝ) (hp : 1 < p)
    (hML : ∀ n s : ℕ, MeasureTheory.MemLp (mstNuS P l P.natDegree χ η n s) ⊤ (AddCircle.haarAddCircle (T := 1)))
    (hηml : ∀ s : ℕ, MeasureTheory.MemLp (mstEta P.natDegree χ η s) ⊤ (AddCircle.haarAddCircle (T := 1)))
    (hlevel : ∃ C : ℝ, 0 < C ∧ ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s → ∀ (i : ℕ) (g : ℤ →₀ ℂ),
      MeasureTheory.eLpNorm (fun m : ℤ => ENNReal.ofReal (rmLevel (mstKappa P s) i
          (fun j : ℕ => ‖opMulFinsuppLM (mstPiCls P l P.natDegree χ η s (hηml s) (2 ^ j)) g m‖)))
          (ENNReal.ofReal p) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C * Real.log ((s : ℝ) + 2))
          * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal p) MeasureTheory.Measure.count)
    (hbase : ∃ C : ℝ, 0 < C ∧ ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s → ∀ g : ℤ →₀ ℂ,
      MeasureTheory.eLpNorm (fun m : ℤ =>
            opMulFinsuppLM (mstPiCls P l P.natDegree χ η s (hηml s) (2 ^ 0)) g m)
          (ENNReal.ofReal p) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C * Real.log ((s : ℝ) + 2))
          * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal p) MeasureTheory.Measure.count)
    (herr : ∃ C : ℝ, 0 < C ∧ ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s → ∀ k : ℕ, ∀ g : ℤ →₀ ℂ,
      MeasureTheory.eLpNorm (fun m : ℤ => opMulFinsuppLM
          (mstNuSCls P l P.natDegree χ η k s (hML k s)
            - khatZMult P (⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊)
              • mstPiCls P l P.natDegree χ η s (hηml s) (2 ^ k)) g m)
          (ENNReal.ofReal p) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C * Real.exp (-(Real.sqrt ((s : ℝ) + 1) / 4)))
          * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal p) MeasureTheory.Measure.count)
    (htriv : ∃ K : ℝ, 0 < K ∧ ∀ (s : ℕ) (k : ℕ) (g : ℤ →₀ ℂ),
      MeasureTheory.eLpNorm (fun m : ℤ => opMulFinsuppLM
            (mstNuSCls P l P.natDegree χ η k s (hML k s)) g m)
          (ENNReal.ofReal p) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (((mstU l (s + 1)).card : ℝ) * K)
          * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal p) MeasureTheory.Measure.count) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℕ, ∀ g : ℤ →₀ ℂ,
      MeasureTheory.eLpNorm (fun m : ℤ => (⨆ k ∈ Finset.range (2 ^ (mstKappa P s) + 1),
          ‖Work.BourgainPlan.IonescuWainger.opMul
            (mstNuSCls P l P.natDegree χ η k s (hML k s)) (⇑g)
            (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g) m‖ₑ))
          (ENNReal.ofReal p) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C * (((s : ℝ) + 1) * Real.log ((s : ℝ) + 2)))
          * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal p) MeasureTheory.Measure.count := by
  obtain ⟨Clev, hClevpos, slev, hlev⟩ := hlevel
  obtain ⟨Cbas, hCbaspos, sbas, hbas⟩ := hbase
  obtain ⟨Cerr, hCerrpos, serr, herr'⟩ := herr
  obtain ⟨Ktriv, hKtrivpos, htriv'⟩ := htriv
  obtain ⟨Sκ, hSκ⟩ := mstKappa_add_one_le P (by omega)
  obtain ⟨Sarith, hSarith⟩ := mstKappa_exp_le_one P (by omega)
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  obtain ⟨S₀, hslev, hsbas, hserr, hsSκ, hsSarith, hs2⟩ :
      ∃ S₀ : ℕ, slev ≤ S₀ ∧ sbas ≤ S₀ ∧ serr ≤ S₀ ∧ Sκ ≤ S₀ ∧ Sarith ≤ S₀ ∧ 2 ≤ S₀ :=
    ⟨slev + sbas + serr + Sκ + Sarith + 2,
      by omega, by omega, by omega, by omega, by omega, by omega⟩
  -- the constant
  set Cf : ℝ := max ((Cbas + 2 * Clev + Cerr) / Real.log 2 + 1)
      (((2 : ℝ) ^ (mstKappa P S₀ + 1) * (((mstU l S₀).card : ℝ) * Ktriv)) / Real.log 2 + 1)
    with hCf
  have hlog2le : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  refine ⟨Cf, ?_, ?_⟩
  · rw [hCf]
    have h0 : (0 : ℝ) < (Cbas + 2 * Clev + Cerr) / Real.log 2 + 1 := by
      have hnum : 0 < Cbas + 2 * Clev + Cerr := by linarith
      positivity
    exact lt_of_lt_of_le h0 (le_max_left _ _)
  · intro s g
    set Ln : ℝ := ((s : ℝ) + 1) * Real.log ((s : ℝ) + 2) with hLn
    have hs0 : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg s
    have h1s : (1 : ℝ) ≤ (s : ℝ) + 1 := by linarith
    have hlogspos : 0 < Real.log ((s : ℝ) + 2) := Real.log_pos (by linarith)
    have hLnn : 0 ≤ Ln := by
      rw [hLn]
      exact mul_nonneg (by linarith) hlogspos.le
    have hLge : Real.log 2 ≤ Ln := by
      rw [hLn]
      have h2 : Real.log 2 ≤ Real.log ((s : ℝ) + 2) :=
        Real.log_le_log (by norm_num) (by linarith)
      nlinarith [h1s, h2, hlog2]
    by_cases hs : s < S₀
    · -- small scales: crude bound with the (large) constant `Cf`
      have hsm : (2 ^ (mstKappa P s) + 1 : ℕ) ≤ 2 ^ (mstKappa P S₀ + 1) := by
        have h1 : mstKappa P s + 1 ≤ mstKappa P S₀ + 1 := by
          have := mstKappa_mono P (le_of_lt hs)
          omega
        calc (2 ^ (mstKappa P s) + 1 : ℕ) ≤ 2 ^ (mstKappa P s) + 2 ^ (mstKappa P s) := by
              have : 1 ≤ 2 ^ (mstKappa P s) := Nat.one_le_pow _ _ (by norm_num)
              omega
          _ = 2 * 2 ^ (mstKappa P s) := by ring
          _ = 2 ^ (mstKappa P s + 1) := by rw [pow_succ]; ring
          _ ≤ 2 ^ (mstKappa P S₀ + 1) := Nat.pow_le_pow_right (by norm_num) h1
      have hc : ((mstU l (s + 1)).card : ℝ) ≤ ((mstU l S₀).card : ℝ) := by
        exact_mod_cast mstU_card_mono l (by omega : s + 1 ≤ S₀)
      have hsup_le : ∀ m : ℤ, (⨆ k ∈ Finset.range (2 ^ (mstKappa P s) + 1),
            ‖Work.BourgainPlan.IonescuWainger.opMul
              (mstNuSCls P l P.natDegree χ η k s (hML k s)) (⇑g)
              (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g) m‖ₑ)
          ≤ ∑ k ∈ Finset.range (2 ^ (mstKappa P s) + 1),
              ‖Work.BourgainPlan.IonescuWainger.opMul
                (mstNuSCls P l P.natDegree χ η k s (hML k s)) (⇑g)
                (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g) m‖ₑ := by
        intro m
        refine iSup₂_le (fun k hk => ?_)
        exact Finset.single_le_sum (f := fun j : ℕ => ‖Work.BourgainPlan.IonescuWainger.opMul
            (mstNuSCls P l P.natDegree χ η j s (hML j s)) (⇑g)
            (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g) m‖ₑ) (fun i _ => zero_le) hk
      have h1 : MeasureTheory.eLpNorm (fun m : ℤ => (⨆ k ∈ Finset.range (2 ^ (mstKappa P s) + 1),
            ‖Work.BourgainPlan.IonescuWainger.opMul
              (mstNuSCls P l P.natDegree χ η k s (hML k s)) (⇑g)
              (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g) m‖ₑ))
            (ENNReal.ofReal p) MeasureTheory.Measure.count
          ≤ ∑ k ∈ Finset.range (2 ^ (mstKappa P s) + 1),
              MeasureTheory.eLpNorm (fun m : ℤ => ‖Work.BourgainPlan.IonescuWainger.opMul
                (mstNuSCls P l P.natDegree χ η k s (hML k s)) (⇑g)
                (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g) m‖ₑ)
              (ENNReal.ofReal p) MeasureTheory.Measure.count := by
        refine (eLpNorm_mono_enorm
            (f := fun m : ℤ => (⨆ k ∈ Finset.range (2 ^ (mstKappa P s) + 1),
              ‖Work.BourgainPlan.IonescuWainger.opMul
                (mstNuSCls P l P.natDegree χ η k s (hML k s)) (⇑g)
                (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g) m‖ₑ))
            (g := fun m : ℤ => ∑ k ∈ Finset.range (2 ^ (mstKappa P s) + 1),
              ‖Work.BourgainPlan.IonescuWainger.opMul
                (mstNuSCls P l P.natDegree χ η k s (hML k s)) (⇑g)
                (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g) m‖ₑ)
            AEStronglyMeasurable.of_discrete (fun m => ?_)).trans ?_
        · rw [enorm_eq_self, enorm_eq_self]
          exact hsup_le m
        · exact Commons.MeasureTheory.Lp.eLpNorm_finset_sum_le_ennreal
            (ENNReal.one_le_ofReal.mpr hp.le)
            (fun k _ => (measurable_of_countable _).aemeasurable)
      have h2 : (∑ k ∈ Finset.range (2 ^ (mstKappa P s) + 1),
              MeasureTheory.eLpNorm (fun m : ℤ => ‖Work.BourgainPlan.IonescuWainger.opMul
                (mstNuSCls P l P.natDegree χ η k s (hML k s)) (⇑g)
                (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g) m‖ₑ)
              (ENNReal.ofReal p) MeasureTheory.Measure.count)
          ≤ ((2 ^ (mstKappa P s) + 1 : ℕ) : ℝ≥0∞)
              * (ENNReal.ofReal (((mstU l (s + 1)).card : ℝ) * Ktriv)
                * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal p) MeasureTheory.Measure.count) := by
        calc (∑ k ∈ Finset.range (2 ^ (mstKappa P s) + 1),
              MeasureTheory.eLpNorm (fun m : ℤ => ‖Work.BourgainPlan.IonescuWainger.opMul
                (mstNuSCls P l P.natDegree χ η k s (hML k s)) (⇑g)
                (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g) m‖ₑ)
              (ENNReal.ofReal p) MeasureTheory.Measure.count)
            ≤ ∑ k ∈ Finset.range (2 ^ (mstKappa P s) + 1),
                ENNReal.ofReal (((mstU l (s + 1)).card : ℝ) * Ktriv)
                * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal p) MeasureTheory.Measure.count := by
              refine Finset.sum_le_sum (fun k _ => ?_)
              refine (le_of_eq ?_).trans (htriv' s k g)
              exact eLpNorm_enorm (opMulFinsuppLM (mstNuSCls P l P.natDegree χ η k s
                (hML k s)) g) (ENNReal.ofReal p)
          _ = ((2 ^ (mstKappa P s) + 1 : ℕ) : ℝ≥0∞)
                * (ENNReal.ofReal (((mstU l (s + 1)).card : ℝ) * Ktriv)
                  * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal p) MeasureTheory.Measure.count) := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hXnat : ((2 ^ (mstKappa P s) + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (mstKappa P S₀ + 1) := by
        have hcast : ((2 ^ (mstKappa P s) + 1 : ℕ) : ℝ)
            ≤ ((2 ^ (mstKappa P S₀ + 1) : ℕ) : ℝ) := by exact_mod_cast hsm
        calc ((2 ^ (mstKappa P s) + 1 : ℕ) : ℝ) ≤ ((2 ^ (mstKappa P S₀ + 1) : ℕ) : ℝ) := hcast
          _ = (2 : ℝ) ^ (mstKappa P S₀ + 1) := by push_cast; ring
      have hAnat : ((mstU l (s + 1)).card : ℝ) * Ktriv ≤ ((mstU l S₀).card : ℝ) * Ktriv :=
        mul_le_mul_of_nonneg_right hc hKtrivpos.le
      have hkey : ((2 ^ (mstKappa P s) + 1 : ℕ) : ℝ) * (((mstU l (s + 1)).card : ℝ) * Ktriv)
          ≤ Cf * Ln := by
        have hmul : ((2 ^ (mstKappa P s) + 1 : ℕ) : ℝ) * (((mstU l (s + 1)).card : ℝ) * Ktriv)
            ≤ (2 : ℝ) ^ (mstKappa P S₀ + 1) * (((mstU l S₀).card : ℝ) * Ktriv) :=
          mul_le_mul hXnat hAnat (by positivity) (by positivity)
        refine hmul.trans ?_
        have hCge : ((2 : ℝ) ^ (mstKappa P S₀ + 1) * (((mstU l S₀).card : ℝ) * Ktriv))
              / Real.log 2 + 1 ≤ Cf := by
          rw [hCf]; exact le_max_right _ _
        calc (2 : ℝ) ^ (mstKappa P S₀ + 1) * (((mstU l S₀).card : ℝ) * Ktriv)
            = (2 : ℝ) ^ (mstKappa P S₀ + 1) * (((mstU l S₀).card : ℝ) * Ktriv)
                / Real.log 2 * Real.log 2 := by
              rw [div_mul_cancel₀ _ hlog2.ne']
          _ ≤ (2 : ℝ) ^ (mstKappa P S₀ + 1) * (((mstU l S₀).card : ℝ) * Ktriv)
                / Real.log 2 * Ln :=
              mul_le_mul_of_nonneg_left hLge (div_nonneg (by positivity) hlog2.le)
          _ ≤ (((2 : ℝ) ^ (mstKappa P S₀ + 1) * (((mstU l S₀).card : ℝ) * Ktriv))
                / Real.log 2 + 1) * Ln :=
              mul_le_mul_of_nonneg_right (by linarith) hLnn
          _ ≤ Cf * Ln := mul_le_mul_of_nonneg_right hCge hLnn
      refine h1.trans (h2.trans ?_)
      rw [← mul_assoc]
      refine mul_le_mul_of_nonneg_right ?_ (zero_le)
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
      exact ENNReal.ofReal_le_ofReal hkey
    · -- large scales
      push_neg at hs
      have hslev' : slev ≤ s := le_trans hslev hs
      have hsbas' : sbas ≤ s := le_trans hsbas hs
      have hserr' : serr ≤ s := le_trans hserr hs
      have hsSκ' : Sκ ≤ s := le_trans hsSκ hs
      have hsSarith' : Sarith ≤ s := le_trans hsSarith hs
      have hκle : mstKappa P s + 1 ≤ s + 1 := hSκ s hsSκ'
      -- the `Π`-operators
      set T : ℕ → (ℤ →₀ ℂ) →ₗ[ℂ] (ℤ → ℂ) :=
        fun k => opMulFinsuppLM (mstPiCls P l P.natDegree χ η s (hηml s) (2 ^ k)) with hT
      have hTapp : ∀ (k : ℕ) (h : ℤ →₀ ℂ), T k h = opMulFinsuppLM
          (mstPiCls P l P.natDegree χ η s (hηml s) (2 ^ k)) h := fun k h => rfl
      -- the RM bound
      have hrm := rm_iSup_bound (mstKappa P s) T hp.le g
      -- the level terms
      have hlev' : ∀ i : ℕ, MeasureTheory.eLpNorm (fun m : ℤ => ENNReal.ofReal
            (rmLevel (mstKappa P s) i (fun j : ℕ => ‖T j g m‖)))
            (ENNReal.ofReal p) MeasureTheory.Measure.count
          ≤ ENNReal.ofReal (Clev * Real.log ((s : ℝ) + 2))
            * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal p) MeasureTheory.Measure.count :=
        fun i => hlev s hslev' i g
      have hbas'' : MeasureTheory.eLpNorm (fun m : ℤ => ‖T 0 g m‖ₑ) (ENNReal.ofReal p)
            MeasureTheory.Measure.count
          ≤ ENNReal.ofReal (Cbas * Real.log ((s : ℝ) + 2))
            * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal p) MeasureTheory.Measure.count := by
        have h := hbas s hsbas' g
        exact (le_of_eq (eLpNorm_enorm ((T 0) g) (ENNReal.ofReal p))).trans h
      have hClevlog : 0 ≤ Clev * Real.log ((s : ℝ) + 2) := (mul_pos hClevpos hlogspos).le
      have hCbaslog : 0 ≤ Cbas * Real.log ((s : ℝ) + 2) := (mul_pos hCbaspos hlogspos).le
      have hs1nn : 0 ≤ (s : ℝ) + 1 := by linarith
      have h2clev : 0 ≤ (2 * Clev * ((s : ℝ) + 1)) * Real.log ((s : ℝ) + 2) :=
        mul_nonneg (by positivity) hlogspos.le
      -- the `2^κ + 1` level terms, with the `s + 1` factor
      have hPiS : ENNReal.ofReal 2 * ∑ i ∈ Finset.range (mstKappa P s + 1),
            MeasureTheory.eLpNorm (fun m : ℤ => ENNReal.ofReal
              (rmLevel (mstKappa P s) i (fun j : ℕ => ‖T j g m‖)))
            (ENNReal.ofReal p) MeasureTheory.Measure.count
          ≤ ENNReal.ofReal ((2 * Clev * ((s : ℝ) + 1)) * Real.log ((s : ℝ) + 2))
            * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal p) MeasureTheory.Measure.count := by
        have hcast : ((mstKappa P s + 1 : ℕ) : ℝ≥0∞) ≤ ENNReal.ofReal ((s : ℝ) + 1) := by
          rw [← ENNReal.ofReal_natCast]
          exact ENNReal.ofReal_le_ofReal (by exact_mod_cast hκle)
        calc ENNReal.ofReal 2 * ∑ i ∈ Finset.range (mstKappa P s + 1),
              MeasureTheory.eLpNorm (fun m : ℤ => ENNReal.ofReal
                (rmLevel (mstKappa P s) i (fun j : ℕ => ‖T j g m‖)))
              (ENNReal.ofReal p) MeasureTheory.Measure.count
            ≤ ENNReal.ofReal 2 * (((mstKappa P s + 1 : ℕ) : ℝ≥0∞)
                * (ENNReal.ofReal (Clev * Real.log ((s : ℝ) + 2))
                  * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal p)
                    MeasureTheory.Measure.count)) := by
              refine mul_le_mul_of_nonneg_left ?_ (zero_le)
              calc (∑ i ∈ Finset.range (mstKappa P s + 1),
                    MeasureTheory.eLpNorm (fun m : ℤ => ENNReal.ofReal
                      (rmLevel (mstKappa P s) i (fun j : ℕ => ‖T j g m‖)))
                    (ENNReal.ofReal p) MeasureTheory.Measure.count)
                  ≤ ∑ i ∈ Finset.range (mstKappa P s + 1),
                      (ENNReal.ofReal (Clev * Real.log ((s : ℝ) + 2))
                        * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal p)
                          MeasureTheory.Measure.count) :=
                    Finset.sum_le_sum (fun i _ => hlev' i)
                _ = ((mstKappa P s + 1 : ℕ) : ℝ≥0∞)
                      * (ENNReal.ofReal (Clev * Real.log ((s : ℝ) + 2))
                        * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal p)
                          MeasureTheory.Measure.count) := by
                    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          _ ≤ ENNReal.ofReal 2 * (ENNReal.ofReal ((s : ℝ) + 1)
                * (ENNReal.ofReal (Clev * Real.log ((s : ℝ) + 2))
                  * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal p)
                    MeasureTheory.Measure.count)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcast (zero_le)) (zero_le)
          _ = ENNReal.ofReal (2 * ((s : ℝ) + 1) * (Clev * Real.log ((s : ℝ) + 2)))
                * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal p) MeasureTheory.Measure.count := by
              rw [ofReal_mul_ofReal_mul_ofReal_mul (ha := by norm_num) (hb := by positivity)]
          _ ≤ ENNReal.ofReal ((2 * Clev * ((s : ℝ) + 1)) * Real.log ((s : ℝ) + 2))
                * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal p) MeasureTheory.Measure.count := by
              exact ofReal_mul_le_mul (le_of_eq (by ring)) _
      -- the maximal inequality for the `Π`-family
      have hPi : MeasureTheory.eLpNorm (fun m : ℤ => ⨆ k ∈ Finset.range (2 ^ (mstKappa P s) + 1),
            ‖T k g m‖ₑ) (ENNReal.ofReal p) MeasureTheory.Measure.count
          ≤ ENNReal.ofReal ((Cbas + 2 * Clev * ((s : ℝ) + 1)) * Real.log ((s : ℝ) + 2))
            * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal p) MeasureTheory.Measure.count := by
        have hsum1 : Cbas * Real.log ((s : ℝ) + 2)
            + (2 * Clev * ((s : ℝ) + 1)) * Real.log ((s : ℝ) + 2)
            = (Cbas + 2 * Clev * ((s : ℝ) + 1)) * Real.log ((s : ℝ) + 2) := by ring
        calc MeasureTheory.eLpNorm (fun m : ℤ => ⨆ k ∈ Finset.range (2 ^ (mstKappa P s) + 1),
              ‖T k g m‖ₑ) (ENNReal.ofReal p) MeasureTheory.Measure.count
            ≤ MeasureTheory.eLpNorm (fun m : ℤ => ‖T 0 g m‖ₑ) (ENNReal.ofReal p)
                MeasureTheory.Measure.count
              + ENNReal.ofReal 2 * ∑ i ∈ Finset.range (mstKappa P s + 1),
                MeasureTheory.eLpNorm (fun m : ℤ => ENNReal.ofReal
                  (rmLevel (mstKappa P s) i (fun j : ℕ => ‖T j g m‖)))
                (ENNReal.ofReal p) MeasureTheory.Measure.count := hrm
          _ ≤ ENNReal.ofReal (Cbas * Real.log ((s : ℝ) + 2))
                * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal p) MeasureTheory.Measure.count
              + ENNReal.ofReal ((2 * Clev * ((s : ℝ) + 1)) * Real.log ((s : ℝ) + 2))
                * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal p) MeasureTheory.Measure.count :=
              add_le_add hbas'' hPiS
          _ = ENNReal.ofReal ((Cbas + 2 * Clev * ((s : ℝ) + 1)) * Real.log ((s : ℝ) + 2))
                * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal p) MeasureTheory.Measure.count := by
              rw [ofReal_mul_add_mul (ha := hCbaslog) (hb := h2clev), hsum1]
      -- the frozen density average step
      have hdisc : MeasureTheory.eLpNorm (fun m : ℤ => (⨆ k ∈ Finset.range (2 ^ (mstKappa P s) + 1),
            ‖discAvgZC P (⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊) (T k g) m‖ₑ))
            (ENNReal.ofReal p) MeasureTheory.Measure.count
          ≤ ENNReal.ofReal ((Cbas + 2 * Clev) * Ln)
            * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal p) MeasureTheory.Measure.count := by
        have hd := eLpNorm_discAvg_iSup_le P (⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊)
          (2 ^ (mstKappa P s) + 1) (Nat.floor_pos.mpr (Real.one_le_exp (by positivity)))
          (fun k : ℕ => T k g) hp.le
        refine hd.trans (hPi.trans ?_)
        have hAs : Cbas + 2 * Clev * ((s : ℝ) + 1) ≤ (Cbas + 2 * Clev) * ((s : ℝ) + 1) := by
          have hCs : 0 ≤ Cbas * (s : ℝ) := mul_nonneg hCbaspos.le hs0
          nlinarith [hCs]
        have hreal : (Cbas + 2 * Clev * ((s : ℝ) + 1)) * Real.log ((s : ℝ) + 2)
            ≤ (Cbas + 2 * Clev) * Ln := by
          calc (Cbas + 2 * Clev * ((s : ℝ) + 1)) * Real.log ((s : ℝ) + 2)
              ≤ ((Cbas + 2 * Clev) * ((s : ℝ) + 1)) * Real.log ((s : ℝ) + 2) :=
                mul_le_mul_of_nonneg_right hAs hlogspos.le
            _ = (Cbas + 2 * Clev) * Ln := by rw [hLn]; ring
        exact ofReal_mul_le_mul hreal
          (MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal p) MeasureTheory.Measure.count)
      -- the freezing error terms
      have herrterm : ∀ k ∈ Finset.range (2 ^ (mstKappa P s) + 1),
          MeasureTheory.eLpNorm (fun m : ℤ => ‖opMulFinsuppLM
              (mstNuSCls P l P.natDegree χ η k s (hML k s)
                - khatZMult P (⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊)
                  • mstPiCls P l P.natDegree χ η s (hηml s) (2 ^ k)) g m‖ₑ)
              (ENNReal.ofReal p) MeasureTheory.Measure.count
            ≤ ENNReal.ofReal (Cerr * Real.exp (-(Real.sqrt ((s : ℝ) + 1) / 4)))
              * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal p) MeasureTheory.Measure.count :=
        fun k _ => (le_of_eq (eLpNorm_enorm (opMulFinsuppLM
            (mstNuSCls P l P.natDegree χ η k s (hML k s)
              - khatZMult P (⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊)
                • mstPiCls P l P.natDegree χ η s (hηml s) (2 ^ k)) g)
            (ENNReal.ofReal p))).trans (herr' s hserr' k g)
      have herrsum : MeasureTheory.eLpNorm (fun m : ℤ =>
            ∑ k ∈ Finset.range (2 ^ (mstKappa P s) + 1),
              ‖opMulFinsuppLM
                (mstNuSCls P l P.natDegree χ η k s (hML k s)
                  - khatZMult P (⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊)
                    • mstPiCls P l P.natDegree χ η s (hηml s) (2 ^ k)) g m‖ₑ)
            (ENNReal.ofReal p) MeasureTheory.Measure.count
          ≤ ENNReal.ofReal ((Cerr / Real.log 2) * Ln)
            * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal p) MeasureTheory.Measure.count := by
        have hsum := (Commons.MeasureTheory.Lp.eLpNorm_finset_sum_le_ennreal
          (α := ℤ) (μ := MeasureTheory.Measure.count)
          (s := Finset.range (2 ^ (mstKappa P s) + 1))
          (ENNReal.one_le_ofReal.mpr hp.le)
          (fun k _ => (measurable_of_countable _).aemeasurable)
          (g := fun k (m : ℤ) => ‖opMulFinsuppLM
              (mstNuSCls P l P.natDegree χ η k s (hML k s)
                - khatZMult P (⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊)
                  • mstPiCls P l P.natDegree χ η s (hηml s) (2 ^ k)) g m‖ₑ))
        refine hsum.trans ((Finset.sum_le_sum herrterm).trans ?_)
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        have hcardnat : ((2 ^ (mstKappa P s) + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (mstKappa P s + 1) := by
          have h0 : (1 : ℕ) ≤ 2 ^ mstKappa P s := Nat.one_le_pow _ _ (by norm_num)
          have hle : (2 ^ (mstKappa P s) + 1 : ℕ) ≤ 2 ^ (mstKappa P s + 1) := by
            calc 2 ^ mstKappa P s + 1 ≤ 2 ^ mstKappa P s + 2 ^ mstKappa P s := by omega
              _ = 2 ^ (mstKappa P s + 1) := by rw [pow_succ]; ring
          exact_mod_cast hle
        have hcoe : (2 : ℝ) ^ (mstKappa P s + 1)
              * (Cerr * Real.exp (-(Real.sqrt ((s : ℝ) + 1) / 4)))
            ≤ (Cerr / Real.log 2) * Ln := by
          have hexp1 := hSarith s hsSarith'
          have hone : Cerr * ((2 : ℝ) ^ (mstKappa P s + 1)
              * Real.exp (-(Real.sqrt ((s : ℝ) + 1) / 4))) ≤ Cerr * 1 :=
            mul_le_mul_of_nonneg_left hexp1 hCerrpos.le
          have hLgeq : (1 : ℝ) ≤ Ln / Real.log 2 := by
            rw [le_div_iff₀ hlog2, one_mul]; exact hLge
          calc (2 : ℝ) ^ (mstKappa P s + 1)
                * (Cerr * Real.exp (-(Real.sqrt ((s : ℝ) + 1) / 4)))
              = Cerr * ((2 : ℝ) ^ (mstKappa P s + 1)
                  * Real.exp (-(Real.sqrt ((s : ℝ) + 1) / 4))) := by ring
            _ ≤ Cerr * 1 := hone
            _ = Cerr := mul_one _
            _ ≤ Cerr * (Ln / Real.log 2) := by
              simpa using mul_le_mul_of_nonneg_left hLgeq hCerrpos.le
            _ = (Cerr / Real.log 2) * Ln := by ring
        calc ((2 ^ (mstKappa P s) + 1 : ℕ) : ℝ≥0∞)
              * (ENNReal.ofReal (Cerr * Real.exp (-(Real.sqrt ((s : ℝ) + 1) / 4)))
                * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal p) MeasureTheory.Measure.count)
            = ((2 ^ (mstKappa P s) + 1 : ℕ) : ℝ≥0∞)
                * ENNReal.ofReal (Cerr * Real.exp (-(Real.sqrt ((s : ℝ) + 1) / 4)))
              * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal p) MeasureTheory.Measure.count := by
              rw [← mul_assoc]
          _ ≤ ENNReal.ofReal ((2 : ℝ) ^ (mstKappa P s + 1))
                * ENNReal.ofReal (Cerr * Real.exp (-(Real.sqrt ((s : ℝ) + 1) / 4)))
              * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal p) MeasureTheory.Measure.count := by
              refine mul_le_mul_of_nonneg_right ?_ (zero_le)
              refine mul_le_mul_of_nonneg_right ?_ (zero_le)
              rw [← ENNReal.ofReal_natCast]
              exact ENNReal.ofReal_le_ofReal hcardnat
          _ = ENNReal.ofReal ((2 : ℝ) ^ (mstKappa P s + 1)
                * (Cerr * Real.exp (-(Real.sqrt ((s : ℝ) + 1) / 4))))
              * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal p) MeasureTheory.Measure.count := by
              rw [← ENNReal.ofReal_mul (by positivity)]
          _ ≤ ENNReal.ofReal ((Cerr / Real.log 2) * Ln)
              * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal p) MeasureTheory.Measure.count :=
              ofReal_mul_le_mul hcoe
                (MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal p) MeasureTheory.Measure.count)
      -- the pointwise reduction of the level model to the frozen model plus freezing error
      have hpoint : ∀ m : ℤ, (⨆ k ∈ Finset.range (2 ^ (mstKappa P s) + 1),
            ‖Work.BourgainPlan.IonescuWainger.opMul
              (mstNuSCls P l P.natDegree χ η k s (hML k s)) (⇑g)
              (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g) m‖ₑ)
          ≤ (⨆ k ∈ Finset.range (2 ^ (mstKappa P s) + 1), ‖discAvgZC P
                (⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊) (T k g) m‖ₑ)
            + ∑ k ∈ Finset.range (2 ^ (mstKappa P s) + 1),
                ‖opMulFinsuppLM
                  (mstNuSCls P l P.natDegree χ η k s (hML k s)
                    - khatZMult P (⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊)
                      • mstPiCls P l P.natDegree χ η s (hηml s) (2 ^ k)) g m‖ₑ := by
        intro m
        refine iSup₂_le (fun k hk => ?_)
        have hsplit : mstNuSCls P l P.natDegree χ η k s (hML k s)
            = khatZMult P (⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊)
                • mstPiCls P l P.natDegree χ η s (hηml s) (2 ^ k)
              + (mstNuSCls P l P.natDegree χ η k s (hML k s)
                - khatZMult P (⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊)
                  • mstPiCls P l P.natDegree χ η s (hηml s) (2 ^ k)) := by abel
        have hsmul : opMul (khatZMult P (⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊)
              • mstPiCls P l P.natDegree χ η s (hηml s) (2 ^ k))
              (⇑g) (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g)
            = discAvgZC P (⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊) (T k g) := by
          rw [show (T k) g = opMul (mstPiCls P l P.natDegree χ η s (hηml s) (2 ^ k)) (⇑g)
              (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g) from rfl]
          rw [← opMul_mul]
          exact opMul_khatZMult_eq_discAvgZC P (⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊)
            (opMul (mstPiCls P l P.natDegree χ η s (hηml s) (2 ^ k)) (⇑g)
              (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g))
            (Work.BourgainPlan.IonescuWainger.opMul_memℓp
              (mstPiCls P l P.natDegree χ η s (hηml s) (2 ^ k)) (⇑g)
              (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g))
        rw [hsplit, opMul_add]
        refine (enorm_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [hsmul, hTapp]
          exact le_iSup₂ (f := fun k _ => ‖discAvgZC P
            (⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊) (T k g) m‖ₑ) k hk
        · exact Finset.single_le_sum (f := fun j : ℕ => ‖Work.BourgainPlan.IonescuWainger.opMul
              (mstNuSCls P l P.natDegree χ η j s (hML j s)
                - khatZMult P (⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊)
                  • mstPiCls P l P.natDegree χ η s (hηml s) (2 ^ j)) (⇑g)
              (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g) m‖ₑ) (fun i _ => zero_le) hk
      -- combine
      refine (eLpNorm_mono_enorm
        (f := fun m : ℤ => (⨆ k ∈ Finset.range (2 ^ (mstKappa P s) + 1),
            ‖Work.BourgainPlan.IonescuWainger.opMul
              (mstNuSCls P l P.natDegree χ η k s (hML k s)) (⇑g)
              (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g) m‖ₑ))
        (g := fun m : ℤ => (⨆ k ∈ Finset.range (2 ^ (mstKappa P s) + 1), ‖discAvgZC P
                (⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊) (T k g) m‖ₑ)
            + ∑ k ∈ Finset.range (2 ^ (mstKappa P s) + 1),
                ‖opMulFinsuppLM
                  (mstNuSCls P l P.natDegree χ η k s (hML k s)
                    - khatZMult P (⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊)
                      • mstPiCls P l P.natDegree χ η s (hηml s) (2 ^ k)) g m‖ₑ)
        AEStronglyMeasurable.of_discrete (fun m => ?_)).trans ?_
      · rw [enorm_eq_self, enorm_eq_self]
        exact hpoint m
      refine (eLpNorm_add_le (ENNReal.one_le_ofReal.mpr hp.le)).trans ?_
      refine (add_le_add hdisc herrsum).trans ?_
      have hcf1 : 0 ≤ (Cbas + 2 * Clev) * Ln :=
        mul_nonneg (by linarith [hCbaspos, hClevpos]) hLnn
      have hcf2 : 0 ≤ (Cerr / Real.log 2) * Ln :=
        mul_nonneg (div_nonneg hCerrpos.le hlog2.le) hLnn
      have hcoef : Cbas + 2 * Clev + Cerr / Real.log 2 ≤ Cf := by
        have hCL0 : 0 ≤ Cbas + 2 * Clev := by linarith [hCbaspos, hClevpos]
        have hdiv : Cbas + 2 * Clev ≤ (Cbas + 2 * Clev) / Real.log 2 := by
          rw [le_div_iff₀ hlog2]
          nlinarith [hlog2le, hCL0]
        have hkey : Cbas + 2 * Clev + Cerr / Real.log 2
            ≤ (Cbas + 2 * Clev + Cerr) / Real.log 2 + 1 := by
          rw [add_div]
          linarith
        have hmax := le_max_left ((Cbas + 2 * Clev + Cerr) / Real.log 2 + 1)
          (((2 : ℝ) ^ (mstKappa P S₀ + 1) * (((mstU l S₀).card : ℝ) * Ktriv))
            / Real.log 2 + 1)
        rw [hCf]
        linarith [hkey, hmax]
      have hfinal : (Cbas + 2 * Clev) * Ln + (Cerr / Real.log 2) * Ln ≤ Cf * Ln := by
        calc (Cbas + 2 * Clev) * Ln + (Cerr / Real.log 2) * Ln
            = (Cbas + 2 * Clev + Cerr / Real.log 2) * Ln := by ring
          _ ≤ Cf * Ln := mul_le_mul_of_nonneg_right hcoef hLnn
      calc ENNReal.ofReal ((Cbas + 2 * Clev) * Ln)
              * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal p) MeasureTheory.Measure.count
            + ENNReal.ofReal ((Cerr / Real.log 2) * Ln)
              * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal p) MeasureTheory.Measure.count
          = ENNReal.ofReal ((Cbas + 2 * Clev) * Ln + (Cerr / Real.log 2) * Ln)
            * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal p) MeasureTheory.Measure.count := by
            rw [ofReal_mul_add_mul (ha := hcf1) (hb := hcf2)]
        _ ≤ ENNReal.ofReal (Cf * Ln)
            * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal p) MeasureTheory.Measure.count :=
            ofReal_mul_le_mul hfinal
              (MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal p) MeasureTheory.Measure.count)

end

end Work.BourgainPlan.Maximal
