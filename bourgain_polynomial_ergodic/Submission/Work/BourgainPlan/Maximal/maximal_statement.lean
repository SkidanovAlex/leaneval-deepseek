import Mathlib
import Submission.BourgainPlan.Interfaces
import Submission.Work.BourgainPlan.Maximal.foundations
import Submission.Work.BourgainPlan.Maximal.z_defs
import Submission.Work.BourgainPlan.Maximal.mst_iw_lift
import Submission.Work.BourgainPlan.Maximal.mst_level_defs
import Submission.Work.BourgainPlan.Maximal.mst_major_defs
import Submission.Work.BourgainPlan.Maximal.mst_minor_lp_per_n
import Submission.Work.BourgainPlan.Maximal.mst_minor_per_n
import Submission.Work.BourgainPlan.Maximal.mst_minor_lp_gain
import Submission.Work.BourgainPlan.Maximal.iw_superset_bound
import Submission.Work.BourgainPlan.Maximal.mst_major_err1_lp
import Submission.Work.BourgainPlan.Maximal.mst_major_err2_lp
import Submission.Work.BourgainPlan.Maximal.mstG_gauss
import Submission.Work.BourgainPlan.Maximal.memLp_mst_symbols
import Submission.Work.BourgainPlan.Maximal.mstU_rep
import Submission.Work.BourgainPlan.Maximal.mstG_spec
import Submission.Work.BourgainPlan.Maximal.mikhlin_conditions_scaled_bump
import Submission.Work.BourgainPlan.Maximal.mst_level_lp_glue
import Submission.Work.BourgainPlan.Maximal.mst_theta_defs
import Submission.Work.BourgainPlan.Maximal.mst_dyadic_z_of_pieces
import Submission.Work.BourgainPlan.Maximal.subtwo_of_dyadic_z
import Submission.Work.BourgainPlan.Maximal.assembly
import Submission.Work.BourgainPlan.Maximal.leadingCoeff_pos_of_nonneg
import Submission.Work.BourgainPlan.Maximal.dyadic_z_deg_le_one
import Submission.Work.BourgainPlan.Maximal.exists_mst_bump
import Submission.Work.BourgainPlan.Maximal.mstG_gauss_delta
import Submission.Work.BourgainPlan.Maximal.memLp_mst_classes
import Submission.Work.BourgainPlan.Maximal.mst_hlevel_lr
import Submission.Work.BourgainPlan.Maximal.mst_level_l2
import Submission.Work.BourgainPlan.Maximal.mst_minor_sup_direct
import Submission.Work.BourgainPlan.Maximal.mst_minor_lp_gain_direct
import Submission.Work.BourgainPlan.Maximal.mst_theta_bound

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false

namespace Work.BourgainPlan.Maximal

open MeasureTheory Finset
open scoped BigOperators ENNReal
open Work.BourgainPlan.IonescuWainger

noncomputable section

local notation "haarT" => (AddCircle.haarAddCircle (T := 1))

theorem mst_hlevel_of_endpoints (ν : ℕ → ℕ → MeasureTheory.Lp ℂ ⊤ haarT) {p r : ℝ}
    (hr : 1 < r) (hrp : r < p) (hp2 : p < 2)
    {A₂ e₂ A_r : ℝ} (hA₂ : 0 < A₂) (hA_r : 0 < A_r)
    (h2 : ∀ s : ℕ, ∀ g : ℤ →₀ ℂ,
      MeasureTheory.eLpNorm (fun m : ℤ => (⨆ k : ℕ,
          ‖opMul (ν k s) (⇑g) (memℓp_finsupp g) m‖ₑ))
        (ENNReal.ofReal 2) Measure.count
      ≤ ENNReal.ofReal (A₂ * ((s : ℝ) + 1) ^ e₂)
        * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal 2) Measure.count)
    (hrr : ∀ s : ℕ, ∀ g : ℤ →₀ ℂ,
      MeasureTheory.eLpNorm (fun m : ℤ => (⨆ k : ℕ,
          ‖opMul (ν k s) (⇑g) (memℓp_finsupp g) m‖ₑ))
        (ENNReal.ofReal r) Measure.count
      ≤ ENNReal.ofReal (A_r * (((s : ℝ) + 1) * Real.log ((s : ℝ) + 2)))
        * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal r) Measure.count)
    (he₂ : e₂ ≤ -3 / ((1 / r - 1 / p) / (1 / r - 1 / 2))) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℕ, ∀ g : ℤ →₀ ℂ,
      MeasureTheory.eLpNorm (fun m : ℤ => (⨆ (k : ℕ) (_ : s < k),
          ‖opMul (ν k s) (⇑g) (memℓp_finsupp g) m‖ₑ))
        (ENNReal.ofReal p) Measure.count
      ≤ ENNReal.ofReal (C * ((s : ℝ) + 1) ^ (-2 : ℝ))
        * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal p) Measure.count := by
  have hr0 : (0 : ℝ) < r := lt_trans zero_lt_one hr
  have hr2 : r < 2 := lt_trans hrp hp2
  have hp1 : (1 : ℝ) < p := lt_trans hr hrp
  have hp0 : (0 : ℝ) < p := lt_trans zero_lt_one hp1
  set θ : ℝ := (1 / r - 1 / p) / (1 / r - 1 / 2) with hθdef
  have hden : (0 : ℝ) < 1 / r - 1 / 2 := by
    have h : (1 : ℝ) / 2 < 1 / r := one_div_lt_one_div_of_lt hr0 hr2
    linarith
  have hnum : (0 : ℝ) < 1 / r - 1 / p := by
    have h : (1 : ℝ) / p < 1 / r := one_div_lt_one_div_of_lt hr0 hrp
    linarith
  have hθ0 : (0 : ℝ) < θ := by rw [hθdef]; exact div_pos hnum hden
  have hθ1 : θ < 1 := by
    rw [hθdef, div_lt_one hden]
    have h : (1 : ℝ) / 2 < 1 / p := one_div_lt_one_div_of_lt hp0 hp2
    linarith
  obtain ⟨C, hCpos, hC⟩ := mst_level_lp_arith hθ0 hθ1 hA₂ hA_r he₂
  refine ⟨C, hCpos, fun s g => ?_⟩
  have hslog : (0 : ℝ) < Real.log ((s : ℝ) + 2) := by
    apply Real.log_pos
    have : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg s
    linarith
  have hAs : 0 < A_r * (((s : ℝ) + 1) * Real.log ((s : ℝ) + 2)) := by
    have : (0 : ℝ) < (s : ℝ) + 1 := by positivity
    positivity
  have hBs : 0 < A₂ * ((s : ℝ) + 1) ^ e₂ := by
    have : (0 : ℝ) < (s : ℝ) + 1 := by positivity
    positivity
  have hfin := mst_level_lp_finset
    (Φ := fun k => ν k s) hr hrp hp2 hAs hBs (h2 s) (hrr s)
  set z : ℕ → ℤ → ENNReal := fun k m => ‖opMul (ν k s) (⇑g) (memℓp_finsupp g) m‖ₑ with hzdef
  have hbound : ∀ n : ℕ, MeasureTheory.eLpNorm
        (fun m : ℤ => ⨆ k ∈ Finset.range (n + 1), z k m)
        (ENNReal.ofReal p) MeasureTheory.Measure.count
      ≤ ENNReal.ofReal ((A_r * (((s : ℝ) + 1) * Real.log ((s : ℝ) + 2))) ^ (1 - θ)
          * (A₂ * ((s : ℝ) + 1) ^ e₂) ^ θ)
        * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal p) MeasureTheory.Measure.count := by
    intro n
    have h := hfin (Finset.range (n + 1)) ⟨0, Finset.mem_range.mpr (Nat.succ_pos n)⟩ g
    simpa only [hzdef] using h
  have hmono : Monotone (fun n : ℕ => fun m : ℤ => ⨆ k ∈ Finset.range (n + 1), z k m) := by
    intro n n' hnn'
    refine fun m => iSup_le fun k => iSup_le fun hk => ?_
    exact le_iSup_of_le k (le_iSup_of_le
      (Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hk) (Nat.succ_le_succ hnn'))) le_rfl)
  have hsup := mst_eLpNorm_iSup_mono_le (q := p) hp0 hmono hbound
  have hfun : (fun m : ℤ => ⨆ n : ℕ, ⨆ k ∈ Finset.range (n + 1), z k m)
      = (fun m : ℤ => ⨆ k : ℕ, z k m) := by
    funext m
    refine le_antisymm ?_ ?_
    · refine iSup_le fun n => iSup_le fun k => iSup_le fun _ => le_iSup (fun k => z k m) k
    · refine iSup_le fun k => ?_
      have h1 : z k m ≤ ⨆ j ∈ Finset.range (k + 1), z j m :=
        le_iSup_of_le k (le_iSup_of_le (Finset.mem_range.mpr (Nat.lt_succ_self k)) le_rfl)
      exact le_iSup_of_le k h1
  rw [hfun] at hsup
  refine le_trans (MeasureTheory.eLpNorm_mono_enorm
    (f := fun m : ℤ => (⨆ (k : ℕ) (_ : s < k), z k m))
    (g := fun m : ℤ => (⨆ k : ℕ, z k m))
    MeasureTheory.AEStronglyMeasurable.of_discrete (fun m => ?_)) (le_trans hsup ?_)
  · exact iSup_le fun k => iSup_le fun _ => le_iSup (fun k : ℕ => z k m) k
  · refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (hC s)) (zero_le)

theorem maximal_statement_of_inputs : Submission.BourgainPlan.MaximalStatement
:= by
  refine maximal_statement_of_subtwo (subtwo_of_dyadic_z ?_)
  intro P hP p hp1 hp2
  by_cases hdeg : P.natDegree ≤ 1
  · exact dyadic_z_deg_le_one P hP hdeg p hp1 hp2
  · have hd : 2 ≤ P.natDegree := by omega
    have hc : 0 < P.leadingCoeff := leadingCoeff_pos_of_nonneg P hP (by omega)
    -- the bump
    obtain ⟨η, M, hMpos, hηc, hηbd, hder, hder2, hηone, hη0⟩ := exists_mst_bump
    have hη01 : η 0 = 1 := hηone 0 (by norm_num)
    have hηsup : ∀ x : ℝ, 1 / 2 ≤ |x| → η x = 0 :=
      contDiff_eta_zero_of_half_le_abs hηc hη0
    have hηcont : Continuous η := hηc.continuous
    -- the exponent χ
    set χ : ℝ := 1 / 20 with hχdef
    have hχ0 : 0 < χ := by rw [hχdef]; norm_num
    have hχ1 : χ < 1 / 10 := by rw [hχdef]; norm_num
    -- the MemLp of the level bumps (independent of l)
    have hηml : ∀ n : ℕ, MeasureTheory.MemLp (mstEta P.natDegree χ η n) ⊤ haarT := by
      intro n
      have hEq : mstEta P.natDegree χ η n
          = fun ξ => η ((2 : ℝ) ^ ((n : ℝ) * ((P.natDegree : ℝ) - χ)) * iwRep ξ) := by
        funext ξ; rw [mstEta_apply]
      rw [hEq]
      exact (memLp_mst_symbols P (2 ^ n) ((2 : ℝ) ^ ((n : ℝ) * ((P.natDegree : ℝ) - χ)))
        η hηcont).2.2
    -- the interpolation exponents
    set r : ℝ := (1 + p) / 2 with hrdef
    have hr1 : 1 < r := by rw [hrdef]; linarith
    have hrp : r < p := by rw [hrdef]; linarith
    set θ : ℝ := (1 / r - 1 / p) / (1 / r - 1 / 2) with hθdef
    have hp0 : (0 : ℝ) < p := by linarith
    have hp0' : (0 : ℝ) < 1 + p := by linarith
    have h2eq : (1 : ℝ) / ((1 + p) / 2) = 2 / (1 + p) := by rw [one_div, inv_div]
    have hlt1 : (1 : ℝ) / 2 < 2 / (1 + p) := by
      rw [div_lt_div_iff₀ (by norm_num) hp0']; linarith
    have hlt2 : (1 : ℝ) / p < 2 / (1 + p) := by
      rw [div_lt_div_iff₀ hp0 hp0']; linarith
    have hden : (0 : ℝ) < 1 / r - 1 / 2 := by rw [hrdef, h2eq]; linarith
    have hnum : (0 : ℝ) < 1 / r - 1 / p := by rw [hrdef, h2eq]; linarith
    have hθ0 : 0 < θ := by rw [hθdef]; exact div_pos hnum hden
    -- the Gauss decay exponent δ of mstG
    obtain ⟨δ, hδpos, hδ⟩ := mstG_gauss_delta P hd hc
    -- the minor-arc level threshold l₀
    obtain ⟨l₀, hl₀⟩ := mst_minor_lp_gain_direct mst_minor_sup_direct P hd hc η hηc M hMpos hηbd hηone hη0 hder hder2
      hχ0 hχ1 hηml hp1 hp2
    -- a level l large enough for both the minor-arc gain and the level arithmetic
    set l : ℕ := max l₀ (Nat.ceil ((3 / θ + 1) / δ) + 1) with hldef
    have hl1 : 1 ≤ l := le_trans (Nat.one_le_iff_ne_zero.mpr (by positivity)) (le_max_right _ _)
    have hl₀' : l₀ ≤ l := le_max_left _ _
    have hlδ : 3 / θ + 1 ≤ δ * (l : ℝ) := by
      have hceil_le : Nat.ceil ((3 / θ + 1) / δ) ≤ l :=
        le_trans (Nat.le_succ _) (le_max_right _ _)
      have h1 : (3 / θ + 1) / δ ≤ (Nat.ceil ((3 / θ + 1) / δ) : ℝ) := Nat.le_ceil _
      have h2 : (Nat.ceil ((3 / θ + 1) / δ) : ℝ) ≤ (l : ℝ) := by exact_mod_cast hceil_le
      have h3 := mul_le_mul_of_nonneg_left (le_trans h1 h2) hδpos.le
      have h4 : δ * ((3 / θ + 1) / δ) = 3 / θ + 1 := by field_simp
      linarith [h3, h4.le, h4.symm.le]
    -- the Gauss data at level l
    obtain ⟨D, hDpos, hGauss⟩ := hδ l hl1
    -- the MemLp data at level l
    obtain ⟨hνml, hνsml, _⟩ := memLp_mst_classes P l P.natDegree χ η hηcont
    -- the representative data for the first major-arc error
    obtain ⟨nrep, hrep0⟩ := mstU_rep l hl1
    have hrep : ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ β ∈ mstU l n, ∃ (q : ℕ) (a : ℤ),
        0 < q ∧ 0 ≤ a ∧ a < q ∧ arcPt q a = β ∧
        mstG P β = polyWeight P q a ∧
        (q : ℝ) ≤ Real.exp (((n : ℝ) ^ l) ^ (mstRho l)) := by
      refine ⟨nrep, fun n hn β hβ => ?_⟩
      obtain ⟨q, a, hq, ha, haq, _, hβeq, hqle⟩ := hrep0 n hn β hβ
      exact ⟨q, a, hq, ha, haq, hβeq, mstG_spec P hq ha haq hβeq, hqle⟩
    -- the Mikhlin data of the level bumps
    have hbumpdata : ∀ n : ℕ,
        ContDiff ℝ 2 (Work.BourgainPlan.Thm52.circleLift (mstEta P.natDegree χ η n)) ∧
        (∀ x : ℝ, ‖Work.BourgainPlan.Thm52.circleLift (mstEta P.natDegree χ η n) x‖ ≤ M) ∧
        (∀ x : ℝ, |x| * ‖deriv (Work.BourgainPlan.Thm52.circleLift (mstEta P.natDegree χ η n)) x‖ ≤ M) ∧
        (∀ x : ℝ, |x| ^ 2 * ‖iteratedDeriv 2
          (Work.BourgainPlan.Thm52.circleLift (mstEta P.natDegree χ η n)) x‖ ≤ M) := by
      intro n
      have hexp : (0 : ℝ) ≤ (n : ℝ) * ((P.natDegree : ℝ) - χ) := by
        have h2 : (2 : ℝ) ≤ (P.natDegree : ℝ) := by exact_mod_cast hd
        have h3 : χ < 2 := lt_trans hχ1 (by norm_num)
        exact mul_nonneg (Nat.cast_nonneg n) (by linarith)
      have hc1 : (1 : ℝ) ≤ |(2 : ℝ) ^ ((n : ℝ) * ((P.natDegree : ℝ) - χ))| := by
        rw [abs_of_nonneg (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2)
          ((n : ℝ) * ((P.natDegree : ℝ) - χ)))]
        exact Real.one_le_rpow (by norm_num) hexp
      have h := mikhlin_conditions_scaled_bump (η := η) (M := M)
        (c := (2 : ℝ) ^ ((n : ℝ) * ((P.natDegree : ℝ) - χ))) hMpos.le hc1
        hηc hηbd hder hder2 hηsup
      have hEq : mstEta P.natDegree χ η n
          = fun ξ => η ((2 : ℝ) ^ ((n : ℝ) * ((P.natDegree : ℝ) - χ)) * iwRep ξ) := by
        funext ξ; rw [mstEta_apply]
      rw [hEq]
      exact h
    have hcd : ∀ n : ℕ, ContDiff ℝ 2 (Work.BourgainPlan.Thm52.circleLift (mstEta P.natDegree χ η n)) :=
      fun n => (hbumpdata n).1
    have hbdd : ∀ (n : ℕ) (x : ℝ), ‖Work.BourgainPlan.Thm52.circleLift (mstEta P.natDegree χ η n) x‖ ≤ M :=
      fun n x => (hbumpdata n).2.1 x
    have hder' : ∀ (n : ℕ) (x : ℝ), |x| * ‖deriv (Work.BourgainPlan.Thm52.circleLift (mstEta P.natDegree χ η n)) x‖ ≤ M :=
      fun n x => (hbumpdata n).2.2.1 x
    have hder2' : ∀ (n : ℕ) (x : ℝ), |x| ^ 2 * ‖iteratedDeriv 2 (Work.BourgainPlan.Thm52.circleLift (mstEta P.natDegree χ η n)) x‖ ≤ M :=
      fun n x => (hbumpdata n).2.2.2 x
    -- the four families
    obtain ⟨Cminor, hCminor, Nminor, hminor⟩ := hl₀ l hl₀'
    obtain ⟨C₁, c₁, hC₁, hc₁, N₁, herr1⟩ :=
      mst_major_err1_lp P hd hc hχ0 hχ1 η M hMpos hηbd hηone hη0 l hl1 M hMpos
        hcd hbdd hder' hder2' hrep hηml hνml hp1 hp2
    obtain ⟨C₂, c₂, hC₂, hc₂, N₂, herr2⟩ :=
      mst_major_err2_lp P hd hc hχ0 hχ1 η M hMpos hηbd hηone hη0 l hl1 M hMpos
        hcd hbdd hder' hder2' hνml hνsml hp1 hp2
    -- the level estimate
    obtain ⟨Cl2, hCl2, hl2⟩ := mst_level_l2 P hd hc l hl1 hχ0 hχ1 η hηc hη01 hηsup hδpos D hDpos hGauss hνsml
    obtain ⟨Clr, hClr, hlr⟩ := mst_hlevel_lr mst_theta_bound P hd hc l hl1 hχ0 hχ1 η M hMpos hηc hηbd hder hder2 hηsup hδpos D hDpos hGauss hνsml hr1 (by rw [hrdef]; linarith)
    have he₂ : (1 / 10 : ℝ) - δ * l ≤ -3 / ((1 / r - 1 / p) / (1 / r - 1 / 2)) := by
      have h5 : 3 / θ + 1 ≤ δ * (l : ℝ) := hlδ
      have h6 : (1 / 10 : ℝ) - (δ * (l : ℝ)) ≤ (-(9 / 10) : ℝ) - 3 / θ := by
        have he : (-(9 / 10) : ℝ) - 3 / θ = 1 / 10 - (3 / θ + 1) := by ring
        rw [he]
        exact sub_le_sub_left h5 (1 / 10)
      have h7 : (-(9 / 10) : ℝ) - 3 / θ ≤ -3 / θ := by
        rw [sub_le_iff_le_add]
        ring_nf
        norm_num
      rw [← hθdef]
      exact le_trans h6 h7
    obtain ⟨C₄, hC₄, hlevel⟩ := mst_hlevel_of_endpoints
      (ν := fun k s => mstNuSCls P l P.natDegree χ η k s (hνsml k s))
      (p := p) (r := r) (A₂ := Cl2) (e₂ := 1 / 10 - δ * l) (A_r := Clr)
      hr1 hrp hp2 hCl2 hClr hl2 hlr he₂
    refine mst_dyadic_z_of_pieces P hP hp1 hp2 l hl1 hχ0 hχ1 η hηml hνml hνsml
      (max (max Nminor N₁) N₂) Cminor hCminor ?_ C₁ c₁ hC₁ hc₁ ?_ C₂ c₂ hC₂ hc₂ ?_ C₄ hC₄ hlevel
    · intro k hk g
      exact hminor k (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hk) g
    · intro k hk g
      exact herr1 k (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hk) g
    · intro k hk g
      exact herr2 k (le_max_right _ _ |>.trans <| hk) g

/-- **Bourgain's discrete `ℓᵖ` maximal inequality, all `1 < p < ∞`.**

WIRING STATUS (H3, session 30, 10:15) — **COMPLETE**.  `maximal_statement_of_inputs` has *no*
hypotheses: every ingredient is a proved theorem, and the whole transitive import closure of this
file is gap-free.  The chain is

    maximal_statement = maximal_statement_of_inputs
      = maximal_statement_of_subtwo ∘ subtwo_of_dyadic_z ∘ mst_dyadic_z_of_pieces
        ⟨ hminor := mst_minor_lp_gain_direct mst_minor_sup_direct        (MST (63) + §4.1; no MSTWeylBound)
        , herr1  := mst_major_err1_lp, herr2 := mst_major_err2_lp        (§4.2)
        , hlevel := mst_hlevel_of_endpoints ∘ (mst_level_l2, mst_hlevel_lr) ⟩

with `mst_hlevel_lr = mst_level_lr_small + mst_level_lr_large` (the two standalone halves under
`Submission/Work/Maximal/`, the large one via `mstNuS_lr_large_aux_glue` and the proved lattice
principle `mstLatticePrinciple`, restricted to the `s ≥ s₀` range with the finitely many smaller
levels absorbed into the constant) and `mst_theta_bound : MSTThetaBound` supplying MST's `(C2)`
(via `mst_theta_raw ⟸ mstThetaRawMult_of_real ⟸ mst_theta_real ⟸ mst_theta_real_l2`).
`#print axioms maximal_statement` gives `propext, Classical.choice, Quot.sound` only.
-/
theorem maximal_statement : Submission.BourgainPlan.MaximalStatement :=
  maximal_statement_of_inputs

end
end Work.BourgainPlan.Maximal
