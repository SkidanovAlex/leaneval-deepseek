import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.CoercivityFix.Transfer.L4Step
import Submission.Work.FTS.StrongEps.EpsE4Thr.Coer1LhatO
import Submission.Work.FTS.StrongEps.EpsE4Thr.Coer1Open
import Submission.Work.FTS.StrongEps.EpsE4Thr.CoerData2FourO
import Submission.Work.FTS.StrongEps.EpsE4Thr.CoerDataTO
import Submission.Work.FTS.StrongEps.EpsE4Thr.hardyHyp_of_coerAdmO
import Submission.Work.FTS.StrongEps.EpsLocalPStar.JepsMarginalZero_zero
import Submission.Work.FTS.StrongEps.L12Sub4.L12ZeroLog
import Submission.Work.FTS.StrongPersist.L3Aux.bcoefRadBound
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.DelicateHon
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS.TransportS.SlotT2.supThetaIntOpen
import Submission.Work.FTS_EllLimOK.exists_ellLimOK3_of_closed
import Submission.Work.FTS_LocDatum3a.Assembly

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.TransO

open Work.FTS.Galerkin (Fn)
open Work.FTS.CoercivityFix.Transfer
open Work.FTS.StrongEps.EpsE4Thr (CoerAdmO CoerData2O CoerDataTO RegQo)

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! ## The two elementary `α`-bounds -/

/-- If `α·(A+1) ≤ min B 1`, then `A·α² ≤ B`. -/
private lemma key1 {A B α : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hα : 0 ≤ α)
    (h : α * (A + 1) ≤ min B 1) : A * α ^ 2 ≤ B := by
  have h3 : 0 ≤ α * (A + 1) := mul_nonneg hα (by linarith)
  have h4 : (α * (A + 1)) ^ 2 ≤ min B 1 := by
    nlinarith [h, h3, min_le_right B 1]
  have h5 : A * α ^ 2 ≤ (α * (A + 1)) ^ 2 := by nlinarith [hA, hα]
  linarith [h4, h5, min_le_left B 1]

/-- If `α·(A+1) ≤ B`, then `A·α ≤ B`. -/
private lemma key2 {A B α : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hα : 0 ≤ α)
    (h : α * (A + 1) ≤ B) : A * α ≤ B := by
  have : A * α ≤ α * (A + 1) := by nlinarith [hA, hα]
  linarith



/-- **The level-`4` transfer data for the concrete `IP4`, from the two defect lemmas.**

Runs the clean and the transfer inductions side by side with the coefficients
`c₁ = c₁' = c₁'' = 1` and `c₂, c₂', c₂''` chosen small, producing the `coer` clause of the
headline. -/
theorem transfer_level4_O
    (hE1 : ∃ κ₁ : ℝ, 0 ≤ κ₁ ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (n : ℕ), n ≤ 3 → ∀ f : Fn,
      Work.FTS.StrongEps.EpsE4Thr.CoerAdmO α f →
        Work.Spaces.HkNorm α n (E1 α f)
          ≤ α * κ₁ * (Work.Spaces.HkNorm α n f + Work.Spaces.HkNorm α n (Work.Spaces.Dth f)))
    (hE2 : ∃ κ₂ : ℝ, 0 ≤ κ₂ ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (n : ℕ), n ≤ 3 → ∀ f : Fn,
      Work.FTS.StrongEps.EpsE4Thr.CoerAdmO α f →
        Work.Spaces.HkNorm α n (E2 α f)
          ≤ κ₂ * (Work.Spaces.HkNorm α n f + Work.Spaces.HkNorm α n (Work.Spaces.Dth f)))
    (CC₁ : ℝ) (hCC₁ : 0 < CC₁)
    (hCD₁ : ∀ α : ℝ, α ∈ Set.Ioc 0 (1 / 10 ^ 14) →
      Work.FTS.StrongEps.EpsE4Thr.CoerData2O α 1 (Work.Coercivity.H1IP α) 2 CC₁)
    (hok₁ : ∀ α : ℝ, 0 < α → α ≤ 1 → Work.FTS.StrongEps.EpsE4Thr.TransO.LevelPkgO α 1 (Work.Coercivity.H1IP α) CC₁)
    (hok₂ : ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ c₂ : ℝ, 0 < c₂ →
      Work.FTS.StrongEps.EpsE4Thr.TransO.LevelPkgO α 2 (Work.FTS.CoercivityFix.Assembly.IP2 1 c₂ α) (3 * max 1 (max 1 c₂) * CC₁))
    (hok₃ : ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ c₂ c₂' : ℝ, 0 < c₂ → 0 < c₂' →
      Work.FTS.StrongEps.EpsE4Thr.TransO.LevelPkgO α 3 (Work.FTS.CoercivityFix.Assembly.IP3 1 c₂ 1 c₂' α)
        (3 * max 1 (max 1 c₂') * (3 * max 1 (max 1 c₂) * CC₁))) :
    ∃ (c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ),
      0 < c₁ ∧ 0 < c₂ ∧ 0 < c₁' ∧ 0 < c₂' ∧ 0 < c₁'' ∧ 0 < c₂'' ∧
      ∃ (α₂ cc CC : ℝ), 0 < α₂ ∧ 0 < cc ∧ 0 < CC ∧
        ∀ α : ℝ, α ∈ Set.Ioc 0 α₂ →
          Work.FTS.StrongEps.EpsE4Thr.CoerDataTO α 4
            (Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α) cc CC := by
  obtain ⟨κ₁, hκ₁, hE1'⟩ := hE1
  obtain ⟨κ₂, hκ₂, hE2'⟩ := hE2
  obtain ⟨κE₁, hκE₁, hÊ₁⟩ := Work.FTS.StrongEps.EpsE4Thr.hE2_unif_O 1
  obtain ⟨κE₂, hκE₂, hÊ₂⟩ := Work.FTS.StrongEps.EpsE4Thr.hE2_unif_O 2
  obtain ⟨κE₃, hκE₃, hÊ₃⟩ := Work.FTS.StrongEps.EpsE4Thr.hE2_unif_O 3
  set κE : ℝ := max κE₁ (max κE₂ κE₃) with hκEdef
  have hκE0 : 0 ≤ κE := le_trans hκE₁ (le_max_left _ _)
  -- the level-`1` transfer data, at the *same* `CC₁` as the clean level-`1` data
  have ht₁ : ∀ α : ℝ, α ∈ Set.Ioc 0 (1 / 10 ^ 14) →
      Work.FTS.StrongEps.EpsE4Thr.CoerDataTO α 1 (Work.Coercivity.H1IP α) 1 CC₁ := by
    intro α hα
    refine ⟨one_pos, hCC₁, fun f g hf hg => (hCD₁ α ⟨hα.1, by linarith [hα.2]⟩).cs f g hf hg, ?_⟩
    intro f hf
    simpa using Work.FTS.StrongEps.EpsE4Thr.coer1_LGammaT_O (α := α) hα.1 hα.2 hf
      (Work.FTS.StrongEps.EpsE4Thr.IntPkg_O (α := α) hα.1
        (Work.FTS.StrongEps.EpsE4Thr.regQo_mono (k := 2) (l := 5) (by norm_num) hf.1))
  -- the step coefficients
  obtain ⟨c₂s, hc₂s, hss₁⟩ := Work.FTS.CoercivityFix.exists_small_step_coeffs
    (cc := 2) (CC := CC₁) (κ := κE) (c₁ := 1) (by norm_num) hCC₁ one_pos hκE0
  set c₂ : ℝ := min c₂s (min (2 / (64 * ((CC₁ * κ₂) ^ 2 + 1))) (1 / 2)) with hc₂def
  have hc₂pos : 0 < c₂ :=
    lt_min hc₂s (lt_min (div_pos (by norm_num) (by positivity)) (by norm_num))
  have hc₂le : c₂ ≤ c₂s := min_le_left _ _
  have hss₁' : Work.FTS.CoercivityFix.StepSmall 2 CC₁ κE 1 c₂ :=
    ⟨le_trans (mul_le_mul_of_nonneg_right hc₂le (sq_nonneg _)) hss₁.1,
     le_trans (mul_le_mul_of_nonneg_right hc₂le (sq_nonneg _)) hss₁.2⟩
  have hc₂le2 : c₂ ≤ 2 / (64 * ((CC₁ * κ₂) ^ 2 + 1)) :=
    le_trans (min_le_right _ _) (min_le_left _ _)
  have hs3₁ : c₂ * (16 * (CC₁ * κ₂) ^ 2) ≤ 1 * 2 := by
    have h1 : c₂ * (16 * (CC₁ * κ₂) ^ 2)
        ≤ (2 / (64 * ((CC₁ * κ₂) ^ 2 + 1))) * (16 * (CC₁ * κ₂) ^ 2) :=
      mul_le_mul_of_nonneg_right hc₂le2 (by positivity)
    have hden : 0 < 64 * ((CC₁ * κ₂) ^ 2 + 1) := by positivity
    have h2 : (2 / (64 * ((CC₁ * κ₂) ^ 2 + 1))) * (16 * (CC₁ * κ₂) ^ 2) ≤ 2 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hden]
      nlinarith [sq_nonneg (CC₁ * κ₂)]
    linarith [h1, h2]
  have hs4₁ : c₂ * (16 * (CC₁ * κ₂) ^ 2) ≤ 1 * 2 ^ 2 := by linarith [hs3₁]
  -- the level-`2` constants
  set CC₂ : ℝ := 3 * max 1 (max 1 c₂) * CC₁ with hCC₂def
  have hCC₂pos : 0 < CC₂ := by
    have h1 : (1:ℝ) ≤ max 1 (max 1 c₂) := le_max_left _ _
    rw [hCC₂def]; nlinarith [hCC₁]
  set cc₂ : ℝ := 2 * min 1 (min 1 c₂) / (2 * 1) with hcc₂def
  have hcc₂pos : 0 < cc₂ := by
    rw [hcc₂def]
    exact div_pos (mul_pos (by norm_num) (lt_min one_pos (lt_min one_pos hc₂pos)))
      (by norm_num)
  set ccT₂ : ℝ := min (3 * 1 / 4) (min (5 * 1 * 2 / 8) (3 * c₂ * 2 / 4)) / 1 with hccT₂def
  have hccT₂pos : 0 < ccT₂ := by
    rw [hccT₂def]
    refine div_pos (lt_min (by norm_num) (lt_min (by norm_num) ?_)) one_pos
    nlinarith [hc₂pos]
  -- the second step coefficient
  obtain ⟨c₂ds, hc₂ds, hss₂⟩ := Work.FTS.CoercivityFix.exists_small_step_coeffs
    (cc := cc₂) (CC := CC₂) (κ := κE) (c₁ := 1) hcc₂pos hCC₂pos one_pos hκE0
  set c₂' : ℝ := min c₂ds (min (min (ccT₂ * cc₂) (cc₂ ^ 2) / (64 * ((CC₂ * κ₂) ^ 2 + 1)))
    (1 / 2)) with hc₂'def
  have hc₂'pos : 0 < c₂' :=
    lt_min hc₂ds (lt_min (div_pos (lt_min (mul_pos hccT₂pos hcc₂pos)
      (pow_pos hcc₂pos 2)) (by positivity)) (by norm_num))
  have hc₂'le : c₂' ≤ c₂ds := min_le_left _ _
  have hss₂' : Work.FTS.CoercivityFix.StepSmall cc₂ CC₂ κE 1 c₂' :=
    ⟨le_trans (mul_le_mul_of_nonneg_right hc₂'le (sq_nonneg _)) hss₂.1,
     le_trans (mul_le_mul_of_nonneg_right hc₂'le (sq_nonneg _)) hss₂.2⟩
  have hc₂'le2 : c₂' ≤ min (ccT₂ * cc₂) (cc₂ ^ 2) / (64 * ((CC₂ * κ₂) ^ 2 + 1)) :=
    le_trans (min_le_right _ _) (min_le_left _ _)
  have hs3₂ : c₂' * (16 * (CC₂ * κ₂) ^ 2) ≤ ccT₂ * cc₂ := by
    have h1 : c₂' * (16 * (CC₂ * κ₂) ^ 2)
        ≤ (min (ccT₂ * cc₂) (cc₂ ^ 2) / (64 * ((CC₂ * κ₂) ^ 2 + 1)))
          * (16 * (CC₂ * κ₂) ^ 2) :=
      mul_le_mul_of_nonneg_right hc₂'le2 (by positivity)
    have hden : 0 < 64 * ((CC₂ * κ₂) ^ 2 + 1) := by positivity
    have h2 : (min (ccT₂ * cc₂) (cc₂ ^ 2) / (64 * ((CC₂ * κ₂) ^ 2 + 1)))
        * (16 * (CC₂ * κ₂) ^ 2) ≤ ccT₂ * cc₂ := by
      have hX : min (ccT₂ * cc₂) (cc₂ ^ 2) ≤ ccT₂ * cc₂ := min_le_left _ _
      have hX0 : 0 ≤ min (ccT₂ * cc₂) (cc₂ ^ 2) :=
        le_of_lt (lt_min (mul_pos hccT₂pos hcc₂pos) (pow_pos hcc₂pos 2))
      have hY0 : 0 ≤ ccT₂ * cc₂ := (mul_pos hccT₂pos hcc₂pos).le
      have hZ : (0:ℝ) ≤ (CC₂ * κ₂) ^ 2 := sq_nonneg _
      have hmul : min (ccT₂ * cc₂) (cc₂ ^ 2) * (16 * (CC₂ * κ₂) ^ 2)
          ≤ (ccT₂ * cc₂) * (16 * (CC₂ * κ₂) ^ 2) :=
        mul_le_mul_of_nonneg_right hX (by positivity)
      have hYle : (ccT₂ * cc₂) * (16 * (CC₂ * κ₂) ^ 2)
          ≤ (ccT₂ * cc₂) * (64 * ((CC₂ * κ₂) ^ 2 + 1)) :=
        mul_le_mul_of_nonneg_left (by nlinarith [hZ]) hY0
      have hmul2 : (min (ccT₂ * cc₂) (cc₂ ^ 2) / (64 * ((CC₂ * κ₂) ^ 2 + 1)))
          * (16 * (CC₂ * κ₂) ^ 2)
          = min (ccT₂ * cc₂) (cc₂ ^ 2) * (16 * (CC₂ * κ₂) ^ 2)
            / (64 * ((CC₂ * κ₂) ^ 2 + 1)) := by ring
      rw [hmul2, div_le_iff₀ hden]
      linarith [hmul, hYle]
    linarith [h1, h2]
  have hs4₂ : c₂' * (16 * (CC₂ * κ₂) ^ 2) ≤ 1 * cc₂ ^ 2 := by
    have h1 : c₂' * (16 * (CC₂ * κ₂) ^ 2)
        ≤ (min (ccT₂ * cc₂) (cc₂ ^ 2) / (64 * ((CC₂ * κ₂) ^ 2 + 1)))
          * (16 * (CC₂ * κ₂) ^ 2) :=
      mul_le_mul_of_nonneg_right hc₂'le2 (by positivity)
    have hden : 0 < 64 * ((CC₂ * κ₂) ^ 2 + 1) := by positivity
    have h2 : (min (ccT₂ * cc₂) (cc₂ ^ 2) / (64 * ((CC₂ * κ₂) ^ 2 + 1)))
        * (16 * (CC₂ * κ₂) ^ 2) ≤ 1 * cc₂ ^ 2 := by
      have hX : min (ccT₂ * cc₂) (cc₂ ^ 2) ≤ cc₂ ^ 2 := min_le_right _ _
      have hX0 : 0 ≤ min (ccT₂ * cc₂) (cc₂ ^ 2) :=
        le_of_lt (lt_min (mul_pos hccT₂pos hcc₂pos) (pow_pos hcc₂pos 2))
      have hY0 : 0 ≤ cc₂ ^ 2 := sq_nonneg _
      have hZ : (0:ℝ) ≤ (CC₂ * κ₂) ^ 2 := sq_nonneg _
      have hmul : min (ccT₂ * cc₂) (cc₂ ^ 2) * (16 * (CC₂ * κ₂) ^ 2)
          ≤ cc₂ ^ 2 * (16 * (CC₂ * κ₂) ^ 2) :=
        mul_le_mul_of_nonneg_right hX (by positivity)
      have hYle : cc₂ ^ 2 * (16 * (CC₂ * κ₂) ^ 2)
          ≤ cc₂ ^ 2 * (64 * ((CC₂ * κ₂) ^ 2 + 1)) :=
        mul_le_mul_of_nonneg_left (by nlinarith [hZ]) hY0
      have hmul2 : (min (ccT₂ * cc₂) (cc₂ ^ 2) / (64 * ((CC₂ * κ₂) ^ 2 + 1)))
          * (16 * (CC₂ * κ₂) ^ 2)
          = min (ccT₂ * cc₂) (cc₂ ^ 2) * (16 * (CC₂ * κ₂) ^ 2)
            / (64 * ((CC₂ * κ₂) ^ 2 + 1)) := by ring
      rw [hmul2, div_le_iff₀ hden]
      linarith [hmul, hYle]
    linarith [h1, h2]
  -- the level-`3` constants
  set CC₃ : ℝ := 3 * max 1 (max 1 c₂') * CC₂ with hCC₃def
  have hCC₃pos : 0 < CC₃ := by
    have h1 : (1:ℝ) ≤ max 1 (max 1 c₂') := le_max_left _ _
    rw [hCC₃def]; nlinarith [hCC₂pos]
  set cc₃ : ℝ := cc₂ * min 1 (min 1 c₂') / (2 * 1) with hcc₃def
  have hcc₃pos : 0 < cc₃ := by
    rw [hcc₃def]
    exact div_pos (mul_pos hcc₂pos (lt_min one_pos (lt_min one_pos hc₂'pos)))
      (by norm_num)
  set ccT₃ : ℝ := min (3 * ccT₂ / 4) (min (5 * 1 * cc₂ / 8) (3 * c₂' * cc₂ / 4)) / 1
    with hccT₃def
  have hccT₃pos : 0 < ccT₃ := by
    rw [hccT₃def]
    refine div_pos (lt_min (by linarith [hccT₂pos]) (lt_min (by linarith [hcc₂pos]) ?_))
      one_pos
    positivity
  -- the third step coefficient
  obtain ⟨c₂ds2, hc₂ds2, hss₃⟩ := Work.FTS.CoercivityFix.exists_small_step_coeffs
    (cc := cc₃) (CC := CC₃) (κ := κE) (c₁ := 1) hcc₃pos hCC₃pos one_pos hκE0
  set c₂'' : ℝ := min c₂ds2 (min (min (ccT₃ * cc₃) (cc₃ ^ 2) / (64 * ((CC₃ * κ₂) ^ 2 + 1)))
    (1 / 2)) with hc₂''def
  have hc₂''pos : 0 < c₂'' :=
    lt_min hc₂ds2 (lt_min (div_pos (lt_min (mul_pos hccT₃pos hcc₃pos)
      (pow_pos hcc₃pos 2)) (by positivity)) (by norm_num))
  have hc₂''le : c₂'' ≤ c₂ds2 := min_le_left _ _
  have hss₃' : Work.FTS.CoercivityFix.StepSmall cc₃ CC₃ κE 1 c₂'' :=
    ⟨le_trans (mul_le_mul_of_nonneg_right hc₂''le (sq_nonneg _)) hss₃.1,
     le_trans (mul_le_mul_of_nonneg_right hc₂''le (sq_nonneg _)) hss₃.2⟩
  have hc₂''le2 : c₂'' ≤ min (ccT₃ * cc₃) (cc₃ ^ 2) / (64 * ((CC₃ * κ₂) ^ 2 + 1)) :=
    le_trans (min_le_right _ _) (min_le_left _ _)
  have hs3₃ : c₂'' * (16 * (CC₃ * κ₂) ^ 2) ≤ ccT₃ * cc₃ := by
    have h1 : c₂'' * (16 * (CC₃ * κ₂) ^ 2)
        ≤ (min (ccT₃ * cc₃) (cc₃ ^ 2) / (64 * ((CC₃ * κ₂) ^ 2 + 1)))
          * (16 * (CC₃ * κ₂) ^ 2) :=
      mul_le_mul_of_nonneg_right hc₂''le2 (by positivity)
    have hden : 0 < 64 * ((CC₃ * κ₂) ^ 2 + 1) := by positivity
    have h2 : (min (ccT₃ * cc₃) (cc₃ ^ 2) / (64 * ((CC₃ * κ₂) ^ 2 + 1)))
        * (16 * (CC₃ * κ₂) ^ 2) ≤ ccT₃ * cc₃ := by
      have hX : min (ccT₃ * cc₃) (cc₃ ^ 2) ≤ ccT₃ * cc₃ := min_le_left _ _
      have hX0 : 0 ≤ min (ccT₃ * cc₃) (cc₃ ^ 2) :=
        le_of_lt (lt_min (mul_pos hccT₃pos hcc₃pos) (pow_pos hcc₃pos 2))
      have hY0 : 0 ≤ ccT₃ * cc₃ := (mul_pos hccT₃pos hcc₃pos).le
      have hZ : (0:ℝ) ≤ (CC₃ * κ₂) ^ 2 := sq_nonneg _
      have hmul : min (ccT₃ * cc₃) (cc₃ ^ 2) * (16 * (CC₃ * κ₂) ^ 2)
          ≤ (ccT₃ * cc₃) * (16 * (CC₃ * κ₂) ^ 2) :=
        mul_le_mul_of_nonneg_right hX (by positivity)
      have hYle : (ccT₃ * cc₃) * (16 * (CC₃ * κ₂) ^ 2)
          ≤ (ccT₃ * cc₃) * (64 * ((CC₃ * κ₂) ^ 2 + 1)) :=
        mul_le_mul_of_nonneg_left (by nlinarith [hZ]) hY0
      have hmul2 : (min (ccT₃ * cc₃) (cc₃ ^ 2) / (64 * ((CC₃ * κ₂) ^ 2 + 1)))
          * (16 * (CC₃ * κ₂) ^ 2)
          = min (ccT₃ * cc₃) (cc₃ ^ 2) * (16 * (CC₃ * κ₂) ^ 2)
            / (64 * ((CC₃ * κ₂) ^ 2 + 1)) := by ring
      rw [hmul2, div_le_iff₀ hden]
      linarith [hmul, hYle]
    linarith [h1, h2]
  have hs4₃ : c₂'' * (16 * (CC₃ * κ₂) ^ 2) ≤ 1 * cc₃ ^ 2 := by
    have h1 : c₂'' * (16 * (CC₃ * κ₂) ^ 2)
        ≤ (min (ccT₃ * cc₃) (cc₃ ^ 2) / (64 * ((CC₃ * κ₂) ^ 2 + 1)))
          * (16 * (CC₃ * κ₂) ^ 2) :=
      mul_le_mul_of_nonneg_right hc₂''le2 (by positivity)
    have hden : 0 < 64 * ((CC₃ * κ₂) ^ 2 + 1) := by positivity
    have h2 : (min (ccT₃ * cc₃) (cc₃ ^ 2) / (64 * ((CC₃ * κ₂) ^ 2 + 1)))
        * (16 * (CC₃ * κ₂) ^ 2) ≤ 1 * cc₃ ^ 2 := by
      have hX : min (ccT₃ * cc₃) (cc₃ ^ 2) ≤ cc₃ ^ 2 := min_le_right _ _
      have hX0 : 0 ≤ min (ccT₃ * cc₃) (cc₃ ^ 2) :=
        le_of_lt (lt_min (mul_pos hccT₃pos hcc₃pos) (pow_pos hcc₃pos 2))
      have hY0 : 0 ≤ cc₃ ^ 2 := sq_nonneg _
      have hZ : (0:ℝ) ≤ (CC₃ * κ₂) ^ 2 := sq_nonneg _
      have hmul : min (ccT₃ * cc₃) (cc₃ ^ 2) * (16 * (CC₃ * κ₂) ^ 2)
          ≤ cc₃ ^ 2 * (16 * (CC₃ * κ₂) ^ 2) :=
        mul_le_mul_of_nonneg_right hX (by positivity)
      have hYle : cc₃ ^ 2 * (16 * (CC₃ * κ₂) ^ 2)
          ≤ cc₃ ^ 2 * (64 * ((CC₃ * κ₂) ^ 2 + 1)) :=
        mul_le_mul_of_nonneg_left (by nlinarith [hZ]) hY0
      have hmul2 : (min (ccT₃ * cc₃) (cc₃ ^ 2) / (64 * ((CC₃ * κ₂) ^ 2 + 1)))
          * (16 * (CC₃ * κ₂) ^ 2)
          = min (ccT₃ * cc₃) (cc₃ ^ 2) * (16 * (CC₃ * κ₂) ^ 2)
            / (64 * ((CC₃ * κ₂) ^ 2 + 1)) := by ring
      rw [hmul2, div_le_iff₀ hden]
      linarith [hmul, hYle]
    linarith [h1, h2]
  -- the level-`4` constants
  set CC₄ : ℝ := 3 * max 1 (max 1 c₂'') * CC₃ with hCC₄def
  have hCC₄pos : 0 < CC₄ := by
    have h1 : (1:ℝ) ≤ max 1 (max 1 c₂'') := le_max_left _ _
    rw [hCC₄def]; nlinarith [hCC₃pos]
  set ccT₄ : ℝ := min (3 * ccT₃ / 4) (min (5 * 1 * cc₃ / 8) (3 * c₂'' * cc₃ / 4)) / 1
    with hccT₄def
  have hccT₄pos : 0 < ccT₄ := by
    rw [hccT₄def]
    refine div_pos (lt_min (by linarith [hccT₃pos]) (lt_min (by linarith [hcc₃pos]) ?_))
      one_pos
    positivity
  -- the `α`-bound
  set A₁ : ℝ := min (1 * 2) 1 / (16 * (CC₁ * κ₁) ^ 2 + 1) with hA₁def
  set B₁ : ℝ := (2 / 8) / (CC₁ * κ₁ + 1) with hB₁def
  set A₂ : ℝ := min (ccT₂ * cc₂) 1 / (16 * (CC₂ * κ₁) ^ 2 + 1) with hA₂def
  set B₂ : ℝ := (cc₂ / 8) / (CC₂ * κ₁ + 1) with hB₂def
  set A₃ : ℝ := min (ccT₃ * cc₃) 1 / (16 * (CC₃ * κ₁) ^ 2 + 1) with hA₃def
  set B₃ : ℝ := (cc₃ / 8) / (CC₃ * κ₁ + 1) with hB₃def
  set α₂ : ℝ := min (1 / 10 ^ 14)
    (min (min (min A₁ B₁) (min A₂ B₂)) (min (min A₃ B₃) 1)) with hα₂def
  have hA₁pos : 0 < A₁ := by
    rw [hA₁def]
    exact div_pos (lt_min (by norm_num) one_pos) (by positivity)
  have hB₁pos : 0 < B₁ := by
    rw [hB₁def]; exact div_pos (by norm_num) (by positivity)
  have hA₂pos : 0 < A₂ := by
    rw [hA₂def]
    exact div_pos (lt_min (mul_pos hccT₂pos hcc₂pos) one_pos) (by positivity)
  have hB₂pos : 0 < B₂ := by
    rw [hB₂def]; exact div_pos (by linarith [hcc₂pos]) (by positivity)
  have hA₃pos : 0 < A₃ := by
    rw [hA₃def]
    exact div_pos (lt_min (mul_pos hccT₃pos hcc₃pos) one_pos) (by positivity)
  have hB₃pos : 0 < B₃ := by
    rw [hB₃def]; exact div_pos (by linarith [hcc₃pos]) (by positivity)
  have hα₂pos : 0 < α₂ := by
    rw [hα₂def]
    exact lt_min (by norm_num) (lt_min (lt_min (lt_min hA₁pos hB₁pos)
      (lt_min hA₂pos hB₂pos)) (lt_min (lt_min hA₃pos hB₃pos) one_pos))
  refine ⟨1, c₂, 1, c₂', 1, c₂'', one_pos, hc₂pos, one_pos, hc₂'pos, one_pos, hc₂''pos, ?_⟩
  refine ⟨α₂, ccT₄, CC₄, hα₂pos, hccT₄pos, hCC₄pos, ?_⟩
  intro α hαI
  have hα : 0 < α := hαI.1
  have hαA₁ : α ≤ A₁ := le_trans hαI.2 (by
    rw [hα₂def]; exact le_trans (min_le_right _ _) (le_trans (min_le_left _ _)
      (le_trans (min_le_left _ _) (min_le_left _ _))))
  have hαB₁ : α ≤ B₁ := le_trans hαI.2 (by
    rw [hα₂def]; exact le_trans (min_le_right _ _) (le_trans (min_le_left _ _)
      (le_trans (min_le_left _ _) (min_le_right _ _))))
  have hαA₂ : α ≤ A₂ := le_trans hαI.2 (by
    rw [hα₂def]; exact le_trans (min_le_right _ _) (le_trans (min_le_left _ _)
      (le_trans (min_le_right _ _) (min_le_left _ _))))
  have hαB₂ : α ≤ B₂ := le_trans hαI.2 (by
    rw [hα₂def]; exact le_trans (min_le_right _ _) (le_trans (min_le_left _ _)
      (le_trans (min_le_right _ _) (min_le_right _ _))))
  have hαA₃ : α ≤ A₃ := le_trans hαI.2 (by
    rw [hα₂def]; exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_left _ _) (min_le_left _ _))))
  have hαB₃ : α ≤ B₃ := le_trans hαI.2 (by
    rw [hα₂def]; exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_left _ _) (min_le_right _ _))))
  have hα1 : α ≤ 1 := le_trans hαI.2 (by
    rw [hα₂def]; exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (min_le_right _ _)))
  have hαe : α ∈ Set.Ioc 0 (1 / 10 ^ 14) := ⟨hα, le_trans hαI.2 (by
    rw [hα₂def]; exact min_le_left _ _)⟩
  have hα10 : -(1 / 10 : ℝ) ≤ α := by linarith
  -- the six `α`-conditions
  have hs1₁ : 1 * (16 * (CC₁ * α * κ₁) ^ 2) ≤ 1 * 2 := by
    have hmul : α * (16 * (CC₁ * κ₁) ^ 2 + 1) ≤ min (1 * 2) 1 := by
      have hden : 0 < 16 * (CC₁ * κ₁) ^ 2 + 1 := by positivity
      rw [hA₁def, le_div_iff₀ hden] at hαA₁
      linarith [hαA₁]
    have := key1 (A := 16 * (CC₁ * κ₁) ^ 2) (B := 1 * 2) (α := α)
      (by positivity) (by norm_num) (le_of_lt hα) hmul
    linarith [this]
  have hs2₁ : CC₁ * α * κ₁ ≤ 2 / 8 := by
    have hmul : α * (CC₁ * κ₁ + 1) ≤ 2 / 8 := by
      have hden : 0 < CC₁ * κ₁ + 1 := by positivity
      rw [hB₁def, le_div_iff₀ hden] at hαB₁
      linarith [hαB₁]
    have := key2 (A := CC₁ * κ₁) (B := 2 / 8) (α := α) (by positivity) (by norm_num)
      (le_of_lt hα) hmul
    linarith [this]
  have hs1₂ : 1 * (16 * (CC₂ * α * κ₁) ^ 2) ≤ ccT₂ * cc₂ := by
    have hmul : α * (16 * (CC₂ * κ₁) ^ 2 + 1) ≤ min (ccT₂ * cc₂) 1 := by
      have hden : 0 < 16 * (CC₂ * κ₁) ^ 2 + 1 := by positivity
      rw [hA₂def, le_div_iff₀ hden] at hαA₂
      linarith [hαA₂]
    have := key1 (A := 16 * (CC₂ * κ₁) ^ 2) (B := ccT₂ * cc₂) (α := α)
      (by positivity) (by positivity) (le_of_lt hα) hmul
    linarith [this]
  have hs2₂ : CC₂ * α * κ₁ ≤ cc₂ / 8 := by
    have hmul : α * (CC₂ * κ₁ + 1) ≤ cc₂ / 8 := by
      have hden : 0 < CC₂ * κ₁ + 1 := by positivity
      rw [hB₂def, le_div_iff₀ hden] at hαB₂
      linarith [hαB₂]
    have := key2 (A := CC₂ * κ₁) (B := cc₂ / 8) (α := α) (by positivity)
      (by linarith [hcc₂pos]) (le_of_lt hα) hmul
    linarith [this]
  have hs1₃ : 1 * (16 * (CC₃ * α * κ₁) ^ 2) ≤ ccT₃ * cc₃ := by
    have hmul : α * (16 * (CC₃ * κ₁) ^ 2 + 1) ≤ min (ccT₃ * cc₃) 1 := by
      have hden : 0 < 16 * (CC₃ * κ₁) ^ 2 + 1 := by positivity
      rw [hA₃def, le_div_iff₀ hden] at hαA₃
      linarith [hαA₃]
    have := key1 (A := 16 * (CC₃ * κ₁) ^ 2) (B := ccT₃ * cc₃) (α := α)
      (by positivity) (by positivity) (le_of_lt hα) hmul
    linarith [this]
  have hs2₃ : CC₃ * α * κ₁ ≤ cc₃ / 8 := by
    have hmul : α * (CC₃ * κ₁ + 1) ≤ cc₃ / 8 := by
      have hden : 0 < CC₃ * κ₁ + 1 := by positivity
      rw [hB₃def, le_div_iff₀ hden] at hαB₃
      linarith [hαB₃]
    have := key2 (A := CC₃ * κ₁) (B := cc₃ / 8) (α := α) (by positivity)
      (by linarith [hcc₃pos]) (le_of_lt hα) hmul
    linarith [this]
  -- the common defect inputs
  have hid1 : ∀ g : Fn, Work.FTS.StrongEps.EpsE4Thr.CoerAdmO α g → ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.Dth (Work.Coercivity.LGammaT α g) z θ
        = Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dth g) z θ + E1 α g z θ := by
    intro g hg z θ hmem
    exact Work.FTS.StrongEps.EpsE4Thr.TransO.Dth_LGammaT_eq_O α hg.1.1 hmem.1 hmem.2.1 hmem.2.2
  have hid2 : ∀ g : Fn, Work.FTS.StrongEps.EpsE4Thr.CoerAdmO α g → ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.Dz (Work.Coercivity.LGammaT α g) z θ
        = Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz g) z θ + E2 α g z θ := by
    intro g hg z θ hmem
    exact Work.FTS.StrongEps.EpsE4Thr.TransO.Dz_LGammaT_eq_O α hg.1.1
      (Work.FTS.StrongEps.EpsE4Thr.hardyHyp_of_coerAdmO (α := α) hα hαe.2 hg)
      hmem.1 hmem.2.1 hmem.2.2
  have hÊ1 : ∀ g : Fn, Work.FTS.StrongEps.EpsE4Thr.RegQo α 2 g →
      Work.Spaces.HkNorm α 1 (Work.FTS.CoercivityFix.E2hat g)
        ≤ κE * (Work.Spaces.HkNorm α 1 g + Work.Spaces.HkNorm α 1 (Work.Spaces.Dth g)) := by
    intro g hg
    have h0 : 0 ≤ Work.Spaces.HkNorm α 1 g + Work.Spaces.HkNorm α 1 (Work.Spaces.Dth g) := by
      rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm]; positivity
    have h := hÊ₁ α hα g hg
    have hle : κE₁ ≤ κE := le_max_left _ _
    nlinarith [h, hle, h0]
  have hÊ2 : ∀ g : Fn, Work.FTS.StrongEps.EpsE4Thr.RegQo α 3 g →
      Work.Spaces.HkNorm α 2 (Work.FTS.CoercivityFix.E2hat g)
        ≤ κE * (Work.Spaces.HkNorm α 2 g + Work.Spaces.HkNorm α 2 (Work.Spaces.Dth g)) := by
    intro g hg
    have h0 : 0 ≤ Work.Spaces.HkNorm α 2 g + Work.Spaces.HkNorm α 2 (Work.Spaces.Dth g) := by
      rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm]; positivity
    have h := hÊ₂ α hα g hg
    have hle : κE₂ ≤ κE := le_trans (le_max_left _ _) (le_max_right _ _)
    nlinarith [h, hle, h0]
  have hÊ3 : ∀ g : Fn, Work.FTS.StrongEps.EpsE4Thr.RegQo α 4 g →
      Work.Spaces.HkNorm α 3 (Work.FTS.CoercivityFix.E2hat g)
        ≤ κE * (Work.Spaces.HkNorm α 3 g + Work.Spaces.HkNorm α 3 (Work.Spaces.Dth g)) := by
    intro g hg
    have h0 : 0 ≤ Work.Spaces.HkNorm α 3 g + Work.Spaces.HkNorm α 3 (Work.Spaces.Dth g) := by
      rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm]; positivity
    have h := hÊ₃ α hα g hg
    have hle : κE₃ ≤ κE := le_trans (le_max_right _ _) (le_max_right _ _)
    nlinarith [h, hle, h0]
  -- level 1 → 2
  have hp₁ := Work.FTS.StrongEps.EpsE4Thr.TransO.stepPair_O α 1 hα (by norm_num) (by norm_num) (hcl := hCD₁ α ⟨hα, by linarith [hαe.2]⟩)
    (ht := ht₁ α hαe) (hc := Work.FTS.StrongEps.EpsE4Thr.Comm2_L1_O α hα) (hcw := (hok₁ α hα hα1).1) (hcs1 := fun g hg => ((hok₁ α hα hα1).2 g hg).2.2.1)
    (hcs2 := fun g hg => ((hok₁ α hα hα1).2 g hg).2.2.2)
    (hreg := Work.FTS.StrongEps.EpsE4Thr.StepReg2_all_O α hα 1) (hκE := hκE0)
    (hκ₁ := hκ₁) (hκ₂ := hκ₂) (hJ := hc₂pos) (hÊ := hÊ1) (hid1 := hid1) (hid2 := hid2)
    (hbk1 := fun g hg => ((hok₁ α hα hα1).2 g hg).1) (hbk2 := fun g hg => ((hok₁ α hα hα1).2 g hg).2.1)
    (hnA := fun g hg => (hE1' α hα hα1 1 (by norm_num) g hg))
    (hnB := fun g hg => (hE2' α hα hα1 1 (by norm_num) g hg))
    (hsmall := hss₁') (hs3 := hs3₁) (hs4 := hs4₁) (hs1 := hs1₁) (hs2 := hs2₁)
  obtain ⟨_, _, hcl₂, ht₂⟩ := hp₁
  -- level 2 → 3
  have hLP₂ := hok₂ α hα hα1 c₂ hc₂pos
  have hp₂ := Work.FTS.StrongEps.EpsE4Thr.TransO.stepPair_O α 2 hα (by norm_num) (by norm_num) (hcl := hcl₂) (ht := ht₂)
    (hc := Work.FTS.StrongEps.EpsE4Thr.Comm2_succ_O α hα 1 (Work.FTS.StrongEps.EpsE4Thr.Comm2_L1_O α hα)) (hcw := hLP₂.1) (hcs1 := fun g hg => (hLP₂.2 g hg).2.2.1)
    (hcs2 := fun g hg => (hLP₂.2 g hg).2.2.2)
    (hreg := Work.FTS.StrongEps.EpsE4Thr.StepReg2_all_O α hα 2) (hκE := hκE0)
    (hκ₁ := hκ₁) (hκ₂ := hκ₂) (hJ := hc₂'pos) (hÊ := hÊ2) (hid1 := hid1) (hid2 := hid2)
    (hbk1 := fun g hg => (hLP₂.2 g hg).1) (hbk2 := fun g hg => (hLP₂.2 g hg).2.1)
    (hnA := fun g hg => (hE1' α hα hα1 2 (by norm_num) g hg))
    (hnB := fun g hg => (hE2' α hα hα1 2 (by norm_num) g hg))
    (hsmall := hss₂') (hs3 := hs3₂) (hs4 := hs4₂) (hs1 := hs1₂) (hs2 := hs2₂)
  obtain ⟨_, _, hcl₃, ht₃⟩ := hp₂
  -- level 3 → 4
  have hLP₃ := hok₃ α hα hα1 c₂ c₂' hc₂pos hc₂'pos
  have hp₃ := Work.FTS.StrongEps.EpsE4Thr.TransO.stepPair_O α 3 hα (by norm_num) (by norm_num) (hcl := hcl₃) (ht := ht₃)
    (hc := Work.FTS.StrongEps.EpsE4Thr.Comm2_succ_O α hα 2 (Work.FTS.StrongEps.EpsE4Thr.Comm2_succ_O α hα 1 (Work.FTS.StrongEps.EpsE4Thr.Comm2_L1_O α hα))) (hcw := hLP₃.1) (hcs1 := fun g hg => (hLP₃.2 g hg).2.2.1)
    (hcs2 := fun g hg => (hLP₃.2 g hg).2.2.2)
    (hreg := Work.FTS.StrongEps.EpsE4Thr.StepReg2_all_O α hα 3) (hκE := hκE0)
    (hκ₁ := hκ₁) (hκ₂ := hκ₂) (hJ := hc₂''pos) (hÊ := hÊ3) (hid1 := hid1) (hid2 := hid2)
    (hbk1 := fun g hg => (hLP₃.2 g hg).1) (hbk2 := fun g hg => (hLP₃.2 g hg).2.1)
    (hnA := fun g hg => (hE1' α hα hα1 3 (by norm_num) g hg))
    (hnB := fun g hg => (hE2' α hα hα1 3 (by norm_num) g hg))
    (hsmall := hss₃') (hs3 := hs3₃) (hs4 := hs4₃) (hs1 := hs1₃) (hs2 := hs2₃)
  obtain ⟨_, _, hcl₄, ht₄⟩ := hp₃
  simpa only [Work.FTS.CoercivityFix.Assembly.IP4] using ht₄

end Work.FTS.StrongEps.EpsE4Thr.TransO
