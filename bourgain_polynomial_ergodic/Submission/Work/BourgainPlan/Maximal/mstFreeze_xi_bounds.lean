import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_lvl_err_aux
import Submission.Work.BourgainPlan.Maximal.mst_freeze_defs
import Submission.Work.BourgainPlan.Maximal.mstTht_deriv_bounds
import Submission.Work.BourgainPlan.Maximal.mstHat_decay_of_contDiff
import Submission.Work.BourgainPlan.Maximal.mst_lvl_approx_pointwise
import Submission.Work.BourgainPlan.Maximal.mstHat_bound
import Submission.Work.BourgainPlan.Maximal.mst_freeze_small
import Submission.Work.BourgainPlan.Maximal.mst_freeze_arith
import Submission.Work.BourgainPlan.Maximal.norm_deriv2_dilated_mul_le

/-!
# The two size constants of `mstHat (mstFreezeXi …)`

For `β ∈ 𝒰(s+1)`, the level scale `c = c_s = 2^{s(d−χ)}` and `J = ⌊exp √(s+1)⌋`, the frozen symbol
`Ξ = mstFreezeXi P J β c η` (`Ξ w = mstTht P J β (iwRep β) (w/c) · η w`) is small where the bump
lives: `‖mstTht …‖ ≤ C₁ exp(−√(s+1)/2)` on `closure {u | η (c u) ≠ 0}` (`mstTht_small_on_closure`).
Consequently

* `‖mstHat Ξ t‖ ≤ C₁ exp(−√(s+1)/2) · M` for every `t` (`mstHat_bound`), and
* `‖mstHat Ξ t‖ ≤ (A exp(−√(s+1)/2) (G₀ + 2G₁ + G₂) / (2π)²) / t²` for `t ≠ 0`, where
  `G₀ = ∫‖η‖`, `G₁ = ∫‖η'‖`, `G₂ = ∫‖η''‖` (`mstHat_decay_of_contDiff` together with the `L¹`
  bound on `Ξ''` obtained by integrating the pointwise estimate `norm_deriv2_dilated_mul_le`).

Both constants are absorbed into a single `C` independent of `s` and `β`.
-/

open MeasureTheory

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.BourgainPlan.Maximal

open Work.BourgainPlan.IonescuWainger

noncomputable section

/-- A `C²` function vanishing off the closed fundamental interval is integrable, together with its
first two derivatives. -/
theorem integrable_iteratedDeriv_two_of_contDiff_support_aux {η : ℝ → ℂ} (hηc : ContDiff ℝ 2 η)
    (hη0 : ∀ x : ℝ, 1 / 2 < |x| → η x = 0) :
    Integrable η ∧ Integrable (deriv η) ∧ Integrable (iteratedDeriv 2 η) := by
  have hid2 : iteratedDeriv 2 η = deriv (deriv η) := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  have hcs : HasCompactSupport η :=
    HasCompactSupport.intro isCompact_Icc (fun x hx => by
      rw [Set.mem_Icc] at hx
      have hlt : x < -(1 / 2) ∨ 1 / 2 < x := by
        rcases not_and_or.mp hx with h | h
        · exact Or.inl (not_le.mp h)
        · exact Or.inr (not_le.mp h)
      rcases hlt with hlt | hlt
      · exact hη0 x (by rw [abs_of_neg (by linarith)]; linarith)
      · exact hη0 x (by rw [abs_of_pos (by linarith)]; linarith))
  have h1 : Integrable η := hηc.continuous.integrable_of_hasCompactSupport hcs
  have hcd1 : Continuous (deriv η) := by
    rw [← iteratedDeriv_one]
    exact hηc.continuous_iteratedDeriv 1 (by norm_num)
  have h2 : Integrable (deriv η) := hcd1.integrable_of_hasCompactSupport hcs.deriv
  have hcd2 : Continuous (deriv (deriv η)) := by
    have h := hηc.continuous_iteratedDeriv 2 le_rfl
    rwa [hid2] at h
  have h3 : Integrable (iteratedDeriv 2 η) := by
    rw [hid2]
    exact hcd2.integrable_of_hasCompactSupport hcs.deriv.deriv
  exact ⟨h1, h2, h3⟩

theorem mstFreeze_xi_bounds (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (hc : 0 < P.leadingCoeff)
    (l : ℕ) (hl : 1 ≤ l) {χ : ℝ} (hχ0 : 0 < χ) (hχ1 : χ < 1 / 10)
    (η : ℝ → ℂ) (M : ℝ) (hM : 0 < M) (hηc : ContDiff ℝ 2 η)
    (hηbd : ∀ x : ℝ, ‖η x‖ ≤ M) (hη0 : ∀ x : ℝ, 1 / 2 < |x| → η x = 0)
    (hder1 : ∀ x : ℝ, |x| * ‖deriv η x‖ ≤ M)
    (hder2 : ∀ x : ℝ, |x| ^ 2 * ‖iteratedDeriv 2 η x‖ ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s →
      ∀ β ∈ Work.BourgainPlan.Maximal.mstU l (s + 1),
      (∀ t : ℝ, ‖Work.BourgainPlan.Maximal.mstHat
          (Work.BourgainPlan.Maximal.mstFreezeXi P (⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊) β
            (Work.BourgainPlan.Maximal.mstScale P.natDegree χ s) η) t‖
        ≤ C * Real.exp (-(Real.sqrt ((s : ℝ) + 1) / 2))) ∧
      (∀ t : ℝ, t ≠ 0 → ‖Work.BourgainPlan.Maximal.mstHat
          (Work.BourgainPlan.Maximal.mstFreezeXi P (⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊) β
            (Work.BourgainPlan.Maximal.mstScale P.natDegree χ s) η) t‖
        ≤ (C * Real.exp (-(Real.sqrt ((s : ℝ) + 1) / 2))) / t ^ 2) := by
  have hχd : χ + 1 ≤ (P.natDegree : ℝ) := by
    have h2 : (2 : ℝ) ≤ (P.natDegree : ℝ) := by exact_mod_cast hd
    linarith
  obtain ⟨hηi, hηi1, hηi2⟩ := integrable_iteratedDeriv_two_of_contDiff_support_aux hηc hη0
  obtain ⟨C₁, hC₁pos, N₁, hsmall⟩ := mstTht_small_on_closure P hd hc hχ0 hχ1 η hη0 l hl
  set A : ℝ := max C₁ 1 with hAdef
  have hA1 : 1 ≤ A := le_max_right _ _
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA1
  have hC₁leA : C₁ ≤ A := le_max_left _ _
  obtain ⟨s_ar, har⟩ := mst_freeze_arith P hd hχ0 hχ1 A hA1
  set G0 : ℝ := ∫ x, ‖η x‖ with hG0def
  set G1 : ℝ := ∫ x, ‖deriv η x‖ with hG1def
  set G2 : ℝ := ∫ x, ‖iteratedDeriv 2 η x‖ with hG2def
  have hG0nn : 0 ≤ G0 := by rw [hG0def]; exact integral_nonneg (fun x => norm_nonneg _)
  have hG1nn : 0 ≤ G1 := by rw [hG1def]; exact integral_nonneg (fun x => norm_nonneg _)
  have hG2nn : 0 ≤ G2 := by rw [hG2def]; exact integral_nonneg (fun x => norm_nonneg _)
  set C : ℝ := max (A * M) (A * (G0 + 2 * G1 + G2) / (2 * Real.pi) ^ 2) with hCdef
  have hCM : A * M ≤ C := le_max_left _ _
  have hCden : A * (G0 + 2 * G1 + G2) / (2 * Real.pi) ^ 2 ≤ C := le_max_right _ _
  have hCpos : 0 < C := lt_of_lt_of_le (mul_pos hApos hM) hCM
  refine ⟨C, hCpos, max (max N₁ s_ar) 1, ?_⟩
  intro s hs β hβ
  have hsN : N₁ ≤ s := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hs)
  have hssar : s_ar ≤ s := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hs)
  obtain ⟨hs1, hJ3, hLc, hL2c⟩ := har s hssar
  set J : ℕ := ⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊ with hJdef
  set c : ℝ := mstScale P.natDegree χ s with hcdef
  set e : ℝ := Real.exp (-(Real.sqrt ((s : ℝ) + 1) / 2)) with hedef
  have hepos : 0 < e := by rw [hedef]; exact Real.exp_pos _
  have hJ3' : 3 ≤ J := by rw [hJdef]; exact hJ3
  have hc1 : 1 ≤ c := by rw [hcdef]; exact one_le_mstScale hχd s
  have hcpos : 0 < c := by rw [hcdef]; exact mstScale_pos P.natDegree χ s
  have hLc' : mstThtL P J / c ≤ A * e := by rw [hJdef, hcdef, hedef]; exact hLc
  have hL2c' : mstThtL P J ^ 2 / c ^ 2 ≤ A * e := by rw [hJdef, hcdef, hedef]; exact hL2c
  set Ξ : ℝ → ℂ := mstFreezeXi P J β c η with hΞdef
  obtain ⟨hcdTht, hder1Tht, hder2Tht⟩ := mstTht_deriv_bounds P J β (iwRep β) (by omega)
  have hsmallB : ∀ u : ℝ, u ∈ closure {u : ℝ | η (c * u) ≠ 0} →
      ‖mstTht P J β (iwRep β) u‖ ≤ C₁ * e := by
    intro u hu
    have hu' : u ∈ closure {u : ℝ | η (mstScale P.natDegree χ s * u) ≠ 0} := by
      rwa [hcdef] at hu
    have h := hsmall s hsN β hβ u hu'
    rw [hJdef, hedef]
    exact h
  have hΞpt : ∀ w : ℝ, Ξ w = mstTht P J β (iwRep β) (w / c) * η w := by
    intro w; rw [hΞdef, mstFreezeXi_apply]
  have hΞbd : ∀ w : ℝ, ‖Ξ w‖ ≤ (C₁ * e) * M := by
    intro w
    rw [hΞpt w, norm_mul]
    by_cases hw : η w = 0
    · rw [hw, norm_zero, mul_zero]; positivity
    · have hmem : w / c ∈ closure {u : ℝ | η (c * u) ≠ 0} :=
        subset_closure (by
          rw [Set.mem_ofPred_eq, show c * (w / c) = w from by
            rw [mul_comm]; exact div_mul_cancel₀ w (ne_of_gt hcpos)]
          exact hw)
      exact mul_le_mul (hsmallB (w / c) hmem) (hηbd w) (norm_nonneg _)
        (mul_nonneg hC₁pos.le hepos.le)
  have hΞsupp : ∀ w : ℝ, 1 / 2 < |w| → Ξ w = 0 := by
    intro w hw; rw [hΞpt w, hη0 w hw, mul_zero]
  have hcdΞ : ContDiff ℝ 2 Ξ := by
    rw [hΞdef]
    exact (hcdTht.comp (contDiff_id.div_const c)).mul hηc
  -- ## The `L¹` bound on the second derivative of `Ξ`
  have hpt : ∀ w : ℝ, ‖deriv (deriv Ξ) w‖
      ≤ (mstThtL P J ^ 2 / c ^ 2) * ‖η w‖ + 2 * (mstThtL P J / c) * ‖deriv η w‖
        + (C₁ * e) * ‖iteratedDeriv 2 η w‖ := by
    intro w
    rw [hΞdef]
    exact norm_deriv2_dilated_mul_le (fun u : ℝ => mstTht P J β (iwRep β) u) η hcdTht hηc c
      hcpos hder1Tht hder2Tht hsmallB w
  have hI1 : Integrable (fun w : ℝ => (mstThtL P J ^ 2 / c ^ 2) * ‖η w‖) :=
    hηi.norm.const_mul _
  have hI2 : Integrable (fun w : ℝ => 2 * (mstThtL P J / c) * ‖deriv η w‖) :=
    hηi1.norm.const_mul _
  have hI3 : Integrable (fun w : ℝ => (C₁ * e) * ‖iteratedDeriv 2 η w‖) :=
    hηi2.norm.const_mul _
  have hI12 : Integrable (fun w : ℝ => (mstThtL P J ^ 2 / c ^ 2) * ‖η w‖
      + 2 * (mstThtL P J / c) * ‖deriv η w‖) := hI1.add hI2
  have hIrhs : Integrable (fun w : ℝ => (mstThtL P J ^ 2 / c ^ 2) * ‖η w‖
      + 2 * (mstThtL P J / c) * ‖deriv η w‖ + (C₁ * e) * ‖iteratedDeriv 2 η w‖) :=
    hI12.add hI3
  have hL1 : ∫ w : ℝ, ‖deriv (deriv Ξ) w‖
      ≤ mstThtL P J ^ 2 / c ^ 2 * G0 + 2 * (mstThtL P J / c) * G1 + (C₁ * e) * G2 := by
    have hmono : ∫ w : ℝ, ‖deriv (deriv Ξ) w‖
        ≤ ∫ w : ℝ, ((mstThtL P J ^ 2 / c ^ 2) * ‖η w‖
            + 2 * (mstThtL P J / c) * ‖deriv η w‖ + (C₁ * e) * ‖iteratedDeriv 2 η w‖) :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall (fun w => norm_nonneg _)) hIrhs
        (Filter.Eventually.of_forall hpt)
    refine hmono.trans ?_
    rw [integral_add hI12 hI3, integral_add hI1 hI2, integral_const_mul, integral_const_mul,
      integral_const_mul, ← hG0def, ← hG1def, ← hG2def]
  have hInt : ∫ x : ℝ, ‖deriv (deriv Ξ) x‖ ≤ (A * e) * (G0 + 2 * G1 + G2) := by
    refine hL1.trans ?_
    have h1 : mstThtL P J ^ 2 / c ^ 2 * G0 ≤ A * e * G0 :=
      mul_le_mul_of_nonneg_right hL2c' hG0nn
    have h2 : 2 * (mstThtL P J / c) * G1 ≤ 2 * (A * e) * G1 := by
      have h := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hLc' hG1nn)
        (by norm_num : (0 : ℝ) ≤ 2)
      calc 2 * (mstThtL P J / c) * G1 = 2 * ((mstThtL P J / c) * G1) := by ring
        _ ≤ 2 * ((A * e) * G1) := h
        _ = 2 * (A * e) * G1 := by ring
    have h3 : (C₁ * e) * G2 ≤ (A * e) * G2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC₁leA hepos.le) hG2nn
    calc mstThtL P J ^ 2 / c ^ 2 * G0 + 2 * (mstThtL P J / c) * G1 + (C₁ * e) * G2
        ≤ (A * e) * G0 + 2 * (A * e) * G1 + (A * e) * G2 := by linarith [h1, h2, h3]
      _ = (A * e) * (G0 + 2 * G1 + G2) := by ring
  have hCU : A * (G0 + 2 * G1 + G2) ≤ C * (2 * Real.pi) ^ 2 := by
    have h2π : (0 : ℝ) < (2 * Real.pi) ^ 2 := by positivity
    have h := mul_le_mul_of_nonneg_right hCden h2π.le
    rwa [div_mul_cancel₀ _ (ne_of_gt h2π)] at h
  refine ⟨?_, ?_⟩
  · intro t
    calc ‖mstHat Ξ t‖ ≤ (C₁ * e) * M := mstHat_bound (mul_nonneg (mul_nonneg hC₁pos.le hepos.le)
          hM.le) hΞbd t
      _ = (C₁ * M) * e := by ring
      _ ≤ (A * M) * e :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC₁leA hM.le) hepos.le
      _ ≤ C * e := mul_le_mul_of_nonneg_right hCM hepos.le
  · intro t ht
    have hdec := mstHat_decay_of_contDiff Ξ hcdΞ hΞsupp t ht
    refine hdec.trans ?_
    have hstep : (∫ x : ℝ, ‖deriv (deriv Ξ) x‖) / (2 * Real.pi) ^ 2 ≤ C * e := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < (2 * Real.pi) ^ 2)]
      calc ∫ x : ℝ, ‖deriv (deriv Ξ) x‖ ≤ (A * e) * (G0 + 2 * G1 + G2) := hInt
        _ = e * (A * (G0 + 2 * G1 + G2)) := by ring
        _ ≤ e * (C * (2 * Real.pi) ^ 2) := mul_le_mul_of_nonneg_left hCU hepos.le
        _ = (C * e) * (2 * Real.pi) ^ 2 := by ring
    exact div_le_div_of_nonneg_right hstep (sq_nonneg t)

end

end Work.BourgainPlan.Maximal
