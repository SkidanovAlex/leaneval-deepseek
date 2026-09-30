import Mathlib
import Submission.Commons.NumberTheory.Zeta.xiE_circle_growth
import Submission.Commons.NumberTheory.Zeta.xiE_noZero_ball
import Submission.Commons.NumberTheory.Zeta.xiE_zeroCount
import Submission.Commons.NumberTheory.Linnik.logDeriv_circle_residue
import Submission.Commons.NumberTheory.Linnik.partialFraction_tail
import Submission.Commons.NumberTheory.Linnik.goodRadius_geometric
import Submission.Commons.NumberTheory.Linnik.completedL_pf_identity_rect
import Submission.Commons.NumberTheory.Linnik.partialFraction_conv
import Submission.Commons.NumberTheory.Linnik.divisor_eq_closedBall_subset
import Submission.Commons.Analysis.Complex.circleLogDerivContour_bound
import Submission.Commons.NumberTheory.Linnik.ell_pow_div_self_tendsto_zero

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open Complex Filter Metric Set Function MeromorphicOn Topology
open scoped Real Topology BigOperators
set_option autoImplicit false
set_option maxHeartbeats 0

namespace Commons.NumberTheory.Zeta

/-- the entire completion `Ξ(s) = 1/2 + (1/2)·s·(s−1)·Λ₀(s)` -/
private def xiF (s : ℂ) : ℂ := (1 / 2 : ℂ) + (1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta₀ s

private lemma xiF_diff : Differentiable ℂ xiF := by
  unfold xiF
  have hΛ : Differentiable ℂ completedRiemannZeta₀ := differentiable_completedZeta₀
  have hhead : Differentiable ℂ (fun s : ℂ => (1 / 2 : ℂ) * s * (s - 1)) := by fun_prop
  exact ((differentiable_const (1 / 2 : ℂ)).add (hhead.mul hΛ))

private lemma xiF_zero_ne : xiF 0 ≠ 0 := by
  unfold xiF
  norm_num

private lemma xiF_zero_val : xiF 0 = (1 / 2 : ℂ) := by
  unfold xiF
  norm_num

private lemma xiF_an (U : Set ℂ) : AnalyticOnNhd ℂ xiF U := by
  intro z hz
  exact xiF_diff.analyticAt z

private lemma xiF_ne_zero_ball :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧ ∀ u : ℂ, ‖u‖ < δ₀ → xiF u ≠ 0 := by
  rcases xiE_noZero_ball with ⟨δ₀, h₁, h₂, h₃⟩
  refine ⟨δ₀, h₁, h₂, ?_⟩
  intro u hu
  exact h₃ u hu

/-- zero count for `xiF` in a closed ball (Jensen + circle growth). -/
private lemma xiF_zeroCount :
    ∃ c : ℝ, ∀ R : ℝ, 2 ≤ R →
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor xiF (Metric.closedBall 0 R)) u : ℤ) : ℝ)) ≤
        c * R * (Real.log (R + 2) + 2) := by
  classical
  rcases xiE_zeroCount with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  intro R hR
  exact hc R hR

/-- circle growth for `xiF`. -/
private lemma xiF_growth :
    ∃ c : ℝ, ∀ R : ℝ, 2 ≤ R → ∀ z : ℂ, ‖z‖ = R →
      ‖xiF z‖ ≤ Real.exp (c * R * (Real.log (R + 2) + 2)) := by
  classical
  rcases xiE_circle_growth with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  intro R hR z hz
  exact hc R hR z hz

/-! ### Divisor/zero-set bookkeeping for `xiF` (generic copy of the L-function lemmas) -/

private lemma xiF_zeroCoeff_ge_one {B : ℝ} {z : ℂ} (hzB : ‖z‖ ≤ B)
    (hz0 : xiF z = 0) :
    (1 : ℤ) ≤ (MeromorphicOn.divisor xiF (Metric.closedBall (0 : ℂ) B)) z := by
  have hΛne : xiF ≠ 0 := by
    intro h
    exact xiF_zero_ne (congrFun h 0)
  have hzK : z ∈ closedBall (0 : ℂ) B := by simpa [Metric.mem_closedBall, dist_eq_norm] using hzB
  have hnz : MeromorphicOn.divisor xiF (closedBall (0 : ℂ) B) z ≠ 0 :=
    Commons.NumberTheory.Linnik.divisor_ne_zero_of_apply_eq_zero xiF_diff hΛne hzK hz0
  have hnn : (0 : ℤ) ≤ MeromorphicOn.divisor xiF (closedBall (0 : ℂ) B) z := by
    exact (MeromorphicOn.AnalyticOnNhd.divisor_nonneg (f := xiF) (U := closedBall (0 : ℂ) B) (xiF_an _)) z
  omega

private lemma xiF_zeroSet_subset_divisorSupport {B : ℝ} :
    ({u : ℂ | xiF u = 0 ∧ ‖u‖ ≤ B} : Set ℂ) ⊆
      Function.support (fun u : ℂ =>
        MeromorphicOn.divisor xiF (Metric.closedBall (0 : ℂ) B) u) := by
  intro z hz
  rw [Function.mem_support]
  have hΛne : xiF ≠ 0 := by
    intro h
    exact xiF_zero_ne (congrFun h 0)
  have hzK : z ∈ closedBall (0 : ℂ) B := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hz.2
  exact Commons.NumberTheory.Linnik.divisor_ne_zero_of_apply_eq_zero xiF_diff hΛne hzK hz.1

private lemma xiF_zeroSet_finite {B : ℝ} (hB : 0 ≤ B) :
    ({u : ℂ | xiF u = 0 ∧ ‖u‖ ≤ B} : Set ℂ).Finite := by
  have hsup : (Function.support fun u : ℂ => MeromorphicOn.divisor xiF (closedBall (0 : ℂ) B) u).Finite := by
    simpa using (MeromorphicOn.divisor_support_finite_of_subset (f := xiF) (U := closedBall (0 : ℂ) B)
      (V := closedBall (0 : ℂ) B) (xiF_an _).meromorphicOn (isCompact_closedBall (0 : ℂ) B)
        (by intro z hz; exact hz))
  exact hsup.subset xiF_zeroSet_subset_divisorSupport

private lemma xiF_zeroCard_le_divisorFinsum {B : ℝ} (hB : 0 ≤ B) :
    let Z : Set ℂ := {u : ℂ | xiF u = 0 ∧ ‖u‖ ≤ B}
    ∀ hZ : Z.Finite,
      ((hZ.toFinset.card : ℝ) ≤
        ∑ᶠ u : ℂ, (((MeromorphicOn.divisor xiF (Metric.closedBall (0 : ℂ) B)) u : ℤ) : ℝ)) := by
  intro Z hZ
  let coeff : ℂ → ℤ := fun u => MeromorphicOn.divisor xiF (closedBall (0 : ℂ) B) u
  have hcoeff_nonneg (u : ℂ) : (0 : ℤ) ≤ coeff u := by
    exact (MeromorphicOn.AnalyticOnNhd.divisor_nonneg (f := xiF) (U := closedBall (0 : ℂ) B) (xiF_an _)) u
  have hsupFin : (Function.support coeff).Finite := by
    simpa [coeff] using (MeromorphicOn.divisor_support_finite_of_subset (f := xiF)
      (U := closedBall (0 : ℂ) B) (V := closedBall (0 : ℂ) B) (xiF_an _).meromorphicOn
        (isCompact_closedBall (0 : ℂ) B) (by intro z hz; exact hz))
  let Zfin : Finset ℂ := hZ.toFinset
  let supp : Finset ℂ := hsupFin.toFinset
  have hmem_Zfin (z : ℂ) : z ∈ Zfin ↔ z ∈ Z := by
    dsimp [Zfin]
    exact hZ.mem_toFinset
  have hmem_supp (z : ℂ) : z ∈ supp ↔ z ∈ Function.support coeff := by
    dsimp [supp]
    exact hsupFin.mem_toFinset
  have hZsub_supp : Zfin ⊆ supp := by
    intro z hz
    rw [hmem_supp]
    have hzZ : z ∈ Z := (hmem_Zfin z).1 hz
    have hmem : z ∈ Function.support coeff := by
      rw [Function.mem_support]
      dsimp [coeff]
      have hge : (1 : ℤ) ≤ (MeromorphicOn.divisor xiF (closedBall (0 : ℂ) B)) z :=
        xiF_zeroCoeff_ge_one (B := B) hzZ.2 hzZ.1
      exact ne_of_gt (lt_of_lt_of_le (by norm_num) hge)
    exact hmem
  have hsum_Zfin : (Zfin.card : ℝ) ≤ ∑ z ∈ Zfin, ((coeff z : ℤ) : ℝ) := by
    calc
      (Zfin.card : ℝ) = ∑ z ∈ Zfin, (1 : ℝ) := by
        exact_mod_cast (Finset.card_eq_sum_ones Zfin)
      _ ≤ ∑ z ∈ Zfin, ((coeff z : ℤ) : ℝ) := by
        refine Finset.sum_le_sum ?_
        intro z hz
        have hge : (1 : ℤ) ≤ coeff z := by
          have hzZ : z ∈ Z := (hmem_Zfin z).1 hz
          exact xiF_zeroCoeff_ge_one (B := B) hzZ.2 hzZ.1
        exact_mod_cast hge
  have hsum_le_supp : (∑ z ∈ Zfin, ((coeff z : ℤ) : ℝ)) ≤ ∑ z ∈ supp, ((coeff z : ℤ) : ℝ) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hZsub_supp ?_
    intro z hz _hznot
    exact_mod_cast hcoeff_nonneg z
  have hsupp_eq_finsum : (∑ z ∈ supp, ((coeff z : ℤ) : ℝ)) =
      ∑ᶠ u : ℂ, (((coeff u : ℤ) : ℝ)) := by
    refine (finsum_eq_finsetSum_of_support_subset (f := fun u : ℂ => ((coeff u : ℤ) : ℝ))
      (s := supp) ?_).symm
    intro u hu
    have huS : u ∈ Function.support coeff := by
      rw [Function.mem_support] at hu ⊢
      dsimp at hu
      exact_mod_cast hu
    exact (hmem_supp u).2 huS
  calc
    ((hZ.toFinset.card : ℝ)) = (Zfin.card : ℝ) := rfl
    _ ≤ ∑ z ∈ Zfin, ((coeff z : ℤ) : ℝ) := hsum_Zfin
    _ ≤ ∑ z ∈ supp, ((coeff z : ℤ) : ℝ) := hsum_le_supp
    _ = ∑ᶠ u : ℂ, (((coeff u : ℤ) : ℝ)) := hsupp_eq_finsum
    _ = ∑ᶠ u : ℂ, (((MeromorphicOn.divisor xiF (Metric.closedBall (0 : ℂ) B)) u : ℤ) : ℝ) := by
      simp [coeff]

/-! ### Good radius for `xiF` (adapted from `goodRadius_geometric`) -/

private lemma xiF_goodRadius :
    ∃ A₀ : ℝ, 0 < A₀ ∧ ∀ A : ℝ, A₀ ≤ A → ∃ T : ℝ, A ≤ T ∧ T ≤ 2 * A ∧
      ∀ u : ℂ, xiF u = 0 →
          (Real.log (A + 2) + 2) ^ 2 * |‖u‖ - T| ≥ 1 := by
  classical
  rcases xiF_zeroCount with ⟨c0, hc0⟩
  let c : ℝ := max c0 1
  have hc0le : c0 ≤ c := le_max_left c0 1
  have hcge1 : (1 : ℝ) ≤ c := le_max_right c0 1
  have hcge0 : 0 ≤ c := by linarith
  have hc_bound : ∀ R : ℝ, 2 ≤ R →
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor xiF (Metric.closedBall (0 : ℂ) R)) u : ℤ) : ℝ)) ≤
        c * R * (Real.log (R + 2) + 2) := by
    intro R hR
    have hR0 : 0 ≤ R := by linarith
    have hℓR0 : 0 ≤ Real.log (R + 2) + 2 := by
      have h1 : 0 ≤ Real.log (R + 2) := by
        refine Real.log_nonneg ?_
        linarith
      linarith
    exact le_trans (hc0 R hR) (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc0le hR0) hℓR0)
  refine ⟨max 2 (Real.exp (12 * c + 10)), ?_, ?_⟩
  · have hpos2 : 0 < (2 : ℝ) := by norm_num
    exact lt_of_lt_of_le hpos2 (le_max_left _ _)
  · intro A hA₀le
    let L : ℝ := Real.log (A + 2) + 2
    let B : ℝ := 2 * A + 2
    have hA2 : 2 ≤ A := by
      have : (2 : ℝ) ≤ max 2 (Real.exp (12 * c + 10)) := le_max_left _ _
      exact le_trans this hA₀le
    have hApos : 0 < A := by linarith
    have hLbig : 12 * c + 1 ≤ L := by
      dsimp [L]
      have h1 : Real.log (Real.exp (12 * c + 10)) ≤ Real.log (A + 2) := by
        refine Real.log_le_log ?_ ?_
        · positivity
        · calc
            Real.exp (12 * c + 10) ≤ max 2 (Real.exp (12 * c + 10)) := le_max_right _ _
            _ ≤ A := hA₀le
            _ ≤ A + 2 := by linarith
      rw [Real.log_exp] at h1
      nlinarith
    have hLpos : 0 < L := by nlinarith
    have hL1 : 1 ≤ L := by nlinarith
    have hL2pos : 0 < L ^ 2 := sq_pos_of_pos hLpos
    have hB2 : 2 ≤ B := by dsimp [B]; nlinarith
    have hB0 : 0 ≤ B := by dsimp [B]; nlinarith
    have hB3 : B ≤ 3 * A := by dsimp [B]; nlinarith
    let Z : Set ℂ := {u : ℂ | xiF u = 0 ∧ ‖u‖ ≤ B}
    have hZfin : Z.Finite := by
      simpa [Z] using (xiF_zeroSet_finite (B := B) hB0)
    let Zfin : Finset ℂ := hZfin.toFinset
    let centres : Finset ℝ := Zfin.image (fun u : ℂ => ‖u‖)
    have hcentres_le : (centres.card : ℝ) ≤ (Zfin.card : ℝ) := by
      dsimp [centres]
      exact_mod_cast (Finset.card_image_le : (Zfin.image (fun u : ℂ => ‖u‖)).card ≤ Zfin.card)
    have hcardZ : (Zfin.card : ℝ) ≤
        ∑ᶠ u : ℂ, (((MeromorphicOn.divisor xiF (Metric.closedBall (0 : ℂ) B)) u : ℤ) : ℝ) := by
      simpa [Zfin, Z] using (xiF_zeroCard_le_divisorFinsum (B := B) hB0 hZfin)
    let ℓB : ℝ := Real.log (B + 2) + 2
    have hℓB0 : 0 ≤ ℓB := by
      dsimp [ℓB]
      have h1 : 0 ≤ Real.log (B + 2) := by
        refine Real.log_nonneg ?_
        dsimp [B]
        linarith
      linarith
    have hℓB2 : ℓB ≤ 2 * L := by
      dsimp [ℓB, L]
      have hlogB : Real.log (B + 2) ≤ Real.log (A + 2) + 1 := by
        have hEq : B + 2 = 2 * A + 4 := by dsimp [B]; ring
        rw [hEq]
        exact Commons.NumberTheory.Linnik.grg_log_two_mul_add_four hApos
      have hlogAp2 : 0 ≤ Real.log (A + 2) := by
        refine Real.log_nonneg ?_
        linarith
      nlinarith
    have hmainAux : (centres.card : ℝ) * 2 < A * L ^ 2 := by
      have h1 : (centres.card : ℝ) ≤ c * B * ℓB := by
        calc
          (centres.card : ℝ) ≤ (Zfin.card : ℝ) := hcentres_le
          _ ≤ ∑ᶠ u : ℂ, (((MeromorphicOn.divisor xiF (Metric.closedBall (0 : ℂ) B)) u : ℤ) : ℝ) := hcardZ
          _ ≤ c * B * ℓB := by
            simpa [ℓB] using hc_bound B hB2
      calc
        (centres.card : ℝ) * 2 ≤ c * B * ℓB * 2 := by
          exact mul_le_mul_of_nonneg_right h1 (by norm_num)
        _ ≤ c * (3 * A) * (2 * L) * 2 := by
          gcongr
        _ = 12 * c * A * L := by ring
        _ < A * L ^ 2 := by
          exact Commons.NumberTheory.Linnik.grg_poly_lt hcge0 hApos hLbig
    have hcard' : (centres.card : ℝ) * (2 / L ^ 2) < A := by
      rw [← mul_div_assoc]
      rw [div_lt_iff₀ hL2pos]
      simpa [mul_assoc] using hmainAux
    have hcard'' : (centres.card : ℝ) * (2 / L ^ 2) < 2 * A - A := by
      nlinarith [hcard']
    have hw : 0 < 2 / L ^ 2 := by
      exact div_pos (by norm_num) hL2pos
    have hab : A ≤ 2 * A := by linarith
    rcases Commons.NumberTheory.Linnik.grg_exists_good_point_of_small_measure hab hw centres hcard'' with
      ⟨T, hT1, hT2, hgood⟩
    have hw2 : (2 / L ^ 2) / 2 = (1 : ℝ) / L ^ 2 := by
      have hLne : L ≠ 0 := ne_of_gt hLpos
      field_simp [hLne]
    have hgood' : ∀ z ∈ centres, (1 : ℝ) / L ^ 2 ≤ |T - z| := by
      intro z hz
      rw [← hw2]
      exact hgood z hz
    refine ⟨T, hT1, hT2, ?_⟩
    intro u hu0
    have hdist : (1 : ℝ) / L ^ 2 ≤ |‖u‖ - T| := by
      by_cases huB : ‖u‖ ≤ B
      · have hmem : ‖u‖ ∈ centres := by
          dsimp [centres]
          refine Finset.mem_image.mpr ?_
          refine ⟨u, ?_, rfl⟩
          dsimp [Zfin]
          exact (hZfin.mem_toFinset).2 ⟨by simpa using hu0, huB⟩
        have hd := hgood' (‖u‖) hmem
        simpa [abs_sub_comm] using hd
      · have hBlt : B < ‖u‖ := lt_of_not_ge huB
        have hbig : (2 : ℝ) ≤ ‖u‖ - T := by
          have hBT : (2 : ℝ) ≤ B - T := by
            dsimp [B]
            nlinarith [hT2]
          have h1 : B - T < ‖u‖ - T := sub_lt_sub_right hBlt T
          linarith
        have hd2 : (1 : ℝ) / L ^ 2 ≤ 2 := by
          have hle1 : (1 : ℝ) / L ^ 2 ≤ 1 := Commons.NumberTheory.Linnik.grg_one_div_sq_le_one hL1
          linarith
        have hle : (1 : ℝ) / L ^ 2 ≤ ‖u‖ - T := le_trans hd2 hbig
        have hnn : 0 ≤ ‖u‖ - T := by linarith
        simpa [abs_of_nonneg hnn] using hle
    have hfin : L ^ 2 * |‖u‖ - T| ≥ 1 := by
      have h2 : 1 ≤ |‖u‖ - T| * L ^ 2 := (div_le_iff₀ hL2pos).mp hdist
      have h3 : (1 : ℝ) ≤ L ^ 2 * |‖u‖ - T| := by
        simpa [mul_comm] using h2
      linarith
    dsimp [L] at hfin ⊢
    exact hfin


/-! ### Tail bound for the `xiF` divisor sums (adapted from `partialFraction_tail`) -/

private lemma xiF_partialFraction_tail :
    ∃ c : ℝ, ∀ s : ℂ, ∀ R R' : ℝ, 2 ≤ R → R ≤ R' → ‖s‖ ≤ R / 4 →
      ‖(∑ᶠ u : ℂ, (((MeromorphicOn.divisor xiF (Metric.closedBall 0 R')) u : ℤ) : ℂ) *
          (1 / (s - u) + 1 / u))
        - (∑ᶠ u : ℂ, (((MeromorphicOn.divisor xiF (Metric.closedBall 0 R)) u : ℤ) : ℂ) *
          (1 / (s - u) + 1 / u))‖ ≤
        c * ‖s‖ * (Real.log (R + 2) + 2) / R := by
  classical
  let Λ : ℂ → ℂ := xiF
  have hΛdiff : Differentiable ℂ Λ := by simpa [Λ] using xiF_diff
  have hΛan : ∀ U : Set ℂ, AnalyticOnNhd ℂ Λ U := by
    intro U z hz
    exact hΛdiff.analyticAt z
  have hΛmer : ∀ U : Set ℂ, MeromorphicOn Λ U := fun U => (hΛan U).meromorphicOn
  have hdiv_nonneg : ∀ U u, 0 ≤ (MeromorphicOn.divisor Λ U) u := by
    intro U u
    exact MeromorphicOn.AnalyticOnNhd.divisor_nonneg (hΛan U) u
  rcases xiF_zeroCount with ⟨zc, hzc⟩
  let C : ℝ := max zc 0
  have hC0 : 0 ≤ C := by dsimp [C]; exact le_max_right zc 0
  have hzcC : ∀ (ρ : ℝ), 2 ≤ ρ →
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor Λ (closedBall 0 ρ)) u : ℤ) : ℝ)) ≤
        C * ρ * (Real.log (ρ + 2) + 2) := by
    intro ρ hρ
    have h1 := hzc ρ hρ
    have hT0 : 0 ≤ Real.log (ρ + 2) + 2 := by
      have h1 : 0 ≤ Real.log (ρ + 2) := by exact Real.log_nonneg (by linarith)
      linarith
    have hρ0 : 0 ≤ ρ := by linarith
    have hzcC' : zc * ρ * (Real.log (ρ + 2) + 2) ≤
        C * ρ * (Real.log (ρ + 2) + 2) := by
      have hCge : zc ≤ C := by dsimp [C]; exact le_max_left zc 0
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCge hρ0) hT0
    exact le_trans h1 hzcC'
  refine ⟨128 * C, ?_⟩
  intro s R R' hR hRR' hs
  let w : ℂ → ℂ := fun u => 1 / (s - u) + 1 / u
  let m : ℝ → ℂ → ℤ := fun ρ u => MeromorphicOn.divisor Λ (closedBall 0 ρ) u
  let F : ℝ → ℂ := fun ρ => ∑ᶠ u : ℂ, (((m ρ u : ℤ) : ℂ) * w u)
  -- finite support finsets
  have hfin (ρ : ℝ) : (m ρ).support.Finite := by
    dsimp [m]
    exact (MeromorphicOn.divisor Λ (closedBall 0 ρ)).finiteSupport (isCompact_closedBall (0 : ℂ) ρ)
  let S : Finset ℂ := (hfin R').toFinset
  have hS_mem : ∀ u : ℂ, u ∈ S ↔ m R' u ≠ 0 := by
    intro u
    dsimp [S]
    rw [Set.Finite.mem_toFinset]
    rfl
  have hRpos : 0 < R := by linarith
  have hR'_ge_R : R ≤ R' := hRR'
  -- rewrite F into finite sums over S
  have hF' : F R' = ∑ u ∈ S, (((m R' u : ℤ) : ℂ) * w u) := by
    dsimp [F]
    refine finsum_eq_sum_of_support_subset _ ?_
    intro u hu
    rw [Function.mem_support] at hu
    have hm : m R' u ≠ 0 := by
      intro hz
      apply hu
      simp [hz]
    exact (hS_mem u).mpr hm
  have hF : F R = ∑ u ∈ S, (((m R u : ℤ) : ℂ) * w u) := by
    dsimp [F]
    refine finsum_eq_sum_of_support_subset _ ?_
    intro u hu
    rw [Function.mem_support] at hu
    have hm : m R u ≠ 0 := by
      intro hz
      apply hu
      simp [hz]
    have huB : u ∈ closedBall 0 R := (MeromorphicOn.divisor Λ (closedBall 0 R)).supportWithinDomain hm
    have hle : ‖u‖ ≤ R := by simpa [Metric.mem_closedBall, dist_eq_norm] using huB
    have hEq : m R u = m R' u := by
      dsimp [m]
      exact Commons.NumberTheory.Linnik.divisor_closedBall_eq_of_le hΛmer (u := u) (ρ₁ := R) (ρ₂ := R') hle (le_trans hle hRR')
    have hm' : m R' u ≠ 0 := by rwa [← hEq]
    exact (hS_mem u).mpr hm'
  -- difference
  have hD : F R' - F R = ∑ u ∈ S, ((((m R' u - m R u : ℤ) : ℂ)) * w u) := by
    rw [hF', hF]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro u hu
    simp [Int.cast_sub, sub_mul]
  -- collapse to the annulus R < |u|
  let T : Finset ℂ := S.filter (fun u => R < ‖u‖)
  have hDcoll : F R' - F R = ∑ u ∈ T, (((m R' u : ℤ) : ℂ) * w u) := by
    have hstep : ∀ u ∈ S, ((((m R' u - m R u : ℤ) : ℂ)) * w u) =
        if R < ‖u‖ then (((m R' u : ℤ) : ℂ) * w u) else 0 := by
      intro u huS
      by_cases hbig : R < ‖u‖
      · have hmR0 : m R u = 0 := by
          dsimp [m]
          exact Commons.NumberTheory.Linnik.divisor_closedBall_eq_zero_of_lt_norm (f := Λ) hbig
        simp [hbig, hmR0]
      · have hle : ‖u‖ ≤ R := le_of_not_gt hbig
        have hEq : m R u = m R' u := by
          dsimp [m]
          exact Commons.NumberTheory.Linnik.divisor_closedBall_eq_of_le hΛmer (u := u) (ρ₁ := R) (ρ₂ := R') hle (le_trans hle hRR')
        simp [hbig, hEq]
    calc
      F R' - F R = ∑ u ∈ S, ((((m R' u - m R u : ℤ) : ℂ)) * w u) := hD
      _ = ∑ u ∈ S, (if R < ‖u‖ then (((m R' u : ℤ) : ℂ) * w u) else 0) := by
          refine Finset.sum_congr rfl ?_
          intro u hu
          exact hstep u hu
      _ = ∑ u ∈ S.filter (fun u => R < ‖u‖), (((m R' u : ℤ) : ℂ) * w u) := by
          rw [Finset.sum_filter]
      _ = ∑ u ∈ T, (((m R' u : ℤ) : ℂ) * w u) := rfl
  -- norm bound
  have hnorm : ‖F R' - F R‖ ≤ ∑ u ∈ T, ‖(((m R' u : ℤ) : ℂ) * w u)‖ := by
    rw [hDcoll]
    exact norm_sum_le T (fun u => (((m R' u : ℤ) : ℂ) * w u))
  have hterm : ∀ u ∈ T, ‖(((m R' u : ℤ) : ℂ) * w u)‖ = (((m R' u : ℤ) : ℝ) * ‖w u‖) := by
    intro u huT
    have hm0 : 0 ≤ m R' u := hdiv_nonneg (closedBall 0 R') u
    rw [norm_mul, Complex.norm_int_of_nonneg hm0]
  have hnorm2 : ‖F R' - F R‖ ≤ ∑ u ∈ T, (((m R' u : ℤ) : ℝ) * ‖w u‖) := by
    calc
      ‖F R' - F R‖ ≤ ∑ u ∈ T, ‖(((m R' u : ℤ) : ℂ) * w u)‖ := hnorm
      _ = ∑ u ∈ T, (((m R' u : ℤ) : ℝ) * ‖w u‖) := by
          refine Finset.sum_congr rfl ?_
          intro u hu
          exact hterm u hu
  have hwu : ∀ u ∈ T, ‖w u‖ ≤ (4 / 3) * ‖s‖ / ‖u‖ ^ 2 := by
    intro u huT
    have hbig : R < ‖u‖ := (Finset.mem_filter.mp huT).2
    exact Commons.NumberTheory.Linnik.partialFrac_term_norm_le (s := s) (u := u) (R := R) hR hs (le_of_lt hbig)
  have hbnd : ‖F R' - F R‖ ≤ ∑ u ∈ T, (((m R' u : ℤ) : ℝ) * ((4 / 3) * ‖s‖ / ‖u‖ ^ 2)) := by
    calc
      ‖F R' - F R‖ ≤ ∑ u ∈ T, (((m R' u : ℤ) : ℝ) * ‖w u‖) := hnorm2
      _ ≤ ∑ u ∈ T, (((m R' u : ℤ) : ℝ) * ((4 / 3) * ‖s‖ / ‖u‖ ^ 2)) := by
          refine Finset.sum_le_sum ?_
          intro u huT
          have hm0 : 0 ≤ ((m R' u : ℤ) : ℝ) := by exact_mod_cast (hdiv_nonneg (closedBall 0 R') u)
          exact mul_le_mul_of_nonneg_left (hwu u huT) hm0
  let M : ℝ := (4 / 3) * ‖s‖
  have hM0 : 0 ≤ M := by dsimp [M]; positivity
  have hs0 : 0 ≤ ‖s‖ := norm_nonneg s
  let jl : ℂ → ℕ := fun u => Commons.NumberTheory.Linnik.dyadIdx R ‖u‖ (Commons.NumberTheory.Linnik.exists_dyadic_ge R ‖u‖ hRpos)
  have hjl_spec_le : ∀ u : ℂ, ‖u‖ ≤ (2 : ℝ) ^ (jl u + 1) * R := by
    intro u
    dsimp [jl]
    exact Commons.NumberTheory.Linnik.dyadIdx_spec_le R ‖u‖ (Commons.NumberTheory.Linnik.exists_dyadic_ge R ‖u‖ hRpos)
  have hjl_lower : ∀ u : ℂ, R < ‖u‖ → (2 : ℝ) ^ jl u * R < ‖u‖ := by
    intro u hu
    dsimp [jl]
    exact Commons.NumberTheory.Linnik.dyadIdx_lower (Commons.NumberTheory.Linnik.exists_dyadic_ge R ‖u‖ hRpos) hu
  rcases Commons.NumberTheory.Linnik.exists_dyadic_ge R R' hRpos with ⟨K, hK⟩
  have hjl_le_K : ∀ u ∈ T, jl u ≤ K := by
    intro u huT
    have hmem := Finset.mem_filter.mp huT
    have hbig : R < ‖u‖ := hmem.2
    have huS : u ∈ S := hmem.1
    have hm : m R' u ≠ 0 := (hS_mem u).mp huS
    have huB : u ∈ closedBall 0 R' := (MeromorphicOn.divisor Λ (closedBall 0 R')).supportWithinDomain hm
    have huR' : ‖u‖ ≤ R' := by simpa [Metric.mem_closedBall, dist_eq_norm] using huB
    have hK' : ‖u‖ ≤ (2 : ℝ) ^ (K + 1) * R := le_trans huR' hK
    dsimp [jl]
    exact Commons.NumberTheory.Linnik.dyadIdx_le_of R ‖u‖ (Commons.NumberTheory.Linnik.exists_dyadic_ge R ‖u‖ hRpos) hK'
  let Tj : ℕ → Finset ℂ := fun j => S.filter (fun u => (2 : ℝ) ^ j * R < ‖u‖ ∧ ‖u‖ ≤ (2 : ℝ) ^ (j + 1) * R)
  let b : ℕ → ℝ := fun j => ∑ u ∈ Tj j, ((m R' u : ℤ) : ℝ)
  let c : ℂ → ℝ := fun u => ((m R' u : ℤ) : ℝ)
  have hc0 : ∀ u, 0 ≤ c u := by
    intro u
    dsimp [c]
    exact_mod_cast (hdiv_nonneg (closedBall 0 R') u)
  have hc_eq : ∀ u, c u = ((m R' u : ℤ) : ℝ) := by intro u; rfl
  -- (a) pointwise weight bound at the level of u
  have hwM : ∀ u ∈ T, M / ‖u‖ ^ 2 ≤ M / (((4 : ℝ) ^ jl u) * R ^ 2) := by
    intro u huT
    have hbig : R < ‖u‖ := (Finset.mem_filter.mp huT).2
    have hsq := Commons.NumberTheory.Linnik.dyadIdx_sq_le (R := R) (ρ := ‖u‖) hRpos (Commons.NumberTheory.Linnik.exists_dyadic_ge R ‖u‖ hRpos) hbig
    have hy0 : 0 < (4 : ℝ) ^ jl u * R ^ 2 := by positivity
    exact div_le_div₀ hM0 le_rfl hy0 hsq
  have hw1 : ∀ u ∈ T, c u * (M / ‖u‖ ^ 2) ≤ c u * (M / (((4 : ℝ) ^ jl u) * R ^ 2)) := by
    intro u huT
    exact mul_le_mul_of_nonneg_left (hwM u huT) (hc0 u)
  have hc_def (u : ℂ) : c u = ((m R' u : ℤ) : ℝ) := rfl
  have hbndM : ‖F R' - F R‖ ≤ ∑ u ∈ T, (c u * (M / ‖u‖ ^ 2)) := by
    simpa [c, M] using hbnd
  -- (b) split into dyadic fibres
  let Afib : ℕ → ℝ := fun j => ∑ u ∈ T.filter (fun u => jl u = j), (c u * (M / (((4 : ℝ) ^ j) * R ^ 2)))
  have hfib_le_Tj : ∀ j : ℕ, T.filter (fun u => jl u = j) ⊆ Tj j := by
    intro j
    intro u hu
    have hmem := Finset.mem_filter.mp hu
    have huT : u ∈ T := hmem.1
    have hEq : jl u = j := hmem.2
    have hS' : u ∈ S := (Finset.mem_filter.mp huT).1
    have hbig : R < ‖u‖ := (Finset.mem_filter.mp huT).2
    have hlow' : (2 : ℝ) ^ jl u * R < ‖u‖ := hjl_lower u hbig
    have hlow : (2 : ℝ) ^ j * R < ‖u‖ := by simpa [hEq] using hlow'
    have hup : ‖u‖ ≤ (2 : ℝ) ^ (j + 1) * R := by
      simpa [hEq] using hjl_spec_le u
    exact Finset.mem_filter.mpr ⟨hS', ⟨hlow, hup⟩⟩
  have hfib_b : ∀ j : ℕ, (∑ u ∈ T.filter (fun u => jl u = j), c u) ≤ b j := by
    intro j
    dsimp [b]
    exact Finset.sum_le_sum_of_subset_of_nonneg (hfib_le_Tj j)
      (fun u huTj hnot => hc0 u)
  have hpart : (∑ u ∈ T, (c u * (M / (((4 : ℝ) ^ jl u) * R ^ 2)))) =
      ∑ j ∈ Finset.range (K + 1), Afib j := by
    have hpf := Commons.NumberTheory.Linnik.Finset.sum_eq_sum_image_filter (s := T) (g := jl)
      (f := fun u => c u * (M / (((4 : ℝ) ^ jl u) * R ^ 2)))
    have himg : T.image jl ⊆ Finset.range (K + 1) := by
      intro j hj
      rcases Finset.mem_image.mp hj with ⟨u, huT, hEq⟩
      have hle : j ≤ K := by simpa [hEq] using (hjl_le_K u huT)
      exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hle)
    calc
      (∑ u ∈ T, (c u * (M / (((4 : ℝ) ^ jl u) * R ^ 2))))
          = ∑ j ∈ T.image jl, ∑ u ∈ T.filter (fun u => jl u = j),
              (c u * (M / (((4 : ℝ) ^ j) * R ^ 2))) := by
              rw [hpf]
              refine Finset.sum_congr rfl ?_
              intro j hj
              refine Finset.sum_congr rfl ?_
              intro u hu
              have hEq : jl u = j := (Finset.mem_filter.mp hu).2
              simp [hEq]
      _ = ∑ j ∈ T.image jl, Afib j := rfl
      _ = ∑ j ∈ Finset.range (K + 1), Afib j := by
          refine Finset.sum_subset himg ?_
          intro j hj hnot
          -- j ∉ image: the fibre filter is empty
          have hfib_empty : (T.filter (fun u => jl u = j)) = ∅ := by
            ext u
            constructor
            · intro hu
              have hmem2 := Finset.mem_filter.mp hu
              exact False.elim (hnot (Finset.mem_image.mpr ⟨u, hmem2.1, hmem2.2⟩))
            · intro hu
              simp at hu
          simp [Afib, hfib_empty]
  have hweight : ∀ j : ℕ, 0 ≤ M / (((4 : ℝ) ^ j) * R ^ 2) := by
    intro j
    exact div_nonneg hM0 (by positivity)
  have hfib_nonneg : ∀ j : ℕ, 0 ≤ ∑ u ∈ T.filter (fun u => jl u = j), c u := by
    intro j
    exact Finset.sum_nonneg (fun u hu => hc0 u)
  -- (c) the tail bound via dyadicAnnulusTail
  let L : ℝ := 2
  have hL0 : 0 ≤ L := by norm_num
  -- count bound for each dyadic annulus
  have hb_le : ∀ j : ℕ, b j ≤ C * (2 : ℝ) ^ (j + 1) * R *
      (Real.log ((2 : ℝ) ^ (j + 1) * R + 2) + L) := by
    intro j
    let ρ : ℝ := (2 : ℝ) ^ (j + 1) * R
    have hρ2 : 2 ≤ ρ := by
      dsimp [ρ]
      have h1 : (2 : ℝ) ≤ (2 : ℝ) ^ (j + 1) := by
        have := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ (2 : ℝ)) (by omega : (1 : ℕ) ≤ j + 1)
        simpa using this
      nlinarith
    have hρ0 : 0 ≤ ρ := by linarith
    let Sρ : Finset ℂ := (hfin ρ).toFinset
    have hSρ_mem : ∀ u : ℂ, u ∈ Sρ ↔ m ρ u ≠ 0 := by
      intro u
      dsimp [Sρ]
      rw [Set.Finite.mem_toFinset]
      rfl
    have hcount : (∑ u ∈ Sρ, ((m ρ u : ℤ) : ℝ)) ≤ C * ρ * (Real.log (ρ + 2) + 2) := by
      have hc1 := hzcC ρ hρ2
      have hc2 : (∑ᶠ u : ℂ, (((m ρ u : ℤ) : ℝ))) = ∑ u ∈ Sρ, ((m ρ u : ℤ) : ℝ) := by
        refine finsum_eq_sum_of_support_subset _ ?_
        intro u hu
        rw [Function.mem_support] at hu
        have hm : m ρ u ≠ 0 := by
          intro hz
          apply hu
          simp [hz]
        exact (hSρ_mem u).mpr hm
      rwa [hc2] at hc1
    -- b j ≤ the count over Sρ
    have hb_le_count : b j ≤ ∑ u ∈ Sρ, ((m ρ u : ℤ) : ℝ) := by
      have hEq_val : ∀ u ∈ Tj j, m ρ u = m R' u := by
        intro u huTj
        have hmem := Finset.mem_filter.mp huTj
        have huS : u ∈ S := hmem.1
        have hbounds := hmem.2
        have huρ : ‖u‖ ≤ ρ := by
          dsimp [ρ]
          exact hbounds.2
        have huR' : ‖u‖ ≤ R' := by
          have hm' : m R' u ≠ 0 := (hS_mem u).mp huS
          have huB : u ∈ closedBall 0 R' :=
            (MeromorphicOn.divisor Λ (closedBall 0 R')).supportWithinDomain hm'
          simpa [Metric.mem_closedBall, dist_eq_norm] using huB
        dsimp [m]
        exact Commons.NumberTheory.Linnik.divisor_closedBall_eq_of_le hΛmer (u := u) (ρ₁ := ρ) (ρ₂ := R') huρ huR'
      have hsub : Tj j ⊆ Sρ := by
        intro u huTj
        have hmem := Finset.mem_filter.mp huTj
        have huρ : ‖u‖ ≤ ρ := by
          dsimp [ρ]
          exact hmem.2.2
        have hm' : m R' u ≠ 0 := (hS_mem u).mp hmem.1
        have hmρ : m ρ u ≠ 0 := by
          rw [hEq_val u huTj]
          exact hm'
        exact (hSρ_mem u).mpr hmρ
      calc
        b j = ∑ u ∈ Tj j, ((m R' u : ℤ) : ℝ) := by rfl
        _ = ∑ u ∈ Tj j, ((m ρ u : ℤ) : ℝ) := by
            refine Finset.sum_congr rfl ?_
            intro u huTj
            rw [hEq_val u huTj]
        _ ≤ ∑ u ∈ Sρ, ((m ρ u : ℤ) : ℝ) := by
            exact Finset.sum_le_sum_of_subset_of_nonneg hsub
              (fun u huSρ hnot => by
                exact_mod_cast (hdiv_nonneg (closedBall 0 ρ) u))
    calc
      b j ≤ ∑ u ∈ Sρ, ((m ρ u : ℤ) : ℝ) := hb_le_count
      _ ≤ C * ρ * (Real.log (ρ + 2) + 2) := hcount
      _ = C * (2 : ℝ) ^ (j + 1) * R * (Real.log ((2 : ℝ) ^ (j + 1) * R + 2) + L) := by
          dsimp [ρ, L]
          ring
  have hb0 : ∀ j : ℕ, 0 ≤ b j := by
    intro j
    dsimp [b]
    exact Finset.sum_nonneg (fun u hu => hc0 u)
  let G : ℝ := (2 * C * M / R) * (1 + Real.log (R + 2) + L)
  have hG0 : 0 ≤ G := by
    dsimp [G]
    have h1 : 0 ≤ 2 * C * M / R := by positivity
    have h2 : 0 ≤ 1 + Real.log (R + 2) + L := by
      have h : 0 ≤ Real.log (R + 2) := Real.log_nonneg (by linarith)
      linarith
    positivity
  have hlog2le1 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlogR0 : 0 ≤ Real.log (R + 2) := Real.log_nonneg (by linarith)
  have hsum_dyadic : Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) * ((1 / 2 : ℝ) ^ k)) := by
    have h := hasSum_choose_mul_geometric_of_norm_lt_one (k := 1) (r := (1 / 2 : ℝ))
      (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)
    simpa [Nat.choose_one_right] using h.summable
  have hsummable : Summable (fun j : ℕ => b j * (M / ((4 : ℝ) ^ j * R ^ 2))) := by
    refine Summable.of_nonneg_of_le (g := fun j : ℕ => b j * (M / ((4 : ℝ) ^ j * R ^ 2)))
      (f := fun j : ℕ => G * (((j + 1 : ℕ) : ℝ) * ((1 / 2 : ℝ) ^ j))) ?_ ?_ ?_
    · intro j
      exact mul_nonneg (hb0 j) (div_nonneg hM0 (by positivity : 0 ≤ (4 : ℝ) ^ j * R ^ 2))
    · intro j
      have hX : Real.log ((2 : ℝ) ^ (j + 1) * R + 2) + L ≤
          ((j + 1 : ℕ) : ℝ) * (1 + Real.log (R + 2) + L) := by
        have hlog := Commons.NumberTheory.Linnik.log_two_pow_mul_add_two_le hR j
        have hA : ((j + 1 : ℕ) : ℝ) * Real.log 2 + Real.log (R + 2) + L ≤
            ((j + 1 : ℕ) : ℝ) + Real.log (R + 2) + L := by
          have hm : ((j + 1 : ℕ) : ℝ) * Real.log 2 ≤ ((j + 1 : ℕ) : ℝ) := by
            have hjp : 0 ≤ ((j + 1 : ℕ) : ℝ) := by positivity
            calc
              ((j + 1 : ℕ) : ℝ) * Real.log 2 ≤ ((j + 1 : ℕ) : ℝ) * 1 := by
                exact mul_le_mul_of_nonneg_left hlog2le1 hjp
              _ = ((j + 1 : ℕ) : ℝ) := by ring
          linarith
        have hC : ((j + 1 : ℕ) : ℝ) + Real.log (R + 2) + L ≤
            ((j + 1 : ℕ) : ℝ) * (1 + Real.log (R + 2) + L) := by
          have hjp : 1 ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast (Nat.succ_pos j)
          nlinarith
        exact le_trans (le_trans (add_le_add_left hlog L) hA) hC
      have hb'' : b j ≤ C * (2 : ℝ) ^ (j + 1) * R *
          (((j + 1 : ℕ) : ℝ) * (1 + Real.log (R + 2) + L)) := by
        exact le_trans (hb_le j)
          (mul_le_mul_of_nonneg_left hX (by positivity : 0 ≤ C * (2 : ℝ) ^ (j + 1) * R))
      calc
        b j * (M / ((4 : ℝ) ^ j * R ^ 2))
            ≤ (C * (2 : ℝ) ^ (j + 1) * R * (((j + 1 : ℕ) : ℝ) * (1 + Real.log (R + 2) + L))) *
                (M / ((4 : ℝ) ^ j * R ^ 2)) := by
                exact mul_le_mul_of_nonneg_right hb''
                  (div_nonneg hM0 (by positivity : 0 ≤ (4 : ℝ) ^ j * R ^ 2))
        _ = G * (((j + 1 : ℕ) : ℝ) * ((1 / 2 : ℝ) ^ j)) := by
            have hw := Commons.NumberTheory.Linnik.dyadic_weight_eq (C := C) (M := M) (R := R)
              (B := 1 + Real.log (R + 2) + L) (ne_of_gt hRpos) j
            dsimp [G]
            rw [← hw]
    · exact Summable.mul_left G hsum_dyadic

  have hpartial : (∑ j ∈ Finset.range (K + 1), b j * (M / ((4 : ℝ) ^ j * R ^ 2))) ≤
      ∑' j : ℕ, b j * (M / ((4 : ℝ) ^ j * R ^ 2)) := by
    exact Summable.sum_le_tsum (Finset.range (K + 1))
      (fun i hi => by
        exact mul_nonneg (hb0 i) (by positivity : 0 ≤ M / ((4 : ℝ) ^ i * R ^ 2)))
      hsummable
  have htail := Commons.Analysis.Asymptotics.dyadicAnnulusTail (C := C) (R := R) (M := M) (L := L)
    hC0 hR hM0 hL0 b hb0 hb_le
  -- assemble the finite dyadic bound
  have hdybnd : (∑ u ∈ T, (c u * (M / ‖u‖ ^ 2))) ≤
      64 * C * M * (Real.log (R + 2) + L + 1) / R := by
    calc
      (∑ u ∈ T, (c u * (M / ‖u‖ ^ 2))) ≤ ∑ u ∈ T, (c u * (M / (((4 : ℝ) ^ jl u) * R ^ 2))) := by
          refine Finset.sum_le_sum ?_
          intro u huT
          exact hw1 u huT
      _ = ∑ j ∈ Finset.range (K + 1), Afib j := hpart
      _ = ∑ j ∈ Finset.range (K + 1), (M / (((4 : ℝ) ^ j) * R ^ 2)) *
          (∑ u ∈ T.filter (fun u => jl u = j), c u) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          dsimp [Afib]
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro u hu
          ring
      _ ≤ ∑ j ∈ Finset.range (K + 1), (M / (((4 : ℝ) ^ j) * R ^ 2)) * b j := by
          refine Finset.sum_le_sum ?_
          intro j hj
          exact mul_le_mul_of_nonneg_left (hfib_b j) (hweight j)
      _ = ∑ j ∈ Finset.range (K + 1), b j * (M / (((4 : ℝ) ^ j) * R ^ 2)) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          ring
      _ ≤ ∑' j : ℕ, b j * (M / ((4 : ℝ) ^ j * R ^ 2)) := hpartial
      _ ≤ 64 * C * M * (Real.log (R + 2) + L + 1) / R := htail
  -- final real arithmetic
  let Tlog : ℝ := Real.log (R + 2) + 2
  have hT2 : 2 ≤ Tlog := by
    dsimp [Tlog]
    have h1 : 0 ≤ Real.log (R + 2) := hlogR0
    linarith
  have hT0 : 0 ≤ Tlog := by linarith
  have hfrac : (64 : ℝ) * (4 / 3) * (Tlog + 1) ≤ 128 * Tlog := by
    nlinarith
  have hconst : (64 : ℝ) * C * M * (Tlog + 1) ≤ (128 * C) * ‖s‖ * Tlog := by
    have hfrac' : (64 : ℝ) * (4 / 3 : ℝ) * (Tlog + 1) ≤ 128 * Tlog := by
      nlinarith
    dsimp [M]
    have hstep : 64 * (4 / 3 : ℝ) * ‖s‖ * (Tlog + 1) ≤ 128 * ‖s‖ * Tlog := by
      have hm := mul_le_mul_of_nonneg_right hfrac' hs0
      nlinarith
    have hstepC : C * (64 * (4 / 3 : ℝ) * ‖s‖ * (Tlog + 1)) ≤ C * (128 * ‖s‖ * Tlog) :=
      mul_le_mul_of_nonneg_left hstep hC0
    nlinarith
  have hgoal : ‖F R' - F R‖ ≤ (128 * C) * ‖s‖ * Tlog / R := by
    calc
      ‖F R' - F R‖ ≤ ∑ u ∈ T, (c u * (M / ‖u‖ ^ 2)) := hbndM
      _ ≤ 64 * C * M * (Real.log (R + 2) + L + 1) / R := hdybnd
      _ = 64 * C * M * (Tlog + 1) / R := by
          dsimp [Tlog, L]
      _ ≤ (128 * C) * ‖s‖ * Tlog / R := by
          have hdiv := div_le_div_of_nonneg_right hconst (le_of_lt hRpos)
          simpa [M] using hdiv
  simpa [F, w, m, Tlog] using hgoal

/-! ### The full family of divisor sums converges (adapted from `partialFraction_conv`) -/

private lemma xiF_partialFraction_conv (s : ℂ) :
    ∃ L : ℂ, Tendsto (fun R : ℝ =>
        (∑ᶠ u : ℂ, (((MeromorphicOn.divisor xiF (Metric.closedBall 0 R)) u : ℤ) : ℂ) *
          (1 / (s - u) + 1 / u))) atTop (nhds L) := by
  classical
  let F : ℝ → ℂ := fun R =>
        ∑ᶠ u : ℂ, (((MeromorphicOn.divisor xiF (Metric.closedBall 0 R)) u : ℤ) : ℂ) *
          (1 / (s - u) + 1 / u)
  let T : ℝ → ℝ := fun R => Real.log (R + 2) + 2
  rcases xiF_partialFraction_tail with ⟨c, hc⟩
  have hb : ∀ ⦃R R' : ℝ⦄, 2 ≤ R → R ≤ R' → ‖s‖ ≤ R / 4 →
      ‖F R' - F R‖ ≤ c * ‖s‖ * T R / R := by
    intro R R' hR hRR' hs
    simpa [F, T] using hc s R R' hR hRR' hs
  have hdec : Tendsto (fun R : ℝ => c * ‖s‖ * T R / R) atTop (𝓝 0) := by
    have hT : Tendsto (fun R : ℝ => (Real.log (R + 2) + 2) / R) atTop (𝓝 0) := by
      simpa using (Commons.NumberTheory.Linnik.log_add_two_add_const_div_self_tendsto_zero (D := 2))
    have hconst : Tendsto (fun _ : ℝ => c * ‖s‖) atTop (𝓝 (c * ‖s‖)) := tendsto_const_nhds
    have hmain : Tendsto (fun R : ℝ => (c * ‖s‖) * ((Real.log (R + 2) + 2) / R)) atTop (𝓝 0) := by
      simpa using hconst.mul hT
    have heq : (fun R : ℝ => (c * ‖s‖) * ((Real.log (R + 2) + 2) / R)) =ᶠ[atTop]
        fun R : ℝ => c * ‖s‖ * (Real.log (R + 2) + 2) / R := by
      filter_upwards with R
      ring
    simpa using hmain.congr' heq
  have hcauchy : ∀ ε > 0, ∃ R₀ : ℝ, ∀ R R' : ℝ, R₀ ≤ R → R₀ ≤ R' → ‖F R - F R'‖ < ε := by
    intro ε hε
    have hsmall : ∀ᶠ R : ℝ in atTop, c * ‖s‖ * T R / R < ε := by
      simpa [T] using hdec.eventually (Iio_mem_nhds hε)
    rcases (Filter.eventually_atTop.mp hsmall) with ⟨R₁, hR₁⟩
    let base : ℝ := max 2 (max (4 * ‖s‖) R₁)
    refine ⟨base, ?_⟩
    intro R R' hR₀R hR₀R'
    have h2R : 2 ≤ R := le_trans (le_max_left 2 (max (4 * ‖s‖) R₁)) hR₀R
    have h2R' : 2 ≤ R' := le_trans (le_max_left 2 (max (4 * ‖s‖) R₁)) hR₀R'
    have h4sR : (4 : ℝ) * ‖s‖ ≤ R := by
      exact le_trans (le_trans (le_max_left (4 * ‖s‖) R₁)
        (le_max_right 2 (max (4 * ‖s‖) R₁))) hR₀R
    have h4sR' : (4 : ℝ) * ‖s‖ ≤ R' := by
      exact le_trans (le_trans (le_max_left (4 * ‖s‖) R₁)
        (le_max_right 2 (max (4 * ‖s‖) R₁))) hR₀R'
    have hsR : ‖s‖ ≤ R / 4 := by nlinarith
    have hsR' : ‖s‖ ≤ R' / 4 := by nlinarith
    have hR1R : R₁ ≤ R := by
      exact le_trans (le_trans (le_max_right (4 * ‖s‖) R₁)
        (le_max_right 2 (max (4 * ‖s‖) R₁))) hR₀R
    have hR1R' : R₁ ≤ R' := by
      exact le_trans (le_trans (le_max_right (4 * ‖s‖) R₁)
        (le_max_right 2 (max (4 * ‖s‖) R₁))) hR₀R'
    have gRlt : c * ‖s‖ * T R / R < ε := by
      have h := hR₁ R hR1R
      simpa [T] using h
    have gR'lt : c * ‖s‖ * T R' / R' < ε := by
      have h := hR₁ R' hR1R'
      simpa [T] using h
    by_cases hle : R ≤ R'
    · have hb' := hb h2R hle hsR
      have hlelt : ‖F R - F R'‖ < ε := by
        rw [norm_sub_rev]
        exact lt_of_le_of_lt hb' gRlt
      simpa [dist_eq_norm] using hlelt
    · have hle' : R' ≤ R := le_of_not_ge hle
      have hb' := hb h2R' hle' hsR'
      have hlelt : ‖F R - F R'‖ < ε := lt_of_le_of_lt hb' gR'lt
      simpa [dist_eq_norm] using hlelt
  have hFcauchy : Cauchy (Filter.map F atTop) := by
    rw [cauchy_map_iff]
    constructor
    · exact Filter.atTop_neBot
    · rw [Metric.uniformity_basis_dist.tendsto_right_iff]
      intro ε hε
      rcases hcauchy ε hε with ⟨R₀, hR₀⟩
      rw [Filter.eventually_prod_iff]
      refine ⟨(fun R : ℝ => R₀ ≤ R), ?_, (fun R : ℝ => R₀ ≤ R), ?_, ?_⟩
      · exact (Filter.eventually_atTop.mpr ⟨R₀, fun b hb => hb⟩)
      · exact (Filter.eventually_atTop.mpr ⟨R₀, fun b hb => hb⟩)
      · intro R hR R' hR'
        simpa [dist_eq_norm] using hR₀ R R' hR hR'
  rcases (cauchy_map_iff_exists_tendsto (l := atTop) (f := F)).mp hFcauchy with ⟨L, hL⟩
  refine ⟨L, ?_⟩
  simpa [F] using hL

open Commons.NumberTheory.Linnik

namespace XiPF

def xiF (s : ℂ) : ℂ := (1 / 2 : ℂ) + (1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta₀ s

lemma xiF_diff : Differentiable ℂ xiF := by
  unfold xiF
  have hΛ : Differentiable ℂ completedRiemannZeta₀ := differentiable_completedZeta₀
  have hhead : Differentiable ℂ (fun s : ℂ => (1 / 2 : ℂ) * s * (s - 1)) := by fun_prop
  exact ((differentiable_const (1 / 2 : ℂ)).add (hhead.mul hΛ))

lemma xiF_zero_ne : xiF 0 ≠ 0 := by
  unfold xiF
  norm_num

lemma xiF_an (U : Set ℂ) : AnalyticOnNhd ℂ xiF U := by
  intro z hz
  exact xiF_diff.analyticAt z

def xiL (A : ℝ) : ℝ := Real.log (A + 2) + 2

lemma xiL_ge_two {A : ℝ} (hA : 0 ≤ A) : 2 ≤ xiL A := by
  have h1 : 0 ≤ Real.log (A + 2) := by
    refine Real.log_nonneg ?_
    linarith
  dsimp [xiL]
  linarith

lemma xiL_pos {A : ℝ} (hA : 0 ≤ A) : 0 < xiL A := by
  linarith [xiL_ge_two hA]

lemma xiL_mono {A B : ℝ} (hA : 0 ≤ A) (h : A ≤ B) : xiL A ≤ xiL B := by
  have hp1 : 0 < A + 2 := by linarith
  have hp2 : 0 < B + 2 := by linarith
  have hle : A + 2 ≤ B + 2 := by linarith
  have hlog : Real.log (A + 2) ≤ Real.log (B + 2) := Real.log_le_log hp1 hle
  dsimp [xiL]
  linarith

lemma xiL_log_le {A : ℝ} (hA : 0 ≤ A) : Real.log (xiL A) ≤ xiL A := by
  have h1 : 1 ≤ xiL A := by linarith [xiL_ge_two hA]
  exact Real.log_le_self (by linarith)

/-- For 1 ≤ A, xiL(2A) ≤ 2·xiL(A). -/
lemma xiL_two_mul_le {A : ℝ} (hA : 1 ≤ A) : xiL (2 * A) ≤ 2 * xiL A := by
  have hA2 : 0 ≤ A := by linarith
  have h₁ : 0 < A + 1 := by linarith
  have h₂ : 0 < 2 := by norm_num
  have h₁₂ : (A + 1 : ℝ) ≠ 0 := by linarith
  have hlog : Real.log (2 * A + 2) ≤ Real.log (A + 2) + Real.log 2 := by
    calc
      Real.log (2 * A + 2) = Real.log ((A + 1) * 2) := by congr 1; ring
      _ = Real.log (A + 1) + Real.log 2 := by rw [Real.log_mul h₁₂ (by norm_num : (2 : ℝ) ≠ 0)]
      _ ≤ Real.log (A + 2) + Real.log 2 := by
        have hlogle : Real.log (A + 1) ≤ Real.log (A + 2) := Real.log_le_log h₁ (by linarith)
        linarith
  have hlog2 : Real.log 2 ≤ 1 := by
    have hlt := Real.log_two_lt_d9
    norm_num at hlt
    linarith
  have h12 : 1 ≤ Real.log (A + 2) := by
    have he : Real.exp 1 ≤ A + 2 := by
      have h3 : Real.exp 1 ≤ 3 := le_of_lt Real.exp_one_lt_three
      linarith
    have h := Real.log_le_log (Real.exp_pos 1) he
    rwa [Real.log_exp] at h
  dsimp [xiL]
  have h12' : 1 ≤ Real.log (A + 2) := h12
  nlinarith

/-- xiL(A)^2 / A → 0 -/
lemma xiL_sq_div_self_tendsto_zero :
    Tendsto (fun A : ℝ => (xiL A) ^ 2 / A) atTop (𝓝 0) := by
  have h : Tendsto (fun A : ℝ => (Real.log (A + 2) + 2) ^ 2 / A)
      atTop (𝓝 0) := by
    simpa using (ell_pow_div_self_tendsto_zero (N := 1) 2)
  simpa [xiL] using h

lemma xiF_zeroCount : ∃ c : ℝ, ∀ R : ℝ, 2 ≤ R →
    (∑ᶠ u : ℂ, (((MeromorphicOn.divisor xiF (Metric.closedBall 0 R)) u : ℤ) : ℝ)) ≤
      c * R * xiL R := by
  rcases xiE_zeroCount with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  intro R hR
  change (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (fun z : ℂ =>
      (1 / 2 : ℂ) + (1 / 2 : ℂ) * z * (z - 1) * completedRiemannZeta₀ z)
      (Metric.closedBall 0 R)) u : ℤ) : ℝ)) ≤ c * R * (Real.log (R + 2) + 2)
  exact hc R hR

lemma xiF_growth : ∃ c : ℝ, ∀ R : ℝ, 2 ≤ R → ∀ z : ℂ, ‖z‖ = R →
    ‖xiF z‖ ≤ Real.exp (c * R * xiL R) := by
  rcases xiE_circle_growth with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  intro R hR z hz
  change ‖((1 / 2 : ℂ) + (1 / 2 : ℂ) * z * (z - 1) * completedRiemannZeta₀ z)‖ ≤
    Real.exp (c * R * (Real.log (R + 2) + 2))
  exact hc R hR z hz

/-- no-zero neighbourhood at the origin for xiF -/
lemma xiF_zero_free_ball : ∃ δ : ℝ, 0 < δ ∧ ∀ z : ℂ, ‖z‖ < δ → xiF z ≠ 0 := by
  rcases xiE_noZero_ball with ⟨δ₀, hpos, hle1, hball⟩
  refine ⟨δ₀, hpos, ?_⟩
  intro z hz
  exact hball z hz

/-! # Part 1 : local log-derivative difference bound (generic complex analysis) -/

/-- Local log-primitive: `g` analytic and non-zero on a ball admits an analytic `F` on the
ball with `F' = logDeriv g` and `(F w).re = log ‖g w‖`. -/
lemma pf_logPrimitiveOnBall {g : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hg_an : AnalyticOnNhd ℂ g (ball 0 R)) (hg_ne : ∀ w ∈ ball 0 R, g w ≠ 0) :
    ∃ F : ℂ → ℂ,
      DifferentiableOn ℂ F (ball 0 R) ∧
      (∀ w ∈ ball 0 R, HasDerivAt F (deriv g w / g w) w) ∧
      (F 0).re = Real.log ‖g 0‖ ∧
      ∀ w ∈ ball 0 R, (F w).re = Real.log ‖g w‖ := by
  let h : ℂ → ℂ := deriv g / g
  have h0ball : (0 : ℂ) ∈ ball (0 : ℂ) R := Metric.mem_ball_self hR
  have hgne0 : g 0 ≠ 0 := hg_ne 0 h0ball
  have hgDiffOn : DifferentiableOn ℂ g (ball (0 : ℂ) R) := hg_an.differentiableOn
  have hdg_an : AnalyticOnNhd ℂ (deriv g) (ball (0 : ℂ) R) := hg_an.deriv
  have hdgDiffOn : DifferentiableOn ℂ (deriv g) (ball (0 : ℂ) R) := hdg_an.differentiableOn
  have hhDiffOn : DifferentiableOn ℂ h (ball (0 : ℂ) R) := by
    simpa [h] using (DifferentiableOn.div hdgDiffOn hgDiffOn hg_ne)
  have hexact : IsExactOn h (ball (0 : ℂ) R) := hhDiffOn.isExactOn_ball
  obtain ⟨F, hF0, hFh⟩ := hexact.with_val_at (0 : ℂ) (Real.log ‖g 0‖ : ℂ)
  let q : ℂ → ℂ := (fun z : ℂ => cexp (F z)) / g
  have hF0_re : (F 0).re = Real.log ‖g 0‖ := by simp [hF0]
  have hq0 : ∀ x : ℂ, x ∈ ball (0 : ℂ) R → HasDerivAt q 0 x := by
    intro x hx
    have hgx : g x ≠ 0 := hg_ne x hx
    have hFx : HasDerivAt F (deriv g x / g x) x := by simpa [h] using hFh x hx
    have hFexp : HasDerivAt (fun z : ℂ => cexp (F z)) (cexp (F x) * (deriv g x / g x)) x := by
      exact (hFx.cexp : HasDerivAt (fun z : ℂ => cexp (F z)) (cexp (F x) * (deriv g x / g x)) x)
    have hg'_ : HasDerivAt g (deriv g x) x := by
      exact (hgDiffOn.differentiableAt (isOpen_ball.mem_nhds hx)).hasDerivAt
    have hqder := hFexp.div hg'_ hgx
    have hzero : ((cexp (F x) * (deriv g x / g x)) * g x - cexp (F x) * deriv g x) / g x ^ 2 = 0 := by
      have hnum : cexp (F x) * (deriv g x / g x) * g x - cexp (F x) * deriv g x = 0 := by
        field_simp [hgx]
        ring
      rw [hnum, zero_div]
    have hq0x : HasDerivAt q 0 x := by
      simpa [q] using (hqder.congr_deriv hzero)
    exact hq0x
  have hqDiffOn : DifferentiableOn ℂ q (ball (0 : ℂ) R) := by
    intro x hx
    exact (hq0 x hx).differentiableAt.differentiableWithinAt
  have hqderiv0 : EqOn (deriv q) 0 (ball (0 : ℂ) R) := by
    intro x hx
    exact (hq0 x hx).deriv
  have hqconst : ∀ w : ℂ, w ∈ ball (0 : ℂ) R → q w = q 0 := fun w hw =>
    (Metric.isOpen_ball.is_const_of_deriv_eq_zero (convex_ball (0 : ℂ) R).isPreconnected hqDiffOn
      hqderiv0 (x := w) (y := (0 : ℂ)) hw h0ball)
  refine ⟨F, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact (hFh x hx).differentiableAt.differentiableWithinAt
  · intro w hw
    simpa [h] using hFh w hw
  · exact hF0_re
  · intro w hw
    have hqnorm : ‖q w‖ = ‖q 0‖ := by rw [hqconst w hw]
    have hgnw : g w ≠ 0 := hg_ne w hw
    have hg0nz : ‖g 0‖ ≠ 0 := norm_ne_zero_iff.mpr hgne0
    have hnorm_exp0 : ‖cexp (F 0)‖ = ‖g 0‖ := by
      calc
        ‖cexp (F 0)‖ = Real.exp ((F 0).re) := Complex.norm_exp (F 0)
        _ = ‖g 0‖ := by
          rw [hF0_re, Real.exp_log]
          exact (norm_pos_iff.mpr hgne0)
    have hratio : ‖cexp (F w)‖ / ‖g w‖ = 1 := by
      have hq' : ‖cexp (F w) / g w‖ = ‖cexp (F 0) / g 0‖ := by
        simpa [q] using hqnorm
      rw [norm_div, norm_div] at hq'
      calc
        ‖cexp (F w)‖ / ‖g w‖ = ‖cexp (F 0)‖ / ‖g 0‖ := hq'
        _ = 1 := by
          rw [hnorm_exp0]
          exact div_self hg0nz
    have hnw : ‖g w‖ ≠ 0 := norm_ne_zero_iff.mpr hgnw
    have hnorm_expw : ‖cexp (F w)‖ = ‖g w‖ := by
      exact (div_eq_one_iff_eq hnw).mp hratio
    calc
      (F w).re = Real.log ‖cexp (F w)‖ := by
        rw [Complex.norm_exp, Real.log_exp]
      _ = Real.log ‖g w‖ := by rw [hnorm_expw]

/-- The analyticity of the log-derivative of a nonzero analytic function on a ball. -/
lemma pf_logDeriv_analytic_ball {g : ℂ → ℂ} {R : ℝ}
    (hg_an : AnalyticOnNhd ℂ g (ball 0 R)) (hg_ne : ∀ w ∈ ball 0 R, g w ≠ 0) :
    AnalyticOnNhd ℂ (fun w : ℂ => logDeriv g w) (ball (0 : ℂ) R) := by
  intro w hw
  have h1 : AnalyticAt ℂ (deriv g) w := (hg_an.deriv) w hw
  have h2 : AnalyticAt ℂ g w := hg_an w hw
  have hq : AnalyticAt ℂ (fun z : ℂ => deriv g z / g z) w := h1.div h2 (hg_ne w hw)
  convert hq using 1
  funext z
  rw [logDeriv_apply]

/-- derivative-difference bound for a log-primitive, from a sup bound on log‖g‖. -/
lemma pf_logDeriv_sub_of_sup {g : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hg_an : AnalyticOnNhd ℂ g (ball 0 R)) (hg_ne : ∀ w ∈ ball 0 R, g w ≠ 0)
    {M0 : ℝ} (hM0 : 0 ≤ M0)
    (hgM : ∀ w : ℂ, w ∈ ball 0 R → Real.log ‖g w‖ ≤ M0)
    (hg0 : |Real.log ‖g 0‖| ≤ M0) {s : ℂ} (hs : ‖s‖ ≤ R / 8) :
    ‖logDeriv g s - logDeriv g 0‖ ≤ 1024 * (max M0 1) * ‖s‖ / R ^ 2 := by
  classical
  rcases pf_logPrimitiveOnBall (g := g) (R := R) hR hg_an hg_ne with ⟨F, hFdiff, hFh, hF0re, hFre⟩
  let M : ℝ := 2 * max M0 1
  have hMpos : 0 < M := by dsimp [M]; positivity
  have hMge : 2 * M0 ≤ M := by
    dsimp [M]
    have h1 : M0 ≤ max M0 1 := le_max_left M0 1
    nlinarith
  have hFreM : ∀ w : ℂ, w ∈ ball (0 : ℂ) R → ((F w - F 0).re) ≤ M := by
    intro w hw
    have hle1 : (F w).re ≤ M0 := by
      rw [hFre w hw]
      exact hgM w hw
    have hle2 : -M0 ≤ (F 0).re := by
      rw [hF0re]
      have habs := abs_le.mp hg0
      linarith
    have hmain : (F w).re - (F 0).re ≤ 2 * M0 := by linarith
    have : ((F w - F 0).re) = (F w).re - (F 0).re := by simp
    rw [this]
    exact le_trans hmain hMge
  have hF0eq : (fun w : ℂ => F w - F 0) 0 = 0 := by simp
  have hFdiff2 : DifferentiableOn ℂ (fun w : ℂ => F w - F 0) (ball (0 : ℂ) R) := by
    intro w hw
    exact (DifferentiableAt.sub (hFdiff.differentiableAt (isOpen_ball.mem_nhds hw))
      (differentiableAt_const (F 0))).differentiableWithinAt
  have hsup : ∀ w : ℂ, ‖w‖ ≤ R / 2 → ‖F w - F 0‖ ≤ 2 * M := by
    intro w hw
    have hwb : w ∈ ball (0 : ℂ) R := by
      rw [mem_ball_zero_iff]
      have hR2 : 0 ≤ R / 2 := by positivity
      nlinarith
    have hbc := Complex.borelCaratheodory_zero (M := M) hMpos (f := fun z : ℂ => F z - F 0)
      (R := R) hFdiff2 (by intro z hz; simpa using hFreM z hz) hR hwb hF0eq
    have hden : 0 < R - ‖w‖ := by
      rw [mem_ball_zero_iff] at hwb
      linarith
    have hle : ‖w‖ / (R - ‖w‖) ≤ 1 := by
      rw [div_le_one hden]
      have hR2 : R / 2 ≤ R - ‖w‖ := by nlinarith
      linarith
    calc
      ‖F w - F 0‖ ≤ 2 * M * ‖w‖ / (R - ‖w‖) := hbc
      _ = 2 * M * (‖w‖ / (R - ‖w‖)) := by ring
      _ ≤ 2 * M * 1 := by
        exact mul_le_mul_of_nonneg_left hle (by positivity : 0 ≤ 2 * M)
      _ = 2 * M := by ring
  -- ‖logDeriv g z‖ ≤ 16*M/R for ‖z‖ ≤ 3R/8
  have hder1 : ∀ z : ℂ, ‖z‖ ≤ 3 * R / 8 → ‖logDeriv g z‖ ≤ 16 * M / R := by
    intro z hz
    let r : ℝ := R / 8
    have hr : 0 < r := by dsimp [r]; positivity
    have hclosed : Metric.closedBall z r ⊆ ball (0 : ℂ) R := by
      intro x hx
      rw [Metric.mem_closedBall, dist_eq_norm] at hx
      rw [mem_ball_zero_iff]
      have hle : ‖x‖ ≤ ‖z‖ + ‖x - z‖ := by
        have hx2 : ‖x‖ = ‖z + (x - z)‖ := by rw [← add_sub_cancel z x]; ring_nf
        rw [hx2]
        simpa [add_comm] using (norm_add_le z (x - z))
      have hxr : ‖x - z‖ ≤ r := hx
      dsimp [r] at hxr ⊢
      nlinarith [hz, hxr]
    have hFz : DifferentiableOn ℂ (fun w : ℂ => F w - F 0) (Metric.closedBall z r) := by
      intro x hx
      have hxR : x ∈ ball (0 : ℂ) R := hclosed hx
      exact (DifferentiableAt.sub (hFdiff.differentiableAt (isOpen_ball.mem_nhds hxR))
        (differentiableAt_const (F 0))).differentiableWithinAt
    have hdiffCl : DiffContOnCl ℂ (fun w : ℂ => F w - F 0) (ball z r) := by
      refine DifferentiableOn.diffContOnCl ?_
      simpa [r, closure_ball z (ne_of_gt hr)] using hFz
    have hC : ∀ w : ℂ, w ∈ sphere z r → ‖F w - F 0‖ ≤ 2 * M := by
      intro w hw
      rw [Metric.mem_sphere] at hw
      have hwz : ‖w - z‖ = r := by simpa [dist_eq_norm] using hw
      have hw' : ‖w‖ ≤ R / 2 := by
        have hle : ‖w‖ ≤ ‖z‖ + ‖w - z‖ := by
          have hw2 : ‖w‖ = ‖z + (w - z)‖ := by rw [← add_sub_cancel z w]; ring_nf
          rw [hw2]
          simpa [add_comm] using (norm_add_le z (w - z))
        dsimp [r] at hwz ⊢
        nlinarith [hz, hwz]
      exact hsup w hw'
    have hCau := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (f := fun w : ℂ => F w - F 0)
      (c := z) (R := r) hr hdiffCl (by intro w hw; simpa using hC w hw)
    have hzR : z ∈ ball (0 : ℂ) R := by
      rw [mem_ball_zero_iff]
      nlinarith [hz, show 0 < R from hR]
    have hfder : deriv (fun w : ℂ => F w - F 0) z = deriv F z := by
      have hFdz : DifferentiableAt ℂ F z := hFdiff.differentiableAt (isOpen_ball.mem_nhds hzR)
      calc
        deriv (fun w : ℂ => F w - F 0) z
            = deriv ((fun w : ℂ => F w) - (fun _ : ℂ => F 0)) z := by rfl
        _ = deriv F z - deriv (fun _ : ℂ => F 0) z := by
            exact deriv_sub hFdz (differentiableAt_const (F 0))
        _ = deriv F z := by simp
    have hlogz : logDeriv g z = deriv F z := by
      have hFhz := hFh z hzR
      rw [logDeriv_apply, hFhz.deriv]
    calc
      ‖logDeriv g z‖ = ‖deriv F z‖ := by rw [hlogz]
      _ = ‖deriv (fun w : ℂ => F w - F 0) z‖ := by rw [hfder]
      _ ≤ (2 * M) / r := hCau
      _ = 16 * M / R := by
        dsimp [r]
        field_simp [show R ≠ 0 from ne_of_gt hR]
        ring
  -- ‖deriv (logDeriv g) z‖ ≤ 128*M/R^2 for ‖z‖ ≤ R/4
  have hder2 : ∀ z : ℂ, ‖z‖ ≤ R / 4 → ‖deriv (logDeriv g) z‖ ≤ 128 * M / R ^ 2 := by
    intro z hz
    let r : ℝ := R / 8
    have hr : 0 < r := by dsimp [r]; positivity
    have hz3 : ∀ w : ℂ, w ∈ sphere z r → ‖w‖ ≤ 3 * R / 8 := by
      intro w hw
      rw [Metric.mem_sphere] at hw
      have hwz : ‖w - z‖ = r := by simpa [dist_eq_norm] using hw
      have hle : ‖w‖ ≤ ‖z‖ + ‖w - z‖ := by
        have hw2 : ‖w‖ = ‖z + (w - z)‖ := by rw [← add_sub_cancel z w]; ring_nf
        rw [hw2]
        simpa [add_comm] using (norm_add_le z (w - z))
      dsimp [r] at hwz ⊢
      nlinarith [hz, hwz]
    have hF' : ∀ w : ℂ, w ∈ sphere z r → ‖logDeriv g w‖ ≤ 16 * M / R := by
      intro w hw
      exact hder1 w (hz3 w hw)
    have hclosed : Metric.closedBall z r ⊆ ball (0 : ℂ) R := by
      intro x hx
      rw [Metric.mem_closedBall, dist_eq_norm] at hx
      rw [mem_ball_zero_iff]
      have hle : ‖x‖ ≤ ‖z‖ + ‖x - z‖ := by
        have hx2 : ‖x‖ = ‖z + (x - z)‖ := by rw [← add_sub_cancel z x]; ring_nf
        rw [hx2]
        simpa [add_comm] using (norm_add_le z (x - z))
      have hxr : ‖x - z‖ ≤ r := hx
      dsimp [r] at hxr ⊢
      nlinarith [hz, hxr]
    have hlg_an : AnalyticOnNhd ℂ (fun w : ℂ => logDeriv g w) (ball (0 : ℂ) R) :=
      pf_logDeriv_analytic_ball hg_an hg_ne
    have hlg_z : DifferentiableOn ℂ (fun w : ℂ => logDeriv g w) (Metric.closedBall z r) := by
      intro x hx
      have hxR : x ∈ ball (0 : ℂ) R := hclosed hx
      exact (hlg_an.differentiableOn.differentiableAt (isOpen_ball.mem_nhds hxR)).differentiableWithinAt
    have hdiffCl : DiffContOnCl ℂ (fun w : ℂ => logDeriv g w) (ball z r) := by
      refine DifferentiableOn.diffContOnCl ?_
      simpa [r, closure_ball z (ne_of_gt hr)] using hlg_z
    have hCau := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (f := fun w : ℂ => logDeriv g w)
      (c := z) (R := r) hr hdiffCl hF'
    calc
      ‖deriv (logDeriv g) z‖ ≤ (16 * M / R) / r := hCau
      _ = 128 * M / R ^ 2 := by
        dsimp [r]
        field_simp [show R ≠ 0 from ne_of_gt hR]
        ring
  -- mean value on the convex ball
  have hsR4 : s ∈ ball (0 : ℂ) (R / 4) := by
    rw [mem_ball_zero_iff]
    have hRp : 0 < R / 4 := by positivity
    nlinarith
  have h0R4 : (0 : ℂ) ∈ ball (0 : ℂ) (R / 4) := by
    rw [mem_ball_zero_iff]
    have hR4 : 0 < R / 4 := by positivity
    simpa using hR4
  have hCbound : ∀ z : ℂ, z ∈ ball (0 : ℂ) (R / 4) → ‖deriv (logDeriv g) z‖ ≤ 128 * M / R ^ 2 := by
    intro z hz
    rw [mem_ball_zero_iff] at hz
    exact hder2 z (by nlinarith)
  have hdiff_at : ∀ z : ℂ, z ∈ ball (0 : ℂ) (R / 4) → DifferentiableAt ℂ (logDeriv g) z := by
    intro z hz
    have hlg_anR4 : AnalyticOnNhd ℂ (fun w : ℂ => logDeriv g w) (ball (0 : ℂ) (R / 4)) := by
      intro w hw
      have hwR : w ∈ ball (0 : ℂ) R := by
        rw [mem_ball_zero_iff]
        rw [mem_ball_zero_iff] at hw
        nlinarith
      exact (pf_logDeriv_analytic_ball hg_an hg_ne) w hwR
    exact (hlg_anR4.differentiableOn.differentiableAt (isOpen_ball.mem_nhds hz))
  have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℂ) (f := fun w : ℂ => logDeriv g w)
    (s := ball (0 : ℂ) (R / 4)) (C := 128 * M / R ^ 2) hdiff_at hCbound
    (convex_ball (0 : ℂ) (R / 4)) h0R4 hsR4
  have hder : ‖logDeriv g s - logDeriv g 0‖ ≤ 128 * M * ‖s‖ / R ^ 2 := by
    have hmvt' : ‖logDeriv g s - logDeriv g 0‖ ≤ (128 * M / R ^ 2) * ‖s‖ := by simpa using hmvt
    calc
      ‖logDeriv g s - logDeriv g 0‖ ≤ (128 * M / R ^ 2) * ‖s‖ := hmvt'
      _ = 128 * M * ‖s‖ / R ^ 2 := by
        field_simp [show R ^ 2 ≠ 0 from pow_ne_zero 2 (ne_of_gt hR)]
  have hle_mul : 128 * M ≤ 1024 * max M0 1 := by
    dsimp [M]
    nlinarith
  have hle1 : 128 * M * ‖s‖ / R ^ 2 ≤ 1024 * (max M0 1) * ‖s‖ / R ^ 2 := by
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hle_mul (norm_nonneg s))
      (sq_pos_of_pos hR).le
  calc
    ‖logDeriv g s - logDeriv g 0‖ ≤ 128 * M * ‖s‖ / R ^ 2 := hder
    _ ≤ 1024 * (max M0 1) * ‖s‖ / R ^ 2 := hle1



/-! # Part 2 : divisor/factorisation bookkeeping and the good-circle log bound -/

/-- Zeros of the completed L-function stay away from 0 ( primitive non-trivial). -/
lemma xiF_zeros_ge_delta  
      :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ u : ℂ, xiF u = 0 → δ₀ ≤ ‖u‖ := by
  rcases xiF_zero_free_ball  with ⟨δ, hδpos, hδ⟩
  let δ₀ : ℝ := min δ 1
  have hδ₀pos : 0 < δ₀ := by dsimp [δ₀]; positivity
  have hδ₀le1 : δ₀ ≤ 1 := by dsimp [δ₀]; exact min_le_right δ 1
  refine ⟨δ₀, hδ₀pos, hδ₀le1, ?_⟩
  intro u hu
  by_contra hlt
  have hδ₀leδ : δ₀ ≤ δ := by dsimp [δ₀]; exact min_le_left δ 1
  have huδ : ‖u‖ < δ := lt_of_lt_of_le (lt_of_not_ge hlt) hδ₀leδ
  exact (hδ u huδ) hu

lemma xiF_divisor_nonneg_closedBall  
     (R : ℝ) (u : ℂ) :
    0 ≤ (MeromorphicOn.divisor (xiF)
      (closedBall (0 : ℂ) R)) u := by
  have hfan : AnalyticOnNhd ℂ (xiF)
      (closedBall (0 : ℂ) R) := by
    intro z hz
    exact xiF_diff.analyticAt z
  exact (MeromorphicOn.AnalyticOnNhd.divisor_nonneg hfan) u

lemma xiF_divisor_support_finite  
     (R : ℝ) :
    (Function.support (fun u : ℂ =>
      MeromorphicOn.divisor (xiF)
        (closedBall (0 : ℂ) R) u)).Finite := by
  have hfan : AnalyticOnNhd ℂ (xiF)
      (closedBall (0 : ℂ) R) := by
    intro z hz
    exact xiF_diff.analyticAt z
  exact MeromorphicOn.divisor_support_finite_of_subset
    (f := xiF)
    (V := closedBall (0 : ℂ) R) (U := closedBall (0 : ℂ) R)
    hfan.meromorphicOn (isCompact_closedBall (0 : ℂ) R) (by intro z hz; exact hz)

lemma xiF_divisor_ne_zero_is_zero  
     {R : ℝ} {z : ℂ}
    (hd : (MeromorphicOn.divisor (xiF)
      (closedBall (0 : ℂ) R)) z ≠ 0) :
    xiF z = 0 := by
  let Λ : ℂ → ℂ := xiF
  have hfan : AnalyticOnNhd ℂ Λ (closedBall (0 : ℂ) R) := by
    intro w hw
    exact xiF_diff.analyticAt w
  have hzB : z ∈ closedBall (0 : ℂ) R := by
    by_contra hout
    rw [MeromorphicOn.divisor_def] at hd
    simp [hout] at hd
  by_contra hfz
  have hord : meromorphicOrderAt Λ z = 0 :=
    Commons.Analysis.Complex.meromorphicOrderAt_eq_zero_of_ne_zero (hfan z hzB) hfz
  have hdiv : MeromorphicOn.divisor Λ (closedBall (0 : ℂ) R) z = 0 := by
    rw [MeromorphicOn.divisor_apply hfan.meromorphicOn hzB]
    simp [hord, Λ]
  exact hd (by simpa [Λ] using hdiv)

lemma pf_norm_finset_prod {ι : Type*} (S : Finset ι) (a : ι → ℂ) :
    ‖∏ i ∈ S, a i‖ = ∏ i ∈ S, ‖a i‖ := by
  classical
  refine Finset.induction_on S ?_ (fun i S hi ih => ?_)
  · simp
  · rw [Finset.prod_insert hi, Finset.prod_insert hi, norm_mul, ih]

lemma pf_pow_zpow_toNat {x : ℝ} {d : ℤ} (hd : 0 ≤ d) : x ^ d = x ^ d.toNat := by
  rw [← Int.toNat_of_nonneg hd]
  exact (zpow_natCast x d.toNat).symm

lemma pf_zpow_le_of_le {x y : ℝ} {d : ℤ} (hx : 0 ≤ x) (hxy : x ≤ y) (hd : 0 ≤ d) :
    x ^ d ≤ y ^ d := by
  rw [pf_pow_zpow_toNat hd, pf_pow_zpow_toNat hd]
  exact pow_le_pow_left₀ hx hxy d.toNat

lemma pf_zpow_pos {x : ℝ} {d : ℤ} (hx : 0 < x) (hd : 0 ≤ d) : 0 < x ^ d := by
  rw [pf_pow_zpow_toNat hd]
  exact pow_pos hx d.toNat

lemma pf_log_zpow {x : ℝ} {d : ℤ} (hx : 0 < x) (hd : 0 ≤ d) :
    Real.log (x ^ d) = (d : ℝ) * Real.log x := by
  rw [pf_pow_zpow_toNat hd]
  have hlog : Real.log (x ^ d.toNat) = (d.toNat : ℝ) * Real.log x := Real.log_pow x d.toNat
  have hcast : (d.toNat : ℝ) = (d : ℝ) := by
    rw [← Int.cast_natCast d.toNat]
    exact congrArg (fun a : ℤ => (a : ℝ)) (Int.toNat_of_nonneg hd)
  simpa [hcast] using hlog

/-- norm of a zpower equals the zpower of the norm. -/
lemma pf_norm_zpow_eq (z : ℂ) (d : ℤ) : ‖z ^ d‖ = ‖z‖ ^ d := norm_zpow z d

/-- `-log ‖P_T ζ‖ ≤ 2·log L · Z_T` for ζ on a good circle of radius T. -/
lemma xiF_fac_log_lower  
     {A T : ℝ} (hA0 : 0 ≤ A) (hT0 : 0 < T)
    (hmargin : ∀ u : ℂ, xiF u = 0 →
      (xiL A) ^ 2 * |‖u‖ - T| ≥ 1)
    {ζ : ℂ} (hζ : ‖ζ‖ = T) :
    -Real.log ‖∏ᶠ u : ℂ, (ζ - u) ^ (MeromorphicOn.divisor
        (xiF) (closedBall (0 : ℂ) T) u)‖ ≤
      (2 * Real.log (xiL A)) *
        (∑ᶠ u : ℂ, ((MeromorphicOn.divisor (xiF)
          (closedBall (0 : ℂ) T)) u : ℝ)) := by
  classical
  let Λ : ℂ → ℂ := xiF
  let d : ℂ → ℤ := fun u => MeromorphicOn.divisor Λ (closedBall (0 : ℂ) T) u
  let L : ℝ := xiL A
  have hLpos : 0 < L := xiL_pos  hA0
  have hL2pos : 0 < L ^ 2 := pow_pos hLpos 2
  let m : ℝ := 1 / L ^ 2
  have hmpos : 0 < m := by dsimp [m]; exact div_pos (by norm_num) hL2pos
  have hd_nonneg : ∀ u, 0 ≤ d u := by
    intro u
    dsimp [d]
    exact xiF_divisor_nonneg_closedBall  T u
  have hsupport : (Function.support d).Finite := by
    dsimp [d]
    exact xiF_divisor_support_finite  T
  let S : Finset ℂ := hsupport.toFinset
  have hmemS : ∀ u : ℂ, u ∈ S ↔ d u ≠ 0 := by
    intro u
    dsimp [S]
    rw [Set.Finite.mem_toFinset]
    rfl
  have hdist : ∀ u : ℂ, u ∈ S → m ≤ ‖ζ - u‖ := by
    intro u hu
    have hdne : d u ≠ 0 := (hmemS u).mp hu
    have hzu : Λ u = 0 := by
      dsimp [d] at hdne
      exact xiF_divisor_ne_zero_is_zero  hdne
    have hmarg := hmargin u (by simpa [Λ] using hzu)
    have hmul' : 1 ≤ |‖u‖ - T| * (L ^ 2) := by
      simpa [mul_comm, L] using hmarg
    have hle_m : m ≤ |‖u‖ - T| := (div_le_iff₀ hL2pos).mpr hmul'
    have habs : |‖u‖ - ‖ζ‖| ≤ ‖ζ - u‖ := by
      simpa [abs_sub_comm] using (abs_norm_sub_norm_le ζ u)
    have hrew : |‖u‖ - T| = |‖u‖ - ‖ζ‖| := by rw [hζ]
    exact le_trans hle_m (by rwa [hrew])
  have hprod_pos_fac : ∀ u : ℂ, u ∈ S → 0 < ‖(ζ - u) ^ (d u)‖ := by
    intro u hu
    have hb : 0 < ‖ζ - u‖ := lt_of_lt_of_le hmpos (hdist u hu)
    have hpow : ‖(ζ - u) ^ (d u)‖ = ‖ζ - u‖ ^ (d u) := pf_norm_zpow_eq (ζ - u) (d u)
    rw [hpow]
    exact pf_zpow_pos hb (hd_nonneg u)
  have hlog_per : ∀ u : ℂ, u ∈ S →
      -Real.log ‖(ζ - u) ^ (d u)‖ ≤ (d u : ℝ) * (2 * Real.log L) := by
    intro u hu
    have hmle : m ≤ ‖ζ - u‖ := hdist u hu
    have hb : 0 < ‖ζ - u‖ := lt_of_lt_of_le hmpos hmle
    have hpow_le : m ^ (d u) ≤ ‖ζ - u‖ ^ (d u) :=
      pf_zpow_le_of_le (le_of_lt hmpos) hmle (hd_nonneg u)
    have hnorm : ‖(ζ - u) ^ (d u)‖ = ‖ζ - u‖ ^ (d u) := pf_norm_zpow_eq (ζ - u) (d u)
    have h1 : 0 < m ^ (d u) := pf_zpow_pos hmpos (hd_nonneg u)
    have h2 : 0 < ‖ζ - u‖ ^ (d u) := pf_zpow_pos hb (hd_nonneg u)
    have hlog_ge : Real.log (m ^ (d u)) ≤ Real.log ‖(ζ - u) ^ (d u)‖ := by
      rw [hnorm]
      exact Real.log_le_log h1 hpow_le
    have hlogm : Real.log (m ^ (d u)) = (d u : ℝ) * Real.log m := pf_log_zpow hmpos (hd_nonneg u)
    have hlogmval : Real.log m = -2 * Real.log L := by
      dsimp [m]
      rw [one_div, Real.log_inv, Real.log_pow]
      ring
    have hstep : (d u : ℝ) * Real.log m ≤ Real.log ‖(ζ - u) ^ (d u)‖ := by
      simpa [hlogm] using hlog_ge
    have hmain : -Real.log ‖(ζ - u) ^ (d u)‖ ≤ (d u : ℝ) * (2 * Real.log L) := by
      have hcalc : -Real.log ‖(ζ - u) ^ (d u)‖ ≤ -(d u : ℝ) * Real.log m := by linarith
      have hmval : -(d u : ℝ) * Real.log m = (d u : ℝ) * (2 * Real.log L) := by
        rw [hlogmval]
        ring
      linarith
    exact hmain
  have hsubP : mulSupport (fun u : ℂ => (ζ - u) ^ (d u)) ⊆ (S : Set ℂ) := by
    intro u hu
    rw [Function.mem_mulSupport] at hu
    have hdne : d u ≠ 0 := by
      intro hd0
      have : (ζ - u) ^ (d u) = 1 := by simp [hd0]
      exact hu this
    exact (hmemS u).mpr hdne
  have hprod_eq : (∏ᶠ u : ℂ, (ζ - u) ^ (d u)) = ∏ u ∈ S, (ζ - u) ^ (d u) :=
    finprod_eq_prod_of_mulSupport_subset (fun u : ℂ => (ζ - u) ^ (d u)) hsubP
  have hfin_eq : (∑ᶠ u : ℂ, ((d u : ℤ) : ℝ)) = ∑ u ∈ S, ((d u : ℤ) : ℝ) := by
    refine finsum_eq_sum_of_support_subset (fun u : ℂ => ((d u : ℤ) : ℝ)) ?_
    intro u hu
    rw [Function.mem_support] at hu
    have hdne : d u ≠ 0 := by
      intro hd0
      exact hu (by simp [hd0])
    exact (hmemS u).mpr hdne
  have hZge0 : 0 ≤ ∑ᶠ u : ℂ, ((d u : ℤ) : ℝ) := by
    rw [hfin_eq]
    exact Finset.sum_nonneg (by intro u hu; exact_mod_cast (hd_nonneg u))
  have h2L : 0 ≤ 2 * Real.log L := by
    have h1 : 1 ≤ L := by linarith [xiL_ge_two  hA0]
    have hlog : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
    linarith
  calc
    -Real.log ‖∏ᶠ u : ℂ, (ζ - u) ^ (d u)‖
        = -Real.log ‖∏ u ∈ S, (ζ - u) ^ (d u)‖ := by rw [hprod_eq]
    _ = -Real.log (∏ u ∈ S, ‖(ζ - u) ^ (d u)‖) := by
        rw [pf_norm_finset_prod S (fun u => (ζ - u) ^ (d u))]
    _ = -(∑ u ∈ S, Real.log ‖(ζ - u) ^ (d u)‖) := by
        rw [Real.log_prod]
        intro u hu
        exact (hprod_pos_fac u hu).ne'
    _ = ∑ u ∈ S, -Real.log ‖(ζ - u) ^ (d u)‖ := by simp [Finset.sum_neg_distrib]
    _ ≤ ∑ u ∈ S, ((d u : ℤ) : ℝ) * (2 * Real.log L) := by
        refine Finset.sum_le_sum (fun u hu => ?_)
        have hlogp := hlog_per u hu
        -- hlog_per has (d u : ℝ) as ℤ-cast of the int d; align casts
        have hcastd : ((d u : ℤ) : ℝ) = (d u : ℝ) := rfl
        simpa [hcastd] using hlogp
    _ = (∑ u ∈ S, ((d u : ℤ) : ℝ)) * (2 * Real.log L) := by rw [Finset.sum_mul]
    _ = (∑ᶠ u : ℂ, ((d u : ℤ) : ℝ)) * (2 * Real.log L) := by rw [hfin_eq]
    _ = (2 * Real.log L) * (∑ᶠ u : ℂ, ((d u : ℤ) : ℝ)) := by ring
    _ = (2 * Real.log (xiL A)) * (∑ᶠ u : ℂ, (((MeromorphicOn.divisor Λ
          (closedBall (0 : ℂ) T)) u : ℤ) : ℝ)) := by simp [d, L]



def xiZ (T : ℝ) : ℝ :=
  ∑ᶠ u : ℂ, (((MeromorphicOn.divisor xiF (Metric.closedBall (0 : ℂ) T)) u : ℤ) : ℝ)

def xiP (T : ℝ) (z : ℂ) : ℂ :=
  ∏ᶠ u : ℂ, (z - u) ^ (MeromorphicOn.divisor xiF (closedBall (0 : ℂ) T) u)

lemma pf_log_eq_of_mul {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0) :
    Real.log ‖x * y‖ = Real.log ‖x‖ + Real.log ‖y‖ := by
  rw [norm_mul]
  exact Real.log_mul (norm_ne_zero_iff.mpr hx) (norm_ne_zero_iff.mpr hy)

/-- completedL: zero count bound rearranged into xiZ notation. -/
lemma xiF_Log_bound   {T : ℝ} (hT2 : 2 ≤ T)
    {gc : ℝ} (hgc : ∀ R : ℝ, 2 ≤ R → ∀ z : ℂ, ‖z‖ = R →
      ‖xiF z‖ ≤ Real.exp (gc * R * xiL R))
    {ζ : ℂ} (hζ : ‖ζ‖ = T) (hζnz : xiF ζ ≠ 0) :
    Real.log ‖xiF ζ‖ ≤ gc * T * xiL T := by
  have hb := hgc T hT2 ζ hζ
  have hle : Real.log ‖xiF ζ‖ ≤
      Real.log (Real.exp (gc * T * xiL T)) := by
    exact Real.log_le_log (norm_pos_iff.mpr hζnz) hb
  rwa [Real.log_exp] at hle

/-- The divisor product is nonzero at a point of the good circle. -/
lemma xiF_P_ne_zero_circle  
      {T : ℝ} (hTpos : 0 < T)
    (hcirc : ∀ u : ℂ, ‖u‖ = T → xiF u ≠ 0)
    {ζ : ℂ} (hζ : ‖ζ‖ = T) : xiP  T ζ ≠ 0 := by
  classical
  let Λ : ℂ → ℂ := xiF
  have hΛ0 : Λ 0 ≠ 0 := by simpa [Λ] using xiF_zero_ne
  have hΛdiff : Differentiable ℂ Λ := by simpa [Λ] using xiF_diff
  rcases factorization_open (f := Λ) (R := T) hTpos hΛdiff hΛ0 hcirc with ⟨g, ε, hε, hg_an, hg_nz, hfac⟩
  have hζε : ζ ∈ ball (0 : ℂ) (T + ε) := by
    rw [mem_ball_zero_iff]
    nlinarith [hζ, hε]
  have hgζ : g ζ ≠ 0 := hg_nz ζ hζε
  have hfacζ := hfac ζ hζε
  have hΛζ : Λ ζ ≠ 0 := by simpa [Λ] using hcirc ζ hζ
  have hmul : Λ ζ = (∏ᶠ u : ℂ, (ζ - u) ^ (MeromorphicOn.divisor Λ (closedBall (0 : ℂ) T) u)) * g ζ := hfacζ
  have hmul' : xiP  T ζ * g ζ ≠ 0 := by simpa [xiP, Λ, hmul] using hΛζ
  exact (mul_ne_zero_iff.mp hmul').1

/-- |log‖P_T 0‖| ≤ Z·(log T + |log δ₀|) for the divisor product at 0. -/
lemma xiF_P0_log_bound   
    {T : ℝ} (hT : 1 ≤ T) (δ₀ : ℝ) (hδ₀pos : 0 < δ₀)
    (hδ₀ : ∀ u : ℂ, xiF u = 0 → δ₀ ≤ ‖u‖) :
    |Real.log ‖xiP  T 0‖| ≤
      (xiZ  T) * (Real.log T + |Real.log δ₀|) := by
  classical
  let Λc : ℂ → ℂ := xiF
  let d : ℂ → ℤ := fun u => MeromorphicOn.divisor Λc (closedBall (0 : ℂ) T) u
  have hd_nonneg : ∀ u : ℂ, 0 ≤ d u := by
    intro u
    dsimp [d]
    exact xiF_divisor_nonneg_closedBall  T u
  have hsupp : (Function.support d).Finite := by
    dsimp [d]
    exact xiF_divisor_support_finite  T
  let S : Finset ℂ := hsupp.toFinset
  have hmemS : ∀ u : ℂ, u ∈ S ↔ d u ≠ 0 := by
    intro u
    dsimp [S]
    rw [Set.Finite.mem_toFinset]
    rfl
  have hδT : ∀ u : ℂ, u ∈ S → δ₀ ≤ ‖u‖ ∧ ‖u‖ ≤ T := by
    intro u hu
    have hdne : d u ≠ 0 := (hmemS u).mp hu
    have hzu : Λc u = 0 := by
      dsimp [d] at hdne
      exact xiF_divisor_ne_zero_is_zero  hdne
    have huδ : δ₀ ≤ ‖u‖ := hδ₀ u (by simpa [Λc] using hzu)
    have huT : ‖u‖ ≤ T := by
      by_contra hout
      have hdne0 : MeromorphicOn.divisor Λc (closedBall (0 : ℂ) T) u ≠ 0 := by simpa [d] using hdne
      rw [MeromorphicOn.divisor_def] at hdne0
      simp [hout] at hdne0
    exact ⟨huδ, huT⟩
  have hlogTnonneg : 0 ≤ Real.log T := Real.log_nonneg hT
  let B : ℝ := Real.log T + |Real.log δ₀|
  have hB_nonneg : 0 ≤ B := by dsimp [B]; positivity
  have hlogB : ∀ u : ℂ, u ∈ S → |Real.log ‖u‖| ≤ B := by
    intro u hu
    have hδle : δ₀ ≤ ‖u‖ := (hδT u hu).1
    have hTge : ‖u‖ ≤ T := (hδT u hu).2
    have hpos : 0 < ‖u‖ := lt_of_lt_of_le hδ₀pos hδle
    have hle1 : Real.log ‖u‖ ≤ B := by
      have h : Real.log ‖u‖ ≤ Real.log T := Real.log_le_log hpos hTge
      have habs : 0 ≤ |Real.log δ₀| := abs_nonneg _
      dsimp [B]
      linarith
    have hle2 : -B ≤ Real.log ‖u‖ := by
      have h : Real.log δ₀ ≤ Real.log ‖u‖ := Real.log_le_log hδ₀pos hδle
      have hnegabs : -|Real.log δ₀| ≤ Real.log δ₀ := neg_abs_le (Real.log δ₀)
      have h3 : -B ≤ -|Real.log δ₀| := by
        dsimp [B]
        linarith
      exact le_trans (le_trans h3 hnegabs) h
    exact abs_le.mpr ⟨hle2, hle1⟩
  have hprod_pos_fac : ∀ u : ℂ, u ∈ S → 0 < ‖(0 : ℂ) - u‖ := by
    intro u hu
    exact lt_of_lt_of_le hδ₀pos (by simpa [norm_sub_rev] using (hδT u hu).1)
  have hlog_per : ∀ u : ℂ, u ∈ S → -B ≤ Real.log ‖(0 : ℂ) - u‖ ∧ Real.log ‖(0 : ℂ) - u‖ ≤ B := by
    intro u hu
    have hb : |Real.log ‖(0 : ℂ) - u‖| ≤ B := by
      simpa [norm_sub_rev] using hlogB u hu
    exact abs_le.mp hb
  have hsubP : mulSupport (fun u : ℂ => (0 - u) ^ (d u)) ⊆ (S : Set ℂ) := by
    intro u hu
    rw [Function.mem_mulSupport] at hu
    have hdne : d u ≠ 0 := by
      intro hd0
      have : (0 - u) ^ (d u) = 1 := by simp [hd0]
      exact hu this
    exact (hmemS u).mpr hdne
  have hprod_eq : (∏ᶠ u : ℂ, (0 - u) ^ (d u)) = ∏ u ∈ S, (0 - u) ^ (d u) :=
    finprod_eq_prod_of_mulSupport_subset (fun u : ℂ => (0 - u) ^ (d u)) hsubP
  have hfac_pos : ∀ u : ℂ, u ∈ S → 0 < ‖(0 - u) ^ (d u)‖ := by
    intro u hu
    have hb : 0 < ‖(0 : ℂ) - u‖ := hprod_pos_fac u hu
    have hpow : ‖(0 - u) ^ (d u)‖ = ‖(0 : ℂ) - u‖ ^ (d u) := pf_norm_zpow_eq (0 - u) (d u)
    rw [hpow]
    exact pf_zpow_pos hb (hd_nonneg u)
  have hlog_all :
      Real.log ‖∏ᶠ u : ℂ, (0 - u) ^ (d u)‖ = ∑ u ∈ S, ((d u : ℤ) : ℝ) * Real.log ‖(0 : ℂ) - u‖ := by
    calc
      Real.log ‖∏ᶠ u : ℂ, (0 - u) ^ (d u)‖ = Real.log ‖∏ u ∈ S, (0 - u) ^ (d u)‖ := by rw [hprod_eq]
      _ = Real.log (∏ u ∈ S, ‖(0 - u) ^ (d u)‖) := by
          rw [pf_norm_finset_prod S (fun u => (0 - u) ^ (d u))]
      _ = ∑ u ∈ S, Real.log ‖(0 - u) ^ (d u)‖ := by
          exact Real.log_prod (fun u hu => (hfac_pos u hu).ne')
      _ = ∑ u ∈ S, ((d u : ℤ) : ℝ) * Real.log ‖(0 : ℂ) - u‖ := by
          apply Finset.sum_congr rfl
          intro u hu
          have hpow : ‖(0 - u) ^ (d u)‖ = ‖(0 : ℂ) - u‖ ^ (d u) := pf_norm_zpow_eq (0 - u) (d u)
          rw [hpow]
          have hlog : Real.log (‖(0 : ℂ) - u‖ ^ (d u)) = (d u : ℝ) * Real.log ‖(0 : ℂ) - u‖ :=
            pf_log_zpow (hprod_pos_fac u hu) (hd_nonneg u)
          rw [hlog]
  have hlog_abs :
      |Real.log ‖∏ᶠ u : ℂ, (0 - u) ^ (d u)‖| ≤ (∑ u ∈ S, ((d u : ℤ) : ℝ)) * B := by
    rw [hlog_all]
    calc
      |∑ u ∈ S, ((d u : ℤ) : ℝ) * Real.log ‖(0 : ℂ) - u‖|
          ≤ ∑ u ∈ S, |((d u : ℤ) : ℝ) * Real.log ‖(0 : ℂ) - u‖| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ u ∈ S, ((d u : ℤ) : ℝ) * |Real.log ‖(0 : ℂ) - u‖| := by
          apply Finset.sum_congr rfl
          intro u hu
          have hdn : 0 ≤ ((d u : ℤ) : ℝ) := by exact_mod_cast (hd_nonneg u)
          rw [abs_mul, abs_of_nonneg hdn]
      _ ≤ ∑ u ∈ S, ((d u : ℤ) : ℝ) * B := by
          refine Finset.sum_le_sum (fun u hu => ?_)
          have hb := hlog_per u hu
          have hdn : 0 ≤ ((d u : ℤ) : ℝ) := by exact_mod_cast (hd_nonneg u)
          exact mul_le_mul_of_nonneg_left (abs_le.mpr hb) hdn
      _ = (∑ u ∈ S, ((d u : ℤ) : ℝ)) * B := by rw [Finset.sum_mul]
  have hfin_eq : (∑ᶠ u : ℂ, ((d u : ℤ) : ℝ)) = ∑ u ∈ S, ((d u : ℤ) : ℝ) := by
    refine finsum_eq_sum_of_support_subset (fun u : ℂ => ((d u : ℤ) : ℝ)) ?_
    intro u hu
    rw [Function.mem_support] at hu
    have hdne : d u ≠ 0 := by
      intro hd0
      exact hu (by simp [hd0])
    exact (hmemS u).mpr hdne
  have hZ : xiZ  T = ∑ᶠ u : ℂ, ((d u : ℤ) : ℝ) := by
    dsimp [xiZ, d, Λc]
  calc
    |Real.log ‖xiP  T 0‖| = |Real.log ‖∏ᶠ u : ℂ, (0 - u) ^ (d u)‖| := by
        dsimp [xiP, d, Λc]
    _ ≤ (∑ᶠ u : ℂ, ((d u : ℤ) : ℝ)) * B := by
        rw [hfin_eq]
        exact hlog_abs
    _ = (xiZ  T) * (Real.log T + |Real.log δ₀|) := by
        rw [hZ]

/-! ## Constants witnessing growth / zero-count / zero-separation -/

/-- growth constant (nonneg) for |Λ| on circles. -/
noncomputable def xi_gc   
     : ℝ :=
  max ((xiF_growth ).choose) 0

/-- zero-count constant (nonneg). -/
noncomputable def xi_zc   
     : ℝ :=
  max ((xiF_zeroCount ).choose) 0

/-- lower bound for |zeros|. -/
noncomputable def xi_delta   
     : ℝ :=
  (xiF_zeros_ge_delta ).choose

lemma xi_gc_nonneg   
     : 0 ≤ xi_gc  := by
  dsimp [xi_gc]
  exact le_max_right _ 0

lemma xi_zc_nonneg   
     : 0 ≤ xi_zc  := by
  dsimp [xi_zc]
  exact le_max_right _ 0

lemma xi_delta_spec   
     :
    0 < xi_delta  ∧ xi_delta  ≤ 1 ∧
      ∀ u : ℂ, xiF u = 0 →
        xi_delta  ≤ ‖u‖ := by
  exact (xiF_zeros_ge_delta ).choose_spec

lemma xi_gc_spec   
     : ∀ R : ℝ, 2 ≤ R → ∀ z : ℂ, ‖z‖ = R →
      ‖xiF z‖ ≤
        rexp (xi_gc  * R * xiL R) := by
  intro R hR z hz
  let c : ℝ := (xiF_growth ).choose
  have hc : ‖xiF z‖ ≤
      rexp (c * R * (xiL R)) := by
    simpa using ((xiF_growth ).choose_spec R hR z hz)
  have hle : c * R * xiL R ≤ xi_gc  * R * xiL R := by
    have hR0 : 0 ≤ R := by linarith
    have hL : 0 ≤ xiL R := le_of_lt (xiL_pos  hR0)
    dsimp [xi_gc]
    have hcm : c ≤ max c 0 := le_max_left c 0
    calc
      c * R * xiL R = (c * R) * xiL R := by ring
      _ ≤ (max c 0 * R) * xiL R := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcm hR0) hL
  refine le_trans hc ?_
  rw [Real.exp_le_exp]
  have hlog : xiL R = xiL R := by
    rfl
  rw [hlog]
  exact hle

lemma xi_zc_spec   
     : ∀ R : ℝ, 2 ≤ R →
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (xiF)
          (closedBall (0 : ℂ) R)) u : ℤ) : ℝ)) ≤
        xi_zc  * R * xiL R := by
  intro R hR
  let c : ℝ := (xiF_zeroCount ).choose
  have hc : (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (xiF)
          (closedBall (0 : ℂ) R)) u : ℤ) : ℝ)) ≤
      c * R * (xiL R) := by
    simpa using ((xiF_zeroCount ).choose_spec R hR)
  have hle : c * R * xiL R ≤ xi_zc  * R * xiL R := by
    have hR0 : 0 ≤ R := by linarith
    have hL : 0 ≤ xiL R := le_of_lt (xiL_pos  hR0)
    dsimp [xi_zc]
    have hcm : c ≤ max c 0 := le_max_left c 0
    calc
      c * R * xiL R = (c * R) * xiL R := by ring
      _ ≤ (max c 0 * R) * xiL R := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcm hR0) hL
  have hlog : xiL R = xiL R := by
    rfl
  calc
    (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (xiF)
        (closedBall (0 : ℂ) R)) u : ℤ) : ℝ)) ≤ c * R * (xiL R) := hc
    _ = c * R * xiL R := by rw [hlog]
    _ ≤ xi_zc  * R * xiL R := hle

/-- The log-cofactor scale `M0` at a good radius. -/
noncomputable def xi_M0   
     (A T : ℝ) : ℝ :=
  xi_gc  * T * xiL T
  + 2 * Real.log (xiL A) * xi_zc  * T * xiL T
  + |Real.log ‖xiF 0‖|
  + xi_zc  * T * xiL T * (Real.log T + |Real.log (xi_delta )|)
  + 1

lemma xi_M0_nonneg   
     {A T : ℝ} (hA : 0 ≤ A) (hT1 : 1 ≤ T) :
    0 ≤ xi_M0  A T := by
  have hgc : 0 ≤ xi_gc  := xi_gc_nonneg 
  have hzc : 0 ≤ xi_zc  := xi_zc_nonneg 
  have hT0 : 0 ≤ T := by linarith
  have hLT : 0 ≤ xiL T := le_of_lt (xiL_pos  hT0)
  have hLA : 0 ≤ xiL A := le_of_lt (xiL_pos  hA)
  have hlogLA : 0 ≤ Real.log (xiL A) := by
    have hLA1 : 1 ≤ xiL A := by linarith [xiL_ge_two  hA]
    exact Real.log_nonneg hLA1
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT1
  have h1 : 0 ≤ xi_gc  * T * xiL T := by positivity
  have h2 : 0 ≤ 2 * Real.log (xiL A) * xi_zc  * T * xiL T := by positivity
  have h3 : 0 ≤ |Real.log ‖xiF 0‖| := abs_nonneg _
  have h4 : 0 ≤ xi_zc  * T * xiL T * (Real.log T + |Real.log (xi_delta )|) := by
    have hb : 0 ≤ Real.log T + |Real.log (xi_delta )| := by positivity
    positivity
  dsimp [xi_M0]
  nlinarith

/-- Cofactor bound at a good radius: factorization of `Λ` on `ball 0 (T+ε)` with
`log‖g‖ ≤ M0` on `ball 0 T` and `|log‖g 0‖| ≤ M0`, where `M0 = xi_M0  A T`. -/
lemma xi_cofactor_bound   
     {A T : ℝ} (hA : 0 ≤ A) (hTpos : 0 < T) (hT2 : 2 ≤ T)
    (hmargin : ∀ u : ℂ, xiF u = 0 →
      (xiL A) ^ 2 * |‖u‖ - T| ≥ 1) :
    ∃ (g : ℂ → ℂ) (ε : ℝ), 0 < ε ∧
      AnalyticOnNhd ℂ g (ball 0 (T + ε)) ∧
      (∀ w : ℂ, w ∈ ball 0 (T + ε) → g w ≠ 0) ∧
      (∀ z : ℂ, z ∈ ball 0 (T + ε) →
        xiF z =
          xiP  T z * g z) ∧
      (∀ w : ℂ, w ∈ ball 0 T → Real.log ‖g w‖ ≤ xi_M0  A T) ∧
      |Real.log ‖g 0‖| ≤ xi_M0  A T := by
  classical
  let Λc : ℂ → ℂ := xiF
  let gc : ℝ := xi_gc 
  let zc : ℝ := xi_zc 
  let δ₀ : ℝ := xi_delta 
  let LT : ℝ := xiL T
  let LA : ℝ := xiL A
  let Q1 : ℝ := gc * T * LT
  let Q2 : ℝ := (2 * Real.log LA) * (zc * T * LT)
  let Q3 : ℝ := |Real.log ‖Λc 0‖|
  let Q4 : ℝ := zc * T * LT * (Real.log T + |Real.log δ₀|)
  let M0 : ℝ := Q1 + Q2 + Q3 + Q4 + 1
  have hΛ0 : Λc 0 ≠ 0 := by simpa [Λc] using xiF_zero_ne
  have hΛdiff : Differentiable ℂ Λc := by simpa [Λc] using xiF_diff
  have hLApos : 0 < LA := xiL_pos  hA
  have hLTpos : 0 < LT := xiL_pos  (le_of_lt hTpos)
  have hcirc : ∀ u : ℂ, ‖u‖ = T → Λc u ≠ 0 := by
    intro u hu hzu
    have hmm := hmargin u (by simpa [Λc] using hzu)
    have hL2 : 0 < (xiL A) ^ 2 := by positivity
    have hzero : |‖u‖ - T| = 0 := by simp [hu]
    have hb : (1 : ℝ) ≤ 0 := by simpa [hzero, mul_zero] using hmm
    linarith
  rcases factorization_open (f := Λc) (R := T) hTpos hΛdiff hΛ0 hcirc with ⟨g, ε, hε, hg_an, hg_nz, hfac⟩
  have hg_nz_T : ∀ w : ℂ, w ∈ ball 0 T → g w ≠ 0 := by
    intro w hw
    have hwε : w ∈ ball 0 (T + ε) := by
      rw [mem_ball_zero_iff] at hw ⊢
      nlinarith [hε]
    exact hg_nz w hwε
  have hM0_eq : M0 = xi_M0  A T := by
    dsimp [M0, Q1, Q2, Q3, Q4, gc, zc, δ₀, LT, LA, Λc, xi_M0]
    ring
  have hQ3 : 0 ≤ Q3 := by dsimp [Q3]; exact abs_nonneg _
  have hQ4 : 0 ≤ Q4 := by
    dsimp [Q4]
    have hlogT0 : 0 ≤ Real.log T := Real.log_nonneg (by linarith : (1 : ℝ) ≤ T)
    have hzc0 : 0 ≤ zc := xi_zc_nonneg 
    positivity
  have hQ1 : 0 ≤ Q1 := by
    have hgc0 : 0 ≤ gc := by dsimp [gc]; exact xi_gc_nonneg 
    have hT0 : 0 ≤ T := le_of_lt hTpos
    dsimp [Q1]
    positivity
  have hQ2 : 0 ≤ Q2 := by
    have hzc0 : 0 ≤ zc := by dsimp [zc]; exact xi_zc_nonneg 
    have hlogLA0 : 0 ≤ Real.log (xiL A) := by
      have hA1 : 1 ≤ xiL A := by linarith [xiL_ge_two  hA]
      exact Real.log_nonneg hA1
    dsimp [Q2, zc, LA]
    positivity
  have hQ1Q2_le_M0 : Q1 + Q2 ≤ M0 := by
    dsimp [M0]
    nlinarith [hQ3, hQ4]
  have hQ34_le_M0 : Q3 + Q4 ≤ M0 := by
    dsimp [M0]
    nlinarith [hQ1, hQ2]
  -- boundary bound on the sphere
  have hbnd_ζ : ∀ ζ : ℂ, ‖ζ‖ = T → Real.log ‖g ζ‖ ≤ Q1 + Q2 := by
    intro ζ hζ
    have hζε : ζ ∈ ball 0 (T + ε) := by
      rw [mem_ball_zero_iff]
      nlinarith [hζ, hε]
    have hΛζ : Λc ζ ≠ 0 := hcirc ζ hζ
    have hPζ : xiP  T ζ ≠ 0 := xiF_P_ne_zero_circle  hTpos (by intro u hu; simpa [Λc] using hcirc u hu) (hζ := hζ)
    have hgζ : g ζ ≠ 0 := hg_nz ζ hζε
    have hfacζ := hfac ζ hζε
    have hlog_mul : Real.log ‖Λc ζ‖ = Real.log ‖xiP  T ζ‖ + Real.log ‖g ζ‖ := by
      have h1 : ‖Λc ζ‖ = ‖xiP  T ζ * g ζ‖ := by
        rw [hfacζ]
        congr 1
      rw [h1]
      exact pf_log_eq_of_mul hPζ hgζ
    have hlogΛ : Real.log ‖Λc ζ‖ ≤ gc * T * LT := by
      have hb := xiF_Log_bound  (T := T) (hT2 := hT2) (gc := gc)
        (by
          intro R' hR' z' hz'
          exact xi_gc_spec  R' hR' z' hz')
        (hζ := hζ) (hζnz := by simpa [Λc] using hΛζ)
      simpa [gc, LT, Λc] using hb
    have hfaclow : -Real.log ‖xiP  T ζ‖ ≤ (2 * Real.log LA) * xiZ  T := by
      have hb := xiF_fac_log_lower   (A := A) (T := T) hA hTpos
        (by intro u hu; simpa [Λc] using (hmargin u hu)) (hζ := hζ)
      simpa [xiP, xiZ, LA, Λc] using hb
    have hZle : xiZ  T ≤ zc * T * LT := by
      have hb := xi_zc_spec  T hT2
      simpa [xiZ, zc, LT, Λc] using hb
    have hmain : Real.log ‖g ζ‖ ≤ gc * T * LT + (2 * Real.log LA) * xiZ  T := by
      have hstep : Real.log ‖g ζ‖ = Real.log ‖Λc ζ‖ - Real.log ‖xiP  T ζ‖ := by
        rw [hlog_mul]
        ring
      rw [hstep]
      have h1 : Real.log ‖Λc ζ‖ ≤ gc * T * LT := hlogΛ
      have h2 : -Real.log ‖xiP  T ζ‖ ≤ (2 * Real.log LA) * xiZ  T := hfaclow
      linarith
    have hstep2 : gc * T * LT + (2 * Real.log LA) * xiZ  T ≤ Q1 + Q2 := by
      dsimp [Q1, Q2]
      have hz0 : 0 ≤ 2 * Real.log LA := by
        have hLA1 : 1 ≤ LA := by dsimp [LA]; linarith [xiL_ge_two  hA]
        have hlog : 0 ≤ Real.log LA := Real.log_nonneg hLA1
        positivity
      nlinarith
    exact le_trans hmain hstep2
  -- ball bound via maximum modulus on the frontier
  have hbnd_ball : ∀ w : ℂ, w ∈ ball 0 T → Real.log ‖g w‖ ≤ M0 := by
    intro w hw
    have hcl : DifferentiableOn ℂ g (closedBall 0 T) := by
      intro x hx
      have hxε : x ∈ ball 0 (T + ε) := by
        rw [mem_ball_zero_iff]
        have hxT : ‖x‖ ≤ T := by simpa [Metric.mem_closedBall, dist_eq_norm] using hx
        nlinarith [hε]
      exact (hg_an.differentiableOn.differentiableAt (isOpen_ball.mem_nhds hxε)).differentiableWithinAt
    have hdiffCl : DiffContOnCl ℂ g (ball 0 T) := by
      refine DifferentiableOn.diffContOnCl ?_
      simpa [closure_ball (0 : ℂ) (ne_of_gt hTpos)] using hcl
    have hfront : ∀ ζ : ℂ, ζ ∈ frontier (ball 0 T) → ‖g ζ‖ ≤ rexp M0 := by
      intro ζ hζf
      rw [frontier_ball (0 : ℂ) (ne_of_gt hTpos), Metric.mem_sphere, dist_eq_norm] at hζf
      have hζ : ‖ζ‖ = T := by simpa using hζf
      have hb := hbnd_ζ ζ hζ
      have hleM : Real.log ‖g ζ‖ ≤ M0 := le_trans hb hQ1Q2_le_M0
      have hgζnz : g ζ ≠ 0 := by
        have hζε : ζ ∈ ball 0 (T + ε) := by rw [mem_ball_zero_iff]; nlinarith [hζ, hε]
        exact hg_nz ζ hζε
      have hnormpos : 0 < ‖g ζ‖ := norm_pos_iff.mpr hgζnz
      calc
        ‖g ζ‖ = rexp (Real.log ‖g ζ‖) := by rw [Real.exp_log hnormpos]
        _ ≤ rexp M0 := Real.exp_le_exp.mpr hleM
    have hwT : ‖w‖ < T := by simpa [mem_ball_zero_iff] using hw
    have hwcl : w ∈ closure (ball 0 T) := by
      rw [closure_ball (0 : ℂ) (ne_of_gt hTpos), Metric.mem_closedBall, dist_eq_norm]
      simpa using hwT.le
    have hnorm : ‖g w‖ ≤ rexp M0 := Complex.norm_le_of_forall_mem_frontier_norm_le
      Metric.isBounded_ball hdiffCl hfront hwcl
    have hgwpos : 0 < ‖g w‖ := norm_pos_iff.mpr (hg_nz_T w hw)
    have hlogle : Real.log ‖g w‖ ≤ Real.log (rexp M0) := Real.log_le_log hgwpos hnorm
    rwa [Real.log_exp] at hlogle
  -- origin bound
  have h0ε : (0 : ℂ) ∈ ball 0 (T + ε) := by
    rw [mem_ball_zero_iff]
    simp
    positivity
  have hfac0 := hfac 0 h0ε
  have hP0nz : xiP  T 0 ≠ 0 := by
    have hmul0 : xiP  T 0 * g 0 ≠ 0 := by
      change ¬((∏ᶠ u : ℂ, (0 - u) ^ (divisor Λc (closedBall (0 : ℂ) T)) u) * g 0 = 0)
      rw [← hfac0]
      exact hΛ0
    exact (mul_ne_zero_iff.mp hmul0).1
  have hg0nz : g 0 ≠ 0 := hg_nz 0 h0ε
  have hlog_mul0 : Real.log ‖Λc 0‖ = Real.log ‖xiP  T 0‖ + Real.log ‖g 0‖ := by
    have h1 : ‖Λc 0‖ = ‖xiP  T 0 * g 0‖ := by
      rw [hfac0]
      congr 1
    rw [h1]
    exact pf_log_eq_of_mul hP0nz hg0nz
  have hP0_bound : |Real.log ‖xiP  T 0‖| ≤ (xiZ  T) * (Real.log T + |Real.log δ₀|) := by
    have hδspec := xi_delta_spec 
    exact xiF_P0_log_bound  (hT := by linarith) δ₀ hδspec.1 (by intro u hu; simpa [δ₀, Λc] using (hδspec.2.2 u hu))
  have hlogg0 : |Real.log ‖g 0‖| ≤ Q3 + Q4 := by
    have hrew : Real.log ‖g 0‖ = Real.log ‖Λc 0‖ - Real.log ‖xiP  T 0‖ := by
      rw [hlog_mul0]
      ring
    have h1 : |Real.log ‖Λc 0‖ - Real.log ‖xiP  T 0‖| ≤ Q3 + zc * T * LT * (Real.log T + |Real.log δ₀|) := by
      have hA1 : |Real.log ‖Λc 0‖ - Real.log ‖xiP  T 0‖| ≤
          |Real.log ‖Λc 0‖| + |Real.log ‖xiP  T 0‖| := by
        simpa [sub_eq_add_neg, abs_neg] using (abs_add_le (Real.log ‖Λc 0‖) (-Real.log ‖xiP  T 0‖))
      have hZle : xiZ  T ≤ zc * T * LT := by
        have hb := xi_zc_spec  T hT2
        simpa [xiZ, zc, LT, Λc] using hb
      have hb1 : |Real.log ‖xiP  T 0‖| ≤ zc * T * LT * (Real.log T + |Real.log δ₀|) := by
        have hb0 : (xiZ  T) * (Real.log T + |Real.log δ₀|) ≤
            (zc * T * LT) * (Real.log T + |Real.log δ₀|) := by
          have hnon : 0 ≤ Real.log T + |Real.log δ₀| := by
            have hlogT0 : 0 ≤ Real.log T := Real.log_nonneg (by linarith : (1 : ℝ) ≤ T)
            positivity
          exact mul_le_mul_of_nonneg_right hZle hnon
        exact le_trans hP0_bound hb0
      dsimp [Q3]
      linarith
    have hrew2 : Q3 + zc * T * LT * (Real.log T + |Real.log δ₀|) = Q3 + Q4 := by
      rfl
    rw [hrew]
    rw [hrew2]
    exact h1
  have horigin : |Real.log ‖g 0‖| ≤ M0 := by
    exact le_trans hlogg0 hQ34_le_M0
  refine ⟨g, ε, hε, hg_an, hg_nz, hfac, ?_, ?_⟩
  · intro w hw
    exact le_trans (hbnd_ball w hw) (le_of_eq hM0_eq)
  · exact le_trans horigin (le_of_eq hM0_eq)

/-- `log T ≤ 1 + log-scale(A)` when `1 ≤ A`, `A ≤ T`, `T ≤ 2A`. -/
lemma xi_logT_le  {A T : ℝ} (hA1 : 1 ≤ A) (hT2A : T ≤ 2 * A) (hAT : A ≤ T) :
    Real.log T ≤ 1 + xiL A := by
  have hApos : 0 < A := by linarith
  have hTpos : 0 < T := by linarith
  have h1 : Real.log T ≤ Real.log (2 * A) := by
    apply Real.log_le_log hTpos
    exact hT2A
  have h2 : Real.log (2 * A) ≤ 1 + Real.log A := by
    calc
      Real.log (2 * A) = Real.log 2 + Real.log A := by
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hApos)]
      _ ≤ 1 + Real.log A := by
        have hlog2 : Real.log 2 ≤ 1 := by
          have h := Real.log_le_sub_one_of_pos (x := (2 : ℝ)) (by norm_num : (0 : ℝ) < 2)
          linarith
        linarith
  have h3 : Real.log A ≤ Real.log (A + 2) := by
    apply Real.log_le_log (by linarith : 0 < A)
    linarith
  have h4 : Real.log (A + 2) ≤ xiL A := by
    dsimp [xiL]
    linarith
  linarith

/-- `T·log-scale(T) ≤ 4·A·log-scale(A)` when `1 ≤ A ≤ T ≤ 2A`. -/
lemma xi_mul_bound  {A T : ℝ} (hA1 : 1 ≤ A) (hAT : A ≤ T) (hT2A : T ≤ 2 * A) :
    T * xiL T ≤ 4 * A * xiL A := by
  have hT0 : 0 ≤ T := by linarith
  have h2A0 : 0 ≤ 2 * A := by nlinarith
  have hLT0 : 0 ≤ xiL T := le_of_lt (xiL_pos  hT0)
  have hLTle : xiL T ≤ xiL (2 * A) := xiL_mono  hT0 hT2A
  have hLTle2 : xiL T ≤ 2 * xiL A := by
    calc
      xiL T ≤ xiL (2 * A) := hLTle
      _ ≤ 2 * xiL A := xiL_two_mul_le  hA1
  calc
    T * xiL T ≤ (2 * A) * xiL T := mul_le_mul_of_nonneg_right hT2A hLT0
    _ ≤ (2 * A) * (2 * xiL A) := mul_le_mul_of_nonneg_left hLTle2 h2A0
    _ = 4 * A * xiL A := by ring

/-- Coefficient `C0` in the `M0` upper bound. -/
noncomputable def xi_C0   
     : ℝ :=
  4 * xi_gc  + 8 * xi_zc  +
    4 * xi_zc  * (2 + |Real.log (xi_delta )|)

/-- Coefficient `C1` in the `M0` upper bound. -/
noncomputable def xi_C1   
     : ℝ :=
  |Real.log ‖xiF 0‖| + 2

/-- `M0(A,T) ≤ C0·A·(log-scale A)² + C1` for `1 ≤ A ≤ T ≤ 2A`. -/
lemma xi_M0_le   
     {A T : ℝ} (hA1 : 1 ≤ A) (hAT : A ≤ T) (hT2A : T ≤ 2 * A) :
    xi_M0  A T ≤ xi_C0  * A * (xiL A) ^ 2 + xi_C1  := by
  classical
  let gc : ℝ := xi_gc 
  let zc : ℝ := xi_zc 
  let del : ℝ := xi_delta 
  let LA : ℝ := xiL A
  have hA0 : 0 ≤ A := by linarith
  have hT0 : 0 ≤ T := by linarith
  have hLA0 : 0 ≤ LA := le_of_lt (xiL_pos  hA0)
  have hLA1 : 1 ≤ LA := by dsimp [LA]; linarith [xiL_ge_two  hA0]
  have hgc0 : 0 ≤ gc := by dsimp [gc]; exact xi_gc_nonneg 
  have hzc0 : 0 ≤ zc := by dsimp [zc]; exact xi_zc_nonneg 
  have hlogLA0 : 0 ≤ Real.log (xiL A) := Real.log_nonneg (by linarith : 1 ≤ xiL A)
  have hlogT0 : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hLT0 : 0 ≤ xiL T := le_of_lt (xiL_pos  hT0)
  have hlogLAle : Real.log (xiL A) ≤ LA := by
    dsimp [LA]
    exact xiL_log_le  hA0
  have hLT2 : xiL T ≤ 2 * LA := by
    dsimp [LA]
    have hm := xiL_mono  hT0 hT2A
    have h2 := xiL_two_mul_le  hA1
    calc
      xiL T ≤ xiL (2 * A) := hm
      _ ≤ 2 * xiL A := h2
  have hTL4 : T * xiL T ≤ 4 * A * LA := by
    dsimp [LA]
    exact xi_mul_bound  hA1 hAT hT2A
  have hlogTle : Real.log T ≤ 1 + LA := by
    dsimp [LA]
    exact xi_logT_le  hA1 hT2A hAT
  have hlogd : |Real.log del| ≤ |Real.log del| * LA := by
    have h : 1 ≤ LA := hLA1
    rw [mul_comm]
    exact le_mul_of_one_le_left (abs_nonneg _) h
  have hLTleLA2 : Real.log T + |Real.log del| ≤ LA * (2 + |Real.log del|) := by
    nlinarith [hlogTle, hlogd]
  -- term bounds
  have hterm1 : gc * T * xiL T ≤ 4 * gc * A * LA ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left hTL4 hgc0   -- gc·(T·LT) ≤ gc·(4·A·LA)
    have h2 : gc * (4 * A * LA) ≤ gc * (4 * A * LA) * LA := by
      have h4gcA0 : 0 ≤ gc * (4 * A * LA) := by positivity
      exact le_mul_of_one_le_right h4gcA0 hLA1
    dsimp [LA] at h2
    nlinarith [h1, h2]
  have hterm2 : 2 * Real.log (xiL A) * zc * T * xiL T ≤ 8 * zc * A * (xiL A) ^ 2 := by
    have hzcT : zc * (T * xiL T) ≤ zc * (4 * A * LA) := mul_le_mul_of_nonneg_left hTL4 hzc0
    have hlog2 : (2 * Real.log (xiL A)) ≤ (2 * LA) := by nlinarith [hlogLAle]
    have hpart : (2 * LA) * (zc * (4 * A * LA)) ≤ 8 * zc * A * LA ^ 2 := by
      have h1 : 0 ≤ 2 * LA := by positivity
      have h2 : 0 ≤ zc * (4 * A * LA) := by positivity
      nlinarith
    have hzcT0 : 0 ≤ zc * (T * xiL T) := by positivity
    have h2LA0 : 0 ≤ 2 * LA := by positivity
    have hprod : (2 * Real.log (xiL A)) * (zc * (T * xiL T)) ≤ (2 * LA) * (zc * (4 * A * LA)) :=
      mul_le_mul hlog2 hzcT hzcT0 h2LA0
    dsimp [LA] at hpart
    nlinarith [hprod, hpart]
  have hterm4 : zc * T * xiL T * (Real.log T + |Real.log del|)
      ≤ 4 * zc * (2 + |Real.log del|) * A * (xiL A) ^ 2 := by
    have hzcT : zc * (T * xiL T) ≤ zc * (4 * A * LA) := mul_le_mul_of_nonneg_left hTL4 hzc0
    have hx0 : 0 ≤ Real.log T + |Real.log del| := by positivity
    have hX : Real.log T + |Real.log del| ≤ LA * (2 + |Real.log del|) := hLTleLA2
    have hzX0 : 0 ≤ LA * (2 + |Real.log del|) := by positivity
    have h1 : (zc * (T * xiL T)) * (Real.log T + |Real.log del|) ≤
        (zc * (4 * A * LA)) * (LA * (2 + |Real.log del|)) :=
        mul_le_mul hzcT hX hx0 (by positivity : 0 ≤ zc * (4 * A * LA))
    have h2 : (zc * (4 * A * LA)) * (LA * (2 + |Real.log del|)) ≤
        4 * zc * (2 + |Real.log del|) * A * (xiL A) ^ 2 := by
      have heq : (zc * (4 * A * LA)) * (LA * (2 + |Real.log del|)) =
          4 * zc * (2 + |Real.log del|) * A * LA ^ 2 := by ring
      have hLA0' : 0 ≤ LA ^ 2 := by positivity
      have hzc0' : 0 ≤ zc := hzc0
      have hd0 : 0 ≤ 2 + |Real.log del| := by positivity
      have hA0' : 0 ≤ A := hA0
      rw [heq]
    dsimp [LA] at h2
    nlinarith [h1, h2]
  have hq3 : |Real.log ‖xiF 0‖| ≤
      |Real.log ‖xiF 0‖| := le_rfl
  calc
    xi_M0  A T
        = xi_gc  * T * xiL T
            + 2 * Real.log (xiL A) * xi_zc  * T * xiL T
            + |Real.log ‖xiF 0‖|
            + xi_zc  * T * xiL T * (Real.log T + |Real.log (xi_delta )|)
            + 1 := by
            dsimp [xi_M0]
    _ ≤ 4 * gc * A * LA ^ 2 + 8 * zc * A * LA ^ 2
            + |Real.log ‖xiF 0‖|
            + 4 * zc * (2 + |Real.log del|) * A * LA ^ 2 + 1 := by
            nlinarith [hterm1, hterm2, hterm4]
    _ ≤ xi_C0  * A * (xiL A) ^ 2 + xi_C1  := by
            dsimp [xi_C0, xi_C1, gc, zc, del]
            nlinarith
/-! ### Divisor/zero-set bookkeeping for `xiF` (generic copy of the L-function lemmas) -/

lemma xiF_zeroCoeff_ge_one {B : ℝ} {z : ℂ} (hzB : ‖z‖ ≤ B)
    (hz0 : xiF z = 0) :
    (1 : ℤ) ≤ (MeromorphicOn.divisor xiF (Metric.closedBall (0 : ℂ) B)) z := by
  have hΛne : xiF ≠ 0 := by
    intro h
    exact xiF_zero_ne (congrFun h 0)
  have hzK : z ∈ closedBall (0 : ℂ) B := by simpa [Metric.mem_closedBall, dist_eq_norm] using hzB
  have hnz : MeromorphicOn.divisor xiF (closedBall (0 : ℂ) B) z ≠ 0 :=
    Commons.NumberTheory.Linnik.divisor_ne_zero_of_apply_eq_zero xiF_diff hΛne hzK hz0
  have hnn : (0 : ℤ) ≤ MeromorphicOn.divisor xiF (closedBall (0 : ℂ) B) z := by
    exact (MeromorphicOn.AnalyticOnNhd.divisor_nonneg (f := xiF) (U := closedBall (0 : ℂ) B) (xiF_an _)) z
  omega

lemma xiF_zeroSet_subset_divisorSupport {B : ℝ} :
    ({u : ℂ | xiF u = 0 ∧ ‖u‖ ≤ B} : Set ℂ) ⊆
      Function.support (fun u : ℂ =>
        MeromorphicOn.divisor xiF (Metric.closedBall (0 : ℂ) B) u) := by
  intro z hz
  rw [Function.mem_support]
  have hΛne : xiF ≠ 0 := by
    intro h
    exact xiF_zero_ne (congrFun h 0)
  have hzK : z ∈ closedBall (0 : ℂ) B := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hz.2
  exact Commons.NumberTheory.Linnik.divisor_ne_zero_of_apply_eq_zero xiF_diff hΛne hzK hz.1

lemma xiF_zeroSet_finite {B : ℝ} (hB : 0 ≤ B) :
    ({u : ℂ | xiF u = 0 ∧ ‖u‖ ≤ B} : Set ℂ).Finite := by
  have hsup : (Function.support fun u : ℂ => MeromorphicOn.divisor xiF (closedBall (0 : ℂ) B) u).Finite := by
    simpa using (MeromorphicOn.divisor_support_finite_of_subset (f := xiF) (U := closedBall (0 : ℂ) B)
      (V := closedBall (0 : ℂ) B) (xiF_an _).meromorphicOn (isCompact_closedBall (0 : ℂ) B)
        (by intro z hz; exact hz))
  exact hsup.subset xiF_zeroSet_subset_divisorSupport

lemma xiF_zeroCard_le_divisorFinsum {B : ℝ} (hB : 0 ≤ B) :
    let Z : Set ℂ := {u : ℂ | xiF u = 0 ∧ ‖u‖ ≤ B}
    ∀ hZ : Z.Finite,
      ((hZ.toFinset.card : ℝ) ≤
        ∑ᶠ u : ℂ, (((MeromorphicOn.divisor xiF (Metric.closedBall (0 : ℂ) B)) u : ℤ) : ℝ)) := by
  intro Z hZ
  let coeff : ℂ → ℤ := fun u => MeromorphicOn.divisor xiF (closedBall (0 : ℂ) B) u
  have hcoeff_nonneg (u : ℂ) : (0 : ℤ) ≤ coeff u := by
    exact (MeromorphicOn.AnalyticOnNhd.divisor_nonneg (f := xiF) (U := closedBall (0 : ℂ) B) (xiF_an _)) u
  have hsupFin : (Function.support coeff).Finite := by
    simpa [coeff] using (MeromorphicOn.divisor_support_finite_of_subset (f := xiF)
      (U := closedBall (0 : ℂ) B) (V := closedBall (0 : ℂ) B) (xiF_an _).meromorphicOn
        (isCompact_closedBall (0 : ℂ) B) (by intro z hz; exact hz))
  let Zfin : Finset ℂ := hZ.toFinset
  let supp : Finset ℂ := hsupFin.toFinset
  have hmem_Zfin (z : ℂ) : z ∈ Zfin ↔ z ∈ Z := by
    dsimp [Zfin]
    exact hZ.mem_toFinset
  have hmem_supp (z : ℂ) : z ∈ supp ↔ z ∈ Function.support coeff := by
    dsimp [supp]
    exact hsupFin.mem_toFinset
  have hZsub_supp : Zfin ⊆ supp := by
    intro z hz
    rw [hmem_supp]
    have hzZ : z ∈ Z := (hmem_Zfin z).1 hz
    have hmem : z ∈ Function.support coeff := by
      rw [Function.mem_support]
      dsimp [coeff]
      have hge : (1 : ℤ) ≤ (MeromorphicOn.divisor xiF (closedBall (0 : ℂ) B)) z :=
        xiF_zeroCoeff_ge_one (B := B) hzZ.2 hzZ.1
      exact ne_of_gt (lt_of_lt_of_le (by norm_num) hge)
    exact hmem
  have hsum_Zfin : (Zfin.card : ℝ) ≤ ∑ z ∈ Zfin, ((coeff z : ℤ) : ℝ) := by
    calc
      (Zfin.card : ℝ) = ∑ z ∈ Zfin, (1 : ℝ) := by
        exact_mod_cast (Finset.card_eq_sum_ones Zfin)
      _ ≤ ∑ z ∈ Zfin, ((coeff z : ℤ) : ℝ) := by
        refine Finset.sum_le_sum ?_
        intro z hz
        have hge : (1 : ℤ) ≤ coeff z := by
          have hzZ : z ∈ Z := (hmem_Zfin z).1 hz
          exact xiF_zeroCoeff_ge_one (B := B) hzZ.2 hzZ.1
        exact_mod_cast hge
  have hsum_le_supp : (∑ z ∈ Zfin, ((coeff z : ℤ) : ℝ)) ≤ ∑ z ∈ supp, ((coeff z : ℤ) : ℝ) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hZsub_supp ?_
    intro z hz _hznot
    exact_mod_cast hcoeff_nonneg z
  have hsupp_eq_finsum : (∑ z ∈ supp, ((coeff z : ℤ) : ℝ)) =
      ∑ᶠ u : ℂ, (((coeff u : ℤ) : ℝ)) := by
    refine (finsum_eq_finsetSum_of_support_subset (f := fun u : ℂ => ((coeff u : ℤ) : ℝ))
      (s := supp) ?_).symm
    intro u hu
    have huS : u ∈ Function.support coeff := by
      rw [Function.mem_support] at hu ⊢
      dsimp at hu
      exact_mod_cast hu
    exact (hmem_supp u).2 huS
  calc
    ((hZ.toFinset.card : ℝ)) = (Zfin.card : ℝ) := rfl
    _ ≤ ∑ z ∈ Zfin, ((coeff z : ℤ) : ℝ) := hsum_Zfin
    _ ≤ ∑ z ∈ supp, ((coeff z : ℤ) : ℝ) := hsum_le_supp
    _ = ∑ᶠ u : ℂ, (((coeff u : ℤ) : ℝ)) := hsupp_eq_finsum
    _ = ∑ᶠ u : ℂ, (((MeromorphicOn.divisor xiF (Metric.closedBall (0 : ℂ) B)) u : ℤ) : ℝ) := by
      simp [coeff]

/-! ### Good radius for `xiF` (adapted from `goodRadius_geometric`) -/

lemma xiF_goodRadius :
    ∃ A₀ : ℝ, 0 < A₀ ∧ ∀ A : ℝ, A₀ ≤ A → ∃ T : ℝ, A ≤ T ∧ T ≤ 2 * A ∧
      ∀ u : ℂ, xiF u = 0 →
          (Real.log (A + 2) + 2) ^ 2 * |‖u‖ - T| ≥ 1 := by
  classical
  rcases xiF_zeroCount with ⟨c0, hc0⟩
  let c : ℝ := max c0 1
  have hc0le : c0 ≤ c := le_max_left c0 1
  have hcge1 : (1 : ℝ) ≤ c := le_max_right c0 1
  have hcge0 : 0 ≤ c := by linarith
  have hc_bound : ∀ R : ℝ, 2 ≤ R →
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor xiF (Metric.closedBall (0 : ℂ) R)) u : ℤ) : ℝ)) ≤
        c * R * (Real.log (R + 2) + 2) := by
    intro R hR
    have hR0 : 0 ≤ R := by linarith
    have hℓR0 : 0 ≤ Real.log (R + 2) + 2 := by
      have h1 : 0 ≤ Real.log (R + 2) := by
        refine Real.log_nonneg ?_
        linarith
      linarith
    exact le_trans (hc0 R hR) (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc0le hR0) hℓR0)
  refine ⟨max 2 (Real.exp (12 * c + 10)), ?_, ?_⟩
  · have hpos2 : 0 < (2 : ℝ) := by norm_num
    exact lt_of_lt_of_le hpos2 (le_max_left _ _)
  · intro A hA₀le
    let L : ℝ := Real.log (A + 2) + 2
    let B : ℝ := 2 * A + 2
    have hA2 : 2 ≤ A := by
      have : (2 : ℝ) ≤ max 2 (Real.exp (12 * c + 10)) := le_max_left _ _
      exact le_trans this hA₀le
    have hApos : 0 < A := by linarith
    have hLbig : 12 * c + 1 ≤ L := by
      dsimp [L]
      have h1 : Real.log (Real.exp (12 * c + 10)) ≤ Real.log (A + 2) := by
        refine Real.log_le_log ?_ ?_
        · positivity
        · calc
            Real.exp (12 * c + 10) ≤ max 2 (Real.exp (12 * c + 10)) := le_max_right _ _
            _ ≤ A := hA₀le
            _ ≤ A + 2 := by linarith
      rw [Real.log_exp] at h1
      nlinarith
    have hLpos : 0 < L := by nlinarith
    have hL1 : 1 ≤ L := by nlinarith
    have hL2pos : 0 < L ^ 2 := sq_pos_of_pos hLpos
    have hB2 : 2 ≤ B := by dsimp [B]; nlinarith
    have hB0 : 0 ≤ B := by dsimp [B]; nlinarith
    have hB3 : B ≤ 3 * A := by dsimp [B]; nlinarith
    let Z : Set ℂ := {u : ℂ | xiF u = 0 ∧ ‖u‖ ≤ B}
    have hZfin : Z.Finite := by
      simpa [Z] using (xiF_zeroSet_finite (B := B) hB0)
    let Zfin : Finset ℂ := hZfin.toFinset
    let centres : Finset ℝ := Zfin.image (fun u : ℂ => ‖u‖)
    have hcentres_le : (centres.card : ℝ) ≤ (Zfin.card : ℝ) := by
      dsimp [centres]
      exact_mod_cast (Finset.card_image_le : (Zfin.image (fun u : ℂ => ‖u‖)).card ≤ Zfin.card)
    have hcardZ : (Zfin.card : ℝ) ≤
        ∑ᶠ u : ℂ, (((MeromorphicOn.divisor xiF (Metric.closedBall (0 : ℂ) B)) u : ℤ) : ℝ) := by
      simpa [Zfin, Z] using (xiF_zeroCard_le_divisorFinsum (B := B) hB0 hZfin)
    let ℓB : ℝ := Real.log (B + 2) + 2
    have hℓB0 : 0 ≤ ℓB := by
      dsimp [ℓB]
      have h1 : 0 ≤ Real.log (B + 2) := by
        refine Real.log_nonneg ?_
        dsimp [B]
        linarith
      linarith
    have hℓB2 : ℓB ≤ 2 * L := by
      dsimp [ℓB, L]
      have hlogB : Real.log (B + 2) ≤ Real.log (A + 2) + 1 := by
        have hEq : B + 2 = 2 * A + 4 := by dsimp [B]; ring
        rw [hEq]
        exact Commons.NumberTheory.Linnik.grg_log_two_mul_add_four hApos
      have hlogAp2 : 0 ≤ Real.log (A + 2) := by
        refine Real.log_nonneg ?_
        linarith
      nlinarith
    have hmainAux : (centres.card : ℝ) * 2 < A * L ^ 2 := by
      have h1 : (centres.card : ℝ) ≤ c * B * ℓB := by
        calc
          (centres.card : ℝ) ≤ (Zfin.card : ℝ) := hcentres_le
          _ ≤ ∑ᶠ u : ℂ, (((MeromorphicOn.divisor xiF (Metric.closedBall (0 : ℂ) B)) u : ℤ) : ℝ) := hcardZ
          _ ≤ c * B * ℓB := by
            simpa [ℓB] using hc_bound B hB2
      calc
        (centres.card : ℝ) * 2 ≤ c * B * ℓB * 2 := by
          exact mul_le_mul_of_nonneg_right h1 (by norm_num)
        _ ≤ c * (3 * A) * (2 * L) * 2 := by
          gcongr
        _ = 12 * c * A * L := by ring
        _ < A * L ^ 2 := by
          exact Commons.NumberTheory.Linnik.grg_poly_lt hcge0 hApos hLbig
    have hcard' : (centres.card : ℝ) * (2 / L ^ 2) < A := by
      rw [← mul_div_assoc]
      rw [div_lt_iff₀ hL2pos]
      simpa [mul_assoc] using hmainAux
    have hcard'' : (centres.card : ℝ) * (2 / L ^ 2) < 2 * A - A := by
      nlinarith [hcard']
    have hw : 0 < 2 / L ^ 2 := by
      exact div_pos (by norm_num) hL2pos
    have hab : A ≤ 2 * A := by linarith
    rcases Commons.NumberTheory.Linnik.grg_exists_good_point_of_small_measure hab hw centres hcard'' with
      ⟨T, hT1, hT2, hgood⟩
    have hw2 : (2 / L ^ 2) / 2 = (1 : ℝ) / L ^ 2 := by
      have hLne : L ≠ 0 := ne_of_gt hLpos
      field_simp [hLne]
    have hgood' : ∀ z ∈ centres, (1 : ℝ) / L ^ 2 ≤ |T - z| := by
      intro z hz
      rw [← hw2]
      exact hgood z hz
    refine ⟨T, hT1, hT2, ?_⟩
    intro u hu0
    have hdist : (1 : ℝ) / L ^ 2 ≤ |‖u‖ - T| := by
      by_cases huB : ‖u‖ ≤ B
      · have hmem : ‖u‖ ∈ centres := by
          dsimp [centres]
          refine Finset.mem_image.mpr ?_
          refine ⟨u, ?_, rfl⟩
          dsimp [Zfin]
          exact (hZfin.mem_toFinset).2 ⟨by simpa using hu0, huB⟩
        have hd := hgood' (‖u‖) hmem
        simpa [abs_sub_comm] using hd
      · have hBlt : B < ‖u‖ := lt_of_not_ge huB
        have hbig : (2 : ℝ) ≤ ‖u‖ - T := by
          have hBT : (2 : ℝ) ≤ B - T := by
            dsimp [B]
            nlinarith [hT2]
          have h1 : B - T < ‖u‖ - T := sub_lt_sub_right hBlt T
          linarith
        have hd2 : (1 : ℝ) / L ^ 2 ≤ 2 := by
          have hle1 : (1 : ℝ) / L ^ 2 ≤ 1 := Commons.NumberTheory.Linnik.grg_one_div_sq_le_one hL1
          linarith
        have hle : (1 : ℝ) / L ^ 2 ≤ ‖u‖ - T := le_trans hd2 hbig
        have hnn : 0 ≤ ‖u‖ - T := by linarith
        simpa [abs_of_nonneg hnn] using hle
    have hfin : L ^ 2 * |‖u‖ - T| ≥ 1 := by
      have h2 : 1 ≤ |‖u‖ - T| * L ^ 2 := (div_le_iff₀ hL2pos).mp hdist
      have h3 : (1 : ℝ) ≤ L ^ 2 * |‖u‖ - T| := by
        simpa [mul_comm] using h2
      linarith
    dsimp [L] at hfin ⊢
    exact hfin



/-! ### Tail bound for the `xiF` divisor sums (adapted from `partialFraction_tail`) -/

lemma xiF_partialFraction_tail :
    ∃ c : ℝ, ∀ s : ℂ, ∀ R R' : ℝ, 2 ≤ R → R ≤ R' → ‖s‖ ≤ R / 4 →
      ‖(∑ᶠ u : ℂ, (((MeromorphicOn.divisor xiF (Metric.closedBall 0 R')) u : ℤ) : ℂ) *
          (1 / (s - u) + 1 / u))
        - (∑ᶠ u : ℂ, (((MeromorphicOn.divisor xiF (Metric.closedBall 0 R)) u : ℤ) : ℂ) *
          (1 / (s - u) + 1 / u))‖ ≤
        c * ‖s‖ * (Real.log (R + 2) + 2) / R := by
  classical
  let Λ : ℂ → ℂ := xiF
  have hΛdiff : Differentiable ℂ Λ := by simpa [Λ] using xiF_diff
  have hΛan : ∀ U : Set ℂ, AnalyticOnNhd ℂ Λ U := by
    intro U z hz
    exact hΛdiff.analyticAt z
  have hΛmer : ∀ U : Set ℂ, MeromorphicOn Λ U := fun U => (hΛan U).meromorphicOn
  have hdiv_nonneg : ∀ U u, 0 ≤ (MeromorphicOn.divisor Λ U) u := by
    intro U u
    exact MeromorphicOn.AnalyticOnNhd.divisor_nonneg (hΛan U) u
  rcases xiF_zeroCount with ⟨zc, hzc⟩
  let C : ℝ := max zc 0
  have hC0 : 0 ≤ C := by dsimp [C]; exact le_max_right zc 0
  have hzcC : ∀ (ρ : ℝ), 2 ≤ ρ →
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor Λ (closedBall 0 ρ)) u : ℤ) : ℝ)) ≤
        C * ρ * (Real.log (ρ + 2) + 2) := by
    intro ρ hρ
    have h1 := hzc ρ hρ
    have hT0 : 0 ≤ Real.log (ρ + 2) + 2 := by
      have h1 : 0 ≤ Real.log (ρ + 2) := by exact Real.log_nonneg (by linarith)
      linarith
    have hρ0 : 0 ≤ ρ := by linarith
    have hzcC' : zc * ρ * (Real.log (ρ + 2) + 2) ≤
        C * ρ * (Real.log (ρ + 2) + 2) := by
      have hCge : zc ≤ C := by dsimp [C]; exact le_max_left zc 0
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCge hρ0) hT0
    exact le_trans h1 hzcC'
  refine ⟨128 * C, ?_⟩
  intro s R R' hR hRR' hs
  let w : ℂ → ℂ := fun u => 1 / (s - u) + 1 / u
  let m : ℝ → ℂ → ℤ := fun ρ u => MeromorphicOn.divisor Λ (closedBall 0 ρ) u
  let F : ℝ → ℂ := fun ρ => ∑ᶠ u : ℂ, (((m ρ u : ℤ) : ℂ) * w u)
  -- finite support finsets
  have hfin (ρ : ℝ) : (m ρ).support.Finite := by
    dsimp [m]
    exact (MeromorphicOn.divisor Λ (closedBall 0 ρ)).finiteSupport (isCompact_closedBall (0 : ℂ) ρ)
  let S : Finset ℂ := (hfin R').toFinset
  have hS_mem : ∀ u : ℂ, u ∈ S ↔ m R' u ≠ 0 := by
    intro u
    dsimp [S]
    rw [Set.Finite.mem_toFinset]
    rfl
  have hRpos : 0 < R := by linarith
  have hR'_ge_R : R ≤ R' := hRR'
  -- rewrite F into finite sums over S
  have hF' : F R' = ∑ u ∈ S, (((m R' u : ℤ) : ℂ) * w u) := by
    dsimp [F]
    refine finsum_eq_sum_of_support_subset _ ?_
    intro u hu
    rw [Function.mem_support] at hu
    have hm : m R' u ≠ 0 := by
      intro hz
      apply hu
      simp [hz]
    exact (hS_mem u).mpr hm
  have hF : F R = ∑ u ∈ S, (((m R u : ℤ) : ℂ) * w u) := by
    dsimp [F]
    refine finsum_eq_sum_of_support_subset _ ?_
    intro u hu
    rw [Function.mem_support] at hu
    have hm : m R u ≠ 0 := by
      intro hz
      apply hu
      simp [hz]
    have huB : u ∈ closedBall 0 R := (MeromorphicOn.divisor Λ (closedBall 0 R)).supportWithinDomain hm
    have hle : ‖u‖ ≤ R := by simpa [Metric.mem_closedBall, dist_eq_norm] using huB
    have hEq : m R u = m R' u := by
      dsimp [m]
      exact Commons.NumberTheory.Linnik.divisor_closedBall_eq_of_le hΛmer (u := u) (ρ₁ := R) (ρ₂ := R') hle (le_trans hle hRR')
    have hm' : m R' u ≠ 0 := by rwa [← hEq]
    exact (hS_mem u).mpr hm'
  -- difference
  have hD : F R' - F R = ∑ u ∈ S, ((((m R' u - m R u : ℤ) : ℂ)) * w u) := by
    rw [hF', hF]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro u hu
    simp [Int.cast_sub, sub_mul]
  -- collapse to the annulus R < |u|
  let T : Finset ℂ := S.filter (fun u => R < ‖u‖)
  have hDcoll : F R' - F R = ∑ u ∈ T, (((m R' u : ℤ) : ℂ) * w u) := by
    have hstep : ∀ u ∈ S, ((((m R' u - m R u : ℤ) : ℂ)) * w u) =
        if R < ‖u‖ then (((m R' u : ℤ) : ℂ) * w u) else 0 := by
      intro u huS
      by_cases hbig : R < ‖u‖
      · have hmR0 : m R u = 0 := by
          dsimp [m]
          exact Commons.NumberTheory.Linnik.divisor_closedBall_eq_zero_of_lt_norm (f := Λ) hbig
        simp [hbig, hmR0]
      · have hle : ‖u‖ ≤ R := le_of_not_gt hbig
        have hEq : m R u = m R' u := by
          dsimp [m]
          exact Commons.NumberTheory.Linnik.divisor_closedBall_eq_of_le hΛmer (u := u) (ρ₁ := R) (ρ₂ := R') hle (le_trans hle hRR')
        simp [hbig, hEq]
    calc
      F R' - F R = ∑ u ∈ S, ((((m R' u - m R u : ℤ) : ℂ)) * w u) := hD
      _ = ∑ u ∈ S, (if R < ‖u‖ then (((m R' u : ℤ) : ℂ) * w u) else 0) := by
          refine Finset.sum_congr rfl ?_
          intro u hu
          exact hstep u hu
      _ = ∑ u ∈ S.filter (fun u => R < ‖u‖), (((m R' u : ℤ) : ℂ) * w u) := by
          rw [Finset.sum_filter]
      _ = ∑ u ∈ T, (((m R' u : ℤ) : ℂ) * w u) := rfl
  -- norm bound
  have hnorm : ‖F R' - F R‖ ≤ ∑ u ∈ T, ‖(((m R' u : ℤ) : ℂ) * w u)‖ := by
    rw [hDcoll]
    exact norm_sum_le T (fun u => (((m R' u : ℤ) : ℂ) * w u))
  have hterm : ∀ u ∈ T, ‖(((m R' u : ℤ) : ℂ) * w u)‖ = (((m R' u : ℤ) : ℝ) * ‖w u‖) := by
    intro u huT
    have hm0 : 0 ≤ m R' u := hdiv_nonneg (closedBall 0 R') u
    rw [norm_mul, Complex.norm_int_of_nonneg hm0]
  have hnorm2 : ‖F R' - F R‖ ≤ ∑ u ∈ T, (((m R' u : ℤ) : ℝ) * ‖w u‖) := by
    calc
      ‖F R' - F R‖ ≤ ∑ u ∈ T, ‖(((m R' u : ℤ) : ℂ) * w u)‖ := hnorm
      _ = ∑ u ∈ T, (((m R' u : ℤ) : ℝ) * ‖w u‖) := by
          refine Finset.sum_congr rfl ?_
          intro u hu
          exact hterm u hu
  have hwu : ∀ u ∈ T, ‖w u‖ ≤ (4 / 3) * ‖s‖ / ‖u‖ ^ 2 := by
    intro u huT
    have hbig : R < ‖u‖ := (Finset.mem_filter.mp huT).2
    exact Commons.NumberTheory.Linnik.partialFrac_term_norm_le (s := s) (u := u) (R := R) hR hs (le_of_lt hbig)
  have hbnd : ‖F R' - F R‖ ≤ ∑ u ∈ T, (((m R' u : ℤ) : ℝ) * ((4 / 3) * ‖s‖ / ‖u‖ ^ 2)) := by
    calc
      ‖F R' - F R‖ ≤ ∑ u ∈ T, (((m R' u : ℤ) : ℝ) * ‖w u‖) := hnorm2
      _ ≤ ∑ u ∈ T, (((m R' u : ℤ) : ℝ) * ((4 / 3) * ‖s‖ / ‖u‖ ^ 2)) := by
          refine Finset.sum_le_sum ?_
          intro u huT
          have hm0 : 0 ≤ ((m R' u : ℤ) : ℝ) := by exact_mod_cast (hdiv_nonneg (closedBall 0 R') u)
          exact mul_le_mul_of_nonneg_left (hwu u huT) hm0
  let M : ℝ := (4 / 3) * ‖s‖
  have hM0 : 0 ≤ M := by dsimp [M]; positivity
  have hs0 : 0 ≤ ‖s‖ := norm_nonneg s
  let jl : ℂ → ℕ := fun u => Commons.NumberTheory.Linnik.dyadIdx R ‖u‖ (Commons.NumberTheory.Linnik.exists_dyadic_ge R ‖u‖ hRpos)
  have hjl_spec_le : ∀ u : ℂ, ‖u‖ ≤ (2 : ℝ) ^ (jl u + 1) * R := by
    intro u
    dsimp [jl]
    exact Commons.NumberTheory.Linnik.dyadIdx_spec_le R ‖u‖ (Commons.NumberTheory.Linnik.exists_dyadic_ge R ‖u‖ hRpos)
  have hjl_lower : ∀ u : ℂ, R < ‖u‖ → (2 : ℝ) ^ jl u * R < ‖u‖ := by
    intro u hu
    dsimp [jl]
    exact Commons.NumberTheory.Linnik.dyadIdx_lower (Commons.NumberTheory.Linnik.exists_dyadic_ge R ‖u‖ hRpos) hu
  rcases Commons.NumberTheory.Linnik.exists_dyadic_ge R R' hRpos with ⟨K, hK⟩
  have hjl_le_K : ∀ u ∈ T, jl u ≤ K := by
    intro u huT
    have hmem := Finset.mem_filter.mp huT
    have hbig : R < ‖u‖ := hmem.2
    have huS : u ∈ S := hmem.1
    have hm : m R' u ≠ 0 := (hS_mem u).mp huS
    have huB : u ∈ closedBall 0 R' := (MeromorphicOn.divisor Λ (closedBall 0 R')).supportWithinDomain hm
    have huR' : ‖u‖ ≤ R' := by simpa [Metric.mem_closedBall, dist_eq_norm] using huB
    have hK' : ‖u‖ ≤ (2 : ℝ) ^ (K + 1) * R := le_trans huR' hK
    dsimp [jl]
    exact Commons.NumberTheory.Linnik.dyadIdx_le_of R ‖u‖ (Commons.NumberTheory.Linnik.exists_dyadic_ge R ‖u‖ hRpos) hK'
  let Tj : ℕ → Finset ℂ := fun j => S.filter (fun u => (2 : ℝ) ^ j * R < ‖u‖ ∧ ‖u‖ ≤ (2 : ℝ) ^ (j + 1) * R)
  let b : ℕ → ℝ := fun j => ∑ u ∈ Tj j, ((m R' u : ℤ) : ℝ)
  let c : ℂ → ℝ := fun u => ((m R' u : ℤ) : ℝ)
  have hc0 : ∀ u, 0 ≤ c u := by
    intro u
    dsimp [c]
    exact_mod_cast (hdiv_nonneg (closedBall 0 R') u)
  have hc_eq : ∀ u, c u = ((m R' u : ℤ) : ℝ) := by intro u; rfl
  -- (a) pointwise weight bound at the level of u
  have hwM : ∀ u ∈ T, M / ‖u‖ ^ 2 ≤ M / (((4 : ℝ) ^ jl u) * R ^ 2) := by
    intro u huT
    have hbig : R < ‖u‖ := (Finset.mem_filter.mp huT).2
    have hsq := Commons.NumberTheory.Linnik.dyadIdx_sq_le (R := R) (ρ := ‖u‖) hRpos (Commons.NumberTheory.Linnik.exists_dyadic_ge R ‖u‖ hRpos) hbig
    have hy0 : 0 < (4 : ℝ) ^ jl u * R ^ 2 := by positivity
    exact div_le_div₀ hM0 le_rfl hy0 hsq
  have hw1 : ∀ u ∈ T, c u * (M / ‖u‖ ^ 2) ≤ c u * (M / (((4 : ℝ) ^ jl u) * R ^ 2)) := by
    intro u huT
    exact mul_le_mul_of_nonneg_left (hwM u huT) (hc0 u)
  have hc_def (u : ℂ) : c u = ((m R' u : ℤ) : ℝ) := rfl
  have hbndM : ‖F R' - F R‖ ≤ ∑ u ∈ T, (c u * (M / ‖u‖ ^ 2)) := by
    simpa [c, M] using hbnd
  -- (b) split into dyadic fibres
  let Afib : ℕ → ℝ := fun j => ∑ u ∈ T.filter (fun u => jl u = j), (c u * (M / (((4 : ℝ) ^ j) * R ^ 2)))
  have hfib_le_Tj : ∀ j : ℕ, T.filter (fun u => jl u = j) ⊆ Tj j := by
    intro j
    intro u hu
    have hmem := Finset.mem_filter.mp hu
    have huT : u ∈ T := hmem.1
    have hEq : jl u = j := hmem.2
    have hS' : u ∈ S := (Finset.mem_filter.mp huT).1
    have hbig : R < ‖u‖ := (Finset.mem_filter.mp huT).2
    have hlow' : (2 : ℝ) ^ jl u * R < ‖u‖ := hjl_lower u hbig
    have hlow : (2 : ℝ) ^ j * R < ‖u‖ := by simpa [hEq] using hlow'
    have hup : ‖u‖ ≤ (2 : ℝ) ^ (j + 1) * R := by
      simpa [hEq] using hjl_spec_le u
    exact Finset.mem_filter.mpr ⟨hS', ⟨hlow, hup⟩⟩
  have hfib_b : ∀ j : ℕ, (∑ u ∈ T.filter (fun u => jl u = j), c u) ≤ b j := by
    intro j
    dsimp [b]
    exact Finset.sum_le_sum_of_subset_of_nonneg (hfib_le_Tj j)
      (fun u huTj hnot => hc0 u)
  have hpart : (∑ u ∈ T, (c u * (M / (((4 : ℝ) ^ jl u) * R ^ 2)))) =
      ∑ j ∈ Finset.range (K + 1), Afib j := by
    have hpf := Commons.NumberTheory.Linnik.Finset.sum_eq_sum_image_filter (s := T) (g := jl)
      (f := fun u => c u * (M / (((4 : ℝ) ^ jl u) * R ^ 2)))
    have himg : T.image jl ⊆ Finset.range (K + 1) := by
      intro j hj
      rcases Finset.mem_image.mp hj with ⟨u, huT, hEq⟩
      have hle : j ≤ K := by simpa [hEq] using (hjl_le_K u huT)
      exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hle)
    calc
      (∑ u ∈ T, (c u * (M / (((4 : ℝ) ^ jl u) * R ^ 2))))
          = ∑ j ∈ T.image jl, ∑ u ∈ T.filter (fun u => jl u = j),
              (c u * (M / (((4 : ℝ) ^ j) * R ^ 2))) := by
              rw [hpf]
              refine Finset.sum_congr rfl ?_
              intro j hj
              refine Finset.sum_congr rfl ?_
              intro u hu
              have hEq : jl u = j := (Finset.mem_filter.mp hu).2
              simp [hEq]
      _ = ∑ j ∈ T.image jl, Afib j := rfl
      _ = ∑ j ∈ Finset.range (K + 1), Afib j := by
          refine Finset.sum_subset himg ?_
          intro j hj hnot
          -- j ∉ image: the fibre filter is empty
          have hfib_empty : (T.filter (fun u => jl u = j)) = ∅ := by
            ext u
            constructor
            · intro hu
              have hmem2 := Finset.mem_filter.mp hu
              exact False.elim (hnot (Finset.mem_image.mpr ⟨u, hmem2.1, hmem2.2⟩))
            · intro hu
              simp at hu
          simp [Afib, hfib_empty]
  have hweight : ∀ j : ℕ, 0 ≤ M / (((4 : ℝ) ^ j) * R ^ 2) := by
    intro j
    exact div_nonneg hM0 (by positivity)
  have hfib_nonneg : ∀ j : ℕ, 0 ≤ ∑ u ∈ T.filter (fun u => jl u = j), c u := by
    intro j
    exact Finset.sum_nonneg (fun u hu => hc0 u)
  -- (c) the tail bound via dyadicAnnulusTail
  let L : ℝ := 2
  have hL0 : 0 ≤ L := by norm_num
  -- count bound for each dyadic annulus
  have hb_le : ∀ j : ℕ, b j ≤ C * (2 : ℝ) ^ (j + 1) * R *
      (Real.log ((2 : ℝ) ^ (j + 1) * R + 2) + L) := by
    intro j
    let ρ : ℝ := (2 : ℝ) ^ (j + 1) * R
    have hρ2 : 2 ≤ ρ := by
      dsimp [ρ]
      have h1 : (2 : ℝ) ≤ (2 : ℝ) ^ (j + 1) := by
        have := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ (2 : ℝ)) (by omega : (1 : ℕ) ≤ j + 1)
        simpa using this
      nlinarith
    have hρ0 : 0 ≤ ρ := by linarith
    let Sρ : Finset ℂ := (hfin ρ).toFinset
    have hSρ_mem : ∀ u : ℂ, u ∈ Sρ ↔ m ρ u ≠ 0 := by
      intro u
      dsimp [Sρ]
      rw [Set.Finite.mem_toFinset]
      rfl
    have hcount : (∑ u ∈ Sρ, ((m ρ u : ℤ) : ℝ)) ≤ C * ρ * (Real.log (ρ + 2) + 2) := by
      have hc1 := hzcC ρ hρ2
      have hc2 : (∑ᶠ u : ℂ, (((m ρ u : ℤ) : ℝ))) = ∑ u ∈ Sρ, ((m ρ u : ℤ) : ℝ) := by
        refine finsum_eq_sum_of_support_subset _ ?_
        intro u hu
        rw [Function.mem_support] at hu
        have hm : m ρ u ≠ 0 := by
          intro hz
          apply hu
          simp [hz]
        exact (hSρ_mem u).mpr hm
      rwa [hc2] at hc1
    -- b j ≤ the count over Sρ
    have hb_le_count : b j ≤ ∑ u ∈ Sρ, ((m ρ u : ℤ) : ℝ) := by
      have hEq_val : ∀ u ∈ Tj j, m ρ u = m R' u := by
        intro u huTj
        have hmem := Finset.mem_filter.mp huTj
        have huS : u ∈ S := hmem.1
        have hbounds := hmem.2
        have huρ : ‖u‖ ≤ ρ := by
          dsimp [ρ]
          exact hbounds.2
        have huR' : ‖u‖ ≤ R' := by
          have hm' : m R' u ≠ 0 := (hS_mem u).mp huS
          have huB : u ∈ closedBall 0 R' :=
            (MeromorphicOn.divisor Λ (closedBall 0 R')).supportWithinDomain hm'
          simpa [Metric.mem_closedBall, dist_eq_norm] using huB
        dsimp [m]
        exact Commons.NumberTheory.Linnik.divisor_closedBall_eq_of_le hΛmer (u := u) (ρ₁ := ρ) (ρ₂ := R') huρ huR'
      have hsub : Tj j ⊆ Sρ := by
        intro u huTj
        have hmem := Finset.mem_filter.mp huTj
        have huρ : ‖u‖ ≤ ρ := by
          dsimp [ρ]
          exact hmem.2.2
        have hm' : m R' u ≠ 0 := (hS_mem u).mp hmem.1
        have hmρ : m ρ u ≠ 0 := by
          rw [hEq_val u huTj]
          exact hm'
        exact (hSρ_mem u).mpr hmρ
      calc
        b j = ∑ u ∈ Tj j, ((m R' u : ℤ) : ℝ) := by rfl
        _ = ∑ u ∈ Tj j, ((m ρ u : ℤ) : ℝ) := by
            refine Finset.sum_congr rfl ?_
            intro u huTj
            rw [hEq_val u huTj]
        _ ≤ ∑ u ∈ Sρ, ((m ρ u : ℤ) : ℝ) := by
            exact Finset.sum_le_sum_of_subset_of_nonneg hsub
              (fun u huSρ hnot => by
                exact_mod_cast (hdiv_nonneg (closedBall 0 ρ) u))
    calc
      b j ≤ ∑ u ∈ Sρ, ((m ρ u : ℤ) : ℝ) := hb_le_count
      _ ≤ C * ρ * (Real.log (ρ + 2) + 2) := hcount
      _ = C * (2 : ℝ) ^ (j + 1) * R * (Real.log ((2 : ℝ) ^ (j + 1) * R + 2) + L) := by
          dsimp [ρ, L]
          ring
  have hb0 : ∀ j : ℕ, 0 ≤ b j := by
    intro j
    dsimp [b]
    exact Finset.sum_nonneg (fun u hu => hc0 u)
  let G : ℝ := (2 * C * M / R) * (1 + Real.log (R + 2) + L)
  have hG0 : 0 ≤ G := by
    dsimp [G]
    have h1 : 0 ≤ 2 * C * M / R := by positivity
    have h2 : 0 ≤ 1 + Real.log (R + 2) + L := by
      have h : 0 ≤ Real.log (R + 2) := Real.log_nonneg (by linarith)
      linarith
    positivity
  have hlog2le1 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlogR0 : 0 ≤ Real.log (R + 2) := Real.log_nonneg (by linarith)
  have hsum_dyadic : Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) * ((1 / 2 : ℝ) ^ k)) := by
    have h := hasSum_choose_mul_geometric_of_norm_lt_one (k := 1) (r := (1 / 2 : ℝ))
      (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)
    simpa [Nat.choose_one_right] using h.summable
  have hsummable : Summable (fun j : ℕ => b j * (M / ((4 : ℝ) ^ j * R ^ 2))) := by
    refine Summable.of_nonneg_of_le (g := fun j : ℕ => b j * (M / ((4 : ℝ) ^ j * R ^ 2)))
      (f := fun j : ℕ => G * (((j + 1 : ℕ) : ℝ) * ((1 / 2 : ℝ) ^ j))) ?_ ?_ ?_
    · intro j
      exact mul_nonneg (hb0 j) (div_nonneg hM0 (by positivity : 0 ≤ (4 : ℝ) ^ j * R ^ 2))
    · intro j
      have hX : Real.log ((2 : ℝ) ^ (j + 1) * R + 2) + L ≤
          ((j + 1 : ℕ) : ℝ) * (1 + Real.log (R + 2) + L) := by
        have hlog := Commons.NumberTheory.Linnik.log_two_pow_mul_add_two_le hR j
        have hA : ((j + 1 : ℕ) : ℝ) * Real.log 2 + Real.log (R + 2) + L ≤
            ((j + 1 : ℕ) : ℝ) + Real.log (R + 2) + L := by
          have hm : ((j + 1 : ℕ) : ℝ) * Real.log 2 ≤ ((j + 1 : ℕ) : ℝ) := by
            have hjp : 0 ≤ ((j + 1 : ℕ) : ℝ) := by positivity
            calc
              ((j + 1 : ℕ) : ℝ) * Real.log 2 ≤ ((j + 1 : ℕ) : ℝ) * 1 := by
                exact mul_le_mul_of_nonneg_left hlog2le1 hjp
              _ = ((j + 1 : ℕ) : ℝ) := by ring
          linarith
        have hC : ((j + 1 : ℕ) : ℝ) + Real.log (R + 2) + L ≤
            ((j + 1 : ℕ) : ℝ) * (1 + Real.log (R + 2) + L) := by
          have hjp : 1 ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast (Nat.succ_pos j)
          nlinarith
        exact le_trans (le_trans (add_le_add_left hlog L) hA) hC
      have hb'' : b j ≤ C * (2 : ℝ) ^ (j + 1) * R *
          (((j + 1 : ℕ) : ℝ) * (1 + Real.log (R + 2) + L)) := by
        exact le_trans (hb_le j)
          (mul_le_mul_of_nonneg_left hX (by positivity : 0 ≤ C * (2 : ℝ) ^ (j + 1) * R))
      calc
        b j * (M / ((4 : ℝ) ^ j * R ^ 2))
            ≤ (C * (2 : ℝ) ^ (j + 1) * R * (((j + 1 : ℕ) : ℝ) * (1 + Real.log (R + 2) + L))) *
                (M / ((4 : ℝ) ^ j * R ^ 2)) := by
                exact mul_le_mul_of_nonneg_right hb''
                  (div_nonneg hM0 (by positivity : 0 ≤ (4 : ℝ) ^ j * R ^ 2))
        _ = G * (((j + 1 : ℕ) : ℝ) * ((1 / 2 : ℝ) ^ j)) := by
            have hw := Commons.NumberTheory.Linnik.dyadic_weight_eq (C := C) (M := M) (R := R)
              (B := 1 + Real.log (R + 2) + L) (ne_of_gt hRpos) j
            dsimp [G]
            rw [← hw]
    · exact Summable.mul_left G hsum_dyadic

  have hpartial : (∑ j ∈ Finset.range (K + 1), b j * (M / ((4 : ℝ) ^ j * R ^ 2))) ≤
      ∑' j : ℕ, b j * (M / ((4 : ℝ) ^ j * R ^ 2)) := by
    exact Summable.sum_le_tsum (Finset.range (K + 1))
      (fun i hi => by
        exact mul_nonneg (hb0 i) (by positivity : 0 ≤ M / ((4 : ℝ) ^ i * R ^ 2)))
      hsummable
  have htail := Commons.Analysis.Asymptotics.dyadicAnnulusTail (C := C) (R := R) (M := M) (L := L)
    hC0 hR hM0 hL0 b hb0 hb_le
  -- assemble the finite dyadic bound
  have hdybnd : (∑ u ∈ T, (c u * (M / ‖u‖ ^ 2))) ≤
      64 * C * M * (Real.log (R + 2) + L + 1) / R := by
    calc
      (∑ u ∈ T, (c u * (M / ‖u‖ ^ 2))) ≤ ∑ u ∈ T, (c u * (M / (((4 : ℝ) ^ jl u) * R ^ 2))) := by
          refine Finset.sum_le_sum ?_
          intro u huT
          exact hw1 u huT
      _ = ∑ j ∈ Finset.range (K + 1), Afib j := hpart
      _ = ∑ j ∈ Finset.range (K + 1), (M / (((4 : ℝ) ^ j) * R ^ 2)) *
          (∑ u ∈ T.filter (fun u => jl u = j), c u) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          dsimp [Afib]
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro u hu
          ring
      _ ≤ ∑ j ∈ Finset.range (K + 1), (M / (((4 : ℝ) ^ j) * R ^ 2)) * b j := by
          refine Finset.sum_le_sum ?_
          intro j hj
          exact mul_le_mul_of_nonneg_left (hfib_b j) (hweight j)
      _ = ∑ j ∈ Finset.range (K + 1), b j * (M / (((4 : ℝ) ^ j) * R ^ 2)) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          ring
      _ ≤ ∑' j : ℕ, b j * (M / ((4 : ℝ) ^ j * R ^ 2)) := hpartial
      _ ≤ 64 * C * M * (Real.log (R + 2) + L + 1) / R := htail
  -- final real arithmetic
  let Tlog : ℝ := Real.log (R + 2) + 2
  have hT2 : 2 ≤ Tlog := by
    dsimp [Tlog]
    have h1 : 0 ≤ Real.log (R + 2) := hlogR0
    linarith
  have hT0 : 0 ≤ Tlog := by linarith
  have hfrac : (64 : ℝ) * (4 / 3) * (Tlog + 1) ≤ 128 * Tlog := by
    nlinarith
  have hconst : (64 : ℝ) * C * M * (Tlog + 1) ≤ (128 * C) * ‖s‖ * Tlog := by
    have hfrac' : (64 : ℝ) * (4 / 3 : ℝ) * (Tlog + 1) ≤ 128 * Tlog := by
      nlinarith
    dsimp [M]
    have hstep : 64 * (4 / 3 : ℝ) * ‖s‖ * (Tlog + 1) ≤ 128 * ‖s‖ * Tlog := by
      have hm := mul_le_mul_of_nonneg_right hfrac' hs0
      nlinarith
    have hstepC : C * (64 * (4 / 3 : ℝ) * ‖s‖ * (Tlog + 1)) ≤ C * (128 * ‖s‖ * Tlog) :=
      mul_le_mul_of_nonneg_left hstep hC0
    nlinarith
  have hgoal : ‖F R' - F R‖ ≤ (128 * C) * ‖s‖ * Tlog / R := by
    calc
      ‖F R' - F R‖ ≤ ∑ u ∈ T, (c u * (M / ‖u‖ ^ 2)) := hbndM
      _ ≤ 64 * C * M * (Real.log (R + 2) + L + 1) / R := hdybnd
      _ = 64 * C * M * (Tlog + 1) / R := by
          dsimp [Tlog, L]
      _ ≤ (128 * C) * ‖s‖ * Tlog / R := by
          have hdiv := div_le_div_of_nonneg_right hconst (le_of_lt hRpos)
          simpa [M] using hdiv
  simpa [F, w, m, Tlog] using hgoal


/-! ### The full family of divisor sums converges (adapted from `partialFraction_conv`) -/

lemma xiF_partialFraction_conv (s : ℂ) :
    ∃ L : ℂ, Tendsto (fun R : ℝ =>
        (∑ᶠ u : ℂ, (((MeromorphicOn.divisor xiF (Metric.closedBall 0 R)) u : ℤ) : ℂ) *
          (1 / (s - u) + 1 / u))) atTop (nhds L) := by
  classical
  let F : ℝ → ℂ := fun R =>
        ∑ᶠ u : ℂ, (((MeromorphicOn.divisor xiF (Metric.closedBall 0 R)) u : ℤ) : ℂ) *
          (1 / (s - u) + 1 / u)
  let T : ℝ → ℝ := fun R => Real.log (R + 2) + 2
  rcases xiF_partialFraction_tail with ⟨c, hc⟩
  have hb : ∀ ⦃R R' : ℝ⦄, 2 ≤ R → R ≤ R' → ‖s‖ ≤ R / 4 →
      ‖F R' - F R‖ ≤ c * ‖s‖ * T R / R := by
    intro R R' hR hRR' hs
    simpa [F, T] using hc s R R' hR hRR' hs
  have hdec : Tendsto (fun R : ℝ => c * ‖s‖ * T R / R) atTop (𝓝 0) := by
    have hT : Tendsto (fun R : ℝ => (Real.log (R + 2) + 2) / R) atTop (𝓝 0) := by
      simpa using (Commons.NumberTheory.Linnik.log_add_two_add_const_div_self_tendsto_zero (D := 2))
    have hconst : Tendsto (fun _ : ℝ => c * ‖s‖) atTop (𝓝 (c * ‖s‖)) := tendsto_const_nhds
    have hmain : Tendsto (fun R : ℝ => (c * ‖s‖) * ((Real.log (R + 2) + 2) / R)) atTop (𝓝 0) := by
      simpa using hconst.mul hT
    have heq : (fun R : ℝ => (c * ‖s‖) * ((Real.log (R + 2) + 2) / R)) =ᶠ[atTop]
        fun R : ℝ => c * ‖s‖ * (Real.log (R + 2) + 2) / R := by
      filter_upwards with R
      ring
    simpa using hmain.congr' heq
  have hcauchy : ∀ ε > 0, ∃ R₀ : ℝ, ∀ R R' : ℝ, R₀ ≤ R → R₀ ≤ R' → ‖F R - F R'‖ < ε := by
    intro ε hε
    have hsmall : ∀ᶠ R : ℝ in atTop, c * ‖s‖ * T R / R < ε := by
      simpa [T] using hdec.eventually (Iio_mem_nhds hε)
    rcases (Filter.eventually_atTop.mp hsmall) with ⟨R₁, hR₁⟩
    let base : ℝ := max 2 (max (4 * ‖s‖) R₁)
    refine ⟨base, ?_⟩
    intro R R' hR₀R hR₀R'
    have h2R : 2 ≤ R := le_trans (le_max_left 2 (max (4 * ‖s‖) R₁)) hR₀R
    have h2R' : 2 ≤ R' := le_trans (le_max_left 2 (max (4 * ‖s‖) R₁)) hR₀R'
    have h4sR : (4 : ℝ) * ‖s‖ ≤ R := by
      exact le_trans (le_trans (le_max_left (4 * ‖s‖) R₁)
        (le_max_right 2 (max (4 * ‖s‖) R₁))) hR₀R
    have h4sR' : (4 : ℝ) * ‖s‖ ≤ R' := by
      exact le_trans (le_trans (le_max_left (4 * ‖s‖) R₁)
        (le_max_right 2 (max (4 * ‖s‖) R₁))) hR₀R'
    have hsR : ‖s‖ ≤ R / 4 := by nlinarith
    have hsR' : ‖s‖ ≤ R' / 4 := by nlinarith
    have hR1R : R₁ ≤ R := by
      exact le_trans (le_trans (le_max_right (4 * ‖s‖) R₁)
        (le_max_right 2 (max (4 * ‖s‖) R₁))) hR₀R
    have hR1R' : R₁ ≤ R' := by
      exact le_trans (le_trans (le_max_right (4 * ‖s‖) R₁)
        (le_max_right 2 (max (4 * ‖s‖) R₁))) hR₀R'
    have gRlt : c * ‖s‖ * T R / R < ε := by
      have h := hR₁ R hR1R
      simpa [T] using h
    have gR'lt : c * ‖s‖ * T R' / R' < ε := by
      have h := hR₁ R' hR1R'
      simpa [T] using h
    by_cases hle : R ≤ R'
    · have hb' := hb h2R hle hsR
      have hlelt : ‖F R - F R'‖ < ε := by
        rw [norm_sub_rev]
        exact lt_of_le_of_lt hb' gRlt
      simpa [dist_eq_norm] using hlelt
    · have hle' : R' ≤ R := le_of_not_ge hle
      have hb' := hb h2R' hle' hsR'
      have hlelt : ‖F R - F R'‖ < ε := lt_of_le_of_lt hb' gR'lt
      simpa [dist_eq_norm] using hlelt
  have hFcauchy : Cauchy (Filter.map F atTop) := by
    rw [cauchy_map_iff]
    constructor
    · exact Filter.atTop_neBot
    · rw [Metric.uniformity_basis_dist.tendsto_right_iff]
      intro ε hε
      rcases hcauchy ε hε with ⟨R₀, hR₀⟩
      rw [Filter.eventually_prod_iff]
      refine ⟨(fun R : ℝ => R₀ ≤ R), ?_, (fun R : ℝ => R₀ ≤ R), ?_, ?_⟩
      · exact (Filter.eventually_atTop.mpr ⟨R₀, fun b hb => hb⟩)
      · exact (Filter.eventually_atTop.mpr ⟨R₀, fun b hb => hb⟩)
      · intro R hR R' hR'
        simpa [dist_eq_norm] using hR₀ R R' hR hR'
  rcases (cauchy_map_iff_exists_tendsto (l := atTop) (f := F)).mp hFcauchy with ⟨L, hL⟩
  refine ⟨L, ?_⟩
  simpa [F] using hL



lemma xi_pf_tendsto   
     (s : ℂ)
    (hΛs : xiF s ≠ 0) :
    Tendsto (fun R : ℝ =>
        (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (xiF)
            (Metric.closedBall 0 R)) u : ℤ) : ℂ) * (1 / (s - u) + 1 / u)))
      atTop (nhds (deriv (xiF) s /
        xiF s -
        deriv (xiF) 0 /
          xiF 0)) := by
  classical
  let Λc : ℂ → ℂ := xiF
  let PF : ℝ → ℂ := fun R : ℝ =>
        ∑ᶠ u : ℂ, (((MeromorphicOn.divisor Λc (Metric.closedBall 0 R)) u : ℤ) : ℂ) * (1 / (s - u) + 1 / u)
  let K : ℂ := deriv Λc s / Λc s - deriv Λc 0 / Λc 0
  have hΛ0 : Λc 0 ≠ 0 := by simpa [Λc] using xiF_zero_ne
  have hΛdiff : Differentiable ℂ Λc := by simpa [Λc] using xiF_diff
  have hΛs' : Λc s ≠ 0 := by simpa [Λc] using hΛs
  have hPF_def : ∀ R : ℝ, PF R = (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (xiF)
            (Metric.closedBall 0 R)) u : ℤ) : ℂ) * (1 / (s - u) + 1 / u)) := by
    intro R
    rfl
  -- the full family converges (xiF_partialFraction_conv)
  rcases xiF_partialFraction_conv  s with ⟨L, hL⟩
  have hL' : Tendsto PF atTop (𝓝 L) := by
    simpa [PF] using hL
  -- good-radius selector
  rcases xiF_goodRadius  with ⟨A₀, hA₀pos, hA₀R⟩
  let τ : ℝ → ℝ := fun A => if h : A₀ ≤ A then (hA₀R A h).choose else 1
  have hτ_spec : ∀ A : ℝ, A₀ ≤ A → A ≤ τ A ∧ τ A ≤ 2 * A ∧
      ∀ u : ℂ, Λc u = 0 → (xiL A) ^ 2 * |‖u‖ - τ A| ≥ 1 := by
    intro A hA
    dsimp [τ]
    rw [dif_pos hA]
    have hs := (hA₀R A hA).choose_spec
    exact hs
  have hτ_top : Tendsto τ atTop atTop := by
    have hev : ∀ᶠ A : ℝ in atTop, A ≤ τ A := by
      filter_upwards [eventually_ge_atTop A₀] with A hA
      exact (hτ_spec A hA).1
    exact tendsto_atTop_mono' atTop hev tendsto_id
  -- constants for the decay bound
  let gc : ℝ := xi_gc 
  let zc : ℝ := xi_zc 
  let del : ℝ := xi_delta 
  let C0 : ℝ := 4 * gc + 8 * zc + 4 * zc * (2 + |Real.log del|)
  let C1 : ℝ := |Real.log ‖Λc 0‖| + 2
  let D : ℝ := C1 + 1
  let E : ℝ → ℝ := fun A : ℝ => 1024 * ‖s‖ * (C0 * (xiL A) ^ 2 / A + D / A ^ 2)
  have hgc0 : 0 ≤ gc := by dsimp [gc]; exact xi_gc_nonneg 
  have hzc0 : 0 ≤ zc := by dsimp [zc]; exact xi_zc_nonneg 
  have hC0 : 0 ≤ C0 := by dsimp [C0]; positivity
  have hC1 : 0 ≤ C1 := by dsimp [C1]; positivity
  have hdec_E : Tendsto E atTop (𝓝 0) := by
    have h1 : Tendsto (fun A : ℝ => (xiL A) ^ 2 / A) atTop (𝓝 0) := by
      exact xiL_sq_div_self_tendsto_zero
    have h1' : Tendsto (fun A : ℝ => C0 * ((xiL A) ^ 2 / A)) atTop (𝓝 0) := by
      simpa using ((tendsto_const_nhds (x := C0)).mul h1)
    have h1'' : (fun A : ℝ => C0 * ((xiL A) ^ 2 / A)) =ᶠ[atTop] fun A => C0 * (xiL A) ^ 2 / A := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with A hA
      ring
    have hA1 : Tendsto (fun A : ℝ => C0 * (xiL A) ^ 2 / A) atTop (𝓝 0) := h1'.congr' h1''
    have hinv : Tendsto (fun A : ℝ => A⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
    have hDinv : Tendsto (fun A : ℝ => D * A⁻¹) atTop (𝓝 0) := by
      simpa using ((tendsto_const_nhds (x := D)).mul hinv)
    have hDinv2 : Tendsto (fun A : ℝ => D * A⁻¹ * A⁻¹) atTop (𝓝 0) := by
      simpa using (hDinv.mul hinv)
    have h2 : Tendsto (fun A : ℝ => D / A ^ 2) atTop (𝓝 0) := by
      have hsq : (fun A : ℝ => D / A ^ 2) =ᶠ[atTop] fun A : ℝ => D * A⁻¹ * A⁻¹ := by
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with A hA
        field_simp [ne_of_gt hA]
      exact hDinv2.congr' hsq.symm
    have hsum : Tendsto (fun A : ℝ => C0 * (xiL A) ^ 2 / A + D / A ^ 2) atTop (𝓝 0) := by
      simpa using (hA1.add h2)
    have h3 : Tendsto (fun A : ℝ => 1024 * ‖s‖ * (C0 * (xiL A) ^ 2 / A + D / A ^ 2)) atTop (𝓝 0) := by
      simpa using ((tendsto_const_nhds (x := 1024 * ‖s‖)).mul hsum)
    have h4 : (fun A : ℝ => 1024 * ‖s‖ * (C0 * (xiL A) ^ 2 / A + D / A ^ 2)) =ᶠ[atTop] fun A => E A := by
      filter_upwards with A
      dsimp [E]
    exact h3.congr' h4
  -- bound of the error along good radii
  have hmain : ∀ᶠ A : ℝ in atTop, ‖PF (τ A) - K‖ ≤ E A := by
    filter_upwards [eventually_ge_atTop A₀, eventually_ge_atTop (8 * ‖s‖),
      eventually_ge_atTop (2 : ℝ)] with A hA₀ hA8 hA2
    let T : ℝ := τ A
    have hspec := hτ_spec A hA₀
    have hA_le_T : A ≤ T := hspec.1
    have hT_le_2A : T ≤ 2 * A := hspec.2.1
    have hmargin : ∀ u : ℂ, Λc u = 0 → (xiL A) ^ 2 * |‖u‖ - T| ≥ 1 := hspec.2.2
    have hA0 : 0 ≤ A := by linarith
    have hTpos : 0 < T := by dsimp [T]; linarith
    have hT2 : 2 ≤ T := by dsimp [T]; linarith
    have hT1 : 1 ≤ T := by linarith
    have hsT : ‖s‖ ≤ T / 8 := by
      dsimp [T]
      have h1 : 8 * ‖s‖ ≤ A := hA8
      have hle : A ≤ τ A := hA_le_T
      nlinarith
    rcases xi_cofactor_bound  (A := A) (T := T) hA0 hTpos hT2 hmargin with
      ⟨g, ε, hε, hg_an, hg_nz, hfac, hgM, hg0M⟩
    have hg_an_T : AnalyticOnNhd ℂ g (ball 0 T) := by
      refine AnalyticOnNhd.mono hg_an ?_
      intro w hw
      rw [mem_ball_zero_iff] at hw ⊢
      nlinarith [hε]
    have hg_nz_T : ∀ w : ℂ, w ∈ ball 0 T → g w ≠ 0 := by
      intro w hw
      have hwε : w ∈ ball 0 (T + ε) := by
        rw [mem_ball_zero_iff]
        rw [mem_ball_zero_iff] at hw
        nlinarith [hε]
      exact hg_nz w hwε
    have hM0nn : 0 ≤ xi_M0  A T := xi_M0_nonneg  (A := A) (T := T) hA0 hT1
    have hsub := pf_logDeriv_sub_of_sup (g := g) (R := T) hTpos hg_an_T hg_nz_T
      (M0 := xi_M0  A T) hM0nn hgM hg0M hsT
    -- decompositions at s and at 0
    have hfac_sT : ∀ z : ℂ, z ∈ ball 0 (T + ε) →
        Λc z = (∏ᶠ u : ℂ, (z - u) ^ (MeromorphicOn.divisor Λc (closedBall (0 : ℂ) T)) u) * g z := hfac
    have hdec_s := logDeriv_decompose (f := Λc) (g := g) (R := T) (ε := ε) hΛdiff hfac_sT
      (x := s) (hx := by
        rw [mem_ball_zero_iff]
        have hsT' : ‖s‖ < T := by nlinarith [hsT, show 0 < T from hTpos]
        nlinarith [hε]) hΛs' (hg_an s (by
          rw [mem_ball_zero_iff]
          have hsT' : ‖s‖ < T := by nlinarith [hsT, show 0 < T from hTpos]
          nlinarith [hε])).differentiableAt (hg_nz s (by
            rw [mem_ball_zero_iff]
            have hsT' : ‖s‖ < T := by nlinarith [hsT, show 0 < T from hTpos]
            nlinarith [hε]))
    have hdec_0 := logDeriv_decompose (f := Λc) (g := g) (R := T) (ε := ε) hΛdiff hfac_sT
      (x := 0) (hx := by rw [mem_ball_zero_iff]; simp; positivity) hΛ0
      (hg_an 0 (by rw [mem_ball_zero_iff]; simp; positivity)).differentiableAt
        (hg_nz 0 (by rw [mem_ball_zero_iff]; simp; positivity))
    -- finsum bookkeeping over the common support
    let dT : ℂ → ℤ := fun u => MeromorphicOn.divisor Λc (closedBall (0 : ℂ) T) u
    let cT : ℂ → ℂ := fun u => (dT u : ℂ)
    have hsuppZ : (Function.support dT).Finite := by
      dsimp [dT]
      exact xiF_divisor_support_finite  T
    have hsuppC : (Function.support cT).Finite := by
      have hsub : Function.support cT ⊆ Function.support dT := by
        intro u hu
        rw [Function.mem_support] at hu
        rw [Function.mem_support]
        intro hz
        exact hu (by
          dsimp [cT]
          exact_mod_cast hz)
      exact hsuppZ.subset hsub
    let S : Finset ℂ := hsuppC.toFinset
    have hmemS : ∀ u : ℂ, u ∈ S ↔ cT u ≠ 0 := by
      intro u
      dsimp [S]
      rw [Set.Finite.mem_toFinset]
      rfl
    have hS_cT : ∀ u : ℂ, u ∉ S → cT u = 0 := by
      intro u hu
      have hne : cT u = 0 := by
        by_contra h
        exact hu ((hmemS u).mpr h)
      exact hne
    have hsub_sums : ∀ (f : ℂ → ℂ), (∀ u : ℂ, cT u = 0 → f u = 0) →
        (Function.support f) ⊆ (S : Set ℂ) := by
      intro f hf u hu
      rw [Function.mem_support] at hu
      by_contra hS'
      have hc0 : cT u = 0 := hS_cT u hS'
      exact hu (hf u hc0)
    have hPF_T : PF T = ∑ u ∈ S, cT u * (1 / (s - u) + 1 / u) := by
      have hconv : PF T = ∑ᶠ u : ℂ, cT u * (1 / (s - u) + 1 / u) := by
        dsimp [PF, cT, dT]
      rw [hconv]
      refine finsum_eq_sum_of_support_subset (fun u : ℂ => cT u * (1 / (s - u) + 1 / u)) ?_
      exact hsub_sums (fun u : ℂ => cT u * (1 / (s - u) + 1 / u)) (fun u hc0 => by simp [hc0])
    have hdec_s_sum : (∑ᶠ u : ℂ, cT u * (1 / (s - u))) = ∑ u ∈ S, cT u * (1 / (s - u)) := by
      refine finsum_eq_sum_of_support_subset (fun u : ℂ => cT u * (1 / (s - u))) ?_
      exact hsub_sums (fun u : ℂ => cT u * (1 / (s - u))) (fun u hc0 => by simp [hc0])
    have hdec_0_sum : (∑ᶠ u : ℂ, cT u * (1 / ((0 : ℂ) - u))) = ∑ u ∈ S, cT u * (1 / ((0 : ℂ) - u)) := by
      refine finsum_eq_sum_of_support_subset (fun u : ℂ => cT u * (1 / ((0 : ℂ) - u))) ?_
      exact hsub_sums (fun u : ℂ => cT u * (1 / ((0 : ℂ) - u))) (fun u hc0 => by simp [hc0])
    have hB_sum : (∑ᶠ u : ℂ, cT u * (1 / u)) = ∑ u ∈ S, cT u * (1 / u) := by
      refine finsum_eq_sum_of_support_subset (fun u : ℂ => cT u * (1 / u)) ?_
      exact hsub_sums (fun u : ℂ => cT u * (1 / u)) (fun u hc0 => by simp [hc0])
    have hsumB_neg : (∑ u ∈ S, cT u * (1 / ((0 : ℂ) - u))) = -∑ u ∈ S, cT u * (1 / u) := by
      calc
        (∑ u ∈ S, cT u * (1 / ((0 : ℂ) - u))) = ∑ u ∈ S, -(cT u * (1 / u)) := by
          apply Finset.sum_congr rfl
          intro u hu
          congr 1
          ring
        _ = -∑ u ∈ S, cT u * (1 / u) := by rw [Finset.sum_neg_distrib]
    -- the key identity PF(T) - K = -(logDeriv g s - logDeriv g 0)
    have hdec_s' : logDeriv Λc s = (∑ u ∈ S, cT u * (1 / (s - u))) + logDeriv g s := by
      rw [← hdec_s_sum]
      simpa [cT, one_div] using hdec_s
    have hdec_0' : logDeriv Λc 0 = (∑ u ∈ S, cT u * (1 / ((0 : ℂ) - u))) + logDeriv g 0 := by
      rw [← hdec_0_sum]
      simpa [cT, one_div] using hdec_0
    have hK : K = logDeriv Λc s - logDeriv Λc 0 := by
      dsimp [K]
      rw [← logDeriv_apply]
      rw [← logDeriv_apply]
    have hrel : PF T = K - (logDeriv g s - logDeriv g 0) := by
      have hterm : (fun u : ℂ => cT u * (1 / (s - u) + 1 / u)) =
          fun u : ℂ => cT u * (1 / (s - u)) + cT u * (1 / u) := by
        funext u
        ring
      calc
        PF T = (∑ u ∈ S, cT u * (1 / (s - u))) + (∑ u ∈ S, cT u * (1 / u)) := by
            rw [hPF_T]
            rw [hterm]
            rw [Finset.sum_add_distrib]
        _ = (logDeriv Λc s - logDeriv Λc 0) - (logDeriv g s - logDeriv g 0) := by
            rw [hdec_s', hdec_0', hsumB_neg]
            ring
        _ = K - (logDeriv g s - logDeriv g 0) := by
            rw [← hK]
    have hnorm_bound : ‖PF (τ A) - K‖ ≤ 1024 * (max (xi_M0  A T) 1) * ‖s‖ / T ^ 2 := by
      have hPFK : PF (τ A) = K - (logDeriv g s - logDeriv g 0) := by
        simpa [T] using hrel
      have hn : ‖PF (τ A) - K‖ = ‖logDeriv g s - logDeriv g 0‖ := by
        rw [hPFK]
        have hEq : (K - (logDeriv g s - logDeriv g 0)) - K = -(logDeriv g s - logDeriv g 0) := by
          abel
        rw [hEq]
        rw [norm_neg]
      rw [hn]
      exact hsub
    -- decay of the explicit bound:  ‖PF(τA) − K‖ ≤ 1024·(M0+1)·‖s‖/T² ≤ E A
    have hnorm_lin : 1024 * (max (xi_M0  A T) 1) * ‖s‖ / T ^ 2 ≤
        1024 * (xi_M0  A T + 1) * ‖s‖ / T ^ 2 := by
      have hT2nn : 0 ≤ T ^ 2 := by positivity
      have h1 : max (xi_M0  A T) 1 ≤ xi_M0  A T + 1 := by
        by_cases h : xi_M0  A T ≤ 1
        · simpa [max_eq_right h]
        · have hlt : 1 < xi_M0  A T := lt_of_not_ge h
          simpa [max_eq_left (le_of_lt hlt)]
      have h2 : 1024 * max (xi_M0  A T) 1 * ‖s‖ ≤
          1024 * (xi_M0  A T + 1) * ‖s‖ := by
        have h1024 : 0 ≤ (1024 : ℝ) := by norm_num
        have hmm := mul_le_mul_of_nonneg_left h1 h1024
        exact mul_le_mul_of_nonneg_right hmm (norm_nonneg s)
      exact div_le_div_of_nonneg_right h2 hT2nn
    have hmain' : 1024 * (xi_M0  A T + 1) * ‖s‖ / T ^ 2 ≤ E A := by
      have hM0le : xi_M0  A T ≤ xi_C0  * A * (xiL A) ^ 2 + xi_C1  := by
        exact xi_M0_le  (hA1 := (by linarith : 1 ≤ A)) hA_le_T hT_le_2A
      have hA2le : A ^ 2 ≤ T ^ 2 := by
        have hTmA : 0 ≤ T - A := by linarith
        have hTpA : 0 ≤ T + A := by
          have hT0' : 0 ≤ T := le_of_lt hTpos
          linarith
        have hprod : 0 ≤ (T - A) * (T + A) := mul_nonneg hTmA hTpA
        nlinarith [hprod]
      have hdenpos : 0 < A ^ 2 := by positivity
      have hdenpos' : 0 < T ^ 2 := by positivity
      have hnumle : (xi_M0  A T + 1) / T ^ 2 ≤
          (xi_C0  * A * (xiL A) ^ 2 + xi_C1  + 1) / A ^ 2 := by
        rw [div_le_div_iff₀ hdenpos' hdenpos]
        have hnn0 : 0 ≤ xi_M0  A T + 1 := by linarith [hM0nn]
        have hle_num : xi_M0  A T + 1 ≤
            xi_C0  * A * (xiL A) ^ 2 + xi_C1  + 1 := by linarith
        have hT0 : 0 ≤ T ^ 2 := by positivity
        have hA0s : 0 ≤ A ^ 2 := by positivity
        nlinarith [hA2le, hle_num, hT0, hA0s]
      calc
        1024 * (xi_M0  A T + 1) * ‖s‖ / T ^ 2
            = 1024 * ‖s‖ * ((xi_M0  A T + 1) / T ^ 2) := by
                have hT2nz : T ^ 2 ≠ 0 := by positivity
                field_simp [hT2nz]
        _ ≤ 1024 * ‖s‖ * ((xi_C0  * A * (xiL A) ^ 2 + xi_C1  + 1) / A ^ 2) := by
              exact mul_le_mul_of_nonneg_left hnumle (by positivity : 0 ≤ 1024 * ‖s‖)
        _ = E A := by
              dsimp [E, C0, C1, D, xi_C0, xi_C1, gc, zc, del, Λc]
              have hAne : A ≠ 0 := by positivity
              have hA2nz : A ^ 2 ≠ 0 := by positivity
              field_simp [hAne, hA2nz]
              ring_nf
    exact le_trans hnorm_bound (le_trans hnorm_lin hmain')

  have hnorm0 : Tendsto (fun A : ℝ => ‖PF (τ A) - K‖) atTop (𝓝 0) := by
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' (tendsto_const_nhds (x := (0 : ℝ))) hdec_E
      (by filter_upwards with A; exact norm_nonneg _) hmain
  have hseq : Tendsto (fun A : ℝ => PF (τ A)) atTop (𝓝 K) := by
    have hzero : Tendsto (fun A : ℝ => PF (τ A) - K) atTop (𝓝 0) :=
      tendsto_zero_iff_norm_tendsto_zero.mpr hnorm0
    have hadd : Tendsto (fun A : ℝ => (PF (τ A) - K) + K) atTop (𝓝 (0 + K)) := hzero.add tendsto_const_nhds
    have heq : (fun A : ℝ => (PF (τ A) - K) + K) =ᶠ[atTop] fun A : ℝ => PF (τ A) := by
      filter_upwards with A
      abel
    simpa using (hadd.congr' heq)
  have hcompL : Tendsto (fun A : ℝ => PF (τ A)) atTop (𝓝 L) := hL'.comp hτ_top
  have hLK : L = K := tendsto_nhds_unique hcompL hseq
  have hPFK : Tendsto PF atTop (𝓝 K) := by
    simpa [hLK] using hL'
  simpa [PF, Λc, K, logDeriv_apply] using hPFK


theorem xi_pf_identity_rect  
      :
    ∃ B : ℂ, ∀ s : ℂ,
      xiF s ≠ 0 →
      Filter.Tendsto (fun R : ℝ =>
        (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (xiF)
            (Metric.closedBall 0 R)) u : ℤ) : ℂ) * (1 / (s - u) + 1 / u)))
        Filter.atTop (nhds (deriv (xiF) s /
          xiF s - B)) := by
  classical
  refine ⟨deriv (xiF) 0 /
    xiF 0, ?_⟩
  intro s hs
  exact xi_pf_tendsto  s hs


theorem xi_pf_identity (s : ℂ) (hs : xiF s ≠ 0) :
    Tendsto (fun R : ℝ =>
        (∑ᶠ u : ℂ, (((MeromorphicOn.divisor xiF (Metric.closedBall 0 R)) u : ℤ) : ℂ) *
          (1 / (s - u) + 1 / u)))
      atTop (nhds (logDeriv xiF s - logDeriv xiF 0)) := by
  exact xi_pf_tendsto s hs

end XiPF

/-- **Partial fraction (log-derivative) identity for the entire Riemann xi completion.**

For `xiE(s) = 1/2 + (1/2)·s·(s-1)·Λ₀(s)` (the Riemann xi function), the divisor-weighted
partial sums

    Σ_{‖u‖ ≤ R} ord_{xiE}(u)·(1/(s-u) + 1/u)

converge, as `R → ∞`, to the difference of logarithmic derivatives
`(xiE'/xiE)(s) − (xiE'/xiE)(0)` whenever `xiE(s) ≠ 0`.  This is the exact-value form of the
Hadamard partial-fraction expansion (the genus-one Hadamard factorisation of `xiE`), proved
by the circle/contour machinery of `Commons.NumberTheory.Linnik.completedL_pf_identity_rect`
adapted to the Riemann zeta completion (see `XiPF` above).
-/
theorem xiE_partialFraction_eq (s : ℂ)
    (hs : ((1 / 2 : ℂ) + (1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta₀ s) ≠ 0) :
    Filter.Tendsto (fun R : ℝ =>
      (∑ᶠ u : ℂ,
        (((MeromorphicOn.divisor (fun z : ℂ =>
            (1 / 2 : ℂ) + (1 / 2 : ℂ) * z * (z - 1) * completedRiemannZeta₀ z)
          (Metric.closedBall 0 R)) u : ℤ) : ℂ) * (1 / (s - u) + 1 / u)))
      Filter.atTop (nhds
        (logDeriv (fun z : ℂ =>
            (1 / 2 : ℂ) + (1 / 2 : ℂ) * z * (z - 1) * completedRiemannZeta₀ z) s -
         logDeriv (fun z : ℂ =>
            (1 / 2 : ℂ) + (1 / 2 : ℂ) * z * (z - 1) * completedRiemannZeta₀ z) 0)) := by
  exact XiPF.xi_pf_identity s (by simpa [XiPF.xiF] using hs)

end Commons.NumberTheory.Zeta
