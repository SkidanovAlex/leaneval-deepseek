import Submission.Work.VolterraLong.Estimates.Operator
import Submission.Work.VolterraLong.Weighted.Metric
import Submission.Work.VolterraLong.FixedPoint

/-!
# Long-interval existence for the Volterra system

The main theorem of this chapter: for data `G, Θ, Ξ` which is `ε`-close to base
data `(G₀,Θ₀,Ξ₀)` admitting a base solution `Z₀`, the integro-differential
system

`(★)   G(s, Z(s)) = ∫_s^b Θ(s,σ,Z(σ)) dσ + Ξ(s)`

has a solution on the **whole** interval `[a,b]`, with `dist (Z s) (Z₀ s) ≤ K ε`,
provided `ε` is small enough.  In contrast with
`Commons.Geometry.Ulam.volterra_perturbation_exists_continuous_theta_small` no
smallness of `b - a` is required: the exponentially weighted supremum norm
gains a factor `1/λ` in the Volterra integral.
-/

set_option linter.unusedVariables false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology Interval

namespace Work.VolterraLong

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
/-- The core of the long-interval existence theorem, with the smallness
thresholds made explicit: `lam = 4 B L + 1` is the exponential weight,
`M = 2 + (b - a)` and `EE = e^{lam (b-a)}` are the sup-norm conversion
factors. -/
theorem volterra_long_exists_eps {a b : ℝ} (hab : a ≤ b)
    (A : ℝ → E ≃L[ℝ] E) (G0 G : ℝ → E → E) (Θ0 Θ : ℝ → ℝ → E → E) (Ξ0 Ξ : ℝ → E)
    (Z₀ : ℝ → E) {B L Cg : ℝ} (hB : 0 < B) (hL : 0 ≤ L) (hCg : 0 ≤ Cg)
    (hA_spec : ∀ s ∈ Set.Icc a b, (A s : E →L[ℝ] E) = fderiv ℝ (fun z => G0 s z) (Z₀ s))
    (hA_cont : ContinuousOn (fun s => ((A s).symm : E →L[ℝ] E)) (Set.Icc a b))
    (hAb : ∀ s ∈ Set.Icc a b, ‖((A s).symm : E →L[ℝ] E)‖ ≤ B)
    (hG_cont : Continuous (fun p : ℝ × E => G p.1 p.2))
    (hΘ_cont : Continuous (fun p : ℝ × ℝ × E => Θ p.1 p.2.1 p.2.2))
    (hΞ_cont : Continuous Ξ)
    (hZ₀_cont : ContinuousOn Z₀ (Set.Icc a b))
    (hΘ0_cont : Continuous (fun p : ℝ × ℝ × E => Θ0 p.1 p.2.1 p.2.2))
    (hbase : ∀ s ∈ Set.Icc a b, G0 s (Z₀ s) = (∫ σ in s..b, Θ0 s σ (Z₀ σ)) + Ξ0 s)
    (hΘ_lip : ∀ s ∈ Set.Icc a b, ∀ σ ∈ Set.Icc a b, ∀ z ∈ Metric.closedBall (Z₀ σ) 1,
      ∀ z' ∈ Metric.closedBall (Z₀ σ) 1, ‖Θ s σ z - Θ s σ z'‖ ≤ L * ‖z - z'‖)
    (hdiff : ∀ s ∈ Set.Icc a b, ∀ z ∈ Metric.closedBall (Z₀ s) 1,
      DifferentiableAt ℝ (fun w => G s w) z)
    (lam M EE : ℝ) (hlam_def : lam = 4 * B * L + 1) (hM_def : M = 2 + (b - a))
    (hEE_def : EE = Real.exp (lam * (b - a)))
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hε2 : ε < 1 / (2 * B * M * EE))
    (hε3 : ε < 1 / (4 * B * (2 * B * Cg * M * EE + 1)))
    (hΞc : ∀ s ∈ Set.Icc a b, dist (Ξ s) (Ξ0 s) < ε)
    (hGc : ∀ s ∈ Set.Icc a b, ∀ z ∈ Metric.closedBall (Z₀ s) 1,
      dist (G s z) (G0 s z) < ε)
    (hΘc : ∀ s ∈ Set.Icc a b, ∀ σ ∈ Set.Icc a b, ∀ z ∈ Metric.closedBall (Z₀ σ) 1,
      dist (Θ s σ z) (Θ0 s σ z) < ε)
    (hder : ∀ s ∈ Set.Icc a b, ∀ z ∈ Metric.closedBall (Z₀ s) 1,
      ‖fderiv ℝ (fun w => G s w) z - (A s : E →L[ℝ] E)‖ ≤ Cg * ‖z - Z₀ s‖ + ε) :
    ∃ Z : ℝ → E, ContinuousOn Z (Set.Icc a b) ∧ SolvesOn a b G Θ Ξ Z ∧
      (∀ s ∈ Set.Icc a b, dist (Z s) (Z₀ s) ≤ 2 * B * M * EE * ε) := by
  classical
  have hlam_pos : 0 < lam := by rw [hlam_def]; nlinarith [hB, hL]
  have hlam_nonneg : 0 ≤ lam := le_of_lt hlam_pos
  have hM_pos : 0 < M := by rw [hM_def]; linarith
  have hEE_one : 1 ≤ EE := by
    rw [hEE_def, ← Real.exp_zero, hlam_def]
    exact Real.exp_le_exp.mpr (by nlinarith [hB, hL, hab])
  have hEE_pos : 0 < EE := lt_of_lt_of_le one_pos hEE_one
  let D : Data (E := E) hab :=
    { A := A, G := G, Θ := Θ, Ξ := Ξ, Z₀ := Z₀, hA := hA_cont, hG := hG_cont,
      hΘ := hΘ_cont, hΞ := hΞ_cont, hZ₀ := hZ₀_cont }
  have hDop : D.op = longOp hab A G Θ Ξ Z₀ hA_cont hG_cont hΘ_cont hΞ_cont hZ₀_cont := rfl
  set Rw : ℝ := 2 * B * M * ε with hRw_def
  set Rs : ℝ := Rw * EE with hRs_def
  have hRw_nonneg : 0 ≤ Rw := by rw [hRw_def]; positivity
  have hRw_pos : 0 < Rw := by rw [hRw_def]; positivity
  have hRs_nonneg : 0 ≤ Rs := by rw [hRs_def]; positivity
  have hRs_le_one : Rs ≤ 1 := by
    rw [hRs_def, hRw_def]
    have hden : 0 < 2 * B * M * EE := by positivity
    have hlt := (lt_div_iff₀ hden).mp hε2
    nlinarith [hlt]
  have h0fun : ∀ s : Set.Icc a b, (0 : BoundedContinuousFunction (Set.Icc a b) E) s = 0 :=
    fun _ => rfl
  -- the supremum-norm bound of the weighted ball
  have hsup : ∀ W ∈ {W : BoundedContinuousFunction (Set.Icc a b) E | wdist lam W 0 ≤ Rw},
      ∀ s : Set.Icc a b, ‖W s‖ ≤ Rs := by
    intro W hW s
    have h1 : ‖W s - (0 : BoundedContinuousFunction (Set.Icc a b) E) s‖ *
        Real.exp (-(lam * (b - (s:ℝ)))) ≤ Rw :=
      le_trans (le_wdist hlam_nonneg W 0 s) hW
    rw [h0fun s, sub_zero] at h1
    have h2 : ‖W s‖ ≤ Rw * Real.exp (lam * (b - (s:ℝ))) := by
      have hpos : 0 < Real.exp (lam * (b - (s:ℝ))) := Real.exp_pos _
      have h3 : ‖W s‖ * (Real.exp (lam * (b - (s:ℝ))))⁻¹ *
          Real.exp (lam * (b - (s:ℝ))) ≤ Rw * Real.exp (lam * (b - (s:ℝ))) := by
        rw [Real.exp_neg] at h1
        exact mul_le_mul_of_nonneg_right h1 (le_of_lt hpos)
      rwa [mul_assoc, inv_mul_cancel₀ (ne_of_gt hpos), mul_one] at h3
    calc ‖W s‖ ≤ Rw * Real.exp (lam * (b - (s:ℝ))) := h2
      _ ≤ Rw * EE := by
          apply mul_le_mul_of_nonneg_left _ hRw_nonneg
          rw [hEE_def]
          exact Real.exp_le_exp.mpr (by nlinarith [hlam_nonneg, s.2.1])
      _ = Rs := by rw [hRs_def]
  -- the contractivity constant is at most 1/2
  have hκ_le_half : B * (L / lam + (Cg * Rs + ε)) ≤ 1 / 2 := by
    have h1 : B * (L / lam) ≤ 1 / 4 := by
      have h4 : 4 * (B * (L / lam)) ≤ 1 := by
        rw [show 4 * (B * (L / lam)) = 4 * B * L / lam by ring]
        rw [div_le_one hlam_pos, hlam_def]
        linarith
      linarith
    have h2 : B * (Cg * Rs + ε) ≤ 1 / 4 := by
      have hRs_eq : Cg * Rs + ε = ε * (2 * B * Cg * M * EE + 1) := by
        rw [hRs_def, hRw_def]; ring
      rw [hRs_eq]
      have hden : 0 < 4 * B * (2 * B * Cg * M * EE + 1) := by positivity
      have hlt := (lt_div_iff₀ hden).mp hε3
      nlinarith [hlt]
    linarith
  have hκ_nonneg : 0 ≤ B * (L / lam + (Cg * Rs + ε)) := by
    have : 0 ≤ L / lam := div_nonneg hL hlam_nonneg
    have : 0 ≤ Cg * Rs + ε := by nlinarith [hCg, hRs_nonneg, hε.le]
    positivity
  have hκ_lt_one : B * (L / lam + (Cg * Rs + ε)) < 1 := lt_of_le_of_lt hκ_le_half (by norm_num)
  -- the weighted balls
  have hBall_closed : IsClosed {W : BoundedContinuousFunction (Set.Icc a b) E |
      wdist lam W 0 ≤ Rw} := isClosed_wdist_ball hlam_nonneg 0 Rw
  have hBall_ne : ({W : BoundedContinuousFunction (Set.Icc a b) E |
      wdist lam W 0 ≤ Rw}).Nonempty :=
    ⟨0, by
      show wdist lam (0 : BoundedContinuousFunction (Set.Icc a b) E) 0 ≤ Rw
      rw [wdist_self]; exact hRw_nonneg⟩
  have hsup0 : ∀ s : Set.Icc a b, ‖(0 : BoundedContinuousFunction (Set.Icc a b) E) s‖ ≤ Rs := by
    intro s; rw [h0fun s]; simpa using hRs_nonneg
  have hderV : ∀ s ∈ Set.Icc a b, ∀ z ∈ Metric.closedBall (Z₀ s) 1,
      ‖fderiv ℝ (fun w => G s w) z - (A s : E →L[ℝ] E)‖ ≤ Cg * ‖z - Z₀ s‖ + ε := hder
  have hmap : ∀ W ∈ {W : BoundedContinuousFunction (Set.Icc a b) E | wdist lam W 0 ≤ Rw},
      D.op W ∈ {W : BoundedContinuousFunction (Set.Icc a b) E | wdist lam W 0 ≤ Rw} := by
    intro W hW
    have h1 : wdist lam (D.op W) (D.op 0) ≤ (B * (L / lam + (Cg * Rs + ε))) *
        wdist lam W 0 := by
      rw [hDop]
      exact wdist_longOp_le D hlam_pos hL hCg hε.le hRs_nonneg hRs_le_one hAb hΘ_lip
        hdiff hderV (hsup W hW) hsup0
    have h2 : wdist lam (D.op 0) 0 ≤ B * M * ε := by
      have hGc' : ∀ s ∈ Set.Icc a b, dist (G s (Z₀ s)) (G0 s (Z₀ s)) < ε := by
        intro s hs
        exact hGc s hs (Z₀ s) (by rw [Metric.mem_closedBall]; simp)
      have hΘc' : ∀ s ∈ Set.Icc a b, ∀ σ ∈ Set.Icc a b,
          dist (Θ s σ (Z₀ σ)) (Θ0 s σ (Z₀ σ)) < ε := by
        intro s hs σ hσ
        exact hΘc s hs σ hσ (Z₀ σ) (by rw [Metric.mem_closedBall]; simp)
      have hΘc'' : ∀ s ∈ Set.Icc a b, ∀ σ ∈ Set.Icc a b,
          dist (D.Θ s σ (D.Z₀ σ)) (Θ0 s σ (D.Z₀ σ)) < ε := fun s hs σ hσ => hΘc' s hs σ hσ
      have := wdist_longOp_zero_le D (lam := lam) hlam_nonneg hε.le (B := B) hAb hΘ0_cont
        hbase hGc' hΘc'' hΞc
      rwa [← hM_def] at this
    have h3 := Work.VolterraLong.Weighted.wdist_triangle hlam_nonneg (D.op W) (D.op 0) 0
    have h4 : (B * (L / lam + (Cg * Rs + ε))) * wdist lam W 0 + B * M * ε ≤ Rw := by
      have h5 : (B * (L / lam + (Cg * Rs + ε))) * wdist lam W 0 ≤ (1 / 2) * Rw := by
        calc (B * (L / lam + (Cg * Rs + ε))) * wdist lam W 0
            ≤ (B * (L / lam + (Cg * Rs + ε))) * Rw :=
              mul_le_mul_of_nonneg_left hW hκ_nonneg
          _ ≤ (1 / 2) * Rw := mul_le_mul_of_nonneg_right hκ_le_half hRw_nonneg
      rw [hRw_def] at *
      linarith
    exact le_trans (le_trans h3 (add_le_add h1 h2)) h4
  have hcontr : ∀ W ∈ {W : BoundedContinuousFunction (Set.Icc a b) E | wdist lam W 0 ≤ Rw},
      ∀ V ∈ {W : BoundedContinuousFunction (Set.Icc a b) E | wdist lam W 0 ≤ Rw},
      wdist lam (D.op W) (D.op V) ≤ (B * (L / lam + (Cg * Rs + ε))) * wdist lam W V := by
    intro W hW V hV
    rw [hDop]
    exact wdist_longOp_le D hlam_pos hL hCg hε.le hRs_nonneg hRs_le_one hAb hΘ_lip
      hdiff hderV (hsup W hW) (hsup V hV)
  obtain ⟨W, hWmem, hWfix⟩ := exists_fixedPoint_of_weighted_contraction (wdist lam)
    (c := Real.exp (-(lam * (b - a)))) (κ := B * (L / lam + (Cg * Rs + ε)))
    (Real.exp_pos _) hκ_nonneg hκ_lt_one
    (fun x y => wdist_le_dist hlam_nonneg x y)
    (fun x y => exp_mul_dist_le_wdist hab hlam_nonneg x y)
    hBall_closed hBall_ne hmap hcontr
  have hfix : longOp hab A G Θ Ξ Z₀ hA_cont hG_cont hΘ_cont hΞ_cont hZ₀_cont W = W := by
    rw [hDop] at hWfix
    exact hWfix
  refine ⟨fun s => Z₀ s + bcfExt hab W s, ?_, ?_, ?_⟩
  · exact hZ₀_cont.add (bcfExt_continuous hab W).continuousOn
  · exact solvesOn_of_longOp_fixedPoint hab A G Θ Ξ Z₀ hA_cont hG_cont hΘ_cont hΞ_cont
      hZ₀_cont W hfix
  · intro s hs
    have h1 : ‖bcfExt hab W s‖ ≤ Rw * Real.exp (lam * (b - s)) := by
      rw [bcfExt_of_mem hab (Z := W) hs]
      have hWle : wdist lam W 0 ≤ Rw := hWmem
      have h2 : ‖W ⟨s, hs⟩ - (0 : BoundedContinuousFunction (Set.Icc a b) E) ⟨s, hs⟩‖ *
          Real.exp (-(lam * (b - s))) ≤ Rw :=
        le_trans (le_wdist hlam_nonneg W 0 ⟨s, hs⟩) hWle
      rw [h0fun ⟨s, hs⟩, sub_zero] at h2
      have hpos : 0 < Real.exp (lam * (b - s)) := Real.exp_pos _
      have h3 : ‖W ⟨s, hs⟩‖ * (Real.exp (lam * (b - s)))⁻¹ *
          Real.exp (lam * (b - s)) ≤ Rw * Real.exp (lam * (b - s)) := by
        rw [Real.exp_neg] at h2
        exact mul_le_mul_of_nonneg_right h2 (le_of_lt hpos)
      rwa [mul_assoc, inv_mul_cancel₀ (ne_of_gt hpos), mul_one] at h3
    calc dist (Z₀ s + bcfExt hab W s) (Z₀ s) = ‖bcfExt hab W s‖ := by
          rw [dist_eq_norm]
          congr 1
          abel
      _ ≤ Rw * Real.exp (lam * (b - s)) := h1
      _ ≤ Rw * EE := by
          apply mul_le_mul_of_nonneg_left _ hRw_nonneg
          rw [hEE_def]
          exact Real.exp_le_exp.mpr (by nlinarith [hlam_nonneg, hs.1])
      _ = 2 * B * M * EE * ε := by
          rw [hRw_def]
          ring

/-- **Long-interval existence for the Volterra system.**  There is a threshold
`ε₀ > 0` such that whenever the perturbed data is `ε`-close to the base data
(with `ε < ε₀`), the system `(★)` has a solution on the whole interval `[a,b]`,
`2 B (2 + (b-a)) e^{(4BL+1)(b-a)} ε`-close to `Z₀`.  No smallness of `b - a` is
required. -/
theorem volterra_long_exists {a b : ℝ} (hab : a ≤ b)
    (A : ℝ → E ≃L[ℝ] E) (G0 G : ℝ → E → E) (Θ0 Θ : ℝ → ℝ → E → E) (Ξ0 Ξ : ℝ → E)
    (Z₀ : ℝ → E) {B L Cg : ℝ} (hB : 0 < B) (hL : 0 ≤ L) (hCg : 0 ≤ Cg)
    (hA_spec : ∀ s ∈ Set.Icc a b, (A s : E →L[ℝ] E) = fderiv ℝ (fun z => G0 s z) (Z₀ s))
    (hA_cont : ContinuousOn (fun s => ((A s).symm : E →L[ℝ] E)) (Set.Icc a b))
    (hAb : ∀ s ∈ Set.Icc a b, ‖((A s).symm : E →L[ℝ] E)‖ ≤ B)
    (hG_cont : Continuous (fun p : ℝ × E => G p.1 p.2))
    (hΘ_cont : Continuous (fun p : ℝ × ℝ × E => Θ p.1 p.2.1 p.2.2))
    (hΞ_cont : Continuous Ξ)
    (hZ₀_cont : ContinuousOn Z₀ (Set.Icc a b))
    (hΘ0_cont : Continuous (fun p : ℝ × ℝ × E => Θ0 p.1 p.2.1 p.2.2))
    (hbase : ∀ s ∈ Set.Icc a b, G0 s (Z₀ s) = (∫ σ in s..b, Θ0 s σ (Z₀ σ)) + Ξ0 s)
    (hΘ_lip : ∀ s ∈ Set.Icc a b, ∀ σ ∈ Set.Icc a b, ∀ z ∈ Metric.closedBall (Z₀ σ) 1,
      ∀ z' ∈ Metric.closedBall (Z₀ σ) 1, ‖Θ s σ z - Θ s σ z'‖ ≤ L * ‖z - z'‖)
    (hdiff : ∀ s ∈ Set.Icc a b, ∀ z ∈ Metric.closedBall (Z₀ s) 1,
      DifferentiableAt ℝ (fun w => G s w) z) :
    ∃ ε₀ > 0, ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      (∀ s ∈ Set.Icc a b, dist (Ξ s) (Ξ0 s) < ε) →
      (∀ s ∈ Set.Icc a b, ∀ z ∈ Metric.closedBall (Z₀ s) 1, dist (G s z) (G0 s z) < ε) →
      (∀ s ∈ Set.Icc a b, ∀ σ ∈ Set.Icc a b, ∀ z ∈ Metric.closedBall (Z₀ σ) 1,
        dist (Θ s σ z) (Θ0 s σ z) < ε) →
      (∀ s ∈ Set.Icc a b, ∀ z ∈ Metric.closedBall (Z₀ s) 1,
        ‖fderiv ℝ (fun w => G s w) z - (A s : E →L[ℝ] E)‖ ≤ Cg * ‖z - Z₀ s‖ + ε) →
      ∃ Z : ℝ → E, ContinuousOn Z (Set.Icc a b) ∧ SolvesOn a b G Θ Ξ Z ∧
        (∀ s ∈ Set.Icc a b, dist (Z s) (Z₀ s) ≤ 2 * B * (2 + (b - a)) *
          Real.exp ((4 * B * L + 1) * (b - a)) * ε) := by
  refine ⟨min 1 (min (1 / (2 * B * (2 + (b - a)) *
        Real.exp ((4 * B * L + 1) * (b - a))))
      (1 / (4 * B * (2 * B * Cg * (2 + (b - a)) *
        Real.exp ((4 * B * L + 1) * (b - a)) + 1)))), ?_, ?_⟩
  · positivity
  · intro ε hε hε₀ hΞc hGc hΘc hder
    exact volterra_long_exists_eps hab A G0 G Θ0 Θ Ξ0 Ξ Z₀ hB hL hCg hA_spec hA_cont hAb
      hG_cont hΘ_cont hΞ_cont hZ₀_cont hΘ0_cont hbase hΘ_lip hdiff
      (4 * B * L + 1) (2 + (b - a)) (Real.exp ((4 * B * L + 1) * (b - a))) rfl rfl rfl
      hε (lt_of_lt_of_le hε₀ (min_le_left _ _))
      (lt_of_lt_of_le hε₀ (le_trans (min_le_right _ _) (min_le_left _ _)))
      (lt_of_lt_of_le hε₀ (le_trans (min_le_right _ _) (min_le_right _ _)))
      hΞc hGc hΘc hder

/-- The smallness condition of `volterra_long_exists` written out: with
`λ = 4 B L + 1`, `M = 2 + (b-a)` and `E = e^{λ(b-a)}` it suffices that
`ε < min 1 (min (1/(2 B M E)) (1/(4 B (2 B C_g M E + 1))))`. -/
theorem volterra_long_exists_explicit {a b : ℝ} (hab : a ≤ b)
    (A : ℝ → E ≃L[ℝ] E) (G0 G : ℝ → E → E) (Θ0 Θ : ℝ → ℝ → E → E) (Ξ0 Ξ : ℝ → E)
    (Z₀ : ℝ → E) {B L Cg : ℝ} (hB : 0 < B) (hL : 0 ≤ L) (hCg : 0 ≤ Cg)
    (hA_spec : ∀ s ∈ Set.Icc a b, (A s : E →L[ℝ] E) = fderiv ℝ (fun z => G0 s z) (Z₀ s))
    (hA_cont : ContinuousOn (fun s => ((A s).symm : E →L[ℝ] E)) (Set.Icc a b))
    (hAb : ∀ s ∈ Set.Icc a b, ‖((A s).symm : E →L[ℝ] E)‖ ≤ B)
    (hG_cont : Continuous (fun p : ℝ × E => G p.1 p.2))
    (hΘ_cont : Continuous (fun p : ℝ × ℝ × E => Θ p.1 p.2.1 p.2.2))
    (hΞ_cont : Continuous Ξ)
    (hZ₀_cont : ContinuousOn Z₀ (Set.Icc a b))
    (hΘ0_cont : Continuous (fun p : ℝ × ℝ × E => Θ0 p.1 p.2.1 p.2.2))
    (hbase : ∀ s ∈ Set.Icc a b, G0 s (Z₀ s) = (∫ σ in s..b, Θ0 s σ (Z₀ σ)) + Ξ0 s)
    (hΘ_lip : ∀ s ∈ Set.Icc a b, ∀ σ ∈ Set.Icc a b, ∀ z ∈ Metric.closedBall (Z₀ σ) 1,
      ∀ z' ∈ Metric.closedBall (Z₀ σ) 1, ‖Θ s σ z - Θ s σ z'‖ ≤ L * ‖z - z'‖)
    (hdiff : ∀ s ∈ Set.Icc a b, ∀ z ∈ Metric.closedBall (Z₀ s) 1,
      DifferentiableAt ℝ (fun w => G s w) z)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hε2 : ε < 1 / (2 * B * (2 + (b - a)) *
      Real.exp ((4 * B * L + 1) * (b - a))))
    (hε3 : ε < 1 / (4 * B * (2 * B * Cg * (2 + (b - a)) *
      Real.exp ((4 * B * L + 1) * (b - a)) + 1)))
    (hΞc : ∀ s ∈ Set.Icc a b, dist (Ξ s) (Ξ0 s) < ε)
    (hGc : ∀ s ∈ Set.Icc a b, ∀ z ∈ Metric.closedBall (Z₀ s) 1,
      dist (G s z) (G0 s z) < ε)
    (hΘc : ∀ s ∈ Set.Icc a b, ∀ σ ∈ Set.Icc a b, ∀ z ∈ Metric.closedBall (Z₀ σ) 1,
      dist (Θ s σ z) (Θ0 s σ z) < ε)
    (hder : ∀ s ∈ Set.Icc a b, ∀ z ∈ Metric.closedBall (Z₀ s) 1,
      ‖fderiv ℝ (fun w => G s w) z - (A s : E →L[ℝ] E)‖ ≤ Cg * ‖z - Z₀ s‖ + ε) :
    ∃ Z : ℝ → E, ContinuousOn Z (Set.Icc a b) ∧ SolvesOn a b G Θ Ξ Z ∧
      (∀ s ∈ Set.Icc a b, dist (Z s) (Z₀ s) ≤ 2 * B * (2 + (b - a)) *
        Real.exp ((4 * B * L + 1) * (b - a)) * ε) :=
  volterra_long_exists_eps hab A G0 G Θ0 Θ Ξ0 Ξ Z₀ hB hL hCg hA_spec hA_cont hAb
    hG_cont hΘ_cont hΞ_cont hZ₀_cont hΘ0_cont hbase hΘ_lip hdiff
    (4 * B * L + 1) (2 + (b - a)) (Real.exp ((4 * B * L + 1) * (b - a))) rfl rfl rfl
    hε hε1 (by simpa using hε2) (by simpa using hε3) hΞc hGc hΘc hder

end Work.VolterraLong
