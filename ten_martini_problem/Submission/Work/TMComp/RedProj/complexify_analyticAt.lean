import Mathlib
import Submission.Work.TMComp.RedProj.complexify_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Complexifying a real-analytic function of two real variables

Given `f : ℝ × ℝ → ℂ` real-analytic at `x₀`, we produce a complex-analytic `F : ℂ × ℂ → ℂ` on a
neighbourhood of `(x₀.1, x₀.2)` agreeing with `f` on the real points.

The construction is the standard one: if `p` is the formal multilinear series of `f` at `x₀`, its
complexification `cplxify p` (defined in `complexify_defs.lean` as the unique `ℂ`-multilinear
extension of each `p n`, written out in the basis) has positive radius of convergence, and its sum
`F` is the desired extension.
-/

namespace Work.TMComp.RedProj

open FormalMultilinearSeries

open scoped NNReal ENNReal

noncomputable section

/-- The complex coordinate functionals, read on the image of `toCplx`, give the coercions of the
real coordinate functionals. -/
theorem coordC_toCplx (j : Fin 2) (z : ℝ × ℝ) :
    coordC j (toCplx z) = (coordR j z : ℂ) := by
  fin_cases j <;> simp [coordC, coordR, toCplx]

/-- The `ℂ`-module structure on `ℂ` restricted to real scalars agrees with `Complex.real_smul`. -/
theorem ofReal_smul_eq (a : ℝ) (z : ℂ) : (a : ℂ) • z = a • z := by
  rw [Complex.real_smul, smul_eq_mul]

/-- The basis expansion of an `ℝ`-multilinear map on `(ℝ × ℝ)^n`. -/
theorem apply_eq_sum_basis (p : FormalMultilinearSeries ℝ (ℝ × ℝ) ℂ) (n : ℕ)
    (y : Fin n → ℝ × ℝ) :
    p n y = ∑ r : Fin n → Fin 2,
      (∏ i, coordR (r i) (y i)) • p n (fun i => basisVec (r i)) := by
  conv_lhs => rw [show y = (fun i => ∑ j : Fin 2, coordR j (y i) • basisVec j) from
    funext fun i => (sum_coordR_smul_basisVec (y i)).symm]
  rw [ContinuousMultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [ContinuousMultilinearMap.map_smul_univ]

/-- `cplxify p n` restricts to `p n` on tuples of real vectors. -/
theorem cplxify_apply_real (p : FormalMultilinearSeries ℝ (ℝ × ℝ) ℂ) (n : ℕ)
    (y : Fin n → ℝ × ℝ) :
    cplxify p n (fun i => toCplx (y i)) = p n y := by
  rw [cplxify_apply, apply_eq_sum_basis]
  refine Finset.sum_congr rfl fun r _ => ?_
  have h1 : (∏ i, coordC (r i) (toCplx (y i))) =
      (∏ i, ((coordR (r i) (y i) : ℝ) : ℂ)) :=
    Finset.prod_congr rfl fun i _ => coordC_toCplx (r i) (y i)
  rw [h1, ← Complex.ofReal_prod (s := Finset.univ) (f := fun i => coordR (r i) (y i)),
    ofReal_smul_eq]

/-- The coordinate projections of `ℂ × ℂ` have norm at most `1`. -/
theorem norm_coordC_le (j : Fin 2) (w : ℂ × ℂ) : ‖coordC j w‖ ≤ ‖w‖ := by
  fin_cases j
  · simpa using norm_fst_le w
  · simpa using norm_snd_le w

/-- The basis vectors of `ℝ × ℝ` have norm `1`. -/
theorem norm_basisVec (j : Fin 2) : ‖basisVec j‖ = 1 := by
  fin_cases j <;> simp [basisVec]

/-- Norm bound on the complexified coefficients. -/
theorem norm_cplxify_le (p : FormalMultilinearSeries ℝ (ℝ × ℝ) ℂ) (n : ℕ) :
    ‖cplxify p n‖ ≤ (2 : ℝ) ^ n * ‖p n‖ := by
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun v => ?_
  rw [cplxify_apply]
  calc ‖∑ r : Fin n → Fin 2, (∏ i, coordC (r i) (v i)) • p n (fun i => basisVec (r i))‖
      ≤ ∑ r : Fin n → Fin 2,
          ‖(∏ i, coordC (r i) (v i)) • p n (fun i => basisVec (r i))‖ := norm_sum_le _ _
    _ ≤ ∑ _r : Fin n → Fin 2, (∏ i, ‖v i‖) * ‖p n‖ := by
        refine Finset.sum_le_sum fun r _ => ?_
        calc ‖(∏ i, coordC (r i) (v i)) • p n (fun i => basisVec (r i))‖
            = (∏ i, ‖coordC (r i) (v i)‖) * ‖p n (fun i => basisVec (r i))‖ := by
              rw [norm_smul, norm_prod]
          _ ≤ (∏ i, ‖v i‖) * ‖p n‖ := by
              have hc : (∏ i, ‖coordC (r i) (v i)‖) ≤ ∏ i, ‖v i‖ :=
                Finset.prod_le_prod₀ (fun i _ => norm_nonneg _)
                  (fun i _ => norm_coordC_le (r i) (v i))
              have hb : ‖p n (fun i => basisVec (r i))‖ ≤ ‖p n‖ := by
                calc ‖p n (fun i => basisVec (r i))‖
                    ≤ ‖p n‖ * ∏ i : Fin n, ‖basisVec (r i)‖ :=
                      ContinuousMultilinearMap.le_opNorm _ _
                  _ = ‖p n‖ := by simp [norm_basisVec]
              exact mul_le_mul hc hb (norm_nonneg _) (by positivity)
    _ = ((Fintype.card (Fin n → Fin 2) : ℕ) : ℝ) * ((∏ i, ‖v i‖) * ‖p n‖) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = (2 : ℝ) ^ n * ‖p n‖ * ∏ i, ‖v i‖ := by
        have hcard : Fintype.card (Fin n → Fin 2) = 2 ^ n := by
          rw [Fintype.card_fun]; simp
        rw [hcard]
        push_cast
        ring

/-- Halving the radius of `p` gives a valid radius for `cplxify p`. -/
theorem cplxify_radius (p : FormalMultilinearSeries ℝ (ℝ × ℝ) ℂ) {ρ : ℝ≥0}
    (hρ : (ρ : ℝ≥0∞) < p.radius) :
    ((ρ / 2 : ℝ≥0) : ℝ≥0∞) ≤ (cplxify p).radius := by
  obtain ⟨a, ha, C, hC, hp⟩ := p.norm_mul_pow_le_mul_pow_of_lt_radius hρ
  refine FormalMultilinearSeries.le_radius_of_bound (cplxify p) C fun n => ?_
  have hc : ((ρ / 2 : ℝ≥0) : ℝ) = (ρ : ℝ) / 2 := by
    rw [NNReal.coe_div]; norm_num
  calc ‖cplxify p n‖ * ((ρ / 2 : ℝ≥0) : ℝ) ^ n
      ≤ (‖p n‖ * (2 : ℝ) ^ n) * ((ρ / 2 : ℝ≥0) : ℝ) ^ n := by
        have h := norm_cplxify_le p n
        rw [mul_comm] at h
        exact mul_le_mul_of_nonneg_right h (by positivity)
    _ = ‖p n‖ * (ρ : ℝ) ^ n := by
        have h2 : (2 : ℝ) ^ n * ((ρ : ℝ) / 2) ^ n = (ρ : ℝ) ^ n := by
          rw [← mul_pow]
          rw [show (2 : ℝ) * ((ρ : ℝ) / 2) = (ρ : ℝ) by ring]
        rw [hc, mul_assoc, h2]
    _ ≤ C * a ^ n := hp n
    _ ≤ C := by
        have ha1 : a ^ n ≤ 1 := pow_le_one₀ ha.1.le ha.2.le
        calc C * a ^ n ≤ C * 1 := by gcongr
          _ = C := mul_one C

theorem complexify_analyticAt (f : ℝ × ℝ → ℂ) (x₀ : ℝ × ℝ) (hf : AnalyticAt ℝ f x₀) :
    ∃ (r : ℝ) (_ : 0 < r) (F : ℂ × ℂ → ℂ),
      AnalyticOnNhd ℂ F (Metric.ball ((x₀.1 : ℂ), (x₀.2 : ℂ)) r) ∧
      (∀ x : ℝ × ℝ, x ∈ Metric.ball x₀ r → F ((x.1 : ℂ), (x.2 : ℂ)) = f x) := by
  obtain ⟨p, R, hR⟩ := hf
  -- a positive real radius strictly below `R`
  obtain ⟨ρ, hρpos, hρR⟩ : ∃ ρ : ℝ≥0, 0 < ρ ∧ (ρ : ℝ≥0∞) < R := by
    obtain ⟨ρ, h1, h2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hR.r_pos
    exact ⟨ρ, ENNReal.coe_pos.mp h1, h2⟩
  have hρrad : (ρ : ℝ≥0∞) < p.radius := lt_of_lt_of_le hρR hR.r_le
  have hqrad : ((ρ / 2 : ℝ≥0) : ℝ≥0∞) ≤ (cplxify p).radius := cplxify_radius p hρrad
  have hqpos : 0 < (cplxify p).radius :=
    lt_of_lt_of_le (by rw [ENNReal.coe_pos]; exact div_pos hρpos (by norm_num)) hqrad
  set z₀ : ℂ × ℂ := ((x₀.1 : ℂ), (x₀.2 : ℂ)) with hz0
  set δ : ℝ := ((ρ / 2 : ℝ≥0) : ℝ) with hδ
  have hδpos : 0 < δ := by rw [hδ]; positivity
  set F : ℂ × ℂ → ℂ := fun z => (cplxify p).sum (z - z₀) with hF
  refine ⟨δ, hδpos, F, ?_, ?_⟩
  · -- analyticity of `F` near `z₀`
    have hpack : HasFPowerSeriesOnBall (fun z : ℂ × ℂ => (cplxify p).sum (z - z₀))
        (cplxify p) (0 + z₀) (cplxify p).radius :=
      (FormalMultilinearSeries.hasFPowerSeriesOnBall (cplxify p) hqpos).comp_sub z₀
    rw [zero_add] at hpack
    have hδrad : ENNReal.ofReal δ ≤ (cplxify p).radius := by
      rw [hδ, ENNReal.ofReal_coe_nnreal]; exact hqrad
    have hball : Metric.ball z₀ δ ⊆ Metric.eball z₀ (cplxify p).radius :=
      calc Metric.ball z₀ δ = Metric.eball z₀ (ENNReal.ofReal δ) := by rw [Metric.eball_ofReal]
        _ ⊆ Metric.eball z₀ (cplxify p).radius := Metric.eball_subset_eball hδrad
    rw [hF]
    exact hpack.analyticOnNhd.mono hball
  · -- agreement on real points
    intro x hx
    rw [Metric.mem_ball] at hx
    set y : ℝ × ℝ := x - x₀ with hy
    have hw : ((x.1 : ℂ), (x.2 : ℂ)) - z₀ = toCplx y := by
      rw [hz0, hy]
      ext <;> simp [toCplx]
    have hxR : y ∈ Metric.eball (0 : ℝ × ℝ) R := by
      rw [hy, Metric.mem_eball]
      have e : edist (x - x₀) 0 = ENNReal.ofReal (dist x x₀) := by
        simp only [edist_dist, dist_eq_norm, sub_zero]
      rw [e]
      have h1 : ENNReal.ofReal (dist x x₀) < ENNReal.ofReal δ :=
        (ENNReal.ofReal_lt_ofReal_iff hδpos).2 hx
      have h2 : ENNReal.ofReal δ < R := by
        have h3 : ENNReal.ofReal δ = ((ρ / 2 : ℝ≥0) : ℝ≥0∞) := by
          rw [hδ, ENNReal.ofReal_coe_nnreal]
        rw [h3]
        exact lt_of_lt_of_le
          (ENNReal.coe_lt_coe.mpr (NNReal.half_lt_self (ne_of_gt hρpos))) hρR.le
      exact lt_trans h1 h2
    have hL : F ((x.1 : ℂ), (x.2 : ℂ)) = ∑' n : ℕ, p n (fun _ => y) := by
      simp only [hF]
      change (∑' n : ℕ, (cplxify p) n (fun _ => ((x.1 : ℂ), (x.2 : ℂ)) - z₀)) =
        ∑' n : ℕ, p n (fun _ => y)
      rw [hw]
      exact tsum_congr fun n => cplxify_apply_real p n (fun _ => y)
    have hRr : f x = ∑' n : ℕ, p n (fun _ => y) := by
      have hs : (∑' n : ℕ, p n (fun _ => y)) = f (x₀ + y) := (hR.hasSum hxR).tsum_eq
      have hxy : x₀ + y = x := by rw [hy]; abel
      rw [hxy] at hs
      exact hs.symm
    exact hL.trans hRr.symm

end

end Work.TMComp.RedProj
