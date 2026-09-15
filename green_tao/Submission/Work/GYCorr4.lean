import Submission.Work.GYCorr3

/-!
# Green–Tao §9 (Proposition GY2): the contour shift and the box-average main term

This file completes the transplantation of §10 to the correlation system: the pole-free vertical
shift `Γ_{bb} → Γ_a` of the `Ψ`-integrand, and the resulting identification of the box-average main
term (Green–Tao's estimate `(GY2-est)`).
-/

open Finset
open scoped BigOperators

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

namespace GYMaj
namespace Corr

open GYMaj.BoxAvg
open Commons.NumberTheory.Sieve
open Commons.Analysis.Complex

variable {m : ℕ}

/-! ## 1. Continuity and holomorphy of the correlation integrand -/

lemma continuousOn_Psi_corr {W : ℕ} {h : Fin m → ℤ} (hm : 1 ≤ m) (hW0 : 0 < W)
    (hΔ0 : Delta h ≠ 0) (R : ℕ) (hR0 : (R : ℂ) ≠ 0) {a bb : ℝ} (ha : 0 < a) :
    ContinuousOn (Function.uncurry (Psi (t := 1) R W (Ac m) h)) (stripPair (m := m) a bb) := by
  have hsub : stripPair (m := m) a bb ⊆ goodRegion m (-(1 / (6 * (m : ℝ)))) :=
    fun x hx => mem_goodRegion_of_strip hm ha hx
  have h12 : ContinuousOn (fun x : (Fin m → ℂ) × (Fin m → ℂ) =>
      G1u W (Ac m) h x.1 x.2 * G2u W x.1 x.2) (stripPair (m := m) a bb) :=
    ((continuousOn_G1c hm hW0 hΔ0).mono hsub).mul ((continuousOn_G2c hm hW0).mono hsub)
  exact (h12.mul (continuousOn_G3R_pair (m := m) ha)).mul
    (continuousOn_Ker_pair (m := m) ha hR0)

lemma differentiableAt_Psi_curve₁_corr {W : ℕ} {h : Fin m → ℤ} (hm : 1 ≤ m) (hW0 : 0 < W)
    (hΔ0 : Delta h ≠ 0) (R : ℕ) (hR0 : (R : ℂ) ≠ 0)
    {z z' : Fin m → ℂ} {j : Fin m} (hz : ∀ i, 0 < (z i).re) (hz' : ∀ i, 0 < (z' i).re) :
    DifferentiableAt ℂ (fun w : ℂ => Psi R W (Ac m) h (Function.update z j w) z') (z j) := by
  have hneg := neg_sixth_lt_zero hm
  have hz6 : ∀ i, -(1 / (6 * (m : ℝ))) < (z i).re := fun i => lt_trans hneg (hz i)
  have hz6' : ∀ i, -(1 / (6 * (m : ℝ))) < (z' i).re := fun i => lt_trans hneg (hz' i)
  have hs : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hmem : z j ∈ {w : ℂ | 0 < w.re} := hz j
  rw [show Psi R W (Ac m) h = fun z z' =>
      (G1u W (Ac m) h z z' * G2u W z z' * G3R z z') * Ker R z z' from rfl]
  exact (((differentiableAt_G1c_curve₁ hm hW0 hΔ0 hz6 hz6').mul
      (differentiableAt_G2c_curve₁ hm hW0 hz6 hz6')).mul
    ((differentiableOn_G3R_curve₁ hz hz').differentiableAt (hs.mem_nhds hmem))).mul
    ((differentiableOn_Ker_curve₁ hR0 hz hz').differentiableAt (hs.mem_nhds hmem))

lemma differentiableAt_Psi_curve₂_corr {W : ℕ} {h : Fin m → ℤ} (hm : 1 ≤ m) (hW0 : 0 < W)
    (hΔ0 : Delta h ≠ 0) (R : ℕ) (hR0 : (R : ℂ) ≠ 0)
    {z z' : Fin m → ℂ} {j : Fin m} (hz : ∀ i, 0 < (z i).re) (hz' : ∀ i, 0 < (z' i).re) :
    DifferentiableAt ℂ (fun w : ℂ => Psi R W (Ac m) h z (Function.update z' j w)) (z' j) := by
  have hneg := neg_sixth_lt_zero hm
  have hz6 : ∀ i, -(1 / (6 * (m : ℝ))) < (z i).re := fun i => lt_trans hneg (hz i)
  have hz6' : ∀ i, -(1 / (6 * (m : ℝ))) < (z' i).re := fun i => lt_trans hneg (hz' i)
  have hs : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hmem : z' j ∈ {w : ℂ | 0 < w.re} := hz' j
  rw [show Psi R W (Ac m) h = fun z z' =>
      (G1u W (Ac m) h z z' * G2u W z z' * G3R z z') * Ker R z z' from rfl]
  exact (((differentiableAt_G1c_curve₂ hm hW0 hΔ0 hz6 hz6').mul
      (differentiableAt_G2c_curve₂ hm hW0 hz6 hz6')).mul
    ((differentiableOn_G3R_curve₂ hz hz').differentiableAt (hs.mem_nhds hmem))).mul
    ((differentiableOn_Ker_curve₂ hR0 hz hz').differentiableAt (hs.mem_nhds hmem))

/-! ## 2. The `g`-bound on the strip -/

/-- The constant `Cg` of the vertical-shift bound for the correlation system. -/
noncomputable def shiftBoundCorr (D R W m : ℕ) (a bb : ℝ) : ℝ :=
  stripBoundCorr D W m * ((R : ℝ) ^ (2 * bb)) ^ m
    * ((riemannZeta ((1 + 2 * a : ℝ) : ℂ)).re
      * (riemannZeta ((1 + a : ℝ) : ℂ)).re * (riemannZeta ((1 + a : ℝ) : ℂ)).re) ^ m

lemma shiftBoundCorr_nonneg {D R W m : ℕ} {a bb : ℝ}
    (hZ1 : 0 ≤ (riemannZeta ((1 + a : ℝ) : ℂ)).re)
    (hZ2 : 0 ≤ (riemannZeta ((1 + 2 * a : ℝ) : ℂ)).re) :
    0 ≤ shiftBoundCorr D R W m a bb := by
  rw [shiftBoundCorr]
  have hc : 0 ≤ (riemannZeta ((1 + 2 * a : ℝ) : ℂ)).re
      * (riemannZeta ((1 + a : ℝ) : ℂ)).re * (riemannZeta ((1 + a : ℝ) : ℂ)).re :=
    mul_nonneg (mul_nonneg hZ2 hZ1) hZ1
  have hSB : 0 ≤ stripBoundCorr D W m := by rw [stripBoundCorr]; positivity
  exact mul_nonneg (mul_nonneg hSB (by positivity)) (pow_nonneg hc m)

lemma norm_Psi_le_corr {a bb : ℝ} (ha : 0 < a) {W : ℕ} {h : Fin m → ℤ} (hm : 1 ≤ m)
    (hW0 : 0 < W) (hΔ0 : Delta h ≠ 0) {R : ℕ} (hR : 1 ≤ R) {z z' : Fin m → ℂ}
    (hz : ∀ i, a ≤ (z i).re ∧ (z i).re ≤ bb)
    (hz' : ∀ i, a ≤ (z' i).re ∧ (z' i).re ≤ bb) :
    ‖Psi R W (Ac m) h z z'‖ ≤ shiftBoundCorr (Delta h) R W m a bb
      * (∏ i, shiftWeight a ((z i).im)) * (∏ i, shiftWeight a ((z' i).im)) := by
  have hR1 : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  have hZ1 : 0 ≤ (riemannZeta ((1 + a : ℝ) : ℂ)).re :=
    le_of_lt (Commons.NumberTheory.Zeta.re_riemannZeta_ofReal_pos (σ := 1 + a) (by linarith))
  have hZ2 : 0 ≤ (riemannZeta ((1 + 2 * a : ℝ) : ℂ)).re :=
    le_of_lt (Commons.NumberTheory.Zeta.re_riemannZeta_ofReal_pos (σ := 1 + 2 * a) (by linarith))
  have hc : 0 ≤ (riemannZeta ((1 + 2 * a : ℝ) : ℂ)).re
      * (riemannZeta ((1 + a : ℝ) : ℂ)).re * (riemannZeta ((1 + a : ℝ) : ℂ)).re :=
    mul_nonneg (mul_nonneg hZ2 hZ1) hZ1
  have hE : 0 ≤ Real.exp (∑' n : ℕ, e1pMajorCorr (Delta h) m n) := Real.exp_nonneg _
  have hD : 0 ≤ (32 : ℝ) ^ (m * W.divisors.card) := by positivity
  have hSE : (0 : ℝ) ≤ stripBoundCorr (Delta h) W m := by rw [stripBoundCorr]; positivity
  have hprod : (∏ i, (a ^ 2 + (z i).im ^ 2)⁻¹) ≤ ∏ i, shiftWeight a ((z i).im) :=
    Finset.prod_le_prod (fun i _ => by positivity) (fun i _ => inv_sq_le_shiftWeight ha _)
  have hprod' : (∏ i, (a ^ 2 + (z' i).im ^ 2)⁻¹) ≤ ∏ i, shiftWeight a ((z' i).im) :=
    Finset.prod_le_prod (fun i _ => by positivity) (fun i _ => inv_sq_le_shiftWeight ha _)
  have hSB := shiftBoundCorr_nonneg (D := Delta h) (R := R) (W := W) (m := m) (bb := bb) hZ1 hZ2
  have hneg : -(1 / (6 * (m : ℝ))) < 0 := neg_sixth_lt_zero hm
  have hz6 : ∀ i, -(1 / (6 * (m : ℝ))) ≤ (z i).re :=
    fun i => le_of_lt (lt_trans hneg (lt_of_lt_of_le ha (hz i).1))
  have hz6' : ∀ i, -(1 / (6 * (m : ℝ))) ≤ (z' i).re :=
    fun i => le_of_lt (lt_trans hneg (lt_of_lt_of_le ha (hz' i).1))
  have hstep := norm_G1c_le (z := z) (z' := z') hm hW0 hΔ0 hz6 hz6'
  have hstep2 := norm_G2c_le (z := z) (z' := z') hm hW0 hz6 hz6'
  have hstep3 := norm_G3R_le (m := m) (z := z) (z' := z') ha (fun i => (hz i).1) (fun i => (hz' i).1)
  have hstep4 := norm_Ker_le (m := m) (z := z) (z' := z') ha (by omega : 0 < R) hz hz'
  calc ‖Psi R W (Ac m) h z z'‖
      ≤ (Real.exp (∑' n : ℕ, e1pMajorCorr (Delta h) m n) * (32 : ℝ) ^ (m * W.divisors.card)
            * (∏ _j : Fin m, ((riemannZeta ((1 + 2 * a : ℝ) : ℂ)).re
              * (riemannZeta ((1 + a : ℝ) : ℂ)).re * (riemannZeta ((1 + a : ℝ) : ℂ)).re)))
          * (((R : ℝ) ^ (2 * bb)) ^ m
            * (∏ i, (a ^ 2 + (z i).im ^ 2)⁻¹) * (∏ i, (a ^ 2 + (z' i).im ^ 2)⁻¹)) := by
        rw [Psi, norm_mul, norm_mul, norm_mul]
        refine mul_le_mul (mul_le_mul (mul_le_mul hstep hstep2 (norm_nonneg _) hE) hstep3
          (norm_nonneg _) (mul_nonneg hE hD)) hstep4 (by positivity)
          (mul_nonneg (mul_nonneg hE hD) (Finset.prod_nonneg fun j _ => hc))
    _ = shiftBoundCorr (Delta h) R W m a bb * (∏ i, (a ^ 2 + (z i).im ^ 2)⁻¹)
          * (∏ i, (a ^ 2 + (z' i).im ^ 2)⁻¹) := by
        rw [shiftBoundCorr, stripBoundCorr, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        ring
    _ ≤ shiftBoundCorr (Delta h) R W m a bb * (∏ i, shiftWeight a ((z i).im))
          * (∏ i, shiftWeight a ((z' i).im)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hprod hSB) hprod'
          (Finset.prod_nonneg fun i _ => by positivity)
          (mul_nonneg hSB (Finset.prod_nonneg fun i _ => shiftWeight_nonneg ha _))

/-! ## 3. The vertical shift -/

theorem contourShift_Psi_corr {W : ℕ} {h : Fin m → ℤ} (hm : 1 ≤ m) (hW0 : 0 < W)
    (hΔ0 : Delta h ≠ 0) {R : ℕ} (hR : 3 ≤ R) {a bb : ℝ} (ha : 0 < a) (hab : a ≤ bb) :
    (∫ t : Fin m → ℝ, ∫ t' : Fin m → ℝ,
        Psi R W (Ac m) h (fun i => sline bb (t i)) (fun i => sline bb (t' i)))
      = ∫ t : Fin m → ℝ, ∫ t' : Fin m → ℝ,
        Psi R W (Ac m) h (fun i => sline a (t i)) (fun i => sline a (t' i)) := by
  have hRpos : 0 < R := by omega
  have hR1 : 1 ≤ R := by omega
  have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hRpos)
  have hZ1 : 0 ≤ (riemannZeta ((1 + a : ℝ) : ℂ)).re :=
    le_of_lt (Commons.NumberTheory.Zeta.re_riemannZeta_ofReal_pos (σ := 1 + a) (by linarith))
  have hZ2 : 0 ≤ (riemannZeta ((1 + 2 * a : ℝ) : ℂ)).re :=
    le_of_lt (Commons.NumberTheory.Zeta.re_riemannZeta_ofReal_pos (σ := 1 + 2 * a) (by linarith))
  exact (integral_vertical_shift_pair (m := m) hab (Psi R W (Ac m) h)
    (shiftBoundCorr_nonneg (D := Delta h) (R := R) (W := W) (m := m) (bb := bb) hZ1 hZ2)
    (shiftWeight_nonneg ha)
    (Commons.Analysis.Integral.integrable_tendsto_log_inv_sq ha).1
    (Commons.Analysis.Integral.integrable_tendsto_log_inv_sq ha).2.1
    (Commons.Analysis.Integral.integrable_tendsto_log_inv_sq ha).2.2
    (fun z z' hz hz' => norm_Psi_le_corr ha hm hW0 hΔ0 hR1 hz hz')
    (continuousOn_Psi_corr hm hW0 hΔ0 R hRc ha)
    (fun j z z' hz hz' => differentiableAt_Psi_curve₁_corr hm hW0 hΔ0 R hRc
      (fun i => lt_of_lt_of_le ha (hz i).1) (fun i => lt_of_lt_of_le ha (hz' i).1))
    (fun j z z' hz hz' => differentiableAt_Psi_curve₂_corr hm hW0 hΔ0 R hRc
      (fun i => lt_of_lt_of_le ha (hz i).1) (fun i => lt_of_lt_of_le ha (hz' i).1))).symm

/-- On `Re = c > 1` the integrand `Eker` is the shifted integrand `Psi` (correlation system). -/
lemma Eker_eq_Psi_corr {c : ℝ} (hc : 1 < c) {W : ℕ} {h : Fin m → ℤ} (hm : 1 ≤ m) (hW0 : 0 < W)
    (hΔ0 : Delta h ≠ 0) (R : ℕ) (p : Fin m → ℝ × ℝ) :
    Eker (t := 1) c R W (Ac m) h p
      = Psi R W (Ac m) h (fun i => sline c ((p i).1)) (fun i => sline c ((p i).2)) := by
  have hz : ∀ j, 1 < (sline c ((p j).1)).re := fun j => by simpa [sline] using hc
  have hz' : ∀ j, 1 < (sline c ((p j).2)).re := fun j => by simpa [sline] using hc
  rw [Eker, Psi, tprod_eulerFactor_eq_corr hm hW0 hΔ0 (z := fun i => sline c ((p i).1))
    (z' := fun i => sline c ((p i).2)) hz hz']

/-- The integrand of the shifted contour. -/
lemma Psi_mul_I_eq_corr {W : ℕ} {h : Fin m → ℤ} {R : ℕ} (hRc : (R : ℂ) ≠ 0) {a : ℝ}
    (t t' : Fin m → ℝ) :
    Psi R W (Ac m) h (fun i => sline a (t i)) (fun i => sline a (t' i))
        * (Complex.I ^ m * Complex.I ^ m)
      = ((G1u W (Ac m) h (fun j => sline a (t j)) (fun j => sline a (t' j))
              * G2u W (fun j => sline a (t j)) (fun j => sline a (t' j)))
          * (∏ j, (riemannZeta (1 + sline a (t j) + sline a (t' j))
              / (riemannZeta (1 + sline a (t j)) * riemannZeta (1 + sline a (t' j)))))
          * (((R : ℝ)) : ℂ) ^ (∑ j, (sline a (t j) + sline a (t' j)))
          * (∏ j, ((sline a (t j)) ^ 2 * (sline a (t' j)) ^ 2)⁻¹))
        * Complex.I ^ m * Complex.I ^ m := by
  simp only [Psi, Ker_eq (m := m) hRc, G3R, zetaM1Eta_eq_sline, Complex.ofReal_natCast]
  ring

/-! ## 4. Green–Tao (10.2) = (GY2-est) for the degenerate system -/

/-- **The box-average main term of the correlation system.** -/
theorem mainSum_eq_logR_corr {W : ℕ} {h : Fin m → ℤ} (hm : 1 ≤ m) (hW0 : 0 < W)
    (hΔ0 : Delta h ≠ 0) {R : ℕ} (hR : 3 ≤ R) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧
      ‖(mainSum (m := m) (t := 1) R W (Ac m) h : ℂ)
          - (G1u W (Ac m) h 0 0 * G2u (m := m) W 0 0) * (Real.log (R : ℝ)) ^ m‖
        ≤ C ^ m * stripBoundCorr (Delta h) W m * (1 + (Real.log (R : ℝ)) ^ (m - 1))
          + C ^ m * stripBoundCorr (Delta h) W m
              * Real.exp (-(δ * Real.sqrt (Real.log (R : ℝ)))) := by
  obtain ⟨δ, C, hδ, hC, hmain⟩ := zetaBound_G1G2_corr (m := m) hm hW0 hΔ0
  refine ⟨δ, C, hδ, hC, ?_⟩
  have hR1 : (1 : ℝ) < (R : ℝ) := by exact_mod_cast (by omega : 1 < R)
  have hlog : 0 < Real.log (R : ℝ) := Real.log_pos hR1
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlog3one : (1 : ℝ) < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)]
    exact Real.exp_one_lt_three
  have ha : 0 < 1 / Real.log (R : ℝ) := by positivity
  have hlogle : Real.log 3 ≤ Real.log (R : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hR)
  have hab : 1 / Real.log (R : ℝ) ≤ 1 + (m : ℝ) := by
    have h1 : 1 / Real.log (R : ℝ) ≤ 1 / Real.log 3 :=
      one_div_le_one_div_of_le hlog3 hlogle
    have h2 : 1 / Real.log 3 ≤ 1 := by
      rw [div_le_one hlog3]; exact le_of_lt hlog3one
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (by omega : 0 < R))
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hc1m : (1 : ℝ) < 1 + (m : ℝ) := by linarith
  have hmain' := hmain (R : ℝ) (by exact_mod_cast hR)
  rw [mainSum_eq_contour (m := m) (t := 1) hm (c := 1 + (m : ℝ)) (by linarith) R W (Ac m) h
      le_rfl (Ac_natAbs_le m) (Ac_ne_zero m) hW0, ContourInt_eq]
  rw [show (∫ t_ : Fin m → ℝ, ∫ t_' : Fin m → ℝ,
        Eker (t := 1) (1 + (m : ℝ)) R W (Ac m) h (fun i => (t_ i, t_' i)))
      = ∫ t_ : Fin m → ℝ, ∫ t_' : Fin m → ℝ,
        Psi R W (Ac m) h (fun i => sline (1 + (m : ℝ)) (t_ i))
          (fun i => sline (1 + (m : ℝ)) (t_' i)) by
    simp_rw [Eker_eq_Psi_corr hc1m hm hW0 hΔ0]]
  rw [show (∫ t_ : Fin m → ℝ, ∫ t_' : Fin m → ℝ,
        Psi R W (Ac m) h (fun i => sline (1 + (m : ℝ)) (t_ i))
          (fun i => sline (1 + (m : ℝ)) (t_' i)))
      = ∫ t_ : Fin m → ℝ, ∫ t_' : Fin m → ℝ,
        Psi R W (Ac m) h (fun i => sline (1 / Real.log (R : ℝ)) (t_ i))
          (fun i => sline (1 / Real.log (R : ℝ)) (t_' i)) from
    contourShift_Psi_corr hm hW0 hΔ0 hR ha hab]
  simp_rw [← MeasureTheory.integral_mul_const]
  have hI : (∫ t_ : Fin m → ℝ, ∫ t_' : Fin m → ℝ,
        Psi R W (Ac m) h (fun i => sline (1 / Real.log (R : ℝ)) (t_ i))
          (fun i => sline (1 / Real.log (R : ℝ)) (t_' i)) * (Complex.I ^ m * Complex.I ^ m))
      = (∫ t_ : Fin m → ℝ, ∫ t_' : Fin m → ℝ,
          (G1u W (Ac m) h (fun j => Commons.NumberTheory.Zeta.zetaM1Eta (R : ℝ) (t_ j))
              (fun j => Commons.NumberTheory.Zeta.zetaM1Eta (R : ℝ) (t_' j))
            * G2u W (fun j => Commons.NumberTheory.Zeta.zetaM1Eta (R : ℝ) (t_ j))
              (fun j => Commons.NumberTheory.Zeta.zetaM1Eta (R : ℝ) (t_' j)))
          * (∏ j, (riemannZeta (1 + Commons.NumberTheory.Zeta.zetaM1Eta (R : ℝ) (t_ j)
                + Commons.NumberTheory.Zeta.zetaM1Eta (R : ℝ) (t_' j))
              / (riemannZeta (1 + Commons.NumberTheory.Zeta.zetaM1Eta (R : ℝ) (t_ j))
                  * riemannZeta (1 + Commons.NumberTheory.Zeta.zetaM1Eta (R : ℝ) (t_' j)))))
          * (((R : ℝ)) : ℂ) ^ (∑ j, (Commons.NumberTheory.Zeta.zetaM1Eta (R : ℝ) (t_ j)
              + Commons.NumberTheory.Zeta.zetaM1Eta (R : ℝ) (t_' j)))
          * (∏ j, ((Commons.NumberTheory.Zeta.zetaM1Eta (R : ℝ) (t_ j)) ^ 2
                * (Commons.NumberTheory.Zeta.zetaM1Eta (R : ℝ) (t_' j)) ^ 2)⁻¹)
          * Complex.I ^ m * Complex.I ^ m) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t_ => ?_)
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t_' => ?_)
    exact Psi_mul_I_eq_corr hRc t_ t_'
  rw [hI]
  exact hmain'

end Corr
end GYMaj
