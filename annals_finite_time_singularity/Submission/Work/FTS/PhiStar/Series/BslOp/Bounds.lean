import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PhiStar.Series.BslOp.Setup

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Series

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- **The six pointwise bounds on the mode terms.**  From the angular bounds `hAng`, the coefficient
decay `hDec`, the radial bounds `hGamma` and the arithmetic of `hterm`, every differentiated mode
term is dominated by a fixed multiple of the majorant `majPow`. -/
theorem mode_bounds (α : ℝ) (ψ : ℝ → ℝ) (hα : 0 < α)
    (hmom : (∫ θ in Work.Spaces.Iθ, ψ θ * Work.Elliptic.sinCos2 θ) = 0)
    (hAng : ∀ m : ℕ, ∀ θ : ℝ, θ ∈ Set.Ioo 0 (π / 2) →
      |Gegenbauer.eFam m θ| ≤ Real.sqrt ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) ∧
      |deriv (Gegenbauer.eFam m) θ|
        ≤ 100 * ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) / (Real.cos θ) ^ 2 ∧
      |iteratedDeriv 2 (Gegenbauer.eFam m) θ|
        ≤ 1000 * ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3))
            * Real.sqrt ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) / (Real.cos θ) ^ 4 ∧
      |deriv (fun θ' => Real.tan θ' * Gegenbauer.eFam m θ') θ|
        ≤ 1000 * ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) / (Real.cos θ) ^ 3)
    (hDec : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      |bmode m ψ| ≤ C / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
    (hGamma : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m → ∀ k : ℕ, k ≤ 2 → ∀ z : ℝ, 0 < z →
      |iteratedDeriv k (gammaFun α m) z| ≤ C / Gegenbauer.lam m)
    (hInt : (∀ m : ℕ, ContinuousOn (fun t => cmode m (RemSource α ψ) t) (Set.Ioi 0)) ∧
      (∀ m : ℕ, MeasureTheory.IntegrableOn
        (fun t => cmode m (RemSource α ψ) t * t ^ ((2 * (m : ℝ) + 5) / α - 1))
        (Set.Ioo 0 1)) ∧
      (∀ m : ℕ, MeasureTheory.IntegrableOn
        (fun t => cmode m (RemSource α ψ) t * t ^ (-(2 * (m : ℝ) / α) - 1))
        (Set.Ioi 1)) ∧
      ContinuousOn (VocabO.phiA α) (Set.Ioi 0) ∧
      (∀ m : ℕ, MeasureTheory.IntegrableOn
        (fun t => VocabO.phiA α t * t ^ ((2 * (m : ℝ) + 5) / α - 1)) (Set.Ioo 0 1)) ∧
      (∀ m : ℕ, MeasureTheory.IntegrableOn
        (fun t => VocabO.phiA α t * t ^ (-(2 * (m : ℝ) / α) - 1)) (Set.Ioi 1)))
    (hterm : ∀ (Cdec CBz Kφ : ℝ), 0 < Cdec → 0 < CBz → 0 < Kφ → ∀ cθ : ℝ, 0 < cθ →
      ∃ D : ℝ, 0 < D ∧ ∀ m : ℕ, 1 ≤ m →
        let L := (Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1)
        (α ^ 2 * Cdec * CBz * Kφ / L * (3 * ((m : ℝ) + 1)) ≤ D * majPow m) ∧
        (α ^ 2 * Cdec * CBz * Kφ / L * (900 * ((m : ℝ) + 1) ^ 2 / cθ ^ 2) ≤ D * majPow m) ∧
        (α ^ 2 * Cdec * CBz * Kφ / L * (27000 * ((m : ℝ) + 1) ^ 3 / cθ ^ 4)
            ≤ D * majPow m) ∧
        (α ^ 2 * Cdec * CBz * Kφ / L * (9000 * ((m : ℝ) + 1) ^ 2 / cθ ^ 3)
            ≤ D * majPow m)) :
    ∀ z, 0 < z → ∀ θ, 0 < θ → θ < π / 2 → ∃ D : ℝ, 0 < D ∧
      (∀ m : ℕ, ∀ y : ℝ, 0 < y →
        |acoeff α m (RemSource α ψ) y| * |Gegenbauer.eFam m θ| ≤ D * majPow m) ∧
      (∀ m : ℕ, ∀ y : ℝ, 0 < y →
        |deriv (acoeff α m (RemSource α ψ)) y| * |Gegenbauer.eFam m θ| ≤ D * majPow m) ∧
      (∀ m : ℕ, ∀ y : ℝ, 0 < y →
        |deriv (deriv (acoeff α m (RemSource α ψ))) y| * |Gegenbauer.eFam m θ| ≤ D * majPow m) ∧
      (∀ m : ℕ, ∀ y : ℝ, 0 < y → y ≤ (θ + π / 2) / 2 →
        |acoeff α m (RemSource α ψ) z| * |deriv (Gegenbauer.eFam m) y| ≤ D * majPow m) ∧
      (∀ m : ℕ, ∀ y : ℝ, 0 < y → y ≤ (θ + π / 2) / 2 →
        |acoeff α m (RemSource α ψ) z| * |iteratedDeriv 2 (Gegenbauer.eFam m) y|
          ≤ D * majPow m) ∧
      (∀ m : ℕ, ∀ y : ℝ, 0 < y → y ≤ (θ + π / 2) / 2 →
        |acoeff α m (RemSource α ψ) z|
          * |deriv (fun θ' => Real.tan θ' * Gegenbauer.eFam m θ') y| ≤ D * majPow m) := by
  intro z hz θ hθ hθ2
  have hcosθ : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ2⟩)
  set θu : ℝ := (θ + π / 2) / 2 with hθu
  -- the `m = 0` mode coefficient vanishes
  have hb0 : bmode 0 ψ = 0 := by
    have hF : Elliptic.Fstar (fun _ θ => ψ θ) 0 = 0 := by
      simpa only [Elliptic.Fstar] using hmom
    rw [bmode_eq_cmode 0 ψ 0]
    exact eFam_zero_moment (fun _ θ => ψ θ) hF
  have hac0 : ∀ y : ℝ, acoeff α 0 (RemSource α ψ) y = 0 := by
    intro y
    rw [acoeff_RemSource, hb0]
    ring
  obtain ⟨Cdec, hCdecpos, hDec'⟩ := hDec
  obtain ⟨CBz, hCBzpos, hGamma'⟩ := hGamma
  have hθu_lt : θu < Real.pi / 2 := by rw [hθu]; linarith [hθ2]
  have hcθ : 0 < Real.cos θu :=
    Real.cos_pos_of_mem_Ioo ⟨by rw [hθu]; linarith [Real.pi_pos], hθu_lt⟩
  obtain ⟨D, hDpos, hDsh⟩ :=
    hterm Cdec CBz 1 hCdecpos hCBzpos one_pos (Real.cos θu) hcθ
  -- differentiability of the mode solutions and of their derivatives
  have hdiffA : ∀ m : ℕ,
      (∀ y, 0 < y → HasDerivAt (gammaFun α m) (rgiD1 α m (VocabO.phiA α) y) y) ∧
      (∀ y, 0 < y →
        HasDerivAt (deriv (gammaFun α m)) (deriv (rgiD1 α m (VocabO.phiA α)) y) y) :=
    fun m => hasDerivAt_gammaFun hα m hInt.2.2.2.1 (hInt.2.2.2.2.1 m) (hInt.2.2.2.2.2 m)
  have hderA : ∀ m : ℕ,
      (∀ y, 0 < y → HasDerivAt (acoeff α m (RemSource α ψ))
        (α ^ 2 * bmode m ψ * rgiD1 α m (VocabO.phiA α) y) y) ∧
      (∀ y, 0 < y → HasDerivAt (deriv (acoeff α m (RemSource α ψ)))
        (α ^ 2 * bmode m ψ * deriv (rgiD1 α m (VocabO.phiA α)) y) y) :=
    fun m => hasDerivAt_acoeff m (hdiffA m).1 (hdiffA m).2
  -- the two basic product bounds
  have hbase : ∀ m : ℕ, 1 ≤ m → ∀ k : ℕ, k ≤ 2 → ∀ y : ℝ, 0 < y →
      |bmode m ψ| * |iteratedDeriv k (gammaFun α m) y|
        ≤ Cdec * CBz / ((Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1)) := by
    intro m hm k hk y hy
    exact bound_mul (le_of_lt hCdecpos) (le_of_lt hCBzpos) (lam_pos hm) (sqrt_two_m_pos m)
      (hDec' m hm) (hGamma' m hm k hk y hy)
  have hacc : ∀ m : ℕ, 1 ≤ m → ∀ k : ℕ, k ≤ 2 → ∀ y : ℝ, 0 < y →
      |iteratedDeriv k (acoeff α m (RemSource α ψ)) y|
        ≤ α ^ 2 * Cdec * CBz / ((Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1)) := by
    intro m hm k hk y hy
    have hbase0 := hbase m hm
    interval_cases k
    · have h := hbase0 0 (by norm_num) y hy
      rw [iteratedDeriv_zero] at h
      have habs : |acoeff α m (RemSource α ψ) y|
          = α ^ 2 * (|bmode m ψ| * |gammaFun α m y|) := by
        rw [acoeff_RemSource,
          show ((α ^ 2 * bmode m ψ) * Radial.radGreen α m (VocabO.phiA α) y)
            = α ^ 2 * bmode m ψ * gammaFun α m y from rfl,
          abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ α ^ 2)]
        ring
      rw [iteratedDeriv_zero, habs]
      calc α ^ 2 * (|bmode m ψ| * |gammaFun α m y|)
          ≤ α ^ 2 * (Cdec * CBz / ((Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1))) :=
            mul_le_mul_of_nonneg_left h (by positivity)
        _ = α ^ 2 * Cdec * CBz / ((Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1)) := by
            ring
    · have h := hbase0 1 (by norm_num) y hy
      rw [iteratedDeriv_one, (hdiffA m).1 y hy |>.deriv] at h
      have habs : |iteratedDeriv 1 (acoeff α m (RemSource α ψ)) y|
          = α ^ 2 * (|bmode m ψ| * |rgiD1 α m (VocabO.phiA α) y|) := by
        rw [iteratedDeriv_one, deriv_acoeff m (hdiffA m).1 y hy, abs_mul, abs_mul,
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ α ^ 2)]
        ring
      rw [habs]
      calc α ^ 2 * (|bmode m ψ| * |rgiD1 α m (VocabO.phiA α) y|)
          ≤ α ^ 2 * (Cdec * CBz / ((Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1))) :=
            mul_le_mul_of_nonneg_left h (by positivity)
        _ = α ^ 2 * Cdec * CBz / ((Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1)) := by
            ring
    · have h := hbase0 2 (by norm_num) y hy
      rw [iteratedDeriv_two_apply, (hdiffA m).2 y hy |>.deriv] at h
      have habs : |iteratedDeriv 2 (acoeff α m (RemSource α ψ)) y|
          = α ^ 2 * (|bmode m ψ| * |deriv (rgiD1 α m (VocabO.phiA α)) y|) := by
        rw [iteratedDeriv_two_apply, deriv_deriv_acoeff m (hdiffA m).1 (hdiffA m).2 y hy,
          abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ α ^ 2)]
        ring
      rw [habs]
      calc α ^ 2 * (|bmode m ψ| * |deriv (rgiD1 α m (VocabO.phiA α)) y|)
          ≤ α ^ 2 * (Cdec * CBz / ((Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1))) :=
            mul_le_mul_of_nonneg_left h (by positivity)
        _ = α ^ 2 * Cdec * CBz / ((Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1)) := by
            ring
  -- the four arithmetic shapes of `termEstimates`
  have hshape1 : ∀ m : ℕ, 1 ≤ m →
      α ^ 2 * Cdec * CBz * 1
          / ((Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1)) * (3 * ((m : ℝ) + 1))
        ≤ D * majPow m := by
    intro m hm
    have h := (hDsh m hm).1
    simpa only [mul_one] using h
  have hshape2 : ∀ m : ℕ, 1 ≤ m →
      α ^ 2 * Cdec * CBz * 1
          / ((Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1))
          * (900 * ((m : ℝ) + 1) ^ 2 / (Real.cos θu) ^ 2) ≤ D * majPow m := by
    intro m hm
    have h := (hDsh m hm).2.1
    simpa only [mul_one] using h
  have hshape3 : ∀ m : ℕ, 1 ≤ m →
      α ^ 2 * Cdec * CBz * 1
          / ((Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1))
          * (27000 * ((m : ℝ) + 1) ^ 3 / (Real.cos θu) ^ 4) ≤ D * majPow m := by
    intro m hm
    have h := (hDsh m hm).2.2.1
    simpa only [mul_one] using h
  have hshape4 : ∀ m : ℕ, 1 ≤ m →
      α ^ 2 * Cdec * CBz * 1
          / ((Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1))
          * (9000 * ((m : ℝ) + 1) ^ 2 / (Real.cos θu) ^ 3) ≤ D * majPow m := by
    intro m hm
    have h := (hDsh m hm).2.2.2
    simpa only [mul_one] using h
  -- the five pointwise bounds
  have hB0 : ∀ m : ℕ, ∀ y : ℝ, 0 < y →
      |acoeff α m (RemSource α ψ) y| * |Gegenbauer.eFam m θ| ≤ D * majPow m := by
    intro m y hy
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      rw [hac0 y, abs_zero, zero_mul]
      exact mul_nonneg (le_of_lt hDpos) (majPow_nonneg 0)
    · have h1 := hacc m hm 0 (by norm_num) y hy
      rw [iteratedDeriv_zero] at h1
      calc |acoeff α m (RemSource α ψ) y| * |Gegenbauer.eFam m θ|
          ≤ (α ^ 2 * Cdec * CBz
              / ((Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1)))
              * (3 * ((m : ℝ) + 1)) := by
            have h2 : |Gegenbauer.eFam m θ|
                ≤ Real.sqrt ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) := (hAng m θ ⟨hθ, hθ2⟩).1
            have h3 := sqrt_mu_le hm
            calc |acoeff α m (RemSource α ψ) y| * |Gegenbauer.eFam m θ|
                ≤ (α ^ 2 * Cdec * CBz
                    / ((Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1)))
                    * (3 * ((m : ℝ) + 1)) :=
                  mul_le_mul h1 (le_trans h2 h3) (abs_nonneg _) (by positivity)
              _ = _ := rfl
        _ ≤ D * majPow m := by
            have h4 := hshape1 m hm
            calc (α ^ 2 * Cdec * CBz
                  / ((Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1)))
                  * (3 * ((m : ℝ) + 1))
                = α ^ 2 * Cdec * CBz * 1
                  / ((Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1))
                  * (3 * ((m : ℝ) + 1)) := by rw [mul_one]
              _ ≤ D * majPow m := h4
  have hB1 : ∀ m : ℕ, ∀ y : ℝ, 0 < y →
      |deriv (acoeff α m (RemSource α ψ)) y| * |Gegenbauer.eFam m θ| ≤ D * majPow m := by
    intro m y hy
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      have : deriv (acoeff α 0 (RemSource α ψ)) y = 0 := by
        rw [show acoeff α 0 (RemSource α ψ) = fun _ => (0 : ℝ) from funext hac0]
        simp
      rw [this, abs_zero, zero_mul]
      exact mul_nonneg (le_of_lt hDpos) (majPow_nonneg 0)
    · have h1 := hacc m hm 1 (by norm_num) y hy
      rw [iteratedDeriv_one] at h1
      have h2 : |Gegenbauer.eFam m θ|
          ≤ Real.sqrt ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) := (hAng m θ ⟨hθ, hθ2⟩).1
      have h3 := sqrt_mu_le hm
      calc |deriv (acoeff α m (RemSource α ψ)) y| * |Gegenbauer.eFam m θ|
          ≤ (α ^ 2 * Cdec * CBz
              / ((Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1)))
              * (3 * ((m : ℝ) + 1)) :=
            mul_le_mul h1 (le_trans h2 h3) (abs_nonneg _) (by positivity)
        _ ≤ D * majPow m := by
            have h4 := hshape1 m hm
            calc (α ^ 2 * Cdec * CBz
                  / ((Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1)))
                  * (3 * ((m : ℝ) + 1))
                = α ^ 2 * Cdec * CBz * 1
                  / ((Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1))
                  * (3 * ((m : ℝ) + 1)) := by rw [mul_one]
              _ ≤ D * majPow m := h4
  have hB2 : ∀ m : ℕ, ∀ y : ℝ, 0 < y →
      |deriv (deriv (acoeff α m (RemSource α ψ))) y| * |Gegenbauer.eFam m θ|
        ≤ D * majPow m := by
    intro m y hy
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      have hd : deriv (acoeff α 0 (RemSource α ψ)) = fun _ => (0 : ℝ) := by
        rw [show acoeff α 0 (RemSource α ψ) = fun _ => (0 : ℝ) from funext hac0]
        simp
      have : deriv (deriv (acoeff α 0 (RemSource α ψ))) y = 0 := by rw [hd]; simp
      rw [this, abs_zero, zero_mul]
      exact mul_nonneg (le_of_lt hDpos) (majPow_nonneg 0)
    · have h1 := hacc m hm 2 (by norm_num) y hy
      rw [iteratedDeriv_two_apply] at h1
      have h2 : |Gegenbauer.eFam m θ|
          ≤ Real.sqrt ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) := (hAng m θ ⟨hθ, hθ2⟩).1
      have h3 := sqrt_mu_le hm
      calc |deriv (deriv (acoeff α m (RemSource α ψ))) y| * |Gegenbauer.eFam m θ|
          ≤ (α ^ 2 * Cdec * CBz
              / ((Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1)))
              * (3 * ((m : ℝ) + 1)) :=
            mul_le_mul h1 (le_trans h2 h3) (abs_nonneg _) (by positivity)
        _ ≤ D * majPow m := by
            have h4 := hshape1 m hm
            calc (α ^ 2 * Cdec * CBz
                  / ((Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1)))
                  * (3 * ((m : ℝ) + 1))
                = α ^ 2 * Cdec * CBz * 1
                  / ((Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1))
                  * (3 * ((m : ℝ) + 1)) := by rw [mul_one]
              _ ≤ D * majPow m := h4
  have hB3 : ∀ m : ℕ, ∀ y : ℝ, 0 < y → y ≤ θu →
      |acoeff α m (RemSource α ψ) z| * |deriv (Gegenbauer.eFam m) y| ≤ D * majPow m := by
    intro m y hy hyu
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      rw [hac0 z, abs_zero, zero_mul]
      exact mul_nonneg (le_of_lt hDpos) (majPow_nonneg 0)
    · have h1 := hacc m hm 0 (by norm_num) z hz
      rw [iteratedDeriv_zero] at h1
      have hcosy : Real.cos θu ≤ Real.cos y := by
        refine Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) ?_ hyu
        linarith [Real.pi_pos, hθ2]
      have hcvy : 0 < Real.cos y := lt_of_lt_of_le hcθ hcosy
      have h2 : |deriv (Gegenbauer.eFam m) y|
          ≤ 100 * ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) / (Real.cos y) ^ 2 :=
        (hAng m y ⟨hy, by linarith [hyu, hθu_lt]⟩).2.1
      have h3 : 100 * ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) / (Real.cos y) ^ 2
          ≤ 900 * ((m : ℝ) + 1) ^ 2 / (Real.cos θu) ^ 2 := by
        have hmu := mu_le hm
        have hsq : (Real.cos θu) ^ 2 ≤ (Real.cos y) ^ 2 := by
          exact pow_le_pow_left₀ (le_of_lt hcθ) hcosy 2
        calc 100 * ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) / (Real.cos y) ^ 2
            ≤ 100 * (9 * ((m : ℝ) + 1) ^ 2) / (Real.cos y) ^ 2 := by
              exact div_le_div_of_nonneg_right (by linarith [hmu]) (by positivity)
          _ = 900 * ((m : ℝ) + 1) ^ 2 / (Real.cos y) ^ 2 := by ring
          _ ≤ 900 * ((m : ℝ) + 1) ^ 2 / (Real.cos θu) ^ 2 := by
              exact div_le_div_of_nonneg_left (by positivity) (by positivity) hsq
      calc |acoeff α m (RemSource α ψ) z| * |deriv (Gegenbauer.eFam m) y|
          ≤ (α ^ 2 * Cdec * CBz
              / ((Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1)))
              * (900 * ((m : ℝ) + 1) ^ 2 / (Real.cos θu) ^ 2) :=
            mul_le_mul h1 (le_trans h2 h3) (abs_nonneg _) (by positivity)
        _ ≤ D * majPow m := by
            have h4 := hshape2 m hm
            calc (α ^ 2 * Cdec * CBz
                  / ((Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1)))
                  * (900 * ((m : ℝ) + 1) ^ 2 / (Real.cos θu) ^ 2)
                = α ^ 2 * Cdec * CBz * 1
                  / ((Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1))
                  * (900 * ((m : ℝ) + 1) ^ 2 / (Real.cos θu) ^ 2) := by rw [mul_one]
              _ ≤ D * majPow m := h4
  have hB4 : ∀ m : ℕ, ∀ y : ℝ, 0 < y → y ≤ θu →
      |acoeff α m (RemSource α ψ) z| * |iteratedDeriv 2 (Gegenbauer.eFam m) y|
        ≤ D * majPow m := by
    intro m y hy hyu
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      rw [hac0 z, abs_zero, zero_mul]
      exact mul_nonneg (le_of_lt hDpos) (majPow_nonneg 0)
    · have h1 := hacc m hm 0 (by norm_num) z hz
      rw [iteratedDeriv_zero] at h1
      have hcosy : Real.cos θu ≤ Real.cos y := by
        refine Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) ?_ hyu
        linarith [Real.pi_pos, hθ2]
      have hcvy : 0 < Real.cos y := lt_of_lt_of_le hcθ hcosy
      have h2 : |iteratedDeriv 2 (Gegenbauer.eFam m) y|
          ≤ 1000 * ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3))
              * Real.sqrt ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) / (Real.cos y) ^ 4 :=
        (hAng m y ⟨hy, by linarith [hyu, hθu_lt]⟩).2.2.1
      have h3 : 1000 * ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3))
              * Real.sqrt ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) / (Real.cos y) ^ 4
          ≤ 27000 * ((m : ℝ) + 1) ^ 3 / (Real.cos θu) ^ 4 := by
        have hmu := mu_mul_sqrt_mu_le hm
        have hsq : (Real.cos θu) ^ 4 ≤ (Real.cos y) ^ 4 := by
          exact pow_le_pow_left₀ (le_of_lt hcθ) hcosy 4
        calc 1000 * ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3))
                * Real.sqrt ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) / (Real.cos y) ^ 4
            ≤ 1000 * (27 * ((m : ℝ) + 1) ^ 3) / (Real.cos y) ^ 4 := by
              exact div_le_div_of_nonneg_right (by linarith [hmu]) (by positivity)
          _ = 27000 * ((m : ℝ) + 1) ^ 3 / (Real.cos y) ^ 4 := by ring
          _ ≤ 27000 * ((m : ℝ) + 1) ^ 3 / (Real.cos θu) ^ 4 := by
              exact div_le_div_of_nonneg_left (by positivity) (by positivity) hsq
      calc |acoeff α m (RemSource α ψ) z| * |iteratedDeriv 2 (Gegenbauer.eFam m) y|
          ≤ (α ^ 2 * Cdec * CBz
              / ((Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1)))
              * (27000 * ((m : ℝ) + 1) ^ 3 / (Real.cos θu) ^ 4) :=
            mul_le_mul h1 (le_trans h2 h3) (abs_nonneg _) (by positivity)
        _ ≤ D * majPow m := by
            have h4 := hshape3 m hm
            calc (α ^ 2 * Cdec * CBz
                  / ((Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1)))
                  * (27000 * ((m : ℝ) + 1) ^ 3 / (Real.cos θu) ^ 4)
                = α ^ 2 * Cdec * CBz * 1
                  / ((Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1))
                  * (27000 * ((m : ℝ) + 1) ^ 3 / (Real.cos θu) ^ 4) := by rw [mul_one]
              _ ≤ D * majPow m := h4
  have hB5 : ∀ m : ℕ, ∀ y : ℝ, 0 < y → y ≤ θu →
      |acoeff α m (RemSource α ψ) z|
        * |deriv (fun θ' => Real.tan θ' * Gegenbauer.eFam m θ') y| ≤ D * majPow m := by
    intro m y hy hyu
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      rw [hac0 z, abs_zero, zero_mul]
      exact mul_nonneg (le_of_lt hDpos) (majPow_nonneg 0)
    · have h1 := hacc m hm 0 (by norm_num) z hz
      rw [iteratedDeriv_zero] at h1
      have hcosy : Real.cos θu ≤ Real.cos y := by
        refine Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) ?_ hyu
        linarith [Real.pi_pos, hθ2]
      have hcvy : 0 < Real.cos y := lt_of_lt_of_le hcθ hcosy
      have h2 : |deriv (fun θ' => Real.tan θ' * Gegenbauer.eFam m θ') y|
          ≤ 1000 * ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) / (Real.cos y) ^ 3 :=
        (hAng m y ⟨hy, by linarith [hyu, hθu_lt]⟩).2.2.2
      have h3 : 1000 * ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) / (Real.cos y) ^ 3
          ≤ 9000 * ((m : ℝ) + 1) ^ 2 / (Real.cos θu) ^ 3 := by
        have hmu := mu_le hm
        have hsq : (Real.cos θu) ^ 3 ≤ (Real.cos y) ^ 3 := by
          exact pow_le_pow_left₀ (le_of_lt hcθ) hcosy 3
        calc 1000 * ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) / (Real.cos y) ^ 3
            ≤ 1000 * (9 * ((m : ℝ) + 1) ^ 2) / (Real.cos y) ^ 3 := by
              exact div_le_div_of_nonneg_right (by linarith [hmu]) (by positivity)
          _ = 9000 * ((m : ℝ) + 1) ^ 2 / (Real.cos y) ^ 3 := by ring
          _ ≤ 9000 * ((m : ℝ) + 1) ^ 2 / (Real.cos θu) ^ 3 := by
              exact div_le_div_of_nonneg_left (by positivity) (by positivity) hsq
      calc |acoeff α m (RemSource α ψ) z|
            * |deriv (fun θ' => Real.tan θ' * Gegenbauer.eFam m θ') y|
          ≤ (α ^ 2 * Cdec * CBz
              / ((Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1)))
              * (9000 * ((m : ℝ) + 1) ^ 2 / (Real.cos θu) ^ 3) :=
            mul_le_mul h1 (le_trans h2 h3) (abs_nonneg _) (by positivity)
        _ ≤ D * majPow m := by
            have h4 := hshape4 m hm
            calc (α ^ 2 * Cdec * CBz
                  / ((Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1)))
                  * (9000 * ((m : ℝ) + 1) ^ 2 / (Real.cos θu) ^ 3)
                = α ^ 2 * Cdec * CBz * 1
                  / ((Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1))
                  * (9000 * ((m : ℝ) + 1) ^ 2 / (Real.cos θu) ^ 3) := by rw [mul_one]
              _ ≤ D * majPow m := h4
  exact ⟨D, hDpos, hB0, hB1, hB2, hB3, hB4, hB5⟩

end Work.FTS.PhiStar.Series
