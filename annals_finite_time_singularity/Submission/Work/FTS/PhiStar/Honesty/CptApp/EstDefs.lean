import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Submission.Work.FTS.PhiStar.Honesty.CptApp.approxSmoothCptQ
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.Spaces.HkSq_terms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty.CptApp

set_option autoImplicit false

/-! ## The shrinking angular region -/

/-- The angular part of the shrinking region: `1` where the angular cutoff `zetaR n` is not
constant, i.e. off `[2/n, π/2 − 2/n]`. -/
def thShrink (n : ℕ) (θ : ℝ) : ℝ :=
  if θ < 2 / (n : ℝ) ∨ Real.pi / 2 - 2 / (n : ℝ) < θ then 1 else 0

/-- The angular profile of the moment correction: `∑_{i ≤ k}(D_θ^iρ)²(sin^{−γ} + sin^{−η})`,
a fixed finite quantity for fixed `k` (the support of `ρ` is `(1, 3/2) ⊂ (0, π/2)`, where
all these functions are bounded). -/
def rhoProf (α : ℝ) (k : ℕ) (θ : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1),
    (Work.Spaces.DthIter i (fun _ θ' : ℝ => rho θ') 0 θ) ^ 2
      * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          + (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))

/-- The indicator of `Ω_n`, as a real number. -/
def omegaInd (n : ℕ) (z θ : ℝ) : ℝ := by
  classical
  exact if (z, θ) ∈ Omega n then 1 else 0

/-- The `Ω_n`-part of the `ℋᵏ`-integrand. -/
def omegaPart (α : ℝ) (k : ℕ) (n : ℕ) (F : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ := by
  classical
  exact if (z, θ) ∈ Omega n then Work.Spaces.HkIntegrand α k F z θ else 0

/-- **The pointwise majorant of the `ℋᵏ`-integrand of the error.**  Three groups: the
`Ω_n`-supported coefficients, the localised-Hardy group, and the moment correction. -/
def Good (α : ℝ) (k : ℕ) (n : ℕ) (F : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  omegaPart α k n F z θ
    + thShrink n θ
        * (∑ s ∈ Finset.range k, (Work.Spaces.DzIter s F z θ) ^ 2 * (Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
    + (∑ m ∈ Finset.range (k + 1),
        (Work.Spaces.DzIter m (fun z' _ : ℝ => mu n F z') z 0) ^ 2)
        * ((Work.Spaces.w z) ^ 2 * rhoProf α k θ)


/-! ## The honest `C^∞` order and the smoothness of the two cut-offs -/

/-- The honest `C^∞` order of `ContDiff` (the `∞ = ((⊤ : ℕ∞) : ℕ∞ω)` of the library). -/
abbrev smoothOrderC : WithTop ℕ∞ := ((⊤ : ℕ∞) : WithTop ℕ∞)

theorem contDiff_chiR_C (n : ℕ) : ContDiff ℝ smoothOrderC (chiR n) := by
  unfold chiR cut01
  fun_prop

theorem contDiff_zetaR_C (n : ℕ) : ContDiff ℝ smoothOrderC (zetaR n) := by
  unfold zetaR cut01
  fun_prop

/-! ## Elementary properties -/

theorem thShrink_nonneg (n : ℕ) (θ : ℝ) : 0 ≤ thShrink n θ := by
  unfold thShrink
  split_ifs <;> norm_num


/-- `thShrink n θ = 1` exactly on the angular part of `Ω_n`. -/
theorem thShrink_eq_one_iff {n : ℕ} {θ : ℝ} :
    thShrink n θ = 1 ↔ θ < 2 / (n : ℝ) ∨ Real.pi / 2 - 2 / (n : ℝ) < θ := by
  unfold thShrink
  by_cases h : θ < 2 / (n : ℝ) ∨ Real.pi / 2 - 2 / (n : ℝ) < θ
  · rw [if_pos h]; simp [h]
  · rw [if_neg h]; simp [h]

/-- If `thShrink` is nonzero, the point is in `Ω_n` (for every radius). -/
theorem thShrink_eq_zero_or_one (n : ℕ) (θ : ℝ) :
    thShrink n θ = 0 ∨ thShrink n θ = 1 := by
  unfold thShrink
  split_ifs <;> simp


theorem mem_Omega_of_lt_z {n : ℕ} {z θ : ℝ} (h : z < 2 / (n : ℝ)) : (z, θ) ∈ Omega n :=
  Or.inl h

theorem mem_Omega_of_gt_z {n : ℕ} {z θ : ℝ} (h : (n : ℝ) < z) : (z, θ) ∈ Omega n :=
  Or.inr (Or.inl h)

theorem mem_Omega_of_lt_th {n : ℕ} {z θ : ℝ} (h : θ < 2 / (n : ℝ)) : (z, θ) ∈ Omega n :=
  Or.inr (Or.inr (Or.inl h))

theorem mem_Omega_of_gt_th {n : ℕ} {z θ : ℝ} (h : Real.pi / 2 - 2 / (n : ℝ) < θ) :
    (z, θ) ∈ Omega n :=
  Or.inr (Or.inr (Or.inr h))

theorem omegaInd_nonneg (n : ℕ) (z θ : ℝ) : 0 ≤ omegaInd n z θ := by
  unfold omegaInd
  split_ifs <;> norm_num

theorem omegaInd_le_one (n : ℕ) (z θ : ℝ) : omegaInd n z θ ≤ 1 := by
  unfold omegaInd
  split_ifs <;> norm_num

theorem omegaInd_eq_one_iff {n : ℕ} {z θ : ℝ} :
    omegaInd n z θ = 1 ↔ (z, θ) ∈ Omega n := by
  unfold omegaInd
  by_cases h : (z, θ) ∈ Omega n
  · rw [if_pos h]; simp [h]
  · rw [if_neg h]; simp [h]

theorem omegaPart_nonneg (α : ℝ) (k : ℕ) (n : ℕ) (F : ℝ → ℝ → ℝ) (z θ : ℝ) :
    0 ≤ omegaPart α k n F z θ := by
  unfold omegaPart
  split_ifs with h
  · exact Work.Spaces.HkIntegrand_nonneg α k F z θ
  · norm_num

theorem omegaPart_le_HkIntegrand (α : ℝ) (k : ℕ) (n : ℕ) (F : ℝ → ℝ → ℝ) (z θ : ℝ) :
    omegaPart α k n F z θ ≤ Work.Spaces.HkIntegrand α k F z θ := by
  unfold omegaPart
  split_ifs with h
  · exact le_refl _
  · exact Work.Spaces.HkIntegrand_nonneg α k F z θ


/-! ## The two cut-offs: elementary value facts -/

theorem chiR_nonneg (n : ℕ) (z : ℝ) : 0 ≤ chiR n z := by
  rw [chiR, cut01]
  exact mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem chiR_le_one (n : ℕ) (z : ℝ) : chiR n z ≤ 1 := by
  rw [chiR, cut01]
  calc Real.smoothTransition ((n : ℝ) * z - 1) * Real.smoothTransition (2 - z / (n : ℝ))
      ≤ 1 * 1 := mul_le_mul (Real.smoothTransition.le_one _) (Real.smoothTransition.le_one _)
        (Real.smoothTransition.nonneg _) zero_le_one
    _ = 1 := by norm_num

theorem zetaR_nonneg (n : ℕ) (θ : ℝ) : 0 ≤ zetaR n θ := by
  rw [zetaR, cut01]
  exact mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem zetaR_le_one (n : ℕ) (θ : ℝ) : zetaR n θ ≤ 1 := by
  rw [zetaR, cut01]
  calc Real.smoothTransition ((n : ℝ) * θ - 1)
        * Real.smoothTransition ((n : ℝ) * (Real.pi / 2 - θ) - 1)
      ≤ 1 * 1 := mul_le_mul (Real.smoothTransition.le_one _) (Real.smoothTransition.le_one _)
        (Real.smoothTransition.nonneg _) zero_le_one
    _ = 1 := by norm_num

theorem abs_zetaR_le_one (n : ℕ) (θ : ℝ) : |zetaR n θ| ≤ 1 := by
  rw [abs_of_nonneg (zetaR_nonneg n θ)]
  exact zetaR_le_one n θ

/-- `chiR n = 1` on the plateau `[2/n, n]` (`n ≥ 2`). -/
theorem chiR_eq_one {n : ℕ} (hn : 2 ≤ n) {z : ℝ} (h1 : 2 / (n : ℝ) ≤ z)
    (h2 : z ≤ (n : ℝ)) : chiR n z = 1 := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have ha : 1 ≤ (n : ℝ) * z - 1 := by
    have := (div_le_iff₀ hnpos).mp h1
    linarith
  have hb : 1 ≤ 2 - z / (n : ℝ) := by
    have h3 : z / (n : ℝ) ≤ 1 := (div_le_one hnpos).mpr h2
    linarith
  simp only [chiR, cut01]
  rw [Real.smoothTransition.one_of_one_le ha, Real.smoothTransition.one_of_one_le hb]
  norm_num

/-- `chiR n` vanishes to the left of `1/n` (`n ≥ 1`). -/
theorem chiR_eq_zero_of_le {n : ℕ} (hn : 1 ≤ n) {z : ℝ} (h : z ≤ 1 / (n : ℝ)) :
    chiR n z = 0 := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have h1 : (n : ℝ) * z ≤ 1 := by
    calc (n : ℝ) * z ≤ (n : ℝ) * (1 / (n : ℝ)) := mul_le_mul_of_nonneg_left h hnpos.le
      _ = 1 := by rw [mul_one_div, div_self (ne_of_gt hnpos)]
  simp only [chiR, cut01]
  rw [Real.smoothTransition.zero_of_nonpos (by linarith : (n : ℝ) * z - 1 ≤ 0)]
  ring

/-- `chiR n` vanishes to the right of `2n` (`n ≥ 1`). -/
theorem chiR_eq_zero_of_ge {n : ℕ} (hn : 1 ≤ n) {z : ℝ} (h : 2 * (n : ℝ) ≤ z) :
    chiR n z = 0 := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have h2 : 2 - z / (n : ℝ) ≤ 0 := by
    have h3 : 2 ≤ z / (n : ℝ) := (le_div_iff₀ hnpos).mpr h
    linarith
  simp only [chiR, cut01]
  rw [Real.smoothTransition.zero_of_nonpos h2]
  ring

/-- `zetaR n = 1` on the angular plateau `[2/n, π/2 − 2/n]` (`n ≥ 2`). -/
theorem zetaR_eq_one {n : ℕ} (hn : 2 ≤ n) {θ : ℝ} (h1 : 2 / (n : ℝ) ≤ θ)
    (h2 : θ ≤ Real.pi / 2 - 2 / (n : ℝ)) : zetaR n θ = 1 := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have ha : 1 ≤ (n : ℝ) * θ - 1 := by
    have := (div_le_iff₀ hnpos).mp h1
    linarith
  have hb : 1 ≤ (n : ℝ) * (Real.pi / 2 - θ) - 1 := by
    have h : 2 / (n : ℝ) ≤ Real.pi / 2 - θ := by linarith
    have := (div_le_iff₀ hnpos).mp h
    linarith
  simp only [zetaR, cut01]
  rw [Real.smoothTransition.one_of_one_le ha, Real.smoothTransition.one_of_one_le hb]
  norm_num



/-- The product of the two cut-offs is `1` on the plateau, hence `(χζ − 1)² ≤ 1_{Ω_n}`. -/
theorem chiR_zetaR_sub_one_sq_le {n : ℕ} (hn : 2 ≤ n) (z θ : ℝ) :
    (chiR n z * zetaR n θ - 1) ^ 2 ≤ omegaInd n z θ := by
  by_cases h : (z, θ) ∈ Omega n
  · rw [omegaInd_eq_one_iff.mpr h]
    have h1 : 0 ≤ chiR n z * zetaR n θ := mul_nonneg (chiR_nonneg n z) (zetaR_nonneg n θ)
    have h2 : chiR n z * zetaR n θ ≤ 1 := by
      nlinarith [chiR_le_one n z, chiR_nonneg n z, zetaR_le_one n θ, zetaR_nonneg n θ]
    nlinarith [sq_nonneg (chiR n z * zetaR n θ - 1)]
  · rw [show omegaInd n z θ = 0 from by
      unfold omegaInd
      exact if_neg h]
    have hz : ¬(z < 2 / (n : ℝ) ∨ (n : ℝ) < z) := fun hc => h (by
      rcases hc with hc | hc
      · exact mem_Omega_of_lt_z hc
      · exact mem_Omega_of_gt_z hc)
    have hθ : ¬(θ < 2 / (n : ℝ) ∨ Real.pi / 2 - 2 / (n : ℝ) < θ) := fun hc => h (by
      rcases hc with hc | hc
      · exact mem_Omega_of_lt_th hc
      · exact mem_Omega_of_gt_th hc)
    have hz1 : 2 / (n : ℝ) ≤ z := not_lt.mp (fun hc => hz (Or.inl hc))
    have hz2 : z ≤ (n : ℝ) := not_lt.mp (fun hc => hz (Or.inr hc))
    have hθ1 : 2 / (n : ℝ) ≤ θ := not_lt.mp (fun hc => hθ (Or.inl hc))
    have hθ2 : θ ≤ Real.pi / 2 - 2 / (n : ℝ) := not_lt.mp (fun hc => hθ (Or.inr hc))
    rw [chiR_eq_one hn hz1 hz2, zetaR_eq_one hn hθ1 hθ2]
    norm_num

/-! ## Nonnegativity of the majorant -/

theorem w_nonneg (z : ℝ) : 0 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w]
  exact div_nonneg (sq_nonneg _) (sq_nonneg _)

theorem sin_two_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) := by
  rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
  exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [hθ.2, Real.pi_pos])

theorem rpow_gam_nonneg (α : ℝ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
  Real.rpow_nonneg (sin_two_nonneg_of_mem_Iθ hθ) _

theorem rpow_eta_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
  Real.rpow_nonneg (sin_two_nonneg_of_mem_Iθ hθ) _

theorem rhoProf_nonneg (α : ℝ) (k : ℕ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ rhoProf α k θ := by
  rw [rhoProf]
  refine Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (add_nonneg ?_ ?_)
  · exact rpow_gam_nonneg α hθ
  · exact rpow_eta_nonneg hθ

theorem hkZsum_nonneg (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ) (z : ℝ) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ ∑ s ∈ Finset.range k, (Work.Spaces.DzIter s F z θ) ^ 2 * (Work.Spaces.w z) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
  Finset.sum_nonneg fun s _ =>
    mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (rpow_gam_nonneg α hθ)

theorem Good_nonneg (α : ℝ) (k : ℕ) (n : ℕ) (F : ℝ → ℝ → ℝ) {z : ℝ} {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Good α k n F z θ := by
  rw [Good]
  refine add_nonneg (add_nonneg (omegaPart_nonneg α k n F z θ) ?_) ?_
  · exact mul_nonneg (thShrink_nonneg n θ) (hkZsum_nonneg α k F z hθ)
  · refine mul_nonneg (Finset.sum_nonneg fun m _ => sq_nonneg _)
      (mul_nonneg (sq_nonneg _) (rhoProf_nonneg α k hθ))

end Work.FTS.PhiStar.Honesty.CptApp
