import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.RegExportIface.RXT.Leaves
import Submission.Work.FTS_RegExport.RXT.Sys.PullDefs
import Submission.Work.FTS_RegExport.RXT.Sys.pw_regularity
import Submission.Work.FTS_RegExport.RXT.Sys.pw_identity_mine
import Submission.Work.FTS_RegExport.RXT.Sys.pw_bounds
import Submission.Work.FTS_RegExport.RXT.Sys.cone_max_int

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.Sys.weighted_integrated_mp` — T5c of the RX-St1 leaf plan

The weighted, vector, integrated maximum principle in `(z,θ)`: the pulled-back unknown
`φ_k = w_k/ω` (`pw α (w k)`) satisfies, in the logarithmic coordinates
`s = log z`, `ψ = log tan θ`, the *integrated* transport identity

`φ_k(τ₂) − φ_k(τ₁) = ∫_{τ₁}^{τ₂}[f_k − (a·∂_sφ_k + b·∂_ψφ_k + c·φ_k)]`

with `f_k = R_k/om` bounded by `C·∑_j|φ_j| + Kσ`, coefficients `a = Vz`, `b = 2·b`,
`c = 2Vz/(1+z) + 2α·c2m(θ)·b` bounded by `2|M|`, `2|M|`, `(2+4α)|M|` respectively
(`pw_regularity`, `pw_identity_mine`, `pw_bounds`), so the general integrated supra-cone maximum
principle `cone_max_int` gives `|φ_k| ≤ exp(2((2+4α)|M| + n·C⁺)·τ)(K₀⁺ + τKσ⁺)`, and
transferring back (`ω(cz s, cth ψ) = om α s ψ > 0`, `z = eˢ`, `θ = arctan e^ψ`) gives the
claim.
-/

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_RegExport.RXT.Sys

set_option maxHeartbeats 2000000

theorem weighted_integrated_mp {n : ℕ} {w wz wθ R : Fin n → ℝ → ℝ → ℝ → ℝ}
    {Vz b : ℝ → ℝ → ℝ → ℝ} {S M C K₀ Kσ α : ℝ} (hα : 0 < α) (hS : 0 < S)
    (hcont : ∀ k, ContinuousOn (fun p : ℝ × ℝ × ℝ => w k p.1 p.2.1 p.2.2)
      (Set.Ioi (0:ℝ) ×ˢ Set.Ioo (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) S))
    (hz : ∀ k z θ τ, 0 < z → 0 < θ → θ < Real.pi / 2 → τ ∈ Set.Icc (0:ℝ) S →
      HasDerivAt (fun z' => w k z' θ τ) (wz k z θ τ / z) z)
    (hθ : ∀ k z θ τ, 0 < z → 0 < θ → θ < Real.pi / 2 → τ ∈ Set.Icc (0:ℝ) S →
      HasDerivAt (fun θ' => w k z θ' τ) (wθ k z θ τ / Real.sin (2 * θ)) θ)
    (hcz : ∀ k, ContinuousOn (fun p : ℝ × ℝ × ℝ => wz k p.1 p.2.1 p.2.2)
      (Set.Ioi (0:ℝ) ×ˢ Set.Ioo (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) S))
    (hcθ : ∀ k, ContinuousOn (fun p : ℝ × ℝ × ℝ => wθ k p.1 p.2.1 p.2.2)
      (Set.Ioi (0:ℝ) ×ˢ Set.Ioo (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) S))
    (hV : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      ContinuousOn (fun τ => Vz z θ τ) (Set.Icc 0 S) ∧ ContinuousOn (fun τ => b z θ τ) (Set.Icc 0 S))
    (hVb : ∀ z θ τ, 0 < z → 0 < θ → θ < Real.pi / 2 → τ ∈ Set.Icc (0:ℝ) S →
      |Vz z θ τ| ≤ M ∧ |b z θ τ| ≤ M)
    (hRi : ∀ k z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      IntervalIntegrable (fun τ => R k z θ τ) MeasureTheory.volume 0 S)
    (hRb : ∀ k z θ τ, 0 < z → 0 < θ → θ < Real.pi / 2 → τ ∈ Set.Icc (0:ℝ) S →
      |R k z θ τ| ≤ C * ∑ j, |w j z θ τ| + Kσ * Work.FTS.RegExportIface.ω α z θ)
    (hId : ∀ k z θ τ₁ τ₂, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 ≤ τ₁ → τ₁ ≤ τ₂ → τ₂ ≤ S →
      w k z θ τ₂ - w k z θ τ₁
        = ∫ σ in τ₁..τ₂, (R k z θ σ - (Vz z θ σ * wz k z θ σ + b z θ σ * wθ k z θ σ)))
    (h0 : ∀ k z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → |w k z θ 0| ≤ K₀ * Work.FTS.RegExportIface.ω α z θ) :
    ∃ K : ℝ, ∀ k z θ τ, 0 < z → 0 < θ → θ < Real.pi / 2 → τ ∈ Set.Icc (0:ℝ) S →
      |w k z θ τ| ≤ K * Work.FTS.RegExportIface.ω α z θ := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact ⟨0, fun k => k.elim0⟩
  -- ## The three pull-back inputs
  obtain ⟨hpwcont, hpwscont, hpwψcont, hpws, hpwψ⟩ :=
    pw_regularity (n := n) (S := S) (α := α) hα hcont hz hθ hcz hcθ
  have hpwI := pw_identity_mine (n := n) (S := S) (α := α) hα hId
  obtain ⟨hcoefA, hcoefB, hcoefC, hsrc, hinit⟩ := pw_bounds (n := n) hα hS hVb hRb h0
  -- ## Interval-integrability of the pulled-back source
  have hfi : ∀ k s ψ τ₁ τ₂, 0 ≤ τ₁ → τ₁ ≤ τ₂ → τ₂ ≤ S →
      IntervalIntegrable (fun σ => srcF α (R k) s ψ σ) MeasureTheory.volume τ₁ τ₂ := by
    intro k s ψ τ₁ τ₂ h1 h2 h3
    have hR : IntervalIntegrable (fun σ => R k (cz s) (cth ψ) σ) MeasureTheory.volume 0 S :=
      hRi k (cz s) (cth ψ) (cz_pos s) (cth_pos ψ) (cth_lt ψ)
    have hRs : IntervalIntegrable (fun σ => R k (cz s) (cth ψ) σ) MeasureTheory.volume τ₁ τ₂ :=
      hR.mono_set (by
        rw [Set.uIcc_of_le h2, Set.uIcc_of_le (le_of_lt hS)]
        exact Set.Icc_subset_Icc (by linarith) h3)
    have h2' := hRs.div_const (om α s ψ)
    simpa only [srcF] using h2'
  -- ## τ-continuity of the pulled-back coefficients
  have hab : ∀ s ψ, ContinuousOn (fun τ => coefA Vz s ψ τ) (Set.Icc (0:ℝ) S) ∧
      ContinuousOn (fun τ => coefB b s ψ τ) (Set.Icc (0:ℝ) S) ∧
      ContinuousOn (fun τ => coefC α Vz b s ψ τ) (Set.Icc (0:ℝ) S) := by
    intro s ψ
    obtain ⟨hV1, hb1⟩ := hV (cz s) (cth ψ) (cz_pos s) (cth_pos ψ) (cth_lt ψ)
    refine ⟨hV1, ?_, ?_⟩
    · simpa only [coefB] using hb1.const_mul (2 : ℝ)
    · have h1 : ContinuousOn (fun τ : ℝ => 2 * Vz (cz s) (cth ψ) τ / (1 + cz s))
          (Set.Icc (0:ℝ) S) := (hV1.const_mul (2 : ℝ)).div_const (1 + cz s)
      have h2 : ContinuousOn (fun τ : ℝ =>
          α * Work.Construction.c2m (cth ψ) * (2 * b (cz s) (cth ψ) τ)) (Set.Icc (0:ℝ) S) :=
        (hb1.const_mul (2 : ℝ)).const_mul (α * Work.Construction.c2m (cth ψ))
      have h3 : ContinuousOn (fun τ : ℝ => 2 * Vz (cz s) (cth ψ) τ / (1 + cz s)
          + α * Work.Construction.c2m (cth ψ) * (2 * b (cz s) (cth ψ) τ)) (Set.Icc (0:ℝ) S) :=
        h1.add h2
      convert h3 using 1
      ext τ
      simp only [coefC]
  -- ## The integrated supra-cone maximum principle
  have hcone := cone_max_int (n := n)
    (φ := fun k => pw α (w k)) (φs := fun k => pws α (wz k) (w k))
    (φψ := fun k => pwψ α (wθ k) (w k)) (f := fun k => srcF α (R k))
    (a := coefA Vz) (b := coefB b) (c := coefC α Vz b)
    (T := S) (A := 2 * |M|) (C := (2 + 4 * α) * |M|) (C₀ := max C 0)
    (F := max Kσ 0) (K₀ := max K₀ 0)
    hS (by positivity) (by positivity) (le_max_right C 0) (le_max_right Kσ 0) (le_max_right K₀ 0)
    hpwcont hpwscont hpwψcont hpws hpwψ hab hcoefA hcoefB hcoefC hsrc hfi hpwI hinit
  -- ## Transfer back to `(z,θ)` and to `ω`
  refine ⟨Real.exp (2 * ((2 + 4 * α) * |M| + ↑n * max C 0) * S)
    * (max K₀ 0 + S * max Kσ 0), ?_⟩
  intro k z θ τ hz0 hθ0 hθπ hτ
  obtain ⟨s, hs⟩ := exists_exp z hz0
  obtain ⟨ψ, hψ⟩ := exists_arctan_exp θ hθ0 hθπ
  rw [← hs, ← hψ]
  have hom : 0 < om α s ψ := om_pos (α := α) hα
  have hC'nn : 0 ≤ 2 * ((2 + 4 * α) * |M| + ↑n * max C 0) := by positivity
  have h1 := hcone k s ψ τ hτ
  have hKσnn : 0 ≤ max Kσ 0 := le_max_right Kσ 0
  have hK₀nn : 0 ≤ max K₀ 0 := le_max_right K₀ 0
  have hexp : Real.exp (2 * ((2 + 4 * α) * |M| + ↑n * max C 0) * τ)
      ≤ Real.exp (2 * ((2 + 4 * α) * |M| + ↑n * max C 0) * S) := by
    refine Real.exp_le_exp.mpr ?_
    nlinarith [hτ.1, hτ.2, hC'nn]
  have hsum : max K₀ 0 + τ * max Kσ 0 ≤ max K₀ 0 + S * max Kσ 0 := by
    have h := mul_le_mul_of_nonneg_right hτ.2 hKσnn
    linarith
  have hnn : 0 ≤ max K₀ 0 + τ * max Kσ 0 := by
    have h := mul_nonneg hτ.1 hKσnn
    linarith
  have h2 : |pw α (w k) s ψ τ| ≤ Real.exp (2 * ((2 + 4 * α) * |M| + ↑n * max C 0) * S)
      * (max K₀ 0 + S * max Kσ 0) := by
    calc |pw α (w k) s ψ τ|
        ≤ Real.exp (2 * ((2 + 4 * α) * |M| + ↑n * max C 0) * τ)
            * (max K₀ 0 + τ * max Kσ 0) := h1
      _ ≤ Real.exp (2 * ((2 + 4 * α) * |M| + ↑n * max C 0) * S)
            * (max K₀ 0 + S * max Kσ 0) :=
          mul_le_mul hexp hsum hnn (by positivity)
  have hw : |w k (cz s) (cth ψ) τ| = |pw α (w k) s ψ τ| * om α s ψ := by
    have h1' : pw α (w k) s ψ τ = w k (cz s) (cth ψ) τ / om α s ψ := rfl
    rw [h1', abs_div, abs_of_pos hom]
    exact (div_mul_cancel₀ _ (ne_of_gt hom)).symm
  have hgoal : |w k (cz s) (cth ψ) τ| ≤ Real.exp (2 * ((2 + 4 * α) * |M| + ↑n * max C 0) * S)
      * (max K₀ 0 + S * max Kσ 0) * om α s ψ := by
    rw [hw]
    exact mul_le_mul_of_nonneg_right h2 (le_of_lt hom)
  exact hgoal

end Work.FTS_RegExport.RXT.Sys
