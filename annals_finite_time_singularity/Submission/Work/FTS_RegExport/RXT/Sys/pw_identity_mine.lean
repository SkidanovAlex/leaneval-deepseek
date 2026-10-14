import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.TangentCone.Prod
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_RegExport.RXT.Sys.PullDefs
import Submission.Work.FTS_RegExport.VPDefs
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Continuity =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.Continuity` — joint continuity of `φ` and of its spatial derivatives

The cone maximum principle consumes `φ`, `∂_sφ`, `∂_ψφ` as continuous functions on the slab
`ℝ² × [0,S]`.  Since `u` is only assumed `C¹` on `(0,∞) × (0,π/2) × [0,S]` (a set which is
open in the first two variables but *closed* in `τ`), the joint continuity of the partial
derivatives is extracted from `ContDiffOn` through the bundled Fréchet derivative
`fderivWithin` on the slab (`fderivWithin_eq_pz`, `fderivWithin_eq_pth`), which is continuous
on a `UniqueDiffOn` set.
-/

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_RegExport.RXT

set_option autoImplicit false

theorem continuous_cz : Continuous cz := Real.continuous_exp

theorem continuous_cth : Continuous cth := Real.continuous_arctan.comp Real.continuous_exp





/-! ### Joint continuity of the pulled-back quantities -/

/-- The coordinate map `(s,ψ,τ) ↦ (eˢ, arctan e^ψ, τ)` lands in the slab. -/
theorem mapsTo_coords {S : ℝ} :
    Set.MapsTo (fun p : ℝ × ℝ × ℝ => (cz p.1, (cth p.2.1, p.2.2)))
      (Set.univ ×ˢ Set.univ ×ˢ Set.Icc (0:ℝ) S) (dom S) := by
  intro p hp
  obtain ⟨s, ψ, τ⟩ := p
  obtain ⟨-, ⟨-, hτ⟩⟩ := hp
  exact ⟨cz_pos s, ⟨cth_pos ψ, cth_lt ψ⟩, hτ⟩

theorem continuousOn_coords {S : ℝ} :
    ContinuousOn (fun p : ℝ × ℝ × ℝ => (cz p.1, (cth p.2.1, p.2.2)))
      (Set.univ ×ˢ Set.univ ×ˢ Set.Icc (0:ℝ) S) :=
  ((continuous_cz.comp continuous_fst).continuousOn).prodMk
    (((continuous_cth.comp (continuous_fst.comp continuous_snd)).continuousOn).prodMk
      (continuous_snd.comp continuous_snd).continuousOn)


theorem continuousOn_omega {α : ℝ} (hα : 0 < α) :
    ContinuousOn (fun q : ℝ × ℝ => Work.FTS.RegExportIface.ω α q.1 q.2)
      (Set.Ioi (0:ℝ) ×ˢ Set.Ioi (0:ℝ)) := by
  have hz : ContinuousOn (fun q : ℝ × ℝ => q.1) (Set.Ioi (0:ℝ) ×ˢ Set.Ioi (0:ℝ)) :=
    continuous_fst.continuousOn
  have hθ : ContinuousOn (fun q : ℝ × ℝ => q.2) (Set.Ioi (0:ℝ) ×ˢ Set.Ioi (0:ℝ)) :=
    continuous_snd.continuousOn
  have hbase : ContinuousOn (fun q : ℝ × ℝ => Real.sin q.2 * Real.cos q.2 ^ 2)
      (Set.Ioi (0:ℝ) ×ˢ Set.Ioi (0:ℝ)) :=
    ((Real.continuous_sin.comp continuous_snd).continuousOn).mul
      (((Real.continuous_cos.comp continuous_snd).continuousOn).pow 2)
  have hΓ : ContinuousOn (fun q : ℝ × ℝ => Work.FTS.Regularity.Gamma α q.2)
      (Set.Ioi (0:ℝ) ×ˢ Set.Ioi (0:ℝ)) := by
    have h := hbase.rpow_const (fun q _ => Or.inr hα.le)
    simpa [Work.FTS.Regularity.Gamma, Work.ConstructionInstance.Gamma] using h
  have hnum : ContinuousOn
      (fun q : ℝ × ℝ => q.1 ^ 2 * Work.FTS.Regularity.Gamma α q.2)
      (Set.Ioi (0:ℝ) ×ˢ Set.Ioi (0:ℝ)) := (hz.pow 2).mul hΓ
  have hden : ContinuousOn (fun q : ℝ × ℝ => (1 + q.1) ^ 2)
      (Set.Ioi (0:ℝ) ×ˢ Set.Ioi (0:ℝ)) := (continuousOn_const.add hz).pow 2
  refine (hnum.div hden (fun q hq => by
    have h1 : (0:ℝ) < q.1 := hq.1
    exact ne_of_gt (pow_pos (by linarith) 2))).congr ?_
  intro q hq
  simp only [Work.FTS.RegExportIface.ω, Pi.div_apply, div_eq_mul_inv]

theorem continuousOn_om {α S : ℝ} (hα : 0 < α) :
    ContinuousOn (fun p : ℝ × ℝ × ℝ => om α p.1 p.2.1)
      (Set.univ ×ˢ Set.univ ×ˢ Set.Icc (0:ℝ) S) := by
  have hcoords : ContinuousOn (fun p : ℝ × ℝ × ℝ => (cz p.1, cth p.2.1))
      (Set.univ ×ˢ Set.univ ×ˢ Set.Icc (0:ℝ) S) :=
    ((continuous_cz.comp continuous_fst).continuousOn).prodMk
      ((continuous_cth.comp (continuous_fst.comp continuous_snd)).continuousOn)
  have hmap : Set.MapsTo (fun p : ℝ × ℝ × ℝ => (cz p.1, cth p.2.1))
      (Set.univ ×ˢ Set.univ ×ˢ Set.Icc (0:ℝ) S) (Set.Ioi (0:ℝ) ×ˢ Set.Ioi (0:ℝ)) := by
    intro p hp
    exact ⟨cz_pos _, cth_pos _⟩
  have h := (continuousOn_omega hα).comp hcoords hmap
  simpa [om, Function.comp_def] using h




theorem continuousOn_cz {S : ℝ} :
    ContinuousOn (fun p : ℝ × ℝ × ℝ => cz p.1) (Set.univ ×ˢ Set.univ ×ˢ Set.Icc (0:ℝ) S) :=
  (continuous_cz.comp continuous_fst).continuousOn

theorem continuousOn_cth {S : ℝ} :
    ContinuousOn (fun p : ℝ × ℝ × ℝ => cth p.2.1) (Set.univ ×ˢ Set.univ ×ˢ Set.Icc (0:ℝ) S) :=
  (continuous_cth.comp (continuous_fst.comp continuous_snd)).continuousOn

theorem continuousOn_c2m_comp {S : ℝ} :
    ContinuousOn (fun p : ℝ × ℝ × ℝ => Work.Construction.c2m (cth p.2.1))
      (Set.univ ×ˢ Set.univ ×ˢ Set.Icc (0:ℝ) S) := by
  have h2θ : ContinuousOn (fun p : ℝ × ℝ × ℝ => 2 * cth p.2.1)
      (Set.univ ×ˢ Set.univ ×ˢ Set.Icc (0:ℝ) S) :=
    (continuousOn_const : ContinuousOn (fun _ : ℝ × ℝ × ℝ => (2:ℝ)) _).mul (continuousOn_cth (S := S))
  have hcos := Real.continuous_cos.comp_continuousOn h2θ
  have hsin := Real.continuous_sin.comp_continuousOn (continuousOn_cth (S := S))
  have h := hcos.sub (hsin.pow 2)
  convert h using 1
  ext p
  simp only [Pi.sub_apply, Pi.pow_apply, Function.comp_def, Work.Construction.c2m]




end Work.FTS_RegExport.RXT
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Sys.pw_bounds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT.Sys

open Work.FTS_RegExport.RXT (cz cth om)

/-- Helper: on the logarithmic coordinates `z = e^s`, `θ = arctan(e^ψ)` the hypotheses `hVb`,
`hRb`, `h0` transfer verbatim to the pulled-back coefficients, because `cz s > 0`,
`cth ψ ∈ (0, π/2)` and `om α s ψ > 0`. -/
theorem pw_bounds {n : ℕ} {w R : Fin n → ℝ → ℝ → ℝ → ℝ} {Vz b : ℝ → ℝ → ℝ → ℝ}
    {S M C K₀ Kσ α : ℝ} (hα : 0 < α) (hS : 0 < S)
    (hVb : ∀ z θ τ, 0 < z → 0 < θ → θ < Real.pi / 2 → τ ∈ Set.Icc (0:ℝ) S →
      |Vz z θ τ| ≤ M ∧ |b z θ τ| ≤ M)
    (hRb : ∀ k z θ τ, 0 < z → 0 < θ → θ < Real.pi / 2 → τ ∈ Set.Icc (0:ℝ) S →
      |R k z θ τ| ≤ C * ∑ j, |w j z θ τ| + Kσ * Work.FTS.RegExportIface.ω α z θ)
    (h0 : ∀ k z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |w k z θ 0| ≤ K₀ * Work.FTS.RegExportIface.ω α z θ) :
    (∀ s ψ τ, τ ∈ Set.Icc (0:ℝ) S → |coefA Vz s ψ τ| ≤ 2 * |M|) ∧
    (∀ s ψ τ, τ ∈ Set.Icc (0:ℝ) S → |coefB b s ψ τ| ≤ 2 * |M|) ∧
    (∀ s ψ τ, τ ∈ Set.Icc (0:ℝ) S → |coefC α Vz b s ψ τ| ≤ (2 + 4 * α) * |M|) ∧
    (∀ k s ψ τ, τ ∈ Set.Icc (0:ℝ) S →
      |srcF α (R k) s ψ τ| ≤ max C 0 * ∑ j, |pw α (w j) s ψ τ| + max Kσ 0) ∧
    (∀ k s ψ, |pw α (w k) s ψ 0| ≤ max K₀ 0) := by
  have h2pos : (0:ℝ) < 2 := by norm_num
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- `coefA Vz = Vz`
    intro s ψ τ hτ
    obtain ⟨hV, _⟩ := hVb (cz s) (cth ψ) τ (cz_pos s) (cth_pos ψ) (cth_lt ψ) hτ
    simp only [coefA]
    linarith [abs_nonneg M, le_abs_self M]
  · -- `coefB b = 2b`
    intro s ψ τ hτ
    obtain ⟨_, hb⟩ := hVb (cz s) (cth ψ) τ (cz_pos s) (cth_pos ψ) (cth_lt ψ) hτ
    simp only [coefB, abs_mul, abs_of_pos h2pos]
    linarith [abs_nonneg M, le_abs_self M]
  · -- `coefC α Vz b = 2Vz/(1+z) + 2α·c2m(θ)·b`
    intro s ψ τ hτ
    obtain ⟨hV, hb⟩ := hVb (cz s) (cth ψ) τ (cz_pos s) (cth_pos ψ) (cth_lt ψ) hτ
    have hcz : 0 < cz s := cz_pos s
    have hden : 0 < 1 + cz s := by linarith
    have hc2 : |Work.Construction.c2m (cth ψ)| ≤ 2 := c2m_abs_le_two _
    have hc2nn : 0 ≤ |Work.Construction.c2m (cth ψ)| := abs_nonneg _
    have hbnn : 0 ≤ |b (cz s) (cth ψ) τ| := abs_nonneg _
    have hbM : |b (cz s) (cth ψ) τ| ≤ |M| := le_trans hb (le_abs_self M)
    -- the first summand
    have hA1 : |2 * Vz (cz s) (cth ψ) τ / (1 + cz s)| ≤ 2 * |M| := by
      simp only [abs_div, abs_mul, abs_of_pos h2pos, abs_of_pos hden]
      have hstep : 2 * |Vz (cz s) (cth ψ) τ| / (1 + cz s) ≤ 2 * |Vz (cz s) (cth ψ) τ| := by
        rw [div_le_iff₀ hden]
        nlinarith [abs_nonneg (Vz (cz s) (cth ψ) τ)]
      have hVM : |Vz (cz s) (cth ψ) τ| ≤ |M| := le_trans hV (le_abs_self M)
      linarith
    -- the second summand
    have hA2 : |α * Work.Construction.c2m (cth ψ) * (2 * b (cz s) (cth ψ) τ)|
        ≤ 4 * α * |M| := by
      simp only [abs_mul, abs_of_pos hα, abs_of_pos h2pos]
      have hprod : |Work.Construction.c2m (cth ψ)| * |b (cz s) (cth ψ) τ| ≤ 2 * |M| :=
        mul_le_mul hc2 hbM hbnn (by norm_num)
      have hfac : 0 ≤ 2 * α := by linarith
      have := mul_le_mul_of_nonneg_left hprod hfac
      nlinarith [this]
    simp only [coefC]
    calc |2 * Vz (cz s) (cth ψ) τ / (1 + cz s)
            + α * Work.Construction.c2m (cth ψ) * (2 * b (cz s) (cth ψ) τ)|
        ≤ |2 * Vz (cz s) (cth ψ) τ / (1 + cz s)|
            + |α * Work.Construction.c2m (cth ψ) * (2 * b (cz s) (cth ψ) τ)| := abs_add_le _ _
      _ ≤ 2 * |M| + 4 * α * |M| := by linarith
      _ = (2 + 4 * α) * |M| := by ring
  · -- the source `srcF α (R k) = R k / om`
    intro k s ψ τ hτ
    obtain hR := hRb k (cz s) (cth ψ) τ (cz_pos s) (cth_pos ψ) (cth_lt ψ) hτ
    have hom : 0 < om α s ψ := om_pos (α := α) hα
    have hXnn : 0 ≤ ∑ j, |pw α (w j) s ψ τ| := Finset.sum_nonneg (fun j _ => abs_nonneg _)
    have hsum : ∑ j, |w j (cz s) (cth ψ) τ|
        = om α s ψ * (∑ j, |pw α (w j) s ψ τ|) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      simp only [pw, abs_div, abs_of_pos hom, mul_div_cancel₀ _ hom.ne']
    have key : |srcF α (R k) s ψ τ| ≤ C * (∑ j, |pw α (w j) s ψ τ|) + Kσ := by
      simp only [srcF, abs_div, abs_of_pos hom]
      rw [div_le_iff₀ hom]
      have heq : C * (∑ j, |w j (cz s) (cth ψ) τ|)
            + Kσ * Work.FTS.RegExportIface.ω α (cz s) (cth ψ)
          = (C * (∑ j, |pw α (w j) s ψ τ|) + Kσ) * om α s ψ := by
        rw [hsum]
        simp only [om]
        ring
      rw [← heq]
      exact hR
    calc |srcF α (R k) s ψ τ| ≤ C * (∑ j, |pw α (w j) s ψ τ|) + Kσ := key
      _ ≤ max C 0 * (∑ j, |pw α (w j) s ψ τ|) + max Kσ 0 := by
            have hC : C * (∑ j, |pw α (w j) s ψ τ|)
                ≤ max C 0 * (∑ j, |pw α (w j) s ψ τ|) :=
              mul_le_mul_of_nonneg_right (le_max_left C 0) hXnn
            linarith [le_max_left Kσ 0]
  · -- the initial datum
    intro k s ψ
    have h := h0 k (cz s) (cth ψ) (cz_pos s) (cth_pos ψ) (cth_lt ψ)
    have hom : 0 < om α s ψ := om_pos (α := α) hα
    have homnn : 0 ≤ om α s ψ := le_of_lt hom
    simp only [pw, abs_div, abs_of_pos hom]
    rw [div_le_iff₀ hom]
    calc |w k (cz s) (cth ψ) 0| ≤ K₀ * om α s ψ := by simpa only [om] using h
      _ ≤ max K₀ 0 * om α s ψ :=
            mul_le_mul_of_nonneg_right (le_max_left K₀ 0) homnn

end Work.FTS_RegExport.RXT.Sys
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Sys.pw_identity_mine =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.Sys.pw_identity_mine` — the pulled-back integrated identity

The pull-back of the integral identity `w_k(τ₂) − w_k(τ₁) = ∫(R_k − (Vz·wz_k + b·wθ_k))`
to `φ_k = w_k/om` in the logarithmic coordinates, with the pulled-back coefficients
`coefA Vz`, `coefB b`, `coefC α Vz b` and source `srcF α (R k)`.  Immediate from the
algebraic core `pw_alg` together with the constant-`om` pull-out `integral_div`.
-/

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory
namespace Work.FTS_RegExport.RXT.Sys

theorem pw_identity_mine {n : ℕ} {w wz wθ R : Fin n → ℝ → ℝ → ℝ → ℝ}
    {Vz b : ℝ → ℝ → ℝ → ℝ} {S α : ℝ} (hα : 0 < α)
    (hId : ∀ k z θ τ₁ τ₂, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 ≤ τ₁ → τ₁ ≤ τ₂ → τ₂ ≤ S →
      w k z θ τ₂ - w k z θ τ₁
        = ∫ σ in τ₁..τ₂, (R k z θ σ - (Vz z θ σ * wz k z θ σ + b z θ σ * wθ k z θ σ))) :
    ∀ k s ψ τ₁ τ₂, 0 ≤ τ₁ → τ₁ ≤ τ₂ → τ₂ ≤ S →
      pw α (w k) s ψ τ₂ - pw α (w k) s ψ τ₁
        = ∫ σ in τ₁..τ₂, (srcF α (R k) s ψ σ
            - (coefA Vz s ψ σ * pws α (wz k) (w k) s ψ σ
              + coefB b s ψ σ * pwψ α (wθ k) (w k) s ψ σ
              + coefC α Vz b s ψ σ * pw α (w k) s ψ σ)) := by
  intro k s ψ τ₁ τ₂ h1 h2 h3
  have hO : om α s ψ ≠ 0 := ne_of_gt (om_pos (α := α) hα)
  have hL : pw α (w k) s ψ τ₂ - pw α (w k) s ψ τ₁
      = (w k (cz s) (cth ψ) τ₂ - w k (cz s) (cth ψ) τ₁) / om α s ψ := by
    simp only [pw]
    field_simp
  rw [hL, hId k (cz s) (cth ψ) τ₁ τ₂ (cz_pos s) (cth_pos ψ) (cth_lt ψ) h1 h2 h3,
    ← intervalIntegral.integral_div (om α s ψ)]
  refine intervalIntegral.integral_congr ?_
  intro σ _
  exact pw_alg (α := α) hα

end Work.FTS_RegExport.RXT.Sys
end
end
