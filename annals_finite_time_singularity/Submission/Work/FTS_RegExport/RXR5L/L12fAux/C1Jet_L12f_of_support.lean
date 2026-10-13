import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.RegPkgGal.Der.Defs
import Submission.Work.FTS.RegPkgGal.Der.jet_L12f
import Submission.Work.FTS.RegPkgGal.Der.L12fDensBound
import Submission.Work.FTS.RegPkgGal.Der.L12fDensContInt
import Submission.Work.FTS.RegPkgGal.Der.integrableOn_Ioi_of_bound_of_eventually_zero
import Submission.Work.FM.Core2

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXR5L.L12fAux

/-- Monotonicity of `Work.FTS.Regularity.Jet` in its constant `N`.  (A local copy: the shared
one lives in `Work.FTS_RegExport.RXR5L.SG_C1Jet`, whose import cone is much larger than this
file needs.) -/
private theorem jet_mono {α S N N' : ℝ} {h : ℝ → ℝ → ℝ → ℝ}
    (H : Work.FTS.Regularity.Jet α S N h) (hN : N ≤ N') : Work.FTS.Regularity.Jet α S N' h := by
  refine ⟨le_trans H.1 hN, ?_, ?_⟩
  · intro z θ τ hz hθ hτ
    exact le_trans (H.2.1 z θ τ hz hθ hτ) hN
  · intro z z' θ θ' τ τ' hz hz' hθ hθ' hτ hτ'
    have h1 := H.2.2 z z' θ θ' τ τ' hz hz' hθ hθ' hτ hτ'
    have hd : (0 : ℝ) ≤ (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α :=
      Real.rpow_nonneg (by positivity) α
    exact le_trans h1 (mul_le_mul_of_nonneg_right hN hd)

theorem C1Jet_L12f_of_support {α S N Kl Lf Nt : ℝ} {F : ℝ → ℝ → ℝ → ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hS : 0 < S)
    (hJ : Work.FTS.Regularity.Jet α S N F)
    (hlin : 0 ≤ Kl ∧ ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z ∈ Set.Ioo (0:ℝ) 1,
      |F z θ τ| ≤ Kl * z)
    (hsupp : 0 < Lf ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, Lf ≤ z → F z θ τ = 0)
    (htau : 0 ≤ Nt ∧ ∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ,
      ∀ z ∈ Set.Ici (0:ℝ), |F z θ τ - F z θ τ'| ≤ Nt * z * |τ - τ'| ^ α) :
    ∃ N' : ℝ, 0 ≤ N' ∧ Work.FTS.RegPkgGal.C1Jet α S N'
      (fun z θ τ => Work.Coercivity.L12f (Work.FTS.Regularity.gSlice F τ) z) := by
  -- The `Jet` half of the conclusion is the sibling `Der.jet_L12f`; it supplies a constant `N₀`.
  obtain ⟨N₀, hJet₀⟩ := Work.FTS.RegPkgGal.Der.jet_L12f hα hα1 hS hJ hlin hsupp htau
  -- The `z`-derivative half is the fundamental theorem of calculus at `a = 0`, with the density
  -- bound of `Der.L12fDensBound` (and `Der.L12fDensContInt` for the continuity requirements).
  have hCI := Work.FTS.RegPkgGal.Der.L12fDensContInt (α := α) (S := S) (N := N)
    (Kl := Kl) (Lf := Lf) hα hJ hlin hsupp
  have hBd := (Work.FTS.RegPkgGal.Der.L12fDensBound (α := α) (S := S) (N := N)
    (Kl := Kl) (Lf := Lf) hJ hlin hsupp).1
  refine ⟨max N₀ (6 * max Kl N), le_max_of_le_left hJet₀.1, ?_, ?_⟩
  · exact jet_mono hJet₀ (le_max_left _ _)
  · intro τ hτ θ hθ z hz
    refine ⟨-(Work.FM.L12dens Work.Spaces.K (Work.FTS.Regularity.gSlice F τ) z), ?_, ?_⟩
    · exact Work.FM.hasDerivAt_L12_of_integrable (K := Work.Spaces.K)
        (f := Work.FTS.Regularity.gSlice F τ) (a := 0) (ρ := z)
        (hCI τ hτ).2 (fun s hs => (hCI τ hτ).1.continuousAt (Ioi_mem_nhds hs)) hz
    · rw [abs_neg]
      exact le_trans (hBd τ hτ z hz) (le_max_right _ _)

end Work.FTS_RegExport.RXR5L.L12fAux
