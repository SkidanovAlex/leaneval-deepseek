import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS_RegExport.RXT.Slots.v2_hkMem_pointwise_min
import Submission.Work.FTS_RegExport.RXT.Slots.v2_paramC2
import Submission.Work.FTS_RegExport.RXT.C2Radial
import Submission.Work.FTS_RegExport.RXT.velPert
import Submission.Work.FTS.RegExportIface.RXT.Leaves

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.Sys.pert_tilde_contDiffOn` — `Φ̃(τ)` is `C³` on the open quadrant

The residual `Φ̃(τ) = PhiTil (pExp α) (g(τ)) (E (g(τ)))` — i.e.
`E (g(τ)) - Θ(pExp α)(g(τ))` with `Θ α F = (1/(4α)) sin 2θ · L₁₂(F)`, written in the
`PhiTil`-form of `Work.Construction` — is of class `C³` on the open quadrant, for every
`τ ≥ 0`, under the two hypotheses `EllLimOK3 (pExp α) E` and `DynOK' (pExp α) C₀ Φs E g`.

This is the `ContDiffOn` half of the block inside `RXT.velPert` (which also computes the
convergence of the jets of `Φ̃` along the class-`C` approximating sequence); only the
regularity statement is needed here, so the proof is that block with the jet analysis removed.

* the `E`-part: `EllLimOK3` applied to the constant-in-`n` limit `f = slice g τ` along the
  class-`C` approximants `gn` supplied by the `LimApprox` clause of `DynOK'`, at a horizon
  `T = max 1 (τ+1) ≥ τ`.  Its hypotheses are `ClassC (pExp α) (slice (gn n) τ)`,
  `Xn6 (pExp α) (slice (gn n) τ) ≤ B` (both from `LimApprox`), the `C⁴`-regularity of the limit
  (`RegPkgMin.c4`) and the order-`4` jet convergence (`LimApprox`);
* the `Θ`-part: `Θ = const · sin 2θ · L₁₂(g(τ))` factors through the radial function
  `L₁₂(g(τ))`, which is `C³` as soon as the angular moment `𝔽K(g(τ)) = ∫_θ g(τ)·K` is `C²`;
  that in turn is the parametric-integral lemma `paramC2`, whose pointwise bound hypothesis
  comes from the trace-free `ℋ⁴ → L^∞` trade-off `Slots.v2_hkMem_pointwise_min` (wrapped in
  `pert_hkMem_bound` below), applied with the uniform `ℋ⁴`-bound `Xn (g(τ)) ≤ C₀α²` of `DynOK`.
-/

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_RegExport.RXT.Sys

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.Regularity (pExp)

set_option autoImplicit false

/-- The trace-free `ℋ⁴ → L^∞` trade-off `v2_hkMem_pointwise_min`, in the wrapper form used
below (`min z 1 ≤ 1`).  This is `RXT.velPert_hkMem_bound` with the trace-free input
`Slots.v2_hkMem_pointwise_min` in place of `RXT.hkMem_pointwise_min` (which is not available
`sorry`-free). -/
private theorem pert_hkMem_bound {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : ℝ → ℝ → ℝ) (M : ℝ),
      ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0 → Work.Spaces.HkMem α 4 f →
      Work.Spaces.HkNorm α 4 f ≤ M →
      ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.mixed j i f z θ| ≤ C * M * min z 1 := by
  obtain ⟨C, hC0, hC⟩ := Work.FTS_RegExport.RXT.v2_hkMem_pointwise_min hα hα1
  refine ⟨C, hC0, ?_⟩
  intro f M hsm hmem hMn j i hji z θ hz hθ hθ2
  have h1 := hC f hsm hmem j i (by omega) z θ hz hθ hθ2
  have hM0 : 0 ≤ M := le_trans (Work.Spaces.HkNorm_nonneg α 4 f) hMn
  have hm0 : 0 ≤ min z 1 := le_min hz.le zero_le_one
  calc |Work.Spaces.mixed j i f z θ| ≤ C * min z 1 * Work.Spaces.HkNorm α 4 f := h1
    _ ≤ C * min z 1 * M := mul_le_mul_of_nonneg_left hMn (mul_nonneg hC0 hm0)
    _ = C * M * min z 1 := by ring

theorem pert_tilde_contDiffOn {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEL3 : Work.FTS.FinalV2.EllLimOK3 (Work.FTS.Regularity.pExp α) E)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g) :
    ∀ τ : ℝ, 0 ≤ τ →
      ContDiffOn ℝ 3 (Function.uncurry (fun z θ => Work.Construction.PhiTil
        (Work.FTS.Regularity.pExp α) (Work.FTS.Galerkin.slice g τ)
        (E (Work.FTS.Galerkin.slice g τ)) z θ)) Work.FTS.EllipticEst.Q0 := by
  intro τ hτ
  have hαG : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hαG1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  -- a horizon `T > 0` with `τ ∈ [0,T]`, for the approximating sequence of `LimApprox`
  have hS : (0 : ℝ) < max 1 (τ + 1) := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hτS : τ ∈ Set.Icc (0 : ℝ) (max 1 (τ + 1)) :=
    ⟨hτ, le_trans (by linarith) (le_max_right (1 : ℝ) (τ + 1))⟩
  obtain ⟨gn, B, L, hApprox, _hLip, hJet, _hμ⟩ := hOK.2 (max 1 (τ + 1)) hS
  -- the data of the limit slice
  have hF4 : ContDiffOn ℝ 4 (Function.uncurry (slice g τ)) Work.FTS.EllipticEst.Q0 :=
    hOK.1.1.c4 τ hτ
  have hFmem : Work.Spaces.HkMem (Work.FTS.Regularity.pExp α) 4 (slice g τ) :=
    hOK.1.1.mem4 τ hτ
  have hFnorm : Work.Spaces.HkNorm (Work.FTS.Regularity.pExp α) 4 (slice g τ)
      ≤ max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2 := by
    have h2 : C₀ * (Work.FTS.Regularity.pExp α) ^ 2
        ≤ max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2 :=
      mul_le_mul_of_nonneg_right (le_max_left C₀ 0) (sq_nonneg (Work.FTS.Regularity.pExp α))
    exact le_trans (hOK.1.2 τ hτ) h2
  -- ## the `E`-part: `E (g(τ))` is `C³` on the open quadrant
  obtain ⟨_hBsl, hElim3, _hEconv⟩ := hEL3 (fun n => slice (gn n) τ) (slice g τ) B
    (fun n => (hApprox n τ hτS).1) (fun n => (hApprox n τ hτS).2.2) hF4
    (fun j i hji z' θ' hzθ => hJet τ hτS j i hji z' θ' hzθ)
  -- ## the `Θ`-part: `L₁₂(g(τ))` is `C³` on `(0,∞)`
  obtain ⟨C4, hC40, hC4⟩ := pert_hkMem_bound hαG hαG1
  have hFKlim : ContDiffOn ℝ 2 (Work.Construction.FK (slice g τ)) (Set.Ioi 0) := by
    have hF2 : ContDiffOn ℝ 2 (Function.uncurry (slice g τ))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := hF4.of_le (by norm_num)
    have hbase : ∀ (b : ℕ), b ≤ 2 → ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 →
        |Work.Spaces.mixed b 0 (slice g τ) z' θ'|
          ≤ C4 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2) := by
      intro b hb z' θ' hz' hθ' hθ'2
      have h1 := hC4 (slice g τ) (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2) hF4 hFmem
        hFnorm b 0 (by omega) z' θ' hz' hθ' hθ'2
      have h2 : C4 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2) * min z' 1
          ≤ C4 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2) * 1 :=
        mul_le_mul_of_nonneg_left (min_le_right _ _)
          (mul_nonneg hC40 (mul_nonneg (le_max_right C₀ 0)
            (sq_nonneg (Work.FTS.Regularity.pExp α))))
      linarith [h1, h2]
    have hb : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 →
        |(slice g τ) z' θ'| ≤ C4 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2) ∧
        |Work.Spaces.Dz (slice g τ) z' θ'|
          ≤ C4 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2) ∧
        |Work.Spaces.DzIter 2 (slice g τ) z' θ'|
          ≤ C4 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2) :=
      fun z' θ' hz' hθ' hθ'2 =>
        ⟨by simpa using hbase 0 (by norm_num) z' θ' hz' hθ' hθ'2,
         by simpa using hbase 1 (by norm_num) z' θ' hz' hθ' hθ'2,
         by simpa using hbase 2 (by norm_num) z' θ' hz' hθ' hθ'2⟩
    exact Work.FTS_RegExport.RXT.velPertAux.paramC2 (φ := Work.Spaces.K)
      (C := C4 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2))
      Work.FTS_RegExport.RXT.velPert_continuousOn_K hF2 hb
  have hL12lim : ContDiffOn ℝ 3 (Work.Construction.L12 (slice g τ)) (Set.Ioi 0) :=
    Work.FTS_RegExport.RXT.contDiffOn_three_L12 hFKlim
  have hΘ3lim : ContDiffOn ℝ 3
      (Function.uncurry (Work.Construction.Theta (Work.FTS.Regularity.pExp α) (slice g τ)))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS_RegExport.RXT.velPert_contDiffOn_Theta (α := Work.FTS.Regularity.pExp α) hL12lim
  -- ## `Φ̃ = E(g(τ)) - Θ(g(τ))`
  refine ((hElim3.sub hΘ3lim)).congr fun p _ => ?_
  rcases p with ⟨z', θ'⟩
  simp only [Function.uncurry, Work.Construction.PhiTil]

end Work.FTS_RegExport.RXT.Sys
