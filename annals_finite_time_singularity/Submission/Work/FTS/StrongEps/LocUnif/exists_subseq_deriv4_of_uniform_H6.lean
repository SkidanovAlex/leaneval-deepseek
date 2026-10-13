import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.CategoryTheory.Abelian.Ext
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.LocUnif.LocExtract
import Submission.Work.FTS.StrongEps.LocUnif.sup_bound_of_holder_L2
import Submission.Work.FTS.StrongEps.LocUnif.mixed_morrey_step
import Submission.Work.FTS.StrongEps.LocUnif.mixed_rect_L2_bounds
import Submission.Work.FTS.StrongEps.LocUnif.exists_subseq_tendstoLocallyUniformlyOn_fin

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `C⁴`-extraction of `Work.FTS.StrongEps.LocUnif.exists_subseq_deriv4_of_uniform_H6`

This is the final assembly of the extraction: the four analytic inputs live in the sibling files
of this directory (`mixed_rect_L2_bounds`, `mixed_morrey_step`, `sup_bound_of_holder_L2`,
`exists_subseq_tendstoLocallyUniformlyOn_fin`), collected into the structure
`Work.FTS.StrongEps.LocUnif.Inputs`; the extraction itself and the structural theorems
(`limData_of_conv`, `contDiffOn_four_of_LimData`, `identify`) are in `LocExtract` / `LocTower`.
-/

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.LocUnif

set_option autoImplicit false

/-- The four analytic inputs of the extraction, assembled from the sibling files of this
directory. -/
theorem inputs_of_children {α : ℝ} (hα : 0 < α) : Inputs α := by
  refine { L2 := ?_, Mor := ?_, Sup := ?_, Ext := ?_ }
  · intro a b c d ha hab hc hd
    obtain ⟨C, hCpos, hCb⟩ := mixed_rect_L2_bounds ha hab hc hd
    exact ⟨C, hCpos, fun F hF hmem j i hji => hCb α hα F hF hmem j i hji⟩
  · intro χ F C C₀ M Km a b c d a' b' c' d' hmor hKmnn hα' hC₀nn hCpos hχC2 hχcs hχnn hχle1
      hχone hχzero hMfd1 hMfd2 hsub hFsm hFmem hFbd hrect
    exact mixed_morrey_step hmor hKmnn hα' hC₀nn hCpos hχC2 hχcs hχnn hχle1 hχone hχzero
      hMfd1 hMfd2 hsub hFsm hFmem hFbd hrect
  · intro M a b c d C₁ C₂ hab hcd hC₁ hC₂ hcont hholder hL2
    exact sup_bound_of_holder_L2 (M := M) hab hcd hC₁ hC₂ hcont hholder hL2
  · intro k U hU F hbdd heqc
    exact exists_subseq_tendstoLocallyUniformlyOn_fin hU hbdd heqc

theorem exists_subseq_deriv4_of_uniform_H6 {α B : ℝ} (hα : 0 < α)
    {G : ℕ → ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ∀ k : ℕ, ContDiffOn ℝ k (Function.uncurry (G n))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hmem : ∀ n : ℕ, Work.Spaces.HkMem α 6 (G n))
    (hb : ∀ n : ℕ, Work.Spaces.HkNorm α 6 (G n) ≤ B) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f : ℝ → ℝ → ℝ,
      (∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) →
        TendstoUniformlyOn (fun n (p : ℝ × ℝ) => G (φ n) p.1 p.2) (fun p => f p.1 p.2)
          Filter.atTop K) ∧
      ContDiffOn ℝ 4 (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) ∧
      ∀ (j i : ℕ), j + i ≤ 4 → ∀ K : Set (ℝ × ℝ), IsCompact K →
        K ⊆ Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) →
        TendstoUniformlyOn (fun n (p : ℝ × ℝ) => Work.Spaces.mixed j i (G (φ n)) p.1 p.2)
          (fun p => Work.Spaces.mixed j i f p.1 p.2) Filter.atTop K := by
  have hsm' : ∀ n : ℕ, Work.FTS.EllipticEst.SmoothOpen (G n) := fun n =>
    Work.FTS.EllipticEst.smoothOpen_of_forall (hsm n)
  obtain ⟨φ, hφ, F, hF⟩ := exists_limData hα hsm' hmem hb (inputs_of_children hα)
  obtain ⟨h1, h2, h3⟩ := conclusion_of_limData hsm' hF
  exact ⟨φ, hφ, F 0 0, h1, h2, h3⟩

end Work.FTS.StrongEps.LocUnif
