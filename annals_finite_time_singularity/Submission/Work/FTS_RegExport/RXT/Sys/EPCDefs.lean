import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Construction.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.Sys.EPCDefs` — the datum interface of `explicit_pieces_coeff`

The target `Work.FTS_RegExport.RXT.Sys.explicit_pieces_coeff` bounds the `mixed`-jets
(`j + i ≤ 2`) of the four explicit pieces built from the profile
`F(τ) = Ftau (pExp α) (GR α g) τ = F_* + gS α (tauExt g)(τ)`:

* `L₁₂(F)(z) · c2m θ`, `L₁₂(F)(z)`, `sin²θ · 𝔽K(F)(z)`, and `Uop α (Θ α F) / sin 2θ`
  (which on the open quadrant is the radial combination `-(3/(4β))·L₁₂(F) + (1/4)·𝔽K(F)`).

Everything reduces to bounds for the iterated `z∂_z`-jets (order `≤ 2`) of the two radial
transforms `L₁₂(F)` and `𝔽K(F)` of the datum `F`.  This module fixes the interface used to
state that reduction:

* `DatumBnd F C` — `|F|`, `|D_zF|`, `|D_z²F| ≤ C` on the open quadrant;
* `DatumHyp F C` — the `C²`-smoothness of `F` on the open quadrant, the pointwise bound
  `DatumBnd F C`, and the `L¹`-control of the `L₁₂`-density which makes `L₁₂(F)` a primitive.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT.Sys

set_option autoImplicit false

/-- **Pointwise bounds of the first three `D_z`-jets of a datum** on the open quadrant. -/
def DatumBnd (F : ℝ → ℝ → ℝ) (C : ℝ) : Prop :=
  ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
    |F z θ| ≤ C ∧ |Work.Spaces.Dz F z θ| ≤ C ∧ |Work.Spaces.DzIter 2 F z θ| ≤ C

/-- **The hypotheses of the `𝔽K`/`L₁₂` jet package**: `C²`-smoothness of the datum on the
open quadrant, the pointwise jet bounds `DatumBnd`, and the `L¹`-control of the `L₁₂`-density
(with the total mass bounded by the same constant `C`). -/
def DatumHyp (F : ℝ → ℝ → ℝ) (C : ℝ) : Prop :=
  ContDiffOn ℝ 2 (Function.uncurry F) Work.FTS.EllipticEst.Q0 ∧
    DatumBnd F C ∧
    MeasureTheory.IntegrableOn (Work.Construction.L12dens F) (Set.Ioi 0) ∧
    (∫ s in Set.Ioi 0, |Work.Construction.L12dens F s|) ≤ C

theorem DatumHyp.smooth {F : ℝ → ℝ → ℝ} {C : ℝ} (h : DatumHyp F C) :
    ContDiffOn ℝ 2 (Function.uncurry F) Work.FTS.EllipticEst.Q0 := h.1

theorem DatumHyp.bnd {F : ℝ → ℝ → ℝ} {C : ℝ} (h : DatumHyp F C) : DatumBnd F C := h.2.1

theorem DatumHyp.integrable {F : ℝ → ℝ → ℝ} {C : ℝ} (h : DatumHyp F C) :
    MeasureTheory.IntegrableOn (Work.Construction.L12dens F) (Set.Ioi 0) := h.2.2.1

theorem DatumHyp.mass {F : ℝ → ℝ → ℝ} {C : ℝ} (h : DatumHyp F C) :
    (∫ s in Set.Ioi 0, |Work.Construction.L12dens F s|) ≤ C := h.2.2.2

end Work.FTS_RegExport.RXT.Sys
