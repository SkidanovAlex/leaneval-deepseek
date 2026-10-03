import Submission.Work.Analysis.EndVar.Approx
import Submission.Work.Analysis.EndVar.varEstHalfFin_of_majorArcFam
import Submission.Work.Analysis.EndVar.majorArcVarEstimate_of_varp

/-!
# The final assembly of §5: `end-var` from the two named inputs

This module is the top of the `EndVar` chapter.  It records

* `exists_varEstHalfFin_of_inputs`: the paper's variational estimate `end-var` for the halved
  averages on the integer shift (`VarEstHalfFin TZ Measure.count P p₁ p₂ p r`), reduced to the
  two names of the chapter — a major-arc variational estimate (A) and a summable major-arc
  approximation (B) for the family `majorArcPartR Pj P d C₀` of major-arc parts;
* `EndVarFromVarpImprov`: the named `Prop` recording the further reduction of (A) to Theorem
  `varp` (`majorArcVarEstimate_of_varp`) and of (B) to the single-scale minor arc estimate
  `improv` (`ImprovToApprox`), which is the paper's route `end-var ⟸ varp + improv + iw-prop`.

The chapter is therefore:

```
  end-var  (exists_varEstHalfFin_Cv, Submission/ShiftHole.lean)
      ⟸ Assembly.exists_varEstHalfFin_of_inputs     [proved, this file]
          (A) majorArcVarEstimate_of_varp            [target, Varp.lean]
          (B) ImprovToApprox                         [target, Approx.lean]
```

with the §5 objects and the two decomposition identities in `Defs.lean`, the assembly and its
elementary variational bookkeeping in `Statements.lean` and
`varEstHalfFin_of_majorArcFam.lean`, and the summability of the error weights in `Sums.lean`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.Analysis.EndVar

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal PNat BigOperators
open PointwiseErgodicTheorems
open Submission.PointwiseErgodicTheorems
open Work.Analysis.Paraproduct (IWProjections)

/-- **The final assembly.**  Let `R = majorArcPartR Pj P d C₀` be the family of major-arc parts
built from the Ionescu--Wainger projections `Pj`.  If

* **(A)** there is a constant `Cv` with `MajorArcVarEstimate R p₁ p₂ p r Cv`, and
* **(B)** there are `Cerr, C` with `MajorArcApproximation P R p₁ p₂ p Cerr C`,

then the finite variational estimate `VarEstHalfFin` for the halved averages on the integer shift
holds with a constant `Cv'`.  This is the whole §5 reduction: (A) is supplied by the paraproduct
analysis of §4/§7--§10 through Theorem `varp` (`majorArcVarEstimate_of_varp`), and (B) by the
single-scale minor arc estimate `improv` (`ImprovToApprox`). -/
theorem exists_varEstHalfFin_of_inputs {Pj : IWProjections} {P : Polynomial ℤ} {d C₀ : ℕ}
    {p₁ p₂ p : ℝ≥0∞} {r : ℝ≥0}
    (hA : ∃ Cv : ℝ≥0 → ℝ≥0,
      MajorArcVarEstimate (majorArcPartR Pj P d C₀) p₁ p₂ p r Cv)
    (hB : ∃ (Cerr : ℝ≥0 → ℕ → ℝ≥0) (C : ℝ≥0 → ℝ≥0),
      MajorArcApproximation P (majorArcPartR Pj P d C₀) p₁ p₂ p Cerr C)
    (h1p : 1 ≤ p) (hr : 1 ≤ r)
    (hmeasR : ∀ (N : ℝ≥0) (f g : ℤ → ℂ),
      AEMeasurable (majorArcPartR Pj P d C₀ N f g) Measure.count) :
    ∃ Cv : ℝ≥0 → ℝ≥0, VarEstHalfFin TZ Measure.count P p₁ p₂ p r Cv := by
  obtain ⟨Cv, hA'⟩ := hA
  obtain ⟨Cerr, C, hB'⟩ := hB
  exact ⟨_, varEstHalfFin_of_majorArcFam (majorArcPartR Pj P d C₀) hA' hB' h1p hr hmeasR⟩

/-- **The final assembly with the paper's two named inputs.**  **(A)** the major-arc variational
estimate for `majorArcPartR` (from Theorem `varp`) together with the single-scale minor arc input
`MinorArcInput` (from `improv` + `iw-prop` + interpolation, see `Approx.lean`) gives the finite
variational estimate.  The measurability side condition of `exists_varEstHalfFin_of_inputs` is
automatic on `ℤ` with counting measure, so it is discharged here. -/
theorem exists_varEstHalfFin_of_majorArcVar_minorArc {Pj : IWProjections} {P : Polynomial ℤ}
    {d C₀ : ℕ} {p₁ p₂ p : ℝ≥0∞} {r : ℝ≥0}
    (hA : ∃ Cv : ℝ≥0 → ℝ≥0, MajorArcVarEstimate (majorArcPartR Pj P d C₀) p₁ p₂ p r Cv)
    (hB : MinorArcInput Pj P d C₀ p₁ p₂ p) (h1p : 1 ≤ p) (hr : 1 ≤ r) :
    ∃ Cv : ℝ≥0 → ℝ≥0, VarEstHalfFin TZ Measure.count P p₁ p₂ p r Cv := by
  obtain ⟨Cerr, C, hC⟩ :=
    majorArcApproximation_of_minorArc (Pj := Pj) (P := P) (d := d) (C₀ := C₀) h1p hB
  exact exists_varEstHalfFin_of_inputs hA ⟨Cerr, C, hC⟩ h1p hr
    (fun N f g => (measurable_of_countable _).aemeasurable)

/-- **The capstone of the chapter: `end-var` from `varp` and the single-scale minor arc
estimate.**  Theorem `varp` (via the *proved* reduction `majorArcVarEstimate_of_varp`) together
with the single-scale minor arc input `MinorArcInput` (from `improv` + `iw-prop` + interpolation,
see `Approx.lean`) give the finite variational estimate `VarEstHalfFin` for the halved averages
on the integer shift — i.e. the workspace's remaining hole `exists_varEstHalfFin_Cv` in the
`EndVar` formulation.

The two measurability side conditions (`hmeasPj` of `majorArcVarEstimate_of_varp` and `hmeasR` of
`exists_varEstHalfFin_of_inputs`) are automatic on `ℤ` with counting measure and are discharged
here. -/
theorem exists_varEstHalfFin_of_varp_minorArc {Pj : IWProjections} {P : Polynomial ℤ}
    {d C₀ : ℕ} {p₁ p₂ p : ℝ≥0∞} {r : ℝ≥0} (hr : 1 ≤ r) (hp : 1 ≤ p)
    (hvarp : VarpStatement Pj P d C₀ p₁ p₂ p r) (hB : MinorArcInput Pj P d C₀ p₁ p₂ p) :
    ∃ Cv : ℝ≥0 → ℝ≥0, VarEstHalfFin TZ Measure.count P p₁ p₂ p r Cv := by
  obtain ⟨Cv, hA⟩ := majorArcVarEstimate_of_varp hr hp
    (fun _ _ f => (measurable_of_countable _).aemeasurable) hvarp
  exact exists_varEstHalfFin_of_majorArcVar_minorArc ⟨Cv, hA⟩ hB hp hr

/-- **The paper's `end-var` parameters.**  The specialisation of `exists_varEstHalfFin_of_inputs`
to the hypotheses of Theorem 1.17: `P` of degree `≥ 2`, `1 < p₁, p₂ < ⊤`,
`p = (p₁⁻¹ + p₂⁻¹)⁻¹` and `2 < r`. -/
theorem exists_varEstHalfFin_of_inputs_degree {Pj : IWProjections} {P : Polynomial ℤ} {d C₀ : ℕ}
    {p₁ p₂ : ℝ≥0∞} {r : ℝ≥0}
    (hdeg : P.degree ≥ 2) (h1p₁ : 1 < p₁) (h1p₂ : 1 < p₂) (h2p₁ : p₁ < ⊤) (h2p₂ : p₂ < ⊤)
    (hH : p₁⁻¹ + p₂⁻¹ ≤ 1) (hr : 2 < r)
    (hA : ∃ Cv : ℝ≥0 → ℝ≥0,
      MajorArcVarEstimate (majorArcPartR Pj P d C₀) p₁ p₂ (p₁⁻¹ + p₂⁻¹)⁻¹ r Cv)
    (hB : ∃ (Cerr : ℝ≥0 → ℕ → ℝ≥0) (C : ℝ≥0 → ℝ≥0),
      MajorArcApproximation P (majorArcPartR Pj P d C₀) p₁ p₂ (p₁⁻¹ + p₂⁻¹)⁻¹ Cerr C)
    (hmeasR : ∀ (N : ℝ≥0) (f g : ℤ → ℂ),
      AEMeasurable (majorArcPartR Pj P d C₀ N f g) Measure.count) :
    ∃ Cv : ℝ≥0 → ℝ≥0,
      VarEstHalfFin TZ Measure.count P p₁ p₂ (p₁⁻¹ + p₂⁻¹)⁻¹ r Cv :=
  exists_varEstHalfFin_of_inputs hA hB (ENNReal.one_le_inv.mpr hH)
    (le_trans (by norm_num : (1 : ℝ≥0) ≤ 2) (le_of_lt hr)) hmeasR

end

end Work.Analysis.EndVar
