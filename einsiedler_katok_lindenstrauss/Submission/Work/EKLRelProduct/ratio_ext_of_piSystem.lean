import Mathlib
import Submission.Work.EKLContract.Defs
import Submission.Work.EKLRelProduct.measure_ne_top_of_compl_eq_zero
import Submission.Work.EKLRelProduct.inv_smul_restrict_ne_top
import Submission.Work.EKLRelProduct.toReal_inv_smul_apply
import Submission.Work.EKLRelProduct.toReal_inv_smul_restrict_apply

namespace Work.EKLRelProduct

open MeasureTheory

/-- **Ratio extension from a π-system.**

Let `ν₁`, `ν₂` be measures on `SL₃(ℝ)`, let `S` be a Borel set with `0 < ν₁ S < ∞`,
`0 < ν₂ S < ∞`, and suppose `ν₂` is carried by `S` (i.e. `ν₂ Sᶜ = 0`).  If the
`ν₁`-normalised `S`-restriction and the `ν₂`-normalised measure agree on a π-system `C`
which generates the Borel σ-algebra and which contains a countable cover of `SL₃(ℝ)`,
then they agree on every Borel set.

The proof normalises both measures to probability measures
`(ν₁ S)⁻¹ • ν₁.restrict S` and `(ν₂ S)⁻¹ • ν₂`; the hypothesis `ν₂ Sᶜ = 0` makes the second
one finite, so that on the π-system the equality of `toReal`-ratios upgrades to equality of
the two `ℝ≥0∞`-valued measures (`ENNReal.toReal_eq_toReal_iff'`), and then
`Measure.ext_of_generateFrom_of_iUnion` extends that equality to the generated σ-algebra. -/
theorem ratio_ext_of_piSystem {ν₁ ν₂ : MeasureTheory.Measure Work.EKLContract.SL3}
    {S : Set Work.EKLContract.SL3}
    (hS : @MeasurableSet Work.EKLContract.SL3 (borel Work.EKLContract.SL3) S)
    (hd₁ : 0 < ν₁ S) (hd₁' : ν₁ S < ⊤) (hd₂ : 0 < ν₂ S) (hd₂' : ν₂ S < ⊤)
    (hcar : ν₂ Sᶜ = 0)
    {C : Set (Set Work.EKLContract.SL3)} (hC : IsPiSystem C)
    (hgen : MeasurableSpace.generateFrom C = borel Work.EKLContract.SL3)
    {Bs : ℕ → Set Work.EKLContract.SL3} (hBs : ⋃ i, Bs i = Set.univ) (hBsC : ∀ i, Bs i ∈ C)
    (h : ∀ B ∈ C, (ν₁ (B ∩ S)).toReal / (ν₁ S).toReal = (ν₂ B).toReal / (ν₂ S).toReal) :
    ∀ B : Set Work.EKLContract.SL3, @MeasurableSet Work.EKLContract.SL3 (borel Work.EKLContract.SL3) B →
      (ν₁ (B ∩ S)).toReal / (ν₁ S).toReal = (ν₂ B).toReal / (ν₂ S).toReal := by
  -- `ν₂` is finite everywhere, because it is carried by the finite-measure set `S`.
  have hfin₂ : ∀ t : Set Work.EKLContract.SL3, (((ν₂ S)⁻¹) • ν₂) t ≠ ⊤ := by
    intro t
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr (ne_of_gt hd₂))
      (measure_ne_top_of_compl_eq_zero hcar (ne_of_lt hd₂') t)
  -- `(ν₁ S)⁻¹ • ν₁.restrict S` is finite everywhere, being a sub-probability measure.
  have hfin₁ : ∀ t : Set Work.EKLContract.SL3, (((ν₁ S)⁻¹) • (ν₁.restrict S)) t ≠ ⊤ :=
    fun t => inv_smul_restrict_ne_top (ne_of_gt hd₁) (ne_of_lt hd₁') t
  -- On the π-system the two normalised measures coincide.
  have heqC : ∀ s ∈ C, (((ν₁ S)⁻¹) • (ν₁.restrict S)) s = (((ν₂ S)⁻¹) • ν₂) s := by
    intro s hs
    refine (ENNReal.toReal_eq_toReal_iff' (hfin₁ s) (hfin₂ s)).mp ?_
    rw [toReal_inv_smul_restrict_apply ν₁ hS s, toReal_inv_smul_apply ν₂ S s]
    exact h s hs
  have hμeq : (((ν₁ S)⁻¹) • (ν₁.restrict S)) = (((ν₂ S)⁻¹) • ν₂) :=
    Measure.ext_of_generateFrom_of_iUnion C Bs hgen.symm hC hBs hBsC (fun i => hfin₁ (Bs i)) heqC
  intro B hB
  have hB' : (((ν₁ S)⁻¹) • (ν₁.restrict S)) B = (((ν₂ S)⁻¹) • ν₂) B := congrArg (fun μ => μ B) hμeq
  have hto := congrArg ENNReal.toReal hB'
  rw [toReal_inv_smul_restrict_apply ν₁ hS B, toReal_inv_smul_apply ν₂ S B] at hto
  exact hto

end Work.EKLRelProduct
