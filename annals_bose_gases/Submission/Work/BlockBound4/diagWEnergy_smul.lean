import Mathlib.Tactic.Have
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.BlockBound4.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BlockBound4

open Submission BoseGases
open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ## The `pDiagForm` factor

`pDiagForm s F Ψ = Σ_i (2π)⁻³∫_p F‖p‖·(s³)⁻¹∫_{abox}‖pSlotAmp s p Ψ i x‖²` is a sum
over slots of a double integral of a squared slot amplitude; each slot amplitude is
`ℂ`-linear in the state, so the whole form is homogeneous of degree two.  These three
lemmas are the `pDiagForm` piece of `diagWEnergy_smul`; the corresponding statements
for `cnPlus` and `qLHSword` are `Submission.BoseGases.cnPlus_smul` and
`Submission.BoseGases.qLHSword_smul`. -/

/-- The slot amplitude is `ℂ`-linear in the state: scaling the state by a real `c`
scales `pSlotAmp s p Ψ i x` by `(c : ℂ)`. -/
lemma pSlotAmp_smul_d4 (s : ℝ) (p : ℝ³) {N : ℕ} (Ψ : X N → ℝ) (i : Fin N)
    (c : ℝ) (x : X N) :
    pSlotAmp s p (c • Ψ) i x = (c : ℂ) * pSlotAmp s p Ψ i x := by
  unfold pSlotAmp
  rw [← MeasureTheory.integral_const_mul]
  apply integral_congr_ae
  filter_upwards with z
  simp only [Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

/-- The squared slot amplitude is homogeneous of degree two. -/
lemma normSq_pSlotAmp_smul (s : ℝ) (p : ℝ³) {N : ℕ} (Ψ : X N → ℝ) (i : Fin N)
    (c : ℝ) (x : X N) :
    ‖pSlotAmp s p (c • Ψ) i x‖ ^ 2 = c ^ 2 * ‖pSlotAmp s p Ψ i x‖ ^ 2 := by
  rw [pSlotAmp_smul_d4, Complex.sq_norm, Complex.normSq_mul, Complex.normSq_ofReal,
    ← Complex.sq_norm]
  ring

/-- **The `pDiagForm` factor**: `pDiagForm s F (c • Ψ) = c²·pDiagForm s F Ψ`.
Both integrals involved are the Bochner integral, whose `integral_const_mul` is
unconditional, so no integrability hypothesis is needed. -/
theorem pDiagForm_smul_aux (s : ℝ) (F : ℝ → ℝ) {N : ℕ} (Ψ : X N → ℝ) (c : ℝ) :
    pDiagForm s F (c • Ψ) = c ^ 2 * pDiagForm s F Ψ := by
  unfold pDiagForm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hI : (∫ p : ℝ³, F ‖p‖ * ((s ^ 3)⁻¹ * ∫ x in abox N s, ‖pSlotAmp s p (c • Ψ) i x‖ ^ 2))
      = c ^ 2 * (∫ p : ℝ³, F ‖p‖ *
          ((s ^ 3)⁻¹ * ∫ x in abox N s, ‖pSlotAmp s p Ψ i x‖ ^ 2)) := by
    rw [← MeasureTheory.integral_const_mul]
    apply integral_congr_ae
    filter_upwards with p
    have hx : (∫ x in abox N s, ‖pSlotAmp s p (c • Ψ) i x‖ ^ 2)
        = c ^ 2 * (∫ x in abox N s, ‖pSlotAmp s p Ψ i x‖ ^ 2) := by
      rw [← MeasureTheory.integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      rw [normSq_pSlotAmp_smul]
    rw [hx]; ring
  rw [hI]; ring

/-- **Quadratic homogeneity of the faithful energy**:
`diagWEnergy n s μ w w1 c₀ cgap (c • Φ) = c²·diagWEnergy n s μ w w1 c₀ cgap Φ`.

The energy is `cgap·cnPlus + pDiagForm s (fsKinCoeff c₀) + qLHSword`, and the
three pieces are each homogeneous of degree two under pointwise scaling
(`Submission.BoseGases.cnPlus_smul` and `Submission.BoseGases.qLHSword_smul` are
already proved; `Work.BlockBound4.pDiagForm_smul` supplies the `pDiagForm`
factor).  This is the hinge of the `le_ciInf` step in
`diagW_block_bound_of_D1`. -/
theorem diagWEnergy_smul {n : ℕ} {s μ : ℝ}
    (w w1 : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ) {c₀ cgap : ℝ}
    {Φ : X (n + 1) → ℝ} (c : ℝ) :
    diagWEnergy n s μ w w1 c₀ cgap (c • Φ)
      = (c ^ 2) * diagWEnergy n s μ w w1 c₀ cgap Φ := by
  have h1 : cnPlus s (c • Φ) = c ^ 2 * cnPlus s Φ := cnPlus_smul s Φ c
  have h2 : pDiagForm s (fsKinCoeff c₀) (c • Φ) = c ^ 2 * pDiagForm s (fsKinCoeff c₀) Φ :=
    pDiagForm_smul_aux s (fsKinCoeff c₀) Φ c
  have h3 : qLHSword (N := n + 1) s μ w w1 (c • Φ)
      = c ^ 2 * qLHSword (N := n + 1) s μ w w1 Φ := qLHSword_smul w w1 c
  unfold diagWEnergy Work.KinPSuperadd.diagKinPEnergy Work.KinPSuperadd.diagSlotWord
  rw [h1, h2, h3]
  ring

end Work.BlockBound4
