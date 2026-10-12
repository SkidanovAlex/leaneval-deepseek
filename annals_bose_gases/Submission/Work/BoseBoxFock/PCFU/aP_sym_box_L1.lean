import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open MeasureTheory

namespace Work.BoseBoxFock.PCFU

/-- **Self-adjointness of the slot mean `aP ℓ i` over the centred box `abox n ℓ`, in the `L¹` form.**
The proved `Work.BoseBoxFock.Weak.aP_sym_box` (`Submission/Work/BoseBoxFock/weakAux.lean`) and the
corpus `Submission.BoseGases.aP_sym_box` (`Submission/Q0Sector.lean`) both demand a *global
sup-norm* bound on `Ψ`; this version replaces that by the two `IntegrableOn` hypotheses that the
peel actually consumes.  Proof: mirror `Weak.aP_sym_box`'s proof -- peel the `i`-th slot of both
sides (`Submission.BoseGases.abox_integral_peel`, justified by `h1`/`h2`), rewrite
`aP ℓ i Φ (kcInsN n i (y,r))` by `Submission.BoseGases.aP_kcInsN` (a constant in `y`), pull the
constant out of the fibre integral (`MeasureTheory.integral_mul_const`,
`MeasureTheory.integral_const_mul`, both hypothesis-free), and compare the two iterated integrals.
NOTE for the file: the checker has no `open MeasureTheory`, so write `MeasureTheory.IntegrableOn`
and `MeasureTheory.volume` (or add `open MeasureTheory` above the statement). -/
theorem aP_sym_box_L1 {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin n)
    {Φ Ψ : Submission.BoseGases.X n → ℝ}
    (h1 : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n =>
      Submission.BoseGases.aP ℓ i Φ x * Ψ x) (Submission.BoseGases.abox n ℓ) MeasureTheory.volume)
    (h2 : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n =>
      Φ x * Submission.BoseGases.aP ℓ i Ψ x) (Submission.BoseGases.abox n ℓ) MeasureTheory.volume) :
    (∫ x in Submission.BoseGases.abox n ℓ, Submission.BoseGases.aP ℓ i Φ x * Ψ x)
      = ∫ x in Submission.BoseGases.abox n ℓ, Φ x * Submission.BoseGases.aP ℓ i Ψ x := by
  cases n with
  | zero => exact i.elim0
  | succ m =>
    have hP1 := Submission.BoseGases.abox_integral_peel (i := i)
      (F := fun x : Submission.BoseGases.X (m + 1) =>
        Submission.BoseGases.aP ℓ i Φ x * Ψ x) h1
    have hP2 := Submission.BoseGases.abox_integral_peel (i := i)
      (F := fun x : Submission.BoseGases.X (m + 1) =>
        Φ x * Submission.BoseGases.aP ℓ i Ψ x) h2
    have hpoint : ∀ r : Submission.BoseGases.X m,
        (∫ y in Submission.BoseGases.acube ℓ,
            Submission.BoseGases.aP ℓ i Φ (Submission.BoseGases.kcInsN m i (y, r))
              * Ψ (Submission.BoseGases.kcInsN m i (y, r)))
          = ∫ y in Submission.BoseGases.acube ℓ,
              Φ (Submission.BoseGases.kcInsN m i (y, r))
                * Submission.BoseGases.aP ℓ i Ψ (Submission.BoseGases.kcInsN m i (y, r)) := by
      intro r
      have hL : (∫ y in Submission.BoseGases.acube ℓ,
            Submission.BoseGases.aP ℓ i Φ (Submission.BoseGases.kcInsN m i (y, r))
              * Ψ (Submission.BoseGases.kcInsN m i (y, r)))
          = (1 / ℓ ^ 3)
              * (∫ z in Submission.BoseGases.acube ℓ,
                  Φ (Submission.BoseGases.kcInsN m i (z, r)))
              * (∫ y in Submission.BoseGases.acube ℓ,
                  Ψ (Submission.BoseGases.kcInsN m i (y, r))) := by
        simp only [Submission.BoseGases.aP_kcInsN]
        rw [MeasureTheory.integral_const_mul]
      have hR : (∫ y in Submission.BoseGases.acube ℓ,
            Φ (Submission.BoseGases.kcInsN m i (y, r))
              * Submission.BoseGases.aP ℓ i Ψ (Submission.BoseGases.kcInsN m i (y, r)))
          = (1 / ℓ ^ 3)
              * (∫ z in Submission.BoseGases.acube ℓ,
                  Φ (Submission.BoseGases.kcInsN m i (z, r)))
              * (∫ y in Submission.BoseGases.acube ℓ,
                  Ψ (Submission.BoseGases.kcInsN m i (y, r))) := by
        simp only [Submission.BoseGases.aP_kcInsN]
        rw [MeasureTheory.integral_mul_const]
        ring
      rw [hL, hR]
    rw [hP1, hP2]
    refine integral_congr_ae ?_
    filter_upwards with r
    exact hpoint r

end Work.BoseBoxFock.PCFU
