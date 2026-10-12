import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.B13Aux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.ae_eval_compl`

On the one-slot fibre `Fib1 p = I1 p → E3` (with the product measure), the evaluation of a
configuration at the slot `p.1` is almost everywhere outside any null set `N ⊆ E3`.

This is the marginal statement behind the fibre decompositions: the product volume
`Measure.pi (fun _ : I1 p => volume)` is mapped by `Function.eval ⟨p.1, hp⟩` to `volume` up to a
constant factor, hence `QuasiMeasurePreserving`, and the preimage of a null set is null.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock

theorem ae_eval_compl {n : ℕ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2) {N : Set (EuclideanSpace ℝ (Fin 3))} (hN : MeasurableSet N) (h0 : MeasureTheory.volume N = 0) : ∀ᵐ x' : Work.BoseBoxFock.Fib1 p, x' ⟨p.1, hp⟩ ∉ N := by
  have hg : ∀ᵐ x : EuclideanSpace ℝ (Fin 3), x ∉ N := by
    rw [MeasureTheory.ae_iff]
    simpa using h0
  have hqmp := MeasureTheory.Measure.quasiMeasurePreserving_eval
    (μ := fun _ : I1 p => (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3))))
    (⟨p.1, hp⟩ : I1 p)
  exact hqmp.ae hg

end Work.BoseBoxFock
