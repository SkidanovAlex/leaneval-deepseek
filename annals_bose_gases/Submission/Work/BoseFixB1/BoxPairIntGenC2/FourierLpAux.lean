import Mathlib.Analysis.Fourier.LpSpace
import Submission.Commons.Analysis.Fourier.integral_norm_sq_fourier_l1l2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Auxiliary Plancherel facts for the Fourier transform on finite-dimensional inner product spaces

This module collects the small Plancherel corollaries that the `L¹` Fourier-transform lemma
`Work.BoseFixB1.BoxPairIntGenC2.fourier_memLp_one_of_contDiff_two` and its companion lemmas rely
on.  The substantive input is the team lemma

* `Commons.Analysis.Fourier.fourier_toLp_ae_eq_fourier_of_memLp` — on `L¹ ∩ L²` the `L²`
  (Plancherel) Fourier transform is a.e. the pointwise Fourier integral.

from which we deduce that the pointwise Fourier integral of an `L¹ ∩ L²` function is again `L²`.
-/

noncomputable section

open MeasureTheory
open scoped FourierTransform

namespace Work.BoseFixB1.BoxPairIntGenC2

/-- **Plancherel, `L¹ ∩ L²` case.**  The pointwise Fourier integral of a function which is both
integrable and square-integrable is square-integrable. -/
theorem memLp_two_fourier {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] {f : V → ℂ}
    (h1 : MemLp f 1 (volume : Measure V)) (h2 : MemLp f 2 (volume : Measure V)) :
    MemLp (𝓕 f) 2 (volume : Measure V) :=
  (Lp.memLp (𝓕 (h2.toLp f))).ae_eq
    (Commons.Analysis.Fourier.fourier_toLp_ae_eq_fourier_of_memLp h1 h2)

/-- **Plancherel, `L¹ ∩ L²` case, squared-norm form.**  The squared modulus of the pointwise
Fourier integral of an `L¹ ∩ L²` function is integrable. -/
theorem integrable_norm_fourier_sq' {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] {f : V → ℂ}
    (h1 : MemLp f 1 (volume : Measure V)) (h2 : MemLp f 2 (volume : Measure V)) :
    Integrable (fun ξ : V => ‖𝓕 f ξ‖ ^ 2) (volume : Measure V) := by
  have h := memLp_two_fourier h1 h2
  exact (memLp_two_iff_integrable_sq_norm h.aestronglyMeasurable).mp h

end Work.BoseFixB1.BoxPairIntGenC2
