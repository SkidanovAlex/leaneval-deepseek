import Mathlib
import Submission.Work.Drive.ProjectiveTopology

/-!
# A globally smooth model of the *class equality* on `ℝP³`

The genericity statement `ClassTripleRegular` (the lead's `L5`) has to be produced from a **globally
smooth** system whose zeros are exactly the triples of plane parameters with a common class.  The
projective chart `projChartMap i` is a chart, so its coordinate functions are only smooth on the chart
source; on the whole of `ℝP³` one needs a global smooth "difference" map whose zero set is the diagonal
of `ℝP³ × ℝP³`.

This file provides one, using the identification `ℝ⁴ ≅ ℍ` of the capping space's class space `ℝP³` with
the quaternions modulo `±1`: for vectors `v, w ∈ ℍ` the imaginary part of `v · conj w` vanishes exactly
when `v` and `w` are real multiples of one another, i.e. when they represent the *same* class.  The map

`qform v w := Im (v · conj w) = w₀ • v' - v₀ • w' - (v' × w')`

(with `v = (v₀, v')`, `w = (w₀, w')` and `×` the cross product in the imaginary `ℝ³`) is bilinear,
anti-symmetric and smooth on the whole of `ℝ⁴ × ℝ⁴`; the properties are proved in
`Work.Drive.qform_bilinear`, and its kernel in the second variable is the line `ℝ v` for `v ≠ 0`
(`Work.Drive.qform_kernel`).

`Eucl 3 = ℝ⁴` is indexed by `Fin 4`; `0 : Fin 4` is the "real" coordinate and `Fin.succ : Fin 3 → Fin 4`
the three imaginary coordinates, so that the imaginary part is a vector of `ℝ³`.
-/

namespace Work.Drive

open scoped ContDiff Topology

noncomputable section

/-- The imaginary part of a vector of `Eucl 3 = ℝ⁴ ≅ ℍ`, as a vector of `ℝ³`. -/
def imagPart (v : Eucl 3) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 (fun i : Fin 3 => v (Fin.succ i))

@[simp] lemma imagPart_ofLp (v : Eucl 3) (i : Fin 3) : (imagPart v).ofLp i = v (Fin.succ i) := by
  simp only [imagPart, WithLp.ofLp_toLp]

/-- The imaginary part of `v · conj w` for `v, w ∈ Eucl 3 = ℝ⁴ ≅ ℍ`, as a vector of `ℝ³`. -/
def qform (v w : Eucl 3) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 (fun k : Fin 3 =>
    w 0 * v (Fin.succ k) - v 0 * w (Fin.succ k)
      - (crossProduct (imagPart v) (imagPart w)) k)

@[simp] lemma qform_ofLp (v w : Eucl 3) (k : Fin 3) :
    (qform v w).ofLp k =
      w 0 * v (Fin.succ k) - v 0 * w (Fin.succ k)
        - (crossProduct (imagPart v) (imagPart w)) k := by
  simp only [qform, WithLp.ofLp_toLp]

end

end Work.Drive
