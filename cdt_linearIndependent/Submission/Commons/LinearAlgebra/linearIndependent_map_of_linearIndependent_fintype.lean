import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

/-!
# Base change of a linearly independent family of functions

If `v : ι → σ → K` is linearly independent over a field `K`, and `σ` is finite, then
applying `algebraMap K L` pointwise produces a family that is linearly independent over
any field extension `L` of `K`.

This is the finite-index (`[Fintype σ]`) form of Mathlib's
`linearIndependent_algebraMap_comp_iff`.
-/

namespace Commons.LinearAlgebra

theorem linearIndependent_map_of_linearIndependent_fintype {K L : Type*} [Field K] [Field L] [Algebra K L] {ι σ : Type*} [Fintype σ] (v : ι → σ → K) (h : LinearIndependent K v) : LinearIndependent L (fun i : ι => fun s : σ => algebraMap K L (v i s)) := by
  exact (linearIndependent_algebraMap_comp_iff (R := K) (S := L) (v := v)).mpr h

end Commons.LinearAlgebra