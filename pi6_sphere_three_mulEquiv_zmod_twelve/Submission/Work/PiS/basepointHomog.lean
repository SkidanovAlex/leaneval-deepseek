import Mathlib
import Submission.Work.PiS.Interfaces
import Submission.Work.PiS.sphereIsometryHomeomorph
import Submission.Work.PiS.reflectionSphere
import Submission.Work.Stems.mulEquiv_of_homotopyEquiv

set_option synthInstance.maxHeartbeats 400000

/-!
# Area BASEPT: the homotopy groups of `Sⁿ` do not depend on the base point

For the sphere `Sph n = Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1` and any two points
`x y : Sph n` we produce a bijection `π_k(Sⁿ,x) ≃ π_k(Sⁿ,y)`, i.e. `Work.PiS.BasepointHomog`.

The construction is uniform in `n` (including the degenerate case `n = 0`, where `Sph 0` is the
two-point space `{±1}`).

* `k = 0`: `π₀` is `ZerothHomotopy`, which is *defined* from the whole space and makes no reference
  to the base point, so both sides are canonically equivalent to the same type
  (`HomotopyGroup.pi0EquivZerothHomotopy`).

* `k ≥ 1`: reflection of the ambient Euclidean space in the hyperplane orthogonal to `x - y`
  (`Submodule.reflection` of `(ℝ ∙ (x - y))ᗮ`) is a linear isometry equivalence
  (`Work.PiS.reflectionSphere` computes that it carries `x` to `y`), hence restricts to a
  homeomorphism `Φ` of the sphere with `Φ x = y` (`Work.PiS.sphereIsometryHomeomorph`).  A
  homeomorphism — more generally a homotopy equivalence — of a space with `Φ x = y` induces an
  isomorphism of homotopy groups `π_k(X,x) ≃* π_k(X, Φ x)`
  (`Work.Stems.mulEquiv_of_homotopyEquiv`), and the base point `Φ x` is transported to `y` along
  the *equality* `Φ x = y` (a `cast` on the base-point index, for which no further naturality is
  needed).  This is `homotopyGroupEquivOfHomeomorph` below.

The resulting equivalence is a plain `Equiv`; the group structure is not part of the contract.
-/

namespace Work.PiS

noncomputable section

open scoped Topology

/-- **Base point change along a homeomorphism.**  If `Φ` is a homeomorphism of `X` with
`Φ x = y`, then `π_k(X,x)` and `π_k(X,y)` are in bijection (`k ≥ 1`). -/
theorem homotopyGroupEquivOfHomeomorph {X : Type*} [TopologicalSpace X] (k : ℕ) (hk : 1 ≤ k)
    {x y : X} (Φ : X ≃ₜ X) (hxy : Φ x = y) :
    Nonempty (HomotopyGroup (Fin k) X x ≃ HomotopyGroup (Fin k) X y) := by
  haveI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  -- a homeomorphism is a homotopy equivalence, and the induced isomorphism lands at `Φ x`
  obtain ⟨e⟩ := Work.Stems.mulEquiv_of_homotopyEquiv (N := Fin k) Φ.toHomotopyEquiv x
  -- the underlying map of `Φ.toHomotopyEquiv` is `Φ`, so its value at `x` is `y`
  have h' : Φ.toHomotopyEquiv.toFun x = y := by
    rw [Homeomorph.coe_toHomotopyEquiv]
    exact hxy
  exact ⟨e.toEquiv.trans (Equiv.cast (congrArg (fun t : X => HomotopyGroup (Fin k) X t) h'))⟩

theorem basepointHomog : Work.PiS.BasepointHomog := by
  intro n k x y
  rcases k with _ | j
  · -- `π₀` is the set of path components, which does not depend on the base point
    exact ⟨(HomotopyGroup.pi0EquivZerothHomotopy (x := x)).trans
      (HomotopyGroup.pi0EquivZerothHomotopy (x := y)).symm⟩
  · -- `k = j + 1 ≥ 1`: move the base point by the reflection in `(ℝ ∙ (x - y))ᗮ`
    obtain ⟨Φ, hΦ⟩ := sphereIsometryHomeomorph n
      (((ℝ ∙ ((x : EuclideanSpace ℝ (Fin (n + 1)))
        - (y : EuclideanSpace ℝ (Fin (n + 1)))))ᗮ).reflection)
    refine homotopyGroupEquivOfHomeomorph (j + 1) (by omega) Φ ?_
    exact Subtype.ext (by rw [hΦ]; exact reflectionSphere n x y)

end

end Work.PiS
