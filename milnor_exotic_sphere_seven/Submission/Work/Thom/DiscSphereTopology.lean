import Mathlib
import Submission.Work.Thom.Basic

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-!
# The topology of the disc and sphere bundles of a Euclidean real bundle

For a Euclidean real bundle `Z` (`Work.Thom.IsEuclidean`, i.e. the transition functions preserve the
fibre norm), the **fibrewise norm** `Work.Thom.fibreNorm Z : Z.TotalSpace → ℝ` is continuous
(`Work.Thom.continuous_fibreNorm`).  This is the statement that makes the unit disc and the unit
sphere well behaved:

* `Work.Thom.discSet_isOpen` — the open unit disc bundle is open;
* `Work.Thom.closedDiscSet_isClosed` — the closed unit disc bundle is closed;
* `Work.Thom.sphereSet_isClosed` — the sphere bundle is closed (in the total space, hence in the
  closed disc bundle), so the pair `(D(E),S(E))` is a genuine pair of a closed subspace with its
  boundary and the Thom space `D(E)/S(E)` is the quotient of a good pair.

The proof of `continuous_fibreNorm` is *local in the trivialisations*: near a point `p` one uses the
chart `Z.localTriv (Z.indexAt p.1)`, in which `fibreNorm` is `‖(Z.localTriv i ·).2‖` by
`Work.Thom.fibreNorm_localTriv` (this is where `IsEuclidean` is used), and that composite is
continuous because a trivialisation is continuous on its (open) source.  Without `IsEuclidean` the
statement is false: a transition function that is not an isometry makes the fibrewise norm jump.
-/

namespace Work.Thom

open Bundle Filter

open scoped Topology

open Work.TangentClasses

noncomputable section

variable {B : Type*} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type*}

/-- **The fibrewise norm of a Euclidean bundle is continuous.** -/
theorem continuous_fibreNorm {Z : RealBundle B F ι} (hZ : IsEuclidean Z) :
    Continuous (fibreNorm Z) := by
  rw [continuous_iff_continuousAt]
  intro p
  have hsource : p ∈ (Z.localTriv (Z.indexAt p.1)).source := by
    rw [VectorBundleCore.mem_localTriv_source]
    exact Z.mem_baseSet_at p.1
  have hcont : ContinuousAt
      (fun q : Z.TotalSpace => ‖((Z.localTriv (Z.indexAt p.1)) q).2‖) p :=
    ((Z.localTriv (Z.indexAt p.1)).continuousOn.continuousAt
      ((Z.localTriv (Z.indexAt p.1)).open_source.mem_nhds hsource)).snd.norm
  refine hcont.congr ?_
  filter_upwards [((Z.isOpen_baseSet (Z.indexAt p.1)).preimage Z.continuous_proj).mem_nhds
    (Z.mem_baseSet_at p.1)] with q hq
  exact (fibreNorm_localTriv hZ (Z.indexAt p.1) q hq).symm

/-- **The open unit disc bundle of a Euclidean bundle is open.** -/
theorem discSet_isOpen {Z : RealBundle B F ι} (hZ : IsEuclidean Z) : IsOpen (discSet Z) :=
  isOpen_lt (continuous_fibreNorm hZ) continuous_const

/-- **The closed unit disc bundle of a Euclidean bundle is closed.** -/
theorem closedDiscSet_isClosed {Z : RealBundle B F ι} (hZ : IsEuclidean Z) :
    IsClosed (closedDiscSet Z) :=
  isClosed_le (continuous_fibreNorm hZ) continuous_const

/-- **The sphere bundle of a Euclidean bundle is closed.** -/
theorem sphereSet_isClosed {Z : RealBundle B F ι} (hZ : IsEuclidean Z) :
    IsClosed (sphereSet Z) :=
  isClosed_eq (continuous_fibreNorm hZ) continuous_const

/-- The sphere bundle is closed in the closed disc bundle (they form a genuine pair). -/
theorem sphereInDisc_isClosed {Z : RealBundle B F ι} (hZ : IsEuclidean Z) :
    IsClosed (sphereInDisc Z) :=
  (sphereSet_isClosed hZ).preimage continuous_subtype_val

end

end Work.Thom
