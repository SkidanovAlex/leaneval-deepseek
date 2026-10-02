import Mathlib
import Submission.Work.Gen.puncturedSlabs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped Topology

namespace Work.Gen

/-- **The weighted fibrewise norm `slabNu Z φ p = ∑ i, φ i p.1 * ‖(Z.localTriv i p).2‖` is
continuous**, provided each weight's support closure lies in the corresponding chart set.

The support condition is what kills the junk: `(Z.localTriv i p).2` is `Z.coordChange (Z.indexAt p.1) i p.1`
applied to the fibre component of `p`, and it is a continuous function of `p` only at points with
`p.1 ∈ Z.baseSet i`.  If `p.1 ∉ Z.baseSet i` then (by `hφ`, with `tsupport` closed) the weight `φ i`
vanishes on a neighbourhood of `p.1`, so the `i`-th summand is identically zero near `p`.  Each
summand is therefore continuous everywhere (glue along the open cover `π ⁻¹' Z.baseSet i` and
`π ⁻¹' (tsupport (φ i))ᶜ`), and a finite sum of continuous functions is continuous. -/
theorem continuous_slabNu {B : Type*} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {ι : Type*} [Fintype ι] (Z : Work.TangentClasses.RealBundle B F ι)
    (φ : ι → ContinuousMap B ℝ) (hφ : ∀ i, tsupport (φ i) ⊆ Z.baseSet i) :
    Continuous (Work.Gen.slabNu Z φ) := by
  -- Each summand `p ↦ φ i p.1 * ‖(Z.localTriv i p).2‖` is continuous.
  have hterm : ∀ i, Continuous (fun p : Z.TotalSpace => φ i p.1 * ‖(Z.localTriv i p).2‖) := by
    intro i
    -- The fibre coordinate in the chart `i` is continuous on the open set `π ⁻¹' baseSet i`.
    have hchart : ContinuousOn (fun q : Z.TotalSpace => (Z.localTriv i q).2)
        (Z.proj ⁻¹' Z.baseSet i) := by
      have h := (Z.localTriv i).continuousOn_toFun
      rw [show (Z.localTriv i).source = Z.proj ⁻¹' Z.baseSet i from by
        rw [Bundle.Trivialization.source_eq]; rfl] at h
      exact continuous_snd.comp_continuousOn h
    have hconton : ContinuousOn (fun q : Z.TotalSpace => φ i q.1 * ‖(Z.localTriv i q).2‖)
        (Z.proj ⁻¹' Z.baseSet i) :=
      (((φ i).continuous.comp Z.continuous_proj).continuousOn).mul hchart.norm
    rw [continuous_iff_continuousAt]
    intro p
    by_cases hp : p.1 ∈ Z.baseSet i
    · -- Inside the chart set the summand is continuous by the chart computation.
      have hUopen : IsOpen (Z.proj ⁻¹' Z.baseSet i) :=
        (Z.isOpen_baseSet i).preimage Z.continuous_proj
      exact hconton.continuousAt (hUopen.mem_nhds hp)
    · -- Otherwise `φ i` vanishes near `p.1`, so the summand is locally zero.
      have hpt : p.1 ∉ tsupport (φ i) := fun h => hp (hφ i h)
      have hVopen : IsOpen (Z.proj ⁻¹' (tsupport (φ i))ᶜ) :=
        ((isClosed_tsupport (φ i)).isOpen_compl).preimage Z.continuous_proj
      have hzero : ∀ q : Z.TotalSpace, q ∈ Z.proj ⁻¹' (tsupport (φ i))ᶜ →
          φ i q.1 * ‖(Z.localTriv i q).2‖ = 0 := by
        intro q hq
        rw [image_eq_zero_of_notMem_tsupport hq, zero_mul]
      have hEV : (fun q : Z.TotalSpace => φ i q.1 * ‖(Z.localTriv i q).2‖) =ᶠ[𝓝 p]
          (fun _ => (0:ℝ)) := by
        filter_upwards [hVopen.mem_nhds hpt] with q hq
        exact hzero q hq
      rw [ContinuousAt, hzero p hpt]
      exact hEV.tendsto
  -- `slabNu` is the finite sum of the summands.
  change Continuous (fun (p : Z.TotalSpace) => ∑ i, φ i p.1 * ‖(Z.localTriv i p).2‖)
  exact continuous_finsetSum (s := Finset.univ)
    (f := fun i (p : Z.TotalSpace) => φ i p.1 * ‖(Z.localTriv i p).2‖) (fun i _ => hterm i)

end Work.Gen
