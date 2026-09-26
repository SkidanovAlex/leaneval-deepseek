import Mathlib
import Submission.Commons.Topology.Connected.locallyConnectedSpace_of_finite_fibers
import Submission.Commons.Topology.Plane.peano_essential_loop_of_bounded_complement

open Set Metric
open scoped Topology

namespace Commons.Topology.Circle

/-- On the unit circle, the points with a prescribed real part are at most two: if `‖w‖ = 1` and
`w.re = c` then `w = c ± √(1 - c²) · I`. -/
lemma finite_complex_of_re_eq_norm_eq_one (c : ℝ) :
    ({w : ℂ | w.re = c ∧ ‖w‖ = 1} : Set ℂ).Finite := by
  set d : ℝ := Real.sqrt (1 - c ^ 2) with hd
  have hsub : {w : ℂ | w.re = c ∧ ‖w‖ = 1} ⊆
      ({(c : ℂ) + (d : ℂ) * Complex.I, (c : ℂ) - (d : ℂ) * Complex.I} : Set ℂ) := by
    rintro w ⟨hr, hn⟩
    have h1 : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    have hsq : w.im ^ 2 = 1 - c ^ 2 := by
      rw [hn, hr] at h1; nlinarith [h1]
    have hnn : 0 ≤ 1 - c ^ 2 := hsq ▸ sq_nonneg w.im
    have hd2 : d ^ 2 = 1 - c ^ 2 := by rw [hd]; exact Real.sq_sqrt hnn
    have hcases : w.im = d ∨ w.im = -d := sq_eq_sq_iff_eq_or_eq_neg.mp (by rw [hsq, hd2])
    rw [← Complex.re_add_im w, hr]
    rcases hcases with h | h
    · rw [h]; simp
    · rw [h]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      right
      push_cast
      ring
  exact (Set.Finite.insert _ (Set.finite_singleton _)).subset hsub

/-- The set of points of the circle with a prescribed real part is finite (at most two). -/
lemma finite_circle_of_re_eq (c : ℝ) :
    ({z : Circle | ((z : ℂ)).re = c} : Set Circle).Finite := by
  have himg : ((fun z : Circle => (z : ℂ)) '' {z : Circle | (z : ℂ).re = c}).Finite := by
    apply (finite_complex_of_re_eq_norm_eq_one c).subset
    rintro w ⟨z, hz, rfl⟩
    refine ⟨hz, ?_⟩
    have h : (z : ℂ) ∈ Metric.sphere (0 : ℂ) 1 := z.2
    rwa [Metric.mem_sphere, dist_zero_right] at h
  exact Set.Finite.of_finite_image himg (fun a _ b _ h => Subtype.ext h)

/-- **A compact connected set in the cylinder with finite meridians is locally path connected.**

The real part `(·.1 : ℂ).re` is a continuous real-valued function whose level sets on the circle
have at most two points; hence, by `locallyConnectedSpace_of_finite_fibers`, `↥K` is locally
connected, and a compact metric space that is locally connected is locally path connected
(`locallyPathConnectedSpace_of_complete_locallyConnected`). -/
theorem locallyPathConnectedSpace_of_finite_meridians {K : Set (Circle × ℝ)} (hK : IsCompact K)
    (hKc : IsConnected K) (hfin : ∀ z : Circle, (K ∩ {q : Circle × ℝ | q.1 = z}).Finite) :
    LocallyPathConnectedSpace ↥K := by
  haveI : CompactSpace ↥K := isCompact_iff_compactSpace.mp hK
  haveI : ConnectedSpace ↥K := isConnected_iff_connectedSpace.mp hKc
  -- each meridian, viewed inside `↥K`, is finite
  have hmer : ∀ z : Circle, ({q : ↥K | (q : Circle × ℝ).1 = z}).Finite := by
    intro z
    have hsub : {q : ↥K | (q : Circle × ℝ).1 = z}
        = Subtype.val ⁻¹' (K ∩ {q : Circle × ℝ | q.1 = z}) := by
      ext q
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_inter_iff]
      exact ⟨fun h => ⟨q.2, h⟩, fun h => h.2⟩
    rw [hsub]
    exact (hfin z).preimage (fun a _ b _ hab => Subtype.val_injective hab)
  -- the level sets of the real part are finite
  have hfib : ∀ c : ℝ,
      ({q : ↥K | (((q : Circle × ℝ).1 : Circle) : ℂ).re = c}).Finite := by
    intro c
    have hS : ({z : Circle | ((z : ℂ)).re = c} : Set Circle).Finite := finite_circle_of_re_eq c
    rw [show {q : ↥K | (((q : Circle × ℝ).1 : Circle) : ℂ).re = c}
          = ⋃ z ∈ {z : Circle | ((z : ℂ)).re = c}, {q : ↥K | (q : Circle × ℝ).1 = z} from by
        ext q; simp only [Set.mem_setOf_eq, Set.mem_iUnion]
        constructor
        · intro hq; exact ⟨(q : Circle × ℝ).1, hq, rfl⟩
        · rintro ⟨z, hz, hzq⟩; rw [hzq]; exact hz]
    exact hS.biUnion (fun z _ => hmer z)
  have hlc : LocallyConnectedSpace ↥K :=
    Commons.Topology.Connected.locallyConnectedSpace_of_finite_fibers (X := ↥K)
      (fun q => ((q : Circle × ℝ).1 : ℂ).re) (by fun_prop) hfib
      (fun p t r => (hfib t).subset (fun x hx => hx.1))
  haveI : CompleteSpace ↥K := (completeSpace_coe_iff_isComplete (s := K)).mpr hK.isComplete
  exact Commons.Topology.Plane.LocalPeano.locallyPathConnectedSpace_of_complete_locallyConnected ↥K

end Commons.Topology.Circle
