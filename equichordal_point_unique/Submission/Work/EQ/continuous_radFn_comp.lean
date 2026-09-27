import Mathlib
import Submission.Work.EQ.normDefs

namespace Work.EQ

open LeanEval.Geometry.Equichordal

theorem continuous_radFn_comp {K : Set (EuclideanSpace ℝ (Fin 2))}
    {O : EuclideanSpace ℝ (Fin 2)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hO : O ∈ interior K) {γ : Type*} [TopologicalSpace γ] {u : γ → EuclideanSpace ℝ (Fin 2)}
    (hu : Continuous u) (hu1 : ∀ x, u x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :
    Continuous fun x => radFn K O (u x) := by
  have hSconv : Convex ℝ (shiftSet K O) := by
    have h : shiftSet K O = (fun x => -O + x) '' K := by simp [shiftSet, Homeomorph.addLeft]
    rw [h]
    exact hconv.translate (-O)
  have hScomp : IsCompact (shiftSet K O) := hK.image (Homeomorph.addLeft (-O)).continuous
  have hSbound : Bornology.IsVonNBounded ℝ (shiftSet K O) := hScomp.isVonNBounded ℝ
  have h0int : (0 : EuclideanSpace ℝ (Fin 2)) ∈ interior (shiftSet K O) := by
    change (0 : EuclideanSpace ℝ (Fin 2)) ∈ interior ((Homeomorph.addLeft (-O)) '' K)
    rw [← Homeomorph.image_interior]
    exact ⟨O, hO, by simp⟩
  have hSnhds : shiftSet K O ∈ nhds (0 : EuclideanSpace ℝ (Fin 2)) :=
    mem_interior_iff_mem_nhds.mp h0int
  have habs : Absorbent ℝ (shiftSet K O) := absorbent_nhds_zero hSnhds
  have hcont : Continuous fun x => gauge (shiftSet K O) (u x) :=
    (continuous_gauge hSconv hSnhds).comp hu
  have hne : ∀ x, gauge (shiftSet K O) (u x) ≠ 0 := by
    intro x
    have hux : u x ≠ 0 := by
      intro h
      have := hu1 x
      rw [Metric.mem_sphere, h] at this
      simp at this
    exact ne_of_gt ((gauge_pos habs hSbound).mpr hux)
  convert hcont.inv₀ hne using 1
  ext x
  simp [radFn, Pi.inv_apply]

end Work.EQ
