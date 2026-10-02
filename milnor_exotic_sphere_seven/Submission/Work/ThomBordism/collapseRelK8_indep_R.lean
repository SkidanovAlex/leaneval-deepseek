import Mathlib
import Submission.Work.Tubular.ThomRepOfLocalDegree
import Submission.Work.Stems.hurewiczChain_eq_of_homotopic
import Submission.Work.Tubular.Gauss

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 800000

namespace Work.ThomBordism

section RadiusHomotopy

open scoped Topology unitInterval
open Work.Tubular

/-- **The cube collapse is insensitive to the radius, up to a homotopy rel the boundary of the
cube.**  For two radii `R, R' ≥ 0` each satisfying the box condition for the same tube, the
`GenLoop`s `tubeGenLoopOnePoint C g hg hR hbox` and `tubeGenLoopOnePoint C g hg hR' hbox'` are
homotopic relative to `∂I^{8+k}`, by the straight-line interpolation
`(s, t) ↦ g (OnePoint.some (cubeToEuc (8+k) (R + s (R' - R)) t))` of the radius: on the boundary
of the cube `cubeToEuc` has a coordinate of absolute value the interpolated radius
(`Work.Tubular.cubeToEuc_boundary`), which is `≥ min R R'`, hence the point is outside the tube and
the collapse lands at the basepoint. -/
theorem tubeGenLoopOnePoint_homotopic_radius {V : Work.ThomBordism.Man8} {k : ℕ}
    {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)} {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε)
    (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
    (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
    {R R' : ℝ} (hR : 0 ≤ R) (hR' : 0 ≤ R')
    (hbox : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y j| < R)
    (hbox' : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y j| < R') :
    GenLoop.Homotopic (Work.Tubular.tubeGenLoopOnePoint C g hg hR hbox)
      (Work.Tubular.tubeGenLoopOnePoint C g hg hR' hbox') := by
  -- joint continuity of `(s, t) ↦ cubeToEuc (8+k) (R + s (R'-R)) t`
  have hcont : Continuous fun p : unitInterval × (Fin (8 + k) → unitInterval) =>
      cubeToEuc (8 + k) (R + (p.1:ℝ)*(R'-R)) p.2 := by
    have h : (fun p : unitInterval × (Fin (8 + k) → unitInterval) =>
        cubeToEuc (8 + k) (R + (p.1:ℝ)*(R'-R)) p.2)
        = fun p => funToEuc (8+k)
            (fun i => 2 * (R + (p.1:ℝ)*(R'-R)) * ((p.2 i : ℝ) - 1/2)) := by
      funext p
      rw [cubeToEuc_apply, show cubeToFun (8+k) (R + ↑p.1 * (R'-R)) p.2 =
        (fun i => 2 * (R + ↑p.1 * (R'-R)) * ((p.2 i : ℝ) - 1/2)) from rfl]
    rw [h]
    exact (funToEuc (8+k)).continuous.comp (continuous_pi fun i => by fun_prop)
  -- the interpolated cube maps the boundary of the cube outside the tube
  have hbound : ∀ (s : unitInterval) (t : Fin (8+k) → unitInterval),
      t ∈ Cube.boundary (Fin (8+k)) →
      g (OnePoint.some (cubeToEuc (8+k) (R + (s:ℝ)*(R'-R)) t)) = OnePoint.infty := by
    intro s t ht
    refine hg _ (fun hmem => ?_)
    have hmemU : cubeToEuc (8+k) (R + (s:ℝ)*(R'-R)) t ∈ C.U := C.openTube_subset_U hmem
    -- the interpolated radius is nonnegative
    have hnn : 0 ≤ R + (s:ℝ)*(R'-R) := by
      rcases le_total R R' with h | h
      · have : 0 ≤ (s:ℝ) * (R' - R) := mul_nonneg s.2.1 (sub_nonneg.mpr h)
        linarith
      · have h2 : 0 ≤ (1 - (s:ℝ)) * (R - R') :=
          mul_nonneg (sub_nonneg.mpr s.2.2) (sub_nonneg.mpr h)
        nlinarith
    obtain ⟨i, hi⟩ := cubeToEuc_boundary (8+k) hnn ht
    rcases le_total R R' with h | h
    · -- radius interpolated between `R` and `R'`: it is `≥ R`, but the box condition for `R` gives `< R`
      have h1 := hbox _ hmemU i
      have : 0 ≤ (s:ℝ) * (R' - R) := mul_nonneg s.2.1 (sub_nonneg.mpr h)
      rw [hi] at h1
      linarith
    · -- radius interpolated between `R'` and `R`: it is `≥ R'`
      have h1 := hbox' _ hmemU i
      have h2 : R' - R ≤ (s:ℝ) * (R' - R) := by
        have h3 : 0 ≤ (1 - (s:ℝ)) * (R - R') :=
          mul_nonneg (sub_nonneg.mpr s.2.2) (sub_nonneg.mpr h)
        nlinarith
      rw [hi] at h1
      linarith
  refine ⟨⟨⟨⟨fun p => g (OnePoint.some (cubeToEuc (8+k) (R + (p.1:ℝ)*(R'-R)) p.2)),
    g.continuous.comp (OnePoint.continuous_coe.comp hcont)⟩, ?_, ?_⟩, ?_⟩⟩
  · intro x
    show g (OnePoint.some (cubeToEuc (8+k) (R + (((0:unitInterval):ℝ))*(R'-R)) x))
      = tubeCollapseCubeOnePoint g R x
    rw [show (((0:unitInterval):ℝ)) = 0 from rfl, zero_mul, add_zero]
    rfl
  · intro x
    show g (OnePoint.some (cubeToEuc (8+k) (R + (((1:unitInterval):ℝ))*(R'-R)) x))
      = tubeCollapseCubeOnePoint g R' x
    rw [show (((1:unitInterval):ℝ)) = 1 from rfl, one_mul,
      show R + (R' - R) = R' from by ring]
    rfl
  · intro s x hx
    show g (OnePoint.some (cubeToEuc (8+k) (R + (s:ℝ)*(R'-R)) x))
      = tubeCollapseCubeOnePoint g R x
    rw [tubeCollapseCubeOnePoint_boundary C g hg hR hbox hx]
    exact hbound s x hx

end RadiusHomotopy

/-- The class `collapseRelK8 C g hg hR hbox` of the Pontryagin–Thom collapse does not depend on
the cube radius `R`: for any two radii `R, R' ≥ 0` satisfying the box condition for the same tube,
the classes agree.  Proof idea: the loops `tubeGenLoopOnePoint C g hg hR hbox` and
`... hR' hbox'` are related by the homotopy `(s, t) ↦ g (OnePoint.some (cubeToEuc (8+k) (R + s(R'-R)) t))`
of cube maps; on the boundary of the cube the point `cubeToEuc (8+k) (s-interpolated radius) t` has a
coordinate of absolute value `≥ min R R'` (via `cubeToEuc_boundary`; case split on which of `R, R'`
is smaller and use the corresponding box condition), hence is outside `C.U`, hence outside
`C.openTube`, so the homotopy lands on the basepoint throughout; `cubeLift_homotopic_of_homotopicRel`
and `hurewiczChain_eq_of_homotopic` then give equal `hurewiczChain`s, and `collapseRelK8` is defined
from that chain by the same transport `compIso E (k+8)`. -/
theorem collapseRelK8_indep_R {V : Work.ThomBordism.Man8} {k : ℕ}
    {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)} {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε)
    (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
    (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
    {R R' : ℝ} (hR : 0 ≤ R) (hR' : 0 ≤ R')
    (hbox : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y j| < R)
    (hbox' : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y j| < R') :
    Work.Tubular.collapseRelK8 C g hg hR hbox = Work.Tubular.collapseRelK8 C g hg hR' hbox' := by
  have hchain := Work.Stems.hurewiczChain_eq_of_homotopic (8 + k) (by omega)
    (tubeGenLoopOnePoint_homotopic_radius C g hg hR hR' hbox hbox')
  unfold Work.Tubular.collapseRelK8
  rw [hchain]

end Work.ThomBordism
