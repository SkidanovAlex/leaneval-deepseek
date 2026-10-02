import Submission.Work.Tubular.Gauss
import Submission.Work.Tubular.tubeChart_mono

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# Interpolating the tube radius of a Pontryagin–Thom collapse

The collapse class `Work.Tubular.collapseRelK8` of a tubular neighbourhood is built from the
metric-free collapse map `g`, which on the open tube is pinned by the blow-up formula
`y ↦ some (normalBlowUp E ε (C.inv y))` and is `∞` off the open tube.  Two tube charts of the same
embedding, of radii `ε` and `ε'`, therefore give *different* maps, related by a positive fibrewise
radial rescaling of the normal directions.

This file sets up the interpolation used to compare them:

* `Work.ThomBordism.tubeRadiusInterp ε ε' s = (1-s) * ε + s * ε'`, the intermediate radius;
* `Work.ThomBordism.collapseRadial C r`, the collapse map of the chart `C` with the tube radius
  replaced by the *variable* radius `r`.

The mathematical content — that `s ↦ collapseRadial C (tubeRadiusInterp ε ε' s)` is a *continuous*
map of `I × ℝ^{8+k}` into `ν⁺` — is the statement `Work.ThomBordism.continuous_collapseRadial_interp`
(kept in the separate module `Submission.Work.ThomBordism.collapseInterpCont`).
-/

attribute [local instance] Classical.propDecidable

open scoped Manifold ContDiff Topology unitInterval
open Function Topology Filter

open Work.ThomBordism.PontryaginThom (EmbeddingData)

namespace Work.ThomBordism

noncomputable section

variable {V : Work.ThomBordism.Man8} {k : ℕ}

/-- The linear interpolation `s ↦ (1-s) * ε + s * ε'` of two tube radii. -/
def tubeRadiusInterp (ε ε' : ℝ) (s : unitInterval) : ℝ :=
  (1 - (s : ℝ)) * ε + (s : ℝ) * ε'

@[simp] theorem tubeRadiusInterp_zero (ε ε' : ℝ) : tubeRadiusInterp ε ε' 0 = ε := by
  simp [tubeRadiusInterp]

@[simp] theorem tubeRadiusInterp_one (ε ε' : ℝ) : tubeRadiusInterp ε ε' 1 = ε' := by
  simp [tubeRadiusInterp]

theorem continuous_tubeRadiusInterp (ε ε' : ℝ) : Continuous (tubeRadiusInterp ε ε') := by
  unfold tubeRadiusInterp
  fun_prop

/-- The interpolated radius lies between the two radii. -/
theorem tubeRadiusInterp_mem {ε ε' : ℝ} (hle : ε' ≤ ε) (s : unitInterval) :
    ε' ≤ tubeRadiusInterp ε ε' s ∧ tubeRadiusInterp ε ε' s ≤ ε := by
  have h0 : (0 : ℝ) ≤ (s : ℝ) := s.2.1
  have h1 : (s : ℝ) ≤ 1 := s.2.2
  have h2 : tubeRadiusInterp ε ε' s = ε - (s : ℝ) * (ε - ε') := by
    unfold tubeRadiusInterp; ring
  have h3 : tubeRadiusInterp ε ε' s = ε' + (1 - (s : ℝ)) * (ε - ε') := by
    unfold tubeRadiusInterp; ring
  constructor
  · rw [h3]; nlinarith
  · rw [h2]; nlinarith

/-- The interpolated radius is positive when both radii are. -/
theorem tubeRadiusInterp_pos {ε ε' : ℝ} (hle : ε' ≤ ε) (hε' : 0 < ε') (s : unitInterval) :
    0 < tubeRadiusInterp ε ε' s :=
  lt_of_lt_of_le hε' (tubeRadiusInterp_mem hle s).1

/-- **The collapse map of a tube chart with a variable tube radius.**  A point of the closed tube
`C.U` whose normal foot has norm `< r` is sent to the blow-up of radius `r` of its normal foot;
every other point is sent to `∞`.  At `r = ε` this is the pinned collapse map `g` of the chart. -/
def collapseRadial {E : EmbeddingData V (8 + k)} {ε : ℝ} (C : Work.Tubular.TubeChart E ε)
    (r : ℝ) (y : Work.Tubular.Euc (8 + k)) : OnePoint (Work.Tubular.NormalTotal E) :=
  if y ∈ C.U ∧ Work.Tubular.normalNorm E (C.inv y) < r then
    OnePoint.some (Work.Tubular.normalBlowUp E r (C.inv y)) else OnePoint.infty

variable {E : EmbeddingData V (8 + k)} {ε : ℝ}

theorem collapseRadial_of_mem (C : Work.Tubular.TubeChart E ε) {r : ℝ}
    {y : Work.Tubular.Euc (8 + k)} (hU : y ∈ C.U)
    (hr : Work.Tubular.normalNorm E (C.inv y) < r) :
    collapseRadial C r y = OnePoint.some (Work.Tubular.normalBlowUp E r (C.inv y)) := by
  rw [collapseRadial, if_pos ⟨hU, hr⟩]

theorem collapseRadial_of_not (C : Work.Tubular.TubeChart E ε) {r : ℝ}
    {y : Work.Tubular.Euc (8 + k)}
    (h : ¬ (y ∈ C.U ∧ Work.Tubular.normalNorm E (C.inv y) < r)) :
    collapseRadial C r y = OnePoint.infty := by
  rw [collapseRadial, if_neg h]

theorem collapseRadial_of_not_mem (C : Work.Tubular.TubeChart E ε) {r : ℝ}
    {y : Work.Tubular.Euc (8 + k)} (hy : y ∉ C.U) : collapseRadial C r y = OnePoint.infty :=
  collapseRadial_of_not C fun h => hy h.1

/-- At the chart's own radius, on the open tube, the variable-radius collapse is the pinned
collapse of the tube data. -/
theorem collapseRadial_self_of_mem (C : Work.Tubular.TubeChart E ε)
    {y : Work.Tubular.Euc (8 + k)} (hy : y ∈ C.openTube) :
    collapseRadial C ε y = OnePoint.some (Work.Tubular.normalBlowUp E ε (C.inv y)) :=
  collapseRadial_of_mem C (C.openTube_subset_U hy) (C.normalNorm_inv_lt hy)

/-- At the chart's own radius, off the open tube, the variable-radius collapse is `∞`. -/
theorem collapseRadial_self_of_notMem (C : Work.Tubular.TubeChart E ε)
    {y : Work.Tubular.Euc (8 + k)} (hy : y ∉ C.openTube) :
    collapseRadial C ε y = OnePoint.infty := by
  refine collapseRadial_of_not C (fun ⟨hU, hr⟩ => hy ?_)
  exact ⟨C.inv y, hr, C.tubeMap_inv y hU⟩

/-- **The variable-radius collapse at a smaller radius.**  For `ε' ≤ ε` and a point of the open tube
of radius `ε'`, the collapse of the *large* chart at the small radius is the blow-up of the normal
foot of the large chart. -/
theorem collapseRadial_of_le_mem (C : Work.Tubular.TubeChart E ε) {ε' : ℝ} (hle : ε' ≤ ε)
    {y : Work.Tubular.Euc (8 + k)} (hy : y ∈ Work.Tubular.openTubeSet E ε') :
    collapseRadial C ε' y = OnePoint.some (Work.Tubular.normalBlowUp E ε' (C.inv y)) := by
  obtain ⟨p, hp, hpy⟩ := hy
  refine collapseRadial_of_mem C ?_ ?_
  · rw [← hpy]
    exact C.mem_U p (le_trans (le_of_lt hp) hle)
  · rw [C.eq_inv_of_tubeMap_eq (lt_of_lt_of_le hp hle) hpy]
    exact hp

/-- **The variable-radius collapse at a smaller radius, off the small open tube.** -/
theorem collapseRadial_of_le_notMem (C : Work.Tubular.TubeChart E ε) {ε' : ℝ}
    {y : Work.Tubular.Euc (8 + k)} (hy : y ∉ Work.Tubular.openTubeSet E ε') :
    collapseRadial C ε' y = OnePoint.infty := by
  refine collapseRadial_of_not C (fun ⟨hU, hr⟩ => hy ?_)
  exact ⟨C.inv y, hr, C.tubeMap_inv y hU⟩

/-- **The variable-radius collapse at a smaller radius, in the chart of that radius.**  The normal
foot of the large chart agrees with that of the small chart on the small open tube. -/
theorem collapseRadial_of_le_chart_mem (C : Work.Tubular.TubeChart E ε)
    {ε' : ℝ} (C' : Work.Tubular.TubeChart E ε') (hle : ε' ≤ ε)
    {y : Work.Tubular.Euc (8 + k)} (hy : y ∈ C'.openTube) :
    collapseRadial C ε' y = OnePoint.some (Work.Tubular.normalBlowUp E ε' (C'.inv y)) := by
  have hset : C'.openTube = Work.Tubular.openTubeSet E ε' := rfl
  rw [collapseRadial_of_le_mem C hle (hset ▸ hy)]
  congr 1
  obtain ⟨p, hp, hpy⟩ := hy
  rw [C.eq_inv_of_tubeMap_eq (lt_of_lt_of_le hp hle) hpy, C'.eq_inv_of_tubeMap_eq hp hpy]

/-- **The variable-radius collapse at a smaller radius, off the small chart's tube.** -/
theorem collapseRadial_of_le_chart_notMem (C : Work.Tubular.TubeChart E ε)
    {ε' : ℝ} (C' : Work.Tubular.TubeChart E ε') (hle : ε' ≤ ε)
    {y : Work.Tubular.Euc (8 + k)} (hy : y ∉ C'.openTube) :
    collapseRadial C ε' y = OnePoint.infty := by
  have hset : C'.openTube = Work.Tubular.openTubeSet E ε' := rfl
  exact collapseRadial_of_le_notMem C (hset ▸ hy)

/-- **The pinned collapse map of the tube data, evaluated.**  The two defining hypotheses pin `g`
completely on the complement of `∞` in `OnePoint (Euc (8+k))`. -/
theorem tubeData_apply (C : Work.Tubular.TubeChart E ε)
    {g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E))}
    (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
    (hg2 : ∀ y, y ∈ C.openTube →
      g (OnePoint.some y) = OnePoint.some (Work.Tubular.normalBlowUp E ε (C.inv y)))
    (y : Work.Tubular.Euc (8 + k)) :
    g (OnePoint.some y) = collapseRadial C ε y := by
  by_cases h : y ∈ C.openTube
  · rw [collapseRadial_self_of_mem C h, hg2 y h]
  · rw [collapseRadial_self_of_notMem C h, hg y h]

end

end Work.ThomBordism
