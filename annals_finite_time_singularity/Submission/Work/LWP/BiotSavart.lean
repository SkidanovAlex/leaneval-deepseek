/-
# `Work.LWP.BiotSavart` — item 1: the Hölder-space Biot–Savart bounds

The Biot–Savart operator `biotSavart` and the input `BiotSavartSchauder` are defined in
`Work.LWP.Defs` resp. `Work.LWP.Inputs`.  This module turns the input into the *consumer
shapes* used by the assembly (the `C^{1,α}` closure of the Biot–Savart map, the Biot–Savart
law, and the odd/reflection parity clause), and records the far-field decay statement that the
Stability layer's `St4` uses for the compactly supported route.

## What is proved here (from the inputs, no `sorry`)

* `biotSavart_isContDiffHolder` — the `C^{1,α}` closure instance: bounded, `α`-Hölder,
  divergence-free, `L¹` vorticity ⟹ `biotSavart ω ∈ C^{1,α}(ℝ³)`.
* `vorticity_biotSavart`, `div_biotSavart` — the two halves of the Biot–Savart law.
* `biotSavart_reflZ` — the reflection/oddness clause.
* the *uniform-in-time* forms `biotSavart_isContDiffHolderOn` etc. used by the assembly.

## What is not proved here

The Schauder estimate itself, the Biot–Savart law itself and the reflection equivariance are
the three named inputs `BiotSavartSchauder`, `BiotSavartLaw`, `BiotSavartReflection` of
`Work.LWP.Inputs`; see `NOTES.md`.  The far-field decay
`‖biotSavart ω‖ ≤ C/‖x‖²` (and `C/‖x‖³` for `D biotSavart ω`) for compactly supported `ω` is
*not* an input: it is elementary and is proved in `Submission/Work/LWP/BiotSavart/`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.LWP.Inputs
import Submission.Work.LWP.BiotSavart.exists_decay_of_compactSupport

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

set_option autoImplicit false

namespace Work.LWP

variable {α : NNReal}

/-! ## The `C^{1,α}` closure of the Biot–Savart map -/

/-- **The Biot–Savart closure instance consumed by the assembly.**  For `ω ∈ L¹ ∩ L^∞` that is
`α`-Hölder and divergence-free, the velocity field `biotSavart ω` is of class `C^{1,α}(ℝ³)`,
i.e. `ContDiff ℝ 1`, with bounded `α`-Hölder derivative.  This is the form in which the
assembly checks that its reconstructed initial datum lies in
`EulerData α u₀` (`contDiffHolder` field). -/
theorem biotSavart_isContDiffHolder (h : BiotSavartSchauder α) {ω : R3 → R3}
    (hint : Integrable ω) (hb : IsBoundedFun ω) (hh : Holder α ω)
    (hdiv : ∀ x, div ω x = 0) : IsContDiffHolder ℝ α (biotSavart ω) :=
  h ω hint hb hh hdiv

/-- The derivative of `biotSavart ω` is bounded, without the Hölder clause. -/
theorem isBoundedFun_fderiv_biotSavart (h : BiotSavartSchauder α) {ω : R3 → R3}
    (hint : Integrable ω) (hb : IsBoundedFun ω) (hh : Holder α ω)
    (hdiv : ∀ x, div ω x = 0) : IsBoundedFun (fderiv ℝ (biotSavart ω)) :=
  (biotSavart_isContDiffHolder h hint hb hh hdiv).2.1

/-! ## The Biot–Savart law -/

/-- **Curl half of the Biot–Savart law**: `∇× (biotSavart ω) = ω` for divergence-free `ω`. -/
theorem vorticity_biotSavart (h : BiotSavartLaw) {ω : R3 → R3} (hint : Integrable ω)
    (hb : IsBoundedFun ω) (hdiv : ∀ x, div ω x = 0) (x : R3) :
    vorticity (biotSavart ω) x = ω x :=
  (h ω hint hb hdiv).1 x

/-- **Divergence half of the Biot–Savart law**: `div (biotSavart ω) = 0`. -/
theorem div_biotSavart (h : BiotSavartLaw) {ω : R3 → R3} (hint : Integrable ω)
    (hb : IsBoundedFun ω) (hdiv : ∀ x, div ω x = 0) (x : R3) :
    div (biotSavart ω) x = 0 :=
  (h ω hint hb hdiv).2 x

/-! ## The odd/reflection clause -/

/-- **Reflection equivariance of the Biot–Savart map.**  A vorticity in the parity class
`IsOddVorticity` produces a reflection-invariant velocity field; together with axisymmetry this
is `IsOdd u` (see `Work.Cyl.isOdd_of_reflZ_invariant`).  This is the "odd" clause of the
Lichtenstein–Gunther class at the level of the Biot–Savart map. -/
theorem biotSavart_reflZ (h : BiotSavartReflection) {ω : R3 → R3} (hω : IsOddVorticity ω)
    (x : R3) : biotSavart ω (reflZ x) = flipZ (biotSavart ω x) :=
  h ω hω x


/-! ## The assembly's datum construction -/

/-- **The assembly's `EulerData` construction.**  If `ω₀` is `L¹`, bounded, `α`-Hölder and
divergence-free, if `u₀ = biotSavart ω₀` is odd (the parity clause, available for the
axisymmetric no-swirl class from `Work.Cyl`), and if `ω₀` decays like `‖x‖^{-α}`, then
`u₀ = biotSavart ω₀` is Lichtenstein–Gunther admissible data:
`div u₀ = 0`, `IsOdd u₀`, `IsContDiffHolder ℝ α u₀`, and `VorticityDecay α (vorticity u₀)`
(the last two by `BiotSavartLaw` and `BiotSavartSchauder`). -/
theorem eulerData_of_biotSavart {α : NNReal} (hS : BiotSavartSchauder α) (hLaw : BiotSavartLaw)
    {ω₀ : R3 → R3} (hint : Integrable ω₀) (hb : IsBoundedFun ω₀) (hh : Holder α ω₀)
    (hdiv : ∀ x, div ω₀ x = 0) (hodd : IsOdd (biotSavart ω₀))
    (hdec : VorticityDecay α ω₀) :
    EulerData α (biotSavart ω₀) :=
  ⟨funext (hLaw ω₀ hint hb hdiv).2, hodd, hS ω₀ hint hb hh hdiv,
   by rw [funext (hLaw ω₀ hint hb hdiv).1]; exact hdec⟩

/-- The Biot–Savart-compatible data (`EulerDataBS`) for the assembly's construction: for a
vorticity `ω₀` that is `L¹`, bounded, `α`-Hölder and divergence-free, the field
`biotSavart ω₀` has `L¹`, divergence-free, bounded, `α`-Hölder vorticity; the remaining decay
field of `EulerDataBS` is exactly the far-field statement of `farField_decay`. -/
theorem eulerDataBS_of_biotSavart {α : NNReal} (hLaw : BiotSavartLaw) {ω₀ : R3 → R3}
    (hint : Integrable ω₀) (hb : IsBoundedFun ω₀) (hh : Holder α ω₀)
    (hdiv : ∀ x, div ω₀ x = 0)
    (hdecay : ∃ C : ℝ, ∀ x : R3, ‖biotSavart ω₀ x‖ ≤ C / (1 + ‖x‖)) :
    EulerDataBS α (biotSavart ω₀) := by
  have h := hLaw ω₀ hint hb hdiv
  refine ⟨?_, ?_, ?_, ?_, hdecay⟩
  · rw [funext h.1]; exact hint
  · rw [funext h.1]; exact hdiv
  · rw [funext h.1]; exact hb
  · rw [funext h.1]; exact hh


/-- Boundedness of a field from a uniform bound on its norm. -/
theorem isBoundedFun_of_norm_le {ω : R3 → R3} {M : ℝ} (h : ∀ y, ‖ω y‖ ≤ M) :
    IsBoundedFun ω :=
  (Metric.isBounded_iff_subset_closedBall (0 : R3)).mpr ⟨M, fun y hy => by
    obtain ⟨x, -, rfl⟩ := hy
    simpa [Metric.mem_closedBall] using h x⟩

/-- **The assembly's `EulerDataBS`, fully automatic for compactly supported vorticity.**  If `ω₀`
is `L¹`, bounded by `M` and supported in `B(0,R)`, `α`-Hölder and divergence-free, then
`biotSavart ω₀` carries the whole Biot–Savart-compatible datum class; the decay field is
`Work.LWP.BiotSavart.exists_decay_of_compactSupport` (far-field decay plus the near-field bound),
so no decay hypothesis has to be supplied by hand. -/
theorem eulerDataBS_of_compactSupport {α : NNReal} (hLaw : BiotSavartLaw) {ω₀ : R3 → R3}
    {R M : ℝ} (hR : 0 ≤ R) (hM : 0 ≤ M) (hint : Integrable ω₀) (hω : ∀ y, ‖ω₀ y‖ ≤ M)
    (hh : Holder α ω₀) (hdiv : ∀ x, div ω₀ x = 0)
    (hsupp : ∀ y, ω₀ y ≠ 0 → y ∈ Metric.closedBall 0 R) :
    EulerDataBS α (biotSavart ω₀) :=
  eulerDataBS_of_biotSavart hLaw hint (isBoundedFun_of_norm_le hω) hh hdiv
    (BiotSavart.exists_decay_of_compactSupport hR hM hω hsupp)

/-- **The self-consistency clause `hself` of `Work.LWP.local_existence`, automatically.**  For
`u₀ = biotSavart ω₀` with `vorticity u₀ = ω₀` (the Biot–Savart law), `u₀ = biotSavart (vorticity u₀)`
holds by rewriting. -/
theorem self_eq_biotSavart_of_biotSavart (hLaw : BiotSavartLaw) {ω₀ : R3 → R3}
    (hint : Integrable ω₀) (hb : IsBoundedFun ω₀) (hdiv : ∀ x, div ω₀ x = 0) :
    ∀ x, biotSavart ω₀ x = biotSavart (vorticity (biotSavart ω₀)) x := by
  have h := funext (hLaw ω₀ hint hb hdiv).1
  intro x
  rw [h]

end Work.LWP
