import Submission.Work.FlatComponents
import Submission.Work.FlatHeightFacts
import Submission.PaperBand.KernelSegments

open OptimalMoebius Topology ContDiff
open scoped BigOperators Matrix Topology Metric
open Filter
set_option autoImplicit false
set_option maxHeartbeats 800000
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
# The U-sides of a flat component (GREEN)

Foundation for the frontier lemma (A) of `session_status40`: the "same
connected `U`-side" relation.  For a flat point `z₀` of a flat component
`C`, each `U`-point `x` keeps all of `C` strictly on ONE side of its
ruling (its ruling line avoids `C` entirely — `interior_on_line_is_U`),
and that side is the sign of the continuous functional

    uSideFunc f z₀ x = signedLineFunc x (unitKernelDir f x) z₀.

This file proves:
* `uSideFunc_ne_zero` — the functional never vanishes at `U`-points
  (`flat_point_not_on_uBend_dir`), so every `U`-point has a definite side;
* `continuousAt_uSideFunc` / `continuousOn_uSideFunc` — it is continuous on
  any set of `U`-points (copy of the `ruling_flat_side_locally_constant`
  continuity pattern);
* **`uSide_sign_constant`** — side constancy: on any PRECONNECTED set `S`
  of `U`-points the functional keeps a single sign (it is continuous,
  nowhere zero, so by the intermediate value it cannot take both signs) —
  i.e. the side of `C` is constant on every connected set of `U`-points.
  This is exactly "same connected U-side ⟹ same side", the topological
  half of lemma (A); the equality of limiting CHORD DIRECTIONS for two
  such sequences still needs the frontier normal form.
-/

noncomputable section
namespace Submission.PaperBand

/-- The set of `U`-points of the strip interior (where the shape operator
is nonzero). -/
def UPoints (f : ℝ² → ℝ³) : Set ℝ² := {x | x ∈ stripInterior ∧ dN f x ≠ 0}

/-- The signed side functional: for a `U`-point `x` and a fixed flat point
`z₀`, the sign of `signedLineFunc x (unitKernelDir f x) z₀` records on
which side of `x`'s ruling the point `z₀` (hence the whole flat component
of `z₀`) lies. -/
def uSideFunc (f : ℝ² → ℝ³) (z₀ : ℝ²) (x : ℝ²) : ℝ :=
  signedLineFunc x (unitKernelDir f x) z₀

/-- **The side functional never vanishes at a `U`-point**: the flat point
`z₀` never lies on the ruling line of a `U`-point. -/
lemma uSideFunc_ne_zero {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {z₀ : ℝ²} (hz₀F : z₀ ∈ FlatSet f) {x : ℝ²}
    (hxU : x ∈ UPoints f) : uSideFunc f z₀ x ≠ 0 := by
  have hxS : x ∈ stripInterior := hxU.1
  have hU : dN f x ≠ 0 := hxU.2
  have hd0 : (unitKernelDir f x) 0 ≠ 0 := by
    apply kernel_vector_coord0_ne_zero hf ha hxS hU (unitKernelDir_mem_ker hf hxS)
    exact unitKernelDir_ne_zero (V2f_ne_zero_at_U hf ha hxS hU)
  unfold uSideFunc
  exact flat_point_not_on_uBend_dir hf ha hz₀F hxS hU
    (unitKernelDir_mem_ker hf hxS)
    (unitKernelDir_ne_zero (V2f_ne_zero_at_U hf ha hxS hU)) hd0

/-- The side functional is continuous at every `U`-point. -/
lemma continuousAt_uSideFunc {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {x₀ : ℝ²} (hx₀U : x₀ ∈ UPoints f) (z₀ : ℝ²) :
    ContinuousAt (uSideFunc f z₀) x₀ := by
  have hq₀S : x₀ ∈ stripInterior := hx₀U.1
  have hU₀ : dN f x₀ ≠ 0 := hx₀U.2
  have hUc : ContinuousAt (fun q : ℝ² => unitKernelDir f q) x₀ :=
    continuousAt_uBendUnitDir hf ha hq₀S hU₀
  have hU0c : ContinuousAt (fun q : ℝ² => (unitKernelDir f q) 0) x₀ := by
    have hc0 : ContinuousAt (fun d : ℝ² => d 0) (unitKernelDir f x₀) := by fun_prop
    exact ContinuousAt.comp (x := x₀) (f := unitKernelDir f) (g := fun d : ℝ² => d 0)
      hc0 hUc
  have hU1c : ContinuousAt (fun q : ℝ² => (unitKernelDir f q) 1) x₀ := by
    have hc1 : ContinuousAt (fun d : ℝ² => d 1) (unitKernelDir f x₀) := by fun_prop
    exact ContinuousAt.comp (x := x₀) (f := unitKernelDir f) (g := fun d : ℝ² => d 1)
      hc1 hUc
  have hterm0 : ContinuousAt (fun q : ℝ² => (z₀ 0 - q 0) * (unitKernelDir f q) 1) x₀ := by
    have hz : ContinuousAt (fun q : ℝ² => z₀ 0 - q 0) x₀ := by fun_prop
    exact ContinuousAt.mul hz hU1c
  have hterm1 : ContinuousAt (fun q : ℝ² => (z₀ 1 - q 1) * (unitKernelDir f q) 0) x₀ := by
    have hz : ContinuousAt (fun q : ℝ² => z₀ 1 - q 1) x₀ := by fun_prop
    exact ContinuousAt.mul hz hU0c
  have hm := ContinuousAt.sub hterm0 hterm1
  unfold uSideFunc signedLineFunc
  exact hm

/-- The side functional is continuous on any set of `U`-points. -/
lemma continuousOn_uSideFunc {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {S : Set ℝ²} (hSsub : S ⊆ UPoints f) (z₀ : ℝ²) :
    ContinuousOn (uSideFunc f z₀) S := by
  intro x₀ hx₀
  exact (continuousAt_uSideFunc hf ha (hSsub hx₀) z₀).continuousWithinAt

/-- **Side constancy on connected sets of `U`-points**: if a PRECONNECTED
set `S` consists of `U`-points and the flat point `z₀` is fixed, then the
side of the ruling relative to `z₀` is constant on `S` — either all
rulings of `S` keep `z₀` strictly on their positive side or all keep it on
their negative side.  (The functional is continuous, nowhere zero on `S`,
and `S` is connected, so it cannot take both signs.) -/
theorem uSide_sign_constant {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {S : Set ℝ²} (hSconn : IsPreconnected S)
    (hSsub : S ⊆ UPoints f) {z₀ : ℝ²} (hz₀F : z₀ ∈ FlatSet f) :
    (∀ x ∈ S, 0 < uSideFunc f z₀ x) ∨ (∀ x ∈ S, uSideFunc f z₀ x < 0) := by
  have hne0 : ∀ x ∈ S, uSideFunc f z₀ x ≠ 0 := by
    intro x hx
    exact uSideFunc_ne_zero hf ha hz₀F (hSsub hx)
  have hφcontOn : ContinuousOn (uSideFunc f z₀) S :=
    continuousOn_uSideFunc hf ha hSsub z₀
  by_cases hpos : ∃ x ∈ S, 0 < uSideFunc f z₀ x
  · left
    intro x₂ hx₂
    by_contra hnot
    have hx₂le : uSideFunc f z₀ x₂ ≤ 0 := le_of_not_gt hnot
    have hx₂neg : uSideFunc f z₀ x₂ < 0 := lt_of_le_of_ne hx₂le (hne0 x₂ hx₂)
    rcases hpos with ⟨x₁, hx₁, hx₁pos⟩
    have hIVT : Set.Icc (uSideFunc f z₀ x₂) (uSideFunc f z₀ x₁) ⊆ (uSideFunc f z₀) '' S :=
      IsPreconnected.intermediate_value hSconn hx₂ hx₁ hφcontOn
    have hzero_mem : (0 : ℝ) ∈ Set.Icc (uSideFunc f z₀ x₂) (uSideFunc f z₀ x₁) := by
      rw [Set.mem_Icc]
      exact ⟨le_of_lt hx₂neg, le_of_lt hx₁pos⟩
    rcases hIVT hzero_mem with ⟨x₀, hx₀, hφx₀⟩
    exact hne0 x₀ hx₀ (by simpa using hφx₀)
  · right
    intro x₂ hx₂
    have hx₂le : uSideFunc f z₀ x₂ ≤ 0 := by
      by_contra hgt
      exact hpos ⟨x₂, hx₂, lt_of_not_ge hgt⟩
    exact lt_of_le_of_ne hx₂le (hne0 x₂ hx₂)


/-! ## The full ruling line avoids flat components (normal-form input (a)) -/

/-- **Any strip-interior point on the kernel LINE of a `U`-point is a
`U`-point**: for a nonzero kernel direction `w` at `x`, every point of the
full affine line `x + ℝ·w` inside the strip interior lies on the canonical
leaf, hence in `U`.  (Generalizes `FlatFrontier.interior_on_line_is_U`
from the canonical direction to arbitrary kernel directions.) -/
lemma kernel_line_is_U {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {x w z : ℝ²} (hx : x ∈ stripInterior) (hU : dN f x ≠ 0)
    (hwker : dN f x w = 0) (hwne : w ≠ 0)
    (hz : z ∈ stripInterior) (hline : ∃ s : ℝ, z = x + s • w) :
    dN f z ≠ 0 := by
  rcases uBendDirPos_spec hf ha hx hU with ⟨hker, hwne0, hwpos⟩
  rcases kernel_direction_parallel hf hx hU hker hwker hwne0 with ⟨c, hc⟩
  rcases hline with ⟨s, hs⟩
  apply interior_on_line_is_U hf ha hx hU hz
  refine ⟨s * c, ?_⟩
  calc
    z = x + s • w := hs
    _ = x + s • (c • uBendDirPos hf ha hx hU) := by rw [hc]
    _ = x + (s * c) • uBendDirPos hf ha hx hU := by rw [smul_smul]

/-- **The ruling line of a `U`-point contains no flat point**: it meets
`FlatSet` nowhere. -/
lemma kernel_line_avoids_flatSet {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {x w z : ℝ²} (hx : x ∈ stripInterior) (hU : dN f x ≠ 0)
    (hwker : dN f x w = 0) (hwne : w ≠ 0)
    (hzF : z ∈ FlatSet f) (hline : ∃ s : ℝ, z = x + s • w) : False := by
  have hzS : z ∈ stripInterior := (mem_FlatSet.mp hzF).1
  have hzU : dN f z ≠ 0 := kernel_line_is_U hf ha hx hU hwker hwne hzS hline
  exact hzU (mem_FlatSet.mp hzF).2

/-- **The ruling line of a `U`-point avoids every flat component**: it
meets no point of any `flatComponent`.  (This is normal-form input (a):
a bordering ruling of a flat component never crosses into it.) -/
lemma kernel_line_avoids_flatComponent {a : ℝ} {f : ℝ² → ℝ³}
    (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {x w p z : ℝ²}
    (hx : x ∈ stripInterior) (hU : dN f x ≠ 0)
    (hwker : dN f x w = 0) (hwne : w ≠ 0)
    (hzC : z ∈ flatComponent f p) (hline : ∃ s : ℝ, z = x + s • w) : False := by
  exact kernel_line_avoids_flatSet hf ha hx hU hwker hwne
    (flatComponent_subset_FlatSet f p hzC) hline
