/-
# `Work.FTS.GalBasis.cc.CutDefs` — the explicit cutoff family of the density lemma

This module only *defines* the family of smooth cutoffs used by
`Work.FTS.GalBasis.exists_cc_of_honClass` (the `ℋ⁴`-density of the compactly supported smooth
class `Coreφ` in the honest open class `{SmoothOpen, HkMem α 4, BdryTraces α 4, L₁₂(·)(0) = 0}`).

For `N : ℕ` the cutoff is the product of two one-dimensional smooth steps,

  `psiCut N z θ = cutA N z * cutB N θ`,

with the *scale invariant* mesh `1/(N+1)` (the point of the construction: the operators
`D_z = z ∂_z` and `D_θ = sin(2θ) ∂_θ` of the `ℋ⁴`-norm act on a step of mesh `h` with bounds
*uniform in* `h`):

* `cutA N z = smoothTransition ((N+1) z - 1) * smoothTransition (2 - z/(N+1))` is `0` for
  `z ≤ 1/(N+1)`, `1` on `[2/(N+1), N+1]`, and `0` again for `z ≥ 2(N+1)`;
* `cutB N θ = smoothTransition ((N+1) θ - 1) * smoothTransition ((N+1) (π/2 - θ) - 1)` is `0`
  for `θ ≤ 1/(N+1)` or `θ ≥ π/2 - 1/(N+1)`, and `1` on `[2/(N+1), π/2 - 2/(N+1)]`.

Hence `psiCut N` is `1` on the *plateau* `[2/(N+1), N+1] × [2/(N+1), π/2 - 2/(N+1)]` and
vanishes off the *outer box* `[1/(N+1), 2(N+1)] × [1/(N+1), π/2 - 1/(N+1)]`, and the plateau
increases to the whole quadrant as `N → ∞` while the outer box shrinks to the boundary.

The scalar steps `cutA`, `cutB` are separate definitions because the mixed derivatives of the
product factorise through them (`mixed j i (psiCut N) = DzIter j (cutA N) * DthIter i (cutB N)`),
which is what makes both the uniform derivative bound and the support of the `θ`-derivatives
(`θ ∉ layer → D_θ^i (cutB N) = 0` for `i ≥ 1`) immediate.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.Galerkin.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology

namespace Work.FTS.GalBasis.cc

open Work.FTS.Galerkin (Fn)

/-- The radial step of mesh `1/(N+1)`: `0` for `z ≤ 1/(N+1)`, `1` on `[2/(N+1), N+1]`, `0`
again for `z ≥ 2(N+1)`. -/
def cutA (N : ℕ) : ℝ → ℝ := fun z =>
  Real.smoothTransition (((N : ℝ) + 1) * z - 1) * Real.smoothTransition (2 - z / ((N : ℝ) + 1))

/-- The angular step of mesh `1/(N+1)`: `0` for `θ ≤ 1/(N+1)` or `θ ≥ π/2 - 1/(N+1)`, and `1`
on `[2/(N+1), π/2 - 2/(N+1)]`. -/
def cutB (N : ℕ) : ℝ → ℝ := fun θ =>
  Real.smoothTransition (((N : ℝ) + 1) * θ - 1)
    * Real.smoothTransition (((N : ℝ) + 1) * (Real.pi / 2 - θ) - 1)

/-- **The cutoff family** of the density lemma. -/
def psiCut (N : ℕ) : Fn := fun z θ => cutA N z * cutB N θ

/-- The lower end of the outer box in the `z`-variable: `1/(N+1)`. -/
def zlo (N : ℕ) : ℝ := 1 / ((N : ℝ) + 1)

/-- The upper end of the outer box in the `z`-variable: `2(N+1)`. -/
def zhi (N : ℕ) : ℝ := 2 * ((N : ℝ) + 1)

/-- The lower end of the outer box in the `θ`-variable: `1/(N+1)`. -/
def tlo (N : ℕ) : ℝ := 1 / ((N : ℝ) + 1)

/-- The upper end of the outer box in the `θ`-variable: `π/2 - 1/(N+1)`. -/
def thi (N : ℕ) : ℝ := Real.pi / 2 - 1 / ((N : ℝ) + 1)

/-- The lower end of the plateau in the `z`-variable: `2/(N+1)`. -/
def plo (N : ℕ) : ℝ := 2 / ((N : ℝ) + 1)

/-- The upper end of the plateau in the `z`-variable: `N+1`. -/
def phiN (N : ℕ) : ℝ := (N : ℝ) + 1

/-- The lower end of the plateau in the `θ`-variable: `2/(N+1)`. -/
def qlo (N : ℕ) : ℝ := 2 / ((N : ℝ) + 1)

/-- The upper end of the plateau in the `θ`-variable: `π/2 - 2/(N+1)`. -/
def qhi (N : ℕ) : ℝ := Real.pi / 2 - 2 / ((N : ℝ) + 1)

/-- `(z,θ)` lies in the *plateau* of `psiCut N`, where it equals `1`. -/
def InPlateau (N : ℕ) (z θ : ℝ) : Prop := z ∈ Set.Icc (plo N) (phiN N) ∧ θ ∈ Set.Icc (qlo N) (qhi N)

/-- `(z,θ)` lies outside the *outer box* of `psiCut N`, where it vanishes. -/
def OffBox (N : ℕ) (z θ : ℝ) : Prop :=
  z ∉ Set.Icc (zlo N) (zhi N) ∨ θ ∉ Set.Icc (tlo N) (thi N)

/-- `θ` lies outside the two *layers* of the angular step `cutB N` (the intervals
`[1/(N+1), 2/(N+1)]` and `[π/2 - 2/(N+1), π/2 - 1/(N+1)]`), i.e. in the region where `cutB N` is
constant and its iterated `D_θ`-derivatives vanish. -/
def NotInThetaLayer (N : ℕ) (θ : ℝ) : Prop :=
  θ ∉ Set.Icc (tlo N) (2 / ((N : ℝ) + 1)) ∧ θ ∉ Set.Icc (Real.pi / 2 - 2 / ((N : ℝ) + 1)) (thi N)

/-- The outer box of `psiCut N` lies in the open quadrant: on it `z > 0` and `0 < θ < π/2`.
Consequently the support of `psiCut N` is contained in `Q0`, which is what makes `psiCut N · f`
globally smooth for a function `f` that is only smooth on the open quadrant. -/
theorem box_subset_quadrant (N : ℕ) {z θ : ℝ}
    (hz : z ∈ Set.Icc (zlo N) (zhi N)) (hθ : θ ∈ Set.Icc (tlo N) (thi N)) :
    0 < z ∧ 0 < θ ∧ θ < Real.pi / 2 := by
  have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have h1 : 0 < 1 / ((N : ℝ) + 1) := by positivity
  refine ⟨lt_of_lt_of_le h1 hz.1, lt_of_lt_of_le h1 hθ.1, ?_⟩
  have hthi : thi N < Real.pi / 2 := by
    simp only [thi]; linarith [h1]
  exact lt_of_le_of_lt hθ.2 hthi

/-- The support of `psiCut N` is contained in the open quadrant. -/
theorem supp_subset_quadrant (N : ℕ) {z θ : ℝ} (h : psiCut N z θ ≠ 0) :
    0 < z ∧ 0 < θ ∧ θ < Real.pi / 2 := by
  have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  obtain ⟨ha, hb⟩ := mul_ne_zero_iff.mp h
  have ha' : Real.smoothTransition (((N : ℝ) + 1) * z - 1) ≠ 0 ∧
      Real.smoothTransition (2 - z / ((N : ℝ) + 1)) ≠ 0 := by
    simpa only [cutA] using mul_ne_zero_iff.mp ha
  have hb' : Real.smoothTransition (((N : ℝ) + 1) * θ - 1) ≠ 0 ∧
      Real.smoothTransition (((N : ℝ) + 1) * (Real.pi / 2 - θ) - 1) ≠ 0 := by
    simpa only [cutB] using mul_ne_zero_iff.mp hb
  obtain ⟨ha1, ha2⟩ := ha'
  obtain ⟨hb1, hb2⟩ := hb'
  have e1 : 0 < ((N : ℝ) + 1) * z - 1 := by
    by_contra hc
    exact ha1 (Real.smoothTransition.zero_of_nonpos (le_of_not_gt hc))
  have e2 : 0 < ((N : ℝ) + 1) * θ - 1 := by
    by_contra hc
    exact hb1 (Real.smoothTransition.zero_of_nonpos (le_of_not_gt hc))
  have e3 : 0 < ((N : ℝ) + 1) * (Real.pi / 2 - θ) - 1 := by
    by_contra hc
    exact hb2 (Real.smoothTransition.zero_of_nonpos (le_of_not_gt hc))
  refine ⟨by nlinarith, by nlinarith, by nlinarith⟩

end Work.FTS.GalBasis.cc
