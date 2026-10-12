import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Algebra.Order.Star.Real
import ChallengeDeps
import Submission.Work.BSKinetic.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1B.chiCubeBump` — the **smooth, cube-supported** bump

Holder of `Submission/Work/BoseFixB1B/lowCountBound.lean`; decision (B) of the lead, recorded in
`FINDING_flatArmCountInputs.md` §10–§11.

## Why

`chiSmall M = (ζζζ)^M/√…` (`ζ(y) = cos(πy)`, `ChiSmall.lean`) is the corpus's **cube**-supported
window, and with `M := mValue = 48` it is only `C^{47}`.  The ball bump `chiB` is a Mathlib
`ContDiffBump`, hence `C^∞`, and *that* is why the ball-cutoff chapter's cut-words estimate
(`Work.BoseFixB1S.corrCutWordsSharp`, proved by a **265-fold** integration by parts, with parameter
lemma `ℓ³d⁻⁵s^{525} ≤ a³ℓ⁻²`, `525 = 2·265−5`) works there.  Both reviewers refuted the cube twin of
that theorem for exactly this reason: only `‖p‖^{-49}` decay is available at `chiSmall 48`, so the
sharp `ℓ⁻²` rows lose `X^{-O(400)}`.

This module supplies the repair: a bump that is **both cube-supported** (so FS's
`eq:chiBdefinition`, `goodSet`, `dlBox`, `boxMass` and every kernel geometry carry over verbatim)
**and `C^∞`** (so the IBP engine applies).

## The trick that makes `ContDiff` immediate

The naive form `smoothTransition (2 - 4*|t|)` is smooth only because the profile is *flat* where
`|t|` is not, which is awkward to formalise.  But the profile of `|t|` is the **product of the two
one-sided profiles**:

    smoothTransition (2 - 4*|t|) = smoothTransition (2 - 4*t) * smoothTransition (2 + 4*t)

(each side is killed by the factor that is `1` there, since `1 ≤ 2 + 4t` for `t ≥ 0` and
`1 ≤ 2 - 4t` for `t ≤ 0`).  So the bump is a product of **six** smooth compositions of the
coordinate functionals — no smoothness of `|·|` is needed anywhere.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseFixB1B

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The one-sided factorisation of the profile of `|t|`.** -/
lemma smoothTransition_abs_eq_mul (t : ℝ) :
    Real.smoothTransition (2 - 4 * |t|)
      = Real.smoothTransition (2 - 4 * t) * Real.smoothTransition (2 + 4 * t) := by
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht,
      Real.smoothTransition.one_of_one_le (show (1:ℝ) ≤ 2 + 4 * t by linarith)]
    ring
  · rw [abs_of_neg (not_le.mp ht),
      Real.smoothTransition.one_of_one_le (show (1:ℝ) ≤ 2 - 4 * t by linarith)]
    ring

/-- **The smooth cube-supported bump**: the product of the three coordinate profiles,
`tsupport ⊆ [-1/2,1/2]³`, plateau `= 1` on `|z_j| ≤ 1/4`, and `ContDiff ℝ ∞`. -/
noncomputable def chiCubeBase (z : E3) : ℝ :=
  Real.smoothTransition (2 - 4 * |z.ofLp 0|) * Real.smoothTransition (2 - 4 * |z.ofLp 1|)
    * Real.smoothTransition (2 - 4 * |z.ofLp 2|)

/-- The bump as a product of six smooth one-sided profiles (the form whose smoothness is immediate). -/
lemma chiCubeBase_eq_prod (z : E3) : chiCubeBase z =
    (Real.smoothTransition (2 - 4 * z.ofLp 0) * Real.smoothTransition (2 + 4 * z.ofLp 0))
      * (Real.smoothTransition (2 - 4 * z.ofLp 1) * Real.smoothTransition (2 + 4 * z.ofLp 1))
      * (Real.smoothTransition (2 - 4 * z.ofLp 2) * Real.smoothTransition (2 + 4 * z.ofLp 2)) := by
  simp only [chiCubeBase, smoothTransition_abs_eq_mul]

lemma chiCubeBase_nonneg (z : E3) : 0 ≤ chiCubeBase z := by
  rw [chiCubeBase]
  exact mul_nonneg (mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _))
    (Real.smoothTransition.nonneg _)

lemma chiCubeBase_le_one (z : E3) : chiCubeBase z ≤ 1 := by
  rw [chiCubeBase]
  have h0 := Real.smoothTransition.nonneg (2 - 4 * |z.ofLp 0|)
  have h1 := Real.smoothTransition.nonneg (2 - 4 * |z.ofLp 1|)
  have h2 := Real.smoothTransition.nonneg (2 - 4 * |z.ofLp 2|)
  have h0' := Real.smoothTransition.le_one (2 - 4 * |z.ofLp 0|)
  have h1' := Real.smoothTransition.le_one (2 - 4 * |z.ofLp 1|)
  have h2' := Real.smoothTransition.le_one (2 - 4 * |z.ofLp 2|)
  have h01 : Real.smoothTransition (2 - 4 * |z.ofLp 0|)
      * Real.smoothTransition (2 - 4 * |z.ofLp 1|) ≤ 1 := by nlinarith [h0, h1, h0', h1']
  have h01nn : (0:ℝ) ≤ Real.smoothTransition (2 - 4 * |z.ofLp 0|)
      * Real.smoothTransition (2 - 4 * |z.ofLp 1|) := mul_nonneg h0 h1
  nlinarith [h01, h01nn, h2, h2']

/-- **Plateau**: on the inner cube `|z_j| ≤ 1/4` the bump is `1`. -/
lemma chiCubeBase_eq_one_of_abs_le (z : E3)
    (h0 : |z.ofLp 0| ≤ 1 / 4) (h1 : |z.ofLp 1| ≤ 1 / 4) (h2 : |z.ofLp 2| ≤ 1 / 4) :
    chiCubeBase z = 1 := by
  rw [chiCubeBase, Real.smoothTransition.one_of_one_le (by linarith : (1:ℝ) ≤ 2 - 4 * |z.ofLp 0|),
    Real.smoothTransition.one_of_one_le (by linarith : (1:ℝ) ≤ 2 - 4 * |z.ofLp 1|),
    Real.smoothTransition.one_of_one_le (by linarith : (1:ℝ) ≤ 2 - 4 * |z.ofLp 2|)]
  ring

/-- **Support**: the bump vanishes off the cube `|z_j| < 1/2`. -/
lemma chiCubeBase_eq_zero_of_half_le (z : E3) (h : 1 / 2 ≤ |z.ofLp 0| ∨ 1 / 2 ≤ |z.ofLp 1|
    ∨ 1 / 2 ≤ |z.ofLp 2|) : chiCubeBase z = 0 := by
  rcases h with h | h | h
  · rw [chiCubeBase, Real.smoothTransition.zero_of_nonpos (by linarith : 2 - 4 * |z.ofLp 0| ≤ 0),
      zero_mul, zero_mul]
  · rw [chiCubeBase, Real.smoothTransition.zero_of_nonpos (by linarith : 2 - 4 * |z.ofLp 1| ≤ 0),
      mul_zero, zero_mul]
  · rw [chiCubeBase, Real.smoothTransition.zero_of_nonpos (by linarith : 2 - 4 * |z.ofLp 2| ≤ 0),
      mul_zero]

/-- **Smoothness** — the whole point of the construction. -/
lemma chiCubeBase_contDiff : ContDiff ℝ ∞ chiCubeBase := by
  have hfac : ∀ i : Fin 3, ContDiff ℝ ∞ (fun z : E3 =>
      Real.smoothTransition (2 - 4 * z.ofLp i) * Real.smoothTransition (2 + 4 * z.ofLp i)) := by
    intro i
    have hclm : ContDiff ℝ ∞ (fun z : E3 => z.ofLp i) := by
      simpa using
        (ContinuousLinearMap.contDiff (𝕜 := ℝ)
          (PiLp.proj (p := 2) (β := fun _ : Fin 3 => ℝ) i))
    exact (Real.smoothTransition.contDiff.comp ((contDiff_const.sub (contDiff_const.mul hclm)))).mul
      (Real.smoothTransition.contDiff.comp ((contDiff_const.add (contDiff_const.mul hclm))))
  rw [show chiCubeBase = fun z : E3 =>
      (Real.smoothTransition (2 - 4 * z.ofLp 0) * Real.smoothTransition (2 + 4 * z.ofLp 0))
        * (Real.smoothTransition (2 - 4 * z.ofLp 1) * Real.smoothTransition (2 + 4 * z.ofLp 1))
        * (Real.smoothTransition (2 - 4 * z.ofLp 2) * Real.smoothTransition (2 + 4 * z.ofLp 2))
      from funext chiCubeBase_eq_prod]
  exact ((hfac 0).mul (hfac 1)).mul (hfac 2)

/-- The `ℓ`-scaled bump `chiCubeScale ℓ z = chiCubeBase (ℓ⁻¹ • z)` — the twin of `chiScale ℓ`. -/
noncomputable def chiCubeScale (ℓ : ℝ) (z : E3) : ℝ := chiCubeBase ((ℓ⁻¹) • z)

/-- **The `chiSmallB` twin**: FS's `χ_{B(u)}` at the *smooth* cube bump.  The `M` argument is
carried (and unused) so that the whole chapter's restatements are a **name swap**
`chiSmallB M ℓ d u` ↦ `chiCubeB M ℓ d u` with nothing else touched. -/
noncomputable def chiCubeB (M : ℕ) (ℓ d : ℝ) (u z : E3) : ℝ :=
  chiCubeScale ℓ z * chiCubeScale (ℓ * d) (z - (ℓ * d) • u)

lemma chiCubeScale_contDiff (ℓ : ℝ) : ContDiff ℝ ∞ (chiCubeScale ℓ) := by
  unfold chiCubeScale
  exact chiCubeBase_contDiff.comp
    (ContinuousLinearMap.contDiff ((ℓ⁻¹) • ContinuousLinearMap.id ℝ E3))

/-- **The twin is smooth** — the property that makes the 265-fold IBP engine available at the cube
window, and that `chiSmall 48` cannot provide. -/
lemma chiCubeB_contDiff (M : ℕ) (ℓ d : ℝ) (u : E3) : ContDiff ℝ ∞ (chiCubeB M ℓ d u) := by
  have h2 : ContDiff ℝ ∞ (fun z : E3 => z - (ℓ * d) • u) :=
    contDiff_id.sub contDiff_const
  unfold chiCubeB
  exact (chiCubeScale_contDiff ℓ).mul ((chiCubeScale_contDiff (ℓ * d)).comp h2)

/-- **Support (first factor)**: the twin vanishes wherever the `ℓ`-scaled bump does. -/
lemma chiCubeB_eq_zero_of_fst (M : ℕ) {ℓ d : ℝ} {u z : E3}
    (h : chiCubeBase ((ℓ⁻¹) • z) = 0) : chiCubeB M ℓ d u z = 0 := by
  unfold chiCubeB chiCubeScale
  rw [h, zero_mul]

/-- **Support (second factor)**: and wherever the `(ℓd)`-scaled bump does — together these give
`tsupport ⊆ dlBox ℓ d u`, exactly as for `chiSmallB`. -/
lemma chiCubeB_eq_zero_of_snd (M : ℕ) {ℓ d : ℝ} {u z : E3}
    (h : chiCubeBase (((ℓ * d)⁻¹) • (z - (ℓ * d) • u)) = 0) :
    chiCubeB M ℓ d u z = 0 := by
  unfold chiCubeB chiCubeScale
  rw [h, mul_zero]


lemma chiCubeScale_nonneg (ℓ : ℝ) (z : E3) : 0 ≤ chiCubeScale ℓ z :=
  chiCubeBase_nonneg _

lemma chiCubeScale_le_one (ℓ : ℝ) (z : E3) : chiCubeScale ℓ z ≤ 1 :=
  chiCubeBase_le_one _

lemma chiCubeB_nonneg (M : ℕ) (ℓ d : ℝ) (u z : E3) : 0 ≤ chiCubeB M ℓ d u z := by
  unfold chiCubeB
  exact mul_nonneg (chiCubeScale_nonneg ℓ z) (chiCubeScale_nonneg (ℓ * d) _)

/-- **The twin is a window of height `1`**: this supplies the `∀ z, |χ z| ≤ κ` hypothesis of every
one-window instrument at `κ = 1` (the `chiSmallB` statements carry `κ = chiSupAbs·chiSmallNormFactor M`,
which is what forces the *astronomical* credit constants of `FINDING_creditConstantObstruction.md`). -/
lemma chiCubeB_le_one (M : ℕ) (ℓ d : ℝ) (u z : E3) : chiCubeB M ℓ d u z ≤ 1 := by
  unfold chiCubeB
  have h1 := chiCubeScale_le_one ℓ z
  have h2 := chiCubeScale_le_one (ℓ * d) (z - (ℓ * d) • u)
  have h1' := chiCubeScale_nonneg ℓ z
  have h2' := chiCubeScale_nonneg (ℓ * d) (z - (ℓ * d) • u)
  nlinarith [mul_nonneg h1' h2', mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2)]

/-- **The localised pair kernel at the smooth cube bump** — the `wSmall1Pair` twin of the matched
window: the same `χ x · χ y · 𝒲(x − y)` shape with `chiSmallB` replaced by `chiCubeB` (a name swap:
the `M` argument is carried and unused, see `chiCubeB`). -/
noncomputable def wSmall1PairCube {v : E3 → ℝ} (h : Work.UBB.ScatSol v) (M : ℕ) (ℓ d : ℝ)
    (u : E3) : E3 → E3 → ℝ :=
  fun x y => chiCubeB M ℓ d u x * chiCubeB M ℓ d u y *
    (Submission.BoseGases.wSmallScaled M (ℓ * d) (Submission.BoseGases.g0 v h) (x - y)
      / Submission.BoseGases.convScale ℓ (x - y))

/-- **The kernel-shape lemma**: `wSmall1PairCube` is *definitionally* the `χ x · χ y · 𝒲(x − y)`
shape that `Work.BoseFixB1S.boxPairIntGenC2'` and the matched-window rung consume — the exact
analogue of `Work.BoseFixB1B.pairRung.chainInputs.wSmall1Pair_kernel` for `wSmall1Pair`. -/
lemma wSmall1PairCube_kernel {v : E3 → ℝ} (h : Work.UBB.ScatSol v) (M : ℕ) (ℓ d : ℝ) (u : E3) :
    wSmall1PairCube h M ℓ d u = fun x y : E3 => chiCubeB M ℓ d u x * chiCubeB M ℓ d u y *
      (Submission.BoseGases.wSmallScaled M (ℓ * d) (Submission.BoseGases.g0 v h) (x - y)
        / Submission.BoseGases.convScale ℓ (x - y)) := rfl

/-- **The `C²` form**: the hypothesis actually consumed by the one-window instruments
(`boxPairIntGenC2'` and the `contDiff_three` slots), obtained from `chiCubeB_contDiff` — carry it
so that the chapter's restatements are a name swap of the `chiSmallB` lemmas. -/
lemma chiCubeB_contDiff_two (M : ℕ) (ℓ d : ℝ) (u : E3) : ContDiff ℝ 2 (chiCubeB M ℓ d u) :=
  (chiCubeB_contDiff M ℓ d u).of_le (WithTop.coe_le_coe.mpr le_top)

/-- **The absolute-value bound**: the `abs_chiSmallB_le` slot, at `κ = 1`. -/
lemma chiCubeB_abs_le_one (M : ℕ) (ℓ d : ℝ) (u z : E3) : |chiCubeB M ℓ d u z| ≤ 1 := by
  rw [abs_of_nonneg (chiCubeB_nonneg M ℓ d u z)]
  exact chiCubeB_le_one M ℓ d u z

end Work.BoseFixB1B
