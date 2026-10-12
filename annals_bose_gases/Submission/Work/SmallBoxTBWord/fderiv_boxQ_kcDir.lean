import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SmallBoxTBWord.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `Q_B`-projection is free in the slot-`i` derivative

`boxQ volA A i Φ = Φ - boxP volA A i Φ`, and the box mean
`boxP volA A i Φ x = (1/volA)∫_{z∈A} Φ (x_{i←z})` *ignores* the slot-`i`
coordinate of `x` (the insertion `Function.update · i z` overwrites it).  Hence
the directional derivative of `boxP` along any direction supported in slot `i`
vanishes, and in particular along `kcDir N i k = δ_{i,k}e_k`.

The proof has two ingredients:

* `boxP` is differentiable at `x` — this is differentiability under the integral
  sign over the compact set `A` (`Commons.Analysis.Calculus`), since the
  uncurried integrand `(p, z) ↦ Φ (x_{i←z})` is smooth;
* `boxP` is constant along the line `x + t • kcDir N i k`, because
  `Function.update (x + t • kcDir) i z = Function.update x i z`
  (`Function.update_idem`).

Then for any function `g` differentiable at `x` that is constant along that
line, `fderiv ℝ g x (kcDir N i k) = 0` by the chain rule applied to the curve
`t ↦ x + t • kcDir N i k` and uniqueness of the derivative.
-/

noncomputable section

open MeasureTheory Metric
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.SmallBoxTBWord

open Submission.BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## The insertion map `(p, z) ↦ p_{i←z}` is smooth -/

lemma contDiff_update_pair {N : ℕ} (i : Fin N) : ContDiff ℝ (⊤ : ENat)
    (fun q : X N × ℝ³ => Function.update q.1 i q.2) := by
  rw [contDiff_pi]
  intro j
  by_cases h : j = i
  · subst h
    have hf : (fun q : X N × ℝ³ => Function.update q.1 j q.2 j) =
        (fun q : X N × ℝ³ => q.2) := by
      funext q; simp
    rw [hf]
    simpa using contDiff_snd (𝕜 := ℝ) (n := (⊤ : ENat)) (E := X N) (F := ℝ³)
  · have hf : (fun q : X N × ℝ³ => Function.update q.1 i q.2 j) =
        (fun q : X N × ℝ³ => q.1 j) := by
      funext q; simp [h]
    rw [hf]
    have h1 : (fun q : X N × ℝ³ => q.1 j) =
        ((ContinuousLinearMap.proj j).comp (ContinuousLinearMap.fst ℝ (X N) ℝ³)) := by
      ext q; rfl
    rw [h1]
    exact (ContinuousLinearMap.proj (R := ℝ) j |>.comp
      (ContinuousLinearMap.fst ℝ (X N) ℝ³)).contDiff

/-! ## The box mean is differentiable -/

lemma boxP_differentiableAt {N : ℕ} {A : Set ℝ³} (hA : IsCompact A) (volA : ℝ)
    (i : Fin N) {Φ : X N → ℝ} (hΦ : ContDiff ℝ (⊤ : ENat) Φ) (x : X N) :
    DifferentiableAt ℝ (boxP volA A i Φ) x := by
  have hU : ContDiff ℝ (⊤ : ENat) (fun q : X N × ℝ³ => Function.update q.1 i q.2) :=
    contDiff_update_pair i
  have hF : ContDiff ℝ (⊤ : ENat)
      (Function.uncurry (fun (p : X N) (z : ℝ³) => Φ (Function.update p i z))) :=
    hΦ.comp hU
  have hmain : ContDiff ℝ (⊤ : ENat) (fun p : X N => ∫ z in A, Φ (Function.update p i z)) :=
    Commons.Analysis.Calculus.contDiff_setIntegral_isCompact (k := A) hA hF
  have hD : DifferentiableAt ℝ (fun p : X N => ∫ z in A, Φ (Function.update p i z)) x :=
    hmain.contDiffAt.differentiableAt (by simp)
  have hgoal : boxP volA A i Φ =
      fun y : X N => (1 / volA) * ∫ z in A, Φ (Function.update y i z) := rfl
  rw [hgoal]
  exact hD.const_mul (1 / volA)

/-! ## The line `x + t • kcDir` and the invariance of the box mean -/

/-- `x + t • kcDir N i k` is the insertion of `x i + t • kcStdBasis k` into slot
`i`. -/
lemma add_smul_kcDir {N : ℕ} (i : Fin N) (k : Fin 3) (x : X N) (t : ℝ) :
    x + t • kcDir N i k = Function.update x i (x i + t • kcStdBasis k) := by
  ext j
  rw [Pi.add_apply, Pi.smul_apply]
  by_cases h : j = i
  · subst h; simp [kcDir]
  · have hz : (kcDir N i k) j = 0 := by simp [kcDir, h]
    rw [hz, smul_zero, add_zero]
    simp [h]

/-- The box mean is constant along the `kcDir N i k` direction. -/
lemma boxP_add_smul_kcDir {N : ℕ} {A : Set ℝ³} (volA : ℝ) (i : Fin N) (Φ : X N → ℝ)
    (k : Fin 3) (x : X N) (t : ℝ) :
    boxP volA A i Φ (x + t • kcDir N i k) = boxP volA A i Φ x := by
  simp only [boxP, add_smul_kcDir, Function.update_idem]

/-! ## A differentiable function constant along a line has zero derivative -/

lemma fderiv_apply_eq_zero_of_const_line {N : ℕ} {g : X N → ℝ} {x v : X N}
    (hg : DifferentiableAt ℝ g x) (hconst : ∀ t : ℝ, g (x + t • v) = g x) :
    fderiv ℝ g x v = 0 := by
  have hline : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    have h1 : HasDerivAt (fun t : ℝ => t • v) v 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const v
    simpa using h1.const_add x
  have hl' : HasFDerivAt g (fderiv ℝ g x) ((fun t : ℝ => x + t • v) 0) := by
    simpa using hg.hasFDerivAt
  have hcomp : HasDerivAt (fun t : ℝ => g (x + t • v)) (fderiv ℝ g x v) 0 :=
    hl'.comp_hasDerivAt 0 hline
  have hconst0 : HasDerivAt (fun t : ℝ => g (x + t • v)) 0 0 := by
    have hfun : (fun t : ℝ => g (x + t • v)) = (fun _ : ℝ => g x) := funext hconst
    rw [hfun]
    exact hasDerivAt_const 0 (g x)
  exact hcomp.unique hconst0

/-! ## The target -/

theorem fderiv_boxQ_kcDir {N : ℕ} {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : IsCompact A) (volA : ℝ) (i : Fin N) {Φ : Submission.BoseGases.X N → ℝ} (hΦ : ContDiff ℝ (⊤ : ENat) Φ) (x : Submission.BoseGases.X N) (k : Fin 3) : fderiv ℝ (Work.SmallBoxTBWord.boxQ volA A i Φ) x (Submission.BoseGases.kcDir N i k) = fderiv ℝ Φ x (Submission.BoseGases.kcDir N i k) := by
  have hΦdiff : DifferentiableAt ℝ Φ x := hΦ.contDiffAt.differentiableAt (by simp)
  have hboxPdiff : DifferentiableAt ℝ (boxP volA A i Φ) x :=
    boxP_differentiableAt hA volA i hΦ x
  have hzero : fderiv ℝ (boxP volA A i Φ) x (kcDir N i k) = 0 :=
    fderiv_apply_eq_zero_of_const_line hboxPdiff
      (fun t => boxP_add_smul_kcDir volA i Φ k x t)
  have hsub : fderiv ℝ (boxQ volA A i Φ) x =
      fderiv ℝ Φ x - fderiv ℝ (boxP volA A i Φ) x := by
    rw [show boxQ volA A i Φ = Φ - boxP volA A i Φ from rfl]
    exact fderiv_sub hΦdiff hboxPdiff
  rw [hsub, sub_apply, hzero, sub_zero]

end Work.SmallBoxTBWord
