import Mathlib.Tactic.Have
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SmallBoxBridge.Bridge
import Submission.Work.SmallBoxTBWord.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Smoothness of the box mean `boxP`

    `boxP volA A i Φ x = (1/volA) · ∫_{z∈A} Φ (x_{i←z}) dz`

is smooth in `x` whenever `Φ` is smooth and `A` is compact: the uncurried
integrand `(x, z) ↦ Φ (x_{i←z})` is smooth (composition of `Φ` with the
smooth insertion map `(x,z) ↦ Function.update x i z`), and the parameter
dependent integral over the compact set `A` is smooth
(`Commons.Analysis.Calculus.contDiff_setIntegral_isCompact`).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.SmallBoxTBWord

open Submission.BoseGases
open _root_.BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-- The insertion map `(x, z) ↦ Function.update x i z` is smooth (jointly in `x` and `z`). -/
theorem boxP_contDiff_update_smooth {N : ℕ} (i : Fin N) :
    ContDiff ℝ (⊤ : ENat) (fun q : X N × ℝ³ => Function.update q.1 i q.2) := by
  have hEq : (fun q : X N × ℝ³ => Function.update q.1 i q.2)
      = fun q : X N × ℝ³ => q.1 + Function.update (0 : X N) i (q.2 - q.1 i) := by
    funext q j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Function.update_of_ne hj]
  rw [hEq]
  have hz : ContDiff ℝ (⊤ : ENat) (fun q : X N × ℝ³ => q.2 - q.1 i) := by fun_prop
  exact contDiff_fst.add ((contDiff_update (⊤ : ENat) (0 : X N) i).comp hz)

theorem boxP_contDiff {N : ℕ} {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : IsCompact A) (volA : ℝ) (i : Fin N) {Φ : Submission.BoseGases.X N → ℝ} (hΦ : ContDiff ℝ (⊤ : ENat) Φ) : ContDiff ℝ (⊤ : ENat) (Work.SmallBoxTBWord.boxP volA A i Φ) := by
  have hU : ContDiff ℝ (⊤ : ENat) (fun q : X N × ℝ³ => Function.update q.1 i q.2) :=
    boxP_contDiff_update_smooth i
  have hF : ContDiff ℝ (⊤ : ENat)
      (Function.uncurry (fun (p : X N) (z : ℝ³) => Φ (Function.update p i z))) := by
    have hEq : (Function.uncurry (fun (p : X N) (z : ℝ³) => Φ (Function.update p i z)))
        = fun q : X N × ℝ³ => Φ (Function.update q.1 i q.2) := rfl
    rw [hEq]
    exact hΦ.comp hU
  have hmain : ContDiff ℝ (⊤ : ENat) (fun p : X N => ∫ z in A, Φ (Function.update p i z)) :=
    Commons.Analysis.Calculus.contDiff_setIntegral_isCompact (k := A) hA hF
  unfold boxP
  exact hmain.const_smul (1 / volA)

end Work.SmallBoxTBWord
