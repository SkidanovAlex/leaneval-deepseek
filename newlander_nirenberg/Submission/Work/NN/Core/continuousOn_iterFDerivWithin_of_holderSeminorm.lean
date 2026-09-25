import Mathlib
import Submission.Work.CR.Flat.Holder

namespace Work.NN.Core

open scoped NNReal ENNReal
open Set Metric

/-- If the `m`-th iterated (within) derivative of `f` has finite Hölder seminorm of
order `α > 0` on `Ω`, then it is continuous on `Ω`.

Indeed the seminorm bound gives `‖D^m f x - D^m f y‖ ≤ C ‖x - y‖^α` for all `x, y ∈ Ω`,
so `D^m f` is Hölder continuous with exponent `α > 0` on `Ω`, hence continuous. -/
theorem continuousOn_iterFDerivWithin_of_holderSeminorm {n : ℕ} {m : ℕ} {α C : ℝ} (hα : 0 < α)
    (hC : 0 ≤ C) {f : (Fin n → ℂ) → ℂ} {Ω : Set (Fin n → ℂ)}
    (h : Work.CR.Flat.holderSeminorm m α f Ω ≤ ENNReal.ofReal C) :
    ContinuousOn (iteratedFDerivWithin ℝ m f Ω) Ω := by
  set g := iteratedFDerivWithin ℝ m f Ω with hg
  -- The seminorm bound yields the pointwise Hölder estimate on `Ω`.
  have hb : ∀ x ∈ Ω, ∀ y ∈ Ω, ‖g x - g y‖ ≤ C * ‖x - y‖ ^ α := by
    intro x hx y hy
    rcases eq_or_ne x y with rfl | hxy
    · simp only [sub_self, norm_zero]
      rw [Real.zero_rpow hα.ne']
      simp
    · have h1 : ENNReal.ofReal (‖g x - g y‖ / ‖x - y‖ ^ α) ≤ ENNReal.ofReal C :=
        le_trans (Work.CR.Flat.le_holderSeminorm m α f Ω hx hy hxy) h
      have h2 : ‖g x - g y‖ / ‖x - y‖ ^ α ≤ C := (ENNReal.ofReal_le_ofReal_iff hC).mp h1
      have hpos : 0 < ‖x - y‖ ^ α :=
        Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) α
      rwa [div_le_iff₀ hpos] at h2
  -- Assemble the Hölder condition in extended-distance form.
  have hCcoe : (↑(C.toNNReal) : ENNReal) = ENNReal.ofReal C := by
    rw [← ENNReal.ofReal_coe_nnreal (p := C.toNNReal), Real.coe_toNNReal C hC]
  have hH : HolderOnWith C.toNNReal α.toNNReal g Ω := by
    intro x hx y hy
    rw [edist_dist, edist_dist, dist_eq_norm, dist_eq_norm]
    rw [hCcoe, Real.coe_toNNReal α (le_of_lt hα)]
    calc ENNReal.ofReal ‖g x - g y‖
        ≤ ENNReal.ofReal (C * ‖x - y‖ ^ α) := ENNReal.ofReal_le_ofReal (hb x hx y hy)
      _ = ENNReal.ofReal C * ENNReal.ofReal (‖x - y‖ ^ α) := ENNReal.ofReal_mul hC
      _ = ENNReal.ofReal C * (ENNReal.ofReal ‖x - y‖) ^ α := by
            rw [ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (le_of_lt hα)]
  have h0 : (0 : ℝ≥0) < α.toNNReal := Real.toNNReal_pos.mpr hα
  exact hH.continuousOn h0

end Work.NN.Core
