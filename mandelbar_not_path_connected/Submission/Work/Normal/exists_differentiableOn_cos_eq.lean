import Mathlib
import Submission.Work.Escape.exists_differentiableOn_ball_clog

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Lifting a holomorphic function on the disc through `cos`

Given a holomorphic `f` on the unit disc which never takes the values `1` or `-1`, we construct a
holomorphic `g` on the disc with `cos (g z) = f z`.

The construction is the classical one.  Since `f z ≠ ±1`, the function `f ² - 1` is holomorphic
and nowhere vanishing on the disc, so it admits a holomorphic square root `h` (`h z ^ 2 = f z ^ 2 -
1`); this uses `Work.Escape.exists_differentiableOn_ball_clog` for the logarithm and `exp (L / 2)`
for the square root.  Then `w = f + h` is holomorphic and nowhere zero, because
`w * (f - h) = f ² - h ² = 1`; hence `w` has a holomorphic logarithm `M`.  Finally
`g = -i M` satisfies `cos (g z) = cosh (M z) = (w z + 1 / w z) / 2 = (w z + f z - h z) / 2 = f z`.
-/

namespace Work.Normal

theorem exists_differentiableOn_cos_eq {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (Metric.ball 0 1))
    (hne : ∀ z ∈ Metric.ball 0 1, f z ≠ 1 ∧ f z ≠ -1) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (Metric.ball 0 1) ∧
      ∀ z ∈ Metric.ball 0 1, Complex.cos (g z) = f z := by
  -- Step 1: `f ^ 2 - 1` is holomorphic and nowhere zero on the disc.
  have hFdiff : DifferentiableOn ℂ (fun z => f z ^ 2 - 1) (Metric.ball 0 1) := by fun_prop
  have hFne : ∀ z ∈ Metric.ball 0 1, f z ^ 2 - 1 ≠ 0 := by
    intro z hz h
    have hfac : (f z - 1) * (f z + 1) = 0 := by
      have hh : f z ^ 2 - 1 = (f z - 1) * (f z + 1) := by ring
      rw [hh] at h
      exact h
    rcases mul_eq_zero.mp hfac with h1 | h2
    · exact (hne z hz).1 (sub_eq_zero.mp h1)
    · exact (hne z hz).2 (add_eq_zero_iff_eq_neg.mp h2)
  obtain ⟨L, hLdiff, hLexp, _⟩ :=
    Work.Escape.exists_differentiableOn_ball_clog (c := 0) (r := 1) hFdiff hFne
  -- Step 2: a holomorphic square root `h` of `f ^ 2 - 1`.
  set h : ℂ → ℂ := fun z => Complex.exp (L z / 2) with hhdef
  have hhdiff : DifferentiableOn ℂ h (Metric.ball 0 1) := by
    rw [hhdef]; fun_prop
  have hhsq : ∀ z ∈ Metric.ball 0 1, h z ^ 2 = f z ^ 2 - 1 := by
    intro z hz
    have hexp : Complex.exp (L z / 2) ^ 2 = Complex.exp (L z) := by
      rw [sq, ← Complex.exp_add]
      congr 1
      ring
    rw [hhdef]
    simp only
    rw [hexp, hLexp z hz]
  -- Step 3: `w = f + h` is holomorphic and nowhere zero.
  have hsumdiff : DifferentiableOn ℂ (fun z => f z + h z) (Metric.ball 0 1) :=
    hf.add hhdiff
  set w : ℂ → ℂ := fun z => f z + h z with hwdef
  have hwdiff : DifferentiableOn ℂ w (Metric.ball 0 1) := by
    rw [hwdef]; exact hsumdiff
  have hprod : ∀ z ∈ Metric.ball 0 1, w z * (f z - h z) = 1 := by
    intro z hz
    have h1 : (f z + h z) * (f z - h z) = f z ^ 2 - h z ^ 2 := by ring
    have h2 : h z ^ 2 = f z ^ 2 - 1 := hhsq z hz
    rw [hwdef]
    simp only
    rw [h1, h2]
    ring
  have hwne : ∀ z ∈ Metric.ball 0 1, w z ≠ 0 := by
    intro z hz hw0
    have h1 := hprod z hz
    rw [hw0, zero_mul] at h1
    exact one_ne_zero h1.symm
  -- Step 4: a holomorphic logarithm `M` of `w`.
  obtain ⟨M, hMdiff, hMexp, _⟩ :=
    Work.Escape.exists_differentiableOn_ball_clog (c := 0) (r := 1) hwdiff hwne
  -- Step 5: `g = -i M` satisfies `cos (g z) = f z`.
  refine ⟨fun z => -(Complex.I * M z), ?_, ?_⟩
  · fun_prop
  · intro z hz
    have hcos : Complex.cos (-(Complex.I * M z)) = Complex.cosh (M z) := by
      rw [Complex.cos_neg, mul_comm Complex.I, Complex.cos_mul_I]
    rw [hcos]
    rw [Complex.cosh]
    rw [hMexp z hz]
    have hexpneg : Complex.exp (-(M z)) = (w z)⁻¹ := by
      rw [Complex.exp_neg, hMexp z hz]
    rw [hexpneg]
    have hinv : (w z)⁻¹ = f z - h z := by
      calc (w z)⁻¹ = (w z)⁻¹ * (w z * (f z - h z)) := by rw [hprod z hz, mul_one]
        _ = (w z)⁻¹ * (w z) * (f z - h z) := by ring
        _ = f z - h z := by rw [inv_mul_cancel₀ (hwne z hz), one_mul]
    rw [hinv, hwdef]
    simp only
    ring

end Work.Normal
