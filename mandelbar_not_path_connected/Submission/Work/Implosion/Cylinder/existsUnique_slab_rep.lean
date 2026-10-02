/-
Copyright: subproject `Submission/Work/Implosion/` of `mandelbar_not_path_connected`.

# The slab `x ≤ Re u < x + 1` is a fundamental domain for the cylinder projection

The Écalle cylinder of `Cylinder.lean` is modelled by the map

  `u ↦ exp (2πi u)`,

whose kernel is exactly `ℤ ⊂ ℂ` (`exp_two_pi_I_eq_one_iff`).  Every *strip*
`x ≤ Re u < x + 1` therefore meets every fibre of the projection exactly once:
it is a fundamental domain for the translation `u ↦ u + 1`
(`existsUnique_translate_mem_slab`), and the projection restricts to a bijection
from it onto `ℂ \ {0}`.

The general slab `x ≤ Re u < x + 1` is the translate by `x` of the unit strip
`[0,1)`, and `exp (2πi (v + x)) = exp (2πi v) · exp (2πi x)` is a constant nonzero
multiple of `exp (2πi v)`.  Hence existence is obtained by applying the unit-strip
representative theorem `exp_two_pi_I_strip_rep` to `z / exp (2πi x)`, while
uniqueness is the same kernel argument as in `exp_two_pi_I_strip_inj`.

This is the statement that lets a point of the model cylinder `ℂ/ℤ` be represented
by a concrete value of the Écalle coordinate lying in any prescribed slab — in
particular in the slab of the fundamental domain of the implosion, whose cut sits
at a prescribed transit phase `x = ecallePhase`.
-/
import Mathlib
import Submission.Work.Implosion.Basic
import Submission.Work.Implosion.Ecalle
import Submission.Work.Implosion.Cylinder
import Submission.Work.Implosion.Cylinder.exp_two_pi_I_strip_rep

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Implosion.Cylinder

open Complex

/-- **The slab `x ≤ Re u < x + 1` represents the cylinder.**  For every real `x`
and every nonzero complex number `z` there is exactly one `u` in the slab
`x ≤ Re u < x + 1` with `exp (2πi u) = z`.  Thus `u ↦ exp (2πi u)` restricts to a
bijection `slab x ≃ ℂ^*` for every `x`, i.e. every translate of the unit strip is
a fundamental domain for the cylinder projection. -/
theorem existsUnique_slab_rep (x : ℝ) (z : ℂ) (hz : z ≠ 0) :
    ∃! u : ℂ, u ∈ slab x ∧ Complex.exp (2 * Real.pi * I * u) = z := by
  -- The unit-strip representative of `z / exp (2πi x)` shifted by `x` will do.
  set c : ℂ := Complex.exp (2 * Real.pi * I * (x : ℂ)) with hc
  have hcne : c ≠ 0 := Complex.exp_ne_zero _
  have hwne : z / c ≠ 0 := div_ne_zero hz hcne
  obtain ⟨v, hv0, hv1, hve⟩ := exists_exp_two_pi_I_strip (z / c) hwne
  -- Shifting the unit strip by `x` multiplies the projection by the constant `c`.
  have hexpvx : Complex.exp (2 * Real.pi * I * (v + (x : ℂ))) = z := by
    rw [show 2 * (Real.pi : ℂ) * I * (v + (x : ℂ))
          = 2 * (Real.pi : ℂ) * I * v + 2 * (Real.pi : ℂ) * I * (x : ℂ) by ring,
      Complex.exp_add, hve, ← hc]
    exact div_mul_cancel₀ z hcne
  refine ⟨v + (x : ℂ), ⟨?_, hexpvx⟩, ?_⟩
  · -- `v + x` lies in the slab because `0 ≤ Re v < 1`.
    rw [mem_slab_iff, Complex.add_re, Complex.ofReal_re]
    exact ⟨by linarith, by linarith⟩
  · -- Uniqueness: two slab points with the same projection differ by an integer
    -- whose absolute value is `< 1`, hence by `0`.
    intro u hu
    obtain ⟨humem, hue⟩ := hu
    rw [mem_slab_iff] at humem
    have hexp : Complex.exp (2 * Real.pi * I * u)
        = Complex.exp (2 * Real.pi * I * (v + (x : ℂ))) := by
      rw [hue, hexpvx]
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp
    have hsub : u - (v + (x : ℂ)) = (n : ℂ) := by
      have h2 : (2 * (Real.pi : ℂ) * I) * (u - (v + (x : ℂ)))
          = (2 * (Real.pi : ℂ) * I) * (n : ℂ) := by
        rw [mul_sub, hn]; ring
      exact mul_left_cancel₀ Complex.two_pi_I_ne_zero h2
    have hre : u.re - (v + (x : ℂ)).re = (n : ℝ) := by
      have h := congrArg Complex.re hsub
      simpa using h
    have hvr : (v + (x : ℂ)).re = v.re + x := by simp
    have hn1 : (n : ℝ) < 1 := by linarith [humem.2, hvr, hv0]
    have hn2 : (-1 : ℝ) < (n : ℝ) := by linarith [humem.1, hvr, hv1]
    have hnz : n = 0 := by
      have h1 : n < 1 := by exact_mod_cast hn1
      have h2 : -1 < n := by exact_mod_cast hn2
      omega
    exact sub_eq_zero.mp (by rw [hsub, hnz]; simp)

end Work.Implosion.Cylinder
