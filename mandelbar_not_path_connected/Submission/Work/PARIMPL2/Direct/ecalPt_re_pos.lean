/-
Copyright: subproject `Submission/Work/PARIMPL2/` of `mandelbar_not_path_connected`.

# Positivity of the real part of the Écalle point on the principal strip

For the Écalle point map `ζ(u) = a·(e^{2au}+1)/(e^{2au}−1) = a·coth(a u)` of
`Submission/Work/Implosion/Ecalle.lean`, specialised to the purely imaginary
parameter `a = iλ` (`λ > 0`) of the Mandelbar/tricorn implosion, the real part is
strictly positive on the principal strip

  `u ∈ {0 < Re u < π/(2λ)}`.

This is the region between the puncture at `u = 0` and the cut at `Re u = π/(2λ)`
(exactly the strip on which `ζ` is used as the "Ecalle point" coordinate of the
incoming petal).

The proof is a direct computation.  With `θ = λ·Re u` and `η = λ·Im u` we have
`2au = 2iλu = −2η + 2θi`, so

  `E := e^{2au} = e^{−2η}·(cos 2θ + i·sin 2θ)`,

and hence `E.im = e^{−2η} sin 2θ > 0`, which shows `E ≠ 1` (so that `ζ` is
finite on the strip).  Writing `ζ = a·(E+1)/(E−1)` and using

  `Re(z/w) = (z.re·w.re + z.im·w.im)/‖w‖²`,

a two-line algebraic computation gives the explicit formula

  `Re ζ(u) = 2λ·E.im / ‖E − 1‖² = 2λ e^{−2η} sin(2θ) / ‖E − 1‖²`,

which is manifestly positive because `λ > 0`, `sin(2θ) > 0` (as `0 < θ < π/2`)
and `E − 1 ≠ 0`.
-/
import Mathlib
import Submission.Work.Implosion.All

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.PARIMPL2.Direct

open Complex

theorem ecalPt_re_pos (lam : ℝ) (hlam : 0 < lam) (u : ℂ)
    (h1 : 0 < u.re) (h2 : u.re < Real.pi / (2 * lam)) :
    0 < (Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u).re := by
  set a : ℂ := (lam : ℂ) * Complex.I with ha
  set θ : ℝ := lam * u.re with hθdef
  set η : ℝ := lam * u.im with hηdef
  -- `0 < θ < π/2`
  have hθpos : 0 < θ := by rw [hθdef]; exact mul_pos hlam h1
  have hθlt : θ < Real.pi / 2 := by
    have hlt : lam * u.re < lam * (Real.pi / (2 * lam)) := mul_lt_mul_of_pos_left h2 hlam
    have heq : lam * (Real.pi / (2 * lam)) = Real.pi / 2 := by
      field_simp
    rw [← hθdef, heq] at hlt
    exact hlt
  -- `sin (2θ) > 0`
  have hs2 : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  -- real and imaginary parts of the exponent `2 a u`
  have hre : (2 * a * u).re = -2 * η := by
    rw [ha, hηdef]
    simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    ring
  have him : (2 * a * u).im = 2 * θ := by
    rw [ha, hθdef]
    simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    ring
  set E : ℂ := Work.Implosion.ecalE a u with hEdef
  have hE : E = Complex.exp (2 * a * u) := by rw [hEdef]; rfl
  -- the exponential in explicit form
  have hEim : E.im = Real.exp (-2 * η) * Real.sin (2 * θ) := by
    rw [hE, Complex.exp_im, hre, him]
  have hEimpos : 0 < E.im := by
    rw [hEim]; exact mul_pos (Real.exp_pos _) hs2
  -- `E ≠ 1`, hence `E - 1 ≠ 0`
  have hDne : E - 1 ≠ 0 := by
    intro hh
    have h0 : (E - 1).im = 0 := by rw [hh]; simp
    simp only [Complex.sub_im, Complex.one_im] at h0
    linarith [hEimpos]
  have hnorm : 0 < Complex.normSq (E - 1) := Complex.normSq_pos.mpr hDne
  -- real and imaginary parts of the numerator `a * (E + 1)`
  have hNre : (a * (E + 1)).re = -lam * E.im := by
    rw [ha]
    simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  have hNim : (a * (E + 1)).im = lam * (E.re + 1) := by
    rw [ha]
    simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  have hDre : (E - 1).re = E.re - 1 := by simp
  have hDim : (E - 1).im = E.im := by simp
  -- the closed form for the real part
  have hmain : (Work.Implosion.ecalPt a u).re
      = 2 * lam * E.im / Complex.normSq (E - 1) := by
    rw [Work.Implosion.ecalPt, ← hEdef]
    rw [Complex.div_re, hNre, hNim, hDre, hDim]
    ring
  rw [hmain]
  exact div_pos (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hlam) hEimpos) hnorm

end Work.PARIMPL2.Direct
