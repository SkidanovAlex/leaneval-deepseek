import Mathlib
import Submission.Work.FatouDeg.Petal.DefsAux

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FatouDeg.Petal

/-- **The approximate Abel coordinate `Afun` is holomorphic on the right half-plane.**

`Afun m G z = (z ^ (m - 1))⁻¹ * (Ppoly m G).eval z + betac m G * Complex.log z`.  At a point `w`
with `0 < w.re` we have `w ≠ 0` (so `fun z ↦ (z ^ (m-1))⁻¹` is differentiable at `w`) and
`w ∈ Complex.slitPlane` (so `Complex.log` is differentiable at `w` there, see
`Complex.differentiableAt_log` and `Complex.mem_slitPlane_iff`); polynomial evaluation is
everywhere differentiable. -/
theorem afunDifferentiableAt (m : ℕ) (hm : 1 ≤ m) (G : Polynomial ℂ) {w : ℂ} (hw : 0 < w.re) :
    DifferentiableAt ℂ (Afun m G) w := by
  -- the right half-plane avoids the origin, so the inverse power is differentiable there
  have hw0 : w ≠ 0 := by
    intro h
    rw [h] at hw
    simp at hw
  have hpow_ne : w ^ (m - 1) ≠ 0 := pow_ne_zero _ hw0
  have hp : DifferentiableAt ℂ (fun z : ℂ => z ^ (m - 1)) w := differentiableAt_pow _
  have h1 : DifferentiableAt ℂ
      (fun z : ℂ => (z ^ (m - 1))⁻¹ * (Ppoly m G).eval z) w :=
    (hp.inv hpow_ne).mul (Polynomial.differentiableAt (Ppoly m G))
  -- and the right half-plane lies in the slit plane, where `log` is differentiable
  have hl : DifferentiableAt ℂ Complex.log w :=
    Complex.differentiableAt_log (by rw [Complex.mem_slitPlane_iff]; exact Or.inl hw)
  have h2 : DifferentiableAt ℂ (fun z : ℂ => betac m G * Complex.log z) w := hl.const_mul _
  have h3 := h1.add h2
  -- `Afun m G` is definitionally the sum of the two functions above
  convert h3 using 1
  ext z
  simp [Afun]

end Work.FatouDeg.Petal
