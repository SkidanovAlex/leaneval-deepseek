import Mathlib
import Submission.Work.FatouParabolic2.AffineConj
import Submission.Work.FatouParabolic2.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FatouParabolic2

/-- One step of the intertwining: on the ball where `f` and `F` are conjugate by the affine chart,
`aff z₀ lam (f v) = F (aff z₀ lam v)`. -/
theorem aff_conj_step {f F : ℂ → ℂ} {z₀ lam : ℂ} {r : ℝ}
    (hlam : lam ≠ 0)
    (hconj : ∀ u : ℂ, u ∈ Metric.ball 0 r → f u = (F (z₀ + lam * u) - z₀) / lam)
    {v : ℂ} (hv : v ∈ Metric.ball 0 r) :
    aff z₀ lam (f v) = F (aff z₀ lam v) := by
  rw [hconj v hv, aff_apply, aff_apply]
  field_simp
  ring

/-- **Iterate conjugacy along an affine chart.**  If `f` and `F` are related on the ball
`Metric.ball 0 r` by `f u = (F (z₀ + lam * u) - z₀) / lam` (`lam ≠ 0`), and `A` is a
forward-invariant set contained in that ball, then the affine chart `aff z₀ lam` intertwines the
iterates of `f` on `A` with those of `F`. -/
theorem aff_iterate_conj {f F : ℂ → ℂ} {z₀ lam : ℂ} {r : ℝ} {A : Set ℂ}
    (hlam : lam ≠ 0) (hA : A ⊆ Metric.ball 0 r)
    (hconj : ∀ u : ℂ, u ∈ Metric.ball 0 r → f u = (F (z₀ + lam * u) - z₀) / lam)
    (hmap : Set.MapsTo f A A) {u : ℂ} (hu : u ∈ A) (n : ℕ) :
    F^[n] (aff z₀ lam u) = aff z₀ lam (f^[n] u) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply' F n, Function.iterate_succ_apply' f n, ih]
    exact (aff_conj_step hlam hconj (hA (hmap.iterate n hu))).symm

end Work.FatouParabolic2
