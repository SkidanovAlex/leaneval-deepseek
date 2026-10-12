import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.l2Space
import Submission.Work.BoseBoxFock.KzOpC
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.split_N_slice` — the number row on the zero-condensate slice

The `thm:Kafz` dictionary transports operators on the mode lattice `RealFock m` into
the ⟨condensate | spectators⟩ picture `FockCore (cfock (Excited m))` through
`Work.BoseB4.split`.  For the total-number row, the hypothesis `hN` of the target says
that on every state

    `split (T.N y) = (monoOp 1 1 1 + monoOp 0 0 (nPlusC − 1)) (split y)`,

i.e. `N = n₀ + n₊` in the anti-normal (`monoOp`) shape, the `−1` being the vacuum
commutator `a₀a₀† = a₀†a₀ + 1` (`monoOp_11_00_numOp`).

On the **zero-condensate slice**, `split f0 = single 0 v`, only the `n₊` part survives:
`n₀` kills the slice, while the `(1,1)` slot `a₀a₀†` reproduces it exactly, cancelling
the `−1` of the `(0,0)` slot:

    `split (T.N f0) = single 0 (nPlusC v)`.

The whole content is the elementary computation of the helper
`monoOp_11_00_apply_single_zero` below, applied to `A = nPlusC`.
-/

noncomputable section

namespace Work.BoseBoxFock

open Work.BoseB4

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The anti-normal `(1,1) + (0,0)` pair on the zero-condensate slice.**
For any spectator operator `A`,

  `(monoOp 1 1 1 + monoOp 0 0 (A − 1)) (single 0 v) = single 0 (A v)`.

Indeed `monoOp 0 0 (A − 1) = lift (A − 1)`, giving `single 0 ((A − 1) v)`, while
`monoOp 1 1 1 = a₀a₀†` and `a₀†(single 0 v) = single 1 v`, `a₀(single 1 v) = single 0 v`
reproduce `single 0 v`; the two summands add up to `single 0 (v + (A v − v))` (the `−1`
slot cancels the `v` produced by `a₀a₀†`).  This is the `v`-level form of the identity
`monoOp 1 1 1 + monoOp 0 0 (A − 1) = numOp + lift A` (`hN_op_identity`) evaluated on the
slice killed by `numOp`. -/
lemma monoOp_11_00_apply_single_zero {m : ℕ} [NeZero m]
    (A : cfock (Excited m) →ₗ[ℂ] cfock (Excited m)) (v : cfock (Excited m)) :
    ((monoOp (E := cfock (Excited m)) 1 1
          (1 : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))
        + monoOp (E := cfock (Excited m)) 0 0 (A - 1)) (Finsupp.single 0 v)
      : FockCore (cfock (Excited m))) = Finsupp.single 0 (A v) := by
  rw [LinearMap.add_apply, monoOp_zero_zero, lift_single]
  have h11 : (monoOp (E := cfock (Excited m)) 1 1
        (1 : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))) (Finsupp.single 0 v)
      = Finsupp.single 0 v := by
    simp [monoOp, a0_single, a0d_single]
  rw [h11]
  simp

theorem split_N_slice {m : ℕ} [NeZero m] {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode] (B : Work.BoseB4.BoxData) {ℓ : ℝ} (kmom : Mode → EuclideanSpace ℝ (Fin 3))
    (hkmom : ∀ i : Mode, kmom (-i) = -kmom i) (f : Mode → Fin m → ℝ)
    (hf : ∀ i j : Mode, Work.BoseB4.gram (f i) (f j)
      = Work.BoseB7.ccrKernel ℓ B.hatChiSq B.hatChi (kmom i) (kmom j))
    (T : Work.BoseB7A.TildeData (Work.BoseB4.boxFockData B kmom hkmom m f hf))
    (hN : ∀ y : Work.BoseB4.RealFock m, Work.BoseB4.split (T.N y)
      = (Work.BoseB4.monoOp 1 1 (1 : Work.BoseB4.cfock (Work.BoseB4.Excited m) →ₗ[ℂ] Work.BoseB4.cfock (Work.BoseB4.Excited m))
          + Work.BoseB4.monoOp 0 0 ((Work.BoseBoxFock.nPlusC (m := m))
              - (1 : Work.BoseB4.cfock (Work.BoseB4.Excited m) →ₗ[ℂ] Work.BoseB4.cfock (Work.BoseB4.Excited m)))) (Work.BoseB4.split y))
    (f0 : Work.BoseB4.RealFock m) (v : Work.BoseB4.cfock (Work.BoseB4.Excited m))
    (hsp : Work.BoseB4.split f0 = Finsupp.single 0 v) :
    Work.BoseB4.split (T.N f0) = Finsupp.single 0 (Work.BoseBoxFock.nPlusC (m := m) v) := by
  rw [hN f0, hsp]
  exact monoOp_11_00_apply_single_zero (nPlusC (m := m)) v

end Work.BoseBoxFock
