import Mathlib.Algebra.Algebra.Basic
import Mathlib.Data.Real.Basic
import Submission.Work.BoseBoxFock.Defs
import Submission.Work.BoseBoxFock.window_a_pair_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBoxFock.KzWindowGeDagPair`

**The double-creation pair bound on the `n₊`-window**: for a window state `g`
(`T.NWindow M g`, FS `eq:LocalizedAftercNumber`) and under the Bessel/number
hypothesis `Σ_k a_k†a_k ≤ Cn·n₊`,

  `|⟨a_k† a_l† g, g⟩| ≤ Cn (M+1) ‖g‖²`.

## The argument

There is nothing new to prove: the double-creation form is *equal* to the
double-annihilation form of `window_a_pair_le` with the two modes interchanged,
by the two adjoint identities plus symmetry of the Fock form,

`⟨a_k† (a_l† g), g⟩ = ⟨a_l† g, a_k g⟩ = ⟨g, a_l (a_k g)⟩ = ⟨a_l (a_k g), g⟩`,

and `window_a_pair_le` (already proved in this subproject) bounds the
right-hand side by `Cn (M+1) ‖g‖²` for *arbitrary* modes — in particular for the
pair `(l, k)`.

This is exactly the reduction used inside
`Submission/Work/BoseBoxFock/qw_KzBogFS_window_ge.lean` (`hpair'`), recorded here
as a standalone interface lemma.
-/

namespace Work.BoseBoxFock

theorem KzWindowGeDagPair {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (T : Work.BoseB7A.TildeData F) (Cn : ℝ) (hCn0 : 0 ≤ Cn)
    (hBessel : ∀ f : F.H, F.bp ((∑ k : Mode, F.nOp k) f) f ≤ Cn * F.bp (T.N f) f)
    {M : ℝ} (hM : 0 ≤ M) {g : F.H} (hg : T.NWindow M g) (k l : Mode) :
    |F.bp (F.aDag k (F.aDag l g)) g| ≤ Cn * (M + 1) * F.normSq g := by
  -- The double-creation form is the double-annihilation form with `(k,l) ↦ (l,k)`.
  have hred : F.bp (F.aDag k (F.aDag l g)) g = F.bp (F.a l (F.a k g)) g := by
    calc F.bp (F.aDag k (F.aDag l g)) g
        = F.bp (F.aDag l g) (F.a k g) := F.aDag_adjoint k (F.aDag l g) g
      _ = F.bp g (F.a l (F.a k g)) := F.aDag_adjoint l g (F.a k g)
      _ = F.bp (F.a l (F.a k g)) g := F.bp_symm g (F.a l (F.a k g))
  rw [hred]
  exact window_a_pair_le F T Cn hCn0 hBessel hM hg l k

end Work.BoseBoxFock
