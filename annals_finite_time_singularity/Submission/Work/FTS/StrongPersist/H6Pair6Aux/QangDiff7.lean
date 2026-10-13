import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.OpenPkg.QangOpen
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.FTS.StrongPersist.QangDiff6
import Submission.Work.FTS.EllipticEst.UopHk.hkMemDzPth_of_shifted
import Submission.Work.Elliptic.L12Aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `QangDiff7` — the level-six `z`-differentiation of the angular moments

`Work.Elliptic.Qang g j z = ∫_θ Ktheta θ · (D_z^j g)(z,θ) dθ` is the `j`-th angular moment of
`g`.  The level-four chain (`Work.FTS.OpenPkg.QangOpen`) proves, for a datum which is `C^∞` on
the open quadrant and lies in `ℋ⁴`, the divided derivative

  `∂_z (Qang g j) z = Qang g (j+1) z / z`   (`z > 0`, `j ≤ 2`),

and `QangDiff6` pushes this to `j ≤ 4` for a datum in `ℋ⁶`, by transporting the level-four
chain to the shift `D_z²g` (using `Qang g (k+2) = Qang (D_z²g) k`).

Here we push one level further: for `g ∈ ℋ⁷` (and `C^∞` on the quadrant) the divided
derivative holds for `j ≤ 5`.  The extra level is obtained from the *first* shift, exactly as in
`Work.FTS.Nonlinear.Pieces.RNP.RNP24.fk_contDiffOn_four`: the level-six chain for `D_z g`
(available since `g ∈ ℋ⁷` gives `D_z g ∈ ℋ⁶` by `HkMem_Dz_of_smoothOpen`) yields

  `∂_z (Qang (D_z g) j) z = Qang (D_z g) (j+1) z / z`  for `j ≤ 4`,

which, after the identification `Qang (D_z g) k = Qang g (k+1)`, is precisely the statement for
`1 ≤ j ≤ 5`; the remaining case `j = 0` is the `j ≤ 4` instance of the chain for `g` itself.
-/

namespace Work.FTS.StrongPersist.H6Pair6Aux

/-- `D_z^i (D_z f) = D_z^{i+1} f`. -/
theorem DzIter_Dz_shift_one (i : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.DzIter i (Work.Spaces.Dz f) = Work.Spaces.DzIter (i + 1) f := by
  rw [Work.Spaces.DzIter_add_right]
  rfl

/-- The angular-moment tower shifts by one under `f ↦ D_z f`:
`Qang (D_z f) i = Qang f (i + 1)`. -/
theorem Qang_Dz_shift_one (f : ℝ → ℝ → ℝ) (i : ℕ) (z : ℝ) :
    Work.Elliptic.Qang (Work.Spaces.Dz f) i z = Work.Elliptic.Qang f (i + 1) z := by
  rw [Work.Elliptic.Qang, Work.Elliptic.Qang]
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => by
    rw [DzIter_Dz_shift_one i f])

theorem QangDiff7 {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hO : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α 7 g) :
    ∀ j : ℕ, j ≤ 5 → ∀ z : ℝ, 0 < z →
      HasDerivAt (fun w => Work.Elliptic.Qang g j w)
        (Work.Elliptic.Qang g (j + 1) z / z) z := by
  -- the two `ℋ⁶`-data which the level-six chain consumes: `g` itself and its shift `D_z g`
  have hmem6 : Work.Spaces.HkMem α 6 g :=
    Work.FTS.OpenPkg.HkMem_mono_open hO 6 (by norm_num) hmem
  have hmemDz : Work.Spaces.HkMem α 6 (Work.Spaces.Dz g) :=
    Work.FTS.EllipticEst.UopHk.HkMem_Dz_of_smoothOpen α 6 hO hmem
  have hOdz : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dz g) := hO.Dz
  -- the level-six divided derivatives for `g` (giving `j ≤ 4`) and for `D_z g` (giving the
  -- top level `j = 5` through the shift identification)
  have hderG : ∀ j : ℕ, j ≤ 4 → ∀ z : ℝ, 0 < z →
      HasDerivAt (fun w => Work.Elliptic.Qang g j w)
        (Work.Elliptic.Qang g (j + 1) z / z) z :=
    (Work.FTS.StrongPersist.QangDiff6 (α := α) hO hmem6).1
  have hderDz : ∀ j : ℕ, j ≤ 4 → ∀ z : ℝ, 0 < z →
      HasDerivAt (fun w => Work.Elliptic.Qang (Work.Spaces.Dz g) j w)
        (Work.Elliptic.Qang (Work.Spaces.Dz g) (j + 1) z / z) z :=
    (Work.FTS.StrongPersist.QangDiff6 (α := α) hOdz hmemDz).1
  intro j hj z hz
  rcases Nat.lt_or_ge j 5 with hlt | hge
  · exact hderG j (by omega) z hz
  · have hj5 : j = 5 := by omega
    subst hj5
    -- `Qang g 5 = Qang (D_z g) 4` and `Qang (D_z g) 5 = Qang g 6`
    have h' : HasDerivAt (fun w => Work.Elliptic.Qang g 5 w)
        (Work.Elliptic.Qang (Work.Spaces.Dz g) 5 z / z) z :=
      (hderDz 4 (by norm_num) z hz).congr_of_eventuallyEq
        (Filter.Eventually.of_forall (fun w => (Qang_Dz_shift_one g 4 w).symm))
    have hval : Work.Elliptic.Qang (Work.Spaces.Dz g) 5 z / z
        = Work.Elliptic.Qang g 6 z / z := by
      rw [Qang_Dz_shift_one g 5 z]
    rw [hval] at h'
    exact h'

end Work.FTS.StrongPersist.H6Pair6Aux
