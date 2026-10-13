/-
# `FK g` is `C⁴` on `(0,∞)` in the interior class `SmoothQuad`

The angular moment `FK g z = ∫_θ K(θ)·g z θ dθ` (`Work.Construction.FK`) is the radial function
`Qang g 0` of the elliptic chapter, where the *tower* of angular moments is

  `Qang g j z = ∫_θ K(θ)·D_z^j g z θ dθ`   (`Work.Elliptic.Qang`).

`Work.FTS.H2.QangDiff` proves, in the interior class `SmoothQuad g + HkMem α 4 g` (no analyticity:
a cut-off never satisfies `Work.Spaces.SmoothNbhd`),

  `HasDerivAt (Qang g j) (Qang g (j+1) z / z) z`   (`j ≤ 2`, `z > 0`),
  `ContinuousOn (Qang g j) (0,∞)`                  (`j ≤ 3`),

from the primitive identity `Qang g j z - Qang g j z₀ = ∫_{z₀}^{z} Qang g (j+1) x / x dx`.

The two facts missing for `C⁴` are `ContinuousOn (Qang g 4)` and
`HasDerivAt (Qang g 3) (Qang g 4 z / z) z`.  Both are exactly the level-shift of the two facts
already proved: the tower of `D_z g` is the tower of `g` raised by one,
`Qang (D_z g) i = Qang g (i+1)`, and `D_z g` is again `SmoothQuad` with `HkMem α 4 (D_z g)`
(as soon as `HkMem α 5 g`, which follows from `HkMem α 6 g`).  So a second instance of
`QangDiff`, for the datum `D_z g`, supplies the two missing levels:

* `ContinuousOn (Qang (D_z g) i) (0,∞)` for `i ≤ 3`, i.e. `ContinuousOn (Qang g j)` for `1 ≤ j ≤ 4`;
* `HasDerivAt (Qang (D_z g) i) (Qang (D_z g) (i+1) z / z) z` for `i ≤ 2`, i.e. the derivative
  relation for `Qang g j`, `1 ≤ j ≤ 3`.

The `C⁴`-statement then follows by the elementary tower induction
(`contDiffOn_Qang_tower`): `ContDiffOn ℝ (n+1) (Qang g j)` from `HasDerivAt` alone plus
`ContDiffOn ℝ n` of the derivative `z ↦ Qang g (j+1) z / z`, which is `ContDiffOn ℝ n` because
`Qang g (j+1)` is and `z ↦ 1/z` is smooth on `(0,∞)`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.Nonlinear.Pieces.Ctx
import Submission.Work.FTS.H2.QangDiff
import Submission.Work.FTS.H2.QangBox
import Submission.Work.FTS.EllipticEst.moment_relation
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.FTS.CoercivityFix.QuadPorts.RegQ_dz

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.RNP.RNP24

set_option autoImplicit false

/-! ## The shift `f ↦ D_z f` at the level of the tower -/

/-- `SmoothQuad` is closed under `D_z = z ∂_z` (`Work.FTS.LocData.contDiffOn_Dz`). -/
theorem smoothQuad_Dz {f : ℝ → ℝ → ℝ} (hf : Work.FTS.LocData.SmoothQuad f) :
    Work.FTS.LocData.SmoothQuad (Work.Spaces.Dz f) :=
  Work.FTS.LocData.contDiffOn_Dz Work.Spaces.isOpen_quadU hf

/-- `D_z^i (D_z f) = D_z^{i+1} f`. -/
theorem DzIter_Dz_shift (i : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.DzIter i (Work.Spaces.Dz f) = Work.Spaces.DzIter (i + 1) f := by
  rw [Work.Spaces.DzIter_add_right]
  rfl

/-- The angular-moment tower is shifted by one under `f ↦ D_z f`:
`Qang (D_z f) i = Qang f (i+1)`. -/
theorem Qang_Dz_shift (f : ℝ → ℝ → ℝ) (i : ℕ) (z : ℝ) :
    Work.Elliptic.Qang (Work.Spaces.Dz f) i z = Work.Elliptic.Qang f (i + 1) z := by
  rw [Work.Elliptic.Qang, Work.Elliptic.Qang]
  exact setIntegral_congr_fun measurableSet_Icc (fun θ _ => by rw [DzIter_Dz_shift i f])

/-! ## The differentiation tower -/

/-- **The tower of angular moments is `C⁴` on `(0,∞)`.**  If `Qang g j` has derivative
`Qang g (j+1) z / z` at every `z > 0` for `j ≤ 3`, and is continuous on `(0,∞)` for `j ≤ 4`,
then `Qang g 0` is `C⁴` on `(0,∞)`.

Induction on the order `n`: `ContDiffOn ℝ (n+1) (Qang g j)` is
`DifferentiableOn (Qang g j) ∧ ContDiffOn ℝ n (deriv (Qang g j))`
(`contDiffOn_succ_iff_deriv_of_isOpen`); the derivative is `Qang g (j+1) / id`, `C^n` by the
induction hypothesis since `z ↦ 1/z` is smooth on `(0,∞)` and `ContDiffOn.div` applies. -/
theorem contDiffOn_Qang_tower {g : ℝ → ℝ → ℝ}
    (hderiv : ∀ j : ℕ, j ≤ 3 → ∀ z : ℝ, 0 < z →
      HasDerivAt (fun z => Work.Elliptic.Qang g j z) (Work.Elliptic.Qang g (j + 1) z / z) z)
    (hcont : ∀ j : ℕ, j ≤ 4 →
      ContinuousOn (fun z => Work.Elliptic.Qang g j z) (Set.Ioi (0 : ℝ))) :
    ContDiffOn ℝ 4 (fun z => Work.Elliptic.Qang g 0 z) (Set.Ioi (0 : ℝ)) := by
  have htower : ∀ (n j : ℕ), j + n ≤ 4 →
      ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞) (fun z => Work.Elliptic.Qang g j z)
        (Set.Ioi (0 : ℝ)) := by
    intro n
    induction n with
    | zero =>
        intro j hj
        exact (contDiffOn_zero (𝕜 := ℝ)).2 (hcont j (by omega))
    | succ n ih =>
        intro j hj
        have hj3 : j ≤ 3 := by omega
        rw [show (((Nat.succ n : ℕ)) : WithTop ℕ∞) = ((n : ℕ) : WithTop ℕ∞) + 1 from by
          push_cast; ring]
        refine (contDiffOn_succ_iff_deriv_of_isOpen (𝕜 := ℝ)
          (n := ((n : ℕ) : WithTop ℕ∞)) (f := fun z => Work.Elliptic.Qang g j z)
          (s := Set.Ioi (0 : ℝ)) isOpen_Ioi).2 ⟨?_, ?_, ?_⟩
        · intro z hz
          exact (hderiv j hj3 z hz).differentiableAt.differentiableWithinAt
        · intro h
          exact absurd h (by simp)
        · refine ((ih (j + 1) (by omega)).div contDiffOn_id (fun z hz => ne_of_gt hz)).congr
            (fun z hz => ?_)
          exact (hderiv j hj3 z hz).deriv
  exact htower 4 0 (by norm_num)

/-! ## The target -/

theorem fk_contDiffOn_four {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hsm : Work.FTS.LocData.SmoothQuad g)
    (hmem : Work.Spaces.HkMem α 6 g) :
    ContDiffOn ℝ 4 (fun z => Work.Construction.FK g z) (Set.Ioi (0:ℝ)) := by
  -- ## Step 1: the shifted datum `D_z g` and the `ℋ^k`-levels it requires
  have hsmDz : Work.FTS.LocData.SmoothQuad (Work.Spaces.Dz g) := smoothQuad_Dz hsm
  have hmem5 : Work.Spaces.HkMem α 5 g := Work.GalerkinFix.RegQ.HkMem_mono_Q hsm hmem
  have hmem4 : Work.Spaces.HkMem α 4 g := Work.GalerkinFix.RegQ.HkMem_mono_Q hsm hmem5
  have hmemDz : Work.Spaces.HkMem α 4 (Work.Spaces.Dz g) :=
    Work.FTS.CoercivityFix.QuadPorts.HkMem_Dz_quad α 4 hsm hmem5
  -- ## Step 2: the tower relations, from `QangDiff g` and from `QangDiff (D_z g)`
  obtain ⟨hderivG, hcontG⟩ := Work.FTS.H2.QangDiff α g hα hα1 hsm hmem4
  obtain ⟨hderivDz, hcontDz⟩ :=
    Work.FTS.H2.QangDiff α (Work.Spaces.Dz g) hα hα1 hsmDz hmemDz
  have hcont : ∀ j : ℕ, j ≤ 4 →
      ContinuousOn (fun z => Work.Elliptic.Qang g j z) (Set.Ioi (0 : ℝ)) := by
    intro j hj
    rcases lt_or_ge j 4 with hlt | hge
    · exact hcontG j (by omega)
    · have hj4 : j = 4 := by omega
      subst hj4
      refine (hcontDz 3 (by norm_num)).congr (fun z _ => ?_)
      exact (Qang_Dz_shift g 3 z).symm
  have hderiv : ∀ j : ℕ, j ≤ 3 → ∀ z : ℝ, 0 < z →
      HasDerivAt (fun z => Work.Elliptic.Qang g j z)
        (Work.Elliptic.Qang g (j + 1) z / z) z := by
    intro j hj z hz
    rcases lt_or_ge j 3 with hlt | hge
    · exact hderivG j (by omega) z hz
    · have hj3 : j = 3 := by omega
      subst hj3
      have h' : HasDerivAt (fun z => Work.Elliptic.Qang g 3 z)
          (Work.Elliptic.Qang (Work.Spaces.Dz g) 3 z / z) z :=
        (hderivDz 2 (by norm_num) z hz).congr_of_eventuallyEq
          (Eventually.of_forall (fun w => (Qang_Dz_shift g 2 w).symm))
      have hval : Work.Elliptic.Qang (Work.Spaces.Dz g) 3 z / z
          = Work.Elliptic.Qang g 4 z / z := by
        rw [Qang_Dz_shift g 3 z]
      rw [hval] at h'
      exact h'
  -- ## Step 3: the tower, and the identification `FK g = Qang g 0`
  have hQ : ContDiffOn ℝ 4 (fun z => Work.Elliptic.Qang g 0 z) (Set.Ioi (0 : ℝ)) :=
    contDiffOn_Qang_tower hderiv hcont
  refine hQ.congr (fun z _ => ?_)
  rw [Work.Construction.FK, Work.Elliptic.Qang, Work.Spaces.DzIter_zero]
  refine setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
  rw [Work.Elliptic.Ktheta_eq_K]
  ring

end Work.FTS.Nonlinear.Pieces.RNP.RNP24
