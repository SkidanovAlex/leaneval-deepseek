import Mathlib.Algebra.Order.Ring.Star
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.L12Aux
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.OpenPkg.QangOpen
import Submission.Work.FTS.StrongPersist.QangAe6
import Submission.Work.FTS.EllipticEst.UopHk.hkMemDzPth_of_shifted

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

namespace Work.FTS.StrongEps.H5.Atoms

open MeasureTheory

/-- The level-`k+1` angular moment of `g` is the level-`k` angular moment of the radial shift
`D_z g`: `Qang g (k+1) = Qang (D_z g) k`.  This is the shift-by-one companion of
`Work.FTS.StrongPersist.Qang_DzIter_two_shift`, and it is what lets the level-four `z`-calculus of
the angular moments reach level five. -/
theorem Qang_DzIter_one_shift (g : ℝ → ℝ → ℝ) (k : ℕ) :
    Work.Elliptic.Qang g (k + 1) = Work.Elliptic.Qang (Work.Spaces.Dz g) k := by
  funext z
  show (∫ θ in Work.Spaces.Iθ,
      Work.Elliptic.Ktheta θ * Work.Spaces.DzIter (k + 1) g z θ)
    = ∫ θ in Work.Spaces.Iθ,
      Work.Elliptic.Ktheta θ * Work.Spaces.DzIter k (Work.Spaces.Dz g) z θ
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
  rw [Work.Spaces.DzIter_add_right k 1 g]
  simp only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero]

/-- Level-`5` a.e. identity for the iterates of the zeroth angular moment. -/
theorem QangAe5 {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hO : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α 5 g) :
    ∀ᵐ z ∂(MeasureTheory.volume), 0 < z → ∀ i ∈ Finset.range 6,
      Work.Elliptic.DzdIter i (fun z => Work.Elliptic.Qang g 0 z) z = Work.Elliptic.Qang g i z := by
  -- the level-four integrability the `z`-calculus of the moments consumes
  have hmem4 : Work.Spaces.HkMem α 4 g :=
    Work.FTS.OpenPkg.HkMem_mono_open hO 4 (by norm_num) hmem
  -- and its radial shift, which together with the level-four chain reaches level five
  have hmem4' : Work.Spaces.HkMem α 4 (Work.Spaces.Dz g) :=
    Work.FTS.EllipticEst.UopHk.HkMem_Dz_of_smoothOpen α 4 hO hmem
  have hO' : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dz g) := hO.Dz
  -- the a.e. level-four identities, for `g` and for its `D_z`-shift
  have hA := Work.FTS.OpenPkg.QangOpen.DzdIter_Qang_ae_open hO hmem4
  have hB := Work.FTS.OpenPkg.QangOpen.DzdIter_Qang_ae_open hO' hmem4'
  -- the *pointwise* identity at the levels `i ≤ 3`: the divided derivatives of the moments are
  -- pointwise (`hasDerivAt_Qang_open`), so no measure theory is involved below level four
  have hp3 : ∀ i ≤ 3, ∀ z : ℝ, 0 < z →
      Work.Elliptic.DzdIter i (fun z => Work.Elliptic.Qang g 0 z) z = Work.Elliptic.Qang g i z :=
    Work.FTS.StrongPersist.DzdIter_eq_of_hasDerivAt'
      (u := fun z => Work.Elliptic.Qang g 0 z)
      (Φ := fun j => fun z => Work.Elliptic.Qang g j z) 2
      (fun _ => rfl)
      (fun j hj z hz =>
        Work.FTS.OpenPkg.QangOpen.hasDerivAt_Qang_open α g hO hmem4 (j := j) (by omega) hz
          (Work.FTS.OpenPkg.QangOpen.continuousOn_Qang_open α g hO hmem4 (j := j + 1) (by omega)))
  filter_upwards [hA, hB] with z hzA hzB
  intro hzpos i hi
  rcases Nat.lt_or_ge i 5 with hlt | hge
  · exact hzA hzpos i (Finset.mem_range.mpr hlt)
  · have hieq : i = 5 := by
      have := Finset.mem_range.mp hi
      omega
    subst hieq
    -- `D_z⁵(Qang g 0) = D_z⁴(Qang g 1)` (pointwise identity at level one)
    -- `= D_z⁴(Qang (D_z g) 0)` (the shift identity), which the level-four chain of `D_z g` turns
    -- into `Qang (D_z g) 4 = Qang g 5`.
    calc Work.Elliptic.DzdIter 5 (fun z => Work.Elliptic.Qang g 0 z) z
        = Work.Elliptic.DzdIter (4 + 1) (fun z => Work.Elliptic.Qang g 0 z) z := rfl
      _ = Work.Elliptic.DzdIter 4
            (Work.Elliptic.DzdIter 1 (fun z => Work.Elliptic.Qang g 0 z)) z :=
          congrFun (Work.FTS.StrongPersist.DzdIter_add 4 1
            (fun z => Work.Elliptic.Qang g 0 z)) z
      _ = Work.Elliptic.DzdIter 4 (fun z => Work.Elliptic.Qang g 1 z) z :=
          Work.FTS.StrongPersist.DzdIter_congr_Ioi
            (fun y hy => hp3 1 (by norm_num) y hy) 4 z hzpos
      _ = Work.Elliptic.DzdIter 4 (fun z => Work.Elliptic.Qang (Work.Spaces.Dz g) 0 z) z :=
          Work.FTS.StrongPersist.DzdIter_congr_Ioi
            (fun y _ => congrFun (Qang_DzIter_one_shift g 0) y) 4 z hzpos
      _ = Work.Elliptic.Qang (Work.Spaces.Dz g) 4 z := hzB hzpos 4 (by decide)
      _ = Work.Elliptic.Qang g 5 z := (congrFun (Qang_DzIter_one_shift g 4) z).symm

end Work.FTS.StrongEps.H5.Atoms
