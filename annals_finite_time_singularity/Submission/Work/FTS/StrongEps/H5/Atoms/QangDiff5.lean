import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.L12Aux
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.OpenPkg.QangOpen
import Submission.Work.FTS.EllipticEst.UopHk.hkMemDzPth_of_shifted
import Submission.Work.FTS.OpenPkg.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.H5.Atoms

/-- **The one-step index shift of the angular moments.**  Since `D_z = z ∂_z` raises the order of
the angular moment by one and `D_z^{k+1} = D_z^k ∘ D_z`, the `(k+1)`-st moment of `g` is the
`k`-th moment of `D_z g`:

  `Qang g (k+1) = Qang (D_z g) k`. -/
theorem Qang_DzIter_one_shift (g : ℝ → ℝ → ℝ) (k : ℕ) :
    Work.Elliptic.Qang g (k + 1) = Work.Elliptic.Qang (Work.Spaces.Dz g) k := by
  funext z
  show (∫ θ in Work.Spaces.Iθ,
      Work.Elliptic.Ktheta θ * Work.Spaces.DzIter (k + 1) g z θ)
    = ∫ θ in Work.Spaces.Iθ,
      Work.Elliptic.Ktheta θ * Work.Spaces.DzIter k (Work.Spaces.Dz g) z θ
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
  rw [Work.FTS.EllipticEst.UopHk.DzIter_Dz_eq k g]

/-- Level-`5` differentiation of the angular moments: `∂_z (Qang g j) = Qang g (j+1)/z` for `j ≤ 3`, and continuity for `j ≤ 4`. -/
theorem QangDiff5 {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hO : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α 5 g) :
    (∀ j : ℕ, j ≤ 3 → ∀ z : ℝ, 0 < z →
        HasDerivAt (fun w => Work.Elliptic.Qang g j w)
          (Work.Elliptic.Qang g (j + 1) z / z) z) ∧
      (∀ j : ℕ, j ≤ 4 → ContinuousOn (fun z => Work.Elliptic.Qang g j z) (Set.Ioi 0)) := by
  -- The two levels of honesty that the level-4 `z`-calculus of the angular moments consumes:
  -- `HkMem α 4 g` for the moments of `g` itself (levels `0`-`3`), and `HkMem α 4 (D_z g)` for
  -- the moments of the shift (`Qang g (k+1) = Qang (D_z g) k`), i.e. the levels `4` and `5` of
  -- `g`.
  have hmem4 : Work.Spaces.HkMem α 4 g :=
    Work.FTS.OpenPkg.HkMem_mono_open hO 4 (by norm_num) hmem
  have hmem4' : Work.Spaces.HkMem α 4 (Work.Spaces.Dz g) :=
    Work.FTS.EllipticEst.UopHk.HkMem_Dz_of_smoothOpen α 4 hO hmem
  have hO' : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dz g) := hO.Dz
  -- the level-4 chain for `g`
  have hcont1 : ∀ j : ℕ, j ≤ 3 →
      ContinuousOn (fun z => Work.Elliptic.Qang g j z) (Set.Ioi 0) :=
    fun j hj => Work.FTS.OpenPkg.QangOpen.continuousOn_Qang_open α g hO hmem4 hj
  have hder1 : ∀ j : ℕ, j ≤ 2 → ∀ z : ℝ, 0 < z →
      HasDerivAt (fun w => Work.Elliptic.Qang g j w) (Work.Elliptic.Qang g (j + 1) z / z) z :=
    fun j hj z hz =>
      Work.FTS.OpenPkg.QangOpen.hasDerivAt_Qang_open α g hO hmem4 hj hz
        (hcont1 (j + 1) (by omega))
  -- the level-4 chain for the shift `D_z g`
  have hcont2 : ∀ j : ℕ, j ≤ 3 →
      ContinuousOn (fun z => Work.Elliptic.Qang (Work.Spaces.Dz g) j z) (Set.Ioi 0) :=
    fun j hj => Work.FTS.OpenPkg.QangOpen.continuousOn_Qang_open α _ hO' hmem4' hj
  have hder2 : ∀ j : ℕ, j ≤ 2 → ∀ z : ℝ, 0 < z →
      HasDerivAt (fun w => Work.Elliptic.Qang (Work.Spaces.Dz g) j w)
        (Work.Elliptic.Qang (Work.Spaces.Dz g) (j + 1) z / z) z :=
    fun j hj z hz =>
      Work.FTS.OpenPkg.QangOpen.hasDerivAt_Qang_open α _ hO' hmem4' hj hz
        (hcont2 (j + 1) (by omega))
  refine ⟨?_, ?_⟩
  · intro j hj z hz
    rcases Nat.lt_or_ge j 3 with hlt | hge
    · exact hder1 j (by omega) z hz
    · obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
      have hk : k ≤ 2 := by omega
      have hfun : (fun w => Work.Elliptic.Qang g (k + 1) w)
          =ᶠ[𝓝 z] (fun w => Work.Elliptic.Qang (Work.Spaces.Dz g) k w) :=
        Filter.Eventually.of_forall (fun w => congrFun (Qang_DzIter_one_shift g k) w)
      have hval : Work.Elliptic.Qang g (k + 1 + 1) z / z
          = Work.Elliptic.Qang (Work.Spaces.Dz g) (k + 1) z / z := by
        rw [show k + 1 + 1 = (k + 1) + 1 from rfl,
          congrFun (Qang_DzIter_one_shift g (k + 1)) z]
      exact ((hder2 k hk z hz).congr_of_eventuallyEq hfun).congr_deriv hval.symm
  · intro j hj
    rcases Nat.lt_or_ge j 4 with hlt | hge
    · exact hcont1 j (by omega)
    · obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
      have hk : k ≤ 3 := by omega
      exact (hcont2 k hk).congr (fun z _ => congrFun (Qang_DzIter_one_shift g k) z)

end Work.FTS.StrongEps.H5.Atoms
