import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.OpenPkg.QangOpen
import Submission.Work.FTS.H2.QangBox
import Submission.Work.FTS.H2.QangAux
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.EllipticEst.UopHk.hkMemDzPth_of_shifted
import Submission.Work.FTS.OpenPkg.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist

/-- The angular moment at level `k + 2` for `g` is the angular moment at level `k` for the
`D_z²`-shift `D_z²g`: `Qang g (k+2) = Qang (D_z²g) k`.  This is the identity which lets the
whole level-4 `z`-calculus of the angular moments be applied to `D_z²g` instead of `g`,
producing the level-6 statements about `g`. -/
theorem Qang_DzIter_two_shift (g : ℝ → ℝ → ℝ) (k : ℕ) :
    Work.Elliptic.Qang g (k + 2) = Work.Elliptic.Qang (Work.Spaces.DzIter 2 g) k := by
  funext z
  show (∫ θ in Work.Spaces.Iθ,
      Work.Elliptic.Ktheta θ * Work.Spaces.DzIter (k + 2) g z θ)
    = ∫ θ in Work.Spaces.Iθ,
      Work.Elliptic.Ktheta θ * Work.Spaces.DzIter k (Work.Spaces.DzIter 2 g) z θ
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
  rw [Work.Spaces.DzIter_add_right k 2 g]

theorem QangDiff6 {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hO : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α 6 g) :
    (∀ j : ℕ, j ≤ 4 → ∀ z : ℝ, 0 < z →
        HasDerivAt (fun w => Work.Elliptic.Qang g j w)
          (Work.Elliptic.Qang g (j + 1) z / z) z) ∧
      (∀ j : ℕ, j ≤ 5 → ContinuousOn (fun z => Work.Elliptic.Qang g j z) (Set.Ioi 0)) := by
  -- The two levels of honesty that the level-4 `z`-calculus of the angular moments consumes:
  -- `HkMem α 4 g` (for the moments of `g` itself) and `HkMem α 4 (D_z²g)` (for the moments of
  -- the shift, i.e. the moments of `g` at the two levels `4`, `5`).
  have hmem4 : Work.Spaces.HkMem α 4 g :=
    Work.FTS.OpenPkg.HkMem_mono_open hO 4 (by norm_num) hmem
  have hmem5₁ : Work.Spaces.HkMem α 5 (Work.Spaces.Dz g) :=
    Work.FTS.EllipticEst.UopHk.HkMem_Dz_of_smoothOpen α 5 hO hmem
  have hmem4₂ : Work.Spaces.HkMem α 4 (Work.Spaces.DzIter 2 g) := by
    have h : Work.Spaces.HkMem α 4 (Work.Spaces.Dz (Work.Spaces.Dz g)) :=
      Work.FTS.EllipticEst.UopHk.HkMem_Dz_of_smoothOpen α 4 hO.Dz hmem5₁
    simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero] using h
  have hO₂ : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.DzIter 2 g) := hO.DzIter 2
  -- the level-4 chain for `g`
  have hcont1 : ∀ j : ℕ, j ≤ 3 →
      ContinuousOn (fun z => Work.Elliptic.Qang g j z) (Set.Ioi 0) :=
    fun j hj => Work.FTS.OpenPkg.QangOpen.continuousOn_Qang_open α g hO hmem4 hj
  have hder1 : ∀ j : ℕ, j ≤ 2 → ∀ z : ℝ, 0 < z →
      HasDerivAt (fun w => Work.Elliptic.Qang g j w) (Work.Elliptic.Qang g (j + 1) z / z) z :=
    fun j hj z hz =>
      Work.FTS.OpenPkg.QangOpen.hasDerivAt_Qang_open α g hO hmem4 hj hz
        (hcont1 (j + 1) (by omega))
  -- the level-4 chain for the shift `D_z²g`
  have hcont2 : ∀ j : ℕ, j ≤ 3 →
      ContinuousOn (fun z => Work.Elliptic.Qang (Work.Spaces.DzIter 2 g) j z) (Set.Ioi 0) :=
    fun j hj => Work.FTS.OpenPkg.QangOpen.continuousOn_Qang_open α _ hO₂ hmem4₂ hj
  have hder2 : ∀ j : ℕ, j ≤ 2 → ∀ z : ℝ, 0 < z →
      HasDerivAt (fun w => Work.Elliptic.Qang (Work.Spaces.DzIter 2 g) j w)
        (Work.Elliptic.Qang (Work.Spaces.DzIter 2 g) (j + 1) z / z) z :=
    fun j hj z hz =>
      Work.FTS.OpenPkg.QangOpen.hasDerivAt_Qang_open α _ hO₂ hmem4₂ hj hz
        (hcont2 (j + 1) (by omega))
  refine ⟨?_, ?_⟩
  · intro j hj z hz
    rcases Nat.lt_or_ge j 3 with hlt | hge
    · exact hder1 j (by omega) z hz
    · obtain ⟨k, rfl⟩ : ∃ k, j = k + 2 := ⟨j - 2, by omega⟩
      have hk : k ≤ 2 := by omega
      have hfun : (fun w => Work.Elliptic.Qang g (k + 2) w)
          =ᶠ[nhds z] (fun w => Work.Elliptic.Qang (Work.Spaces.DzIter 2 g) k w) :=
        Filter.Eventually.of_forall (fun w => congrFun (Qang_DzIter_two_shift g k) w)
      have hval : Work.Elliptic.Qang g (k + 2 + 1) z / z
          = Work.Elliptic.Qang (Work.Spaces.DzIter 2 g) (k + 1) z / z := by
        rw [show k + 2 + 1 = (k + 1) + 2 from by omega,
          congrFun (Qang_DzIter_two_shift g (k + 1)) z]
      exact (hder2 k hk z hz).congr_of_eventuallyEq hfun |>.congr_deriv hval.symm
  · intro j hj
    rcases Nat.lt_or_ge j 4 with hlt | hge
    · exact hcont1 j (by omega)
    · obtain ⟨k, rfl⟩ : ∃ k, j = k + 2 := ⟨j - 2, by omega⟩
      have hk : k ≤ 3 := by omega
      refine (hcont2 k hk).congr (fun z _ => ?_)
      exact congrFun (Qang_DzIter_two_shift g k) z

end Work.FTS.StrongPersist
