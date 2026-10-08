/-
# `Aut` of a Suzuki 2-group of order `q²` is solvable

Higman's classification identifies a Suzuki 2-group `P` with `|P| = |Z(P)|²` with a "type `A`"
group `A(n,θ)` (`θ ≠ 1` of odd order), and App. VIII Prop. 1 (Peterfalvi I p. 224) says
`Aut(A(n,φ))` is solvable whenever `φ⁴ ≠ 1`.  Since `θ` has odd order `≠ 1`, `θ⁴ ≠ 1`, so
`Aut(P)` is solvable.
-/

import Mathlib
import Submission.Work.Higman.Class
import Submission.Work.Hering.AppVIII.Defs
import Submission.Work.Hering.HardCore.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
namespace Work.Hering.HardCore

open LeanEval.GroupTheory.Defs

theorem q2_aut_solvable (hHig : Submission.Blueprint.HigmanProp) (hVIII1 : Work.Hering.AppVIIIProp1)
    {P : Type} [Group P] [Finite P] (hP : Work.Hering.IsSuzukiTwoGroup P)
    (hcard : Nat.card P = Nat.card ↥(Subgroup.center P) ^ 2) :
    Group.IsSolvable (MulAut P) := by
  obtain ⟨-, -, -, -, hA5⟩ := hHig P hP
  obtain ⟨n, e, θ, hZ, hθne, hθodd, hlaw⟩ := hA5 hcard
  have hθ4 : θ ^ 4 ≠ 1 := by
    intro h
    have hdvd : orderOf θ ∣ 4 := orderOf_dvd_iff_pow_eq_one.mpr h
    rcases hθodd with ⟨k, hk⟩
    have hle : 2 * k + 1 ≤ 4 := by rw [← hk]; exact Nat.le_of_dvd (by norm_num) hdvd
    have hk' : k = 0 ∨ k = 1 := by omega
    rcases hk' with h0 | h1
    · have : orderOf θ = 1 := by omega
      exact hθne (orderOf_eq_one_iff.mp this)
    · rw [hk, h1] at hdvd; norm_num at hdvd
  haveI : Group.IsSolvable (MulAut (Work.Higman.AType (GaloisField 2 n) θ)) := hVIII1 n θ hθ4
  have hφ : Group.IsSolvable (MulAut P) := by
    let toP := Work.Higman.TwoStep.toProd (b := Work.Higman.aCocycle (GaloisField 2 n) θ)
    let φ : P ≃* Work.Higman.AType (GaloisField 2 n) θ :=
      { toFun := fun x => toP.symm (e x)
        invFun := fun y => e.symm (toP y)
        left_inv := by intro x; simp [toP]
        right_inv := by intro y; simp [toP]
        map_mul' := by
          intro x y
          have h1 : (toP.symm (e (x * y))).fst = (e x).1 + (e y).1 := by
            show (e (x * y)).1 = (e x).1 + (e y).1
            rw [hlaw]
          have h2 : (toP.symm (e (x * y))).snd = (e x).2 + (e y).2 + (e x).1 * θ (e y).1 := by
            show (e (x * y)).2 = _
            rw [hlaw]
          apply Work.Higman.TwoStep.ext_iff
          · rw [Work.Higman.TwoStep.fst_mul, h1]; rfl
          · rw [Work.Higman.TwoStep.snd_mul, h2]; simp only [Work.Higman.aCocycle]; rfl }
    exact Group.isSolvable_of_surjective (f := (MulAut.congr φ).symm.toMonoidHom)
      (MulAut.congr φ).symm.surjective
  exact hφ

end Work.Hering.HardCore
