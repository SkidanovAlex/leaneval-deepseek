import Mathlib
import Submission.Work.RatHurewicz.PinchGeom

/-!
# The pinch geometry of the cube boundary

`Work.RatHurewicz.geomPinch` collects the four properties of the pinch pair
`iota : I^m → ∂I^{m+1}` (`PinchGeom.iota`, the inclusion of the complement of the open bottom
face) and `psiBd : ∂I^{m+1} → I^m` (`PinchGeom.psiBd`, the inverse of `iota` there, extended to
the bottom face):

* `psiBd ∘ iota = id`;
* `iota` sends `∂I^m` into the bottom face `{z_last = 0}`;
* `iota ∘ psiBd = id` off the bottom face;
* on the "rim" of the bottom face (`z_last = 0` and a further coordinate in `{0,1}`), `psiBd z`
  lies on `∂I^m`.
-/

open scoped unitInterval Topology
open Work.Stems.Cubical

namespace Work.RatHurewicz

noncomputable section

theorem geomPinch (m : ℕ) (hm : 1 ≤ m) :
    (psiBd m).comp (iota m hm) = ContinuousMap.id (IC m) ∧
    (∀ u : IC m, u ∈ Cube.boundary (Fin m) →
      ((iota m hm u : ↥(Cube.boundary (Fin (m + 1)))) : IC (m + 1)) (Fin.last m) = 0) ∧
    (∀ z : ↥(Cube.boundary (Fin (m + 1))), (z : IC (m + 1)) (Fin.last m) ≠ 0 →
      iota m hm (psiBd m z) = z) ∧
    (∀ z : ↥(Cube.boundary (Fin (m + 1))), (z : IC (m + 1)) (Fin.last m) = 0 →
      (∃ j : Fin m, (z : IC (m + 1)) (Fin.castSucc j) = 0 ∨
        (z : IC (m + 1)) (Fin.castSucc j) = 1) →
      psiBd m z ∈ Cube.boundary (Fin m)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext u i
    exact congrArg Subtype.val (congrFun (psiFun_iotaFun m hm u) i)
  · intro u hu
    show ((iota m hm u : ↥(Cube.boundary (Fin (m + 1)))) : IC (m + 1)) (Fin.last m) = 0
    rw [iota_coe, iotaFun_last]
    apply Subtype.ext
    show tauR m hm u = (0 : ℝ)
    rw [tauR, (sig_eq_one_iff m hm u).mpr hu]
    norm_num
  · intro z hz
    apply Subtype.ext
    funext j
    cases j using Fin.lastCases with
    | last =>
      show iotaFun m hm (psiFun m z.1) (Fin.last m) = z.1 (Fin.last m)
      rw [iotaFun_last]
      apply Subtype.ext
      exact tauR_psiFun m hm z.2 hz
    | cast i =>
      show iotaFun m hm (psiFun m z.1) (Fin.castSucc i) = z.1 (Fin.castSucc i)
      rw [iotaFun_castSucc]
      apply Subtype.ext
      exact radialR_psiFun m hm z.2 hz i
  · intro z hz hw
    obtain ⟨j, hj⟩ := hw
    refine ⟨j, ?_⟩
    have hz0 : ((z.1 (Fin.last m) : unitInterval) : ℝ) = 0 := congrArg Subtype.val hz
    have hcomp : (psiFun m z.1) j = z.1 (Fin.castSucc j) := by
      apply Subtype.ext
      have hval : (((psiFun m z.1) j : unitInterval) : ℝ)
          = 1/2 + (1 - ((z.1 (Fin.last m) : unitInterval) : ℝ)/2) *
              ((((z.1 (Fin.castSucc j)) : unitInterval) : ℝ) - 1/2) := rfl
      rw [hval, hz0]
      ring
    rw [psiBd_apply, hcomp]
    rcases hj with h | h
    · exact Or.inl h
    · exact Or.inr h

end

end Work.RatHurewicz
