import Mathlib
import Submission.Work.KT.D2.Winding
import Submission.Work.KT.D2.windLoop_mul
import Submission.Work.KT.D2.blk_det_ne_zero

namespace Work.KT.D2

/-- **Gauge invariance of the winding of a loop of units at an idempotent.**  If the loop `γ'` is
obtained from `γ` by the boundary values of a disc-valued gauge `w` that commutes with `e` and is
invertible with two-sided inverse `w'` (`γ' x = w (inBall x) * γ x`), then the two windings at `e`
agree.

Route: `windLoop n e γ' = windLoop n e ((w ∘ inBall) * γ) = windLoop n e (w ∘ inBall) +
windLoop n e γ` by `Work.KT.D2.windLoop_mul` (the `Stab(e)` hypotheses come from `hw`).  The first
summand is `0`: `e * w y * e + (1 - e)` is invertible for every `y` on the disc (inverse
`e * w' y * e + (1 - e)`, using `w y * e = e * w y` and `w' y * e = e * w' y`, the latter following
from `w y * w' y = 1`, `w' y * w y = 1` and `w y * e = e * w y`), so its determinant extends over
the disc as a nowhere-zero continuous function and the boundary loop has winding `0`
(`Work.KT.D2.degNZ_comp_inBall`). -/
theorem windLoop_gauge (n : ℕ) (e : Matrix (Fin n) (Fin n) ℂ) (he : e * e = e)
    (γ γ' : C(Work.KT.Sph (EuclideanSpace ℝ (Fin 2)), Matrix (Fin n) (Fin n) ℂ))
    (hγ : ∀ x, γ x * e = e * γ x) (hγ' : ∀ x, γ' x * e = e * γ' x)
    (w : C(Work.KT.Ball (EuclideanSpace ℝ (Fin 2)), Matrix (Fin n) (Fin n) ℂ))
    (hw : ∀ y, w y * e = e * w y)
    (hwinv : ∃ w' : C(Work.KT.Ball (EuclideanSpace ℝ (Fin 2)), Matrix (Fin n) (Fin n) ℂ),
      (∀ y, w y * w' y = 1) ∧ (∀ y, w' y * w y = 1))
    (hgw : ∀ x, γ' x = w (Work.KT.D2.inBall x) * γ x)
    (h : ∀ x, Matrix.det (e * γ x * e + (1 - e)) ≠ 0)
    (h' : ∀ x, Matrix.det (e * γ' x * e + (1 - e)) ≠ 0) :
    Work.KT.D2.windLoop n e γ' h' = Work.KT.D2.windLoop n e γ h := by
  obtain ⟨w', hww', hw'w⟩ := hwinv
  -- The determinant of the gauge on the disc is nowhere zero.
  have hA : ∀ y : Ball (Euc 2), Matrix.det (e * w y * e + (1 - e)) ≠ 0 :=
    fun y => blk_det_ne_zero e (w y) (w' y) he (hw y) (hww' y) (hw'w y)
  -- The boundary values of the gauge.
  let wS : C(Sph (Euc 2), Matrix (Fin n) (Fin n) ℂ) := w.comp inBallCM
  have hwSx : ∀ x, wS x = w (inBall x) := fun x => rfl
  have hwS : ∀ x, wS x * e = e * wS x := fun x => by
    rw [hwSx x]; exact hw (inBall x)
  have hW : ∀ x, Matrix.det (e * wS x * e + (1 - e)) ≠ 0 := fun x => by
    rw [hwSx x]; exact hA (inBall x)
  have h2 : ∀ x, Matrix.det (e * (wS * γ) x * e + (1 - e)) ≠ 0 := by
    intro x
    have hx : (wS * γ) x = γ' x := by
      show wS x * γ x = γ' x
      rw [hwSx x, ← hgw x]
    rw [hx]
    exact h' x
  -- Step 1: `γ'` agrees pointwise with the product `(w ∘ inBall) * γ`.
  have hstep1 : windLoop n e γ' h' = windLoop n e (wS * γ) h2 := by
    have hfun : wlmDet n e γ' = wlmDet n e (wS * γ) := by
      apply ContinuousMap.ext
      intro x
      simp only [wlmDet_apply, ContinuousMap.mul_apply]
      rw [show γ' x = wS x * γ x by rw [hwSx x, hgw x]]
    calc windLoop n e γ' h' = degNZ (wlmDet n e γ') h' := windLoop_eq_degNZ n e γ' h'
      _ = degNZ (wlmDet n e (wS * γ)) h2 := wlmDegNZcongr hfun h' h2
      _ = windLoop n e (wS * γ) h2 := (windLoop_eq_degNZ n e (wS * γ) h2).symm
  -- Step 2: multiplicativity of the winding under the pointwise product.
  have hstep2 : windLoop n e (wS * γ) h2 = windLoop n e wS hW + windLoop n e γ h :=
    windLoop_mul n e he wS γ hwS hγ hW h h2
  -- Step 3: the winding of the gauge itself vanishes, being the boundary of a disc-valued loop.
  have hzero : windLoop n e wS hW = 0 := by
    let gA : C(Ball (Euc 2), ℂ) := ⟨fun y => Matrix.det (e * w y * e + (1 - e)), by
      have hcont : Continuous fun y : Ball (Euc 2) => e * w y * e + (1 - e) := by fun_prop
      exact hcont.matrix_det⟩
    have hgA : ∀ y, gA y ≠ 0 := fun y => hA y
    have hgAin : ∀ x, (gA.comp inBallCM) x ≠ 0 := fun x => hgA (inBall x)
    have hfun : wlmDet n e wS = gA.comp inBallCM := by
      apply ContinuousMap.ext
      intro x
      show Matrix.det (e * wS x * e + (1 - e)) = gA (inBall x)
      rw [hwSx x]
      rfl
    calc windLoop n e wS hW = degNZ (wlmDet n e wS) hW := windLoop_eq_degNZ n e wS hW
      _ = degNZ (gA.comp inBallCM) hgAin := wlmDegNZcongr hfun hW hgAin
      _ = 0 := degNZ_comp_inBall gA hgA
  calc windLoop n e γ' h' = windLoop n e (wS * γ) h2 := hstep1
    _ = windLoop n e wS hW + windLoop n e γ h := hstep2
    _ = 0 + windLoop n e γ h := by rw [hzero]
    _ = windLoop n e γ h := zero_add _

end Work.KT.D2
