import Mathlib
import Submission.Work.Drive.Prelude
import Submission.Work.Drive.quadFamilyDefs

/-!
# Joint smoothness of the perturbation family

The correction `corr D c t` is smooth *jointly* in the coefficient vector `c` and the parameter
`t` (not only separately).  This is the input that lets the genericity arguments apply the
implicit-function-theorem dimension count to maps such as
`(c,w) ↦ patchA (curveData r c w)`.

The mechanism: the coordinate functionals `coefAtLin D i j : QCoeff D →L[ℝ] ℝ` are continuous
linear, the basis functions `scBase D j` are smooth, so

    corr D c t = WithLp.toLp 2 (fun i => ∑ j, coefAtLin D i j c * scBase D j t)

is a sum of products of (linear in `c`) and (smooth in `t`) terms, and `WithLp.toLp` is `C^⊤`
(`PiLp.contDiff_toLp`).  This mirrors `contDiff_pertV_joint` of `tangencyBadSet.lean` for the other
perturbation family.
-/

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

noncomputable section

/-- The coordinate functional `c ↦ c (cIdxEquiv D (i,j))` of the coefficient space, as a
continuous linear map. -/
def coefAtLin (D : ℕ) (i : Fin 3) (j : ScIdx D) : QCoeff D →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (cIdxEquiv D (i, j))).comp
    ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (3 * (2 * D + 1)) => ℝ)).toContinuousLinearMap)

lemma coefAtLin_apply (D : ℕ) (i : Fin 3) (j : ScIdx D) (c : QCoeff D) :
    coefAtLin D i j c = coefAt D c i j := by
  simp [coefAtLin, coefAt, ContinuousLinearMap.proj_apply]

/-- The correction as an explicit sum of basis functions times coordinate functionals. -/
lemma corr_eq_sum (D : ℕ) (c : QCoeff D) (t : ℝ) :
    corr D c t = WithLp.toLp 2 (fun i : Fin 3 =>
      ∑ j : ScIdx D, coefAtLin D i j c * scBase D j t) := by
  ext i
  simp [corr_apply, scFun, coefAtLin_apply, coefC_apply]

/-- The velocity of the correction in the same explicit form. -/
lemma corrD_eq_sum (D : ℕ) (c : QCoeff D) (t : ℝ) :
    corrD D c t = WithLp.toLp 2 (fun i : Fin 3 =>
      ∑ j : ScIdx D, coefAtLin D i j c * scBaseD D j t) := by
  ext i
  simp [corrD_apply, scFunD, coefAtLin_apply, coefC_apply]

/-- **Joint smoothness of the correction.** -/
lemma contDiff_corr_joint (D : ℕ) :
    ContDiff ℝ ⊤ (fun p : QCoeff D × ℝ => corr D p.1 p.2) := by
  have hfun : (fun p : QCoeff D × ℝ => corr D p.1 p.2)
      = fun p : QCoeff D × ℝ => WithLp.toLp 2 (fun i : Fin 3 =>
          ∑ j : ScIdx D, coefAtLin D i j p.1 * scBase D j p.2) := by
    funext p
    exact corr_eq_sum D p.1 p.2
  rw [hfun]
  refine PiLp.contDiff_toLp.comp ?_
  rw [contDiff_pi]
  intro i
  exact ContDiff.sum fun j _ =>
    ((coefAtLin D i j).contDiff.comp contDiff_fst).mul
      ((contDiff_scBase D j).comp contDiff_snd)

/-- **Joint smoothness of the velocity of the correction.** -/
lemma contDiff_corrD_joint (D : ℕ) :
    ContDiff ℝ ⊤ (fun p : QCoeff D × ℝ => corrD D p.1 p.2) := by
  have hfun : (fun p : QCoeff D × ℝ => corrD D p.1 p.2)
      = fun p : QCoeff D × ℝ => WithLp.toLp 2 (fun i : Fin 3 =>
          ∑ j : ScIdx D, coefAtLin D i j p.1 * scBaseD D j p.2) := by
    funext p
    exact corrD_eq_sum D p.1 p.2
  rw [hfun]
  refine PiLp.contDiff_toLp.comp ?_
  rw [contDiff_pi]
  intro i
  exact ContDiff.sum fun j _ =>
    ((coefAtLin D i j).contDiff.comp contDiff_fst).mul
      ((contDiff_scBaseD D j).comp contDiff_snd)

/-- **Joint smoothness of the perturbed curve** in `(c,t)`. -/
lemma contDiff_curve_joint {r : ℝ → Space} (hr : IsSmoothKnot r) (D : ℕ) :
    ContDiff ℝ ⊤ (fun p : QCoeff D × ℝ => curve r D p.1 p.2) := by
  have hfun : (fun p : QCoeff D × ℝ => curve r D p.1 p.2)
      = fun p : QCoeff D × ℝ => r p.2 + corr D p.1 p.2 := by
    funext p
    rfl
  rw [hfun]
  exact (hr.smooth.comp contDiff_snd).add (contDiff_corr_joint D)

/-- **Joint smoothness of the velocity of the perturbed curve** in `(c,t)`. -/
lemma contDiff_velCurve_joint {r : ℝ → Space} (hr : IsSmoothKnot r) (D : ℕ) :
    ContDiff ℝ ⊤ (fun p : QCoeff D × ℝ => velCurve r D p.1 p.2) := by
  have h1 : (⊤ : WithTop ℕ∞) + 1 = ⊤ := by simp
  have hvel0 : ContDiff ℝ ⊤ (deriv r) := by simpa only [h1] using hr.smooth.deriv'
  have hvel : ContDiff ℝ ⊤ (fun p : QCoeff D × ℝ => deriv r p.2) := hvel0.comp contDiff_snd
  have hfun : (fun p : QCoeff D × ℝ => velCurve r D p.1 p.2)
      = fun p : QCoeff D × ℝ => deriv r p.2 + corrD D p.1 p.2 := by
    funext p
    rfl
  rw [hfun]
  exact hvel.add (contDiff_corrD_joint D)


/-- The coordinate functional of `EuclideanSpace ℝ (Fin n)` as a continuous linear map.

Mathlib has no bridge from `ContinuousLinearMap.proj i` (a projection of the *Pi* type
`Fin n → ℝ`) to the `WithLp`-wrapped `EuclideanSpace ℝ (Fin n)`, so this composite is recorded once
and reused.  It is the `WithLp` analogue of `ContinuousLinearMap.proj`. -/
def euclidCoord {n : ℕ} (i : Fin n) : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp
    ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).toContinuousLinearMap)

@[simp] lemma euclidCoord_apply {n : ℕ} (i : Fin n) (x : EuclideanSpace ℝ (Fin n)) :
    euclidCoord i x = x i := by
  simp [euclidCoord, ContinuousLinearMap.proj_apply]

/-- The data (the three positions and the three velocities) of the perturbed curve at the
parameter triple `w`. -/
def curveData (r : ℝ → Space) (c : QCoeff 4) (w : ℝ × ℝ × ℝ) : TripleData :=
  (curve r 4 c w.1, curve r 4 c w.2.1, curve r 4 c w.2.2,
    velCurve r 4 c w.1, velCurve r 4 c w.2.1, velCurve r 4 c w.2.2)

/-- **Joint smoothness of the data of the perturbed curve** at a parameter triple. -/
theorem contDiff_curveData_joint {r : ℝ → Space} (hr : IsSmoothKnot r) :
    ContDiff ℝ 1 (fun p : QCoeff 4 × (ℝ × ℝ × ℝ) => curveData r p.1 p.2) := by
  have hc := contDiff_curve_joint hr 4
  have hv := contDiff_velCurve_joint hr 4
  have hA : ContDiff ℝ ⊤ (fun p : QCoeff 4 × (ℝ × ℝ × ℝ) => curve r 4 p.1 p.2.1) :=
    hc.comp (contDiff_fst.prodMk contDiff_snd.fst)
  have hB : ContDiff ℝ ⊤ (fun p : QCoeff 4 × (ℝ × ℝ × ℝ) => curve r 4 p.1 p.2.2.1) :=
    hc.comp (contDiff_fst.prodMk contDiff_snd.snd.fst)
  have hC : ContDiff ℝ ⊤ (fun p : QCoeff 4 × (ℝ × ℝ × ℝ) => curve r 4 p.1 p.2.2.2) :=
    hc.comp (contDiff_fst.prodMk contDiff_snd.snd.snd)
  have hD : ContDiff ℝ ⊤ (fun p : QCoeff 4 × (ℝ × ℝ × ℝ) => velCurve r 4 p.1 p.2.1) :=
    hv.comp (contDiff_fst.prodMk contDiff_snd.fst)
  have hE : ContDiff ℝ ⊤ (fun p : QCoeff 4 × (ℝ × ℝ × ℝ) => velCurve r 4 p.1 p.2.2.1) :=
    hv.comp (contDiff_fst.prodMk contDiff_snd.snd.fst)
  have hF : ContDiff ℝ ⊤ (fun p : QCoeff 4 × (ℝ × ℝ × ℝ) => velCurve r 4 p.1 p.2.2.2) :=
    hv.comp (contDiff_fst.prodMk contDiff_snd.snd.snd)
  exact (hA.prodMk (hB.prodMk (hC.prodMk (hD.prodMk (hE.prodMk hF))))).of_le le_top

end

end Work.Drive
