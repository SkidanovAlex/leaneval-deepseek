/-
# The explicit jet is the jet of the Fourier series

For a coefficient family `a` supported on the box, the Fourier series `seriesFunM (toCoeff a)` is a
finite sum of characters, and its spatial `2`-jet is the explicit jet `jetExp a` of
`Work.Diff.STE.Flat.Galerkin`.  This identification is what lets the smoothness and Lipschitz
estimates on `jetExp` be transported to the Galerkin right-hand side.
-/
import Mathlib
import Submission.Work.Diff.STE.FlatPDE
import Submission.Work.Diff.STE.flat.GalerkinDefs
import Submission.Work.Diff.STE.flat.GalerkinSmooth
import Submission.Work.Diff.STE.flat.seriesFunM_eq_sum

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE

namespace Flat

namespace Galerkin

noncomputable section

open scoped BigOperators

/-- The Fourier series of a box-supported coefficient family, evaluated through `toCoeff`, is the
explicit finite sum. -/
lemma seriesFunM_toCoeff_apply {n N : ℕ} (a : Coeff n N) (x : Fin n → ℝ) (i j : Fin n) :
    Work.Diff.STE.Flat.seriesFunM (toCoeff a) x i j
      = ∑ m : box n N, a m i j * Work.Diff.STE.fourierExp m.1 x := by
  rw [Work.Diff.STE.flat.seriesFunM_eq_sum (toCoeff a)
      (fun k hk => toCoeff_apply_not_mem a hk) x i j]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [toCoeff_apply_mem a m.2]

/-- The value component of the explicit jet is the value of the Fourier series. -/
lemma valExp_eq_seriesFunM {n N : ℕ} (a : Coeff n N) (x : Fin n → ℝ) :
    valExp a x = Work.Diff.STE.Flat.seriesFunM (toCoeff a) x := by
  funext i j
  rw [seriesFunM_toCoeff_apply]
  rfl

/-- The finite sum defining `valExp` is the pointwise sum of the character functions. -/
lemma sum_character_fun {n N : ℕ} (a : Coeff n N) (i j : Fin n) :
    (fun y : Fin n → ℝ => ∑ m : box n N, a m i j * Work.Diff.STE.fourierExp m.1 y)
      = (∑ m : box n N, fun y : Fin n → ℝ => a m i j * Work.Diff.STE.fourierExp m.1 y) := by
  funext y
  exact (Finset.sum_apply y Finset.univ
    (fun m : box n N => fun y : Fin n → ℝ => a m i j * Work.Diff.STE.fourierExp m.1 y)).symm

/-- The first-derivative component of the explicit jet is the first partial derivative of the
Fourier series. -/
lemma fderiv_seriesFunM_toCoeff {n N : ℕ} (a : Coeff n N) (i j : Fin n) (c : Fin n)
    (x : Fin n → ℝ) :
    fderiv ℝ (fun y : Fin n → ℝ => Work.Diff.STE.Flat.seriesFunM (toCoeff a) y i j) x
        (Pi.single c 1)
      = linExp a x c i j := by
  have hfun : (fun y : Fin n → ℝ => Work.Diff.STE.Flat.seriesFunM (toCoeff a) y i j)
      = fun y => ∑ m : box n N, a m i j * Work.Diff.STE.fourierExp m.1 y :=
    funext (fun y => seriesFunM_toCoeff_apply a y i j)
  rw [hfun, sum_character_fun a i j]
  have hd : HasFDerivAt
      (∑ m : box n N, fun y : Fin n → ℝ => a m i j * Work.Diff.STE.fourierExp m.1 y)
      (∑ m : box n N, (a m i j) • fderiv ℝ (Work.Diff.STE.fourierExp m.1) x) x :=
    HasFDerivAt.sum (u := Finset.univ) fun m _ =>
      ((Work.Diff.STE.contDiff_fourierExp_top m.1).differentiable (by simp) x).hasFDerivAt
        |>.const_mul (a m i j)
  rw [hd.fderiv, sum_apply]
  simp only [smul_apply, smul_eq_mul, linExp]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [fderiv_fourierExp_apply_single m.1 c x]

/-- The second-derivative component of the explicit jet is the second partial derivative of the
Fourier series. -/
lemma fderiv2_seriesFunM_toCoeff {n N : ℕ} (a : Coeff n N) (i j : Fin n) (c d : Fin n)
    (x : Fin n → ℝ) :
    fderiv ℝ (fun y : Fin n → ℝ =>
        fderiv ℝ (fun z : Fin n → ℝ => Work.Diff.STE.Flat.seriesFunM (toCoeff a) z i j) y
          (Pi.single d 1)) x (Pi.single c 1)
      = secExp a x c d i j := by
  have hfun : (fun y : Fin n → ℝ =>
        fderiv ℝ (fun z : Fin n → ℝ => Work.Diff.STE.Flat.seriesFunM (toCoeff a) z i j) y
          (Pi.single d 1))
      = fun y => ∑ m : box n N, a m i j * dExp m.1 d y := by
    funext y
    rw [fderiv_seriesFunM_toCoeff a i j d y]
    rfl
  rw [hfun]
  have hsum' : (fun y : Fin n → ℝ => ∑ m : box n N, a m i j * dExp m.1 d y)
      = (∑ m : box n N, fun y : Fin n → ℝ => a m i j * dExp m.1 d y) := by
    funext y
    exact (Finset.sum_apply y Finset.univ
      (fun m : box n N => fun y : Fin n → ℝ => a m i j * dExp m.1 d y)).symm
  rw [hsum']
  have hd : HasFDerivAt
      (∑ m : box n N, fun y : Fin n → ℝ => a m i j * dExp m.1 d y)
      (∑ m : box n N, (a m i j) • fderiv ℝ (fun y => dExp m.1 d y) x) x :=
    HasFDerivAt.sum (u := Finset.univ) fun m _ =>
      ((contDiff_dExp_single m.1 d).differentiable (by simp) x).hasFDerivAt
        |>.const_mul (a m i j)
  rw [hd.fderiv, sum_apply]
  simp only [smul_apply, smul_eq_mul, secExp]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [fderiv_dExp_apply_single m.1 d c x]

/-- **The explicit jet is the jet of the Fourier series** of a box-supported coefficient family. -/
theorem jetM_seriesFunM_toCoeff {n N : ℕ} (a : Coeff n N) (x : Fin n → ℝ) :
    Work.Diff.STE.Flat.jetM (Work.Diff.STE.Flat.seriesFunM (toCoeff a)) x = jetExp a x := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · exact (valExp_eq_seriesFunM a x).symm
  · refine funext (fun c => funext (fun i => funext (fun j => ?_)))
    exact fderiv_seriesFunM_toCoeff a i j c x
  · refine funext (fun c => funext (fun d => funext (fun i => funext (fun j => ?_))))
    exact fderiv2_seriesFunM_toCoeff a i j c d x

end

end Galerkin

end Flat

end Work.Diff.STE
