import Mathlib
import Submission.Work.RPA3.follow_family_defs
import Submission.Work.RPCore.Flow.clampedField_bounds
import Submission.Work.RPA3.flux_prim_smooth

/-!
# RPA3: `C¹`-regularity of the tangential correction field `Yfield`

Given a `LagFamilyAll` `L` and a Hamiltonian `H` which is `C⁴` as a function of `(t, x)`,
we show that the correction field

`(τ, x, t) ↦ Yfield L H τ (x, t)`

of `follow_family_defs` is `C¹`.  Concretely, `Yfield` is obtained from the Gram matrix of the
slice derivatives `(∂_x ℓ, ∂_t ℓ)` by the formula `G⁻¹ (⟪W, ∂_xℓ⟫, ⟪W, ∂_tℓ⟫)`, where
`W = X_H ∘ ℓ - ∂_τℓ`; the Gram matrix is invertible everywhere (`gramDet_pos`), and each of the
ingredients is smooth in `(τ, x, t)`:

* `∂_xℓ`, `∂_tℓ`, `∂_τℓ` are `C⁷` (`flux_prim_smooth`, `contDiff_sliceDerivTau`),
* the Hamiltonian field `(τ,x,t) ↦ X_{H τ}(ℓ τ (x,t))` is `C³`
  (`ContDiff.fderiv` applied to the uncurried `H`).

In this file all these ingredients are curried onto the single variable
`z : ℝ × (ℝ × ℝ)` (so that `z = (τ, (x,t))`); the target statement is then a combination of
`ContDiff` operations.
-/

open scoped ContDiff

set_option autoImplicit false

noncomputable section

namespace Work.RPA3

/-! ## The ingredients of `Yfield`, curried on `z = (τ, (x,t))` -/

private def dXF (L : LagFamilyAll) : ℝ × (ℝ × ℝ) → PS := fun z => dX L z.1 z.2.1 z.2.2
private def dTF (L : LagFamilyAll) : ℝ × (ℝ × ℝ) → PS := fun z => dT L z.1 z.2.1 z.2.2
private def dTauF (L : LagFamilyAll) : ℝ × (ℝ × ℝ) → PS := fun z => dTau L z.1 z.2.1 z.2.2
private def WvecF (L : LagFamilyAll) (H : ℝ → PS → ℝ) : ℝ × (ℝ × ℝ) → PS :=
  fun z => Wvec L H z.1 z.2.1 z.2.2
private def gramAF (L : LagFamilyAll) : ℝ × (ℝ × ℝ) → ℝ := fun z => gramA L z.1 z.2.1 z.2.2
private def gramBF (L : LagFamilyAll) : ℝ × (ℝ × ℝ) → ℝ := fun z => gramB L z.1 z.2.1 z.2.2
private def gramCF (L : LagFamilyAll) : ℝ × (ℝ × ℝ) → ℝ := fun z => gramC L z.1 z.2.1 z.2.2
private def gramDetF (L : LagFamilyAll) : ℝ × (ℝ × ℝ) → ℝ := fun z => gramDet L z.1 z.2.1 z.2.2
private def num1F (L : LagFamilyAll) (H : ℝ → PS → ℝ) : ℝ × (ℝ × ℝ) → ℝ :=
  fun z => gramCF L z * ip (WvecF L H z) (dXF L z) - gramBF L z * ip (WvecF L H z) (dTF L z)
private def num2F (L : LagFamilyAll) (H : ℝ → PS → ℝ) : ℝ × (ℝ × ℝ) → ℝ :=
  fun z => gramAF L z * ip (WvecF L H z) (dTF L z) - gramBF L z * ip (WvecF L H z) (dXF L z)

/-! ## Smoothness of the Euclidean pairing of two smooth maps -/

private lemma contDiff_ip {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : WithTop ℕ∞}
    {u v : X → PS} (hu : ContDiff ℝ n u) (hv : ContDiff ℝ n v) :
    ContDiff ℝ n (fun z => ip (u z) (v z)) := by
  simp only [ip]
  fun_prop

/-! ## Smoothness of the three slice derivatives -/

private lemma dXF_contDiff (L : LagFamilyAll) : ContDiff ℝ 7 (dXF L) :=
  contDiff_deriv_x L.toLagFamily

private lemma dTF_contDiff (L : LagFamilyAll) : ContDiff ℝ 7 (dTF L) :=
  contDiff_deriv_trd L.toLagFamily

private lemma dTauF_contDiff (L : LagFamilyAll) : ContDiff ℝ 7 (dTauF L) :=
  contDiff_sliceDerivTau L

/-! ## Smoothness of the Hamiltonian field `z ↦ X_{H z.1}(ℓ z)`

The point is that `(z, y) ↦ H z.1 y` is the uncurried Hamiltonian, `C⁴` by hypothesis, so its
partial derivative in `y` is `C³` (`ContDiff.fderiv`), and the four components of `hamVF` are its
values at the four fixed directions. -/

private lemma hamVF_contDiff (L : LagFamilyAll) (H : ℝ → PS → ℝ)
    (hH : ContDiff ℝ 4 (fun z : ℝ × PS => H z.1 z.2)) :
    ContDiff ℝ 3 (fun z : ℝ × (ℝ × ℝ) => hamVF (H z.1) (L.ℓ z.1 z.2)) := by
  have hHu : ContDiff ℝ 4
      (Function.uncurry (fun (z : ℝ × (ℝ × ℝ)) (y : PS) => H z.1 y)) := by
    show ContDiff ℝ 4 (fun p : (ℝ × (ℝ × ℝ)) × PS => H p.1.1 p.2)
    have hmap : ContDiff ℝ 4
        (fun p : (ℝ × (ℝ × ℝ)) × PS => ((p.1.1, p.2) : ℝ × PS)) := by fun_prop
    have := hH.comp hmap
    simpa only [Function.comp_def] using this
  have hg : ContDiff ℝ 3 (fun z : ℝ × (ℝ × ℝ) => L.ℓ z.1 z.2) :=
    L.smooth.of_le (by norm_num)
  have hfd : ContDiff ℝ 3
      (fun z : ℝ × (ℝ × ℝ) => fderiv ℝ (fun y : PS => H z.1 y) (L.ℓ z.1 z.2)) :=
    ContDiff.fderiv (f := fun (z : ℝ × (ℝ × ℝ)) (y : PS) => H z.1 y)
      (g := fun (z : ℝ × (ℝ × ℝ)) => L.ℓ z.1 z.2) hHu hg (by norm_num)
  have hv1 : ContDiff ℝ 3 (fun _ : ℝ × (ℝ × ℝ) => (((0, 0), (1, 0)) : PS)) := contDiff_const
  have hv2 : ContDiff ℝ 3 (fun _ : ℝ × (ℝ × ℝ) => (((0, 0), (0, 1)) : PS)) := contDiff_const
  have hv3 : ContDiff ℝ 3 (fun _ : ℝ × (ℝ × ℝ) => (((1, 0), (0, 0)) : PS)) := contDiff_const
  have hv4 : ContDiff ℝ 3 (fun _ : ℝ × (ℝ × ℝ) => (((0, 1), (0, 0)) : PS)) := contDiff_const
  have hc1 : ContDiff ℝ 3 (fun z : ℝ × (ℝ × ℝ) =>
      (fderiv ℝ (fun y : PS => H z.1 y) (L.ℓ z.1 z.2)) (((0, 0), (1, 0)) : PS)) :=
    ContDiff.clm_apply hfd hv1
  have hc2 : ContDiff ℝ 3 (fun z : ℝ × (ℝ × ℝ) =>
      (fderiv ℝ (fun y : PS => H z.1 y) (L.ℓ z.1 z.2)) (((0, 0), (0, 1)) : PS)) :=
    ContDiff.clm_apply hfd hv2
  have hc3 : ContDiff ℝ 3 (fun z : ℝ × (ℝ × ℝ) =>
      (fderiv ℝ (fun y : PS => H z.1 y) (L.ℓ z.1 z.2)) (((1, 0), (0, 0)) : PS)) :=
    ContDiff.clm_apply hfd hv3
  have hc4 : ContDiff ℝ 3 (fun z : ℝ × (ℝ × ℝ) =>
      (fderiv ℝ (fun y : PS => H z.1 y) (L.ℓ z.1 z.2)) (((0, 1), (0, 0)) : PS)) :=
    ContDiff.clm_apply hfd hv4
  have hfin : ContDiff ℝ 3 (fun z : ℝ × (ℝ × ℝ) =>
      (((fderiv ℝ (fun y : PS => H z.1 y) (L.ℓ z.1 z.2)) (((0, 0), (1, 0)) : PS),
        (fderiv ℝ (fun y : PS => H z.1 y) (L.ℓ z.1 z.2)) (((0, 0), (0, 1)) : PS)),
       (-(fderiv ℝ (fun y : PS => H z.1 y) (L.ℓ z.1 z.2)) (((1, 0), (0, 0)) : PS),
        -(fderiv ℝ (fun y : PS => H z.1 y) (L.ℓ z.1 z.2)) (((0, 1), (0, 0)) : PS)))) :=
    (hc1.prodMk hc2).prodMk (hc3.neg.prodMk hc4.neg)
  simpa only [hamVF] using hfin

/-! ## Assembling the regularity of `Yfield` at level `C¹` -/

private lemma dXF_contDiff1 (L : LagFamilyAll) : ContDiff ℝ 1 (dXF L) :=
  (dXF_contDiff L).of_le (by norm_num)

private lemma dTF_contDiff1 (L : LagFamilyAll) : ContDiff ℝ 1 (dTF L) :=
  (dTF_contDiff L).of_le (by norm_num)

private lemma dTauF_contDiff1 (L : LagFamilyAll) : ContDiff ℝ 1 (dTauF L) :=
  (dTauF_contDiff L).of_le (by norm_num)

private lemma WvecF_contDiff (L : LagFamilyAll) (H : ℝ → PS → ℝ)
    (hH : ContDiff ℝ 4 (fun z : ℝ × PS => H z.1 z.2)) : ContDiff ℝ 1 (WvecF L H) := by
  have h1 : ContDiff ℝ 1 (fun z : ℝ × (ℝ × ℝ) => hamVF (H z.1) (L.ℓ z.1 z.2)) :=
    (hamVF_contDiff L H hH).of_le (by norm_num)
  have h2 := dTauF_contDiff1 L
  exact h1.sub h2

private lemma gramAF_contDiff (L : LagFamilyAll) : ContDiff ℝ 1 (gramAF L) :=
  contDiff_ip (dXF_contDiff1 L) (dXF_contDiff1 L)

private lemma gramBF_contDiff (L : LagFamilyAll) : ContDiff ℝ 1 (gramBF L) :=
  contDiff_ip (dXF_contDiff1 L) (dTF_contDiff1 L)

private lemma gramCF_contDiff (L : LagFamilyAll) : ContDiff ℝ 1 (gramCF L) :=
  contDiff_ip (dTF_contDiff1 L) (dTF_contDiff1 L)

private lemma gramDetF_contDiff (L : LagFamilyAll) : ContDiff ℝ 1 (gramDetF L) := by
  have hA := gramAF_contDiff L
  have hB := gramBF_contDiff L
  have hC := gramCF_contDiff L
  have hsq : ContDiff ℝ 1 (fun z => gramBF L z ^ 2) := by
    simpa only [pow_two] using hB.mul hB
  exact (hA.mul hC).sub hsq

private lemma num1F_contDiff (L : LagFamilyAll) (H : ℝ → PS → ℝ)
    (hH : ContDiff ℝ 4 (fun z : ℝ × PS => H z.1 z.2)) : ContDiff ℝ 1 (num1F L H) := by
  have hW := WvecF_contDiff L H hH
  have hip1 := contDiff_ip hW (dXF_contDiff1 L)
  have hip2 := contDiff_ip hW (dTF_contDiff1 L)
  exact ((gramCF_contDiff L).mul hip1).sub ((gramBF_contDiff L).mul hip2)

private lemma num2F_contDiff (L : LagFamilyAll) (H : ℝ → PS → ℝ)
    (hH : ContDiff ℝ 4 (fun z : ℝ × PS => H z.1 z.2)) : ContDiff ℝ 1 (num2F L H) := by
  have hW := WvecF_contDiff L H hH
  have hip1 := contDiff_ip hW (dXF_contDiff1 L)
  have hip2 := contDiff_ip hW (dTF_contDiff1 L)
  exact ((gramAF_contDiff L).mul hip2).sub ((gramBF_contDiff L).mul hip1)

theorem Yfield_contDiff (L : LagFamilyAll) (H : ℝ → PS → ℝ)
    (hH : ContDiff ℝ 4 (fun z : ℝ × PS => H z.1 z.2)) :
    ContDiff ℝ 1 (fun z : ℝ × (ℝ × ℝ) => Yfield L H z.1 z.2) := by
  have hnum1 := num1F_contDiff L H hH
  have hnum2 := num2F_contDiff L H hH
  have hdet := gramDetF_contDiff L
  have hne : ∀ z, gramDetF L z ≠ 0 := fun z => (gramDet_pos L z.1 z.2.1 z.2.2).ne'
  have hq1 := hnum1.div hdet hne
  have hq2 := hnum2.div hdet hne
  exact hq1.prodMk hq2

end Work.RPA3
