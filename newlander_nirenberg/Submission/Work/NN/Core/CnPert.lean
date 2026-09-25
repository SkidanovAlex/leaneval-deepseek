import Mathlib
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Polydisc

/-!
# The perturbation setup for the analytic core, in the flat model `ℂⁿ`

This module sets up, in the flat model `ℂⁿ = Fin n → ℂ` of the flat chapter (`Work.CR.Flat`),
the objects of the small-perturbation argument of the Newlander–Nirenberg theorem: the standard
structure `Jstd` (multiplication by `i`), a field `J` of real endomorphisms close to it, the
`(0,1)`-operator `dbarCn J`, and its linearisation in the perturbation.

## Conventions

* `dbarCn J u z = (1/2)(du + i·du∘J z)` is the `(0,1)`-part of `du`, exactly as in
  `Submission.dbar` but on `Cn n`; it is `J z`-antilinear when `J z ∘ J z = -1`.
* `stdForm f z` is the standard `(0,1)`-form `Σ_j f_j dz̄_j`, i.e. `w ↦ Σ_j f_j(z)·conj(w_j)`;
  its coefficients are `f_j` (`stdForm_single`), it is `Jstd`-antilinear (`stdForm_antilinear`),
  and `dbarCn Jstd u` is the standard form with coefficients `Work.CR.Flat.dbarCoord j u`
  (`dbarCn_std_eq_stdForm`).
* `dbarCn (Jstd + A) u = dbarCn Jstd u + (i/2)·du∘(A z)` (`dbarCn_lin`): the perturbation of the
  `∂̄`-operator is the first-order operator with coefficients `A`.
-/

noncomputable section

open scoped NNReal ENNReal ContDiff
open Set

namespace Work.NN.Core

/-- The flat model `ℂⁿ = Fin n → ℂ` (the type of the flat chapter `Work.CR.Flat`). -/
abbrev Cn (n : ℕ) := Fin n → ℂ

/-- The standard complex structure on `ℂⁿ`: multiplication by `i`. -/
noncomputable def JstdCn (n : ℕ) : Cn n → Cn n →L[ℝ] Cn n :=
  fun _ => Complex.I • (1 : Cn n →L[ℝ] Cn n)

@[simp] lemma JstdCn_apply (n : ℕ) (z v : Cn n) : JstdCn n z v = Complex.I • v := by
  simp [JstdCn]

lemma JstdCn_sq (n : ℕ) (z v : Cn n) : JstdCn n z (JstdCn n z v) = -v := by
  rw [JstdCn_apply, JstdCn_apply, smul_smul, Complex.I_mul_I, neg_one_smul]

/-- `i • Pi.single j 1 = Pi.single j i`. -/
lemma smul_single_I {n : ℕ} (j : Fin n) :
    (Complex.I • (Pi.single j (1 : ℂ)) : Cn n) = Pi.single j (Complex.I : ℂ) := by
  ext m
  by_cases hm : m = j
  · subst hm; simp [Pi.single_eq_same]
  · simp [Pi.single_eq_of_ne hm]

/-- The `(0,1)`-operator `∂̄_J u = (1/2)(du + i·du∘J)` of a field `J` on `ℂⁿ`. -/
noncomputable def dbarCn {n : ℕ} (J : Cn n → Cn n →L[ℝ] Cn n) (u : Cn n → ℂ)
    (z : Cn n) : Cn n →L[ℝ] ℂ :=
  (1 / 2 : ℝ) • (fderiv ℝ u z + Complex.I • ((fderiv ℝ u z).comp (J z)))

lemma dbarCn_apply {n : ℕ} (J : Cn n → Cn n →L[ℝ] Cn n) (u : Cn n → ℂ) (z v : Cn n) :
    dbarCn J u z v = (1 / 2 : ℂ) * (fderiv ℝ u z v + Complex.I * fderiv ℝ u z (J z v)) := by
  have hcoe : (↑(1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) := by norm_num
  simp only [dbarCn, add_apply, smul_apply, ContinuousLinearMap.comp_apply, Complex.real_smul,
    hcoe]
  ring

/-- `J z`-antilinearity of `dbarCn J u z`. -/
lemma dbarCn_antilinear {n : ℕ} {J : Cn n → Cn n →L[ℝ] Cn n} {u : Cn n → ℂ} {z : Cn n}
    (hJ : ∀ v, J z (J z v) = -v) (v : Cn n) :
    dbarCn J u z (J z v) = -Complex.I * dbarCn J u z v := by
  rw [dbarCn_apply, dbarCn_apply, hJ, map_neg]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- A real-linear form vanishes iff it vanishes on the real basis `{e_j, i·e_j}`. -/
lemma form_eq_zero_iff_basis {n : ℕ} (f : Cn n →L[ℝ] ℂ) :
    f = 0 ↔ (∀ j : Fin n, f (Pi.single j (1 : ℂ)) = 0) ∧
      (∀ j : Fin n, f (Pi.single j (Complex.I : ℂ)) = 0) := by
  constructor
  · intro h; exact ⟨fun j => by rw [h]; rfl, fun j => by rw [h]; rfl⟩
  · rintro ⟨h1, h2⟩
    have hdecomp : ∀ w : Cn n, w = ∑ j : Fin n, ((w j).re • (Pi.single j (1 : ℂ) : Cn n)
        + (w j).im • (Pi.single j (Complex.I : ℂ) : Cn n)) := by
      intro w
      rw [← Finset.univ_sum_single w]
      refine Finset.sum_congr rfl fun j _ => ?_
      ext m
      rcases eq_or_ne m j with rfl | hm
      · simp [Complex.re_add_im]
      · simp [Pi.single_eq_of_ne hm]
    ext w
    rw [hdecomp w, map_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [map_add, map_smul, map_smul, h1 j, h2 j]
    simp

/-- Two real-linear forms are equal if they agree on the real basis `{e_j, i·e_j}`. -/
lemma form_ext_basis {n : ℕ} {f g : Cn n →L[ℝ] ℂ}
    (h1 : ∀ j, f (Pi.single j (1 : ℂ)) = g (Pi.single j (1 : ℂ)))
    (h2 : ∀ j, f (Pi.single j (Complex.I : ℂ)) = g (Pi.single j (Complex.I : ℂ))) : f = g := by
  rw [← sub_eq_zero, form_eq_zero_iff_basis]
  exact ⟨fun j => by rw [sub_apply, h1 j, sub_self],
    fun j => by rw [sub_apply, h2 j, sub_self]⟩

/-! ### The perturbation

`dbarCn (Jstd + A) u = dbarCn Jstd u + (i/2)·du∘(A z)`, the linearity identity that turns the
chart equation into a linear equation. -/

lemma dbarCn_lin {n : ℕ} (A : Cn n → Cn n →L[ℝ] Cn n) (u : Cn n → ℂ) (z : Cn n) :
    dbarCn (JstdCn n + A) u z
      = dbarCn (JstdCn n) u z + (Complex.I / 2) • ((fderiv ℝ u z).comp (A z)) := by
  have hcoe : (↑(1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) := by norm_num
  ext v
  simp only [dbarCn, Pi.add_apply, add_apply, smul_apply, ContinuousLinearMap.comp_apply,
    Complex.real_smul, hcoe, map_add]
  ring

/-! ### The standard form of a coefficient family -/

/-- The standard `(0,1)`-form `Σ_j f_j dz̄_j` with coefficients `f`, i.e. `w ↦ Σ_j f_j(z)·conj(w_j)`. -/
noncomputable def stdForm {n : ℕ} (f : Fin n → Cn n → ℂ) (z : Cn n) : Cn n →L[ℝ] ℂ :=
  ∑ j : Fin n, (f j z) • ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (ContinuousLinearMap.proj j))

lemma stdForm_apply {n : ℕ} (f : Fin n → Cn n → ℂ) (z w : Cn n) :
    stdForm f z w = ∑ j, f j z * Complex.conjCLE (w j) := by
  change (∑ j : Fin n, (f j z) • ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp
      (ContinuousLinearMap.proj j))) w = ∑ j, f j z * Complex.conjCLE (w j)
  rw [show (∑ j : Fin n, (f j z) • ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp
        (ContinuousLinearMap.proj j))) w
      = ∑ j : Fin n, ((f j z) • ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp
        (ContinuousLinearMap.proj j))) w
      from map_sum (ContinuousLinearMap.apply ℝ ℂ w) _ Finset.univ]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    smul_eq_mul]
  rfl

lemma stdForm_single {n : ℕ} (f : Fin n → Cn n → ℂ) (z : Cn n) (j : Fin n) :
    stdForm f z (Pi.single j (1 : ℂ)) = f j z := by
  rw [stdForm_apply]
  rw [Finset.sum_eq_single j (fun l _ hl => by simp [Pi.single_eq_of_ne hl])
    (fun h => absurd (Finset.mem_univ j) h)]
  simp

lemma stdForm_single_I {n : ℕ} (f : Fin n → Cn n → ℂ) (z : Cn n) (j : Fin n) :
    stdForm f z (Pi.single j (Complex.I : ℂ)) = -Complex.I * f j z := by
  rw [stdForm_apply]
  rw [Finset.sum_eq_single j (fun l _ hl => by simp [Pi.single_eq_of_ne hl])
    (fun h => absurd (Finset.mem_univ j) h)]
  rw [Pi.single_eq_same,
    show Complex.conjCLE (Complex.I : ℂ) = -Complex.I from Complex.conj_I]
  ring

lemma stdForm_antilinear {n : ℕ} (f : Fin n → Cn n → ℂ) (z : Cn n) (w : Cn n) :
    stdForm f z (Complex.I • w) = -Complex.I * stdForm f z w := by
  rw [stdForm_apply, stdForm_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Pi.smul_apply, smul_eq_mul]
  simp only [Complex.conjCLE_apply, map_mul]
  rw [show (starRingEnd ℂ) Complex.I = -Complex.I from Complex.conj_I]
  ring

/-- The standard form is determined by its coefficients. -/
lemma stdForm_ext {n : ℕ} {f g : Fin n → Cn n → ℂ} {z : Cn n}
    (h : ∀ j, f j z = g j z) : stdForm f z = stdForm g z := by
  ext w
  rw [stdForm_apply, stdForm_apply]
  exact Finset.sum_congr rfl fun j _ => by rw [h j]

/-- `dbarCn` of the standard structure is the standard form whose coefficients are the flat
`∂̄`-derivatives. -/
lemma dbarCn_std_eq_stdForm {n : ℕ} (u : Cn n → ℂ) (z : Cn n) :
    dbarCn (JstdCn n) u z = stdForm (fun j _ => Work.CR.Flat.dbarCoord j u z) z := by
  refine form_ext_basis ?_ ?_
  · intro j
    rw [dbarCn_apply, stdForm_single, JstdCn_apply, smul_single_I, Work.CR.Flat.dbarCoord]
  · intro j
    have hh : ((JstdCn n) z) (Pi.single j (Complex.I : ℂ))
        = - (Pi.single j (1 : ℂ) : Cn n) := by
      rw [JstdCn_apply]
      ext m
      by_cases hm : m = j
      · subst hm; simp [Pi.single_eq_same, Complex.I_mul_I]
      · simp [Pi.single_eq_of_ne hm]
    rw [dbarCn_apply, stdForm_single_I, hh, map_neg, Work.CR.Flat.dbarCoord]
    ring_nf
    rw [Complex.I_sq]
    ring

/-- The coefficients of `dbarCn Jstd u` are the flat `∂̄_j u`. -/
lemma stdForm_coef_dbar_std {n : ℕ} (u : Cn n → ℂ) (z : Cn n) (j : Fin n) :
    dbarCn (JstdCn n) u z (Pi.single j (1 : ℂ)) = Work.CR.Flat.dbarCoord j u z := by
  rw [dbarCn_std_eq_stdForm, stdForm_single]

/-- The perturbation operator on coefficients: `(L_A w)_j = (i/2)·dw(A z e_j)`.  It is the
difference between the `j`-th coefficient of `∂̄_{Jstd + A} w` and `dbarCoord j w`; it is
*first order* in `w` (`dbarCoef_lin`), which is what makes the small-perturbation contraction
estimate a two-line product estimate. -/
noncomputable def Lcoef {n : ℕ} (A : Cn n → Cn n →L[ℝ] Cn n) (w : Cn n → ℂ) (j : Fin n)
    (z : Cn n) : ℂ :=
  (Complex.I / 2) * fderiv ℝ w z (A z (Pi.single j (1 : ℂ)))

/-- **The linearisation, at the level of coefficients.** -/
lemma dbarCoef_lin {n : ℕ} (A : Cn n → Cn n →L[ℝ] Cn n) (w : Cn n → ℂ) (j : Fin n)
    (z : Cn n) :
    dbarCn (JstdCn n + A) w z (Pi.single j (1 : ℂ))
      = Work.CR.Flat.dbarCoord j w z + Lcoef A w j z := by
  rw [dbarCn_apply, Lcoef, Work.CR.Flat.dbarCoord]
  have h : (JstdCn n + A) z (Pi.single j (1 : ℂ))
      = JstdCn n z (Pi.single j (1 : ℂ)) + A z (Pi.single j (1 : ℂ)) := rfl
  rw [h, map_add, JstdCn_apply, smul_single_I]
  ring

end Work.NN.Core
