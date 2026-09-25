import Mathlib
import Submission.Work.NN.Core.CnPert
import Submission.Work.CR.Flat.Cauchy.bmCz.fderiv_eq_sum_wirtinger

/-!
# Auxiliary algebra for the perturbed `∂̄`-operator on `ℂⁿ`

The target `Work.NN.Core.dbarCn_smooth_of_small_pert` (Weyl lemma for `∂̄_{Jstd + A}`) is proved
by reducing the equation `dbarCn (Jstd + A) u = 0` to a **Beltrami system** for the Wirtinger
derivatives of `u`.

This file contains the two elementary algebraic steps of that reduction:

* `fderiv_eq_sum_dCoord_dbarCoord`: the Wirtinger decomposition
  `du_z(v) = Σ_j (v_j ∂_j u(z) + \overline{v_j} ∂̄_j u(z))`, deduced from
  `Work.CR.Flat.Cauchy.bmCz.fderiv_eq_sum_wirtinger`;
* `dbarCoord_eq_beltrami_implicit`: the Beltrami form of the equation, in *implicit* (not
  decoupled) form:
  `∂̄_k u(z) = Σ_j (β k j z ∂_j u(z) - \overline{β k j z} ∂̄_j u(z))` with
  `β k j z = -(I/2) · (A z (e_k))_j`, a **smooth** (and small) coefficient.
-/

noncomputable section

open scoped NNReal ENNReal ContDiff
open Set

namespace Work.NN.Core

variable {n : ℕ}

/-! ## The Wirtinger decomposition of the real differential -/

/-- **Wirtinger decomposition.**  For any `u : ℂⁿ → ℂ` and `z v`,
`du_z(v) = Σ_j (v_j · ∂_j u(z) + conj(v_j) · ∂̄_j u(z))`.

(The identity is an identity of the *real* differential; it needs no hypothesis because
`dCoord`/`dbarCoord` are defined from `fderiv` for all functions.) -/
theorem fderiv_eq_sum_dCoord_dbarCoord (u : Cn n → ℂ) (z v : Cn n) :
    fderiv ℝ u z v
      = ∑ j : Fin n, (v j * Work.CR.Flat.dCoord j u z
          + starRingEnd ℂ (v j) * Work.CR.Flat.dbarCoord j u z) := by
  rw [Work.CR.Flat.Cauchy.bmCz.fderiv_eq_sum_wirtinger]
  refine Finset.sum_congr rfl fun j _ => ?_
  -- `L e = ∂ + ∂̄` and `L (i e) = I (∂ - ∂̄)`
  have h1 : fderiv ℝ u z (Pi.single j (1 : ℂ))
      = Work.CR.Flat.dCoord j u z + Work.CR.Flat.dbarCoord j u z := by
    simp only [Work.CR.Flat.dCoord, Work.CR.Flat.dbarCoord]
    ring
  have h2 : fderiv ℝ u z (Pi.single j (Complex.I : ℂ))
      = Complex.I * (Work.CR.Flat.dCoord j u z - Work.CR.Flat.dbarCoord j u z) := by
    simp only [Work.CR.Flat.dCoord, Work.CR.Flat.dbarCoord]
    ring_nf
    simp [pow_two, Complex.I_mul_I]
  rw [h1, h2]
  apply Complex.ext <;>
    simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.conj_re, Complex.conj_im, Complex.sub_re, Complex.sub_im] <;> ring

/-! ## The Beltrami form of the equation -/

/-- The smooth coefficient family of the Beltrami form of `∂̄_{Jstd + A}`:
`β k j z = -(I/2) · (A z (e_k))_j`. -/
noncomputable def betaCoef (A : Cn n → Cn n →L[ℝ] Cn n) (k j : Fin n) (z : Cn n) : ℂ :=
  -(Complex.I / 2) * (A z (Pi.single k (1 : ℂ))) j

/-- Smallness of the Beltrami coefficient: `‖β k j z‖ ≤ ‖A z‖ / 2`. -/
theorem norm_betaCoef_le {A : Cn n → Cn n →L[ℝ] Cn n} {ε : ℝ} {z : Cn n}
    (hA : ‖A z‖ ≤ ε) (k j : Fin n) : ‖betaCoef A k j z‖ ≤ ε / 2 := by
  have h1 : ‖(A z (Pi.single k (1 : ℂ))) j‖ ≤ ‖A z‖ := by
    refine le_trans (norm_le_pi_norm _ j) ?_
    have h2 := ContinuousLinearMap.le_opNorm (A z) (Pi.single k (1 : ℂ))
    rwa [Pi.norm_single, norm_one, mul_one] at h2
  have h2 : ‖(A z (Pi.single k (1 : ℂ))) j‖ ≤ ε := le_trans h1 hA
  rw [betaCoef, norm_mul]
  have h3 : ‖(-(Complex.I / 2) : ℂ)‖ = 1 / 2 := by
    rw [norm_neg, norm_div, Complex.norm_I]
    norm_num
  rw [h3]
  linarith

/-- **The Beltrami form of `dbarCn (Jstd + A) u z = 0`** (implicit form).

If the `(0,1)`-form `dbarCn (Jstd + A) u z` vanishes at `z`, then for every `k`
`∂̄_k u(z) = Σ_j (β k j z · ∂_j u(z) - conj(β k j z) · ∂̄_j u(z))`,
where `β k j z = -(I/2)·(A z e_k)_j` is smooth in `z` and satisfies `‖β k j z‖ ≤ ‖A z‖ / 2`. -/
theorem dbarCoord_eq_beltrami_implicit {A : Cn n → Cn n →L[ℝ] Cn n} {u : Cn n → ℂ} {z : Cn n}
    (h : dbarCn (JstdCn n + A) u z = 0) (k : Fin n) :
    Work.CR.Flat.dbarCoord k u z
      = ∑ j : Fin n, (betaCoef A k j z * Work.CR.Flat.dCoord j u z
          - starRingEnd ℂ (betaCoef A k j z) * Work.CR.Flat.dbarCoord j u z) := by
  -- the `e_k`-coefficient of the equation, by `dbarCoef_lin`
  have hk : Work.CR.Flat.dbarCoord k u z + Lcoef A u k z = 0 := by
    have h1 := congrFun (congrArg DFunLike.coe h) (Pi.single k (1 : ℂ))
    simp only [zero_apply] at h1
    rw [dbarCoef_lin] at h1
    exact h1
  -- expand the perturbation term with the Wirtinger decomposition
  have hL : Lcoef A u k z
      = (Complex.I / 2) * ∑ j : Fin n,
          ((A z (Pi.single k (1 : ℂ))) j * Work.CR.Flat.dCoord j u z
            + starRingEnd ℂ ((A z (Pi.single k (1 : ℂ))) j) * Work.CR.Flat.dbarCoord j u z) := by
    rw [Lcoef, fderiv_eq_sum_dCoord_dbarCoord]
  rw [hL] at hk
  -- conjugate coefficient identity
  have hconj : ∀ j : Fin n, starRingEnd ℂ (betaCoef A k j z)
      = (Complex.I / 2) * starRingEnd ℂ ((A z (Pi.single k (1 : ℂ))) j) := by
    intro j
    simp only [betaCoef, map_mul, map_neg, map_div₀, map_ofNat, Complex.conj_I]
    ring
  -- rewrite the target sum
  have hgoal : (∑ j : Fin n, (betaCoef A k j z * Work.CR.Flat.dCoord j u z
        - starRingEnd ℂ (betaCoef A k j z) * Work.CR.Flat.dbarCoord j u z))
      = (-(Complex.I / 2)) * ∑ j : Fin n,
          ((A z (Pi.single k (1 : ℂ))) j * Work.CR.Flat.dCoord j u z
            + starRingEnd ℂ ((A z (Pi.single k (1 : ℂ))) j) * Work.CR.Flat.dbarCoord j u z) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hconj j, betaCoef]
    ring
  rw [hgoal, hL] at *
  linear_combination hk


/-! ## The matrix of the Beltrami system, and its decoupled coefficient -/

section Matrix

variable {n : ℕ}

/-- The `(0,1)`-coefficient matrix `B(z)` acting on the vector `∂u(z)`:
`(B(z) v)_k = Σ_j β k j z · v_j`. -/
noncomputable def Bop (A : Cn n → Cn n →L[ℝ] Cn n) (z : Cn n) : Cn n →L[ℝ] Cn n :=
  ContinuousLinearMap.pi (fun k => ∑ j : Fin n,
    ContinuousLinearMap.smulRight (ContinuousLinearMap.proj j : Cn n →L[ℝ] ℂ) (betaCoef A k j z))

/-- Its conjugate `\bar B(z)`, the matrix multiplying `∂̄u(z)` in the implicit Beltrami form. -/
noncomputable def BopBar (A : Cn n → Cn n →L[ℝ] Cn n) (z : Cn n) : Cn n →L[ℝ] Cn n :=
  ContinuousLinearMap.pi (fun k => ∑ j : Fin n,
    ContinuousLinearMap.smulRight (ContinuousLinearMap.proj j : Cn n →L[ℝ] ℂ)
      (starRingEnd ℂ (betaCoef A k j z)))

@[simp] lemma Bop_apply (A : Cn n → Cn n →L[ℝ] Cn n) (z v : Cn n) (k : Fin n) :
    (Bop A z v) k = ∑ j : Fin n, v j * betaCoef A k j z := by
  simp [Bop]

@[simp] lemma BopBar_apply (A : Cn n → Cn n →L[ℝ] Cn n) (z v : Cn n) (k : Fin n) :
    (BopBar A z v) k = ∑ j : Fin n, v j * starRingEnd ℂ (betaCoef A k j z) := by
  simp [BopBar]

/-- The decoupled Beltrami coefficient `(1 + \bar B(z))⁻¹ B(z)`. -/
noncomputable def beltramiCoeff (A : Cn n → Cn n →L[ℝ] Cn n) (z : Cn n) : Cn n →L[ℝ] Cn n :=
  (ContinuousLinearMap.inverse (1 + BopBar A z)) * Bop A z

/-- The coefficient family, in coordinates. -/
noncomputable def beltramiCoef (A : Cn n → Cn n →L[ℝ] Cn n) (k j : Fin n) (z : Cn n) : ℂ :=
  (beltramiCoeff A z (Pi.single j (1 : ℂ))) k

end Matrix


end Work.NN.Core
