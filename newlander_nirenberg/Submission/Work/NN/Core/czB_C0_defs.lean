/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# Vocabulary for the `C⁰` (continuous data) `L²` bound for `∂ (bmPotential ·)`

The target is `Work.NN.Core.czB_L2_bounded_C0`: for data `ψ` which is only *continuous*
(with compact support) but whose Bochner–Martinelli potential `u = bmPotential ψ` is `C¹`,
the `L²` norm of `∂u` is controlled by the `L²` norm of `ψ`.

The proof runs by duality (`L²`-adjoint): for a compactly supported `C¹` *test* field `φ` one
has, writing `θ = Σ_i ∂̄_i φ_i` and `V_l(w) = ∫ ζ, bmKernel l (ζ - w) * star (θ ζ)`,

  `Σ_i ∫ z, ∂_i u z * star (φ_i z) = Σ_l ∫ w, ψ_l w * V_l w`

(integration by parts for `∂` against a compactly supported test field, then Fubini, using the
oddness of the Bochner–Martinelli kernel).  The *adjoint* `V` is, in turn, a sum of `∂`-derivatives
of Bochner–Martinelli potentials of `C¹` compactly supported data,
`V_l = Σ_i ∂_i (bmPotential (singleFam l (star ∘ φ_i)))`, so the *already proved* `L²` bound in
the `C¹` case (`Work.NN.Core.czB_L2_bounded`) gives `‖V‖ ≤ C‖φ‖`; duality then gives
`‖∂u‖ ≤ C‖ψ‖`.

This file collects the definitions (`czTheta`, `singleFam`, `czV`) together with their elementary
API; the structural facts are in
`Submission/Work/NN/Core/czB_C0_Vpointwise.lean` (the pointwise description of `czV`) and
`Submission/Work/NN/Core/czB_C0_Vbound.lean` (its `L²` bound).
-/
import Mathlib
import Submission.Work.NN.Core.czB_L2_bounded
import Submission.Work.NN.Core.bmPotential_dCoord_eq
import Submission.Work.NN.Core.czbL2_energy

noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace Work.NN.Core

open Work.CR.Flat.Cauchy

/-- The scalar `(0,1)`-divergence `θ = Σ_i ∂̄_i φ_i` of a field `φ`. -/
def czTheta {n : ℕ} (φ : Fin n → (Fin n → ℂ) → ℂ) : (Fin n → ℂ) → ℂ :=
  fun z => ∑ i, Work.CR.Flat.dbarCoord i (φ i) z

@[simp] lemma czTheta_apply {n : ℕ} (φ : Fin n → (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) :
    czTheta φ z = ∑ i, Work.CR.Flat.dbarCoord i (φ i) z := rfl

/-- The family with a single non-zero component `g` in the `l`-th slot. -/
def singleFam {n : ℕ} (l : Fin n) (g : (Fin n → ℂ) → ℂ) : Fin n → (Fin n → ℂ) → ℂ :=
  fun m => if m = l then g else 0

@[simp] lemma singleFam_apply {n : ℕ} (l m : Fin n) (g : (Fin n → ℂ) → ℂ) :
    singleFam l g m = if m = l then g else 0 := rfl

@[simp] lemma singleFam_self {n : ℕ} (l : Fin n) (g : (Fin n → ℂ) → ℂ) :
    singleFam l g l = g := by simp [singleFam]

lemma singleFam_of_ne {n : ℕ} {l m : Fin n} (h : m ≠ l) (g : (Fin n → ℂ) → ℂ) :
    singleFam l g m = 0 := by simp [singleFam, h]

/-- The `L²`-adjoint kernel field of the pairing `φ ↦ Σ_i ∫ z, ∂_i u z * star (φ_i z)`. -/
def czV {n : ℕ} (φ : Fin n → (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) : Fin n → ℂ :=
  fun l => ∫ ζ, bmKernel l (ζ - z) * star (czTheta φ ζ)

@[simp] lemma czV_apply {n : ℕ} (φ : Fin n → (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) (l : Fin n) :
    czV φ z l = ∫ ζ, bmKernel l (ζ - z) * star (czTheta φ ζ) := rfl

/-- The Bochner–Martinelli potential of a single-component family is the corresponding single
convolution with the Bochner–Martinelli kernel. -/
lemma bmPotential_singleFam {n : ℕ} (l : Fin n) (g : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) :
    bmPotential (singleFam l g) z = ∫ ζ, bmKernel l (ζ - z) * g ζ := by
  have hfun : (fun j => ∫ ζ, bmKernel j (ζ - z) * singleFam l g j ζ)
      = fun j => if j = l then ∫ ζ, bmKernel j (ζ - z) * g ζ else 0 := by
    funext j
    by_cases hj : j = l
    · rw [if_pos hj]; subst hj; simp [singleFam_apply]
    · rw [if_neg hj]
      have h0 : singleFam l g j = (0 : (Fin n → ℂ) → ℂ) := by
        rw [singleFam_apply, if_neg hj]
      rw [h0]
      simp
  rw [bmPotential, hfun, Finset.sum_ite_eq' Finset.univ l]
  simp

/-- `bmPot` of a single-component family, with the singularity at the origin. -/
lemma bmPot_singleFam {n : ℕ} (l : Fin n) (g : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) :
    bmPot (singleFam l g) z = ∫ x, bmKernel l x * g (z + x) := by
  have hfun : (fun k => ∫ x, bmKernel k x * singleFam l g k (z + x))
      = fun k => if k = l then ∫ x, bmKernel k x * g (z + x) else 0 := by
    funext k
    by_cases hk : k = l
    · rw [if_pos hk]; subst hk; simp [singleFam_apply]
    · rw [if_neg hk]
      have h0 : singleFam l g k = (0 : (Fin n → ℂ) → ℂ) := by
        rw [singleFam_apply, if_neg hk]
      rw [h0]
      simp
  rw [bmPot, hfun, Finset.sum_ite_eq' Finset.univ l]
  simp

/-- A family with a single `C¹` component is `C¹`. -/
lemma contDiff_singleFam {n : ℕ} {l : Fin n} {g : (Fin n → ℂ) → ℂ} (hg : ContDiff ℝ 1 g) :
    ∀ m, ContDiff ℝ 1 (singleFam l g m) := by
  intro m
  by_cases hm : m = l
  · subst hm; simpa using hg
  · rw [singleFam_apply, if_neg hm]; exact contDiff_const

lemma hasCompactSupport_singleFam {n : ℕ} {l : Fin n} {g : (Fin n → ℂ) → ℂ}
    (hg : HasCompactSupport g) : ∀ m, HasCompactSupport (singleFam l g m) := by
  intro m
  by_cases hm : m = l
  · subst hm; simpa using hg
  · rw [singleFam_apply, if_neg hm]; exact HasCompactSupport.zero

end Work.NN.Core
