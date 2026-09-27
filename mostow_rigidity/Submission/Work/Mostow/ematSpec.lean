import Mathlib
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.poSheet

/-!
# The effective matrix `emat g` of an element of `PO(n,1)`

For `g : PO(n,1)` the *effective matrix* is

`emat g = tsign (rep g) • mat (rep g)`,

i.e. the unique representative of the class of `Quotient.out g` in `O(n,1)` whose
time–time entry is positive.  It is the matrix that acts linearly on the hyperboloid
lift of `ℍⁿ`:

* `emat g *ᵥ hlift u = hlift (g • u)` (the "sheet lemma", in matrix form);
* `emat g` preserves the Minkowski form `mink` on `ℝ^{Fin n ⊕ Fin 1}`;
* the fixed boundary points of `g` are exactly the null directions `nvec ξ = (ξ,1)`
  that are eigenvectors of `mat (rep g)`.

The first two statements are the linearised form of the isometric action of `PO(n,1)`
on `ℍⁿ`; the third identifies the fixed point set of `g` on `∂ℍⁿ` with the
eigen-directions of its matrix representative, which is what makes the boundary action
computable.

All three are proved here from the explicit matrix algebra of `poAux`/`Hyper`/`poSheet`
(no `POActionProp` hypothesis is needed: `emat` is built from the *chosen* representative
`rep g = Quotient.out g`, for which `g • u = actO (rep g) u` holds by definition).
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory Matrix

noncomputable section

variable {n : ℕ}

/-- `Work.Mostow.mink` is the pairing `mform x y = xᵀ J y` of the Minkowski form. -/
lemma mink_eq_mform (x y : Fin n ⊕ Fin 1 → ℝ) : mink x y = mform x y := by
  rw [mform_apply]; rfl

/-- Scalar bilinearity of the Minkowski form `mform`. -/
lemma mform_smul (r s : ℝ) (x y : Fin n ⊕ Fin 1 → ℝ) :
    mform (r • x) (s • y) = r * s * mform x y := by
  rw [mform_apply, mform_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  have h1 : (∑ i, r * x (Sum.inl i) * (s * y (Sum.inl i))) =
      r * s * ∑ i, x (Sum.inl i) * y (Sum.inl i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h1]; ring

/-- `nvec ξ` is the null vector `theta ξ = (ξ,1)`. -/
lemma nvec_eq_theta (ξ : E n) : nvec ξ = theta ξ := rfl

/-- **The effective matrix of `g ∈ PO(n,1)`.**

* it moves the hyperboloid lift of a chart point `u` to that of `g • u`;
* it is an isometry of the Minkowski form `mink`;
* a boundary point `ξ` is fixed by `g` iff `nvec ξ` is an eigenvector of `mat (rep g)`. -/
theorem ematSpec {n : ℕ} (g : LeanEval.Geometry.MostowRigidity.PO n 1) :
    (∀ u : Submission.Mostow.E n, Matrix.mulVec (Work.Mostow.emat g) (Submission.Mostow.hlift u)
        = Submission.Mostow.hlift (g • u)) ∧
    (∀ x y : Fin n ⊕ Fin 1 → ℝ,
        Work.Mostow.mink (Matrix.mulVec (Work.Mostow.emat g) x)
          (Matrix.mulVec (Work.Mostow.emat g) y)
          = Work.Mostow.mink x y) ∧
    (∀ {ξ : Submission.Mostow.E n}, ξ ∈ Submission.Mostow.Sph n →
      (Submission.Mostow.bd g ξ = ξ ↔ ∃ c : ℝ,
        Matrix.mulVec (Submission.Mostow.mat (Submission.Mostow.rep g)) (Work.Mostow.nvec ξ)
          = c • Work.Mostow.nvec ξ)) := by
  refine ⟨?_, ?_, ?_⟩
  · -- the sheet lemma in matrix form
    intro u
    change Matrix.mulVec (emat g) (hlift u) = hlift (actO (rep g) u)
    rw [Submission.Mostow.Hyper.hlift_actO (rep g) u, emat, Matrix.smul_mulVec]
  · -- `emat g` is an isometry of the Minkowski form
    intro x y
    rw [mink_eq_mform, mink_eq_mform, emat, Matrix.smul_mulVec, Matrix.smul_mulVec,
      mform_smul, tsign_sq (rep g), one_mul]
    exact mform_mat_mulVec (rep g) x y
  · -- fixed boundary points are the eigen-directions of `mat (rep g)`
    intro ξ hξ
    change bdO (rep g) ξ = ξ ↔ ∃ c : ℝ, mat (rep g) *ᵥ nvec ξ = c • nvec ξ
    constructor
    · intro h
      -- the renormalisation of `mat (rep g) *ᵥ nvec ξ` is `ξ`, so that vector is a multiple of `nvec ξ`
      have ht : (mat (rep g) *ᵥ theta ξ) (Sum.inr 0) ≠ 0 :=
        mat_mulVec_theta_ne_zero (rep g) hξ
      have hw := smul_theta_of_time_ne_zero (mat (rep g) *ᵥ theta ξ) ht
      refine ⟨(mat (rep g) *ᵥ theta ξ) (Sum.inr 0), ?_⟩
      have hb : (WithLp.toLp 2 (fun i : Fin n =>
          (mat (rep g) *ᵥ theta ξ) (Sum.inl i) /
          (mat (rep g) *ᵥ theta ξ) (Sum.inr 0))) = bdO (rep g) ξ := rfl
      rw [hb, h] at hw
      show mat (rep g) *ᵥ theta ξ = (mat (rep g) *ᵥ theta ξ) (Sum.inr 0) • theta ξ
      exact hw
    · -- conversely an eigen-direction renormalises to `ξ`
      rintro ⟨c, hc⟩
      have hc' : mat (rep g) *ᵥ theta ξ = c • theta ξ := hc
      have ht : (mat (rep g) *ᵥ theta ξ) (Sum.inr 0) ≠ 0 :=
        mat_mulVec_theta_ne_zero (rep g) hξ
      have ht' : (mat (rep g) *ᵥ theta ξ) (Sum.inr 0) = c := by
        conv_lhs => rw [hc']
        simp [theta]
      have hcne : c ≠ 0 := by rw [← ht']; exact ht
      ext i
      rw [bdO_apply]
      have hinl : (mat (rep g) *ᵥ theta ξ) (Sum.inl i) = c * ξ i := by
        have h := congrFun hc' (Sum.inl i)
        have h2 : (c • theta ξ) (Sum.inl i) = c * ξ i := by simp [theta]
        rwa [h2] at h
      rw [hinl, ht', mul_div_cancel_left₀ _ hcne]

end

end Work.Mostow
