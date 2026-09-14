import Mathlib
import Submission.Subspace.Algebra
import Submission.Commons.Analysis.Normed.intVec_coord_norm_le_norm
import Submission.Commons.Analysis.Normed.intVec_norm_ge_one

/-!
# Interface: classical subspace theorem ⇒ challenge statement

The challenge statement is derived from the classical affine subspace theorem
in "normals form":

`SubspaceTheoremNormals σ L`: for every `ε > 0` there is a finite set `s` of
nonzero integer tuples such that every *nonzero* integer point `x` with
`Small L ε x` satisfies `c·x = 0` for some `c ∈ s`.

Since the challenge hypothesis is *strict*, `x = 0` never satisfies it
(`small_zero_false`), and the classical theorem restricted to `x ≠ 0`
immediately gives the challenge statement (`normals_imp_challenge`).

`subspaces_imp_normals` converts the proper-`ℚ`-subspace form (the form in
which the classical theorem is usually proved) to the normals form: each
proper subspace is assigned a nonzero integer normal.
-/

open scoped BigOperators

namespace Submission.Subspace

section Interface

variable {σ : Type*} [Fintype σ]

/-- The strict "smallness" hypothesis of the subspace theorem for an integer
point `x`. -/
def Small (L : σ → σ → ℂ) (ε : ℝ) (x : σ → ℤ) : Prop :=
  ‖(∏ i : σ, ∑ j : σ, L i j * x j : ℂ)‖ < ‖x‖ ^ (-ε)

/-- Classical affine subspace theorem over `ℚ` (normals form, strict
inequality). -/
def SubspaceTheoremNormals (σ : Type*) [Fintype σ] (L : σ → σ → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ s : Finset (σ → ℤ),
    (0 : σ → ℤ) ∉ s ∧
      ∀ x : σ → ℤ, x ≠ 0 → Small L ε x → ∃ c ∈ s, (∑ i, c i * x i : ℤ) = 0

/-- Classical affine subspace theorem over `ℚ` (proper-subspace form). -/
def SubspaceTheoremSubspaces (σ : Type*) [Fintype σ] (L : σ → σ → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ T : Set (Submodule ℚ (σ → ℚ)),
    T.Finite ∧ (∀ W ∈ T, W ≠ ⊤) ∧
      ∀ x : σ → ℤ, x ≠ 0 → Small L ε x →
        ∃ W ∈ T, (fun i : σ => (x i : ℚ)) ∈ W

/-- The smallness condition is monotone in the exponent: a smaller exponent gives a
stronger hypothesis (for nonzero integer points, where `‖x‖ ≥ 1`). -/
theorem small_mono_exp (L : σ → σ → ℂ) {ε ε' : ℝ} (h : ε' ≤ ε) {x : σ → ℤ}
    (hx : x ≠ 0) (hs : Small L ε x) : Small L ε' x := by
  unfold Small at *
  have h1 : (1 : ℝ) ≤ ‖x‖ :=
    Commons.Analysis.Normed.intVec_norm_ge_one x hx
  have hpow : ‖x‖ ^ (-ε) ≤ ‖x‖ ^ (-ε') :=
    Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
  linarith

/-- `x = 0` never satisfies the strict hypothesis. -/
theorem small_zero_false (L : σ → σ → ℂ) (ε : ℝ) (hε : 0 < ε) :
    ¬ Small L ε (0 : σ → ℤ) := by
  intro h
  have hR : ‖(0 : σ → ℤ)‖ ^ (-ε) = 0 := by
    rw [Real.rpow_def_of_nonneg (show (0 : ℝ) ≤ ‖(0 : σ → ℤ)‖ by simp)]
    have hne : -ε ≠ 0 := by linarith
    simp [hne]
  have hnonneg : (0 : ℝ) ≤ ‖(∏ i : σ, ∑ j : σ, L i j * (0 : ℤ) : ℂ)‖ := by positivity
  unfold Small at h
  rw [hR] at h
  exact (not_lt_of_ge hnonneg) h

/-- Integer linear equation: vanishing over `ℤ` is equivalent to vanishing
after casting to `ℚ`. -/
theorem int_sum_eq_zero_iff_rat (c : σ → ℤ) (x : σ → ℤ) :
    ((∑ i, c i * x i : ℤ) : ℚ) = 0 ↔ (∑ i, (c i : ℚ) * (x i : ℚ)) = 0 := by
  have hcast : (∑ i, (c i : ℚ) * (x i : ℚ)) = ((∑ i, c i * x i : ℤ) : ℚ) := by
    norm_num [Int.cast_mul, Int.cast_sum]
  rw [hcast]

/-- The normals form of the classical subspace theorem implies the challenge
statement (which drops the `x ≠ 0` condition; that case is empty). -/
theorem normals_imp_challenge (σ : Type*) [Fintype σ] (_hσ : 2 ≤ Fintype.card σ)
    (L : σ → σ → ℂ) (hst : SubspaceTheoremNormals σ L) :
    ∀ (ε : ℝ) (_hε : 0 < ε),
      ∃ s : Finset (σ → ℤ), (0 : σ → ℤ) ∉ s ∧
        ∀ x : σ → ℤ, Small L ε x → ∃ c ∈ s, (∑ i, c i * x i : ℤ) = 0 := by
  intro ε hε
  rcases hst ε hε with ⟨s, hs0, hs⟩
  refine ⟨s, hs0, ?_⟩
  intro x hx
  by_cases hx0 : x = 0
  · subst x
    exact (small_zero_false L ε hε hx).elim
  · exact hs x hx0 hx

/-- The norm of an integer, viewed in `ℂ`, equals its norm in `ℤ` (both are
`|n|`). -/
theorem complex_norm_int (n : ℤ) : ‖(n : ℂ)‖ = ‖n‖ := by
  rw [Int.norm_eq_abs]
  norm_num

/-- Norm of a product of complex numbers is the product of the norms. -/
theorem prod_norm_complex {τ : Type*} [Fintype τ] (z : τ → ℂ) :
    ‖∏ i, z i‖ = ∏ i, ‖z i‖ := by
  simpa using (Complex.norm_prod (Finset.univ : Finset τ) z)

/-- The smallness hypothesis for `x` is precisely smallness of the product of
the norms of the linear forms evaluated at `x`. -/
theorem small_iff_prod (L : σ → σ → ℂ) (ε : ℝ) (x : σ → ℤ) :
    Small L ε x ↔ (∏ i : σ, ‖(∑ j : σ, L i j * x j : ℂ)‖) < ‖x‖ ^ (-ε) := by
  unfold Small
  rw [prod_norm_complex]

/-- Each linear form value is bounded on the sup-norm box: for all `x` and all
`i`, `‖(L·x)ᵢ‖ ≤ (∑ⱼ ‖L i j‖) · ‖x‖`. -/
theorem linearForm_bound (L : σ → σ → ℂ) (x : σ → ℤ) (i : σ) :
    ‖(∑ j : σ, L i j * (x j : ℂ) : ℂ)‖ ≤ (∑ j : σ, ‖L i j‖) * ‖x‖ := by
  calc
    ‖(∑ j : σ, L i j * (x j : ℂ) : ℂ)‖ ≤ ∑ j : σ, ‖L i j * (x j : ℂ)‖ := by
      exact norm_sum_le _ _
    _ ≤ ∑ j : σ, ‖L i j‖ * ‖(x j : ℂ)‖ := by
      apply Finset.sum_le_sum
      intro j hj
      exact norm_mul_le _ _
    _ ≤ ∑ j : σ, ‖L i j‖ * ‖x‖ := by
      apply Finset.sum_le_sum
      intro j hj
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      calc
        ‖(x j : ℂ)‖ = ‖x j‖ := complex_norm_int (x j)
        _ ≤ ‖x‖ := by
          simpa using (Commons.Analysis.Normed.intVec_coord_norm_le_norm x j)
    _ = (∑ j : σ, ‖L i j‖) * ‖x‖ := by
      rw [mul_comm, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [mul_comm]

/-- The non-strict (`≤`) form implies the strict (`<`) form. -/
theorem normalsLe_imp_normals (σ : Type*) [Fintype σ] (L : σ → σ → ℂ)
    (hst : ∀ ε : ℝ, 0 < ε → ∃ s : Finset (σ → ℤ),
      (0 : σ → ℤ) ∉ s ∧ ∀ x : σ → ℤ, x ≠ 0 →
        ‖(∏ i : σ, ∑ j : σ, L i j * x j : ℂ)‖ ≤ ‖x‖ ^ (-ε) →
          ∃ c ∈ s, (∑ i, c i * x i : ℤ) = 0) :
    SubspaceTheoremNormals σ L := by
  intro ε hε
  rcases hst ε hε with ⟨s, hs0, hs⟩
  refine ⟨s, hs0, ?_⟩
  intro x hx0 hx
  exact hs x hx0 (le_of_lt hx)

/-- The proper-subspace form implies the normals form. -/
theorem subspaces_imp_normals (σ : Type*) [Fintype σ] (L : σ → σ → ℂ)
    (hst : SubspaceTheoremSubspaces σ L) : SubspaceTheoremNormals σ L := by
  classical
  intro ε hε
  rcases hst ε hε with ⟨T, hTfin, hTprop, hTcov⟩
  let Tf : Finset (Submodule ℚ (σ → ℚ)) := hTfin.toFinset
  have hTf_prop (W : Submodule ℚ (σ → ℚ)) (hW : W ∈ Tf) : W ≠ ⊤ := by
    exact hTprop W ((hTfin.mem_toFinset).mp hW)
  have hsel (W : Submodule ℚ (σ → ℚ)) (hW : W ∈ Tf) :
      ∃ c : σ → ℤ, c ≠ 0 ∧ ∀ v : σ → ℚ, v ∈ W → (∑ i, (c i : ℚ) * v i) = 0 :=
    exists_int_normal_of_proper W (hTf_prop W hW)
  let c : Submodule ℚ (σ → ℚ) → σ → ℤ := fun W =>
    if hW : W ∈ Tf then Classical.choose (hsel W hW) else 0
  have hc (W : Submodule ℚ (σ → ℚ)) (hW : W ∈ Tf) :
      c W ≠ 0 ∧ ∀ v : σ → ℚ, v ∈ W → (∑ i, ((c W i : ℚ)) * v i) = 0 := by
    have h := Classical.choose_spec (hsel W hW)
    simpa [c, hW] using h
  let s : Finset (σ → ℤ) := Tf.image c
  refine ⟨s, ?_, ?_⟩
  · intro hs0
    rw [Finset.mem_image] at hs0
    rcases hs0 with ⟨W, hW, hc0⟩
    have hcne := (hc W hW).1
    exact hcne hc0
  · intro x hx0 hx
    rcases hTcov x hx0 hx with ⟨W, hWT, hxW⟩
    have hWf : W ∈ Tf := (hTfin.mem_toFinset).mpr hWT
    have hcv := (hc W hWf).2 (fun i : σ => (x i : ℚ)) hxW
    refine ⟨c W, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨W, hWf, rfl⟩
    · exact_mod_cast ((int_sum_eq_zero_iff_rat (c W) x).mpr hcv)

end Interface

end Submission.Subspace
