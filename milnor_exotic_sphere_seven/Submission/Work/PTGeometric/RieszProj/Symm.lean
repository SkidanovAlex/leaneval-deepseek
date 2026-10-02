import Submission.Work.PTGeometric.RieszProj.Count

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The symmetrisation `symm`, the Grassmannian `Gr` and the domain `good`

API for the symmetrised part `symm A = (A + A†)/2`:

* it is self-adjoint, additive, and a contraction for the operator norm;
* it fixes the orthogonal projections `P ∈ Gr n k`;
* the set `good n k = ⋃_{P ∈ Gr n k} {A | ‖symm A - P‖ < 1/4}` is open, contains `Gr n k`, and
  contains every operator within `1/4` of `Gr n k`;
* `Phi P = P` for a projection `P`, and `Phi S ∈ Gr n k` for `S` within `1/4` of a member of
  `Gr n k` (the latter given the rank count `topCard_eq`).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped ContDiff InnerProduct
open Set Function MeasureTheory

namespace Work.PTGeometric

noncomputable section

variable {n k : ℕ}

lemma continuous_adjoint_clm : Continuous (fun A : EndOp n => (A† : EndOp n)) :=
  ContinuousLinearMap.adjoint.continuous

lemma norm_adjoint_map (A : EndOp n) : ‖(A† : EndOp n)‖ = ‖A‖ :=
  ContinuousLinearMap.adjoint.norm_map A

/-- `symm A = (A + A†)/2` is self-adjoint as a linear map. -/
lemma symm_isSymmetric (A : EndOp n) :
    ((symm A : EndOp n) : Amb n →ₗ[ℝ] Amb n).IsSymmetric := by
  intro x y
  show inner ℝ (symm A x) y = inner ℝ x (symm A y)
  have h1 : inner ℝ (symm A x) y
      = (2:ℝ)⁻¹ * (inner ℝ (A x) y + inner ℝ x (A y)) := by
    rw [symm, smul_apply, add_apply, real_inner_smul_left,
      inner_add_left, ContinuousLinearMap.adjoint_inner_left]
  have h2 : inner ℝ x (symm A y)
      = (2:ℝ)⁻¹ * (inner ℝ (A x) y + inner ℝ x (A y)) := by
    rw [symm, smul_apply, add_apply, real_inner_smul_right,
      inner_add_right, ContinuousLinearMap.adjoint_inner_right]
    ring
  rw [h1, h2]

/-- The adjoint of `symm A` is `symm A`. -/
lemma adjoint_symm (A : EndOp n) : ContinuousLinearMap.adjoint (symm A) = symm A :=
  LinearMap.IsSymmetric.clm_adjoint_eq (symm_isSymmetric A)

lemma adjoint_sub_clm (A P : EndOp n) :
    ContinuousLinearMap.adjoint (A - P)
      = ContinuousLinearMap.adjoint A - ContinuousLinearMap.adjoint P :=
  map_sub _ _ _

/-- `symm` is additive. -/
lemma symm_sub_symm (A P : EndOp n) : symm A - symm P = symm (A - P) := by
  have h1 := adjoint_sub_clm A P
  have key : (2:ℝ) • (symm A - symm P) = (2:ℝ) • symm (A - P) := by
    simp only [symm, smul_sub, smul_add, smul_smul, h1, one_smul,
      mul_inv_cancel₀ (show (2:ℝ) ≠ 0 by norm_num)]
    abel
  have key2 := congrArg (fun Z : EndOp n => (2:ℝ)⁻¹ • Z) key
  rw [smul_smul, smul_smul, show (2:ℝ)⁻¹ * 2 = 1 by norm_num, one_smul, one_smul] at key2
  exact key2

/-- `symm` is a contraction. -/
lemma norm_symm_le (A : EndOp n) : ‖symm A‖ ≤ ‖A‖ := by
  have h2 : (0:ℝ) < (2:ℝ)⁻¹ := by norm_num
  calc ‖symm A‖ = (2:ℝ)⁻¹ * ‖A + A†‖ := by
        rw [symm, norm_smul, Real.norm_eq_abs, abs_of_pos h2]
    _ ≤ (2:ℝ)⁻¹ * (‖A‖ + ‖A†‖) := by
        gcongr
        exact norm_add_le _ _
    _ = ‖A‖ := by
        rw [norm_adjoint_map]
        ring

lemma norm_symm_sub_le (A P : EndOp n) : ‖symm A - symm P‖ ≤ ‖A - P‖ := by
  rw [symm_sub_symm]
  exact norm_symm_le (A - P)

lemma continuous_symm : Continuous (fun A : EndOp n => symm A) := by
  have h : Continuous fun A : EndOp n => A + A† := continuous_id.add continuous_adjoint_clm
  have h2 : Continuous fun A : EndOp n => (2:ℝ)⁻¹ • (A + A†) :=
    (continuous_const_smul ((2:ℝ)⁻¹)).comp h
  simpa only [symm, Function.comp_def] using h2

/-- `symm` fixes the orthogonal projections. -/
lemma symm_eq_self_of_mem_Gr {P : EndOp n} (hP : P ∈ Gr n k) : symm P = P := by
  rw [symm, hP.1, ← two_smul ℝ P, smul_smul]
  norm_num

/-- The domain of the retraction is open. -/
lemma isOpen_good (n k : ℕ) : IsOpen (good n k) := by
  rw [good]
  refine isOpen_iUnion fun P => isOpen_iUnion fun _ => ?_
  exact isOpen_Iio.preimage ((continuous_symm.sub continuous_const).norm)

lemma mem_good_iff {A : EndOp n} :
    A ∈ good n k ↔ ∃ P ∈ Gr n k, ‖symm A - P‖ < 1/4 := by
  simp [good]

lemma Gr_subset_good : Gr n k ⊆ good n k := fun P hP => by
  rw [mem_good_iff]
  refine ⟨P, hP, ?_⟩
  rw [symm_eq_self_of_mem_Gr hP]
  norm_num

/-- Every operator within `1/4` of `Gr n k` lies in `good n k`. -/
lemma good_of_dist {A P : EndOp n} (hP : P ∈ Gr n k) (h : ‖A - P‖ < 1/4) : A ∈ good n k := by
  rw [mem_good_iff]
  refine ⟨P, hP, ?_⟩
  have h1 : ‖symm A - symm P‖ ≤ ‖A - P‖ := norm_symm_sub_le A P
  rw [symm_eq_self_of_mem_Gr hP] at h1
  linarith

lemma finrank_amb (n : ℕ) : Module.finrank ℝ (Amb n) = n := finrank_euclideanSpace_fin

/-- `Phi` fixes the orthogonal projections. -/
lemma Phi_eq_self_of_mem_Gr {P : EndOp n} (hP : P ∈ Gr n k)
    (hn : Module.finrank ℝ (Amb n) = n) : Phi P = P := by
  have hPsym : ((P : EndOp n) : Amb n →ₗ[ℝ] Amb n).IsSymmetric := by
    intro x y
    show inner ℝ (P x) y = inner ℝ x (P y)
    rw [← ContinuousLinearMap.adjoint_inner_right P x y, hP.1]
  have hCl : Cluster P := Cluster.of_dist hP (by norm_num)
  have hev : ∀ i : Fin n, hPsym.eigenvalues hn i = 0 ∨ hPsym.eigenvalues hn i = 1 := by
    intro i
    have hne : hPsym.eigenvectorBasis hn i ≠ 0 :=
      (hPsym.eigenvectorBasis hn).orthonormal.ne_zero i
    have hb : P (hPsym.eigenvectorBasis hn i)
        = hPsym.eigenvalues hn i • hPsym.eigenvectorBasis hn i :=
      hPsym.apply_eigenvectorBasis hn i
    have h2 : (P * P : EndOp n) (hPsym.eigenvectorBasis hn i)
        = P (hPsym.eigenvectorBasis hn i) := by rw [hP.2.1]
    rw [ContinuousLinearMap.mul_apply, hb, map_smul, hb] at h2
    have h3 : (hPsym.eigenvalues hn i * hPsym.eigenvalues hn i - hPsym.eigenvalues hn i) •
        hPsym.eigenvectorBasis hn i = 0 := by
      rw [sub_smul, sub_eq_zero]
      simpa only [smul_smul] using h2
    rcases smul_eq_zero.mp h3 with h4 | h4
    · have h5 : hPsym.eigenvalues hn i * (hPsym.eigenvalues hn i - 1) = 0 := by linarith
      rcases mul_eq_zero.mp h5 with h6 | h6
      · exact Or.inl h6
      · exact Or.inr (by linarith)
    · exact absurd h4 hne
  have hchi : ∀ i : Fin n, chi (hPsym.eigenvalues hn i) = hPsym.eigenvalues hn i := by
    intro i
    rcases hev i with h5 | h5
    · rw [h5]
      norm_num [chi]
    · rw [h5]
      norm_num [chi]
  have hb : ∀ i : Fin n, P (hPsym.eigenvectorBasis hn i)
      = hPsym.eigenvalues hn i • hPsym.eigenvectorBasis hn i :=
    fun i => hPsym.apply_eigenvectorBasis hn i
  refine ContinuousLinearMap.ext fun x => ?_
  rw [Phi_apply_eq hPsym hCl hn x]
  conv_rhs => rw [← sum_repr_inner hPsym hn x]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, hb i, hchi i, smul_smul, mul_comm]

/-- `Phi S` is the orthogonal projection of rank `k` when `S` is within `1/4` of `Gr n k`. -/
lemma Phi_mem_Gr_of_topCard {S P : EndOp n}
    (hSsym : (S : Amb n →ₗ[ℝ] Amb n).IsSymmetric) (hn : Module.finrank ℝ (Amb n) = n)
    (hP : P ∈ Gr n k) (h : ‖S - P‖ < 1/4) (htop : topCard S hSsym hn = k) :
    Phi S ∈ Gr n k := by
  have hCl : Cluster S := Cluster.of_dist hP h
  refine ⟨?_, ?_, ?_⟩
  · exact LinearMap.IsSymmetric.clm_adjoint_eq (Phi_isSymmetric hSsym hCl hn)
  · exact Phi_mul_self hSsym hCl hn
  · rw [trace_Phi_eq_topCard hSsym hCl hn, htop]

end

end Work.PTGeometric
