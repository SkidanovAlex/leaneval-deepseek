import Mathlib
import Submission.Mostow.Interfaces
import Submission.Work.Mostow.Hyper
import Submission.Work.Mostow.HaarBoost
import Submission.Work.Mostow.segfunSpeed
import Submission.Work.Mostow.smulGH
import Submission.Work.Mostow.smulContDiff
import Submission.Work.Mostow.areaFormula

/-!
# Auxiliary lemmas towards `HypIsometryProp`

Assembled by the `hypIsometry` agent (area T2).  Everything here is proved from `POActionProp`
(or unconditionally), using the shared library under `Submission/Work/Mostow/`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory Hyper Matrix

noncomputable section

variable {n : ℕ}

/-! ## Transitivity and invariance -/

/-- Transitivity of the `PO n 1`-action on the chart: the explicit boost moves `0` to `v`. -/
theorem smulZeroSurj' (hA : POActionProp n) (v : E n) : ∃ g : PO n 1, g • 0 = v :=
  ⟨((boost v : O1 n) : PO n 1), boost_smul_zero hA v⟩

/-- A group element sending a prescribed point to the base point. -/
theorem smulEqZero' (hA : POActionProp n) (v : E n) : ∃ g : PO n 1, g • v = 0 := by
  have hone := hA.2.2.2.1
  have hmul := hA.2.2.2.2.1
  obtain ⟨g, hg⟩ := smulZeroSurj' hA v
  refine ⟨g⁻¹, ?_⟩
  calc g⁻¹ • v = g⁻¹ • (g • 0) := by rw [hg]
    _ = (g⁻¹ * g) • 0 := (hmul g⁻¹ g 0).symm
    _ = 0 := by rw [inv_mul_cancel, hone]

/-- The action of `PO n 1` preserves `hdist` (clause 7 of `HypIsometryProp`). -/
theorem hdist_smul' (hA : POActionProp n) (g : PO n 1) (u v : E n) :
    hdist (g • u) (g • v) = hdist u v :=
  congrArg Real.arcosh (cc_actO (rep g) u v)

/-! ## The triangle inequality -/

lemma cosh_hdist_zero_left (u : E n) : Real.cosh (hdist u 0) = tpart u := by
  rw [cosh_hdist]
  simp [tpart]

lemma sinh_hdist_zero_left (u : E n) : Real.sinh (hdist u 0) = ‖u‖ := by
  have h2 : Real.sinh (hdist u 0) ^ 2 = ‖u‖ ^ 2 := by
    rw [Real.sinh_sq, cosh_hdist_zero_left, sq_tpart]
    ring
  have h1 : 0 ≤ Real.sinh (hdist u 0) := Real.sinh_nonneg_iff.2 (hdist_nonneg u 0)
  nlinarith [h1, h2, norm_nonneg u]

/-- The triangle inequality with the base point as the middle point. -/
lemma hdist_le_add_zero (u w : E n) : hdist u w ≤ hdist u 0 + hdist 0 w := by
  have hcosh : Real.cosh (hdist u w) ≤ Real.cosh (hdist u 0 + hdist 0 w) := by
    rw [cosh_hdist, Real.cosh_add, cosh_hdist_zero_left, sinh_hdist_zero_left,
      cosh_hdist_zero, sinh_hdist_zero]
    have hneg : -inner ℝ u w ≤ ‖u‖ * ‖w‖ := by
      have h := (abs_le.mp (abs_real_inner_le_norm u w)).1
      linarith
    linarith
  have h := Real.cosh_le_cosh.mp hcosh
  rwa [abs_of_nonneg (hdist_nonneg u w),
    abs_of_nonneg (add_nonneg (hdist_nonneg u 0) (hdist_nonneg 0 w))] at h

/-- The triangle inequality (clause 4 of `HypIsometryProp`). -/
theorem hdistTriangle' (hA : POActionProp n) (u v w : E n) :
    hdist u w ≤ hdist u v + hdist v w := by
  obtain ⟨g, hg⟩ := smulEqZero' hA v
  have h2 : hdist (g • u) 0 = hdist u v := by rw [← hg, hdist_smul' hA g u v]
  have h3 : hdist 0 (g • w) = hdist v w := by rw [← hg, hdist_smul' hA g v w]
  calc hdist u w = hdist (g • u) (g • w) := (hdist_smul' hA g u w).symm
    _ ≤ hdist (g • u) 0 + hdist 0 (g • w) := hdist_le_add_zero _ _
    _ = hdist u v + hdist v w := by rw [h2, h3]

/-! ## Distance-preserving maps fixing the base point -/

/-- A distance-preserving self-map fixing `0` preserves the time coordinate. -/
lemma tpart_isom_zero (F : E n → E n) (hF : ∀ u v, hdist (F u) (F v) = hdist u v)
    (h0 : F 0 = 0) (u : E n) : tpart (F u) = tpart u := by
  have h := hF u 0
  rw [h0] at h
  have h2 : Real.arcosh (tpart (F u)) = Real.arcosh (tpart u) := by
    simpa [hdist, tpart] using h
  exact le_antisymm
    ((Real.arcosh_le_arcosh (tpart_pos _) (tpart_pos _)).mp (le_of_eq h2))
    ((Real.arcosh_le_arcosh (tpart_pos _) (tpart_pos _)).mp (le_of_eq h2.symm))

/-- A distance-preserving self-map fixing `0` preserves the inner product (clause 8a). -/
theorem isomZeroInner' (F : E n → E n) (hF : ∀ u v, hdist (F u) (F v) = hdist u v)
    (h0 : F 0 = 0) : ∀ u v, inner ℝ (F u) (F v) = inner ℝ u v := by
  have htpart := tpart_isom_zero F hF h0
  intro u v
  have hcc : tpart (F u) * tpart (F v) - inner ℝ (F u) (F v) =
      tpart u * tpart v - inner ℝ u v := by
    have h := hF u v
    have h2 : Real.cosh (hdist (F u) (F v)) = Real.cosh (hdist u v) := by rw [h]
    rwa [cosh_hdist, cosh_hdist] at h2
  rw [htpart u, htpart v] at hcc
  linarith

/-- A self-map fixing `0` and preserving the inner product is the underlying function of a
linear map (clause 8b). -/
theorem innerPresLinear' (F : E n → E n) (h0 : F 0 = 0)
    (hF : ∀ u v, inner ℝ (F u) (F v) = inner ℝ u v) :
    ∃ Q : E n →ₗ[ℝ] E n, ∀ u, Q u = F u := by
  have hnorm : ∀ u, ‖F u‖ = ‖u‖ := by
    intro u
    have h2 : ‖F u‖ ^ 2 = ‖u‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, hF u u]
    nlinarith [h2, norm_nonneg (F u), norm_nonneg u]
  have hadd : ∀ x y, F (x + y) = F x + F y := by
    intro x y
    have h : ‖F (x + y) - F x - F y‖ ^ 2 = 0 := by
      rw [← real_inner_self_eq_norm_sq]
      simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right, hF]
      ring
    have h1 : F (x + y) - F x - F y = 0 := by
      rw [← norm_eq_zero, ← sq_eq_zero_iff]; exact h
    rw [sub_eq_zero] at h1
    have h2 : F (x + y) = F y + F x := eq_add_of_sub_eq h1
    rwa [add_comm (F y)] at h2
  have hsmul : ∀ (c : ℝ) (x : E n), F (c • x) = c • F x := by
    intro c x
    have h : ‖F (c • x) - c • F x‖ ^ 2 = 0 := by
      rw [← real_inner_self_eq_norm_sq]
      simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
        real_inner_smul_right, hF]
      ring
    have h1 : F (c • x) - c • F x = 0 := by
      rw [← norm_eq_zero, ← sq_eq_zero_iff]; exact h
    exact sub_eq_zero.mp h1
  exact ⟨{ toFun := F, map_add' := hadd, map_smul' := hsmul }, fun u => rfl⟩

/-! ## Realising linear isometries by `PO n 1` -/

/-- A norm-preserving linear endomorphism of the chart is realised by the action of `PO n 1`
(clause 8c). -/
theorem linearIsomSmul' (hA : POActionProp n) (Q : E n →ₗ[ℝ] E n) (hQ : ∀ u, ‖Q u‖ = ‖u‖) :
    ∃ g : PO n 1, ∀ u, g • u = Q u := by
  have hQi : ∀ u v, inner ℝ (Q u) (Q v) = inner ℝ u v :=
    (LinearMap.norm_map_iff_inner_map_map Q).mp hQ
  set b : OrthonormalBasis (Fin n) ℝ (E n) := EuclideanSpace.basisFun (Fin n) ℝ with hbdef
  set Qm : Matrix (Fin n) (Fin n) ℝ := fun i j => (Q (b j)) i with hQmdef
  have hbasis : ∀ u : E n, u = ∑ j, (u j) • b j := by
    intro u
    conv_lhs => rw [← OrthonormalBasis.sum_repr b u]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hc : (b.repr u).ofLp j = u j := by
      rw [hbdef]
      exact EuclideanSpace.basisFun_repr (Fin n) ℝ u j
    rw [hc]
  have hQu : ∀ u : E n, (fun i => (Q u) i) = Qm *ᵥ (fun i => u i) := by
    intro u
    have h1 : Q u = ∑ j, (u j) • Q (b j) := by
      conv_lhs => rw [hbasis u]
      rw [map_sum]
      exact Finset.sum_congr rfl fun j _ => map_smul Q (u j) _
    funext i
    rw [h1, WithLp.ofLp_sum, Finset.sum_apply, Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun j _ => by
      simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, hQmdef]; ring
  have hQm_orth : Qm.transpose * Qm = 1 := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.one_apply, Matrix.transpose_apply]
    rw [show (∑ k, Qm k i * Qm k j) = ∑ k, (Q (b i)) k * (Q (b j)) k from
      Finset.sum_congr rfl fun k _ => by rw [hQmdef]]
    rw [← Hyper.inner_eq_sum, hQi, OrthonormalBasis.inner_eq_ite]
  set M : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ :=
    Matrix.fromBlocks Qm 0 0 (1 : Matrix (Fin 1) (Fin 1) ℝ) with hMdef
  have hMconj : M.transpose * (pmOneMat (p := Fin n) (q := Fin 1) (α := ℝ)) * M = pmOneMat := by
    rw [hMdef, show (pmOneMat (p := Fin n) (q := Fin 1) (α := ℝ)) =
      Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 (-1 : Matrix (Fin 1) (Fin 1) ℝ)
      from rfl]
    rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one,
      Matrix.transpose_zero, Matrix.transpose_one, Matrix.zero_mul, Matrix.mul_neg,
      neg_zero, Matrix.one_mul]
    rw [hQm_orth]
  set Ms : MatrixSum (Fin n) (Fin 1) ℝ := M with hMsdef
  have hstar : star Ms * Ms = 1 := by
    have hmatrix : ((pmOneMat (p := Fin n) (q := Fin 1) (α := ℝ)) * M.transpose *
        (pmOneMat (p := Fin n) (q := Fin 1) (α := ℝ))) * M = 1 := by
      rw [show ((pmOneMat (p := Fin n) (q := Fin 1) (α := ℝ)) * M.transpose *
          (pmOneMat (p := Fin n) (q := Fin 1) (α := ℝ))) * M =
          (pmOneMat (p := Fin n) (q := Fin 1) (α := ℝ)) *
            (M.transpose * (pmOneMat (p := Fin n) (q := Fin 1) (α := ℝ)) * M) from by
        noncomm_ring]
      rw [hMconj, pmOneMat_mul_pmOneMat]
    rw [hMsdef]
    exact hmatrix
  haveI : IsDedekindFiniteMonoid (MatrixSum (Fin n) (Fin 1) ℝ) :=
    inferInstanceAs (IsDedekindFiniteMonoid (Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ))
  have hMem : Ms ∈ unitary (MatrixSum (Fin n) (Fin 1) ℝ) := by
    rw [Unitary.mem_iff]
    exact ⟨hstar, (mul_eq_one_comm (a := star Ms) (b := Ms)).mp hstar⟩
  let A : O1 n := ⟨Ms, hMem⟩
  have hmat : (mat A : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ) = M := by
    change Ms = M
    rw [hMsdef]
  have hts : tsign A = 1 := by
    rw [tsign]
    have h00 : (mat A) (Sum.inr 0) (Sum.inr 0) = 1 := by
      rw [hmat]
      change (Matrix.fromBlocks Qm 0 0 (1 : Matrix (Fin 1) (Fin 1) ℝ)) (Sum.inr 0) (Sum.inr 0) = 1
      rw [Matrix.fromBlocks_apply₂₂, Matrix.one_apply_eq]
    rw [h00]
    norm_num
  have hMhlift : ∀ u : E n, M *ᵥ hlift u = hlift (Q u) := by
    intro u
    change (Matrix.fromBlocks Qm 0 0 (1 : Matrix (Fin 1) (Fin 1) ℝ)) *ᵥ hlift u = hlift (Q u)
    funext z
    rcases z with i | j
    · rw [Matrix.mulVec, dotProduct, Fintype.sum_sum_type]
      simp only [hlift, Sum.elim_inl, Sum.elim_inr, Matrix.fromBlocks_apply₁₁,
        Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, mul_zero, Finset.sum_const_zero, add_zero]
      simpa [Matrix.mulVec, dotProduct] using (congrFun (hQu u) i).symm
    · fin_cases j
      rw [Matrix.mulVec, dotProduct, Fintype.sum_sum_type]
      simp only [hlift, Sum.elim_inl, Sum.elim_inr, Matrix.fromBlocks_apply₂₁,
        Matrix.fromBlocks_apply₂₂, Matrix.one_apply, zero_mul, Finset.sum_const_zero, zero_add,
        one_mul]
      simp [tpart, hQ u]
  refine ⟨(A : PO n 1), fun u => ?_⟩
  rw [hA.2.1, actO, hmat, hts]
  simp only [one_mul, hMhlift]
  exact spat_hlift (Q u)

/-! ## Assembly of the surjectivity clause -/

/-- A distance-preserving self-map of the chart is the action of an element of `PO n 1`
(clause 8 of `HypIsometryProp`). -/
theorem isomEqSmul' (hA : POActionProp n) (F : E n → E n)
    (hF : ∀ u v, hdist (F u) (F v) = hdist u v) : ∃ g : PO n 1, ∀ u, F u = g • u := by
  have hone := hA.2.2.2.1
  have hmul := hA.2.2.2.2.1
  obtain ⟨g₁, hg₁⟩ := smulZeroSurj' hA (F 0)
  have hF₁0 : g₁⁻¹ • F 0 = 0 := by
    calc g₁⁻¹ • F 0 = g₁⁻¹ • (g₁ • 0) := by rw [hg₁]
      _ = (g₁⁻¹ * g₁) • 0 := (hmul g₁⁻¹ g₁ 0).symm
      _ = 0 := by rw [inv_mul_cancel, hone]
  have hF₁dist : ∀ u v, hdist (g₁⁻¹ • F u) (g₁⁻¹ • F v) = hdist u v := by
    intro u v
    rw [hdist_smul' hA g₁⁻¹ (F u) (F v), hF u v]
  have hin : ∀ u v, inner ℝ (g₁⁻¹ • F u) (g₁⁻¹ • F v) = inner ℝ u v :=
    isomZeroInner' _ hF₁dist hF₁0
  obtain ⟨Q, hQ⟩ := innerPresLinear' (fun u => g₁⁻¹ • F u) hF₁0 hin
  have hQnorm : ∀ u, ‖Q u‖ = ‖u‖ := by
    intro u
    have h1 : inner ℝ (Q u) (Q u) = inner ℝ u u := by rw [hQ u]; exact hin u u
    have h2 : ‖Q u‖ ^ 2 = ‖u‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, h1]
    nlinarith [h2, norm_nonneg (Q u), norm_nonneg u]
  obtain ⟨g₂, hg₂⟩ := linearIsomSmul' hA Q hQnorm
  refine ⟨g₁ * g₂, fun u => ?_⟩
  have h1 : g₁ • (g₁⁻¹ • F u) = F u := by
    rw [← hmul g₁ g₁⁻¹ (F u), mul_inv_cancel, hone]
  rw [hmul g₁ g₂ u, hg₂ u, hQ u]
  exact h1.symm

/-! ## The Jacobian of the action -/

/-- The standard orthonormal basis of the chart. -/
lemma inner_basisFun (x : E n) (i : Fin n) :
    inner ℝ ((EuclideanSpace.basisFun (Fin n) ℝ) i) x = x i := by
  rw [EuclideanSpace.basisFun_apply, Hyper.inner_eq_sum]
  rw [Finset.sum_eq_single i]
  · rw [EuclideanSpace.single_apply]; simp
  · intro b _ hb
    rw [EuclideanSpace.single_apply, if_neg hb, zero_mul]
  · intro h; exact absurd (Finset.mem_univ i) h

lemma basis_expand (u : E n) :
    u = ∑ j, (u j) • (EuclideanSpace.basisFun (Fin n) ℝ) j := by
  conv_lhs => rw [← OrthonormalBasis.sum_repr (EuclideanSpace.basisFun (Fin n) ℝ) u]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1

/-- The matrix of a linear endomorphism of the chart in the standard orthonormal basis. -/
abbrev matOf (L : E n →ₗ[ℝ] E n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => inner ℝ ((EuclideanSpace.basisFun (Fin n) ℝ) i)
    (L ((EuclideanSpace.basisFun (Fin n) ℝ) j))

lemma matOf_eq_toMatrix (L : E n →ₗ[ℝ] E n) :
    matOf L = LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin n) ℝ).toBasis L := by
  ext i j
  rw [LinearMap.toMatrix_apply]
  exact (OrthonormalBasis.repr_apply_apply (EuclideanSpace.basisFun (Fin n) ℝ)
    (L ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis j)) i).symm

lemma matOf_mulVec (L : E n →ₗ[ℝ] E n) (v : E n) :
    (fun i => (L v) i) = matOf L *ᵥ (fun i => v i) := by
  have h1 : L v = ∑ j, (v j) • L ((EuclideanSpace.basisFun (Fin n) ℝ) j) := by
    conv_lhs => rw [basis_expand v]
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => map_smul L (v j) _
  funext i
  rw [← inner_basisFun (L v) i, h1, inner_sum, Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [real_inner_smul_right]
  ring

lemma gram_transpose (u : E n) : (Hyper.gram u)ᵀ = Hyper.gram u := by
  ext i j
  simp only [Hyper.gram, Matrix.transpose_apply, Matrix.sub_apply, Matrix.one_apply,
    Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
  by_cases h : i = j
  · subst h; ring
  · rw [if_neg h, if_neg (Ne.symm h)]
    ring

lemma dot_single_mulVec_single (M : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    Pi.single i (1 : ℝ) ⬝ᵥ (M *ᵥ Pi.single j 1) = M i j := by
  simp only [dotProduct, Matrix.mulVec]
  rw [Finset.sum_eq_single i]
  · rw [Pi.single_eq_same, one_mul, Finset.sum_eq_single j]
    · rw [Pi.single_eq_same, mul_one]
    · intro b _ hb; rw [Pi.single_eq_of_ne hb, mul_zero]
    · intro h; exact absurd (Finset.mem_univ j) h
  · intro b _ hb; rw [Pi.single_eq_of_ne hb, zero_mul]
  · intro h; exact absurd (Finset.mem_univ i) h

lemma dot_mulVec_mulVec (A : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin n) ℝ)
    (x y : Fin n → ℝ) :
    (A *ᵥ x) ⬝ᵥ (G *ᵥ (A *ᵥ y)) = x ⬝ᵥ ((Aᵀ * G * A) *ᵥ y) := by
  rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, dotProduct_comm]

lemma quad_expand (G : Matrix (Fin n) (Fin n) ℝ) (hG : Gᵀ = G) (a b : Fin n → ℝ) :
    (a + b) ⬝ᵥ (G *ᵥ (a + b)) = a ⬝ᵥ (G *ᵥ a) + 2 * (a ⬝ᵥ (G *ᵥ b)) + b ⬝ᵥ (G *ᵥ b) := by
  rw [Matrix.mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add]
  have hcross : b ⬝ᵥ (G *ᵥ a) = a ⬝ᵥ (G *ᵥ b) := by
    have h := Matrix.dotProduct_transpose_mulVec G b a
    rwa [hG] at h
  linarith [hcross]

/-- A matrix identity from an identity of quadratic forms. -/
theorem quadForm_eq_matrix (G₁ G₂ : Matrix (Fin n) (Fin n) ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (h₁ : G₁ᵀ = G₁) (h₂ : G₂ᵀ = G₂)
    (h : ∀ w : Fin n → ℝ, (A *ᵥ w) ⬝ᵥ (G₂ *ᵥ (A *ᵥ w)) = w ⬝ᵥ (G₁ *ᵥ w)) :
    Aᵀ * G₂ * A = G₁ := by
  ext i j
  have h1 := h (Pi.single i (1 : ℝ) + Pi.single j 1)
  have h2 := h (Pi.single i (1 : ℝ))
  have h3 := h (Pi.single j (1 : ℝ))
  rw [Matrix.mulVec_add (A) (Pi.single i (1 : ℝ)) (Pi.single j 1)] at h1
  rw [quad_expand G₂ h₂ (A *ᵥ Pi.single i 1) (A *ᵥ Pi.single j 1),
    quad_expand G₁ h₁ (Pi.single i (1 : ℝ)) (Pi.single j 1)] at h1
  simp only [dot_mulVec_mulVec, dot_single_mulVec_single] at h1 h2 h3
  rw [← h2, ← h3] at h1
  linarith [h1]

/-- The absolute value of the determinant of the chart derivative of the action. -/
theorem abs_det_smul' (hA : POActionProp n) (g : PO n 1) (u : E n) :
    |(fderiv ℝ (fun w : E n => g • w) u).det| = tpart (g • u) / tpart u := by
  set L : E n →ₗ[ℝ] E n :=
    (((fderiv ℝ (fun w : E n => g • w) u) : E n →L[ℝ] E n) : E n →ₗ[ℝ] E n) with hL
  set Lm : Matrix (Fin n) (Fin n) ℝ := matOf L with hLm
  have hquad : ∀ v : E n, (fun i => (L v) i) ⬝ᵥ (Hyper.gram (g • u) *ᵥ (fun i => (L v) i)) =
      (fun i => v i) ⬝ᵥ (Hyper.gram u *ᵥ (fun i => v i)) := by
    intro v
    rw [← Hyper.gH_eq_gram (g • u) (L v), ← Hyper.gH_eq_gram u v]
    exact smulGH n hA g u v
  have hquad_mat : ∀ w : Fin n → ℝ,
      (Lm *ᵥ w) ⬝ᵥ (Hyper.gram (g • u) *ᵥ (Lm *ᵥ w)) = w ⬝ᵥ (Hyper.gram u *ᵥ w) := by
    intro w
    have h := hquad (WithLp.toLp 2 w)
    rw [matOf_mulVec] at h
    rw [← hLm] at h
    rw [show (fun i => (WithLp.toLp 2 w) i) = w from WithLp.ofLp_toLp 2 w] at h
    exact h
  have hMY : Lmᵀ * Hyper.gram (g • u) * Lm = Hyper.gram u :=
    quadForm_eq_matrix _ _ _ (gram_transpose _) (gram_transpose _) hquad_mat
  have hdet : Lm.det * (tpart (g • u) ^ 2)⁻¹ * Lm.det = (tpart u ^ 2)⁻¹ := by
    have h := congrArg Matrix.det hMY
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Hyper.det_gram,
      Hyper.det_gram] at h
    exact h
  have h2 : Lm.det ^ 2 = (tpart (g • u) / tpart u) ^ 2 := by
    have ha : tpart (g • u) ≠ 0 := tpart_ne_zero _
    have hb : tpart u ≠ 0 := tpart_ne_zero _
    field_simp at hdet ⊢
    nlinarith [hdet]
  have h3 : |Lm.det| = tpart (g • u) / tpart u := by
    have h := (sq_eq_sq_iff_abs_eq_abs Lm.det (tpart (g • u) / tpart u)).mp h2
    rwa [abs_of_nonneg (div_nonneg (le_of_lt (tpart_pos _)) (le_of_lt (tpart_pos _)))] at h
  have hdetL : (fderiv ℝ (fun w : E n => g • w) u).det = Lm.det := by
    change LinearMap.det L = Lm.det
    rw [hLm, matOf_eq_toMatrix]
    exact (LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis L).symm
  rw [hdetL]
  exact h3

/-- The hyperbolic Jacobian of the action of `PO n 1` is `1` (clause 11). -/
theorem hjac_smul' (hA : POActionProp n) (g : PO n 1) (u : E n) :
    hjac (fun w : E n => g • w) u = 1 := by
  rw [hjac_eq, abs_det_smul' hA g u]
  have h1 : tpart (g • u) ≠ 0 := tpart_ne_zero _
  have h2 : tpart u ≠ 0 := tpart_ne_zero _
  field_simp

/-- The action of `PO n 1` preserves hyperbolic volume (clause 12). -/
theorem measurePreserving_smul' (hA : POActionProp n) (g : PO n 1) :
    MeasurePreserving (fun u : E n => g • u) (volH n) (volH n) := by
  have hone := hA.2.2.2.1
  have hmul := hA.2.2.2.2.1
  have hcont : ContDiff ℝ 1 (fun u : E n => g • u) := smulContDiff n hA g
  have hcont' : ContDiff ℝ 1 (fun u : E n => g⁻¹ • u) := smulContDiff n hA g⁻¹
  have hinj : Set.InjOn (fun u : E n => g⁻¹ • u) Set.univ := by
    intro a _ b _ hab
    have hab' : g⁻¹ • a = g⁻¹ • b := hab
    calc a = g • (g⁻¹ • a) := by rw [← hmul g g⁻¹ a, mul_inv_cancel, hone]
      _ = g • (g⁻¹ • b) := by rw [hab']
      _ = b := by rw [← hmul g g⁻¹ b, mul_inv_cancel, hone]
  have hleb : ∀ u : E n, hjacLeb (fun w : E n => g⁻¹ • w) u = hdens u := by
    intro u
    have hpos : (0 : ℝ) < tpart (g⁻¹ • u) / tpart u := div_pos (tpart_pos _) (tpart_pos _)
    rw [hjacLeb, hdens, abs_det_smul' hA g⁻¹ u]
    rw [← ENNReal.ofReal_mul (le_of_lt hpos)]
    congr 1
    have h1 : tpart (g⁻¹ • u) ≠ 0 := tpart_ne_zero _
    have h2 : tpart u ≠ 0 := tpart_ne_zero _
    field_simp
  refine MeasureTheory.MeasurePreserving.mk hcont.continuous.measurable ?_
  refine MeasureTheory.Measure.ext fun s hs => ?_
  rw [Measure.map_apply hcont.continuous.measurable hs]
  have himg : (fun u : E n => g • u) ⁻¹' s = (fun u : E n => g⁻¹ • u) '' s := by
    ext u
    constructor
    · intro hu
      refine ⟨g • u, hu, ?_⟩
      change g⁻¹ • (g • u) = u
      rw [← hmul g⁻¹ g u, inv_mul_cancel, hone]
    · rintro ⟨v, hv, hveq⟩
      change g • u ∈ s
      rw [← hveq]
      change g • (g⁻¹ • v) ∈ s
      rw [← hmul g g⁻¹ v, mul_inv_cancel, hone]
      exact hv
  rw [himg]
  have h1 : volH n ((fun u : E n => g⁻¹ • u) '' s) =
      ∫⁻ u in s, hjacLeb (fun u : E n => g⁻¹ • u) u ∂(volume : Measure (E n)) :=
    volH_image_of_injOn hcont' hs (hinj.mono (Set.subset_univ s))
  rw [h1]
  simp_rw [hleb]
  exact (volHApply n hs).symm

end

end Work.Mostow
