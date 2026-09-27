import Mathlib
import Submission.Work.Mostow.gapA.ogAux
import Submission.Work.Mostow.gapA.ogAux2

/-!
# The orthonormal basis of the normal plane and the determinant of the normal action

* `pb_exists`: existence of an orthonormal basis `PB a b` of the normal plane;
* `rotMat_det_ogAux3`: the normal action of an element of `AxisSub` has determinant `1`.
-/

namespace Work.Mostow.gapA

open Submission.Mostow LeanEval.Geometry.MostowRigidity
open _root_.Matrix

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

noncomputable section

variable {a b : E 3}

/-! ## Existence of an orthonormal basis of the normal plane -/

theorem pb_exists (a b : Submission.Mostow.E 3) (ha : a ∈ Submission.Mostow.Sph 3)
    (hb : b ∈ Submission.Mostow.Sph 3) (hab : a ≠ b) :
    ∃ B : Work.Mostow.gapA.PB a b, True := by
  classical
  obtain ⟨e1, he1a, he1b, he11⟩ := perpNullUnit (n := 3) (by norm_num) ha hb hab
  have hm11 : mink e1 e1 = 1 := by rw [mink_eq_mform]; exact he11
  have hmem1 : e1 ∈ NormP a b := by
    refine mem_NormP.mpr ⟨?_, ?_⟩
    · rw [mink_eq_mform, nvec_eq_theta]; exact he1a
    · rw [mink_eq_mform, nvec_eq_theta]; exact he1b
  let T : (Fin 3 ⊕ Fin 1 → ℝ) →ₗ[ℝ] ℝ × ℝ × ℝ :=
    { toFun := fun x => (mink x (nvec a), mink x (nvec b), mink x e1)
      map_add' := by intro x y; simp [minkSeg_add_left]
      map_smul' := by intro c x; simp [mink_smul_left''] }
  have hlt : Module.finrank ℝ (ℝ × ℝ × ℝ) < Module.finrank ℝ (Fin 3 ⊕ Fin 1 → ℝ) := by
    simp [Module.finrank_prod, Module.finrank_self, Module.finrank_fintype_fun_eq_card,
      Fintype.card_sum, Fintype.card_fin, Fintype.card_unique]
  obtain ⟨y, hyker, hyne⟩ := (Submodule.ne_bot_iff (LinearMap.ker T)).mp
    (LinearMap.ker_ne_bot_of_finrank_lt (f := T) hlt)
  have hy0 := (LinearMap.mem_ker).mp hyker
  have hya : mink y (nvec a) = 0 := congrArg Prod.fst hy0
  have hyb : mink y (nvec b) = 0 := congrArg (fun z : ℝ × ℝ × ℝ => z.2.1) hy0
  have hye : mink y e1 = 0 := congrArg (fun z : ℝ × ℝ × ℝ => z.2.2) hy0
  have hymem : y ∈ NormP a b := mem_NormP.mpr ⟨hya, hyb⟩
  have hypos : 0 < mink y y := by
    rcases lt_or_eq_of_le (mink_self_nonneg_of_mem_NormP ha hymem) with h | h
    · exact h
    · exact absurd (eq_zero_of_mem_NormP_of_mink_self_eq_zero ha hb hab hymem h.symm) hyne
  set r : ℝ := Real.sqrt (mink y y) with hr
  have hr2 : r * r = mink y y := by
    rw [hr, ← sq, Real.sq_sqrt (le_of_lt hypos)]
  have hrne : r ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hypos)
  set e2 : Fin 3 ⊕ Fin 1 → ℝ := r⁻¹ • y with he2
  have hmem2 : e2 ∈ NormP a b := (NormP a b).smul_mem _ hymem
  have h22 : mink e2 e2 = 1 := by
    rw [he2, minkSeg_smul, ← hr2]
    field_simp
  have h12 : mink e1 e2 = 0 := by
    rw [he2, mink_smul_right'', minkSeg_comm e1 y, hye, mul_zero]
  have hLIpair : LinearIndependent ℝ (![e1, e2] : Fin 2 → (Fin 3 ⊕ Fin 1 → ℝ)) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hsum : c 0 • e1 + c 1 • e2 = 0 := by
      have h := hc
      rw [Fin.sum_univ_two] at h
      simpa using h
    have hc0 : c 0 = 0 := by
      have hpair := congrArg (fun z => mink z e1) hsum
      rw [minkSeg_add_left, mink_smul_left'', mink_smul_left'', hm11, minkSeg_comm e2 e1,
        h12, mul_zero, mul_one, add_zero, mink_zero_left] at hpair
      exact hpair
    have hc1 : c 1 = 0 := by
      have hpair := congrArg (fun z => mink z e2) hsum
      rw [minkSeg_add_left, mink_smul_left'', mink_smul_left'', h22, h12, mul_zero, mul_one,
        zero_add, mink_zero_left] at hpair
      exact hpair
    intro j
    fin_cases j
    · exact hc0
    · exact hc1
  have hspan_le : Submodule.span ℝ (Set.range (![e1, e2] : Fin 2 → (Fin 3 ⊕ Fin 1 → ℝ)))
      ≤ NormP a b := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    fin_cases j
    · exact hmem1
    · exact hmem2
  have hspan_eq : Submodule.span ℝ (Set.range (![e1, e2] : Fin 2 → (Fin 3 ⊕ Fin 1 → ℝ)))
      = NormP a b := by
    refine Submodule.eq_of_le_of_finrank_le hspan_le ?_
    rw [finrank_span_eq_card hLIpair, finrank_NormP ha hb hab]
    simp
  have hspan_pair : ∀ Z : Fin 3 ⊕ Fin 1 → ℝ, Z ∈ NormP a b → ∃ α β : ℝ, Z = α • e1 + β • e2 := by
    intro Z hZ
    have hZ' : Z ∈ Submodule.span ℝ (Set.range (![e1, e2] : Fin 2 → (Fin 3 ⊕ Fin 1 → ℝ))) := by
      rw [hspan_eq]; exact hZ
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hZ'
    refine ⟨c 0, c 1, ?_⟩
    have h := hc
    rw [Fin.sum_univ_two] at h
    rw [← h]
    simp
  have hspanV : ∀ Z : Fin 3 ⊕ Fin 1 → ℝ, ∃ α β γ δ : ℝ,
      Z = α • nvec a + β • nvec b + γ • e1 + δ • e2 := by
    intro Z
    set α : ℝ := mink Z (nvec b) / mink (nvec a) (nvec b) with hα
    set β : ℝ := mink Z (nvec a) / mink (nvec b) (nvec a) with hβ
    have hba : mink (nvec b) (nvec a) ≠ 0 := by
      rw [minkSeg_comm]; exact mink_pair_ne_zero ha hb hab
    have hab' : mink (nvec a) (nvec b) ≠ 0 := mink_pair_ne_zero ha hb hab
    set W : Fin 3 ⊕ Fin 1 → ℝ := Z - α • nvec a - β • nvec b with hW
    have hWa : mink W (nvec a) = 0 := by
      have h : mink W (nvec a)
          = mink Z (nvec a) - α * mink (nvec a) (nvec a) - β * mink (nvec b) (nvec a) := by
        rw [hW, mink_sub_left', mink_sub_left', mink_smul_left'', mink_smul_left'']
      rw [h, hα, hβ, mink_nvec_self' ha]
      simp only [mul_zero, sub_zero]
      rw [div_mul_cancel₀ (mink Z (nvec a)) hba]
      ring
    have hWb : mink W (nvec b) = 0 := by
      have h : mink W (nvec b)
          = mink Z (nvec b) - α * mink (nvec a) (nvec b) - β * mink (nvec b) (nvec b) := by
        rw [hW, mink_sub_left', mink_sub_left', mink_smul_left'', mink_smul_left'']
      rw [h, hα, hβ, mink_nvec_self' hb]
      simp only [mul_zero, sub_zero]
      rw [div_mul_cancel₀ (mink Z (nvec b)) hab']
      ring
    obtain ⟨γ, δ, hγδ⟩ := hspan_pair W (mem_NormP.mpr ⟨hWa, hWb⟩)
    have hZW : Z = W + α • nvec a + β • nvec b := by rw [hW]; abel
    have hfin : Z = α • nvec a + β • nvec b + γ • e1 + δ • e2 := by
      rw [hZW, hγδ]; abel
    exact ⟨α, β, γ, δ, hfin⟩
  exact ⟨⟨e1, e2, hmem1, hmem2, hm11, h22, h12, hspan_pair, hspanV⟩, trivial⟩

/-! ## The determinant of the normal action -/

theorem rotMat_det_ogAux3 (hA : Submission.Mostow.POActionProp 3) (a b : Submission.Mostow.E 3)
    (ha : a ∈ Submission.Mostow.Sph 3) (hb : b ∈ Submission.Mostow.Sph 3) (hab : a ≠ b)
    (B : Work.Mostow.gapA.PB a b) (g : LeanEval.Geometry.MostowRigidity.PO 3 1)
    (hg : g ∈ Work.Mostow.gapA.AxisSub hA a b) :
    (Work.Mostow.gapA.rotMat B g).det = 1 := by
  classical
  obtain ⟨hg1, hg2, hgd⟩ := mem_AxisSub_iff.mp hg
  set τ : Fin 2 ⊕ Fin 2 ≃ Fin 3 ⊕ Fin 1 :=
    (finSumFinEquiv : Fin 2 ⊕ Fin 2 ≃ Fin 4).trans
      (finSumFinEquiv : Fin 3 ⊕ Fin 1 ≃ Fin 4).symm with hτ
  set v : Fin 2 ⊕ Fin 2 → (Fin 3 ⊕ Fin 1 → ℝ) := fun j =>
    match j with
    | Sum.inl i => if i = (0 : Fin 2) then nvec a else nvec b
    | Sum.inr i => if i = (0 : Fin 2) then B.e1 else B.e2 with hv
  set C : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ := fun i j => v j (τ i) with hC
  set D : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ :=
    Matrix.fromBlocks 1 0 0 (rotMat B g) with hD
  set A' : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ :=
    (emat g).submatrix (⇑τ) (⇑τ) with hA'
  -- (1) `C` is invertible
  have hCcol : LinearIndependent ℝ C.col := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hsum : ∑ j, c j • v j = 0 := by
      funext k
      have h' := congrFun hc (τ.symm k)
      simp only [Matrix.col_apply, Finset.sum_apply, Pi.smul_apply] at h'
      simpa [hC] using h'
    have hcomb : ∑ j : Fin 2 ⊕ Fin 2, c j • v j
        = c (Sum.inl 0) • nvec a + c (Sum.inl 1) • nvec b
          + c (Sum.inr 0) • B.e1 + c (Sum.inr 1) • B.e2 := by
      rw [Fintype.sum_sum_type, Fin.sum_univ_two, Fin.sum_univ_two]
      simp [hv] <;> abel
    rw [hcomb] at hsum
    obtain ⟨h1, h2, h3, h4⟩ := indepV B ha hb hab hsum
    intro j
    rcases j with i | i <;> fin_cases i
    · exact h1
    · exact h2
    · exact h3
    · exact h4
  have hCd : C.det ≠ 0 := by
    have h1 : IsUnit C := Matrix.linearIndependent_cols_iff_isUnit.mp hCcol
    have h2 : IsUnit C.det := (Matrix.isUnit_iff_isUnit_det C).mp h1
    exact isUnit_iff_ne_zero.mp h2
  -- (2) the four columns of `D` express `emat g *ᵥ v j` in the basis `v`
  have hcol : ∀ j : Fin 2 ⊕ Fin 2, emat g *ᵥ v j = ∑ m, D m j • v m := by
    intro j
    rcases j with i | i
    · fin_cases i
      · show emat g *ᵥ v (Sum.inl 0) = ∑ m, D m (Sum.inl 0) • v m
        have hv0 : v (Sum.inl 0) = nvec a := by simp [hv]
        have hv1 : v (Sum.inl 1) = nvec b := by simp [hv]
        rw [hv0, hg1, Fintype.sum_sum_type, Fin.sum_univ_two, Fin.sum_univ_two, hD]
        simp [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
          Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, hv, hv0, hv1]
      · show emat g *ᵥ v (Sum.inl 1) = ∑ m, D m (Sum.inl 1) • v m
        have hv0 : v (Sum.inl 0) = nvec a := by simp [hv]
        have hv1 : v (Sum.inl 1) = nvec b := by simp [hv]
        rw [hv1, hg2, Fintype.sum_sum_type, Fin.sum_univ_two, Fin.sum_univ_two, hD]
        simp [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
          Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, hv, hv0, hv1]
    · fin_cases i
      · show emat g *ᵥ v (Sum.inr 0) = ∑ m, D m (Sum.inr 0) • v m
        have hv2 : v (Sum.inr 0) = B.e1 := by simp [hv]
        have hv3 : v (Sum.inr 1) = B.e2 := by simp [hv]
        rw [hv2, emat_mulVec_e1 hA B hg, Fintype.sum_sum_type, Fin.sum_univ_two,
          Fin.sum_univ_two, hD]
        simp [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
          Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, hv, hv2, hv3]
      · show emat g *ᵥ v (Sum.inr 1) = ∑ m, D m (Sum.inr 1) • v m
        have hv2 : v (Sum.inr 0) = B.e1 := by simp [hv]
        have hv3 : v (Sum.inr 1) = B.e2 := by simp [hv]
        rw [hv3, emat_mulVec_e2 hA B hg, Fintype.sum_sum_type, Fin.sum_univ_two,
          Fin.sum_univ_two, hD]
        simp [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
          Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, hv, hv2, hv3]
  -- (3) the matrix identity
  have hmv : ∀ x : Fin 3 ⊕ Fin 1 → ℝ,
      A' *ᵥ (fun i : Fin 2 ⊕ Fin 2 => x (τ i)) = fun i => (emat g *ᵥ x) (τ i) := by
    intro x
    funext i
    simp only [Matrix.mulVec, dotProduct, hA', Matrix.submatrix_apply]
    exact Fintype.sum_equiv τ _ _ (fun k => rfl)
  have hkey : A' * C = C * D := by
    ext i j
    have h1 : (A' * C) i j = (A' *ᵥ (fun k => C k j)) i := rfl
    have h2 : (A' *ᵥ (fun k => C k j)) i = (emat g *ᵥ v j) (τ i) := by
      have h := congrFun (hmv (v j)) i
      simpa [hC] using h
    have h3 : (C * D) i j = (∑ m, D m j • v m) (τ i) := by
      rw [Matrix.mul_apply]
      simp only [Finset.sum_apply, Pi.smul_apply]
      refine Finset.sum_congr rfl fun m _ => ?_
      simp only [hC, smul_eq_mul]
      ring
    rw [h1, h2, h3, hcol j]
  -- (4) determinants
  have hdetmul : C.det * D.det = A'.det * C.det := by
    rw [show C.det * D.det = (C * D).det from (Matrix.det_mul C D).symm,
      show A'.det * C.det = (A' * C).det from (Matrix.det_mul A' C).symm, hkey]
  have hDdet : D.det = (rotMat B g).det := by
    rw [hD, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, one_mul]
  have hA'det : A'.det = (emat g).det := by
    rw [hA']
    exact Matrix.det_submatrix_equiv_self τ (emat g)
  have hfinal : C.det * (rotMat B g).det = C.det * 1 := by
    rw [mul_one, ← hDdet, hdetmul, hA'det, hgd, one_mul]
  exact mul_left_cancel₀ hCd hfinal

end

end Work.Mostow.gapA
