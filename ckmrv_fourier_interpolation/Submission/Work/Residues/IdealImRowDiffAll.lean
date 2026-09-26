/-
# Proposition 3.8(1) for `R = ℂ[SL(2,ℤ)]` via the error vector `rowDiff`

The paper (Cohn--Kumar--Miller--Radchenko--Viazovska, Ann. of Math. 196 (2022), proof of
Proposition 3.8(1)) reduces `R` modulo the right ideal `𝓘 = (T-I)²R + S(T-I)²R + (z-1)R` by
means of the six-dimensional representation `σ`: the six elements `M6 = (1, T, TS, S, ST, STS)`
satisfy `M6 · γ ≡ σ(γ) M6 mod 𝓘` for every `γ ∈ PSL(2,ℤ)`.

This file carries out that argument in `R = ℂ[SL(2,ℤ)]` for the representation `σ_R` of
`Submission/Work/Residues/IdealImDefs.lean` (`sigmaR`), using the error vector

  `rowDiff x i = M6 i * x - ∑ j, (σ_R x) i j • M6 j`

and the two base computations
`rowDiff R_S i ∈ 𝓘` (`rowDiff_R_S_mem`) and `rowDiff R_T i ∈ 𝓘` (`rowDiff_R_T_mem`), together
with the structural facts `rowDiff` is additive, `ℂ`-homogeneous and multiplicative
(cocycle identity) and the generation `Algebra.adjoin ℂ {S, T} = ⊤`
(`adjoin_R_S_R_T_eq_top`).

## Main results

* `Work.Residues.rowDiff_mem_of_idealI` : `rowDiff x i ∈ 𝓘` for every `x ∈ R`;
* `Work.Residues.mkQ_M6_span_top` : the images of `M6` span `R/𝓘`;
* `Work.Residues.linearIndependent_mkQ_M6` : they are linearly independent modulo `𝓘`;
* `Work.Residues.basis_quotient_IdealI_rowDiff` : they are a basis of `R/𝓘`.
-/
import Mathlib
import Submission.Work.Residues.IdealImDefs
import Submission.Work.Residues.rowDiff_R_T_mem
import Submission.Work.Residues.adjoin_R_S_R_T_eq_top

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups MonoidAlgebra ModularForm

namespace Work.Residues

open Work.Kernels

/-! ## The first row of `σ_R` vanishes on `𝓘` -/

private lemma row0_sigmaT_sub_one_sq :
    (((Work.Modular.sigmaT - 1) ^ 2 : Matrix (Fin 6) (Fin 6) ℂ)) 0 = 0 := by
  ext j
  fin_cases j <;>
    simp [pow_two, Matrix.mul_apply, Matrix.sub_apply, Work.Modular.sigmaT, Fin.sum_univ_six,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_fin_one]
      <;> norm_num

private lemma row0_sigmaS_mul_sigmaT_sub_one_sq :
    ((Work.Modular.sigmaS * (Work.Modular.sigmaT - 1) ^ 2 : Matrix (Fin 6) (Fin 6) ℂ)) 0
      = 0 := by
  ext j
  fin_cases j <;>
    simp [pow_two, Matrix.mul_apply, Matrix.sub_apply, Work.Modular.sigmaS, Work.Modular.sigmaT,
      Fin.sum_univ_six, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_fin_one]
      <;> norm_num

/-- A matrix whose first row vanishes stays with vanishing first row after right
multiplication. -/
private lemma mul_row0_eq_zero {A : Matrix (Fin 6) (Fin 6) ℂ} (hA : A 0 = 0)
    (M : Matrix (Fin 6) (Fin 6) ℂ) : (A * M) 0 = 0 := by
  ext j
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  rw [congr_fun hA k, Pi.zero_apply, zero_mul]

theorem sigmaR_zero_of_mem_augIdeal {x : R} (hx : x ∈ augIdeal) : sigmaR x = 0 := by
  refine Submodule.span_induction (p := fun y _ => sigmaR y = 0) ?_ ?_ ?_ ?_ hx
  · rintro y ⟨r, s, rfl⟩
    rw [map_mul, map_mul, map_sub, sigmaR_Rneg, map_one, sub_self, mul_zero, zero_mul]
  · rw [map_zero]
  · intro y z _ _ hy hz; rw [map_add, hy, hz, add_zero]
  · intro c y _ hy; rw [map_smul, hy, smul_zero]

theorem sigmaR_row0_of_mem_idealI {x : R} (hx : x ∈ idealI) : (sigmaR x) 0 = 0 := by
  obtain ⟨a, ha, c, hc, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨p, q, rfl⟩ := Work.Kernels.mem_span2.mp ha
  have h1 : sigmaR ((R_T - 1) ^ 2 * p)
      = (Work.Modular.sigmaT - 1) ^ 2 * sigmaR p := by
    rw [map_mul, map_pow, map_sub, sigmaR_R_T, map_one]
  have h2 : sigmaR (R_S * (R_T - 1) ^ 2 * q)
      = (Work.Modular.sigmaS * (Work.Modular.sigmaT - 1) ^ 2) * sigmaR q := by
    rw [map_mul, map_mul, map_pow, map_sub, sigmaR_R_S, sigmaR_R_T, map_one]
  have hc0 : sigmaR c = 0 := sigmaR_zero_of_mem_augIdeal hc
  have hrow1 : (((Work.Modular.sigmaT - 1) ^ 2 * sigmaR p : Matrix (Fin 6) (Fin 6) ℂ)) 0 = 0 :=
    mul_row0_eq_zero row0_sigmaT_sub_one_sq (sigmaR p)
  have hrow2 : (((Work.Modular.sigmaS * (Work.Modular.sigmaT - 1) ^ 2) * sigmaR q
      : Matrix (Fin 6) (Fin 6) ℂ)) 0 = 0 :=
    mul_row0_eq_zero row0_sigmaS_mul_sigmaT_sub_one_sq (sigmaR q)
  rw [map_add, map_add, h1, h2, hc0, add_zero]
  funext j
  rw [Matrix.add_apply, congr_fun hrow1 j, congr_fun hrow2 j]
  simp

theorem sigmaR_row0_M6 (i : Fin 6) : (sigmaR (M6 i)) 0 = Pi.single i 1 := by
  rw [sigmaR_M6]
  exact Work.Modular.sigmaAlg_basisElem_row i

/-! ## The error vector lands in `𝓘` for every element of `R` -/

/-- The elements of `R` whose whole error vector lies in `𝓘`. -/
private def rowDiffSubalgebra : Subalgebra ℂ R where
  carrier := {x | ∀ i, rowDiff x i ∈ idealI}
  mul_mem' := by
    intro x y hx hy i
    rw [rowDiff_mul]
    exact Submodule.add_mem _ (Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (hy j)))
      (idealI_mul_mem (hx i) y)
  add_mem' := by
    intro x y hx hy i
    rw [rowDiff_add]
    exact Submodule.add_mem _ (hx i) (hy i)
  algebraMap_mem' := by
    intro c i
    have h : rowDiff (algebraMap ℂ R c) i = c • rowDiff 1 i := by
      rw [Algebra.algebraMap_eq_smul_one, rowDiff_smul]
    rw [h, rowDiff_one, smul_zero]
    exact Submodule.zero_mem _

/-- **The reduction estimate**: for every `x ∈ R` the six error entries `rowDiff x i` lie in
`𝓘`.  This is the paper's `vec M · γ ∈ σ(γ) vec M + 𝓘⁶`. -/
theorem rowDiff_mem_of_idealI (x : R) (i : Fin 6) : rowDiff x i ∈ idealI := by
  have hle : Algebra.adjoin ℂ ({R_S, R_T} : Set R) ≤ rowDiffSubalgebra := by
    rw [Algebra.adjoin_le_iff]
    intro y hy
    rcases hy with rfl | rfl
    · exact rowDiff_R_S_mem
    · exact rowDiff_R_T_mem
  exact hle (by rw [adjoin_R_S_R_T_eq_top]; trivial) i

/-! ## The six images span and are independent modulo `𝓘` -/

/-- The images of `1, T, TS, S, ST, STS` span `R/𝓘`. -/
theorem mkQ_M6_span_top :
    Submodule.span ℂ (Set.range (fun i : Fin 6 => Submodule.mkQ idealI (M6 i))) = ⊤ := by
  rw [eq_top_iff]
  intro y _
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective idealI y
  have hx : x - ∑ j, (sigmaR x) 0 j • M6 j ∈ idealI := by
    have h := rowDiff_mem_of_idealI x 0
    rwa [rowDiff, M6_zero, one_mul] at h
  have heq : Submodule.mkQ idealI x
      = ∑ j, (sigmaR x) 0 j • Submodule.mkQ idealI (M6 j) := by
    have h0 : Submodule.mkQ idealI (x - ∑ j, (sigmaR x) 0 j • M6 j) = 0 :=
      (Submodule.Quotient.mk_eq_zero idealI).mpr hx
    rw [map_sub, sub_eq_zero] at h0
    rw [h0, map_sum]
    exact Finset.sum_congr rfl (fun j _ => by rw [map_smul])
  rw [heq]
  exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _
    (Submodule.subset_span ⟨j, rfl⟩))

/-- The images of `1, T, TS, S, ST, STS` are linearly independent modulo `𝓘`: the first row of
`σ_R` separates them, and it vanishes on `𝓘`. -/
theorem linearIndependent_mkQ_M6 :
    LinearIndependent ℂ (fun i : Fin 6 => Submodule.mkQ idealI (M6 i)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  have hsum : Submodule.mkQ idealI (∑ i, g i • M6 i) = 0 := by
    rw [map_sum]
    simpa only [map_smul] using hg
  have hmem : (∑ i, g i • M6 i) ∈ idealI :=
    (Submodule.Quotient.mk_eq_zero idealI).mp hsum
  have h0 : (sigmaR (∑ i, g i • M6 i)) 0 = 0 := sigmaR_row0_of_mem_idealI hmem
  have hval : (sigmaR (∑ i, g i • M6 i)) 0 j = g j := by
    rw [map_sum]
    simp only [map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, sigmaR_row0_M6,
      Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [← hval, h0]
  rfl

/-- **Paper Proposition 3.8(1)**: the images of `1, T, TS, S, ST, STS` are a basis of
`R/𝓘 = R/((T-I)²R + S(T-I)²R + (z-1)R)`. -/
theorem basis_quotient_IdealI_rowDiff :
    ∃ b : Module.Basis (Fin 6) ℂ (Work.Kernels.R ⧸ Work.Residues.idealI),
      ∀ i, b i = Submodule.mkQ Work.Residues.idealI (Work.Residues.M6 i) :=
  ⟨Module.Basis.mk linearIndependent_mkQ_M6 (by rw [mkQ_M6_span_top]),
    fun i => Module.Basis.mk_apply _ _ i⟩

end Work.Residues
