/-
# The `M'`-basis of `R/𝓘`: CKMRV Proposition 3.2(1) at even weight

The propagation argument of CKMRV (proof of Proposition 3.2(1)) is run on the six
`SL(2,ℤ)`-translates `M' = (I, T⁻¹, STS, S, ST⁻¹, TS)` of the standard fundamental domain `𝓕`
(which tile the `Γ(2)`-fundamental domain `𝒟`), rather than on the basis
`M = (I, T, TS, S, ST, STS)` in which `Work.Residues.sigmaR` and `Work.Residues.rowDiff` are
expressed.  The reason is that the *support* of the residual
`M'_i ν - ∑ j, σ'(ν)_{ij} M'_j` (for `ν` a neighbour of `𝓕̄`) has to land in the tiles
`⋃_i M'_i 𝓕̄ ⊆ 𝒟̄ ⊆ O`, so that the propagation relations for `f` apply to every point that
occurs.

This file sets up that second basis:

* `Work.Asymptotics.MpR` : the six elements of `R = ℂ[SL(2,ℤ)]`;
* `Work.Asymptotics.MpChange` : the integral change of basis `M'_i ≡ ∑_j G_{ij} M_j (mod 𝓘)`,
  an involution `G² = 1`;
* `Work.Asymptotics.sigmaP` : the representation `σ' = G σ_R G⁻¹`;
* `Work.Asymptotics.rowDiffP` : the error vector `M'_i x - ∑_j σ'(x)_{ij} M'_j ∈ 𝓘`;
* `Work.Asymptotics.NeighborsP` : the neighbours of `𝓕̄` (the set that the geometric lemma
  `exists_neighbour_nbdh_of_Propagates` must produce).
-/
import Mathlib
import Submission.Work.Kernels.All
import Submission.Work.Residues.IdealImDefs
import Submission.Work.Residues.IdealImRowDiffAll
import Submission.Work.Asymptotics.DomainTiling

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology

namespace Work.Asymptotics

open Work.Kernels

/-! ## The neighbours of `𝓕̄` -/

/-- The neighbours of the standard fundamental domain `𝓕̄`: the two edge pairings `T`, `T⁻¹`
(the sides `Re z = 0` and `Re z = 1`), `S` (the vertex `i`), and the vertex stabilisers
`TS`, `(TS)² = ST⁻¹` (the vertex `ω = e^{iπ/3}`) and `TST⁻¹` (the vertex `1+i`), together with
their negatives (which act by the same Möbius transformation, and the same weight-`even` slash
operator). -/
def NeighborsP : Set SL(2,ℤ) :=
  {γ | γ ∈ ({(1 : SL(2,ℤ)), ModularGroup.S, ModularGroup.T, ModularGroup.T⁻¹,
      ModularGroup.T * ModularGroup.S, ModularGroup.S * ModularGroup.T⁻¹,
      ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹} : Set SL(2,ℤ)) ∨
    -γ ∈ ({(1 : SL(2,ℤ)), ModularGroup.S, ModularGroup.T, ModularGroup.T⁻¹,
      ModularGroup.T * ModularGroup.S, ModularGroup.S * ModularGroup.T⁻¹,
      ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹} : Set SL(2,ℤ))}

/-! ## The second basis -/

/-- `M' = (I, T⁻¹, STS, S, ST⁻¹, TS)` as elements of `R = ℂ[SL(2,ℤ)]` (CKMRV, proof of
Prop. 3.2(1)). -/
def MpR : Fin 6 → R :=
  ![1, R_Tinv, R_S * R_T * R_S, R_S, R_S * R_Tinv, R_T * R_S]

lemma MpR_zero : MpR 0 = (1 : R) := rfl
lemma MpR_one : MpR 1 = R_Tinv := rfl
lemma MpR_two : MpR 2 = R_S * R_T * R_S := rfl
lemma MpR_three : MpR 3 = R_S := rfl
lemma MpR_four : MpR 4 = R_S * R_Tinv := rfl
lemma MpR_five : MpR 5 = R_T * R_S := rfl

/-- `MpR i` is the monomial attached to the group element `Mp i`; this is what links the
algebra to the geometry of `Work.Asymptotics.Mp_smul_mem_closure_DomainD`. -/
theorem MpR_eq_of (i : Fin 6) : MpR i = MonoidAlgebra.of ℂ SL(2,ℤ) (Mp i) := by
  rw [MonoidAlgebra.of_apply]
  fin_cases i <;> simp [MpR, Mp, R_S, R_T, R_Tinv, MonoidAlgebra.one_def]

/-- The integral change-of-basis matrix: `M'_i ≡ ∑_j G_{ij} M_j (mod 𝓘)`, where
`M = (I, T, TS, S, ST, STS)` is `Work.Residues.M6`.
It is an involution: `G * G = 1`. -/
def MpChange : Matrix (Fin 6) (Fin 6) ℤ :=
  !![1,0,0,0,0,0;
     2,-1,0,0,0,0;
     0,0,0,0,0,1;
     0,0,0,1,0,0;
     0,0,0,2,-1,0;
     0,0,1,0,0,0]

/-- The complexification of the change of basis matrix. -/
def MpChangeC : Matrix (Fin 6) (Fin 6) ℂ :=
  !![1,0,0,0,0,0;
     2,-1,0,0,0,0;
     0,0,0,0,0,1;
     0,0,0,1,0,0;
     0,0,0,2,-1,0;
     0,0,1,0,0,0]

theorem MpChangeC_eq_map : MpChangeC = MpChange.map (Int.castRingHom ℂ) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [MpChangeC, MpChange]

theorem MpChange_mul_self : MpChange * MpChange = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_six, MpChange]

theorem MpChangeC_mul_self : MpChangeC * MpChangeC = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_six, MpChangeC]

/-! ## The representation `σ'` -/

/-- The representation `σ' = G σ_R G⁻¹` of `R` attached to the basis `M'` (the paper's `σ'`,
which is `σ` conjugated by the change of basis matrix). -/
def sigmaP (x : R) : Matrix (Fin 6) (Fin 6) ℂ := MpChangeC * Work.Residues.sigmaR x * MpChangeC

lemma sigmaP_add (x y : R) : sigmaP (x + y) = sigmaP x + sigmaP y := by
  simp only [sigmaP, map_add]
  rw [mul_add, add_mul]

/-- Conjugating a product by an involutive matrix. -/
lemma conj_mul_eq (A B : Matrix (Fin 6) (Fin 6) ℂ) (hG : MpChangeC * MpChangeC = 1) :
    MpChangeC * (A * B) * MpChangeC = (MpChangeC * A * MpChangeC) * (MpChangeC * B * MpChangeC) := by
  have hG' := hG
  rw [show (MpChangeC * A * MpChangeC) * (MpChangeC * B * MpChangeC)
      = MpChangeC * A * ((MpChangeC * MpChangeC) * (B * MpChangeC)) by noncomm_ring,
    hG', one_mul]
  noncomm_ring

lemma sigmaP_mul (x y : R) : sigmaP (x * y) = sigmaP x * sigmaP y := by
  simp only [sigmaP, map_mul]
  exact conj_mul_eq (Work.Residues.sigmaR x) (Work.Residues.sigmaR y) MpChangeC_mul_self

lemma sigmaP_one : sigmaP (1 : R) = 1 := by
  simp only [sigmaP, map_one, mul_one]
  rw [MpChangeC_mul_self]

lemma sigmaP_smul (c : ℂ) (x : R) : sigmaP (c • x) = c • sigmaP x := by
  simp only [sigmaP, map_smul]
  rw [mul_smul_comm, smul_mul_assoc]

theorem sigmaP_R_S : sigmaP R_S = MpChangeC * Work.Modular.sigmaS * MpChangeC := by
  rw [sigmaP, Work.Residues.sigmaR_R_S]

theorem sigmaP_R_T : sigmaP R_T = MpChangeC * Work.Modular.sigmaT * MpChangeC := by
  rw [sigmaP, Work.Residues.sigmaR_R_T]

/-- `σ'` kills `z - 1`. -/
theorem sigmaP_Rneg : sigmaP Work.Residues.Rneg = 1 := by
  rw [sigmaP, Work.Residues.sigmaR_Rneg]
  rw [mul_one, MpChangeC_mul_self]

/-! ## The error vector in the second basis -/

/-- The error vector of the reduction of `M'_i * x` in the basis `M'`:
`rowDiffP x i = M'_i * x - ∑ j, σ'(x)_{ij} • M'_j`. -/
def rowDiffP (x : R) (i : Fin 6) : R :=
  MpR i * x - ∑ j, (sigmaP x) i j • MpR j

/-- The cocycle identity for the error vector of the second basis. -/
theorem rowDiffP_mul (x y : R) (i : Fin 6) :
    rowDiffP (x * y) i = ∑ j, (sigmaP x) i j • rowDiffP y j + rowDiffP x i * y := by
  simp only [rowDiffP, sigmaP_mul]
  have hY := Work.Residues.matRow_smul_sum (sigmaP x) (sigmaP y) MpR i
  simp only [smul_sub, Finset.sum_sub_distrib, sub_mul, Finset.sum_mul, smul_mul_assoc]
  rw [hY]
  noncomm_ring

end Work.Asymptotics
