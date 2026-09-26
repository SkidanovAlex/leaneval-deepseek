/-
# Auxiliary definitions for the three-dimensional quotient `R / 𝓘_-`

This file sets up the `6 × 6` representation `σ_R` of `R = ℂ[SL(2,ℤ)]` (the paper's
representation `σ`, transported from `ℂ[PSL(2,ℤ)]` along the quotient map `SL(2,ℤ) → PSL(2,ℤ)`
and the classical presentation isomorphism), together with the "error vector"

  `rowDiff x i = M6 i * x - ∑ j, (σ_R x) i j • M6 j`

of the reduction `x ≡ ∑ j, (σ_R x) i j • M6 j`, and its two basic structural properties
(additivity and the cocycle identity for multiplication).

## Main definitions

* `Work.Residues.pslProj` : the algebra homomorphism `ℂ[SL(2,ℤ)] →ₐ[ℂ] ℂ[PSL(2,ℤ)]`.
* `Work.Residues.sigmaR` : the six-dimensional representation `σ_R : R →ₐ[ℂ] M₆(ℂ)`.
* `Work.Residues.rowDiff` : the error vector of the reduction of `M6 i * x`.
-/
import Mathlib
import Submission.Work.Residues.Basic
import Submission.Work.Modular.finrank_quotient_PSL
import Submission.Work.Modular.sigmaAlg_idealI_row
import Submission.Work.Modular.sigmaAlg_basisElem_row

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups MonoidAlgebra ModularForm

namespace Work.Residues

open Work.Kernels

/-! ## The quotient map onto `ℂ[PSL(2,ℤ)]` -/

/-- The algebra homomorphism `ℂ[SL(2,ℤ)] →ₐ[ℂ] ℂ[PSL(2,ℤ)]` induced by the quotient map
`SL(2,ℤ) → PSL(2,ℤ) = SL(2,ℤ)/center`. -/
def pslProj : R →ₐ[ℂ] Work.Modular.PSLGroupRing :=
  MonoidAlgebra.lift ℂ Work.Modular.PSLGroupRing (SL(2,ℤ))
    ((MonoidAlgebra.of ℂ (PSL(2,ℤ))).comp
      (QuotientGroup.mk' (Subgroup.center (SL(2,ℤ)))))

theorem pslProj_of (m : SL(2,ℤ)) :
    pslProj (MonoidAlgebra.of ℂ SL(2,ℤ) m) =
      MonoidAlgebra.of ℂ PSL(2,ℤ) (QuotientGroup.mk' (Subgroup.center (SL(2,ℤ))) m) :=
  MonoidAlgebra.lift_of _ m

theorem pslProj_R_S : pslProj R_S = Work.Modular.pslSR := by
  rw [show R_S = MonoidAlgebra.of ℂ SL(2,ℤ) ModularGroup.S from rfl, pslProj_of]
  rfl

theorem pslProj_R_T : pslProj R_T = Work.Modular.pslTR := by
  rw [show R_T = MonoidAlgebra.of ℂ SL(2,ℤ) ModularGroup.T from rfl, pslProj_of]
  rfl

theorem pslProj_M6 (i : Fin 6) : pslProj (M6 i) = Work.Modular.pslBasisElem i := by
  fin_cases i
  · change pslProj (1 : R) = (1 : Work.Modular.PSLGroupRing); rw [map_one]
  · change pslProj R_T = Work.Modular.pslTR; exact pslProj_R_T
  · change pslProj (R_T * R_S) = Work.Modular.pslTR * Work.Modular.pslSR
    rw [map_mul, pslProj_R_T, pslProj_R_S]
  · change pslProj R_S = Work.Modular.pslSR; exact pslProj_R_S
  · change pslProj (R_S * R_T) = Work.Modular.pslSR * Work.Modular.pslTR
    rw [map_mul, pslProj_R_T, pslProj_R_S]
  · change pslProj (R_S * R_T * R_S) = Work.Modular.pslSR * Work.Modular.pslTR * Work.Modular.pslSR
    rw [map_mul, map_mul, pslProj_R_T, pslProj_R_S]

/-- `-I ∈ SL(2,ℤ)` lies in the center, so it dies in `PSL(2,ℤ)`. -/
theorem neg_one_mem_center : (-1 : SL(2,ℤ)) ∈ Subgroup.center (SL(2,ℤ)) := by
  rw [Subgroup.mem_center_iff]
  intro g
  rw [mul_neg_one, neg_mul, one_mul]

/-- The image of `S` in `PSL(2,ℤ)` is an involution. -/
theorem pslS_sq : Work.Modular.pslS * Work.Modular.pslS = 1 := by
  rw [show (Work.Modular.pslS * Work.Modular.pslS : PSL(2,ℤ))
      = QuotientGroup.mk (ModularGroup.S * ModularGroup.S : SL(2,ℤ)) from rfl]
  rw [show (ModularGroup.S * ModularGroup.S : SL(2,ℤ)) = -1 from by decide]
  rw [QuotientGroup.eq_one_iff]
  exact neg_one_mem_center

/-- `-I` acts trivially in `ℂ[PSL(2,ℤ)]`, i.e. `pslProj z = 1`. -/
theorem pslProj_Rneg : pslProj Rneg = 1 := by
  have h : pslProj Rneg = pslProj R_S * pslProj R_S := by
    rw [show Rneg = R_S * R_S from R_S_mul_R_S_eq.symm, map_mul]
  rw [h, pslProj_R_S]
  rw [show (Work.Modular.pslSR * Work.Modular.pslSR : Work.Modular.PSLGroupRing)
      = MonoidAlgebra.single (Work.Modular.pslS * Work.Modular.pslS) 1 from by
        rw [show Work.Modular.pslSR
            = MonoidAlgebra.single Work.Modular.pslS (1 : ℂ) from rfl]
        rw [MonoidAlgebra.single_mul_single]
        simp]
  rw [pslS_sq, ← MonoidAlgebra.one_def]

/-! ## The six-dimensional representation `σ_R` of `R = ℂ[SL(2,ℤ)]` -/

/-- The inverse of the presentation isomorphism `ℂ[Γ] ≅ ℂ[PSL(2,ℤ)]`, as an algebra
homomorphism. -/
def Epsl : Work.Modular.PSLGroupRing →ₐ[ℂ] Work.Modular.GroupRing :=
  Work.Modular.pslQuotAlgEquiv.symm

theorem Epsl_pslSR : Epsl Work.Modular.pslSR = Work.Modular.sR := by
  rw [show Work.Modular.pslSR = Work.Modular.pslQuotAlgEquiv Work.Modular.sR
      from Work.Modular.pslQuotAlgEquiv_sR.symm]
  exact AlgEquiv.symm_apply_apply _ _

theorem Epsl_pslTR : Epsl Work.Modular.pslTR = Work.Modular.tR := by
  rw [show Work.Modular.pslTR = Work.Modular.pslQuotAlgEquiv Work.Modular.tR
      from Work.Modular.pslQuotAlgEquiv_tR.symm]
  exact AlgEquiv.symm_apply_apply _ _

/-- The paper's six-dimensional representation `σ`, transported to `R = ℂ[SL(2,ℤ)]`:
the composite of the quotient map onto `ℂ[PSL(2,ℤ)]`, the presentation isomorphism
`ℂ[PSL(2,ℤ)] ≅ ℂ[Γ]`, and the explicit representation `σ` on `ℂ[Γ]`. -/
def sigmaR : R →ₐ[ℂ] Matrix (Fin 6) (Fin 6) ℂ :=
  Work.Modular.sigmaAlg.comp (Epsl.comp pslProj)

theorem sigmaR_R_S : sigmaR R_S = Work.Modular.sigmaS := by
  change Work.Modular.sigmaAlg (Epsl (pslProj R_S)) = Work.Modular.sigmaS
  rw [pslProj_R_S, Epsl_pslSR]
  exact Work.Modular.sigmaAlg_sR

theorem sigmaR_R_T : sigmaR R_T = Work.Modular.sigmaT := by
  change Work.Modular.sigmaAlg (Epsl (pslProj R_T)) = Work.Modular.sigmaT
  rw [pslProj_R_T, Epsl_pslTR]
  exact Work.Modular.sigmaAlg_tR

/-- `σ_R` kills `z - 1`. -/
theorem sigmaR_Rneg : sigmaR Rneg = 1 := by
  rw [show Rneg = R_S * R_S from R_S_mul_R_S_eq.symm, map_mul, sigmaR_R_S,
    Work.Modular.sigmaS_mul_self]

theorem Epsl_pslBasisElem (i : Fin 6) : Epsl (Work.Modular.pslBasisElem i)
    = Work.Modular.basisElem i := by
  fin_cases i
  · change Epsl (1 : Work.Modular.PSLGroupRing) = (1 : Work.Modular.GroupRing); rw [map_one]
  · change Epsl Work.Modular.pslTR = Work.Modular.tR; exact Epsl_pslTR
  · change Epsl (Work.Modular.pslTR * Work.Modular.pslSR) = Work.Modular.tR * Work.Modular.sR
    rw [map_mul, Epsl_pslTR, Epsl_pslSR]
  · change Epsl Work.Modular.pslSR = Work.Modular.sR; exact Epsl_pslSR
  · change Epsl (Work.Modular.pslSR * Work.Modular.pslTR) = Work.Modular.sR * Work.Modular.tR
    rw [map_mul, Epsl_pslTR, Epsl_pslSR]
  · change Epsl (Work.Modular.pslSR * Work.Modular.pslTR * Work.Modular.pslSR)
        = Work.Modular.sR * Work.Modular.tR * Work.Modular.sR
    rw [map_mul, map_mul, Epsl_pslTR, Epsl_pslSR]

theorem sigmaR_M6 (i : Fin 6) :
    sigmaR (M6 i) = Work.Modular.sigmaAlg (Work.Modular.basisElem i) := by
  change Work.Modular.sigmaAlg (Epsl (pslProj (M6 i)))
    = Work.Modular.sigmaAlg (Work.Modular.basisElem i)
  rw [pslProj_M6, Epsl_pslBasisElem]

/-! ## The error vector `rowDiff` -/

/-- The error vector of the reduction of `M6 i * x` modulo `𝓘`:
`rowDiff x i = M6 i * x - ∑ j, (σ_R x) i j • M6 j`. -/
def rowDiff (x : R) (i : Fin 6) : R :=
  M6 i * x - ∑ j, (sigmaR x) i j • M6 j

theorem rowDiff_zero (i : Fin 6) : rowDiff 0 i = 0 := by
  simp [rowDiff]

theorem rowDiff_add (x y : R) (i : Fin 6) :
    rowDiff (x + y) i = rowDiff x i + rowDiff y i := by
  simp only [rowDiff, map_add, Matrix.add_apply, mul_add, add_smul, Finset.sum_add_distrib]
  rw [add_sub_add_comm]

theorem rowDiff_smul (c : ℂ) (x : R) (i : Fin 6) :
    rowDiff (c • x) i = c • rowDiff x i := by
  have hcx : rowDiff (c • x) i = M6 i * (c • x) - ∑ j, (c * (sigmaR x) i j) • M6 j := by
    simp only [rowDiff, map_smul, Matrix.smul_apply, smul_eq_mul]
  rw [hcx, rowDiff, smul_sub, Finset.smul_sum]
  congr 1
  · rw [mul_smul_comm]
  · apply Finset.sum_congr rfl
    intro j _
    rw [← smul_smul]

theorem rowDiff_one (i : Fin 6) : rowDiff 1 i = 0 := by
  simp [rowDiff, Matrix.one_apply]

/-- Row-vector form of multiplying a six-tuple of group-algebra elements on the right by a
matrix: `∑ j, A i j • (∑ k, B j k • M k) = ∑ k, (A * B) i k • M k`. -/
theorem matRow_smul_sum (A B : Matrix (Fin 6) (Fin 6) ℂ) (M : Fin 6 → R) (i : Fin 6) :
    (∑ j, A i j • (∑ k, B j k • M k)) = ∑ k, (A * B) i k • M k := by
  simp only [Matrix.mul_apply, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul]

/-- The cocycle identity for the error vector. -/
theorem rowDiff_mul (x y : R) (i : Fin 6) :
    rowDiff (x * y) i = ∑ j, (sigmaR x) i j • rowDiff y j + rowDiff x i * y := by
  simp only [rowDiff, map_mul]
  have hY := matRow_smul_sum (sigmaR x) (sigmaR y) M6 i
  simp only [smul_sub, Finset.sum_sub_distrib, sub_mul, Finset.sum_mul, smul_mul_assoc]
  rw [hY]
  noncomm_ring

/-! ## The ideals are closed under right multiplication -/

theorem IdealI_mul_mem {x : R} (hx : x ∈ Work.Kernels.IdealI) (r : R) :
    x * r ∈ Work.Kernels.IdealI := by
  obtain ⟨a, b, rfl⟩ := Work.Kernels.mem_span2.mp hx
  refine ⟨a * r, b * r, ?_⟩
  rw [add_mul, mul_assoc, mul_assoc]

theorem IdealIp_mul_mem {x : R} (hx : x ∈ Work.Kernels.IdealIp) (r : R) :
    x * r ∈ Work.Kernels.IdealIp := by
  obtain ⟨a, b, rfl⟩ := Work.Kernels.mem_span2.mp hx
  refine ⟨a * r, b * r, ?_⟩
  rw [add_mul, mul_assoc, mul_assoc]

theorem IdealIm_mul_mem {x : R} (hx : x ∈ Work.Kernels.IdealIm) (r : R) :
    x * r ∈ Work.Kernels.IdealIm := by
  obtain ⟨a, b, rfl⟩ := Work.Kernels.mem_span2.mp hx
  refine ⟨a * r, b * r, ?_⟩
  rw [add_mul, mul_assoc, mul_assoc]

theorem idealI_mul_mem {x : R} (hx : x ∈ idealI) (r : R) : x * r ∈ idealI := by
  obtain ⟨a, ha, c, hc, rfl⟩ := Submodule.mem_sup.mp hx
  rw [add_mul]
  exact Submodule.add_mem _ (IdealI_le_idealI (IdealI_mul_mem ha r)) (augIdeal_le_idealI (mul_mem_augIdeal_right hc r))

theorem idealIm_mul_mem {x : R} (hx : x ∈ idealIm) (r : R) : x * r ∈ idealIm := by
  obtain ⟨a, ha, c, hc, rfl⟩ := Submodule.mem_sup.mp hx
  rw [add_mul]
  exact Submodule.add_mem _ (IdealIm_le_idealIm (IdealIm_mul_mem ha r)) (augIdeal_le_idealIm (mul_mem_augIdeal_right hc r))

theorem idealIp_mul_mem {x : R} (hx : x ∈ idealIp) (r : R) : x * r ∈ idealIp := by
  obtain ⟨a, ha, c, hc, rfl⟩ := Submodule.mem_sup.mp hx
  rw [add_mul]
  exact Submodule.add_mem _ (IdealIp_le_idealIp (IdealIp_mul_mem ha r)) (augIdeal_le_idealIp (mul_mem_augIdeal_right hc r))

/-! ## The group-algebra relations of `SL(2,ℤ)` used in the reduction -/

theorem single_pow (g : SL(2,ℤ)) (n : ℕ) :
    (MonoidAlgebra.single g (1 : ℂ) : R) ^ n = MonoidAlgebra.single (g ^ n) 1 := by
  induction n with
  | zero => rw [pow_zero, pow_zero, MonoidAlgebra.one_def]
  | succ n ih =>
    rw [pow_succ, ih, MonoidAlgebra.single_mul_single, mul_one, pow_succ]

theorem R_S_mul_R_T_eq : R_S * R_T = MonoidAlgebra.single (ModularGroup.S * ModularGroup.T) 1 := by
  rw [R_S, R_T, MonoidAlgebra.single_mul_single]; simp

/-- `(S T)^3 = -I`, i.e. `(S T)^3 = z` in `R`. -/
theorem R_ST_cube : (R_S * R_T) ^ 3 = Rneg := by
  rw [R_S_mul_R_T_eq, single_pow,
    show (ModularGroup.S * ModularGroup.T) ^ 3 = (-1 : SL(2,ℤ)) from by decide]

/-- `T S T S T = S` in `SL(2,ℤ)`. -/
theorem R_TSTST : R_T * R_S * R_T * R_S * R_T = R_S := by
  have h : (R_T * R_S * R_T * R_S * R_T : R)
      = MonoidAlgebra.single
          ((ModularGroup.T * ModularGroup.S) * (ModularGroup.T * ModularGroup.S)
            * ModularGroup.T) 1 := by
    rw [R_S, R_T, MonoidAlgebra.single_mul_single, MonoidAlgebra.single_mul_single,
      MonoidAlgebra.single_mul_single, MonoidAlgebra.single_mul_single]
    simp [mul_assoc]
  rw [h,
    show ((ModularGroup.T * ModularGroup.S) * (ModularGroup.T * ModularGroup.S)
        * ModularGroup.T : SL(2,ℤ)) = ModularGroup.S from by decide]

/-! ## The `S`-base case of the reduction -/

/-- The `S`-base case of the reduction of the six elements `1, T, TS, S, ST, STS` modulo
`𝓘`: multiplying the `i`-th of them on the right by `S` and reducing by `σ_R S = sigmaS`
lands in `𝓘`. -/
theorem rowDiff_R_S_mem (i : Fin 6) : rowDiff R_S i ∈ idealI := by
  simp only [rowDiff, sigmaR_R_S]
  fin_cases i
  · change M6 (0 : Fin 6) * R_S - ∑ j, Work.Modular.sigmaS (0 : Fin 6) j • M6 j ∈ idealI
    rw [show M6 (0 : Fin 6) * R_S - ∑ j, Work.Modular.sigmaS (0 : Fin 6) j • M6 j = 0 by
      simp [M6, Work.Modular.sigmaS, Fin.sum_univ_six]]
    exact Submodule.zero_mem _
  · change M6 (1 : Fin 6) * R_S - ∑ j, Work.Modular.sigmaS (1 : Fin 6) j • M6 j ∈ idealI
    rw [show M6 (1 : Fin 6) * R_S - ∑ j, Work.Modular.sigmaS (1 : Fin 6) j • M6 j = 0 by
      simp [M6, Work.Modular.sigmaS, Fin.sum_univ_six, mul_assoc]]
    exact Submodule.zero_mem _
  · change M6 (2 : Fin 6) * R_S - ∑ j, Work.Modular.sigmaS (2 : Fin 6) j • M6 j ∈ idealI
    rw [show (∑ j, Work.Modular.sigmaS (2 : Fin 6) j • M6 j : R) = R_T by
      simp [M6, Work.Modular.sigmaS, Fin.sum_univ_six]]
    have heq : M6 (2 : Fin 6) * R_S - R_T = R_T * (Rneg - 1) := by
      show (R_T * R_S) * R_S - R_T = R_T * (Rneg - 1)
      rw [mul_assoc, R_S_mul_R_S_eq, mul_sub, mul_one]
    rw [heq]
    exact augIdeal_le_idealI (mul_Rneg_sub_one_mem R_T)
  · change M6 (3 : Fin 6) * R_S - ∑ j, Work.Modular.sigmaS (3 : Fin 6) j • M6 j ∈ idealI
    rw [show (∑ j, Work.Modular.sigmaS (3 : Fin 6) j • M6 j : R) = 1 by
      simp [M6, Work.Modular.sigmaS, Fin.sum_univ_six]]
    have heq : M6 (3 : Fin 6) * R_S - 1 = Rneg - 1 := by
      show R_S * R_S - 1 = Rneg - 1
      rw [R_S_mul_R_S_eq]
    rw [heq]
    exact augIdeal_le_idealI Rneg_sub_one_mem_augIdeal
  · change M6 (4 : Fin 6) * R_S - ∑ j, Work.Modular.sigmaS (4 : Fin 6) j • M6 j ∈ idealI
    rw [show M6 (4 : Fin 6) * R_S - ∑ j, Work.Modular.sigmaS (4 : Fin 6) j • M6 j = 0 by
      simp [M6, Work.Modular.sigmaS, Fin.sum_univ_six, mul_assoc]]
    exact Submodule.zero_mem _
  · change M6 (5 : Fin 6) * R_S - ∑ j, Work.Modular.sigmaS (5 : Fin 6) j • M6 j ∈ idealI
    rw [show (∑ j, Work.Modular.sigmaS (5 : Fin 6) j • M6 j : R) = R_S * R_T by
      simp [M6, Work.Modular.sigmaS, Fin.sum_univ_six]]
    have heq : M6 (5 : Fin 6) * R_S - R_S * R_T = (R_S * R_T) * (Rneg - 1) := by
      show (R_S * R_T * R_S) * R_S - R_S * R_T = (R_S * R_T) * (Rneg - 1)
      rw [mul_assoc, R_S_mul_R_S_eq, mul_sub, mul_one]
    rw [heq]
    exact augIdeal_le_idealI (mul_Rneg_sub_one_mem (R_S * R_T))

end Work.Residues
