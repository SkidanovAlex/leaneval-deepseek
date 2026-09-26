/-
# The quotients `R/𝓘`, `R/𝓘_±` and the functionals `φ`, `φ_±` (CKMRV Proposition 3.8)

This file records the quotient theory of the kernels chapter:

* `Work.Residues.finrank_quotient_idealI` : `dim_ℂ R/𝓘 = 6`, with basis the images of
  `1, T, TS, S, ST, STS` (paper Proposition 3.8(1));
* `Work.Residues.finrank_quotient_idealIp` and `finrank_quotient_idealIm` :
  `dim_ℂ R/𝓘_± = 3`, with basis the images of `1, T, TS` (paper Proposition 3.8(2));
* the linear functionals `φ : R → ℂ` vanishing on `𝓘` with `φ(1) = 0, φ(T) = 1,
  φ(TS) = 0, φ(S) = 0, φ(ST) = 0, φ(STS) = 0`, and `φ_± : R → ℂ` vanishing on `𝓘_±` with
  `φ_±(1) = 0, φ_±(T) = 1, φ_±(TS) = 0` (paper (3.12)); these are the functionals appearing in
  the residue theorem (Theorem 4.9(3)).

The bases for `𝓘` and `𝓘_±` are proved in the sibling modules
`Work.Residues.basis_quotient_IdealI`, `Work.Residues.basis_IdealIp_of_basis_IdealI` and
`Work.Residues.basis_quotient_IdealIm`.
-/
import Mathlib
import Submission.Work.Residues.Basic
import Submission.Work.Residues.basis_quotient_IdealI
import Submission.Work.Residues.basis_IdealIp_of_basis_IdealI
import Submission.Work.Residues.basis_quotient_IdealIm

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle

namespace Work.Residues

open Work.Kernels

/-! ## The bases of the three quotients -/

/-- The basis of `R/𝓘` given by the images of `1, T, TS, S, ST, STS`. -/
noncomputable def basisI : Module.Basis (Fin 6) ℂ (R ⧸ idealI) :=
  Classical.choose basis_quotient_IdealI

@[simp] lemma basisI_apply (i : Fin 6) : basisI i = Submodule.mkQ idealI (M6 i) :=
  Classical.choose_spec basis_quotient_IdealI i

/-- The basis of `R/𝓘_+` given by the images of `1, T, TS`. -/
noncomputable def basisIp : Module.Basis (Fin 3) ℂ (R ⧸ idealIp) :=
  Classical.choose (basis_IdealIp_of_basis_IdealI basis_quotient_IdealI)

@[simp] lemma basisIp_apply (i : Fin 3) : basisIp i = Submodule.mkQ idealIp (M3 i) :=
  Classical.choose_spec (basis_IdealIp_of_basis_IdealI basis_quotient_IdealI) i

/-- The basis of `R/𝓘_-` given by the images of `1, T, TS`. -/
noncomputable def basisIm : Module.Basis (Fin 3) ℂ (R ⧸ idealIm) :=
  Classical.choose basis_quotient_IdealIm

@[simp] lemma basisIm_apply (i : Fin 3) : basisIm i = Submodule.mkQ idealIm (M3 i) :=
  Classical.choose_spec basis_quotient_IdealIm i

theorem finrank_quotient_idealI : Module.finrank ℂ (R ⧸ idealI) = 6 := by
  rw [Module.finrank_eq_card_basis basisI]
  simp

theorem finrank_quotient_idealIp : Module.finrank ℂ (R ⧸ idealIp) = 3 := by
  rw [Module.finrank_eq_card_basis basisIp]
  simp

theorem finrank_quotient_idealIm : Module.finrank ℂ (R ⧸ idealIm) = 3 := by
  rw [Module.finrank_eq_card_basis basisIm]
  simp

/-- Paper Proposition 3.8(2) for `𝓘_+` (unconditional form). -/
theorem basis_quotient_IdealIp' :
    ∃ b : Module.Basis (Fin 3) ℂ (R ⧸ idealIp),
      ∀ i, b i = Submodule.mkQ idealIp (M3 i) :=
  ⟨basisIp, basisIp_apply⟩

/-- Paper Proposition 3.8(2) for `𝓘_-` (unconditional form). -/
theorem basis_quotient_IdealIm' :
    ∃ b : Module.Basis (Fin 3) ℂ (R ⧸ idealIm),
      ∀ i, b i = Submodule.mkQ idealIm (M3 i) :=
  ⟨basisIm, basisIm_apply⟩

/-! ## Reduction of an arbitrary element to the basis modulo `𝓘`, `𝓘_±` -/

/-- Every `r : R` agrees modulo `𝓘_+` with a linear combination of `1, T, TS`. -/
theorem exists_sub_sum_smul_M3_mem_idealIp (r : R) :
    ∃ c : Fin 3 → ℂ, r - ∑ i, c i • M3 i ∈ idealIp := by
  refine ⟨fun i => (basisIp.repr (Submodule.mkQ idealIp r)) i, ?_⟩
  have hsum : Submodule.mkQ idealIp
        (∑ i : Fin 3, (basisIp.repr (Submodule.mkQ idealIp r)) i • M3 i)
      = ∑ i : Fin 3, (basisIp.repr (Submodule.mkQ idealIp r)) i • basisIp i := by
    rw [map_sum]
    exact Finset.sum_congr rfl (fun i _ => by rw [map_smul, basisIp_apply])
  have hzero : Submodule.mkQ idealIp
      (r - ∑ i : Fin 3, (basisIp.repr (Submodule.mkQ idealIp r)) i • M3 i) = 0 := by
    rw [map_sub, hsum, Module.Basis.sum_repr, sub_self]
  exact (Submodule.Quotient.mk_eq_zero idealIp).mp hzero

/-- Every `r : R` agrees modulo `𝓘_-` with a linear combination of `1, T, TS`. -/
theorem exists_sub_sum_smul_M3_mem_idealIm (r : R) :
    ∃ c : Fin 3 → ℂ, r - ∑ i, c i • M3 i ∈ idealIm := by
  refine ⟨fun i => (basisIm.repr (Submodule.mkQ idealIm r)) i, ?_⟩
  have hsum : Submodule.mkQ idealIm
        (∑ i : Fin 3, (basisIm.repr (Submodule.mkQ idealIm r)) i • M3 i)
      = ∑ i : Fin 3, (basisIm.repr (Submodule.mkQ idealIm r)) i • basisIm i := by
    rw [map_sum]
    exact Finset.sum_congr rfl (fun i _ => by rw [map_smul, basisIm_apply])
  have hzero : Submodule.mkQ idealIm
      (r - ∑ i : Fin 3, (basisIm.repr (Submodule.mkQ idealIm r)) i • M3 i) = 0 := by
    rw [map_sub, hsum, Module.Basis.sum_repr, sub_self]
  exact (Submodule.Quotient.mk_eq_zero idealIm).mp hzero

/-! ## The functionals `φ`, `φ_±` -/

/-- The linear functional `φ_+` of CKMRV (3.12): the functional on `R/𝓘_+` with
`φ_+(1) = 0`, `φ_+(T) = 1`, `φ_+(TS) = 0`, pulled back to `R`. -/
noncomputable def phiPlus : R →ₗ[ℂ] ℂ :=
  ((basisIp.coord (1 : Fin 3)) : (R ⧸ idealIp) →ₗ[ℂ] ℂ).comp (Submodule.mkQ idealIp)

/-- The linear functional `φ_-` of CKMRV (3.12): the functional on `R/𝓘_-` with
`φ_-(1) = 0`, `φ_-(T) = 1`, `φ_-(TS) = 0`, pulled back to `R`. -/
noncomputable def phiMinus : R →ₗ[ℂ] ℂ :=
  ((basisIm.coord (1 : Fin 3)) : (R ⧸ idealIm) →ₗ[ℂ] ℂ).comp (Submodule.mkQ idealIm)

/-- The linear functional `φ` of CKMRV (3.12): the functional on `R/𝓘` with `φ(1) = φ(S) =
φ(STS) = φ(TS) = φ(ST) = 0` and `φ(T) = 1`, pulled back to `R`. -/
noncomputable def phi : R →ₗ[ℂ] ℂ :=
  ((basisI.coord (1 : Fin 6)) : (R ⧸ idealI) →ₗ[ℂ] ℂ).comp (Submodule.mkQ idealI)

lemma phiPlus_M3 (i : Fin 3) : phiPlus (M3 i) = if i = 1 then 1 else 0 := by
  simp only [phiPlus, LinearMap.comp_apply, Module.Basis.coord_apply]
  rw [← basisIp_apply i, Module.Basis.repr_self, Finsupp.single_apply]

lemma phiMinus_M3 (i : Fin 3) : phiMinus (M3 i) = if i = 1 then 1 else 0 := by
  simp only [phiMinus, LinearMap.comp_apply, Module.Basis.coord_apply]
  rw [← basisIm_apply i, Module.Basis.repr_self, Finsupp.single_apply]

lemma phi_M6 (i : Fin 6) : phi (M6 i) = if i = 1 then 1 else 0 := by
  simp only [phi, LinearMap.comp_apply, Module.Basis.coord_apply]
  rw [← basisI_apply i, Module.Basis.repr_self, Finsupp.single_apply]

@[simp] lemma phiPlus_R_T : phiPlus R_T = 1 := by
  simpa [M3] using phiPlus_M3 1

@[simp] lemma phiPlus_one : phiPlus 1 = 0 := by
  simpa [M3] using phiPlus_M3 0

@[simp] lemma phiPlus_TS : phiPlus (R_T * R_S) = 0 := by
  simpa [M3] using phiPlus_M3 2

@[simp] lemma phiMinus_R_T : phiMinus R_T = 1 := by
  simpa [M3] using phiMinus_M3 1

@[simp] lemma phiMinus_one : phiMinus 1 = 0 := by
  simpa [M3] using phiMinus_M3 0

@[simp] lemma phiMinus_TS : phiMinus (R_T * R_S) = 0 := by
  simpa [M3] using phiMinus_M3 2

@[simp] lemma phi_R_T : phi R_T = 1 := by
  simpa [M6] using phi_M6 1

@[simp] lemma phi_one : phi 1 = 0 := by
  simpa [M6] using phi_M6 0

@[simp] lemma phi_TS : phi (R_T * R_S) = 0 := by
  simpa [M6] using phi_M6 2

@[simp] lemma phi_R_S : phi R_S = 0 := by
  simpa [M6] using phi_M6 3

@[simp] lemma phi_ST : phi (R_S * R_T) = 0 := by
  simpa [M6] using phi_M6 4

@[simp] lemma phi_STS : phi (R_S * R_T * R_S) = 0 := by
  simpa [M6] using phi_M6 5

lemma phi_eq_zero_of_mem_idealI {r : R} (hr : r ∈ idealI) : phi r = 0 := by
  rw [phi, LinearMap.comp_apply, Submodule.mkQ_apply,
    (Submodule.Quotient.mk_eq_zero idealI).mpr hr, map_zero]

lemma phiPlus_eq_zero_of_mem_idealIp {r : R} (hr : r ∈ idealIp) : phiPlus r = 0 := by
  rw [phiPlus, LinearMap.comp_apply, Submodule.mkQ_apply,
    (Submodule.Quotient.mk_eq_zero idealIp).mpr hr, map_zero]

lemma phiMinus_eq_zero_of_mem_idealIm {r : R} (hr : r ∈ idealIm) : phiMinus r = 0 := by
  rw [phiMinus, LinearMap.comp_apply, Submodule.mkQ_apply,
    (Submodule.Quotient.mk_eq_zero idealIm).mpr hr, map_zero]

end Work.Residues

namespace Work.Residues

open Work.Kernels

/-! ## The values of `φ_±` on the basis of `R/𝓘` and the relation `φ = (φ₊ + φ₋)/2` -/

lemma phiPlus_R_S : phiPlus R_S = 0 := by
  have h : (R_S + 1) * 1 ∈ idealIp := IdealIp_le_idealIp (gen_S_add_mem_IdealIp 1)
  have h0 : phiPlus R_S + phiPlus 1 = 0 := by
    have := phiPlus_eq_zero_of_mem_idealIp h
    simpa [map_add, mul_one] using this
  rw [phiPlus_one, add_zero] at h0
  exact h0

lemma phiMinus_R_S : phiMinus R_S = 0 := by
  have h : (R_S - 1) * 1 ∈ idealIm := IdealIm_le_idealIm (gen_S_sub_mem_IdealIm 1)
  have h0 : phiMinus R_S - phiMinus 1 = 0 := by
    have := phiMinus_eq_zero_of_mem_idealIm h
    simpa [map_sub, mul_one] using this
  rw [phiMinus_one, sub_zero] at h0
  exact h0

lemma phiPlus_ST : phiPlus (R_S * R_T) = -1 := by
  have h : (R_S + 1) * R_T ∈ idealIp := IdealIp_le_idealIp (gen_S_add_mem_IdealIp R_T)
  have h0 : phiPlus (R_S * R_T) + phiPlus R_T = 0 := by
    have := phiPlus_eq_zero_of_mem_idealIp h
    simpa [map_add, add_mul, one_mul] using this
  rw [phiPlus_R_T, add_eq_zero_iff_eq_neg] at h0
  simpa using h0

lemma phiMinus_ST : phiMinus (R_S * R_T) = 1 := by
  have h : (R_S - 1) * R_T ∈ idealIm := IdealIm_le_idealIm (gen_S_sub_mem_IdealIm R_T)
  have h0 : phiMinus (R_S * R_T) - phiMinus R_T = 0 := by
    have := phiMinus_eq_zero_of_mem_idealIm h
    simpa [map_sub, sub_mul, one_mul] using this
  rw [phiMinus_R_T, sub_eq_zero] at h0
  simpa using h0

lemma phiPlus_STS : phiPlus (R_S * R_T * R_S) = 0 := by
  have h : (R_S + 1) * (R_T * R_S) ∈ idealIp := IdealIp_le_idealIp (gen_S_add_mem_IdealIp (R_T * R_S))
  have h0 : phiPlus (R_S * (R_T * R_S)) + phiPlus (R_T * R_S) = 0 := by
    have := phiPlus_eq_zero_of_mem_idealIp h
    simpa [map_add, add_mul, one_mul] using this
  rw [phiPlus_TS, add_zero] at h0
  simpa [mul_assoc] using h0

lemma phiMinus_STS : phiMinus (R_S * R_T * R_S) = 0 := by
  have h : (R_S - 1) * (R_T * R_S) ∈ idealIm := IdealIm_le_idealIm (gen_S_sub_mem_IdealIm (R_T * R_S))
  have h0 : phiMinus (R_S * (R_T * R_S)) - phiMinus (R_T * R_S) = 0 := by
    have := phiMinus_eq_zero_of_mem_idealIm h
    simpa [map_sub, sub_mul, one_mul] using this
  rw [phiMinus_TS, sub_zero] at h0
  simpa [mul_assoc] using h0

/-- Every `r : R` agrees modulo `𝓘` with a linear combination of the basis `M6`. -/
theorem exists_sub_sum_smul_M6_mem_idealI (r : R) :
    ∃ c : Fin 6 → ℂ, r - ∑ i, c i • M6 i ∈ idealI := by
  refine ⟨fun i => (basisI.repr (Submodule.mkQ idealI r)) i, ?_⟩
  have hsum : Submodule.mkQ idealI
        (∑ i : Fin 6, (basisI.repr (Submodule.mkQ idealI r)) i • M6 i)
      = ∑ i : Fin 6, (basisI.repr (Submodule.mkQ idealI r)) i • basisI i := by
    rw [map_sum]
    exact Finset.sum_congr rfl (fun i _ => by rw [map_smul, basisI_apply])
  have hzero : Submodule.mkQ idealI
      (r - ∑ i : Fin 6, (basisI.repr (Submodule.mkQ idealI r)) i • M6 i) = 0 := by
    rw [map_sub, hsum, Module.Basis.sum_repr, sub_self]
  exact (Submodule.Quotient.mk_eq_zero idealI).mp hzero

/-- **The relation between the three functionals of CKMRV (3.12)**: `φ = (φ₊ + φ₋)/2`. -/
theorem phi_eq_half_phiPlus_add_phiMinus (r : R) :
    phi r = (phiPlus r + phiMinus r) / 2 := by
  obtain ⟨c, hc⟩ := exists_sub_sum_smul_M6_mem_idealI r
  have hsplit : r = (r - ∑ i : Fin 6, c i • M6 i) + ∑ i : Fin 6, c i • M6 i := by abel
  rw [hsplit, map_add, map_add, map_add]
  rw [phi_eq_zero_of_mem_idealI hc, phiPlus_eq_zero_of_mem_idealIp (idealI_le_idealIp hc),
    phiMinus_eq_zero_of_mem_idealIm (idealI_le_idealIm hc)]
  simp only [zero_add]
  -- reduce to the six basis values
  have hexp : (∑ i : Fin 6, c i • M6 i)
      = c 0 • (1 : R) + c 1 • R_T + c 2 • (R_T * R_S) + c 3 • R_S + c 4 • (R_S * R_T)
        + c 5 • (R_S * R_T * R_S) := by
    rw [Fin.sum_univ_six, M6_zero, M6_one, M6_two, M6_three, M6_four, M6_five]
  have hphi : ∀ x y z w u v : ℂ,
      phi (x • (1 : R) + y • R_T + z • (R_T * R_S) + w • R_S + u • (R_S * R_T)
          + v • (R_S * R_T * R_S))
        = (phiPlus (x • (1 : R) + y • R_T + z • (R_T * R_S) + w • R_S + u • (R_S * R_T)
            + v • (R_S * R_T * R_S))
          + phiMinus (x • (1 : R) + y • R_T + z • (R_T * R_S) + w • R_S + u • (R_S * R_T)
            + v • (R_S * R_T * R_S))) / 2 := by
    intro x y z w u v
    simp only [map_add, map_smul, phi_one, phi_R_T, phi_TS, phi_R_S, phi_ST, phi_STS,
      phiPlus_one, phiPlus_R_T,
      phiPlus_TS, phiPlus_R_S, phiPlus_ST, phiPlus_STS, phiMinus_one, phiMinus_R_T,
      phiMinus_TS, phiMinus_R_S, phiMinus_ST, phiMinus_STS, smul_eq_mul, mul_zero, mul_one,
      mul_neg, zero_add, add_zero]
    ring
  rw [hexp]
  exact hphi (c 0) (c 1) (c 2) (c 3) (c 4) (c 5)

end Work.Residues
