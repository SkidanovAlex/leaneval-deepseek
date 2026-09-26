/-
# Joint continuity of the cleared kernel `AfunFun`

The function `AfunFun ℓ d τ z = (AfunPlus d z τ + AfunMinus ℓ d z τ)/2` is the average of
the two cleared kernels `K_±^{(d)}` divided by the (nowhere vanishing) denominator
`Δ(τ)Δ(z)^{e}`.  Concretely, with `e = dpow d`,

  `AfunFun ℓ d τ z = (KPlusClear d τ z + KMinusClear ℓ d τ z) / (2 · Δ(τ) · Δ(z)^e)`,

so its continuity as a function of the pair `(τ,z)` follows from the joint continuity of the
two cleared kernels `KPlusClear`, `KMinusClear` and the nonvanishing of the denominator.

Both cleared kernels are finite sums of products

  `φ_i(τ) · Υ_{ij}^{clear}(d,τ,z) · φ̃_j(z)`,   `ψ_i(τ) · Υ_{ij}^{clear}(d,τ,z) · ψ̃_j(z)`,

where the matirx entries `Υ^{clear}` are polynomials in `E₄, E₆, Δ, j(τ), j(z)` (the matrix
formulas of CKMRV Section 4.4, written without any division by `j(τ)-j(z)`), and the basis
vectors are built from `E₂`, the theta functions and the logarithms `𝓛, 𝓛_S`.  All of these
are continuous on `ℍ`, and every ingredient depends on `(τ,z)` only through one of the two
projections, so the whole expression is jointly continuous.

This file proves the continuity from scratch, entry by entry, for the two explicit matrices
of CKMRV, and assembles the result.
-/
import Mathlib
import Submission.Work.Asymptotics.KfunAuxDefs

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology

namespace Work.Asymptotics

open Work.Kernels Work.Residues

/-! ## Continuity of the scalar building blocks on `ℍ` -/

private lemma cafDeltaCont : Continuous (DeltaFun : ℍ → ℂ) :=
  (CuspForm.holo' CuspForm.discriminant).continuous

private lemma cafE4Cont : Continuous (E4Fun : ℍ → ℂ) :=
  (ModularForm.holo' ModularForm.E₄).continuous

private lemma cafE6Cont : Continuous (E6Fun : ℍ → ℂ) :=
  (ModularForm.holo' ModularForm.E₆).continuous

private lemma cafE2Cont : Continuous (E2Fun : ℍ → ℂ) :=
  ClassicalFacts.E2Fun_mem_InP.1.continuous

private lemma cafJCont : Continuous (jInvariantFun : ℍ → ℂ) := by
  rw [show jInvariantFun = fun τ => E4Fun τ ^ 3 / DeltaFun τ from rfl]
  exact (cafE4Cont.pow 3).div cafDeltaCont (fun τ => ClassicalFacts.DeltaFun_ne_zero τ)

private lemma cafUCont : Continuous (UFun : ℍ → ℂ) :=
  (ClassicalFacts.theta00Fun_mem_InP.1.continuous).pow 4

private lemma cafWCont : Continuous (WFun : ℍ → ℂ) :=
  (ClassicalFacts.theta01Fun_mem_InP.1.continuous).pow 4

private lemma cafVCont : Continuous (VFun : ℍ → ℂ) :=
  (ClassicalFacts.theta10Fun_mem_InP.1.continuous).pow 4

private lemma cafXi2Cont : Continuous (xi2Fun : ℍ → ℂ) := by
  rw [show xi2Fun = fun τ => UFun τ + WFun τ from rfl]
  exact cafUCont.add cafWCont

private lemma cafXi4Cont : Continuous (xi4Fun : ℍ → ℂ) := by
  rw [show xi4Fun = fun τ => UFun τ ^ 2 + WFun τ ^ 2 - 2 * VFun τ ^ 2 from rfl]
  exact ((cafUCont.pow 2).add (cafWCont.pow 2)).sub ((cafVCont.pow 2).const_mul 2)

private lemma cafPsi2Cont (ℓ : LogLambdaData) : Continuous (fun τ : ℍ => psi2 ℓ τ) := by
  have h : (fun τ : ℍ => psi2 ℓ τ) = fun τ : ℍ =>
      xi2Fun τ * ℓ.L τ + (-(UFun τ + VFun τ)) * ℓ.L_S τ := by
    funext τ
    show xi2Fun τ * ℓ.L τ + (SlashAction.map (2 : ℤ) ModularGroup.S xi2Fun) τ * ℓ.L_S τ = _
    rw [KernelFacts.xi2Fun_slash_S τ]
  rw [h]
  exact (cafXi2Cont.mul ℓ.holo.continuous).add
    (((cafUCont.add cafVCont).neg).mul ℓ.holo_S.continuous)

private lemma cafPsi4Cont (ℓ : LogLambdaData) : Continuous (fun τ : ℍ => psi4 ℓ τ) := by
  have h : (fun τ : ℍ => psi4 ℓ τ) = fun τ : ℍ =>
      xi4Fun τ * ℓ.L τ + (UFun τ ^ 2 + VFun τ ^ 2 - 2 * WFun τ ^ 2) * ℓ.L_S τ := by
    funext τ
    show xi4Fun τ * ℓ.L τ + (SlashAction.map (4 : ℤ) ModularGroup.S xi4Fun) τ * ℓ.L_S τ = _
    rw [KernelFacts.xi4S_apply τ]
  rw [h]
  exact (cafXi4Cont.mul ℓ.holo.continuous).add
    ((((cafUCont.pow 2).add (cafVCont.pow 2)).sub ((cafWCont.pow 2).const_mul 2)).mul
      ℓ.holo_S.continuous)

private lemma cafE2SCont : Continuous (E2S : ℍ → ℂ) := by
  have h : (E2S : ℍ → ℂ) = fun z : ℍ =>
      E2Fun z - 6 * Complex.I / ((Real.pi : ℂ) * (z : ℂ)) := by
    funext z; exact TildeFacts.E2S_eq z
  rw [h]
  refine Continuous.sub cafE2Cont ?_
  refine continuous_const.div (continuous_const.mul continuous_coe) ?_
  intro z
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) (KernelFacts.kpc_tau_ne_zero z)

private lemma cafFkCont (k : ℤ) : Continuous (fk k : ℍ → ℂ) := by
  have hE8 : Continuous (E8Fun : ℍ → ℂ) := cafE4Cont.pow 2
  have hE10 : Continuous (E10Fun : ℍ → ℂ) := cafE4Cont.mul cafE6Cont
  have hE14 : Continuous (E14Fun : ℍ → ℂ) := (cafE4Cont.pow 2).mul cafE6Cont
  have hq10 : Continuous (fun τ : ℍ => E10Fun τ / DeltaFun τ) :=
    hE10.div cafDeltaCont (fun τ => ClassicalFacts.DeltaFun_ne_zero τ)
  have hq14 : Continuous (fun τ : ℍ => E14Fun τ / DeltaFun τ) :=
    hE14.div cafDeltaCont (fun τ => ClassicalFacts.DeltaFun_ne_zero τ)
  unfold fk
  split_ifs
  · exact hq10
  · exact continuous_const
  · exact hq14
  · exact cafE4Cont
  · exact cafE6Cont
  · exact hE8
  · exact hE10
  · exact cafDeltaCont
  · exact hE14
  · exact continuous_const

private lemma cafPhiCont (i : Fin 3) : Continuous (fun τ : ℍ => phiVec τ i) := by
  fin_cases i
  · change Continuous (fun τ : ℍ => phiVec τ 0)
    have h : (fun τ : ℍ => phiVec τ 0) = fun τ : ℍ => (τ : ℂ) := by funext τ; rfl
    rw [h]; exact continuous_coe
  · change Continuous (fun τ : ℍ => phiVec τ 1)
    have h : (fun τ : ℍ => phiVec τ 1) = fun τ : ℍ =>
        (τ : ℂ) * E2Fun τ - 3 * Complex.I / (Real.pi : ℂ) := by funext τ; rfl
    rw [h]
    exact (continuous_coe.mul cafE2Cont).sub continuous_const
  · change Continuous (fun τ : ℍ => phiVec τ 2)
    have h : (fun τ : ℍ => phiVec τ 2) = fun τ : ℍ =>
        (τ : ℂ) * E2Fun τ ^ 2 - (6 * Complex.I / (Real.pi : ℂ)) * E2Fun τ := by
      funext τ; rfl
    rw [h]
    exact (continuous_coe.mul (cafE2Cont.pow 2)).sub (continuous_const.mul cafE2Cont)

private lemma cafPhitCont (j : Fin 3) : Continuous (fun z : ℍ => phitVec z j) := by
  fin_cases j
  · change Continuous (fun z : ℍ => phitVec z 0)
    have h : (fun z : ℍ => phitVec z 0) = fun z : ℍ => (z : ℂ) ^ 2 := by funext z; rfl
    rw [h]; exact continuous_coe.pow 2
  · change Continuous (fun z : ℍ => phitVec z 1)
    have h : (fun z : ℍ => phitVec z 1) = fun z : ℍ => (z : ℂ) ^ 2 * E2S z := by
      funext z; rfl
    rw [h]; exact (continuous_coe.pow 2).mul cafE2SCont
  · change Continuous (fun z : ℍ => phitVec z 2)
    have h : (fun z : ℍ => phitVec z 2) = fun z : ℍ => (z : ℂ) ^ 2 * (E2S z) ^ 2 := by
      funext z; rfl
    rw [h]; exact (continuous_coe.pow 2).mul (cafE2SCont.pow 2)

private lemma cafPsiVecCont (ℓ : LogLambdaData) (i : Fin 3) :
    Continuous (fun τ : ℍ => psiVec ℓ τ i) := by
  fin_cases i
  · change Continuous (fun τ : ℍ => psiVec ℓ τ 0)
    simpa [psiVec] using (continuous_const : Continuous (fun _ : ℍ => (1 : ℂ)))
  · change Continuous (fun τ : ℍ => psiVec ℓ τ 1)
    simpa [psiVec] using cafPsi2Cont ℓ
  · change Continuous (fun τ : ℍ => psiVec ℓ τ 2)
    simpa [psiVec] using cafPsi4Cont ℓ

private lemma cafPsitVecCont (ℓ : LogLambdaData) (j : Fin 3) :
    Continuous (fun z : ℍ => psitVec ℓ z j) := by
  fin_cases j
  · change Continuous (fun z : ℍ => psitVec ℓ z 0)
    simpa [psitVec] using ℓ.holo.continuous
  · change Continuous (fun z : ℍ => psitVec ℓ z 1)
    simpa [psitVec] using cafWCont
  · change Continuous (fun z : ℍ => psitVec ℓ z 2)
    have h : (fun z : ℍ => psitVec ℓ z 2) = fun z : ℍ => UFun z ^ 2 - VFun z ^ 2 := by
      funext z; rfl
    rw [h]
    exact (cafUCont.pow 2).sub (cafVCont.pow 2)

/-! ## Joint continuity of the diagonal matrices `ΠΔ`, `Π` -/

private lemma cafPiMatDeltaCont (v : Fin 3 → ℤ) :
    Continuous (fun p : ℍ × ℍ => PiMatDelta v p.1) := by
  apply continuous_matrix
  intro i j
  simp only [PiMatDelta, Matrix.diagonal_apply]
  split_ifs
  · exact (cafDeltaCont.comp continuous_fst).mul ((cafFkCont (v i)).comp continuous_fst)
  · exact continuous_const

private lemma cafPiMatCont (v : Fin 3 → ℤ) :
    Continuous (fun p : ℍ × ℍ => PiMat v p.2) := by
  apply continuous_matrix
  intro i j
  simp only [PiMat, Matrix.diagonal_apply]
  split_ifs
  · exact (cafFkCont (v i)).comp continuous_snd
  · exact continuous_const

/-! ## Joint continuity of the two explicit coefficient matrices `Υ_±^{clear}` -/

private lemma cafMatPlus8 : Continuous (fun p : ℍ × ℍ =>
    (!![jInvariantFun p.1 - jInvariantFun p.2, 0, 1;
       -2 * (jInvariantFun p.1 - jInvariantFun p.2), -2, 0; 1, 0, 0] :
      Matrix (Fin 3) (Fin 3) ℂ)) := by
  have hj1 : Continuous (fun p : ℍ × ℍ => jInvariantFun p.1) :=
    cafJCont.comp continuous_fst
  have hj2 : Continuous (fun p : ℍ × ℍ => jInvariantFun p.2) :=
    cafJCont.comp continuous_snd
  have hJ : Continuous (fun p : ℍ × ℍ => jInvariantFun p.1 - jInvariantFun p.2) := hj1.sub hj2
  apply continuous_matrix
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.empty_val']
  all_goals first
    | exact continuous_const
    | exact hJ
    | exact (continuous_const.mul hJ)

private lemma cafMatPlus24 : Continuous (fun p : ℍ × ℍ =>
    (!![6 * (jInvariantFun p.1 - jInvariantFun p.2), 0,
         c1728 - 6 * (jInvariantFun p.1 - jInvariantFun p.2);
       -12 * jInvariantFun p.1 * (jInvariantFun p.1 - jInvariantFun p.2) +
           5 * c1728 * (jInvariantFun p.1 - jInvariantFun p.2),
         -2 * c1728,
         12 * jInvariantFun p.1 * (jInvariantFun p.1 - jInvariantFun p.2) -
           7 * c1728 * (jInvariantFun p.1 - jInvariantFun p.2);
       c1728 + 6 * (jInvariantFun p.1 - jInvariantFun p.2), 0,
         -6 * (jInvariantFun p.1 - jInvariantFun p.2)] :
      Matrix (Fin 3) (Fin 3) ℂ)) := by
  have hj1 : Continuous (fun p : ℍ × ℍ => jInvariantFun p.1) :=
    cafJCont.comp continuous_fst
  have hj2 : Continuous (fun p : ℍ × ℍ => jInvariantFun p.2) :=
    cafJCont.comp continuous_snd
  have hJ : Continuous (fun p : ℍ × ℍ => jInvariantFun p.1 - jInvariantFun p.2) := hj1.sub hj2
  apply continuous_matrix
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.empty_val']
  all_goals first
    | exact continuous_const
    | exact ((continuous_const.mul hj1).mul hJ).add (continuous_const.mul hJ)
    | exact ((continuous_const.mul hj1).mul hJ).sub (continuous_const.mul hJ)
    | exact continuous_const.add (continuous_const.mul hJ)
    | exact continuous_const.sub (continuous_const.mul hJ)
    | exact (continuous_const.mul hJ)

private lemma cafMatMinus8 : Continuous (fun p : ℍ × ℍ =>
    (!![-2 * c1728, 0, 0; 0, 1, -1;
        0, c1728 - jInvariantFun p.1, jInvariantFun p.1] :
      Matrix (Fin 3) (Fin 3) ℂ)) := by
  have hj1 : Continuous (fun p : ℍ × ℍ => jInvariantFun p.1) :=
    cafJCont.comp continuous_fst
  apply continuous_matrix
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.empty_val']
  all_goals first
    | exact continuous_const
    | exact hj1
    | exact (continuous_const.sub hj1)

private lemma cafMatMinus24 : Continuous (fun p : ℍ × ℍ =>
    (!![-2 * c1728, -2 * c1728 * (jInvariantFun p.1 - jInvariantFun p.2), 0;
       0, jInvariantFun p.1 + 2 * (jInvariantFun p.1 - jInvariantFun p.2), -1;
       0, c1728 - 2 * (jInvariantFun p.1 - jInvariantFun p.2) - jInvariantFun p.1, 1] :
      Matrix (Fin 3) (Fin 3) ℂ)) := by
  have hj1 : Continuous (fun p : ℍ × ℍ => jInvariantFun p.1) :=
    cafJCont.comp continuous_fst
  have hj2 : Continuous (fun p : ℍ × ℍ => jInvariantFun p.2) :=
    cafJCont.comp continuous_snd
  have hJ : Continuous (fun p : ℍ × ℍ => jInvariantFun p.1 - jInvariantFun p.2) := hj1.sub hj2
  apply continuous_matrix
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.empty_val']
  all_goals first
    | exact continuous_const
    | exact hj1.add (continuous_const.mul hJ)
    | exact (continuous_const.sub (continuous_const.mul hJ)).sub hj1
    | exact (continuous_const.mul hJ)

private lemma cafUpsilonPlusCont (d : ℕ) :
    Continuous (fun p : ℍ × ℍ => UpsilonPlusClear d p.1 p.2) := by
  by_cases h8 : d = 8
  · subst h8
    simp only [UpsilonPlusClear, ↓reduceIte]
    have hM := ((cafPiMatDeltaCont ![6, 4, 2]).matrix_mul cafMatPlus8).matrix_mul
      (cafPiMatCont ![12, 10, 8])
    exact hM.const_smul ((36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)⁻¹
  · by_cases h24 : d = 24
    · subst h24
      simp only [UpsilonPlusClear, ↓reduceIte]
      have hDz : Continuous (fun p : ℍ × ℍ => DeltaFun p.2) := cafDeltaCont.comp continuous_snd
      have hC : Continuous (fun p : ℍ × ℍ => DeltaFun p.2 • PiMat ![4, 2, 0] p.2) :=
        hDz.smul (cafPiMatCont ![4, 2, 0])
      have hM := ((cafPiMatDeltaCont ![14, 12, 10]).matrix_mul cafMatPlus24).matrix_mul hC
      exact hM.const_smul ((36 : ℂ) * c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)⁻¹
    · have hzero : (fun p : ℍ × ℍ => UpsilonPlusClear d p.1 p.2) = fun _ => 0 := by
        funext p
        simp only [UpsilonPlusClear]
        rw [if_neg h8, if_neg h24]
      rw [hzero]; exact continuous_const

private lemma cafUpsilonMinusCont (d : ℕ) :
    Continuous (fun p : ℍ × ℍ => UpsilonMinusClear d p.1 p.2) := by
  by_cases h8 : d = 8
  · subst h8
    simp only [UpsilonMinusClear, ↓reduceIte]
    have hM := ((cafPiMatDeltaCont ![4, 2, 0]).matrix_mul cafMatMinus8).matrix_mul
      (cafPiMatCont ![10, 8, 6])
    exact hM.const_smul ((2 : ℂ) * c1728 * (Real.pi : ℂ))⁻¹
  · by_cases h24 : d = 24
    · subst h24
      simp only [UpsilonMinusClear, ↓reduceIte]
      have hDz : Continuous (fun p : ℍ × ℍ => DeltaFun p.2) := cafDeltaCont.comp continuous_snd
      have hC : Continuous (fun p : ℍ × ℍ => DeltaFun p.2 • PiMat ![2, 0, -2] p.2) :=
        hDz.smul (cafPiMatCont ![2, 0, -2])
      have hM := ((cafPiMatDeltaCont ![12, 10, 8]).matrix_mul cafMatMinus24).matrix_mul hC
      exact hM.const_smul ((2 : ℂ) * c1728 * (Real.pi : ℂ))⁻¹
    · have hzero : (fun p : ℍ × ℍ => UpsilonMinusClear d p.1 p.2) = fun _ => 0 := by
        funext p
        simp only [UpsilonMinusClear]
        rw [if_neg h8, if_neg h24]
      rw [hzero]; exact continuous_const

/-! ## Joint continuity of the cleared kernels -/

private lemma cafKPlusClearCont (d : ℕ) :
    Continuous (fun p : ℍ × ℍ => KPlusClear d p.1 p.2) := by
  have h : (fun p : ℍ × ℍ => KPlusClear d p.1 p.2) = fun p => ∑ i : Fin 3, ∑ j : Fin 3,
      phiVec p.1 i * UpsilonPlusClear d p.1 p.2 i j * phitVec p.2 j := by
    funext p; rfl
  rw [h]
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro j _
  have hentry : Continuous (fun p : ℍ × ℍ => UpsilonPlusClear d p.1 p.2 i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp (cafUpsilonPlusCont d))
  exact (((cafPhiCont i).comp continuous_fst).mul hentry).mul
    ((cafPhitCont j).comp continuous_snd)

private lemma cafKMinusClearCont (ℓ : LogLambdaData) (d : ℕ) :
    Continuous (fun p : ℍ × ℍ => KMinusClear ℓ d p.1 p.2) := by
  have h : (fun p : ℍ × ℍ => KMinusClear ℓ d p.1 p.2) = fun p => ∑ i : Fin 3, ∑ j : Fin 3,
      psiVec ℓ p.1 i * UpsilonMinusClear d p.1 p.2 i j * psitVec ℓ p.2 j := by
    funext p; rfl
  rw [h]
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro j _
  have hentry : Continuous (fun p : ℍ × ℍ => UpsilonMinusClear d p.1 p.2 i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp (cafUpsilonMinusCont d))
  exact (((cafPsiVecCont ℓ i).comp continuous_fst).mul hentry).mul
    ((cafPsitVecCont ℓ j).comp continuous_snd)

/-! ## The target -/

/-- The cleared kernel `AfunFun`, as a function of the pair `(τ,z)`, is continuous. -/
theorem continuous_AfunFun (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) :
    Continuous (fun p : UpperHalfPlane × UpperHalfPlane => Work.Asymptotics.AfunFun ℓ d p.1 p.2) := by
  have hnum : Continuous (fun p : ℍ × ℍ => KPlusClear d p.1 p.2 + KMinusClear ℓ d p.1 p.2) :=
    (cafKPlusClearCont d).add (cafKMinusClearCont ℓ d)
  have hden : Continuous (fun p : ℍ × ℍ =>
      2 * (DeltaFun p.1 * DeltaFun p.2 ^ dpow d)) :=
    continuous_const.mul ((cafDeltaCont.comp continuous_fst).mul
      ((cafDeltaCont.comp continuous_snd).pow (dpow d)))
  have hne : ∀ p : ℍ × ℍ, 2 * (DeltaFun p.1 * DeltaFun p.2 ^ dpow d) ≠ 0 := by
    intro p
    exact mul_ne_zero (by norm_num) (mul_ne_zero (ClassicalFacts.DeltaFun_ne_zero p.1)
      (pow_ne_zero _ (ClassicalFacts.DeltaFun_ne_zero p.2)))
  have h : (fun p : ℍ × ℍ => AfunFun ℓ d p.1 p.2) = fun p =>
      (KPlusClear d p.1 p.2 + KMinusClear ℓ d p.1 p.2) /
        (2 * (DeltaFun p.1 * DeltaFun p.2 ^ dpow d)) := by
    funext p
    rw [AfunFun, AfunPlus, AfunMinus]
    ring
  rw [h]
  exact hnum.div hden hne

end Work.Asymptotics
