import Mathlib
import Submission.Work.Modular.GroupAlgebra
import Submission.Work.Modular.basisElem_mul_sR

namespace Work.Modular

open Work.Modular
open scoped MonoidAlgebra

noncomputable section

/-- Row-vector form of multiplying a six-tuple of group-algebra elements on the right by a
matrix: `∑ j, A i j • (∑ k, B j k • M k) = ∑ k, (A * B) i k • M k`. -/
private theorem matRow_smul_sum (A B : Matrix (Fin 6) (Fin 6) ℂ) (M : Fin 6 → GroupRing)
    (i : Fin 6) :
    (∑ j, A i j • (∑ k, B j k • M k)) = ∑ k, (A * B) i k • M k := by
  simp only [Matrix.mul_apply, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul]

/-- The right ideal `I` is closed under right multiplication: `x ∈ I → x * r ∈ I`. -/
private theorem idealI_mul_mem {x : GroupRing} (hx : x ∈ idealI) (r : GroupRing) :
    x * r ∈ idealI := by
  refine Submodule.span_induction (p := fun y _ => y * r ∈ idealI) ?_ ?_ ?_ ?_ hx
  · rintro y (⟨s, rfl⟩ | ⟨s, rfl⟩)
    · exact Submodule.subset_span (Or.inl ⟨s * r, by rw [mul_assoc]⟩)
    · exact Submodule.subset_span (Or.inr ⟨s * r, by rw [mul_assoc]⟩)
  · rw [zero_mul]; exact Submodule.zero_mem _
  · intro y z _ _ hy hz; rw [add_mul]; exact Submodule.add_mem _ hy hz
  · intro a y _ hy; rw [smul_mul_assoc]; exact Submodule.smul_mem _ a hy

/-- The "error vector" of the six-dimensional representation: the `i`-th entry of
`vec M · γ - σ(γ) vec M`. The paper's equation (3.7) says this lies in `I`. -/
private def rowDiff (γ : Gamma) (i : Fin 6) : GroupRing :=
  basisElem i * MonoidAlgebra.of ℂ Gamma γ -
    ∑ j, (sigmaAlg (MonoidAlgebra.of ℂ Gamma γ)) i j • basisElem j

/-- `rowDiff` at the identity vanishes. -/
private theorem rowDiff_one (i : Fin 6) : rowDiff 1 i ∈ idealI := by
  have h : rowDiff 1 i = 0 := by
    simp only [rowDiff, map_one, Matrix.one_apply, mul_one]
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb; rw [if_neg (Ne.symm hb), zero_smul]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  rw [h]; exact Submodule.zero_mem _

/-- The group-algebra relation `T S T S T = S`, the group-ring form of `(S T) ^ 3 = 1`. -/
private theorem sR_tR_sR_tR_rel : tR * sR * tR * sR * tR = sR := by
  have hcube : sR * tR * sR * tR * sR * tR = 1 := by
    simpa [pow_succ, pow_two, mul_assoc] using sR_mul_tR_cube
  have h := congrArg (fun x => sR * x) hcube
  simp only [mul_one] at h
  have key : sR * (sR * tR * sR * tR * sR * tR) = tR * sR * tR * sR * tR := by
    calc sR * (sR * tR * sR * tR * sR * tR)
        = (sR * sR) * (tR * sR * tR * sR * tR) := by noncomm_ring
      _ = 1 * (tR * sR * tR * sR * tR) := by rw [← pow_two, sR_sq]
      _ = tR * sR * tR * sR * tR := by rw [one_mul]
  rw [key] at h
  exact h

/-- The `i = 2` (paper's `M_3`) computation: `TST + STS - 2 = S (T - 1)² T⁻¹ S`. -/
private theorem rowDiff_aux2 :
    tR * sR * tR - 2 + sR * tR * sR = sR * (tR - 1) ^ 2 * (sR * tR * sR * tR) := by
  rw [show (tR - 1) ^ 2 = tR * tR - 2 * tR + 1 by noncomm_ring]
  rw [show sR * (tR * tR - 2 * tR + 1) * (sR * tR * sR * tR)
      = sR * (tR * (tR * sR * tR * sR * tR)) - 2 * (sR * (tR * sR * tR * sR * tR))
        + (sR * sR) * (tR * sR * tR) by noncomm_ring]
  rw [sR_tR_sR_tR_rel, ← pow_two, sR_sq]
  simp only [mul_one, one_mul]
  noncomm_ring

/-- The `i = 5` (paper's `M_6`) computation: `STST + TS - 2S = (T - 1)² T⁻¹ S`. -/
private theorem rowDiff_aux5 :
    sR * tR * sR * tR + tR * sR - 2 * sR = (tR - 1) ^ 2 * (sR * tR * sR * tR) := by
  rw [show (tR - 1) ^ 2 = tR * tR - 2 * tR + 1 by noncomm_ring]
  rw [show (tR * tR - 2 * tR + 1) * (sR * tR * sR * tR)
      = tR * (tR * sR * tR * sR * tR) - 2 * (tR * sR * tR * sR * tR)
        + (sR * tR * sR * tR) by noncomm_ring]
  rw [sR_tR_sR_tR_rel]
  noncomm_ring

/-- Right multiplication by `S` on a basis element agrees exactly with `σ(S)`. -/
private theorem rowDiff_genS (i : Fin 6) : rowDiff genS i ∈ idealI := by
  have h : rowDiff genS i = 0 := by
    simp only [rowDiff]
    rw [show MonoidAlgebra.of ℂ Gamma genS = sR from rfl, sigmaAlg_sR, basisElem_mul_sR]
    exact sub_self _
  rw [h]; exact Submodule.zero_mem _

/-- Right multiplication by `T` on a basis element agrees with `σ(T)` modulo `I`: this is the
paper's computation `vec M · T = σ(T) vec M + I`. -/
private theorem rowDiff_genT (i : Fin 6) : rowDiff genT i ∈ idealI := by
  simp only [rowDiff]
  rw [show MonoidAlgebra.of ℂ Gamma genT = tR from rfl, sigmaAlg_tR]
  fin_cases i
  · change basisElem 0 * tR - ∑ j, sigmaT 0 j • basisElem j ∈ idealI
    rw [show basisElem 0 * tR - ∑ j, sigmaT 0 j • basisElem j = 0 by
      simp [basisElem, sigmaT, Fin.sum_univ_six]]
    exact Submodule.zero_mem _
  · change basisElem 1 * tR - ∑ j, sigmaT 1 j • basisElem j ∈ idealI
    rw [show basisElem 1 * tR - ∑ j, sigmaT 1 j • basisElem j = (tR - 1) ^ 2 by
      simp [basisElem, sigmaT, Fin.sum_univ_six, two_smul]
      noncomm_ring]
    exact Submodule.subset_span (Or.inl ⟨1, by rw [mul_one]⟩)
  · change basisElem 2 * tR - ∑ j, sigmaT 2 j • basisElem j ∈ idealI
    rw [show basisElem 2 * tR - ∑ j, sigmaT 2 j • basisElem j
        = sR * (tR - 1) ^ 2 * (sR * tR * sR * tR) by
      have hL : basisElem 2 * tR - ∑ j, sigmaT 2 j • basisElem j
          = tR * sR * tR - 2 + sR * tR * sR := by
        simp [basisElem, sigmaT, Fin.sum_univ_six, two_smul]
        rw [one_add_one_eq_two]
        abel
      rw [hL, rowDiff_aux2]]
    exact Submodule.subset_span (Or.inr ⟨_, rfl⟩)
  · change basisElem 3 * tR - ∑ j, sigmaT 3 j • basisElem j ∈ idealI
    rw [show basisElem 3 * tR - ∑ j, sigmaT 3 j • basisElem j = 0 by
      simp [basisElem, sigmaT, Fin.sum_univ_six]]
    exact Submodule.zero_mem _
  · change basisElem 4 * tR - ∑ j, sigmaT 4 j • basisElem j ∈ idealI
    rw [show basisElem 4 * tR - ∑ j, sigmaT 4 j • basisElem j = sR * (tR - 1) ^ 2 by
      simp [basisElem, sigmaT, Fin.sum_univ_six, two_smul]
      rw [show sR * tR + sR * tR = 2 * (sR * tR) by rw [two_mul]]
      rw [show (tR - 1) ^ 2 = tR * tR - 2 * tR + 1 by noncomm_ring]
      rw [show sR * (tR * tR - 2 * tR + 1) = sR * tR * tR - 2 * (sR * tR) + sR
        by noncomm_ring]
      abel]
    exact Submodule.subset_span (Or.inr ⟨1, by rw [mul_one]⟩)
  · change basisElem 5 * tR - ∑ j, sigmaT 5 j • basisElem j ∈ idealI
    rw [show basisElem 5 * tR - ∑ j, sigmaT 5 j • basisElem j
        = (tR - 1) ^ 2 * (sR * tR * sR * tR) by
      have hL : basisElem 5 * tR - ∑ j, sigmaT 5 j • basisElem j
          = sR * tR * sR * tR + tR * sR - 2 * sR := by
        simp [basisElem, sigmaT, Fin.sum_univ_six, two_smul]
        rw [show sR + sR = 2 * sR by rw [two_mul]]
        abel
      rw [hL, rowDiff_aux5]]
    exact Submodule.subset_span (Or.inl ⟨_, rfl⟩)

/-- The cocycle identity: the error vector at `γ * δ` is `σ(γ)` applied to the error vector at
`δ`, plus the error vector at `γ` right-multiplied by `δ`. -/
private theorem rowDiff_mul (γ δ : Gamma) (i : Fin 6) :
    rowDiff (γ * δ) i = ∑ j, (sigmaAlg (MonoidAlgebra.of ℂ Gamma γ)) i j • rowDiff δ j
      + rowDiff γ i * MonoidAlgebra.of ℂ Gamma δ := by
  simp only [rowDiff, map_mul]
  have hY := matRow_smul_sum (sigmaAlg ((MonoidAlgebra.of ℂ Gamma) γ))
    (sigmaAlg ((MonoidAlgebra.of ℂ Gamma) δ)) basisElem i
  simp only [smul_sub, Finset.sum_sub_distrib, sub_mul, Finset.sum_mul, smul_mul_assoc]
  rw [hY]
  noncomm_ring

/-- The error vector stays in `I ^ 6` under right multiplication. -/
private theorem rowDiff_mul_mem {γ δ : Gamma}
    (hγ : ∀ i, rowDiff γ i ∈ idealI) (hδ : ∀ i, rowDiff δ i ∈ idealI) :
    ∀ i, rowDiff (γ * δ) i ∈ idealI := by
  intro i
  rw [rowDiff_mul]
  refine Submodule.add_mem _ ?_ (idealI_mul_mem (hγ i) _)
  exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (hδ j))

/-- The inverse of `genT` written as a product of the two generators. -/
private theorem genT_inv_eq : genT⁻¹ = genS * genT * genS * genT * genS := by
  have hrel : genT * genS * genT * genS * genT = genS := by
    have hcube : genS * genT * genS * genT * genS * genT = 1 := by
      simpa [pow_succ, pow_two, mul_assoc] using genS_mul_genT_cube
    have h := congrArg (fun x => genS * x) hcube
    simp only [mul_one] at h
    have key : genS * (genS * genT * genS * genT * genS * genT)
        = genT * genS * genT * genS * genT := by
      simp only [mul_assoc]
      rw [← mul_assoc, ← pow_two, genS_sq, one_mul]
    rw [key] at h
    exact h
  have hw : genT * (genS * genT * genS * genT * genS) = 1 := by
    calc genT * (genS * genT * genS * genT * genS)
        = (genT * genS * genT * genS * genT) * genS := by group
      _ = genS * genS := by rw [hrel]
      _ = 1 := by rw [← pow_two, genS_sq]
  exact inv_eq_of_mul_eq_one_right hw

/-- The inverse of `genS` is `genS`. -/
private theorem genS_inv_eq : genS⁻¹ = genS := by
  rw [inv_eq_iff_mul_eq_one, ← pow_two, genS_sq]

/-- **Equation (3.7) of the paper.** The six-dimensional representation `σ` describes the right
action of `ℂ[Γ]` on `ℂ[Γ]/I`: right multiplication of the basis element `M i` by the group
element `γ` agrees with `σ (γ)` applied to the row vector `M` modulo the ideal `I`. -/
theorem mul_basisElem_sub_mem_idealI (γ : Gamma) (i : Fin 6) :
    basisElem i * MonoidAlgebra.of ℂ Gamma γ -
      ∑ j, (sigmaAlg (MonoidAlgebra.of ℂ Gamma γ)) i j • basisElem j ∈ idealI := by
  have key : ∀ γ : Gamma, ∀ i : Fin 6, rowDiff γ i ∈ idealI := by
    intro γ
    refine PresentedGroup.induction_on (C := fun x => ∀ i, rowDiff x i ∈ idealI) γ ?_
    intro z
    refine FreeGroup.induction_on
      (motive := fun w => ∀ i, rowDiff (PresentedGroup.mk presentedRels w) i ∈ idealI) z ?_ ?_ ?_ ?_
    · intro i
      simp only [map_one]
      exact rowDiff_one i
    · intro x
      fin_cases x
      · intro i
        change rowDiff genS i ∈ idealI
        exact rowDiff_genS i
      · intro i
        change rowDiff genT i ∈ idealI
        exact rowDiff_genT i
    · intro x hx
      fin_cases x
      · intro i
        change rowDiff genS⁻¹ i ∈ idealI
        rw [genS_inv_eq]
        exact hx i
      · intro i
        change rowDiff genT⁻¹ i ∈ idealI
        rw [genT_inv_eq]
        exact rowDiff_mul_mem
          (rowDiff_mul_mem (rowDiff_mul_mem (rowDiff_mul_mem rowDiff_genS hx) rowDiff_genS)
            hx) rowDiff_genS i
    · intro z1 z2 h1 h2
      rw [map_mul]
      exact rowDiff_mul_mem h1 h2
  exact key γ i

end

end Work.Modular
