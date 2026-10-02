import Mathlib
import Submission.Work.ThomBordism.Grassmann.Smooth.BasicDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

/-!
# The projection/section calculus of the coordinate sets

The identities satisfied by `projS`, `projC`, `inclS`, `inclC` (BasicDefs): the projections retract
the sections, they annihilate the other section, and every vector is the sum of its `S`-part and its
complement part.  The proofs are done on the function space and transported along `ambify`.
-/

open scoped Topology

namespace Work.ThomBordism.Grassmann.Smooth

noncomputable section

variable {k m : ℕ}

/-! ## Unfolding lemmas (definitional, but stated so that `rw` can use them) -/

theorem projS_eq (S : ChartIdx k m) : projS S = ambify (projSFun S) := rfl
theorem projC_eq (S : ChartIdx k m) : projC S = ambify (projCFun S) := rfl
theorem inclS_eq (S : ChartIdx k m) : inclS S = ambify (inclSFun S) := rfl
theorem inclC_eq (S : ChartIdx k m) : inclC S = ambify (inclCFun S) := rfl

/-! ## The function-space level -/

theorem inclSFun_single (S : ChartIdx k m) (i : Fin k) :
    inclSFun S (Pi.single i 1) = Pi.single (idxS S i) 1 := by
  simp only [inclSFun, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; rw [Pi.single_eq_of_ne hj, zero_smul]
  · intro hi; exact absurd (Finset.mem_univ i) hi

theorem inclCFun_single (S : ChartIdx k m) (j : Fin m) :
    inclCFun S (Pi.single j 1) = Pi.single (idxC S j) 1 := by
  simp only [inclCFun, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro j' _ hj; rw [Pi.single_eq_of_ne hj, zero_smul]
  · intro hj; exact absurd (Finset.mem_univ j) hj

theorem inclSFun_apply (S : ChartIdx k m) (v : Fin k → ℝ) (y : Fin (k + m)) :
    inclSFun S v y = if h : y ∈ S.1 then v ((S.1.equivFinOfCardEq S.2) ⟨y, h⟩) else 0 := by
  classical
  have hterm : ∀ i : Fin k, (v i • (Pi.single (idxS S i) 1 : Fin (k + m) → ℝ)) y
      = if y = idxS S i then v i else 0 := by
    intro i
    rw [Pi.smul_apply, Pi.single_apply]
    split_ifs with h
    · rw [smul_eq_mul, mul_one]
    · exact smul_zero _
  have hsum : inclSFun S v = ∑ i : Fin k, v i • (Pi.single (idxS S i) 1 : Fin (k + m) → ℝ) := by
    simp only [inclSFun, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.proj_apply]
  rw [hsum, Finset.sum_apply]
  simp only [hterm]
  by_cases hy : y ∈ S.1
  · rw [dif_pos hy]
    rw [Finset.sum_eq_single ((S.1.equivFinOfCardEq S.2) ⟨y, hy⟩)]
    · rw [if_pos (idxS_apply S y hy).symm]
    · intro i _ hi
      rw [if_neg (fun hc => hi (idxS_injective S (hc.symm.trans (idxS_apply S y hy).symm)))]
    · intro hi; exact absurd (Finset.mem_univ _) hi
  · rw [dif_neg hy]
    rw [Finset.sum_eq_zero]
    · intro i _
      rw [if_neg (fun (hc : y = idxS S i) => hy (hc.symm ▸ idxS_mem S i))]

theorem inclCFun_apply (S : ChartIdx k m) (v : Fin m → ℝ) (y : Fin (k + m)) :
    inclCFun S v y
      = if h : y ∈ S.1ᶜ then v ((S.1ᶜ.equivFinOfCardEq (card_compl S)) ⟨y, h⟩) else 0 := by
  classical
  have hterm : ∀ j : Fin m, (v j • (Pi.single (idxC S j) 1 : Fin (k + m) → ℝ)) y
      = if y = idxC S j then v j else 0 := by
    intro j
    rw [Pi.smul_apply, Pi.single_apply]
    split_ifs with h
    · rw [smul_eq_mul, mul_one]
    · exact smul_zero _
  have hsum : inclCFun S v = ∑ j : Fin m, v j • (Pi.single (idxC S j) 1 : Fin (k + m) → ℝ) := by
    simp only [inclCFun, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.proj_apply]
  rw [hsum, Finset.sum_apply]
  simp only [hterm]
  by_cases hy : y ∈ S.1ᶜ
  · rw [dif_pos hy]
    rw [Finset.sum_eq_single ((S.1ᶜ.equivFinOfCardEq (card_compl S)) ⟨y, hy⟩)]
    · rw [if_pos (idxC_apply S y hy).symm]
    · intro j _ hj
      rw [if_neg (fun hc => hj (idxC_injective S (hc.symm.trans (idxC_apply S y hy).symm)))]
    · intro hj; exact absurd (Finset.mem_univ _) hj
  · rw [dif_neg hy]
    rw [Finset.sum_eq_zero]
    · intro j _
      rw [if_neg (fun (hc : y = idxC S j) =>
        hy (hc.symm ▸ Finset.mem_compl.mpr (idxC_not_mem S j)))]

/-- The `i`-th element of `S` maps back to `i`. -/
@[simp] theorem equivFin_idxS (S : ChartIdx k m) (i : Fin k) :
    (S.1.equivFinOfCardEq S.2) ⟨idxS S i, idxS_mem S i⟩ = i := by
  simp only [idxS]
  exact (S.1.equivFinOfCardEq S.2).apply_symm_apply i

/-- The `j`-th element of the complement of `S` maps back to `j`. -/
@[simp] theorem equivFin_idxC (S : ChartIdx k m) (j : Fin m) :
    (S.1ᶜ.equivFinOfCardEq (card_compl S))
      ⟨idxC S j, Finset.mem_compl.mpr (idxC_not_mem S j)⟩ = j := by
  simp only [idxC]
  exact (S.1ᶜ.equivFinOfCardEq (card_compl S)).apply_symm_apply j

theorem projSFun_inclSFun (S : ChartIdx k m) : projSFun S ∘SL inclSFun S = 1 := by
  ext v i
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply, projSFun_apply,
    inclSFun_apply, dif_pos (idxS_mem S i), equivFin_idxS]

theorem projCFun_inclCFun (S : ChartIdx k m) : projCFun S ∘SL inclCFun S = 1 := by
  ext v j
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply, projCFun_apply,
    inclCFun_apply, dif_pos (Finset.mem_compl.mpr (idxC_not_mem S j)), equivFin_idxC]

theorem projSFun_inclCFun (S : ChartIdx k m) : projSFun S ∘SL inclCFun S = 0 := by
  ext v i
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply, projSFun_apply,
    inclCFun_apply, dif_neg (by simp [Finset.mem_compl, idxS_mem S i])]
  rfl

theorem projCFun_inclSFun (S : ChartIdx k m) : projCFun S ∘SL inclSFun S = 0 := by
  ext v j
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply, projCFun_apply,
    inclSFun_apply, dif_neg (idxC_not_mem S j)]
  rfl

theorem inclSFun_projSFun_add_inclCFun_projCFun (S : ChartIdx k m) (x : Fin (k + m) → ℝ) :
    inclSFun S (projSFun S x) + inclCFun S (projCFun S x) = x := by
  funext y
  rw [Pi.add_apply, inclSFun_apply, inclCFun_apply]
  by_cases h : y ∈ S.1
  · rw [dif_pos h, dif_neg (by rw [Finset.mem_compl]; exact fun h' => h' h), add_zero,
      projSFun_apply, idxS_apply S y h]
  · rw [dif_neg h, dif_pos (Finset.mem_compl.mpr h), zero_add, projCFun_apply,
      idxC_apply S y (Finset.mem_compl.mpr h)]

/-! ## The `Amb` level -/

theorem projS_inclS (S : ChartIdx k m) : projS S ∘SL inclS S = 1 := by
  rw [projS_eq, inclS_eq, ← ambify_comp, projSFun_inclSFun, ambify_one]

theorem projS_inclC (S : ChartIdx k m) : projS S ∘SL inclC S = 0 := by
  rw [projS_eq, inclC_eq, ← ambify_comp, projSFun_inclCFun, ambify_zero]

theorem projC_inclS (S : ChartIdx k m) : projC S ∘SL inclS S = 0 := by
  rw [projC_eq, inclS_eq, ← ambify_comp, projCFun_inclSFun, ambify_zero]

theorem projC_inclC (S : ChartIdx k m) : projC S ∘SL inclC S = 1 := by
  rw [projC_eq, inclC_eq, ← ambify_comp, projCFun_inclCFun, ambify_one]

theorem inclS_projS_add_inclC_projC (S : ChartIdx k m) (x : Amb (k + m)) :
    inclS S (projS S x) + inclC S (projC S x) = x := by
  refine WithLp.ofLp_injective 2 ?_
  have h1 : (inclS S (projS S x) + inclC S (projC S x)).ofLp
      = ofLpCLM (k + m) (inclS S (projS S x)) + ofLpCLM (k + m) (inclC S (projC S x)) := rfl
  rw [h1, inclS_ofLp, inclC_ofLp, projS_eq, projC_eq, ofLpCLM_ambify, ofLpCLM_ambify,
    ofLpCLM_apply]
  exact inclSFun_projSFun_add_inclCFun_projCFun S (ofLpCLM (k + m) x)

theorem inclS_ofLp_apply (S : ChartIdx k m) (v : Amb k) (y : Fin (k + m)) :
    (inclS S v).ofLp y
      = if h : y ∈ S.1 then v.ofLp ((S.1.equivFinOfCardEq S.2) ⟨y, h⟩) else 0 := by
  have h1 : (inclS S v).ofLp = inclSFun S v.ofLp := by
    rw [show (inclS S v).ofLp = ofLpCLM (k + m) (inclS S v) from rfl, inclS_ofLp, ofLpCLM_apply]
  rw [h1, inclSFun_apply]

theorem inclC_ofLp_apply (S : ChartIdx k m) (w : Amb m) (y : Fin (k + m)) :
    (inclC S w).ofLp y
      = if h : y ∈ S.1ᶜ then w.ofLp ((S.1ᶜ.equivFinOfCardEq (card_compl S)) ⟨y, h⟩) else 0 := by
  have h1 : (inclC S w).ofLp = inclCFun S w.ofLp := by
    rw [show (inclC S w).ofLp = ofLpCLM (k + m) (inclC S w) from rfl, inclC_ofLp, ofLpCLM_apply]
  rw [h1, inclCFun_apply]

@[simp] theorem projS_apply_amb (S : ChartIdx k m) (x : Amb (k + m)) (i : Fin k) :
    projS S x i = x (idxS S i) := by
  have h1 : projS S x = ambify (projSFun S) x := rfl
  rw [h1, show (ambify (projSFun S) x : Amb k).ofLp i = projSFun S x.ofLp i from by
    rw [← ofLpCLM_apply, ofLpCLM_ambify, ofLpCLM_apply]]
  rw [projSFun_apply]

@[simp] theorem projC_apply_amb (S : ChartIdx k m) (x : Amb (k + m)) (j : Fin m) :
    projC S x j = x (idxC S j) := by
  have h1 : projC S x = ambify (projCFun S) x := rfl
  rw [h1, show (ambify (projCFun S) x : Amb m).ofLp j = projCFun S x.ofLp j from by
    rw [← ofLpCLM_apply, ofLpCLM_ambify, ofLpCLM_apply]]
  rw [projCFun_apply]

end

end Work.ThomBordism.Grassmann.Smooth
