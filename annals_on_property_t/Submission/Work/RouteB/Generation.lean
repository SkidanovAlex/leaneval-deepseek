import Submission.Work.RouteB.IndexTwo
import Submission.Work.NielsenTheorem
import Submission.Work.Transpositions

open OnPropertyT Submission.FreeGroupAut
open FreeGroup
open scoped BigOperators

set_option autoImplicit false

namespace Submission.Nielsen

noncomputable section

variable {n : ℕ}

/-!
# The transvections plus one inversion generate `Aut(F_n)`

The paper's property-(T) certificate is for `SAut(F_n)` with the standard
transvection generating set `SAutGen n = {ρᵢⱼ^{±1}, λᵢⱼ^{±1}}`.  The index-two
ascent `RouteB.propertyT_of_index_two_extension` then needs to know that
`SAutGen n ∪ {σᵢ}` still generates the whole of `Aut(F_n)` (where `σᵢ` inverts
the `i`-th generator).  This file proves that:

    closure (insert (sigma i) (SAutGen n)) = ⊤        (`i : Fin n`)

The argument uses Nielsen's theorem `aut_nielsen` (`closure (AutGen n) = ⊤`, from
`Submission/Work/NielsenTheorem.lean`) together with the transposition
decomposition `τᵢⱼ = σᵢ · λᵢⱼ · λⱼᵢ⁻¹ · ρᵢⱼ` (`tau_decomposition`): since the
conjugate `τᵢⱼ σᵢ τᵢⱼ⁻¹` is `σⱼ`, every single-generator inversion lies in
`closure (SAutGen n ∪ {σᵢ})`, and with the transvections this is all of
`AutGen n`.
-/

/-- `ρᵢⱼ` is a transvection generator of `SAut(F_n)`. -/
lemma rho_mem_SAutGen (n : ℕ) {i j : Fin n} (hij : i ≠ j) :
    rho i j hij ∈ (SAutGen n : Set (MulAut (FreeGroup (Fin n)))) := by
  classical
  rw [SAutGen]
  exact Finset.mem_image.mpr ⟨⟨((i, j), (true, true)), hij⟩, Finset.mem_univ _, by simp [sAutAut]⟩

/-- `ρᵢⱼ⁻¹` is a transvection generator of `SAut(F_n)`. -/
lemma rhoNeg_mem_SAutGen (n : ℕ) {i j : Fin n} (hij : i ≠ j) :
    rhoNeg i j hij ∈ (SAutGen n : Set (MulAut (FreeGroup (Fin n)))) := by
  classical
  rw [SAutGen]
  exact Finset.mem_image.mpr ⟨⟨((i, j), (true, false)), hij⟩, Finset.mem_univ _, by simp [sAutAut]⟩

/-- `λᵢⱼ` is a transvection generator of `SAut(F_n)`. -/
lemma lam_mem_SAutGen (n : ℕ) {i j : Fin n} (hij : i ≠ j) :
    lam i j hij ∈ (SAutGen n : Set (MulAut (FreeGroup (Fin n)))) := by
  classical
  rw [SAutGen]
  exact Finset.mem_image.mpr ⟨⟨((i, j), (false, true)), hij⟩, Finset.mem_univ _, by simp [sAutAut]⟩

/-- `λᵢⱼ⁻¹` is a transvection generator of `SAut(F_n)`. -/
lemma lamNeg_mem_SAutGen (n : ℕ) {i j : Fin n} (hij : i ≠ j) :
    lamNeg i j hij ∈ (SAutGen n : Set (MulAut (FreeGroup (Fin n)))) := by
  classical
  rw [SAutGen]
  exact Finset.mem_image.mpr ⟨⟨((i, j), (false, false)), hij⟩, Finset.mem_univ _, by simp [sAutAut]⟩

/-- The transposition automorphism is an involution. -/
lemma tau_mul_self (i j : Fin n) (hij : i ≠ j) : tau i j hij * tau i j hij = 1 := by
  ext x
  have h := congrArg (fun φ : FreeGroup (Fin n) →* FreeGroup (Fin n) => φ x)
    (tauHom_comp_self i j hij)
  simpa [tau] using h

/-- **Conjugating an inversion by the transposition gives the other inversion:**
`τᵢⱼ · σᵢ · τᵢⱼ⁻¹ = σⱼ`. -/
lemma tau_conj_sigma (i j : Fin n) (hij : i ≠ j) :
    tau i j hij * sigma i * (tau i j hij)⁻¹ = sigma j := by
  have hji : j ≠ i := fun h => hij h.symm
  have hinv : (tau i j hij)⁻¹ = tau i j hij :=
    inv_eq_of_mul_eq_one_right (tau_mul_self i j hij)
  have hhom : ((tau i j hij * sigma i * (tau i j hij)⁻¹ : MulAut (FreeGroup (Fin n))) :
      FreeGroup (Fin n) →* FreeGroup (Fin n))
      = (sigma j : FreeGroup (Fin n) →* FreeGroup (Fin n)) := by
    apply FreeGroup.ext_hom
    intro k
    rw [hinv]
    change (tau i j hij) ((sigma i) ((tau i j hij) (FreeGroup.of k))) = (sigma j) (FreeGroup.of k)
    by_cases hki : k = i
    · subst k
      rw [tau_apply_i i j hij, sigma_apply_other hji, tau_apply_j i j hij,
        sigma_apply_other hij]
    · by_cases hkj : k = j
      · subst k
        rw [tau_apply_j i j hij, sigma_apply_self]
        rw [show (tau i j hij) ((FreeGroup.of i)⁻¹)
              = ((tau i j hij) (FreeGroup.of i))⁻¹ from
            (tau i j hij : FreeGroup (Fin n) →* FreeGroup (Fin n)).map_inv _]
        rw [tau_apply_i i j hij]
        exact (sigma_apply_self j).symm
      · rw [tau_apply_other hij hki hkj, sigma_apply_other hki,
          tau_apply_other hij hki hkj, sigma_apply_other hkj]
  ext x
  exact congrArg (fun φ : FreeGroup (Fin n) →* FreeGroup (Fin n) => φ x) hhom


/-- **The transvections together with one inversion generate `Aut(F_n)`:**
for every `i : Fin n`,
`closure (SAutGen n ∪ {σᵢ}) = ⊤`.  This is the generation input of the index-two
ascent `RouteB.propertyT_of_index_two_extension` applied to
`SAut(F_n) ⊆ Aut(F_n)`. -/
theorem closure_sAutGen_insert_sigma (n : ℕ) (i : Fin n) :
    Subgroup.closure ((insert (sigma i) (SAutGen n) :
        Finset (MulAut (FreeGroup (Fin n)))) : Set (MulAut (FreeGroup (Fin n)))) = ⊤ := by
  classical
  let C : Subgroup (MulAut (FreeGroup (Fin n))) :=
    Subgroup.closure ((insert (sigma i) (SAutGen n) :
      Finset (MulAut (FreeGroup (Fin n)))) : Set (MulAut (FreeGroup (Fin n))))
  have hsig : ∀ j : Fin n, sigma j ∈ C := by
    intro j
    by_cases hji : j = i
    · rw [hji]
      exact Subgroup.subset_closure (Finset.mem_insert_self _ _)
    · have hij : i ≠ j := fun h => hji h.symm
      have htau : tau i j hij ∈ C := by
        rw [tau_decomposition i j hij, tauWord]
        refine C.mul_mem (C.mul_mem (C.mul_mem ?_ ?_) ?_) ?_
        · exact Subgroup.subset_closure (Finset.mem_insert_self _ _)
        · exact Subgroup.subset_closure (Finset.mem_insert_of_mem (lam_mem_SAutGen n hij))
        · exact Subgroup.subset_closure (Finset.mem_insert_of_mem
            (lamNeg_mem_SAutGen n (fun h : j = i => hij h.symm)))
        · exact Subgroup.subset_closure (Finset.mem_insert_of_mem (rho_mem_SAutGen n hij))
      have hsigi : sigma i ∈ C :=
        Subgroup.subset_closure (Finset.mem_insert_self _ _)
      rw [← tau_conj_sigma i j hij]
      exact C.mul_mem (C.mul_mem htau hsigi) (C.inv_mem htau)
  have hsub : (AutGen n : Set (MulAut (FreeGroup (Fin n)))) ⊆ C := by
    intro g hg
    rw [AutGen, Finset.mem_coe, Finset.mem_union] at hg
    rcases hg with hg | hg
    · exact Subgroup.subset_closure (Finset.mem_insert_of_mem hg)
    · rw [SigmaSet] at hg
      rcases Finset.mem_image.mp hg with ⟨k, _, hk⟩
      rw [← hk]
      exact hsig k
  have htop : (⊤ : Subgroup (MulAut (FreeGroup (Fin n)))) ≤ C := by
    rw [← aut_nielsen n]
    exact (Subgroup.closure_le C).mpr hsub
  exact le_antisymm le_top htop

end

end Submission.Nielsen
