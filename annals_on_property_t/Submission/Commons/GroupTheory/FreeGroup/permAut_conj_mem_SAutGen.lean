import Submission.Commons.GroupTheory.FreeGroup.sigma_conj_mem_SAutGen
import Mathlib

open FreeGroup

set_option autoImplicit false

namespace Commons.GroupTheory.FreeGroup

noncomputable section

variable {n : ℕ}

/-- The monoid homomorphism `F_n → F_n` sending `aᵢ ↦ a_{σ i}` for a permutation
`σ` of the basis. -/
def permHom (σ : Equiv.Perm (Fin n)) : FreeGroup (Fin n) →* FreeGroup (Fin n) :=
  FreeGroup.lift (fun i => FreeGroup.of (σ i))

/-- `permHom σ` sends the `i`-th basis element to the `σ i`-th one. -/
lemma permHom_of (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    permHom σ (FreeGroup.of i) = FreeGroup.of (σ i) := by
  simp [permHom]

/-- `permHom` of the identity permutation is the identity. -/
lemma permHom_one : permHom (1 : Equiv.Perm (Fin n)) = MonoidHom.id (FreeGroup (Fin n)) := by
  apply FreeGroup.ext_hom
  intro i
  simp [permHom]

/-- `permHom` is multiplicative. -/
lemma permHom_comp (σ τ : Equiv.Perm (Fin n)) :
    permHom (σ * τ) = (permHom σ).comp (permHom τ) := by
  apply FreeGroup.ext_hom
  intro i
  simp [permHom]

/-- The induced automorphism of `F_n`. -/
def permAut (σ : Equiv.Perm (Fin n)) : MulAut (FreeGroup (Fin n)) where
  toFun := permHom σ
  invFun := permHom σ.symm
  left_inv x := by
    have h : (permHom σ.symm).comp (permHom σ) = MonoidHom.id (FreeGroup (Fin n)) := by
      apply FreeGroup.ext_hom
      intro i
      simp [permHom]
    exact congrFun (congrArg DFunLike.coe h) x
  right_inv x := by
    have h : (permHom σ).comp (permHom σ.symm) = MonoidHom.id (FreeGroup (Fin n)) := by
      apply FreeGroup.ext_hom
      intro i
      simp [permHom]
    exact congrFun (congrArg DFunLike.coe h) x
  map_mul' := (permHom σ).map_mul

/-- `permAut σ` sends the `i`-th basis element to the `σ i`-th one. -/
lemma permAut_apply (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    permAut σ (FreeGroup.of i) = FreeGroup.of (σ i) :=
  permHom_of σ i

/-- `permAut` of the identity permutation is the identity. -/
lemma permAut_one : permAut (1 : Equiv.Perm (Fin n)) = 1 := by
  ext x
  exact congrFun (congrArg DFunLike.coe (permHom_one (n := n))) x

/-- `permAut` is multiplicative. -/
lemma permAut_mul (σ τ : Equiv.Perm (Fin n)) :
    permAut (σ * τ) = permAut σ * permAut τ := by
  ext x
  show permHom (σ * τ) x = permHom σ (permHom τ x)
  rw [permHom_comp]
  rfl

/-- The inverse of `permAut σ` is `permAut σ.symm`. -/
lemma permAut_inv (σ : Equiv.Perm (Fin n)) :
    (permAut σ)⁻¹ = permAut σ.symm := by
  have hs : σ * σ.symm = 1 := by ext y; simp
  have h : permAut σ * permAut σ.symm = 1 := by
    rw [← permAut_mul, hs, permAut_one]
  exact inv_eq_of_mul_eq_one_right h

/-! ### Equivariance of the four families of Nielsen transvections -/

/-- Conjugation by `permAut σ` sends `ρᵢⱼ` to `ρ_{σi,σj}`. -/
lemma permAut_conj_rho (σ : Equiv.Perm (Fin n)) (i j : Fin n) (hij : i ≠ j)
    (hσ : σ i ≠ σ j) :
    permAut σ * rho i j hij * (permAut σ)⁻¹ = rho (σ i) (σ j) hσ := by
  apply mulAut_eq_of_gen_eq
  intro k
  rw [MulAut.mul_apply, MulAut.mul_apply, permAut_inv, permAut_apply]
  by_cases h : σ.symm k = i
  · rw [h, rho_apply_self i j hij, MulEquiv.map_mul, permAut_apply, permAut_apply]
    have hk : k = σ i := by rw [← Equiv.apply_symm_apply σ k, h]
    rw [hk, rho_apply_self (σ i) (σ j) hσ]
  · rw [rho_apply_other hij h, permAut_apply, Equiv.apply_symm_apply]
    have hk : k ≠ σ i := fun hk => h (by rw [hk, Equiv.symm_apply_apply])
    rw [rho_apply_other hσ hk]

/-- Conjugation by `permAut σ` sends `ρᵢⱼ⁻¹` to `ρ_{σi,σj}⁻¹`. -/
lemma permAut_conj_rhoNeg (σ : Equiv.Perm (Fin n)) (i j : Fin n) (hij : i ≠ j)
    (hσ : σ i ≠ σ j) :
    permAut σ * rhoNeg i j hij * (permAut σ)⁻¹ = rhoNeg (σ i) (σ j) hσ := by
  apply mulAut_eq_of_gen_eq
  intro k
  rw [MulAut.mul_apply, MulAut.mul_apply, permAut_inv, permAut_apply]
  by_cases h : σ.symm k = i
  · rw [h, rhoNeg_apply_self i j hij, MulEquiv.map_mul, MulEquiv.map_inv,
      permAut_apply, permAut_apply]
    have hk : k = σ i := by rw [← Equiv.apply_symm_apply σ k, h]
    rw [hk, rhoNeg_apply_self (σ i) (σ j) hσ]
  · rw [rhoNeg_apply_other hij h, permAut_apply, Equiv.apply_symm_apply]
    have hk : k ≠ σ i := fun hk => h (by rw [hk, Equiv.symm_apply_apply])
    rw [rhoNeg_apply_other hσ hk]

/-- Conjugation by `permAut σ` sends `λᵢⱼ` to `λ_{σi,σj}`. -/
lemma permAut_conj_lam (σ : Equiv.Perm (Fin n)) (i j : Fin n) (hij : i ≠ j)
    (hσ : σ i ≠ σ j) :
    permAut σ * lam i j hij * (permAut σ)⁻¹ = lam (σ i) (σ j) hσ := by
  apply mulAut_eq_of_gen_eq
  intro k
  rw [MulAut.mul_apply, MulAut.mul_apply, permAut_inv, permAut_apply]
  by_cases h : σ.symm k = i
  · rw [h, lam_apply_self i j hij, MulEquiv.map_mul, permAut_apply, permAut_apply]
    have hk : k = σ i := by rw [← Equiv.apply_symm_apply σ k, h]
    rw [hk, lam_apply_self (σ i) (σ j) hσ]
  · rw [lam_apply_other hij h, permAut_apply, Equiv.apply_symm_apply]
    have hk : k ≠ σ i := fun hk => h (by rw [hk, Equiv.symm_apply_apply])
    rw [lam_apply_other hσ hk]

/-- Conjugation by `permAut σ` sends `λᵢⱼ⁻¹` to `λ_{σi,σj}⁻¹`. -/
lemma permAut_conj_lamNeg (σ : Equiv.Perm (Fin n)) (i j : Fin n) (hij : i ≠ j)
    (hσ : σ i ≠ σ j) :
    permAut σ * lamNeg i j hij * (permAut σ)⁻¹ = lamNeg (σ i) (σ j) hσ := by
  apply mulAut_eq_of_gen_eq
  intro k
  rw [MulAut.mul_apply, MulAut.mul_apply, permAut_inv, permAut_apply]
  by_cases h : σ.symm k = i
  · rw [h, lamNeg_apply_self i j hij, MulEquiv.map_mul, MulEquiv.map_inv,
      permAut_apply, permAut_apply]
    have hk : k = σ i := by rw [← Equiv.apply_symm_apply σ k, h]
    rw [hk, lamNeg_apply_self (σ i) (σ j) hσ]
  · rw [lamNeg_apply_other hij h, permAut_apply, Equiv.apply_symm_apply]
    have hk : k ≠ σ i := fun hk => h (by rw [hk, Equiv.symm_apply_apply])
    rw [lamNeg_apply_other hσ hk]

/-! ### Membership of the conjugates in `SAutGen n` -/

lemma permAut_conj_rho_mem (σ : Equiv.Perm (Fin n)) (i j : Fin n) (hij : i ≠ j) :
    permAut σ * rho i j hij * (permAut σ)⁻¹ ∈ SAutGen n := by
  classical
  have hσ : σ i ≠ σ j := fun h => hij (σ.injective h)
  rw [SAutGen]
  refine Finset.mem_image.mpr ⟨⟨((σ i, σ j), (true, true)), hσ⟩, Finset.mem_univ _, ?_⟩
  rw [show sAutAut (⟨((σ i, σ j), (true, true)), hσ⟩ : SAutIdx n) = rho (σ i) (σ j) hσ by
    simp [sAutAut]]
  exact (permAut_conj_rho σ i j hij hσ).symm

lemma permAut_conj_rhoNeg_mem (σ : Equiv.Perm (Fin n)) (i j : Fin n) (hij : i ≠ j) :
    permAut σ * rhoNeg i j hij * (permAut σ)⁻¹ ∈ SAutGen n := by
  classical
  have hσ : σ i ≠ σ j := fun h => hij (σ.injective h)
  rw [SAutGen]
  refine Finset.mem_image.mpr ⟨⟨((σ i, σ j), (true, false)), hσ⟩, Finset.mem_univ _, ?_⟩
  rw [show sAutAut (⟨((σ i, σ j), (true, false)), hσ⟩ : SAutIdx n) = rhoNeg (σ i) (σ j) hσ by
    simp [sAutAut]]
  exact (permAut_conj_rhoNeg σ i j hij hσ).symm

lemma permAut_conj_lam_mem (σ : Equiv.Perm (Fin n)) (i j : Fin n) (hij : i ≠ j) :
    permAut σ * lam i j hij * (permAut σ)⁻¹ ∈ SAutGen n := by
  classical
  have hσ : σ i ≠ σ j := fun h => hij (σ.injective h)
  rw [SAutGen]
  refine Finset.mem_image.mpr ⟨⟨((σ i, σ j), (false, true)), hσ⟩, Finset.mem_univ _, ?_⟩
  rw [show sAutAut (⟨((σ i, σ j), (false, true)), hσ⟩ : SAutIdx n) = lam (σ i) (σ j) hσ by
    simp [sAutAut]]
  exact (permAut_conj_lam σ i j hij hσ).symm

lemma permAut_conj_lamNeg_mem (σ : Equiv.Perm (Fin n)) (i j : Fin n) (hij : i ≠ j) :
    permAut σ * lamNeg i j hij * (permAut σ)⁻¹ ∈ SAutGen n := by
  classical
  have hσ : σ i ≠ σ j := fun h => hij (σ.injective h)
  rw [SAutGen]
  refine Finset.mem_image.mpr ⟨⟨((σ i, σ j), (false, false)), hσ⟩, Finset.mem_univ _, ?_⟩
  rw [show sAutAut (⟨((σ i, σ j), (false, false)), hσ⟩ : SAutIdx n) = lamNeg (σ i) (σ j) hσ by
    simp [sAutAut]]
  exact (permAut_conj_lamNeg σ i j hij hσ).symm

/-- **The permutation action preserves the Nielsen transvection generating set**:
conjugating any element of `SAutGen n` by the permutation automorphism of `σ`
lands again in `SAutGen n`.  (Concretely `permAut σ * ρᵢⱼ * (permAut σ)⁻¹ =
ρ_{σi,σj}` and likewise for `ρᵢⱼ⁻¹`, `λᵢⱼ`, `λᵢⱼ⁻¹`.) -/
theorem permAut_conj_mem_SAutGen (n : ℕ) (σ : Equiv.Perm (Fin n))
    {g : MulAut (FreeGroup (Fin n))} (hg : g ∈ SAutGen n) :
    permAut σ * g * (permAut σ)⁻¹ ∈ SAutGen n := by
  classical
  rw [SAutGen] at hg
  obtain ⟨p, -, hp⟩ := Finset.mem_image.mp hg
  rw [← hp]
  obtain ⟨⟨⟨i, j⟩, b, e⟩, hij⟩ := p
  cases b <;> cases e <;> simp only [sAutAut]
  · exact permAut_conj_lamNeg_mem σ i j hij
  · exact permAut_conj_lam_mem σ i j hij
  · exact permAut_conj_rhoNeg_mem σ i j hij
  · exact permAut_conj_rho_mem σ i j hij

end

end Commons.GroupTheory.FreeGroup
