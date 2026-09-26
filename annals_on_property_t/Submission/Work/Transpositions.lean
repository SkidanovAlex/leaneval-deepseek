import Submission.Work.NielsenCore

open Submission.FreeGroupAut
open FreeGroup
set_option autoImplicit false

/-!
# Basis transpositions as words in the Nielsen generators

Any proof of Nielsen's theorem (that `AutGen n` generates `Aut(F_n)`) needs to
express the permutation automorphisms of the basis in terms of the elementary
generators.  For distinct indices `i ≠ j` the *transposition* automorphism
`τᵢⱼ` (swapping the basis generators `a i` and `a j`) admits the short
decomposition

    τᵢⱼ  =  σᵢ · λᵢⱼ · λⱼᵢ⁻¹ · ρᵢⱼ

where `σᵢ` inverts `aᵢ`, `λᵢⱼ : aᵢ ↦ aⱼ·aᵢ`, and `ρᵢⱼ : aᵢ ↦ aᵢ·aⱼ`
(`·` is composition, the right-most factor is applied first).  Since every one
of `σᵢ`, `λᵢⱼ`, `λⱼᵢ⁻¹`, `ρᵢⱼ` lies in `AutGen n`, we obtain the closure
membership `τᵢⱼ ∈ closure(AutGen n)`.

*Why the decomposition works* (evaluation on the basis):
 - on `aᵢ`: `ρᵢⱼ` sends `aᵢ ↦ aᵢ·aⱼ`; then `λⱼᵢ⁻¹` (which sends
   `aⱼ ↦ aᵢ⁻¹·aⱼ` and fixes `aᵢ`) collapses the product to `aⱼ`; the
   subsequent `λᵢⱼ` and `σᵢ` fix `aⱼ`;
 - on `aⱼ`: `ρᵢⱼ` fixes it; `λⱼᵢ⁻¹` sends it to `aᵢ⁻¹·aⱼ`; `λᵢⱼ` (which sends
   `aᵢ ↦ aⱼ·aᵢ`) maps this to `aᵢ⁻¹`; `σᵢ` (which inverts `aᵢ`) yields `aᵢ`;
 - other basis generators are fixed throughout.
-/

namespace Submission.Nielsen

noncomputable section

open scoped BigOperators

variable {n : ℕ}

private lemma squeeze_inv_left {G : Type*} [Group G] (x y : G) : x * (x⁻¹ * y) = y := by
  rw [← mul_assoc, mul_inv_cancel, one_mul]

private lemma cancel_inv_left {G : Type*} [Group G] (x : G) : x⁻¹ * x = 1 := by
  exact inv_mul_cancel x

/-- The lift underlying the transposition of `a i` and `a j` (`i ≠ j`). -/
def tauHom (i j : Fin n) : FreeGroup (Fin n) →* FreeGroup (Fin n) :=
  FreeGroup.lift (fun k : Fin n => if k = i then FreeGroup.of j
    else if k = j then FreeGroup.of i else FreeGroup.of k)

/-- `tauHom` is an involution. -/
lemma tauHom_comp_self (i j : Fin n) (hij : i ≠ j) :
    (tauHom i j).comp (tauHom i j) = MonoidHom.id (FreeGroup (Fin n)) := by
  apply FreeGroup.ext_hom
  intro k
  by_cases hki : k = i
  · subst k
    have hji : j ≠ i := fun h => hij h.symm
    simp [tauHom, hji]
  · by_cases hkj : k = j
    · subst k
      have hji : j ≠ i := fun h => hij h.symm
      simp [tauHom, hij, hji]
    · simp [tauHom, hki, hkj]

/-- The transposition of the two basis generators `a i`, `a j` (`i ≠ j`). -/
def tau (i j : Fin n) (hij : i ≠ j) : MulAut (FreeGroup (Fin n)) where
  toFun := tauHom i j
  invFun := tauHom i j
  left_inv x := by
    have h := congrArg (fun φ : FreeGroup (Fin n) →* FreeGroup (Fin n) => φ x)
      (tauHom_comp_self i j hij)
    simpa using h
  right_inv x := by
    have h := congrArg (fun φ : FreeGroup (Fin n) →* FreeGroup (Fin n) => φ x)
      (tauHom_comp_self i j hij)
    simpa using h
  map_mul' x y := (tauHom i j).map_mul x y

/-- `tau` sends `a i` to `a j`. -/
lemma tau_apply_i (i j : Fin n) (hij : i ≠ j) :
    (tau i j hij) (FreeGroup.of i) = FreeGroup.of j := by
  have hji : j ≠ i := fun h => hij h.symm
  simp [tau, tauHom, hji]

/-- `tau` sends `a j` to `a i`. -/
lemma tau_apply_j (i j : Fin n) (hij : i ≠ j) :
    (tau i j hij) (FreeGroup.of j) = FreeGroup.of i := by
  have hji : j ≠ i := fun h => hij h.symm
  simp [tau, tauHom, hij, hji]

/-- `tau` fixes every other basis generator. -/
lemma tau_apply_other {i j k : Fin n} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) :
    (tau i j hij) (FreeGroup.of k) = FreeGroup.of k := by
  simp [tau, tauHom, hki, hkj]

/-- The word in the Nielsen generators which realises the transposition:
`σᵢ · λᵢⱼ · λⱼᵢ⁻¹ · ρᵢⱼ`. -/
def tauWord (i j : Fin n) (hij : i ≠ j) : MulAut (FreeGroup (Fin n)) :=
  sigma i * lam i j hij * lamNeg j i (fun h : j = i => hij h.symm) * rho i j hij

/-- On `a i` the word collapses to `a j`. -/
lemma tauWord_apply_i (i j : Fin n) (hij : i ≠ j) :
    (tauWord i j hij) (FreeGroup.of i) = FreeGroup.of j := by
  unfold tauWord
  have hji : j ≠ i := fun h => hij h.symm
  change (sigma i : FreeGroup (Fin n) →* FreeGroup (Fin n))
      ((lam i j hij : FreeGroup (Fin n) →* FreeGroup (Fin n))
        ((lamNeg j i hji : FreeGroup (Fin n) →* FreeGroup (Fin n))
          ((rho i j hij : FreeGroup (Fin n) →* FreeGroup (Fin n)) (FreeGroup.of i))))
      = FreeGroup.of j
  have hRhoF : (rho i j hij : FreeGroup (Fin n) →* FreeGroup (Fin n)) (FreeGroup.of i)
      = FreeGroup.of i * FreeGroup.of j := by
    simpa using rho_apply_self i j hij
  have hLamNFix : (lamNeg j i hji : FreeGroup (Fin n) →* FreeGroup (Fin n)) (FreeGroup.of i)
      = FreeGroup.of i := by
    simpa using (lamNeg_apply_other (hij := hji) (hk := hij))
  have hLamNCh : (lamNeg j i hji : FreeGroup (Fin n) →* FreeGroup (Fin n)) (FreeGroup.of j)
      = (FreeGroup.of i)⁻¹ * FreeGroup.of j := by
    simpa using (lamNeg_apply_self j i hji)
  have hLamN : (lamNeg j i hji : FreeGroup (Fin n) →* FreeGroup (Fin n)) (FreeGroup.of i * FreeGroup.of j)
      = FreeGroup.of j := by
    rw [(lamNeg j i hji : FreeGroup (Fin n) →* FreeGroup (Fin n)).map_mul]
    rw [hLamNFix, hLamNCh]
    exact squeeze_inv_left (FreeGroup.of i) (FreeGroup.of j)
  have hLamFix : (lam i j hij : FreeGroup (Fin n) →* FreeGroup (Fin n)) (FreeGroup.of j)
      = FreeGroup.of j := by
    simpa using (lam_apply_other (hij := hij) (hk := hji))
  have hSigFix : (sigma i : FreeGroup (Fin n) →* FreeGroup (Fin n)) (FreeGroup.of j)
      = FreeGroup.of j := by
    simpa using (sigma_apply_other hji)
  rw [hRhoF, hLamN, hLamFix, hSigFix]

/-- On `a j` the word yields `a i`. -/
lemma tauWord_apply_j (i j : Fin n) (hij : i ≠ j) :
    (tauWord i j hij) (FreeGroup.of j) = FreeGroup.of i := by
  unfold tauWord
  have hji : j ≠ i := fun h => hij h.symm
  change (sigma i : FreeGroup (Fin n) →* FreeGroup (Fin n))
      ((lam i j hij : FreeGroup (Fin n) →* FreeGroup (Fin n))
        ((lamNeg j i hji : FreeGroup (Fin n) →* FreeGroup (Fin n))
          ((rho i j hij : FreeGroup (Fin n) →* FreeGroup (Fin n)) (FreeGroup.of j))))
      = FreeGroup.of i
  have hRhoF : (rho i j hij : FreeGroup (Fin n) →* FreeGroup (Fin n)) (FreeGroup.of j)
      = FreeGroup.of j := by
    simpa using (rho_apply_other (hij := hij) (hk := hji))
  have hLamN : (lamNeg j i hji : FreeGroup (Fin n) →* FreeGroup (Fin n)) (FreeGroup.of j)
      = (FreeGroup.of i)⁻¹ * FreeGroup.of j := by
    simpa using (lamNeg_apply_self j i hji)
  have hLamSelf : (lam i j hij : FreeGroup (Fin n) →* FreeGroup (Fin n)) (FreeGroup.of i)
      = FreeGroup.of j * FreeGroup.of i := by
    simpa using (lam_apply_self i j hij)
  have hLamFix : (lam i j hij : FreeGroup (Fin n) →* FreeGroup (Fin n)) (FreeGroup.of j)
      = FreeGroup.of j := by
    simpa using (lam_apply_other (hij := hij) (hk := hji))
  have hLam : (lam i j hij : FreeGroup (Fin n) →* FreeGroup (Fin n)) ((FreeGroup.of i)⁻¹ * FreeGroup.of j)
      = (FreeGroup.of i)⁻¹ := by
    rw [(lam i j hij : FreeGroup (Fin n) →* FreeGroup (Fin n)).map_mul]
    rw [(lam i j hij : FreeGroup (Fin n) →* FreeGroup (Fin n)).map_inv]
    rw [hLamSelf, hLamFix]
    rw [mul_inv_rev]
    rw [mul_assoc, inv_mul_cancel, mul_one]
  have hSig : (sigma i : FreeGroup (Fin n) →* FreeGroup (Fin n)) ((FreeGroup.of i)⁻¹)
      = FreeGroup.of i := by
    rw [(sigma i : FreeGroup (Fin n) →* FreeGroup (Fin n)).map_inv]
    have hv : (sigma i : FreeGroup (Fin n) →* FreeGroup (Fin n)) (FreeGroup.of i)
        = (FreeGroup.of i)⁻¹ := by
      simpa using sigma_apply_self i
    rw [hv]
    simp
  rw [hRhoF, hLamN, hLam, hSig]

/-- The word fixes every other basis generator. -/
lemma tauWord_apply_other {i j k : Fin n} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) :
    (tauWord i j hij) (FreeGroup.of k) = FreeGroup.of k := by
  unfold tauWord
  have hji : j ≠ i := fun h => hij h.symm
  change (sigma i : FreeGroup (Fin n) →* FreeGroup (Fin n))
      ((lam i j hij : FreeGroup (Fin n) →* FreeGroup (Fin n))
        ((lamNeg j i hji : FreeGroup (Fin n) →* FreeGroup (Fin n))
          ((rho i j hij : FreeGroup (Fin n) →* FreeGroup (Fin n)) (FreeGroup.of k))))
      = FreeGroup.of k
  have hRhoF : (rho i j hij : FreeGroup (Fin n) →* FreeGroup (Fin n)) (FreeGroup.of k)
      = FreeGroup.of k := by
    simpa using (rho_apply_other (hij := hij) (hk := hki))
  have hLamNF : (lamNeg j i hji : FreeGroup (Fin n) →* FreeGroup (Fin n)) (FreeGroup.of k)
      = FreeGroup.of k := by
    simpa using (lamNeg_apply_other (hij := hji) (hk := fun h : k = j => hkj h))
  have hLamF : (lam i j hij : FreeGroup (Fin n) →* FreeGroup (Fin n)) (FreeGroup.of k)
      = FreeGroup.of k := by
    simpa using (lam_apply_other (hij := hij) (hk := hki))
  have hSigF : (sigma i : FreeGroup (Fin n) →* FreeGroup (Fin n)) (FreeGroup.of k)
      = FreeGroup.of k := by
    simpa using (sigma_apply_other hki)
  rw [hRhoF, hLamNF, hLamF, hSigF]

/-- The decomposition of the transposition as a word in the Nielsen generators
and the inversion `σᵢ`:

    τᵢⱼ = σᵢ · λᵢⱼ · λⱼᵢ⁻¹ · ρᵢⱼ

(composition order: the right-most factor is applied first). -/
lemma tau_decomposition (i j : Fin n) (hij : i ≠ j) :
    tau i j hij = tauWord i j hij := by
  have hji : j ≠ i := fun h => hij h.symm
  have hgen : ∀ k : Fin n,
      (tau i j hij) (FreeGroup.of k) = (tauWord i j hij) (FreeGroup.of k) := by
    intro k
    by_cases hki : k = i
    · subst k
      rw [tau_apply_i i j hij, tauWord_apply_i i j hij]
    · by_cases hkj : k = j
      · subst k
        rw [tau_apply_j i j hij, tauWord_apply_j i j hij]
      · rw [tau_apply_other (hij := hij) (hki := hki) (hkj := hkj),
          tauWord_apply_other (hij := hij) (hki := hki) (hkj := hkj)]
  have hhom : (tau i j hij : FreeGroup (Fin n) →* FreeGroup (Fin n)) =
      (tauWord i j hij : FreeGroup (Fin n) →* FreeGroup (Fin n)) := by
    apply FreeGroup.ext_hom
    intro k
    exact hgen k
  ext x
  exact congrArg (fun φ : FreeGroup (Fin n) →* FreeGroup (Fin n) => φ x) hhom

/-- Every `sigma i` (single-generator inversion) belongs to `AutGen n`. -/
lemma sigma_mem_AutGen (n : ℕ) (i : Fin n) :
    sigma i ∈ (AutGen n : Set (MulAut (FreeGroup (Fin n)))) := by
  classical
  rw [AutGen]
  rw [Finset.mem_coe]
  rw [Finset.mem_union]
  right
  rw [SigmaSet]
  rw [Finset.mem_image]
  exact ⟨i, Finset.mem_univ i, rfl⟩

/-- Every right/left Nielsen transvection (any exponent) belongs to `AutGen n`. -/
lemma rho_mem_AutGen (n : ℕ) {i j : Fin n} (hij : i ≠ j) :
    rho i j hij ∈ (AutGen n : Set (MulAut (FreeGroup (Fin n)))) := by
  classical
  rw [AutGen]
  rw [Finset.mem_coe]
  rw [Finset.mem_union]
  left
  rw [SAutGen]
  rw [Finset.mem_image]
  refine ⟨⟨((i, j), (true, true)), hij⟩, Finset.mem_univ _, ?_⟩
  rfl

/-- `lam i j` belongs to `AutGen n`. -/
lemma lam_mem_AutGen (n : ℕ) {i j : Fin n} (hij : i ≠ j) :
    lam i j hij ∈ (AutGen n : Set (MulAut (FreeGroup (Fin n)))) := by
  classical
  rw [AutGen]
  rw [Finset.mem_coe]
  rw [Finset.mem_union]
  left
  rw [SAutGen]
  rw [Finset.mem_image]
  refine ⟨⟨((i, j), (false, true)), hij⟩, Finset.mem_univ _, ?_⟩
  rfl

/-- `lamNeg j i` belongs to `AutGen n` (it is a Nielsen generator itself). -/
lemma lamNeg_mem_AutGen (n : ℕ) {i j : Fin n} (hij : i ≠ j) :
    lamNeg j i (fun h : j = i => hij h.symm) ∈
      (AutGen n : Set (MulAut (FreeGroup (Fin n)))) := by
  classical
  rw [AutGen]
  rw [Finset.mem_coe]
  rw [Finset.mem_union]
  left
  rw [SAutGen]
  rw [Finset.mem_image]
  refine ⟨⟨((j, i), (false, false)), (fun h : j = i => hij h.symm)⟩, Finset.mem_univ _, ?_⟩
  rfl

/-- Every basis transposition belongs to the subgroup generated by `AutGen n`. -/
theorem tau_mem_closure (n : ℕ) {i j : Fin n} (hij : i ≠ j) :
    tau i j hij ∈ Subgroup.closure (AutGen n : Set (MulAut (FreeGroup (Fin n)))) := by
  let C := Subgroup.closure (AutGen n : Set (MulAut (FreeGroup (Fin n))))
  have hs : sigma i ∈ C := Subgroup.subset_closure (sigma_mem_AutGen n i)
  have hLam : lam i j hij ∈ C := Subgroup.subset_closure (lam_mem_AutGen n hij)
  have hLamN : lamNeg j i (fun h : j = i => hij h.symm) ∈ C :=
    Subgroup.subset_closure (lamNeg_mem_AutGen n hij)
  have hRho : rho i j hij ∈ C := Subgroup.subset_closure (rho_mem_AutGen n hij)
  rw [tau_decomposition i j hij]
  unfold tauWord
  rw [mul_assoc, mul_assoc]
  exact C.mul_mem hs (C.mul_mem hLam (C.mul_mem hLamN hRho))

end

end Submission.Nielsen
