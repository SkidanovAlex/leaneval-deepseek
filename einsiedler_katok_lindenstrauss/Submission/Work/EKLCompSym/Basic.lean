/-
# The `S₃`-symmetry of the EKL cross-section statements

For a permutation `τ` of the index set `Fin 3` the permutation matrix `τ.permMatrix ℝ`
conjugates the root groups, the diagonal flows and the displacement neighbourhoods of
`SL₃(ℝ)`:

* `u_ab(s) ↦ u_{τ⁻¹a τ⁻¹b}(s)`,
* `aDiag t ↦ aDiag (t ∘ τ)`, hence `aPrime c s ↦ aPrime (τ⁻¹c) s`,
* `V δ ↦ V δ` (entries are permuted, so the max-entry distance to `1` is preserved),
* `Γ₃ = SL₃(ℤ) ↦ Γ₃` (integral matrices with determinant `1`).

The last point lets us descend to `X₃ = SL₃(ℝ)/Γ₃`: `iso τ` is the induced map of `X₃`.  This
module sets up `conjPerm` and `iso` and their basic API; the transport of the cross-section
predicates along `iso τ` is proved in the sibling modules.
-/
import Mathlib
import Submission.Work.EKLComp.C8Defs
import Submission.Work.EKLContract.Lemmas.mkX_mul

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.EKLCompSym

open Work.EKLContract MeasureTheory
open scoped Matrix

/-! ## 1. The permutation matrix -/

section Mat

variable (τ : Equiv.Perm (Fin 3))

@[simp]
theorem permMatrix_apply (i j : Fin 3) : τ.permMatrix ℝ i j = if τ i = j then 1 else 0 := by
  rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]; simp

theorem permMatrix_mul_transpose : τ.permMatrix ℝ * (τ.permMatrix ℝ)ᵀ = 1 := by
  rw [Matrix.transpose_permMatrix, ← Matrix.permMatrix_mul]; simp

theorem permMatrix_transpose_mul : (τ.permMatrix ℝ)ᵀ * τ.permMatrix ℝ = 1 := by
  rw [Matrix.transpose_permMatrix, ← Matrix.permMatrix_mul]; simp

theorem permMatrix_mul_apply (M : Matrix (Fin 3) (Fin 3) ℝ) (i j : Fin 3) :
    (τ.permMatrix ℝ * M) i j = M (τ i) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (τ i)]
  · simp
  · intro b _ hb; rw [permMatrix_apply, if_neg (Ne.symm hb), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem mul_permMatrix_transpose_apply (M : Matrix (Fin 3) (Fin 3) ℝ) (i j : Fin 3) :
    (M * (τ.permMatrix ℝ)ᵀ) i j = M i (τ j) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (τ j)]
  · simp
  · intro b _ hb; rw [Matrix.transpose_apply, permMatrix_apply, if_neg (Ne.symm hb), mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem permMatrix_conj_apply (M : Matrix (Fin 3) (Fin 3) ℝ) (i j : Fin 3) :
    (τ.permMatrix ℝ * M * (τ.permMatrix ℝ)ᵀ) i j = M (τ i) (τ j) := by
  rw [mul_permMatrix_transpose_apply τ (τ.permMatrix ℝ * M) i j, permMatrix_mul_apply τ M i (τ j)]

theorem permMatrix_conj_mul (M N : Matrix (Fin 3) (Fin 3) ℝ) :
    (τ.permMatrix ℝ * (M * N) * (τ.permMatrix ℝ)ᵀ)
      = (τ.permMatrix ℝ * M * (τ.permMatrix ℝ)ᵀ) * (τ.permMatrix ℝ * N * (τ.permMatrix ℝ)ᵀ) := by
  have h : (τ.permMatrix ℝ * M * (τ.permMatrix ℝ)ᵀ) * (τ.permMatrix ℝ * N * (τ.permMatrix ℝ)ᵀ)
      = τ.permMatrix ℝ * M * ((τ.permMatrix ℝ)ᵀ * τ.permMatrix ℝ) * N * (τ.permMatrix ℝ)ᵀ := by
    noncomm_ring
  rw [h, permMatrix_transpose_mul, Matrix.mul_one]
  noncomm_ring

theorem permMatrix_transpose_conj (M : Matrix (Fin 3) (Fin 3) ℝ) :
    (τ.permMatrix ℝ)ᵀ * (τ.permMatrix ℝ * M * (τ.permMatrix ℝ)ᵀ) * (τ.permMatrix ℝ) = M := by
  have h : (τ.permMatrix ℝ)ᵀ * (τ.permMatrix ℝ * M * (τ.permMatrix ℝ)ᵀ) * (τ.permMatrix ℝ)
      = (τ.permMatrix ℝ)ᵀ * τ.permMatrix ℝ * M * ((τ.permMatrix ℝ)ᵀ * τ.permMatrix ℝ) := by
    noncomm_ring
  rw [h, permMatrix_transpose_mul, Matrix.one_mul, Matrix.mul_one]

theorem det_permMatrix_conj (M : Matrix (Fin 3) (Fin 3) ℝ) (hM : M.det = 1) :
    (τ.permMatrix ℝ * M * (τ.permMatrix ℝ)ᵀ).det = 1 := by
  rw [Matrix.det_mul, Matrix.det_mul, hM, mul_one, ← Matrix.det_mul, permMatrix_mul_transpose,
    Matrix.det_one]

theorem permMatrix_cast : (τ.permMatrix ℤ).map (Int.castRingHom ℝ) = τ.permMatrix ℝ := by
  ext i j; simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]

theorem permMatrix_mul_transpose_int : τ.permMatrix ℤ * (τ.permMatrix ℤ)ᵀ = 1 := by
  rw [Matrix.transpose_permMatrix, ← Matrix.permMatrix_mul]; simp

theorem map_permMatrix_conj (A : Matrix (Fin 3) (Fin 3) ℤ) :
    (τ.permMatrix ℤ * A * (τ.permMatrix ℤ)ᵀ).map (Int.castRingHom ℝ)
      = τ.permMatrix ℝ * A.map (Int.castRingHom ℝ) * (τ.permMatrix ℝ)ᵀ := by
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, permMatrix_cast]

end Mat

/-! ## 2. Conjugation by a permutation matrix -/

section Conj

variable (τ : Equiv.Perm (Fin 3))

/-- Conjugation of `SL₃(ℝ)` by the permutation matrix of `τ`,
`g ↦ τ.permMatrix ℝ * g * τ.permMatrix ℝᵀ`. -/
def conjPerm : SL3 →* SL3 where
  toFun g := ⟨τ.permMatrix ℝ * toMat g * (τ.permMatrix ℝ)ᵀ, det_permMatrix_conj τ (toMat g) g.2⟩
  map_one' := by
    apply ext_toMat
    show τ.permMatrix ℝ * toMat (1 : SL3) * (τ.permMatrix ℝ)ᵀ = toMat (1 : SL3)
    rw [toMat_one, Matrix.mul_one, permMatrix_mul_transpose]
  map_mul' g h := by
    apply ext_toMat
    show τ.permMatrix ℝ * toMat (g * h) * (τ.permMatrix ℝ)ᵀ
      = (τ.permMatrix ℝ * toMat g * (τ.permMatrix ℝ)ᵀ)
          * (τ.permMatrix ℝ * toMat h * (τ.permMatrix ℝ)ᵀ)
    rw [toMat_mul, permMatrix_conj_mul]

theorem toMat_conjPerm (g : SL3) :
    toMat (conjPerm τ g) = τ.permMatrix ℝ * toMat g * (τ.permMatrix ℝ)ᵀ := rfl

theorem conjPerm_apply (g : SL3) (i j : Fin 3) :
    toMat (conjPerm τ g) i j = toMat g (τ i) (τ j) := by
  rw [toMat_conjPerm, permMatrix_conj_apply]

theorem conjPerm_symm_left (g : SL3) : conjPerm τ⁻¹ (conjPerm τ g) = g := by
  apply ext_toMat
  rw [toMat_conjPerm τ⁻¹ (conjPerm τ g), toMat_conjPerm τ g]
  simpa [Matrix.transpose_permMatrix, inv_inv] using permMatrix_transpose_conj τ (toMat g)

theorem conjPerm_symm_right (g : SL3) : conjPerm τ (conjPerm τ⁻¹ g) = g := by
  have h := conjPerm_symm_left τ⁻¹ g
  rwa [inv_inv] at h

theorem conjPerm_injective : Function.Injective (conjPerm τ) := fun g h hgh => by
  have := congrArg (conjPerm τ⁻¹) hgh
  rwa [conjPerm_symm_left, conjPerm_symm_left] at this

theorem conjPerm_eq_one_iff {g : SL3} : conjPerm τ g = 1 ↔ g = 1 :=
  ⟨fun h => by
    have := congrArg (conjPerm τ⁻¹) h
    simpa [conjPerm_symm_left] using this,
   fun h => by rw [h, map_one]⟩

/-- Conjugation by a permutation matrix preserves `Γ₃ = SL₃(ℤ)`. -/
theorem conjPerm_mem_Γ3 {γ : SL3} (hγ : γ ∈ Γ3) : conjPerm τ γ ∈ Γ3 := by
  obtain ⟨A, hA⟩ := MonoidHom.mem_range.mp hγ
  have hA' : (A : Matrix (Fin 3) (Fin 3) ℤ).map (Int.castRingHom ℝ) = toMat γ := by
    rw [← hA]; exact (Matrix.SpecialLinearGroup.map_apply_coe _ A).symm
  have hdet : (τ.permMatrix ℤ * (A : Matrix (Fin 3) (Fin 3) ℤ) * (τ.permMatrix ℤ)ᵀ).det = 1 := by
    rw [Matrix.det_mul, Matrix.det_mul, A.2, mul_one, ← Matrix.det_mul,
      permMatrix_mul_transpose_int, Matrix.det_one]
  refine MonoidHom.mem_range.mpr ⟨⟨_, hdet⟩, ?_⟩
  apply Subtype.ext
  show (τ.permMatrix ℤ * (A : Matrix (Fin 3) (Fin 3) ℤ) * (τ.permMatrix ℤ)ᵀ).map
      (Int.castRingHom ℝ) = toMat (conjPerm τ γ)
  rw [toMat_conjPerm, ← hA', map_permMatrix_conj]

theorem conjPerm_respects {a b : SL3} (hab : QuotientGroup.leftRel Γ3 a b) :
    QuotientGroup.leftRel Γ3 (conjPerm τ a) (conjPerm τ b) := by
  rw [QuotientGroup.leftRel_apply] at hab ⊢
  have : (conjPerm τ a)⁻¹ * conjPerm τ b = conjPerm τ (a⁻¹ * b) := by
    rw [← map_inv, ← map_mul]
  rw [this]
  exact conjPerm_mem_Γ3 τ hab

theorem continuous_conjPerm : Continuous fun g : SL3 => conjPerm τ g :=
  (continuous_const.mul continuous_subtype_val).mul continuous_const |>.subtype_mk _

end Conj

/-! ## 3. The induced map of `X₃` -/

section Iso

variable (τ : Equiv.Perm (Fin 3))

/-- The homeomorphism of `X₃ = SL₃(ℝ)/Γ₃` induced by conjugation by the permutation matrix
of `τ`. -/
def iso : X3 → X3 :=
  Quotient.map' (fun g => conjPerm τ g) (fun a b h => conjPerm_respects τ h)

theorem iso_mkX (g : SL3) : iso τ (mkX g) = mkX (conjPerm τ g) :=
  Quotient.map'_mk'' _ _ g

theorem continuous_iso : Continuous (iso τ) :=
  Continuous.quotient_map' (continuous_conjPerm τ) _

theorem measurable_iso : Measurable (iso τ) := (continuous_iso τ).measurable

theorem iso_smul (u : SL3) (x : X3) : iso τ (u • x) = conjPerm τ u • iso τ x := by
  induction x using QuotientGroup.induction_on with
  | _ g =>
    show iso τ (u • mkX g) = conjPerm τ u • iso τ (mkX g)
    rw [← Work.EKLContract.Lemmas.mkX_mul u g, iso_mkX, iso_mkX, map_mul,
      Work.EKLContract.Lemmas.mkX_mul]

theorem iso_symm_left (x : X3) : iso τ⁻¹ (iso τ x) = x := by
  induction x using QuotientGroup.induction_on with
  | _ g =>
    show iso τ⁻¹ (iso τ (mkX g)) = mkX g
    rw [iso_mkX, iso_mkX, conjPerm_symm_left]

theorem iso_symm_right (x : X3) : iso τ (iso τ⁻¹ x) = x := by
  have h := iso_symm_left τ⁻¹ x
  rwa [inv_inv] at h

theorem iso_injective : Function.Injective (iso τ) := fun x y hxy => by
  have := congrArg (iso τ⁻¹) hxy
  rwa [iso_symm_left, iso_symm_left] at this

end Iso

/-! ## 4. The action of `conjPerm` on the objects of the contract -/

section Actions

variable (τ : Equiv.Perm (Fin 3))

/-- `uij` does not depend on the proof of `i ≠ j`. -/
theorem uij_proof_irrel {a b : Fin 3} (h h' : a ≠ b) (s : ℝ) : uij h s = uij h' s :=
  Subtype.ext rfl

theorem permMatrix_conj_single {a b : Fin 3} (s : ℝ) :
    τ.permMatrix ℝ * Matrix.single a b s * (τ.permMatrix ℝ)ᵀ
      = Matrix.single (τ⁻¹ a) (τ⁻¹ b) s := by
  ext i j
  rw [permMatrix_conj_apply, Matrix.single_apply, Matrix.single_apply]
  simp only [Equiv.Perm.inv_def]
  have hiff : (a = τ i ∧ b = τ j) ↔ (Equiv.symm τ a = i ∧ Equiv.symm τ b = j) := by
    constructor
    · rintro ⟨e1, e2⟩
      exact ⟨by rw [e1, Equiv.symm_apply_apply], by rw [e2, Equiv.symm_apply_apply]⟩
    · rintro ⟨f1, f2⟩
      exact ⟨by rw [← f1, Equiv.apply_symm_apply], by rw [← f2, Equiv.apply_symm_apply]⟩
  by_cases h : a = τ i ∧ b = τ j
  · rw [if_pos h, if_pos (hiff.mp h)]
  · rw [if_neg h, if_neg (fun hh => h (hiff.mpr hh))]

theorem conjPerm_apply_uij {a b : Fin 3} (hab : a ≠ b) (hτ : τ⁻¹ a ≠ τ⁻¹ b) (s : ℝ) :
    conjPerm τ (uij hab s) = uij hτ s := by
  apply ext_toMat
  rw [toMat_conjPerm, Work.EKLContract.Lemmas.toMat_uij, Work.EKLContract.Lemmas.toMat_uij,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, permMatrix_mul_transpose,
    permMatrix_conj_single]

theorem Uij_proof_irrel {a b : Fin 3} (h h' : a ≠ b) : Uij h = Uij h' := by
  have hfun : (fun s : ℝ => uij h s) = (fun s : ℝ => uij h' s) := by
    funext s; exact uij_proof_irrel h h' s
  unfold Uij
  rw [hfun]

/-- The root group only depends on the two indices, not on the proof of their distinctness. -/
theorem Uij_congr {a b a' b' : Fin 3} (ha : a = a') (hb : b = b') (hab : a ≠ b)
    (hab' : a' ≠ b') : Uij hab = Uij hab' := by
  subst ha; subst hb
  exact Uij_proof_irrel hab hab'

/-- The subgroup `Upar` only depends on the three indices, not on the proofs of distinctness. -/
theorem Upar_congr {a b c a' b' c' : Fin 3} (ha : a = a') (hb : b = b') (hc : c = c')
    (h1 : a ≠ b) (h2 : a ≠ c) (h3 : c ≠ b) (h1' : a' ≠ b') (h2' : a' ≠ c') (h3' : c' ≠ b') :
    Upar h1 h2 h3 = Upar h1' h2' h3' := by
  subst ha; subst hb; subst hc
  unfold Upar
  rw [Uij_proof_irrel h1 h1', Uij_proof_irrel h2 h2', Uij_proof_irrel h3 h3']

/-- `NonExceptional` only depends on the indices, not on the proof of distinctness. -/
theorem NonExceptional_congr {μ : Measure X3} {a b c a' b' c' : Fin 3}
    (ha : a = a') (hb : b = b') (hc : c = c') (hab : a ≠ b) (hab' : a' ≠ b') :
    (NonExceptional μ hab c ↔ NonExceptional μ hab' c') := by
  subst ha; subst hb; subst hc
  exact Iff.rfl

theorem Uij_map {a b : Fin 3} (hab : a ≠ b) (hτ : τ⁻¹ a ≠ τ⁻¹ b) :
    (Uij hab).map (conjPerm τ) = Uij hτ := by
  rw [Uij, Uij, MonoidHom.map_closure]
  congr 1
  ext g
  constructor
  · rintro ⟨x, ⟨s, rfl⟩, hxg⟩
    refine ⟨s, ?_⟩
    show uij hτ s = g
    rw [← conjPerm_apply_uij τ hab hτ s, hxg]
  · rintro ⟨s, rfl⟩
    exact ⟨uij hab s, ⟨s, rfl⟩, conjPerm_apply_uij τ hab hτ s⟩

theorem Upar_map {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c) (hcb : c ≠ b)
    (hab' : τ⁻¹ a ≠ τ⁻¹ b) (hac' : τ⁻¹ a ≠ τ⁻¹ c) (hcb' : τ⁻¹ c ≠ τ⁻¹ b) :
    (Upar hab hac hcb).map (conjPerm τ) = Upar hab' hac' hcb' := by
  rw [Upar, Upar, Subgroup.map_sup, Subgroup.map_sup, Uij_map τ hab hab', Uij_map τ hac hac',
    Uij_map τ hcb hcb']

theorem conjPerm_apply_aDiag (t : Fin 3 → ℝ) :
    conjPerm τ (aDiag t) = aDiag (t ∘ ⇑τ) := by
  apply ext_toMat
  rw [toMat_conjPerm, toMat_aDiag, toMat_aDiag]
  ext i j
  rw [permMatrix_conj_apply, Matrix.diagonal, Matrix.diagonal, Matrix.of_apply, Matrix.of_apply]
  by_cases h : i = j
  · subst h
    simp only [Function.comp_apply, if_pos rfl, Equiv.sum_comp]
  · have h' : τ i ≠ τ j := fun hh => h (τ.injective hh)
    simp [h, h']

theorem conjPerm_apply_aPrime (c : Fin 3) (s : ℝ) :
    conjPerm τ (aPrime c s) = aPrime (τ⁻¹ c) s := by
  rw [aPrime, aPrime, conjPerm_apply_aDiag]
  congr 1
  funext i
  rw [Function.comp_apply]
  simp only [Equiv.Perm.inv_def]
  by_cases h : τ i = c
  · rw [if_pos h, if_pos ((Equiv.eq_symm_apply τ).mpr h)]
  · rw [if_neg h, if_neg (fun hh => h ((Equiv.eq_symm_apply τ).mp hh))]

theorem Lset_proof_irrel {a b : Fin 3} (h h' : a ≠ b) : Lset h = Lset h' := by
  ext g
  change (g * uij h 1 = uij h 1 * g) ↔ (g * uij h' 1 = uij h' 1 * g)
  rw [uij_proof_irrel h h' 1]

theorem conjPerm_mem_Lset_iff {a b : Fin 3} (hab : a ≠ b) (hτ : τ⁻¹ a ≠ τ⁻¹ b) (g : SL3) :
    conjPerm τ g ∈ Lset hτ ↔ g ∈ Lset hab := by
  have hu : conjPerm τ (uij hab 1) = uij hτ 1 := conjPerm_apply_uij τ hab hτ 1
  rw [Lset, Lset, Set.mem_ofPred_eq, Set.mem_ofPred_eq, ← hu, ← map_mul, ← map_mul]
  exact ⟨fun h => conjPerm_injective τ h, fun h => by rw [h]⟩

theorem one_apply_perm (i j : Fin 3) : toMat (1 : SL3) (τ i) (τ j) = toMat (1 : SL3) i j := by
  simp [Matrix.one_apply, τ.injective.eq_iff]

theorem conjPerm_mem_V_iff (g : SL3) (δ : ℝ) : conjPerm τ g ∈ V δ ↔ g ∈ V δ := by
  rw [show (conjPerm τ g ∈ V δ) ↔
        ∀ i j, |toMat (conjPerm τ g) i j - toMat (1 : SL3) i j| < δ from Iff.rfl,
      show (g ∈ V δ) ↔ ∀ i j, |toMat g i j - toMat (1 : SL3) i j| < δ from Iff.rfl]
  constructor
  · intro h i j
    have h1 := h (τ.symm i) (τ.symm j)
    rw [conjPerm_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h1
    rwa [one_apply_perm τ.symm i j] at h1
  · intro h i j
    have h1 := h (τ i) (τ j)
    rw [conjPerm_apply, ← one_apply_perm τ i j]
    exact h1

theorem iso_smul_aDiag (t : Fin 3 → ℝ) (x : X3) :
    iso τ (aDiag t • x) = aDiag (t ∘ ⇑τ) • iso τ x := by
  rw [iso_smul, conjPerm_apply_aDiag]

end Actions

end Work.EKLCompSym

end
