/-
Area DSCOH (curric-46) — `d² = 0` for the chart Čech differential.

The `q`-th term of the chart Čech complex is the product, over the `(q+1)`-element subsets `S`
of the index set, of the degree-zero part `degZero ℳ S` of the localization of a graded module
at the monomial `X_S = ∏_{i∈S} Xᵢ`.  The differential `cechDiff ℳ q` sends a `q`-cochain to the
`(q+1)`-cochain whose `T`-component is the alternating sum, over `i ∈ T`, of the restriction
`T \ {i} → T` applied to the `(T \ {i})`-component, with sign `(-1)^{#{j ∈ T : j < i}}`.

The main theorem `Work.DSCOH.cechDiff_comp` proves that two consecutive differentials compose to
zero, so that the chart Čech complex is a cochain complex.

The proof is the classical simplicial computation: composing the two sums produces a double sum
over ordered pairs `(i,j)` of *distinct* elements of `T`; the map `(i,j) ↦ (j,i)` pairs the terms,
the two composites of restriction maps are equal by `resAt_comp` (functoriality of the chart
localizations), and the two signs are opposite because the position of `i` in `T` and the position
of `j` in `T \ {i}` differ from the swapped pair of positions by exactly one.
-/
import Mathlib
import Submission.Work.DSCOH.Cech
import Submission.Work.DSCOH.resAt_comp
import Submission.Work.DSCOH.sum_attach_erase_eq_sum_product
import Submission.Work.DSCOH.sum_product_swap_eq_zero
import Submission.Work.DSCOH.negOne_pow_card_filter_erase

open MvPolynomial

namespace Work.DSCOH

variable {A : Type*} [CommRing A] {n : ℕ}
variable {M : Type*} [AddCommGroup M] [Module A M] [Module (Poly A n) M] [IsScalarTower A (Poly A n) M]

/-- The value of `degPartRestrict` at an element: it is `ψ` applied to the underlying element.
(In particular `degPartRestrict` only depends on `ψ`, not on the compatibility proof, which is
also why proofs of the same proposition may be used interchangeably below.) -/
private lemma degPartRestrict_val {ℳ : ℕ → Submodule A M} {S T : Finset (Fin n)}
    (ψ : locAt (A := A) (M := M) S →ₗ[Poly A n] locAt (A := A) (M := M) T)
    (h : ∀ x ∈ degZero (A := A) ℳ S, ψ x ∈ degZero (A := A) ℳ T) (x : degZero (A := A) ℳ S) :
    ((degPartRestrict (A := A) (M := M) ℳ ψ h x : locAt (A := A) (M := M) T)) = ψ x.1 := rfl

/-- Composition of restrictions of maps to degree-zero parts: `degPartRestrict` respects
composition of the underlying maps. -/
private lemma degPartRestrict_comp {ℳ : ℕ → Submodule A M} {S T U : Finset (Fin n)}
    (ψ : locAt (A := A) (M := M) S →ₗ[Poly A n] locAt (A := A) (M := M) T)
    (hψ : ∀ x ∈ degZero (A := A) ℳ S, ψ x ∈ degZero (A := A) ℳ T)
    (χ : locAt (A := A) (M := M) T →ₗ[Poly A n] locAt (A := A) (M := M) U)
    (hχ : ∀ x ∈ degZero (A := A) ℳ T, χ x ∈ degZero (A := A) ℳ U) :
    (degPartRestrict (A := A) (M := M) ℳ χ hχ).comp (degPartRestrict (A := A) (M := M) ℳ ψ hψ) =
      degPartRestrict (A := A) (M := M) ℳ (χ.comp ψ) (fun x hx => hχ (ψ x) (hψ x hx)) := by
  ext x
  rw [LinearMap.comp_apply, degPartRestrict_val, degPartRestrict_val, degPartRestrict_val]
  rfl

/-- The restriction map `degZero ℳ S → degZero ℳ T` induced by the structure map
`resAt : locAt S → locAt T` of the chart localizations, together with the (graded) verification
that `resAt` preserves the degree-zero parts.  This is the form in which the Čech differentials
are manipulated below. -/
private noncomputable def resZero (ℳ : ℕ → Submodule A M) [SetLike.GradedSMul (homSub A n) ℳ]
    {S T : Finset (Fin n)} (h : S ⊆ T) :
    degZero (A := A) ℳ S →ₗ[A] degZero (A := A) ℳ T :=
  degPartRestrict (A := A) (M := M) ℳ (resAt (A := A) (M := M) h)
    (fun x hx => resAt_degZero (A := A) (n := n) (M := M) (ℳ := ℳ) h x hx)

/-- The defining property of `resZero`: it is `resAt` on the underlying elements (this is
`degPartRestrict_val`). -/
private lemma resZero_apply {ℳ : ℕ → Submodule A M} [SetLike.GradedSMul (homSub A n) ℳ]
    {S T : Finset (Fin n)} (h : S ⊆ T) (x : degZero (A := A) ℳ S) :
    ((resZero (A := A) (M := M) ℳ h x : locAt (A := A) (M := M) T)) = resAt h x.1 := rfl

/-- The restriction maps on degree-zero parts are functorial: `resAt_comp` transported through
`degPartRestrict`. -/
private lemma resZero_comp {ℳ : ℕ → Submodule A M} [SetLike.GradedSMul (homSub A n) ℳ]
    {S T U : Finset (Fin n)} (h₁ : S ⊆ T) (h₂ : T ⊆ U) :
    resZero (A := A) (M := M) ℳ (h₁.trans h₂) =
      (resZero (A := A) (M := M) ℳ h₂).comp (resZero (A := A) (M := M) ℳ h₁) := by
  ext x
  rw [LinearMap.comp_apply, resZero_apply, resZero_apply, resZero_apply, resAt_comp h₁ h₂,
    LinearMap.comp_apply]

/-- Functoriality of `resZero` in the form used to collapse the two composites occurring in
`d²`: `resZero h₂ (resZero h₁ y) = resZero (h₁.trans h₂) y`. -/
private lemma resZero_comp_apply {ℳ : ℕ → Submodule A M} [SetLike.GradedSMul (homSub A n) ℳ]
    {S T U : Finset (Fin n)} (h₁ : S ⊆ T) (h₂ : T ⊆ U) (y : degZero (A := A) ℳ S) :
    resZero (A := A) (M := M) ℳ h₂ (resZero (A := A) (M := M) ℳ h₁ y) =
      resZero (A := A) (M := M) ℳ (h₁.trans h₂) y := by
  have h : resZero (A := A) (M := M) ℳ h₂ (resZero (A := A) (M := M) ℳ h₁ y) =
      ((resZero (A := A) (M := M) ℳ h₂).comp (resZero (A := A) (M := M) ℳ h₁)) y := rfl
  rw [h, ← resZero_comp (h₁ := h₁) (h₂ := h₂)]

/-- `resZero` is insensitive to replacing the source finset by an equal one (the two erased
finsets of an ordered pair of distinct elements agree by `Finset.erase_right_comm`). -/
private lemma resZero_eq_of_eq {ℳ : ℕ → Submodule A M} [SetLike.GradedSMul (homSub A n) ℳ]
    {S S' T : Finset (Fin n)} (hS : S = S') (h : S ⊆ T) (h' : S' ⊆ T)
    {y : degZero (A := A) ℳ S} {y' : degZero (A := A) ℳ S'} (hy : HEq y y') :
    resZero (A := A) (M := M) ℳ h y = resZero (A := A) (M := M) ℳ h' y' := by
  subst hS
  rw [eq_of_heq hy]

/-- Heterogeneous equality of the values of a dependent function at equal arguments. -/
private lemma heq_apply_of_eq {α : Type*} {β : α → Type*} {a b : α} (h : a = b)
    (f : (i : α) → β i) : HEq (f a) (f b) := by
  subst h
  rfl

/-- The `T`-component of the Čech differential, written with the restriction maps `resZero` of
the degree-zero parts (this is just the definition of `cechDiffComp`, using
`degPartRestrict_val` to replace `degPartRestrict` by `resZero`). -/
private lemma cechDiffComp_eq_resZero {ℳ : ℕ → Submodule A M} [SetLike.GradedSMul (homSub A n) ℳ]
    (q : ℕ) (T : {S : Finset (Fin n) // S.card = q + 1 + 1}) :
    cechDiffComp (A := A) (n := n) (M := M) ℳ q T =
      ∑ i ∈ T.1.attach, (-1 : ℤ) ^ ((T.1.filter (fun j => j < i.1)).card) •
        ((resZero (A := A) (M := M) ℳ (Finset.erase_subset i.1 T.1)).comp
          (LinearMap.proj (R := A)
            (φ := fun S : {S : Finset (Fin n) // S.card = q + 1} => degZero (A := A) ℳ S.1)
            ⟨T.1.erase i.1, by rw [Finset.card_erase_of_mem i.2]; omega⟩)) := by
  rw [cechDiffComp]
  rfl

/-- **The chart Čech differential squares to zero.** -/
theorem cechDiff_comp {A : Type*} [CommRing A] {n : ℕ}
    {M : Type*} [AddCommGroup M] [Module A M] [Module (Poly A n) M] [IsScalarTower A (Poly A n) M]
    (ℳ : ℕ → Submodule A M) [SetLike.GradedSMul (homSub A n) ℳ] (q : ℕ) :
    (cechDiff (A := A) (n := n) (M := M) ℳ (q + 1)).comp
      (cechDiff (A := A) (n := n) (M := M) ℳ q) = 0 := by
  apply LinearMap.ext; intro x
  funext T
  -- Expand the outer differential, then the inner one, and push the linear maps through the
  -- sums: this produces the double sum over ordered pairs `(i,j)`, `i ∈ T`, `j ∈ T \ {i}`.
  simp only [LinearMap.comp_apply, LinearMap.zero_apply]
  rw [cechDiff, LinearMap.pi_apply, cechDiffComp_eq_resZero]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply]
  simp only [Pi.zero_apply]
  simp only [LinearMap.proj_apply, LinearMap.pi_apply, cechDiff, cechDiffComp_eq_resZero]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, map_sum, map_zsmul,
    LinearMap.proj_apply, resZero_comp_apply]
  -- Combine the two integer coefficients acting on each summand, and the two nested sums into a
  -- single sum over the product `T × T` (the diagonal contributing zero).
  simp only [Finset.smul_sum, smul_smul]
  let pairCoeff : Fin n → Fin n → ℤ := fun i j =>
    (-1 : ℤ) ^ ((T.1.filter (fun k => k < i)).card) *
      (-1 : ℤ) ^ (((T.1.erase i).filter (fun k => k < j)).card)
  let G : (i : Fin n) → i ∈ T.1 → (j : Fin n) → j ∈ T.1.erase i → degZero (A := A) ℳ T.1 :=
    fun i hi j hj => pairCoeff i j •
      resZero (A := A) (M := M) ℳ
        ((Finset.erase_subset j (T.1.erase i)).trans (Finset.erase_subset i T.1))
        (x ⟨(T.1.erase i).erase j,
          by rw [Finset.card_erase_of_mem hj, Finset.card_erase_of_mem hi]; omega⟩)
  let f : Fin n × Fin n → degZero (A := A) ℳ T.1 := fun p =>
    if h : p.1 ∈ T.1 ∧ p.2 ∈ T.1.erase p.1 then G p.1 h.1 p.2 h.2 else 0
  rw [sum_attach_erase_eq_sum_product (G := G)]
  show ∑ p ∈ T.1 ×ˢ T.1, f p = 0
  -- The diagonal vanishes, and the two terms of an off-diagonal pair are opposites.
  have hdiag : ∀ i ∈ T.1, f (i, i) = 0 := by
    intro i _
    show (if h : i ∈ T.1 ∧ i ∈ T.1.erase i then G i h.1 i h.2 else 0) = 0
    rw [dite_eq_right]
    rintro ⟨-, h2⟩
    exact (Finset.mem_erase.mp h2).1 rfl
  have hswap : ∀ p ∈ T.1 ×ˢ T.1, f p.swap = - f p := by
    rintro ⟨i, j⟩ hp
    have hi : i ∈ T.1 := (Finset.mem_product.mp hp).1
    have hj : j ∈ T.1 := (Finset.mem_product.mp hp).2
    show f (j, i) = - f (i, j)
    by_cases hij : i = j
    · subst hij
      rw [hdiag i hi, neg_zero]
    · have hgi : i ∈ T.1 ∧ j ∈ T.1.erase i := ⟨hi, Finset.mem_erase.mpr ⟨Ne.symm hij, hj⟩⟩
      have hgj : j ∈ T.1 ∧ i ∈ T.1.erase j := ⟨hj, Finset.mem_erase.mpr ⟨hij, hi⟩⟩
      show (if h : j ∈ T.1 ∧ i ∈ T.1.erase j then G j h.1 i h.2 else 0) =
        - (if h : i ∈ T.1 ∧ j ∈ T.1.erase i then G i h.1 j h.2 else 0)
      rw [dite_eq_left hgj, dite_eq_left hgi]
      -- The two erased finsets agree, and so do the two restriction maps applied to `x`.
      have hsub1 : (T.1.erase j).erase i ⊆ T.1 :=
        (Finset.erase_subset i (T.1.erase j)).trans (Finset.erase_subset j T.1)
      have hsub2 : (T.1.erase i).erase j ⊆ T.1 :=
        (Finset.erase_subset j (T.1.erase i)).trans (Finset.erase_subset i T.1)
      have hc1 : ((T.1.erase j).erase i).card = q + 1 := by
        rw [Finset.card_erase_of_mem hgj.2, Finset.card_erase_of_mem hgj.1]; omega
      have hc2 : ((T.1.erase i).erase j).card = q + 1 := by
        rw [Finset.card_erase_of_mem hgi.2, Finset.card_erase_of_mem hgi.1]; omega
      have hval : resZero (A := A) (M := M) ℳ (S := (T.1.erase j).erase i) (T := T.1) hsub1
            (x ⟨(T.1.erase j).erase i, hc1⟩)
          = resZero (A := A) (M := M) ℳ (S := (T.1.erase i).erase j) (T := T.1) hsub2
            (x ⟨(T.1.erase i).erase j, hc2⟩) := by
        have hset : (T.1.erase j).erase i = (T.1.erase i).erase j :=
          (Finset.erase_right_comm (a := i) (b := j)).symm
        have hupair : (⟨(T.1.erase j).erase i, hc1⟩ : {S : Finset (Fin n) // S.card = q + 1})
            = ⟨(T.1.erase i).erase j, hc2⟩ := Subtype.ext hset
        exact resZero_eq_of_eq hset hsub1 hsub2 (heq_apply_of_eq hupair x)
      -- The two integer coefficients sum to zero.
      have hcoe : pairCoeff j i + pairCoeff i j = 0 :=
        negOne_pow_card_filter_erase T.1 hj hi (Ne.symm hij)
      rw [show G j hgj.1 i hgj.2 = pairCoeff j i •
            resZero (A := A) (M := M) ℳ (S := (T.1.erase j).erase i) (T := T.1) hsub1
              (x ⟨(T.1.erase j).erase i, hc1⟩) from rfl,
          show G i hgi.1 j hgi.2 = pairCoeff i j •
            resZero (A := A) (M := M) ℳ (S := (T.1.erase i).erase j) (T := T.1) hsub2
              (x ⟨(T.1.erase i).erase j, hc2⟩) from rfl,
          hval, eq_neg_of_add_eq_zero_right hcoe, neg_smul, neg_neg]
  exact sum_product_swap_eq_zero T.1 f hswap hdiag

end Work.DSCOH
