import Mathlib
import Submission.Commons.NumberTheory.NumberField.not_isSquare_prod_primes
import Submission.Commons.FieldTheory.Adjoin.finrank_adjoin_sq_eq_two_pow
import Submission.Commons.FieldTheory.Galois.isGalois_of_finrank_eq_two
import Submission.Commons.GroupTheory.SpecificGroups.ZModProd.exists_mulEquiv_multiplicative_fin_zmod_two_of_fintype_commutative_pow_two_eq_one_card
import Submission.Commons.NumberTheory.NumberField.differentIdeal_supp_le_iSup_finset
import Submission.Commons.NumberTheory.NumberField.mem_of_primesEquiv_eq
import Submission.Commons.NumberTheory.NumberField.ramificationIdx_one_of_sqrt_prime_mod_eight
import Submission.Commons.NumberTheory.NumberField.differentIdeal_eq_top_of_ramificationIdx

/-!
# A multiquadratic totally real field unramified outside `S`

For a finite set `S` of primes `q ≡ 1 (mod 8)` we construct the field
`K = ℚ(√q : q ∈ S)` (inside a fixed algebraic closure of `ℚ`), which is totally real,
Galois over `ℚ` with Galois group `(ℤ/2)^S.card` and whose different is supported over `S`.
-/

namespace Commons.NumberTheory.NumberField

open Polynomial

open scoped ComplexOrder
open scoped _root_.NumberField

noncomputable section

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

local instance : IsAlgClosure ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.instIsAlgClosure ℚ

/-- A chosen square root of `q : ℚ` inside `AlgebraicClosure ℚ`. -/
def sqrtOf (q : ℕ) : AlgebraicClosure ℚ :=
  Classical.choose (IsAlgClosed.exists_root
    (X ^ 2 - C (algebraMap ℚ (AlgebraicClosure ℚ) (q : ℚ)) : (AlgebraicClosure ℚ)[X])
    (by rw [Polynomial.degree_X_pow_sub_C (by norm_num : (0:ℕ) < 2)]; norm_num))

lemma sqrtOf_sq (q : ℕ) :
    sqrtOf q ^ 2 = algebraMap ℚ (AlgebraicClosure ℚ) (q : ℚ) := by
  have h := Classical.choose_spec (IsAlgClosed.exists_root
    (X ^ 2 - C (algebraMap ℚ (AlgebraicClosure ℚ) (q : ℚ)) : (AlgebraicClosure ℚ)[X])
    (by rw [Polynomial.degree_X_pow_sub_C (by norm_num : (0:ℕ) < 2)]; norm_num))
  simp only [Polynomial.IsRoot, eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] at h
  exact h

lemma sqrtOf_ne_zero {q : ℕ} (hq : q ≠ 0) : sqrtOf q ≠ 0 := by
  intro h
  have h2 := sqrtOf_sq q
  rw [h, zero_pow (by norm_num : (2:ℕ) ≠ 0)] at h2
  have h3 : algebraMap ℚ (AlgebraicClosure ℚ) (q : ℚ)
      = algebraMap ℚ (AlgebraicClosure ℚ) 0 := by
    rw [map_zero]; exact h2.symm
  have h4 : (q : ℚ) = 0 := (algebraMap ℚ (AlgebraicClosure ℚ)).injective h3
  exact hq (by exact_mod_cast h4)

/-- The two square roots of `q` in the algebraic closure are `± sqrtOf q`. -/
lemma eq_or_eq_neg_sqrtOf {q : ℕ} {y : AlgebraicClosure ℚ}
    (hy : y ^ 2 = algebraMap ℚ (AlgebraicClosure ℚ) (q : ℚ)) :
    y = sqrtOf q ∨ y = -sqrtOf q := by
  have h := sqrtOf_sq q
  have hmul : (y - sqrtOf q) * (y + sqrtOf q) = 0 := by
    have : y ^ 2 - (sqrtOf q) ^ 2 = 0 := by rw [hy, h, sub_self]
    linear_combination this
  rcases mul_eq_zero.mp hmul with h1 | h2
  · left; linear_combination h1
  · right; linear_combination h2

/-- The multiquadratic field `ℚ(√q : q ∈ S)`. -/
abbrev mqField (S : Finset ℕ) : IntermediateField ℚ (AlgebraicClosure ℚ) :=
  IntermediateField.adjoin ℚ (Set.range (fun q : S => sqrtOf q.val))

lemma mqField_gen_mem (S : Finset ℕ) (q : S) :
    sqrtOf q.val ∈ (mqField S : Set (AlgebraicClosure ℚ)) :=
  IntermediateField.subset_adjoin ℚ _ (Set.mem_range_self q)

/-- The generator of `mqField S` attached to `q ∈ S`. -/
def mqGen (S : Finset ℕ) (q : S) : ↥(mqField S) := ⟨sqrtOf q.val, mqField_gen_mem S q⟩

lemma mqGen_sq (S : Finset ℕ) (q : S) :
    (mqGen S q : ↥(mqField S)) ^ 2 = algebraMap ℚ ↥(mqField S) ((q : S) : ℕ) := by
  apply Subtype.ext
  change sqrtOf q.val ^ 2 = algebraMap ℚ (AlgebraicClosure ℚ) ((q : S) : ℕ)
  rw [sqrtOf_sq]

lemma mqField_finiteDimensional (S : Finset ℕ) : FiniteDimensional ℚ ↥(mqField S) := by
  have hfin : (Set.range (fun q : S => sqrtOf q.val)).Finite := Set.finite_range _
  refine IntermediateField.finiteDimensional_adjoin ?_
  intro x hx
  simp only [Set.mem_range] at hx
  obtain ⟨q, rfl⟩ := hx
  apply IsIntegral.of_pow (R := ℚ) (B := AlgebraicClosure ℚ) (n := 2) (by norm_num)
  rw [sqrtOf_sq]
  exact isIntegral_natCast (R := ℚ) (B := AlgebraicClosure ℚ) q.val

set_option maxHeartbeats 1600000 in
lemma mqField_normal (S : Finset ℕ) : Normal ℚ (mqField S) :=
  (IntermediateField.normal_iff_forall_fieldRange_le (K := mqField S)).mpr (fun σ => by
    refine fun x hx => ?_
    rw [AlgHom.mem_fieldRange] at hx
    obtain ⟨y, hy⟩ := hx
    subst hy
    have key : ∀ (w : AlgebraicClosure ℚ) (hw : w ∈ (mqField S : Set (AlgebraicClosure ℚ))),
        σ ⟨w, hw⟩ ∈ (mqField S : Set (AlgebraicClosure ℚ)) := by
      intro w hw
      exact (IntermediateField.adjoin_induction (F := ℚ)
        (s := Set.range (fun q : S => sqrtOf q.val))
        (p := fun w (_ : w ∈ IntermediateField.adjoin ℚ (Set.range (fun q : S => sqrtOf q.val))) =>
          ∀ hw' : w ∈ (mqField S : Set (AlgebraicClosure ℚ)),
            σ ⟨w, hw'⟩ ∈ (mqField S : Set (AlgebraicClosure ℚ)))
        (by
          intro w hw'
          simp only [Set.mem_range] at hw'
          obtain ⟨q, rfl⟩ := hw'
          intro hw''
          set x : ↥(mqField S) := ⟨sqrtOf q.val, hw''⟩ with hx
          have hx2 : x ^ 2 = algebraMap ℚ ↥(mqField S) ((q : S) : ℕ) := by
            apply Subtype.ext
            change sqrtOf q.val ^ 2 = algebraMap ℚ (AlgebraicClosure ℚ) ((q : S) : ℕ)
            rw [sqrtOf_sq]
          have hsq : (σ x) ^ 2 = algebraMap ℚ (AlgebraicClosure ℚ) ((q : S) : ℕ) := by
            rw [← map_pow, hx2]
            exact σ.commutes ((q : S) : ℕ)
          rcases eq_or_eq_neg_sqrtOf hsq with h | h
          · rw [h]; exact mqField_gen_mem S q
          · rw [h]; exact neg_mem (mqField_gen_mem S q))
        (by
          intro r hw'
          have h : σ ⟨algebraMap ℚ (AlgebraicClosure ℚ) r, hw'⟩
              = algebraMap ℚ (AlgebraicClosure ℚ) r := by
            change σ (algebraMap ℚ ↥(mqField S) r) = algebraMap ℚ (AlgebraicClosure ℚ) r
            exact σ.commutes r
          rw [h]
          exact (mqField S).algebraMap_mem r)
        (by
          intro a b ha hb iha ihb hw'
          have heq : (⟨a + b, hw'⟩ : ↥(mqField S)) = ⟨a, ha⟩ + ⟨b, hb⟩ := Subtype.ext rfl
          rw [heq, map_add]
          exact add_mem (iha ha) (ihb hb))
        (by
          intro a ha iha hw'
          have heq : (⟨a⁻¹, hw'⟩ : ↥(mqField S)) = (⟨a, ha⟩ : ↥(mqField S))⁻¹ := Subtype.ext rfl
          rw [heq, map_inv₀]
          exact inv_mem (iha ha))
        (by
          intro a b ha hb iha ihb hw'
          have heq : (⟨a * b, hw'⟩ : ↥(mqField S)) = ⟨a, ha⟩ * ⟨b, hb⟩ := Subtype.ext rfl
          rw [heq, map_mul]
          exact mul_mem (iha ha) (ihb hb))
        hw) hw
    exact key y y.2)

set_option maxHeartbeats 1600000 in
lemma mqField_finrank (S : Finset ℕ) (hS : ∀ q ∈ S, Nat.Prime q) :
    Module.finrank ℚ ↥(mqField S) = 2 ^ S.card := by
  haveI := mqField_finiteDimensional S
  have hcard : Fintype.card S = S.card := Fintype.card_coe S
  have key := Commons.FieldTheory.Adjoin.finrank_adjoin_sq_eq_two_pow
    (F := ℚ) (L := ↥(mqField S))
    (a := fun q : S => ((q : S) : ℕ))
    (c := fun q : S => mqGen S q)
    (by intro q; exact_mod_cast (hS q.val q.2).ne_zero)
    (by intro q; exact mqGen_sq S q)
    (by
      let c : S → ↥(mqField S) := fun q => mqGen S q
      let L : IntermediateField ℚ ↥(mqField S) := IntermediateField.adjoin ℚ (Set.range c)
      have hmap : L.map (mqField S).val = mqField S := by
        refine le_antisymm ?_ ?_
        · refine (IntermediateField.map_le_iff_le_comap (f := (mqField S).val) (s := L)
            (t := mqField S)).mpr ?_
          intro x hx
          exact x.2
        · change IntermediateField.adjoin ℚ (Set.range (fun q : S => sqrtOf q.val))
            ≤ L.map (mqField S).val
          refine (IntermediateField.adjoin_le_iff).mpr ?_
          rintro y ⟨q, rfl⟩
          exact (IntermediateField.mem_map (S := L) (f := (mqField S).val)).mpr
            ⟨c q, IntermediateField.subset_adjoin ℚ _ (Set.mem_range_self q), rfl⟩
      have htop : (⊤ : IntermediateField ℚ ↥(mqField S)).map (mqField S).val = mqField S :=
        (AlgHom.fieldRange_eq_map (mqField S).val).symm.trans
          (IntermediateField.fieldRange_val (mqField S))
      exact IntermediateField.map_injective (mqField S).val (hmap.trans htop.symm))
    (by
      intro T hT r hr
      have hinj : ∀ i ∈ T, ∀ j ∈ T, ((i : S) : ℕ) = ((j : S) : ℕ) → i = j := by
        intro i _ j _ hij
        exact Subtype.ext hij
      have h := Commons.NumberTheory.NumberField.not_isSquare_prod_primes T (fun i : S => ((i : S) : ℕ))
        (by intro i _; exact hS i.val i.2) hinj hT r
      refine h ?_
      rw [hr]
      push_cast
      rfl)
  rwa [hcard] at key

instance mqField_numberField (S : Finset ℕ) : NumberField ↥(mqField S) := by
  haveI := mqField_finiteDimensional S
  exact NumberField.of_module_finite ℚ ↥(mqField S)

instance mqField_isGalois (S : Finset ℕ) : IsGalois ℚ ↥(mqField S) :=
  isGalois_iff.mpr ⟨inferInstance, mqField_normal S⟩


lemma mqGen_apply (S : Finset ℕ) (σ : ↥(mqField S) ≃ₐ[ℚ] ↥(mqField S)) (q : S) :
    σ (mqGen S q) = mqGen S q ∨ σ (mqGen S q) = -mqGen S q := by
  have hsq : ((σ (mqGen S q) : ↥(mqField S)) : AlgebraicClosure ℚ) ^ 2
      = algebraMap ℚ (AlgebraicClosure ℚ) (q.val : ℚ) := by
    calc ((σ (mqGen S q) : ↥(mqField S)) : AlgebraicClosure ℚ) ^ 2
        = (mqField S).val ((σ (mqGen S q)) ^ 2) :=
          (map_pow (mqField S).val (σ (mqGen S q)) 2).symm
      _ = (mqField S).val (σ ((mqGen S q) ^ 2)) := by rw [← map_pow σ (mqGen S q) 2]
      _ = (mqField S).val (σ (algebraMap ℚ ↥(mqField S) ((q : S) : ℕ))) := by rw [mqGen_sq]
      _ = (mqField S).val (algebraMap ℚ ↥(mqField S) ((q : S) : ℕ)) := by rw [AlgEquiv.commutes]
      _ = algebraMap ℚ (AlgebraicClosure ℚ) ((q : S) : ℕ) := rfl
      _ = algebraMap ℚ (AlgebraicClosure ℚ) (q.val : ℚ) := by simp
  rcases eq_or_eq_neg_sqrtOf hsq with h | h
  · left; apply Subtype.ext; exact h
  · right; apply Subtype.ext; exact h

set_option maxHeartbeats 1600000 in
lemma mqField_sq_eq_one (S : Finset ℕ) (σ : ↥(mqField S) ≃ₐ[ℚ] ↥(mqField S)) :
    σ ^ 2 = 1 := by
  have hmul : ((σ * σ : ↥(mqField S) ≃ₐ[ℚ] ↥(mqField S)) : ↥(mqField S) →ₐ[ℚ] ↥(mqField S))
      = ((1 : ↥(mqField S) ≃ₐ[ℚ] ↥(mqField S)) : ↥(mqField S) →ₐ[ℚ] ↥(mqField S)) := by
    apply IntermediateField.adjoin_algHom_ext ℚ (s := Set.range (fun q : S => sqrtOf q.val))
    intro x hx
    simp only [Set.mem_range] at hx
    obtain ⟨q, rfl⟩ := hx
    have hgen : (⟨sqrtOf q.val, IntermediateField.subset_adjoin ℚ _ (Set.mem_range_self q)⟩
        : ↥(mqField S)) = mqGen S q := Subtype.ext rfl
    rw [hgen]
    rcases mqGen_apply S σ q with hk | hk
    · show σ (σ (mqGen S q)) = mqGen S q
      rw [hk, hk]
    · show σ (σ (mqGen S q)) = mqGen S q
      rw [hk, map_neg, hk, neg_neg]
  have h2 : (σ * σ : ↥(mqField S) ≃ₐ[ℚ] ↥(mqField S)) = 1 :=
    AlgEquiv.coe_toAlgHom_injective hmul
  rw [pow_two, h2]

lemma mqField_isMulCommutative (S : Finset ℕ) :
    IsMulCommutative (↥(mqField S) ≃ₐ[ℚ] ↥(mqField S)) := by
  rw [isMulCommutative_iff]
  have hinv : ∀ σ : ↥(mqField S) ≃ₐ[ℚ] ↥(mqField S), σ⁻¹ = σ := fun σ =>
    inv_eq_of_mul_eq_one_left (by simpa [pow_two] using mqField_sq_eq_one S σ)
  intro a b
  calc a * b = (a * b)⁻¹ := (hinv (a * b)).symm
    _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    _ = b * a := by rw [hinv b, hinv a]

set_option maxHeartbeats 800000 in
lemma mqField_galoisGroup (S : Finset ℕ) (hS : ∀ q ∈ S, Nat.Prime q) :
    Nonempty ((↥(mqField S) ≃ₐ[ℚ] ↥(mqField S)) ≃* Multiplicative (Fin S.card → ZMod 2)) := by
  haveI := mqField_finiteDimensional S
  haveI := mqField_isMulCommutative S
  have hcard : Nat.card (↥(mqField S) ≃ₐ[ℚ] ↥(mqField S)) = 2 ^ S.card := by
    rw [IsGalois.card_aut_eq_finrank, mqField_finrank S hS]
  exact Commons.GroupTheory.SpecificGroups.ZModProd.exists_mulEquiv_multiplicative_fin_zmod_two_of_fintype_commutative_pow_two_eq_one_card
    (fun σ => by simpa [pow_two] using mqField_sq_eq_one S σ) hcard

set_option maxHeartbeats 1600000 in
lemma mqField_le_maximalRealSubfield (S : Finset ℕ) :
    (mqField S).toSubfield ≤ NumberField.maximalRealSubfield (AlgebraicClosure ℚ) := by
  intro x hx
  rw [NumberField.mem_maximalRealSubfield_iff]
  refine IntermediateField.adjoin_induction ℚ (s := Set.range (fun q : S => sqrtOf q.val))
    (p := fun x (_ : x ∈ IntermediateField.adjoin ℚ (Set.range (fun q : S => sqrtOf q.val))) =>
      ∀ φ : AlgebraicClosure ℚ →+* ℂ, star (φ x) = φ x) ?_ ?_ ?_ ?_ ?_ ?_
  · intro x hx φ
    simp only [Set.mem_range] at hx
    obtain ⟨q, rfl⟩ := hx
    have hz : (φ (sqrtOf q.val)) ^ 2 = ((q.val : ℕ) : ℂ) := by
      rw [← map_pow, sqrtOf_sq]
      simp
    have hz_nn : 0 ≤ (φ (sqrtOf q.val)) ^ 2 := by
      rw [hz, Complex.nonneg_iff]
      constructor
      · exact_mod_cast Nat.zero_le q.val
      · simp
    have him : (φ (sqrtOf q.val)).im = 0 := (Complex.sq_nonneg_iff).mp hz_nn
    apply Complex.ext <;> simp [him]
  · intro r φ
    have h1 : φ (algebraMap ℚ (AlgebraicClosure ℚ) r) = (r : ℂ) := map_ratCast φ r
    rw [h1]
    apply Complex.ext <;> simp
  · intro a b ha hb iha ihb φ
    rw [map_add, star_add, iha φ, ihb φ]
  · intro a ha iha φ
    rw [map_inv₀, star_inv₀, iha φ]
  · intro a b ha hb iha ihb φ
    rw [map_mul, star_mul, iha φ, ihb φ, mul_comm]
  · exact hx

lemma mqField_isTotallyReal (S : Finset ℕ) : NumberField.IsTotallyReal ↥(mqField S) :=
  (NumberField.isTotallyReal_iff_le_maximalRealSubfield (K := AlgebraicClosure ℚ)
    (E := (mqField S).toSubfield)).mpr (mqField_le_maximalRealSubfield S)

/-! ## The quadratic subfields `ℚ(√q)` -/

/-- The quadratic field `ℚ(√q)` for `q : ℕ`. -/
abbrev quadField (q : ℕ) : IntermediateField ℚ (AlgebraicClosure ℚ) :=
  IntermediateField.adjoin ℚ ({sqrtOf q} : Set (AlgebraicClosure ℚ))

lemma quadField_le_mqField (S : Finset ℕ) (q : S) : quadField q.val ≤ mqField S := by
  rw [quadField, IntermediateField.adjoin_le_iff]
  rintro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  exact mqField_gen_mem S q

lemma quadField_finiteDimensional (q : ℕ) : FiniteDimensional ℚ ↥(quadField q) := by
  refine IntermediateField.finiteDimensional_adjoin ?_
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst hx
  apply IsIntegral.of_pow (R := ℚ) (B := AlgebraicClosure ℚ) (n := 2) (by norm_num)
  rw [sqrtOf_sq]
  exact isIntegral_natCast (R := ℚ) (B := AlgebraicClosure ℚ) q

lemma quadField_finrank (q : ℕ) (hq : Nat.Prime q) :
    Module.finrank ℚ ↥(quadField q) = 2 := by
  haveI := quadField_finiteDimensional q
  have hcard : Fintype.card (Fin 1) = 1 := by simp
  have key := Commons.FieldTheory.Adjoin.finrank_adjoin_sq_eq_two_pow
    (F := ℚ) (L := ↥(quadField q)) (ι := Fin 1)
    (a := fun _ : Fin 1 => q) (c := fun _ : Fin 1 => (⟨sqrtOf q, IntermediateField.subset_adjoin ℚ _ (by simp)⟩ : ↥(quadField q)))
    (by intro i; exact_mod_cast hq.ne_zero)
    (by
      intro i
      apply Subtype.ext
      change sqrtOf q ^ 2 = algebraMap ℚ (AlgebraicClosure ℚ) (q : ℚ)
      rw [sqrtOf_sq])
    (by
      let c : Fin 1 → ↥(quadField q) :=
        fun _ => ⟨sqrtOf q, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
      let L : IntermediateField ℚ ↥(quadField q) := IntermediateField.adjoin ℚ (Set.range c)
      have hmap : L.map (quadField q).val = quadField q := by
        refine le_antisymm ?_ ?_
        · refine (IntermediateField.map_le_iff_le_comap (f := (quadField q).val) (s := L)
            (t := quadField q)).mpr ?_
          intro x hx
          exact x.2
        · change IntermediateField.adjoin ℚ ({sqrtOf q} : Set (AlgebraicClosure ℚ))
            ≤ L.map (quadField q).val
          refine (IntermediateField.adjoin_le_iff).mpr ?_
          intro y hy
          rw [Set.mem_singleton_iff] at hy
          subst hy
          exact (IntermediateField.mem_map (S := L) (f := (quadField q).val)).mpr
            ⟨c 0, IntermediateField.subset_adjoin ℚ _ (Set.mem_range_self 0), rfl⟩
      have htop : (⊤ : IntermediateField ℚ ↥(quadField q)).map (quadField q).val = quadField q :=
        (AlgHom.fieldRange_eq_map (quadField q).val).symm.trans
          (IntermediateField.fieldRange_val (quadField q))
      exact IntermediateField.map_injective (quadField q).val (hmap.trans htop.symm))
    (by
      intro T hT r hr
      have hinj : ∀ i ∈ T, ∀ j ∈ T, q = q → i = j := by
        intro i _ j _ _
        exact Subsingleton.elim i j
      have h := Commons.NumberTheory.NumberField.not_isSquare_prod_primes T (fun _ : Fin 1 => q)
        (by intro i _; exact hq) hinj hT r
      refine h ?_
      rw [hr]
      push_cast
      rfl)
  simpa [hcard] using key

instance quadField_numberField (q : ℕ) : NumberField ↥(quadField q) := by
  haveI := quadField_finiteDimensional q
  exact NumberField.of_module_finite ℚ ↥(quadField q)

lemma quadField_isGalois (q : ℕ) (hq : Nat.Prime q) : IsGalois ℚ ↥(quadField q) := by
  haveI := quadField_finiteDimensional q
  exact Commons.FieldTheory.Galois.isGalois_of_finrank_eq_two (quadField_finrank q hq) (by norm_num)

/-! ## Ramification -/

set_option maxHeartbeats 1600000 in
lemma quadField_different_supp (S : Finset ℕ) (hS : ∀ q ∈ S, Nat.Prime q)
    (hmod : ∀ q ∈ S, q % 8 = 1) (q : S) :
    ∀ P : Ideal (𝓞 ↥(quadField q.val)), P.IsPrime → P ≠ ⊥ →
      P ∣ differentIdeal (𝓞 ℚ) (𝓞 ↥(quadField q.val)) →
      ∃ q' ∈ S, P.LiesOver (Ideal.span ({(q' : ℤ)} : Set ℤ)) := by
  
  intro P hP hPne hPdvd
  by_cases hqP : (q.val : 𝓞 ↥(quadField q.val)) ∈ P
  · refine ⟨q, q.2, ?_⟩
    haveI : (Ideal.span ({(q.val : ℤ)} : Set ℤ)).IsPrime := by
      rw [Ideal.span_singleton_prime (by exact_mod_cast (hS q.val q.2).ne_zero)]
      exact Nat.prime_iff_prime_int.mp (hS q.val q.2)
    have hle : Ideal.span ({(q.val : ℤ)} : Set ℤ)
        ≤ Ideal.comap (algebraMap ℤ (𝓞 ↥(quadField q.val))) P := by
      rw [Ideal.span_le]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact (Ideal.mem_comap).mpr (by simpa using hqP)
    have hmax : (Ideal.span ({(q.val : ℤ)} : Set ℤ)).IsMaximal :=
      ‹(Ideal.span ({(q.val : ℤ)} : Set ℤ)).IsPrime›.isMaximal (by
        intro hbot
        have hz : (q.val : ℤ) = 0 := by simpa [Ideal.span_singleton_eq_bot] using hbot
        exact (hS q.val q.2).ne_zero (by exact_mod_cast hz))
    haveI hPcp : (Ideal.comap (algebraMap ℤ (𝓞 ↥(quadField q.val))) P).IsPrime :=
      Ideal.IsPrime.comap _
    exact ⟨hmax.eq_of_le hPcp.ne_top hle⟩
  · exfalso
    set 𝔭 : Ideal (𝓞 ℚ) := P.under (𝓞 ℚ) with h𝔭def
    haveI h𝔭prime : 𝔭.IsPrime := inferInstance
    have h𝔭ne : 𝔭 ≠ ⊥ := Ideal.IsIntegral.comap_ne_bot (𝓞 ℚ) hPne
    let 𝔳 : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ) := ⟨𝔭, h𝔭prime, h𝔭ne⟩
    let p : ℕ := Rat.HeightOneSpectrum.natGenerator 𝔳
    have hp : Nat.Prime p := Rat.HeightOneSpectrum.prime_natGenerator 𝔳
    have hp_mem : (p : 𝓞 ℚ) ∈ 𝔭 :=
      mem_of_primesEquiv_eq 𝔳 p hp rfl
    have hp_ne_q : p ≠ q.val := by
      intro hpq
      apply hqP
      have hmem : algebraMap (𝓞 ℚ) (𝓞 ↥(quadField q.val)) (p : 𝓞 ℚ) ∈ P := by
        rw [← Ideal.mem_comap]
        exact hp_mem
      have h2 : (p : 𝓞 ↥(quadField q.val)) ∈ P := by simpa using hmem
      rwa [hpq] at h2
    let x : ↥(quadField q.val) :=
      ⟨sqrtOf q.val, IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton _)⟩
    have hx : x ^ 2 = algebraMap ℚ ↥(quadField q.val) (q.val : ℚ) := by
      apply Subtype.ext
      change sqrtOf q.val ^ 2 = algebraMap ℚ (AlgebraicClosure ℚ) (q.val : ℚ)
      rw [sqrtOf_sq]
    haveI hfd : FiniteDimensional ℚ ↥(quadField q.val) := quadField_finiteDimensional q.val
    have hgen : Algebra.adjoin ℚ ({x} : Set ↥(quadField q.val)) = ⊤ := by
      refine IntermediateField.adjoin_eq_top_iff.mp ?_
      have hmap : (IntermediateField.adjoin ℚ ({x} : Set ↥(quadField q.val))).map
          (quadField q.val).val = quadField q.val := by
        refine le_antisymm ?_ ?_
        · refine (IntermediateField.map_le_iff_le_comap (f := (quadField q.val).val)
            (s := IntermediateField.adjoin ℚ ({x} : Set ↥(quadField q.val)))
            (t := quadField q.val)).mpr ?_
          intro y hy
          exact y.2
        · change IntermediateField.adjoin ℚ ({sqrtOf q.val} : Set (AlgebraicClosure ℚ))
            ≤ (IntermediateField.adjoin ℚ ({x} : Set ↥(quadField q.val))).map
              (quadField q.val).val
          refine (IntermediateField.adjoin_le_iff).mpr ?_
          intro y hy
          rw [Set.mem_singleton_iff] at hy
          subst hy
          exact (IntermediateField.mem_map
            (S := IntermediateField.adjoin ℚ ({x} : Set ↥(quadField q.val)))
            (f := (quadField q.val).val)).mpr
            ⟨x, IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton _), rfl⟩
      have htop : (⊤ : IntermediateField ℚ ↥(quadField q.val)).map (quadField q.val).val
          = quadField q.val :=
        (AlgHom.fieldRange_eq_map (quadField q.val).val).symm.trans
          (IntermediateField.fieldRange_val (quadField q.val))
      exact IntermediateField.map_injective (quadField q.val).val (hmap.trans htop.symm)
    have hlies : P.LiesOver 𝔭 := ⟨rfl⟩
    have hram : P.ramificationIdx (𝓞 ℚ) = 1 :=
      ramificationIdx_one_of_sqrt_prime_mod_eight (hS q.val q.2) (hmod q.val q.2) hp hp_ne_q
        x hx hgen 𝔭 h𝔭prime h𝔭ne hp_mem P hP hlies
    exact (ramificationIdx_one_iff_not_dvd_differentIdeal (E := ℚ) (K := ↥(quadField q.val))
      P hP).mpr hram hPdvd

set_option maxHeartbeats 1600000 in
lemma mqField_different_supp (S : Finset ℕ) (hS : ∀ q ∈ S, Nat.Prime q)
    (hmod : ∀ q ∈ S, q % 8 = 1) :
    ∀ P : Ideal (𝓞 ↥(mqField S)), P.IsPrime → P ≠ ⊥ →
      P ∣ differentIdeal (𝓞 ℚ) (𝓞 ↥(mqField S)) →
      ∃ q ∈ S, P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ)) := by
  haveI := mqField_finiteDimensional S
  have hfd : ∀ q : S, FiniteDimensional ℚ ↥(quadField q.val) :=
    fun q => quadField_finiteDimensional q.val
  have hgal : ∀ q : S, IsGalois ℚ ↥(quadField q.val) :=
    fun q => quadField_isGalois q.val (hS q.val q.2)
  have hsup := quadField_different_supp S hS hmod
  have hle : mqField S ≤ ⨆ q : S, quadField q.val := by
    rw [mqField, IntermediateField.adjoin_le_iff]
    rintro y ⟨q, rfl⟩
    exact le_iSup (fun q : S => quadField q.val) q
      (IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton _))
  exact @Commons.NumberTheory.NumberField.differentIdeal_supp_le_iSup_finset ℚ _ _ S S
    (fun q : S => quadField q.val) _ hfd hgal hsup (mqField S) _ _ (mqField_isGalois S) hle

theorem exists_multiquadratic_totallyReal_unramifiedOutside
    (S : Finset ℕ) (hS : ∀ q ∈ S, Nat.Prime q) (hmod : ∀ q ∈ S, q % 8 = 1) :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : NumberField.IsTotallyReal K)
      (_ : IsGalois ℚ K),
      Module.finrank ℚ K = 2 ^ S.card ∧
      Nonempty ((K ≃ₐ[ℚ] K) ≃* Multiplicative (Fin S.card → ZMod 2)) ∧
      (∀ (P : Ideal (NumberField.RingOfIntegers K)), P.IsPrime → P ≠ ⊥ →
        P ∣ differentIdeal (NumberField.RingOfIntegers ℚ) (NumberField.RingOfIntegers K) →
          ∃ q ∈ S, P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ))) := by
  haveI := mqField_finiteDimensional S
  haveI := mqField_isGalois S
  exact ⟨↥(mqField S), inferInstance, mqField_numberField S, mqField_isTotallyReal S,
    mqField_isGalois S, mqField_finrank S hS, mqField_galoisGroup S hS,
    mqField_different_supp S hS hmod⟩

end
end Commons.NumberTheory.NumberField
