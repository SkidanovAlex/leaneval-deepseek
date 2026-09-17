import Mathlib
import Submission.Commons.Algebra.Lie.expAd_isLieEquiv
import Submission.Commons.Algebra.Lie.ad_locallyNilpotent_of_generators
import Submission.Commons.Algebra.Lie.SerreConstruction.eq_top_of_lieSubalgebra_of_generators
import Submission.Commons.Algebra.Lie.SerreConstruction.e8_zero_weightSpace_finrank

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable section
open CartanMatrix

namespace Commons.Algebra.Lie.SerreConstruction

/-! ## The quotient map `FL8 → L8` and the Serre relations in `e₈`

Everything here is proved from the defining Serre relations of the Cartan matrix `E₈`. -/

/-- The quotient Lie algebra morphism `FL8 → L8`. -/
noncomputable def quotMk : FL8 →ₗ⁅ℂ⁆ L8 :=
  { toLinearMap := (LieSubmodule.Quotient.mk' lieJ).toLinearMap
    map_lie' := fun {x y} => LieSubmodule.Quotient.mk_bracket lieJ x y }

lemma quotMk_apply (x : FL8) :
    quotMk x = LieSubmodule.Quotient.mk (N := lieJ) x := rfl

@[simp] lemma quotMk_of_H (i : Fin 8) :
    quotMk (FreeLieAlgebra.of ℂ (CartanMatrix.Generators.H i)) = SerreH i := rfl
@[simp] lemma quotMk_of_E (i : Fin 8) :
    quotMk (FreeLieAlgebra.of ℂ (CartanMatrix.Generators.E i)) = SerreE i := rfl
@[simp] lemma quotMk_of_F (i : Fin 8) :
    quotMk (FreeLieAlgebra.of ℂ (CartanMatrix.Generators.F i)) = SerreF i := rfl

lemma quotMk_ad (x y : FL8) :
    quotMk ((LieAlgebra.ad ℂ FL8 x) y) = (LieAlgebra.ad ℂ L8 (quotMk x)) (quotMk y) := by
  rw [LieAlgebra.ad_apply, LieAlgebra.ad_apply]
  exact LieHom.map_lie quotMk x y

lemma quotMk_ad_pow : ∀ (n : ℕ) (x y : FL8),
    quotMk ((((LieAlgebra.ad ℂ FL8) x)^n) y) =
      ((((LieAlgebra.ad ℂ L8) (quotMk x))^n) (quotMk y)) := by
  intro n
  induction n with
  | zero => intro x y; simp
  | succ n ih =>
      intro x y
      simp only [pow_succ, Module.End.mul_apply]
      rw [ih, quotMk_ad]

lemma adE_mem_toSet (i j : Fin 8) :
    CartanMatrix.Relations.adE ℂ E8 (i, j) ∈ CartanMatrix.Relations.toSet ℂ E8 := by
  unfold CartanMatrix.Relations.toSet
  exact Or.inl (Or.inr ⟨(i, j), rfl⟩)

lemma adF_mem_toSet (i j : Fin 8) :
    CartanMatrix.Relations.adF ℂ E8 (i, j) ∈ CartanMatrix.Relations.toSet ℂ E8 := by
  unfold CartanMatrix.Relations.toSet
  exact Or.inr ⟨(i, j), rfl⟩

lemma quotMk_eq_zero_of_mem_toSet {x : FL8} (hx : x ∈ CartanMatrix.Relations.toSet ℂ E8) :
    quotMk x = 0 := by
  rw [quotMk_apply, LieSubmodule.Quotient.mk_eq_zero']
  exact LieSubmodule.subset_lieSpan hx

/-- The `ad E`-Serre relation in `e₈`. -/
lemma serreLie_adE (i j : Fin 8) :
    ((((LieAlgebra.ad ℂ L8) (SerreE i))^((-E8 i j).toNat)) (⁅SerreE i, SerreE j⁆)) = 0 := by
  have hb : ⁅SerreE i, SerreE j⁆
      = quotMk (⁅FreeLieAlgebra.of ℂ (CartanMatrix.Generators.E i),
          FreeLieAlgebra.of ℂ (CartanMatrix.Generators.E j)⁆) := by
    rw [← quotMk_of_E i, ← quotMk_of_E j]
    exact (LieHom.map_lie quotMk _ _).symm
  rw [hb]
  have h := quotMk_ad_pow ((-E8 i j).toNat)
    (FreeLieAlgebra.of ℂ (CartanMatrix.Generators.E i))
    (⁅FreeLieAlgebra.of ℂ (CartanMatrix.Generators.E i),
      FreeLieAlgebra.of ℂ (CartanMatrix.Generators.E j)⁆)
  rw [quotMk_of_E] at h
  rw [← h]
  exact quotMk_eq_zero_of_mem_toSet (adE_mem_toSet i j)

/-- The `ad F`-Serre relation in `e₈`. -/
lemma serreLie_adF (i j : Fin 8) :
    ((((LieAlgebra.ad ℂ L8) (SerreF i))^((-E8 i j).toNat)) (⁅SerreF i, SerreF j⁆)) = 0 := by
  have hb : ⁅SerreF i, SerreF j⁆
      = quotMk (⁅FreeLieAlgebra.of ℂ (CartanMatrix.Generators.F i),
          FreeLieAlgebra.of ℂ (CartanMatrix.Generators.F j)⁆) := by
    rw [← quotMk_of_F i, ← quotMk_of_F j]
    exact (LieHom.map_lie quotMk _ _).symm
  rw [hb]
  have h := quotMk_ad_pow ((-E8 i j).toNat)
    (FreeLieAlgebra.of ℂ (CartanMatrix.Generators.F i))
    (⁅FreeLieAlgebra.of ℂ (CartanMatrix.Generators.F i),
      FreeLieAlgebra.of ℂ (CartanMatrix.Generators.F j)⁆)
  rw [quotMk_of_F] at h
  rw [← h]
  exact quotMk_eq_zero_of_mem_toSet (adF_mem_toSet i j)

/-- `(ad eᵢ)² eⱼ = 0`. -/
lemma serreLie_adE_sq (i j : Fin 8) :
    (((LieAlgebra.ad ℂ L8 (SerreE i))^2) (SerreE j)) = 0 := by
  by_cases hij : i = j
  · subst hij
    rw [pow_two, Module.End.mul_apply]
    simp [LieAlgebra.ad_apply]
  · rcases E8_offdiag i j hij with h | h
    · have hz := serreLie_adE i j
      rw [h] at hz
      simp only [neg_zero, Int.toNat_zero, pow_zero, Module.End.one_apply] at hz
      rw [pow_two, Module.End.mul_apply]
      simp [LieAlgebra.ad_apply, hz]
    · have hz := serreLie_adE i j
      rw [h] at hz
      simp only [neg_neg, Int.toNat_one, pow_one] at hz
      rw [pow_two, Module.End.mul_apply]
      simpa [LieAlgebra.ad_apply] using hz

/-- `(ad fᵢ)² fⱼ = 0`. -/
lemma serreLie_adF_sq (i j : Fin 8) :
    (((LieAlgebra.ad ℂ L8 (SerreF i))^2) (SerreF j)) = 0 := by
  by_cases hij : i = j
  · subst hij
    rw [pow_two, Module.End.mul_apply]
    simp [LieAlgebra.ad_apply]
  · rcases E8_offdiag i j hij with h | h
    · have hz := serreLie_adF i j
      rw [h] at hz
      simp only [neg_zero, Int.toNat_zero, pow_zero, Module.End.one_apply] at hz
      rw [pow_two, Module.End.mul_apply]
      simp [LieAlgebra.ad_apply, hz]
    · have hz := serreLie_adF i j
      rw [h] at hz
      simp only [neg_neg, Int.toNat_one, pow_one] at hz
      rw [pow_two, Module.End.mul_apply]
      simpa [LieAlgebra.ad_apply] using hz

/-- Converting an integer multiple to a complex one. -/
lemma zsmul_int_eq (n : ℤ) (x : L8) : n • x = (((n : ℤ)) : ℂ) • x :=
  (Int.cast_smul_eq_zsmul ℂ n x).symm

lemma serreLie_H_E_c (i j : Fin 8) :
    ⁅SerreH i, SerreE j⁆ = (((E8 i j : ℤ)) : ℂ) • SerreE j := by
  rw [serreLie_H_E, zsmul_int_eq]

lemma serreLie_H_F_c (i j : Fin 8) :
    ⁅SerreH i, SerreF j⁆ = (-(((E8 i j : ℤ)) : ℂ)) • SerreF j := by
  rw [serreLie_H_F, zsmul_int_eq, Int.cast_neg]

/-- `[eᵢ, hⱼ] = -Aᵢⱼ eᵢ`. -/
lemma ad_E_H (i j : Fin 8) :
    (LieAlgebra.ad ℂ L8 (SerreE i)) (SerreH j) = -((((E8 i j : ℤ)) : ℂ) • SerreE i) := by
  rw [LieAlgebra.ad_apply, ← lie_skew (SerreE i) (SerreH j), serreLie_H_E_c j i, E8_symm]

/-- `[fᵢ, hⱼ] = Aᵢⱼ fᵢ`. -/
lemma ad_F_H (i j : Fin 8) :
    (LieAlgebra.ad ℂ L8 (SerreF i)) (SerreH j) = ((((E8 i j : ℤ)) : ℂ) • SerreF i) := by
  rw [LieAlgebra.ad_apply, ← lie_skew (SerreF i) (SerreH j), serreLie_H_F_c j i, E8_symm]
  simp only [neg_smul, neg_neg]

/-- `(ad eᵢ)² hⱼ = 0`. -/
lemma ad_E_H_sq (i j : Fin 8) :
    (((LieAlgebra.ad ℂ L8 (SerreE i))^2) (SerreH j)) = 0 := by
  rw [pow_two, Module.End.mul_apply, ad_E_H]
  simp [LieAlgebra.ad_apply]

/-- `(ad fᵢ)² hⱼ = 0`. -/
lemma ad_F_H_sq (i j : Fin 8) :
    (((LieAlgebra.ad ℂ L8 (SerreF i))^2) (SerreH j)) = 0 := by
  rw [pow_two, Module.End.mul_apply, ad_F_H]
  simp [LieAlgebra.ad_apply]

/-- `[eᵢ, fⱼ] = δᵢⱼ hᵢ`. -/
lemma ad_E_F (i j : Fin 8) :
    (LieAlgebra.ad ℂ L8 (SerreE i)) (SerreF j) = if i = j then SerreH i else 0 := by
  rw [LieAlgebra.ad_apply]; exact serreLie_E_F i j

/-- `[fᵢ, eⱼ] = -δᵢⱼ hᵢ`. -/
lemma ad_F_E (i j : Fin 8) :
    (LieAlgebra.ad ℂ L8 (SerreF i)) (SerreE j) = if i = j then -SerreH i else 0 := by
  rw [LieAlgebra.ad_apply, ← lie_skew (SerreF i) (SerreE j), serreLie_E_F j i]
  by_cases h : j = i
  · subst h; rw [if_pos rfl, if_pos rfl]
  · rw [if_neg h, if_neg (Ne.symm h), neg_zero]

/-- `(ad eᵢ)³ fⱼ = 0`. -/
lemma ad_E_F_cube (i j : Fin 8) :
    (((LieAlgebra.ad ℂ L8 (SerreE i))^3) (SerreF j)) = 0 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, Module.End.mul_apply, ad_E_F]
  by_cases h : i = j
  · rw [if_pos h]; exact ad_E_H_sq i i
  · rw [if_neg h]; simp

/-- `(ad fᵢ)³ eⱼ = 0`. -/
lemma ad_F_E_cube (i j : Fin 8) :
    (((LieAlgebra.ad ℂ L8 (SerreF i))^3) (SerreE j)) = 0 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, Module.End.mul_apply, ad_F_E]
  by_cases h : i = j
  · rw [if_pos h, map_neg, ad_F_H_sq i i, neg_zero]
  · rw [if_neg h]; simp

/-! ## Local nilpotency of `ad eᵢ` and `ad fᵢ` on `e₈`

This is deduced from the Serre relations via the abstract lemma
`Commons.Algebra.Lie.ad_locallyNilpotent_of_generators`. -/

lemma hloc_E (i : Fin 8) :
    ∀ y : L8, ∃ n : ℕ, ((((LieAlgebra.ad ℂ L8 (SerreE i))^n) y) = 0) := by
  refine Commons.Algebra.Lie.ad_locallyNilpotent_of_generators (x := SerreE i)
    (S := Set.range (fun g : CartanMatrix.Generators (Fin 8) =>
      quotMk (FreeLieAlgebra.of ℂ g))) (lie_self _) ?_ ?_
  · refine Commons.Algebra.Lie.SerreConstruction.eq_top_of_lieSubalgebra_of_generators
      (R := ℂ) (B := Fin 8) E8 _ (fun g => ?_)
    exact LieSubalgebra.subset_lieSpan (Set.mem_range_self g)
  · intro y hy
    obtain ⟨g, rfl⟩ := hy
    cases g with
    | H j => exact ⟨2, ad_E_H_sq i j⟩
    | E j => exact ⟨2, serreLie_adE_sq i j⟩
    | F j => exact ⟨3, ad_E_F_cube i j⟩

lemma hloc_F (i : Fin 8) :
    ∀ y : L8, ∃ n : ℕ, ((((LieAlgebra.ad ℂ L8 (SerreF i))^n) y) = 0) := by
  refine Commons.Algebra.Lie.ad_locallyNilpotent_of_generators (x := SerreF i)
    (S := Set.range (fun g : CartanMatrix.Generators (Fin 8) =>
      quotMk (FreeLieAlgebra.of ℂ g))) (lie_self _) ?_ ?_
  · refine Commons.Algebra.Lie.SerreConstruction.eq_top_of_lieSubalgebra_of_generators
      (R := ℂ) (B := Fin 8) E8 _ (fun g => ?_)
    exact LieSubalgebra.subset_lieSpan (Set.mem_range_self g)
  · intro y hy
    obtain ⟨g, rfl⟩ := hy
    cases g with
    | H j => exact ⟨2, ad_F_H_sq i j⟩
    | E j => exact ⟨3, ad_F_E_cube i j⟩
    | F j => exact ⟨2, serreLie_adF_sq i j⟩

/-! ## The truncated exponentials evaluated at Cartan elements

We record the explicit values of `exp (ad eᵢ)` and `exp (-ad fᵢ)` on `hⱼ` and `eᵢ`. -/

lemma expAdMap_eq_trunc {x : L8} (hloc : ∀ y : L8, ∃ n : ℕ, ((((LieAlgebra.ad ℂ L8 x)^n) y) = 0))
    {y : L8} {m : ℕ} (h : ((((LieAlgebra.ad ℂ L8 x)^m) y) = 0)) :
    Commons.Algebra.Lie.expAdMap x hloc y
      = Commons.Algebra.Lie.expAdTrunc (R := ℂ) x m y :=
  Commons.Algebra.Lie.expAdTrunc_eq_of_le (Commons.Algebra.Lie.ad_pow_expAdIndex x hloc y)
    (Commons.Algebra.Lie.expAdIndex_le x hloc h)

lemma expNegAdMap_eq_trunc {x : L8} (hloc : ∀ y : L8, ∃ n : ℕ, ((((LieAlgebra.ad ℂ L8 x)^n) y) = 0))
    {y : L8} {m : ℕ} (h : ((((LieAlgebra.ad ℂ L8 x)^m) y) = 0)) :
    Commons.Algebra.Lie.expNegAdMap x hloc y
      = Commons.Algebra.Lie.expNegAdTrunc (R := ℂ) x m y :=
  Commons.Algebra.Lie.expNegAdTrunc_eq_of_le (Commons.Algebra.Lie.ad_pow_expAdIndex x hloc y)
    (Commons.Algebra.Lie.expAdIndex_le x hloc h)

lemma expAdTrunc_two (x y : L8) :
    Commons.Algebra.Lie.expAdTrunc (R := ℂ) x 2 y = y + (LieAlgebra.ad ℂ L8 x) y := by
  rw [Commons.Algebra.Lie.expAdTrunc_apply]
  norm_num [Finset.sum_range_succ]

lemma expNegAdTrunc_two (x y : L8) :
    Commons.Algebra.Lie.expNegAdTrunc (R := ℂ) x 2 y = y - (LieAlgebra.ad ℂ L8 x) y := by
  rw [Commons.Algebra.Lie.expNegAdTrunc_apply]
  norm_num [Finset.sum_range_succ]
  rw [sub_eq_add_neg, ← lie_skew x y, neg_neg]

lemma expNegAdTrunc_three (x y : L8) :
    Commons.Algebra.Lie.expNegAdTrunc (R := ℂ) x 3 y
      = y - (LieAlgebra.ad ℂ L8 x) y + (2⁻¹ : ℂ) • ((LieAlgebra.ad ℂ L8 x)^2) y := by
  rw [Commons.Algebra.Lie.expNegAdTrunc_apply]
  norm_num [Finset.sum_range_succ]
  rw [sub_eq_add_neg, ← lie_skew x y, neg_neg]

/-- `(ad fᵢ)² eᵢ = -2 fᵢ`. -/
lemma ad_F_E_sq (i : Fin 8) :
    (((LieAlgebra.ad ℂ L8 (SerreF i))^2) (SerreE i)) = -(2 : ℂ) • SerreF i := by
  rw [pow_two, Module.End.mul_apply, ad_F_E, if_pos rfl, map_neg, ad_F_H, E8_diag]
  norm_num

/-- `exp (ad eᵢ)` sends `hⱼ` to `hⱼ - Aᵢⱼ eᵢ`. -/
lemma expAdMap_H (i j : Fin 8) :
    Commons.Algebra.Lie.expAdMap (SerreE i) (hloc_E i) (SerreH j)
      = SerreH j - (((E8 i j : ℤ) : ℂ)) • SerreE i := by
  rw [expAdMap_eq_trunc (hloc_E i) (ad_E_H_sq i j), expAdTrunc_two, ad_E_H, sub_eq_add_neg]

/-- `exp (ad eᵢ)` fixes `eᵢ`. -/
lemma expAdMap_E_self (i : Fin 8) :
    Commons.Algebra.Lie.expAdMap (SerreE i) (hloc_E i) (SerreE i) = SerreE i := by
  rw [expAdMap_eq_trunc (hloc_E i) (serreLie_adE_sq i i), expAdTrunc_two, LieAlgebra.ad_apply,
    lie_self, add_zero]

/-- `exp (ad eᵢ)` sends `hᵢ` to `hᵢ - 2 eᵢ`. -/
lemma expAdMap_H_self (i : Fin 8) :
    Commons.Algebra.Lie.expAdMap (SerreE i) (hloc_E i) (SerreH i)
      = SerreH i - (2 : ℂ) • SerreE i := by
  rw [expAdMap_eq_trunc (hloc_E i) (ad_E_H_sq i i), expAdTrunc_two, ad_E_H, E8_diag,
    sub_eq_add_neg]
  norm_num

/-- `exp (-ad fᵢ)` sends `hⱼ` to `hⱼ - Aᵢⱼ fᵢ`. -/
lemma expNegAdMap_H (i j : Fin 8) :
    Commons.Algebra.Lie.expNegAdMap (SerreF i) (hloc_F i) (SerreH j)
      = SerreH j - (((E8 i j : ℤ) : ℂ)) • SerreF i := by
  rw [expNegAdMap_eq_trunc (hloc_F i) (ad_F_H_sq i j), expNegAdTrunc_two, ad_F_H]

/-- `exp (-ad fᵢ)` sends `eᵢ` to `eᵢ + hᵢ - fᵢ`. -/
lemma expNegAdMap_E (i : Fin 8) :
    Commons.Algebra.Lie.expNegAdMap (SerreF i) (hloc_F i) (SerreE i)
      = SerreE i + SerreH i - SerreF i := by
  rw [expNegAdMap_eq_trunc (hloc_F i) (ad_F_E_cube i i), expNegAdTrunc_three, ad_F_E,
    if_pos rfl, ad_F_E_sq]
  simp only [sub_neg_eq_add]
  module

/-! ## The reflection automorphism `rᵢ = exp(ad eᵢ) exp(-ad fᵢ) exp(ad eᵢ)` -/

/-- The exponential of a locally nilpotent inner derivation, as a Lie algebra equivalence. -/
noncomputable def expAut (x : L8)
    (hloc : ∀ y : L8, ∃ n : ℕ, ((((LieAlgebra.ad ℂ L8 x)^n) y) = 0)) : L8 ≃ₗ⁅ℂ⁆ L8 :=
  LieEquiv.mk
    { toFun := Commons.Algebra.Lie.expAdMap x hloc
      map_add' := Commons.Algebra.Lie.expAdMap_add x hloc
      map_smul' := Commons.Algebra.Lie.expAdMap_smul x hloc
      map_lie' := fun {y z} => Commons.Algebra.Lie.expAdMap_lie x hloc y z }
    (Commons.Algebra.Lie.expNegAdMap x hloc)
    (Commons.Algebra.Lie.expNegAdMap_expAdMap x hloc)
    (Commons.Algebra.Lie.expAdMap_expNegAdMap x hloc)

@[simp] lemma expAut_apply (x : L8)
    (hloc : ∀ y : L8, ∃ n : ℕ, ((((LieAlgebra.ad ℂ L8 x)^n) y) = 0)) (y : L8) :
    expAut x hloc y = Commons.Algebra.Lie.expAdMap x hloc y := rfl

@[simp] lemma expAut_symm_apply (x : L8)
    (hloc : ∀ y : L8, ∃ n : ℕ, ((((LieAlgebra.ad ℂ L8 x)^n) y) = 0)) (y : L8) :
    (expAut x hloc).symm y = Commons.Algebra.Lie.expNegAdMap x hloc y := rfl

lemma expNegAdMap_add (x : L8)
    (hloc : ∀ y : L8, ∃ n : ℕ, ((((LieAlgebra.ad ℂ L8 x)^n) y) = 0)) (y z : L8) :
    Commons.Algebra.Lie.expNegAdMap x hloc (y + z)
      = Commons.Algebra.Lie.expNegAdMap x hloc y
        + Commons.Algebra.Lie.expNegAdMap x hloc z := by
  rw [← expAut_symm_apply x hloc, ← expAut_symm_apply x hloc, ← expAut_symm_apply x hloc,
    map_add]

lemma expNegAdMap_smul (x : L8)
    (hloc : ∀ y : L8, ∃ n : ℕ, ((((LieAlgebra.ad ℂ L8 x)^n) y) = 0)) (c : ℂ) (y : L8) :
    Commons.Algebra.Lie.expNegAdMap x hloc (c • y)
      = c • Commons.Algebra.Lie.expNegAdMap x hloc y := by
  rw [← expAut_symm_apply x hloc, ← expAut_symm_apply x hloc, map_smul]

lemma expNegAdMap_sub (x : L8)
    (hloc : ∀ y : L8, ∃ n : ℕ, ((((LieAlgebra.ad ℂ L8 x)^n) y) = 0)) (y z : L8) :
    Commons.Algebra.Lie.expNegAdMap x hloc (y - z)
      = Commons.Algebra.Lie.expNegAdMap x hloc y
        - Commons.Algebra.Lie.expNegAdMap x hloc z := by
  rw [sub_eq_add_neg, expNegAdMap_add,
    show -z = (-1 : ℂ) • z from (neg_one_smul ℂ z).symm, expNegAdMap_smul, neg_one_smul,
    sub_eq_add_neg]

lemma expAdMap_sub (x : L8)
    (hloc : ∀ y : L8, ∃ n : ℕ, ((((LieAlgebra.ad ℂ L8 x)^n) y) = 0)) (y z : L8) :
    Commons.Algebra.Lie.expAdMap x hloc (y - z)
      = Commons.Algebra.Lie.expAdMap x hloc y
        - Commons.Algebra.Lie.expAdMap x hloc z := by
  rw [sub_eq_add_neg, Commons.Algebra.Lie.expAdMap_add,
    show -z = (-1 : ℂ) • z from (neg_one_smul ℂ z).symm, Commons.Algebra.Lie.expAdMap_smul,
    neg_one_smul, sub_eq_add_neg]

/-- The reflection automorphism `rᵢ = exp(ad eᵢ) exp(-ad fᵢ) exp(ad eᵢ)`. -/
noncomputable def reflAut (i : Fin 8) : L8 ≃ₗ⁅ℂ⁆ L8 :=
  (expAut (SerreE i) (hloc_E i)).trans
    ((expAut (SerreF i) (hloc_F i)).symm.trans (expAut (SerreE i) (hloc_E i)))

@[simp] lemma reflAut_apply (i : Fin 8) (y : L8) :
    reflAut i y = Commons.Algebra.Lie.expAdMap (SerreE i) (hloc_E i)
      (Commons.Algebra.Lie.expNegAdMap (SerreF i) (hloc_F i)
        (Commons.Algebra.Lie.expAdMap (SerreE i) (hloc_E i) y)) := rfl

/-- **The reflection automorphism acts on the Cartan by the simple reflection.** -/
lemma reflAut_H (i j : Fin 8) :
    reflAut i (SerreH j) = SerreH j - (((E8 i j : ℤ) : ℂ)) • SerreH i := by
  have hA : Commons.Algebra.Lie.expNegAdMap (SerreF i) (hloc_F i)
        (SerreH j - (((E8 i j : ℤ) : ℂ)) • SerreE i)
      = SerreH j - (((E8 i j : ℤ) : ℂ)) • SerreE i
        - (((E8 i j : ℤ) : ℂ)) • SerreH i := by
    rw [expNegAdMap_sub, expNegAdMap_smul, expNegAdMap_H, expNegAdMap_E]
    module
  rw [reflAut_apply, expAdMap_H, hA]
  rw [expAdMap_sub, expAdMap_sub, expAdMap_smul, expAdMap_smul, expAdMap_H, expAdMap_E_self,
    expAdMap_H_self]
  module

/-! ## The induced action on weight spaces -/

/-- The simple reflection `sᵢ` acting on weights: `(sᵢ μ)ⱼ = μⱼ - μᵢ Aᵢⱼ`. -/
def sMu (i : Fin 8) (μ : Fin 8 → ℂ) : Fin 8 → ℂ :=
  fun j => μ j - μ i * (((E8 i j : ℤ) : ℂ))

/-- The simple reflection is an involution of the weight lattice. -/
lemma sMu_sMu (i : Fin 8) (μ : Fin 8 → ℂ) : sMu i (sMu i μ) = μ := by
  funext j
  simp only [sMu, E8_diag]
  ring

/-- **A Lie algebra automorphism which acts on the Cartan by the simple reflection maps weight
spaces to weight spaces.** -/
lemma maps_W (i : Fin 8) (Φ : L8 ≃ₗ⁅ℂ⁆ L8)
    (hΦ : ∀ j, Φ (SerreH j) = SerreH j - (((E8 i j : ℤ) : ℂ)) • SerreH i)
    {μ : Fin 8 → ℂ} {x : L8} (hx : x ∈ W μ) : Φ x ∈ W (sMu i μ) := by
  rw [mem_W_iff] at hx ⊢
  have key : ∀ j, ⁅SerreH j, Φ x⁆ - (((E8 i j : ℤ) : ℂ)) • ⁅SerreH i, Φ x⁆ = μ j • Φ x := by
    intro j
    have h1 : ⁅SerreH j, Φ x⁆ - (((E8 i j : ℤ) : ℂ)) • ⁅SerreH i, Φ x⁆
        = ⁅Φ (SerreH j), Φ x⁆ := by
      rw [hΦ j, sub_lie, smul_lie]
    have h2 : ⁅Φ (SerreH j), Φ x⁆ = Φ (⁅SerreH j, x⁆) :=
      (LieEquiv.map_lie Φ (SerreH j) x).symm
    rw [h1, h2, hx j, map_smul]
  have hii : ⁅SerreH i, Φ x⁆ = -μ i • Φ x := by
    have h := key i
    rw [E8_diag] at h
    have h2 : -⁅SerreH i, Φ x⁆ = μ i • Φ x := by
      rw [← h]; module
    simpa using (neg_eq_iff_eq_neg.mp h2)
  intro j
  have h := key j
  rw [hii] at h
  have h2 : ⁅SerreH j, Φ x⁆
      = μ j • Φ x + (((E8 i j : ℤ) : ℂ)) • (-μ i • Φ x) := by
    rw [← h]; abel
  rw [h2, sMu]
  module

/-- If `Φ` acts on the Cartan by the simple reflection then so does `Φ⁻¹`. -/
lemma inv_cartan (i : Fin 8) (Φ : L8 ≃ₗ⁅ℂ⁆ L8)
    (hΦ : ∀ j, Φ (SerreH j) = SerreH j - (((E8 i j : ℤ) : ℂ)) • SerreH i) :
    ∀ j, Φ.symm (SerreH j) = SerreH j - (((E8 i j : ℤ) : ℂ)) • SerreH i := by
  intro j
  have hz : Φ (SerreH j - (((E8 i j : ℤ) : ℂ)) • SerreH i) = SerreH j := by
    rw [map_sub, map_smul, hΦ j, hΦ i, E8_diag]
    module
  exact (congrArg Φ.symm hz).symm.trans (by simp)

/-- **The weight spaces in a Weyl-group orbit have the same dimension.** -/
lemma finrank_W_reflect (i : Fin 8) (μ : Fin 8 → ℂ) :
    Module.finrank ℂ ↥(W (sMu i μ)) = Module.finrank ℂ ↥(W μ) := by
  have hmap : Submodule.map (reflAut i).toLinearEquiv.toLinearMap (W μ) = W (sMu i μ) := by
    refine le_antisymm ?_ ?_
    · rintro y ⟨x, hx, rfl⟩
      exact maps_W i (reflAut i) (reflAut_H i) hx
    · intro y hy
      refine Submodule.mem_map.mpr ⟨(reflAut i).symm y, ?_, ?_⟩
      · have hmem := maps_W i ((reflAut i).symm) (inv_cartan i (reflAut i) (reflAut_H i)) hy
        rwa [sMu_sMu] at hmem
      · simp
  rw [← hmap]
  exact (LinearEquiv.finrank_eq (LinearEquiv.submoduleMap (reflAut i).toLinearEquiv (W μ))).symm

/-- Weight spaces of the Serre-constructed `e₈` in the same Weyl-group orbit have the same
dimension.

`μ : Fin 8 → ℤ` are the eigenvalues of `ad (H i)`, and the simple reflection `s_i` acts on weights
by `(sᵢ μ)ⱼ = μⱼ - μᵢ A i j`.  The automorphism `r_i = exp(ad e_i) exp(-ad f_i) exp(ad e_i)` of `g`
fixes the Cartan and acts on it by `s_i`; since `r_i` is linear, it maps the `μ`-weight space
*onto* the `s_i μ`-weight space, so the two have equal dimension.  (`exp(ad e_i)` is well defined
because `ad e_i` is locally nilpotent on `g`, which follows from the Serre relations and
`Commons.Algebra.Lie.ad_locallyNilpotent_of_generators`.) -/
theorem e8_weightSpace_reflect_finrank (i : Fin 8) (μ : Fin 8 → ℤ) :
    Module.finrank ℂ ↥(⨅ j : Fin 8, (LinearMap.ker (LieAlgebra.ad ℂ (LieAlgebra.e₈ ℂ)
      (LieSubmodule.Quotient.mk (N := CartanMatrix.Relations.toIdeal ℂ CartanMatrix.E₈)
        (FreeLieAlgebra.of ℂ (CartanMatrix.Generators.H j)))
        - ((fun l => μ l - μ i * CartanMatrix.E₈ i l) j : ℂ) • 1) :
        Submodule ℂ (LieAlgebra.e₈ ℂ)))
      = Module.finrank ℂ ↥(⨅ j : Fin 8, (LinearMap.ker (LieAlgebra.ad ℂ (LieAlgebra.e₈ ℂ)
      (LieSubmodule.Quotient.mk (N := CartanMatrix.Relations.toIdeal ℂ CartanMatrix.E₈)
        (FreeLieAlgebra.of ℂ (CartanMatrix.Generators.H j))) - (μ j : ℂ) • 1) :
        Submodule ℂ (LieAlgebra.e₈ ℂ))) := by
  have hν : (fun j : Fin 8 => ((fun l => μ l - μ i * CartanMatrix.E₈ i l) j : ℂ))
      = sMu i (fun j : Fin 8 => (μ j : ℂ)) := by
    funext j
    simp only [sMu]
    push_cast
    ring
  show Module.finrank ℂ
      ↥(W (fun j : Fin 8 => ((fun l => μ l - μ i * CartanMatrix.E₈ i l) j : ℂ)))
    = Module.finrank ℂ ↥(W (fun j : Fin 8 => (μ j : ℂ)))
  rw [hν]
  exact finrank_W_reflect i (fun j : Fin 8 => (μ j : ℂ))

end Commons.Algebra.Lie.SerreConstruction
