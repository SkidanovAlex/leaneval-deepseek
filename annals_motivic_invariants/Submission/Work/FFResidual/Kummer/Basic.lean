/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.
Authors: Work.FFResidual
-/
import Submission.Work.FFResidual.Ord

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The Kummer extension of a function field at a place

Let `P : FunctionFieldPlace 𝔽 𝕜` be a place of a function field `𝕜` over its field of constants
`𝔽`, with uniformizer `π` (`P.ord_uniformizer`).  This file sets up the **Kummer extension**

  `Top P = 𝕜(s)`,  `s ^ 5 = π`

of `𝕜` (`π` is not a fifth power, `P.not_exists_pow_five_uniformizer`, and `𝔽` — hence `𝕜` —
contains a primitive fifth root of unity `ζ`), the concrete model `AdjoinRoot (X ^ 5 - C π)` of the
top field (with its root `P.kummerRoot`), and the **Kummer automorphism** `P.kummerEquiv`, the
generator `s ↦ ζ s` of the cyclic Galois group of `Top P / 𝕜`.

## Main definitions and results

* `FunctionFieldPlace.kummerPoly`, `kummerPoly_irreducible` — the defining polynomial.
* `FunctionFieldPlace.Top`, `kummerRoot`, `kummerRoot_pow_five` — the top field and the root.
* `FunctionFieldPlace.zetaK`, `zetaK_isPrimitiveRoot` — the fifth root of unity in `𝕜`.
* `FunctionFieldPlace.kummerHom` — the `𝕜`-algebra endomorphism `s ↦ ζ s`; `kummerEquiv` — the same
  as an automorphism, with `kummerEquiv_root : kummerEquiv s = ζ • s`.
* `FunctionFieldPlace.kummerCyclicExtension` — `Top P` as a `CyclicExtension 𝕜 5` with generator
  `kummerEquiv`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false


namespace Work.FFResidual

noncomputable section

open Polynomial

namespace FunctionFieldPlace

variable {𝔽 : Type} [Field 𝔽] {𝕜 : Type} [Field 𝕜] [Algebra 𝔽 𝕜]

/-! ## 1. The top field `𝕜(s)`, `s ^ 5 = π` -/

/-- The Kummer element: the uniformizer of the place, viewed in the function field. -/
abbrev kummerElement (P : FunctionFieldPlace 𝔽 𝕜) : 𝕜 := algebraMap P.R 𝕜 P.π

/-- The defining polynomial `X ^ 5 - π` of the Kummer extension of the function field at the
place. -/
abbrev kummerPoly (P : FunctionFieldPlace 𝔽 𝕜) : 𝕜[X] := X ^ 5 - C P.kummerElement

theorem kummerPoly_ne_zero (P : FunctionFieldPlace 𝔽 𝕜) : P.kummerPoly ≠ 0 :=
  X_pow_sub_C_ne_zero (by norm_num) _

theorem kummerPoly_monic (P : FunctionFieldPlace 𝔽 𝕜) : P.kummerPoly.Monic :=
  monic_X_pow_sub_C _ (by norm_num)

theorem kummerPoly_irreducible (P : FunctionFieldPlace 𝔽 𝕜) : Irreducible P.kummerPoly := by
  rw [kummerPoly, X_pow_sub_C_irreducible_iff_forall_prime_of_odd (n := 5) (by norm_num)]
  intro p hp hpdvd b hb
  have hp5 : p = 5 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hpdvd
  subst hp5
  exact P.not_exists_pow_five_uniformizer ⟨b, by rw [hb, kummerElement]⟩

instance kummerPoly_fact (P : FunctionFieldPlace 𝔽 𝕜) : Fact (Irreducible P.kummerPoly) :=
  ⟨P.kummerPoly_irreducible⟩

/-- **The top field of the function-field classes**: `𝕜(s)` with `s ^ 5 = π`, the Kummer extension
of the function field at the place. -/
abbrev Top (P : FunctionFieldPlace 𝔽 𝕜) : Type := AdjoinRoot P.kummerPoly

/-- **The Kummer root** `s`, with `s ^ 5 = π`. -/
abbrev kummerRoot (P : FunctionFieldPlace 𝔽 𝕜) : P.Top := AdjoinRoot.root P.kummerPoly

theorem kummerRoot_pow_five (P : FunctionFieldPlace 𝔽 𝕜) :
    P.kummerRoot ^ 5 = algebraMap 𝕜 P.Top P.kummerElement := by
  have h := AdjoinRoot.eval₂_root P.kummerPoly
  simp only [kummerPoly, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C] at h
  rw [sub_eq_zero] at h
  rw [h, AdjoinRoot.algebraMap_eq]

theorem kummerRoot_ne_zero (P : FunctionFieldPlace 𝔽 𝕜) : P.kummerRoot ≠ 0 := by
  intro h
  have h5 : algebraMap 𝕜 P.Top P.kummerElement = 0 := by
    rw [← P.kummerRoot_pow_five, h, zero_pow (by norm_num : (5 : ℕ) ≠ 0)]
  have h6 : P.kummerElement = 0 := (algebraMap 𝕜 P.Top).injective (by simpa using h5)
  exact P.pi_ne_zero (IsFractionRing.injective P.R 𝕜 (by simpa using h6))

/-! ## 2. The Kummer automorphism `s ↦ ζ s` -/

/-- The fifth root of unity of the constants, viewed in the function field. -/
abbrev zetaK (ζ : 𝔽) : 𝕜 := algebraMap 𝔽 𝕜 ζ

theorem zetaK_isPrimitiveRoot (ζ : 𝔽) (hζ : IsPrimitiveRoot ζ 5) :
    IsPrimitiveRoot (zetaK (𝕜 := 𝕜) ζ) 5 :=
  hζ.map_of_injective (algebraMap 𝔽 𝕜).injective

theorem zetaK_ne_one (ζ : 𝔽) (hζ : IsPrimitiveRoot ζ 5) : zetaK (𝕜 := 𝕜) ζ ≠ 1 :=
  (zetaK_isPrimitiveRoot ζ hζ).ne_one (by norm_num)

theorem zetaK_pow_five (ζ : 𝔽) (hζ : IsPrimitiveRoot ζ 5) : (zetaK (𝕜 := 𝕜) ζ) ^ 5 = 1 :=
  (zetaK_isPrimitiveRoot ζ hζ).pow_eq_one

theorem primitiveRoots_nonempty (ζ : 𝔽) (hζ : IsPrimitiveRoot ζ 5) :
    (primitiveRoots 5 𝕜).Nonempty :=
  ⟨zetaK (𝕜 := 𝕜) ζ,
    (mem_primitiveRoots (by norm_num : (0 : ℕ) < 5)).mpr (zetaK_isPrimitiveRoot ζ hζ)⟩

theorem zetaK_smul_root_pow_five (P : FunctionFieldPlace 𝔽 𝕜) (ζ : 𝔽)
    (hζ : IsPrimitiveRoot ζ 5) :
    (zetaK (𝕜 := 𝕜) ζ • P.kummerRoot) ^ 5 = algebraMap 𝕜 P.Top P.kummerElement := by
  rw [Algebra.smul_def, mul_pow, ← map_pow, zetaK_pow_five ζ hζ, map_one, one_mul,
    P.kummerRoot_pow_five]

theorem kummerPoly_eval_zetaK (P : FunctionFieldPlace 𝔽 𝕜) (ζ : 𝔽)
    (hζ : IsPrimitiveRoot ζ 5) :
    eval₂ (algebraMap 𝕜 P.Top) (zetaK (𝕜 := 𝕜) ζ • P.kummerRoot) P.kummerPoly = 0 := by
  simp only [kummerPoly, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero]
  exact P.zetaK_smul_root_pow_five ζ hζ

/-- **The Kummer endomorphism** `s ↦ ζ s` of the top field, as a `𝕜`-algebra endomorphism. -/
noncomputable def kummerHom (P : FunctionFieldPlace 𝔽 𝕜) (ζ : 𝔽)
    (hζ : IsPrimitiveRoot ζ 5) : P.Top →ₐ[𝕜] P.Top :=
  AdjoinRoot.liftAlgHom P.kummerPoly (Algebra.ofId 𝕜 P.Top) (zetaK (𝕜 := 𝕜) ζ • P.kummerRoot)
    (P.kummerPoly_eval_zetaK ζ hζ)

theorem kummerHom_root (P : FunctionFieldPlace 𝔽 𝕜) (ζ : 𝔽) (hζ : IsPrimitiveRoot ζ 5) :
    P.kummerHom ζ hζ P.kummerRoot = zetaK (𝕜 := 𝕜) ζ • P.kummerRoot :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

theorem kummerHom_algebraMap (P : FunctionFieldPlace 𝔽 𝕜) (ζ : 𝔽)
    (hζ : IsPrimitiveRoot ζ 5) (c : 𝕜) :
    P.kummerHom ζ hζ (algebraMap 𝕜 P.Top c) = algebraMap 𝕜 P.Top c := by
  rw [AdjoinRoot.algebraMap_eq]
  exact AdjoinRoot.liftAlgHom_of _ _ _ _ c

theorem kummerHom_injective (P : FunctionFieldPlace 𝔽 𝕜) (ζ : 𝔽)
    (hζ : IsPrimitiveRoot ζ 5) : Function.Injective (P.kummerHom ζ hζ) := by
  intro x y hxy
  have h : P.kummerHom ζ hζ (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  by_contra hne
  have hx : x - y ≠ 0 := sub_ne_zero.mpr hne
  have hinv := congrArg (P.kummerHom ζ hζ) (inv_mul_cancel₀ hx)
  rw [map_mul, map_one] at hinv
  rw [h, mul_zero] at hinv
  exact one_ne_zero hinv.symm

theorem isSplittingField_kummerPoly (P : FunctionFieldPlace 𝔽 𝕜) (ζ : 𝔽)
    (hζ : IsPrimitiveRoot ζ 5) : IsSplittingField 𝕜 P.Top P.kummerPoly :=
  isSplittingField_AdjoinRoot_X_pow_sub_C (primitiveRoots_nonempty ζ hζ)
    P.kummerPoly_irreducible


theorem finrank_Top (P : FunctionFieldPlace 𝔽 𝕜) (ζ : 𝔽) (hζ : IsPrimitiveRoot ζ 5) :
    Module.finrank 𝕜 P.Top = 5 := by
  haveI := P.isSplittingField_kummerPoly ζ hζ
  exact finrank_of_isSplittingField_X_pow_sub_C (primitiveRoots_nonempty ζ hζ)
    P.kummerPoly_irreducible P.Top

theorem isGalois_Top (P : FunctionFieldPlace 𝔽 𝕜) (ζ : 𝔽) (hζ : IsPrimitiveRoot ζ 5) :
    IsGalois 𝕜 P.Top := by
  haveI := P.isSplittingField_kummerPoly ζ hζ
  exact isGalois_of_isSplittingField_X_pow_sub_C (primitiveRoots_nonempty ζ hζ)
    P.kummerPoly_irreducible P.Top

theorem kummerHom_surjective (P : FunctionFieldPlace 𝔽 𝕜) (ζ : 𝔽)
    (hζ : IsPrimitiveRoot ζ 5) : Function.Surjective (P.kummerHom ζ hζ) := by
  haveI hsplit := P.isSplittingField_kummerPoly ζ hζ
  haveI : FiniteDimensional 𝕜 P.Top := IsSplittingField.finiteDimensional (L := P.Top) P.kummerPoly
  exact (LinearMap.injective_iff_surjective
    (f := (P.kummerHom ζ hζ).toLinearMap)).mp (P.kummerHom_injective ζ hζ)

/-- **The Kummer automorphism** `s ↦ ζ s` of the top field: the generator of the cyclic Galois
group of `Top P / 𝕜`. -/
noncomputable def kummerEquiv (P : FunctionFieldPlace 𝔽 𝕜) (ζ : 𝔽)
    (hζ : IsPrimitiveRoot ζ 5) : P.Top ≃ₐ[𝕜] P.Top :=
  AlgEquiv.ofBijective _ ⟨P.kummerHom_injective ζ hζ, P.kummerHom_surjective ζ hζ⟩

theorem kummerEquiv_root (P : FunctionFieldPlace 𝔽 𝕜) (ζ : 𝔽) (hζ : IsPrimitiveRoot ζ 5) :
    P.kummerEquiv ζ hζ P.kummerRoot = zetaK (𝕜 := 𝕜) ζ • P.kummerRoot :=
  P.kummerHom_root ζ hζ

theorem kummerEquiv_algebraMap (P : FunctionFieldPlace 𝔽 𝕜) (ζ : 𝔽)
    (hζ : IsPrimitiveRoot ζ 5) (c : 𝕜) :
    P.kummerEquiv ζ hζ (algebraMap 𝕜 P.Top c) = algebraMap 𝕜 P.Top c :=
  P.kummerHom_algebraMap ζ hζ c

theorem kummerEquiv_pow_apply_root (P : FunctionFieldPlace 𝔽 𝕜) (ζ : 𝔽)
    (hζ : IsPrimitiveRoot ζ 5) (n : ℕ) :
    (P.kummerEquiv ζ hζ ^ n) P.kummerRoot = (zetaK (𝕜 := 𝕜) ζ) ^ n • P.kummerRoot := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', AlgEquiv.mul_apply, ih, map_smul, kummerEquiv_root, smul_smul, ← pow_succ]

theorem kummerEquiv_pow_algebraMap (P : FunctionFieldPlace 𝔽 𝕜) (ζ : 𝔽)
    (hζ : IsPrimitiveRoot ζ 5) (n : ℕ) (c : 𝕜) :
    (P.kummerEquiv ζ hζ ^ n) (algebraMap 𝕜 P.Top c) = algebraMap 𝕜 P.Top c := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', AlgEquiv.mul_apply, ih, kummerEquiv_algebraMap]

theorem kummerEquiv_pow_five (P : FunctionFieldPlace 𝔽 𝕜) (ζ : 𝔽) (hζ : IsPrimitiveRoot ζ 5) :
    P.kummerEquiv ζ hζ ^ 5 = 1 := by
  refine AlgEquiv.coe_toAlgHom_injective ?_
  refine AdjoinRoot.algHom_ext ?_
  rw [AlgEquiv.coe_toAlgHom, P.kummerEquiv_pow_apply_root ζ hζ, zetaK_pow_five ζ hζ, one_smul]
  rfl

theorem kummerEquiv_ne_one (P : FunctionFieldPlace 𝔽 𝕜) (ζ : 𝔽) (hζ : IsPrimitiveRoot ζ 5) :
    P.kummerEquiv ζ hζ ≠ 1 := by
  intro h
  have h1 : P.kummerEquiv ζ hζ P.kummerRoot = P.kummerRoot := by rw [h, AlgEquiv.one_apply]
  rw [kummerEquiv_root] at h1
  have h2 : (zetaK (𝕜 := 𝕜) ζ - 1) • P.kummerRoot = 0 := by
    rw [sub_smul, one_smul, h1, sub_self]
  rcases smul_eq_zero.mp h2 with h3 | h3
  · exact zetaK_ne_one ζ hζ (sub_eq_zero.mp h3)
  · exact P.kummerRoot_ne_zero h3

theorem orderOf_kummerEquiv (P : FunctionFieldPlace 𝔽 𝕜) (ζ : 𝔽)
    (hζ : IsPrimitiveRoot ζ 5) : orderOf (P.kummerEquiv ζ hζ) = 5 :=
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  orderOf_eq_prime (P.kummerEquiv_pow_five ζ hζ) (P.kummerEquiv_ne_one ζ hζ)

/-- **The top field as a cyclic quintic extension of `𝕜`**, with generator the Kummer
automorphism `s ↦ ζ s`: the extension `L/𝕜` of the function-field classes (b), (c), (d). -/
noncomputable def kummerCyclicExtension (P : FunctionFieldPlace 𝔽 𝕜) (ζ : 𝔽)
    (hζ : IsPrimitiveRoot ζ 5) : Work.TorsorExistence.CyclicExtension 𝕜 5 := by
  haveI hsplit := P.isSplittingField_kummerPoly ζ hζ
  haveI : FiniteDimensional 𝕜 P.Top := IsSplittingField.finiteDimensional (L := P.Top) P.kummerPoly
  haveI hgal := P.isGalois_Top ζ hζ
  haveI : Fintype (P.Top ≃ₐ[𝕜] P.Top) := AlgEquiv.fintype 𝕜 P.Top
  have htop : Subgroup.zpowers (P.kummerEquiv ζ hζ) = ⊤ := by
    refine Subgroup.eq_top_of_card_eq _ ?_
    rw [Nat.card_zpowers, P.orderOf_kummerEquiv ζ hζ,
      IsGalois.card_aut_eq_finrank 𝕜 P.Top, P.finrank_Top ζ hζ]
  refine { L := P.Top
           finrank_eq := P.finrank_Top ζ hζ
           gen := P.kummerEquiv ζ hζ
           orderOf_gen := P.orderOf_kummerEquiv ζ hζ
           gen_generator := ?_ }
  intro g
  have hmem : g ∈ Submonoid.powers (P.kummerEquiv ζ hζ) :=
    (isOfFinOrder_of_finite (P.kummerEquiv ζ hζ)).mem_powers_iff_mem_zpowers.mpr
      (htop ▸ Subgroup.mem_top g)
  obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff g _).mp hmem
  exact ⟨k, hk.symm⟩

theorem kummerCyclicExtension_gen (P : FunctionFieldPlace 𝔽 𝕜) (ζ : 𝔽)
    (hζ : IsPrimitiveRoot ζ 5) :
    (P.kummerCyclicExtension ζ hζ).gen = P.kummerEquiv ζ hζ := rfl

end FunctionFieldPlace

end

end Work.FFResidual
