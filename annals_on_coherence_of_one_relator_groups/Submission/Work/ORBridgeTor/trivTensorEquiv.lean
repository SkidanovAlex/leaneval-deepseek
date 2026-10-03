/-
# `K ⊗[K] N ≅ N` for a left `K[G]`-module `N`

## Status (read this first)

The theorem `trivTensorEquiv` below assumes, besides the compatibility of the `K`- and
`K[G]`-actions requested by Jaikin-Zapirain--Linton Lemma 5.2(2) (`SMulCommClass`), also that the
`K`-module structure on `N` is the one induced by the `K[G]`-structure
(`IsScalarTower K (MonoidAlgebra K G) N`).  **This hypothesis is necessary**: without it there
need not be any `K[G]`-linear isomorphism `K ⊗[K] N ≅ N`, and the counterexample is
machine-checked at the end of this file (`Work.ORBridgeTor.NotIsScalarTower.not_equiv`): for
`K = ℂ`, `G = ℤ` and `N = ℂ × ℂ` carrying the `ℂ[G]`-structure `x • v = ρ x • v`, where
`ρ : ℂ[G] →+* ℂ` is the ring hom `∑ c_g g ↦ conj(∑ c_g χ(g))` with `χ : ℤ →* ℂ`, `χ(1) = I`, no
`ℂ[G]`-linear equivalence exists.  (Both structures satisfy `SMulCommClass K (MonoidAlgebra K G)
N`, so the extra hypothesis is genuinely needed.)

The proof is exactly the suggested proof: `TensorProduct.lid K N` upgraded to `K[G]`-linearity; for `map_smul'` one
inducts on the scalar `x : MonoidAlgebra K G` via `MonoidAlgebra.induction_on`; in the `of g`
case one inducts on the tensor with `TensorProduct.induction_on` and uses
`Work.ORHomAlg.JL52.diag_smul_single_tmul` and `SMulCommClass K (MonoidAlgebra K G) N`; the
K-scalar case (`x = c • r`) is precisely where `IsScalarTower K (MonoidAlgebra K G) N` is
needed (the `K[G]`-action on the tensor restricted to `K`-scalars is the `K`-module structure,
so `TensorProduct.lid` is already `K`-linear, but the same is not true on `N`).

Why `IsScalarTower` is necessary (formally, `Work.ORBridgeTor.NotIsScalarTower.key_g`,
`key_c`): if `e : K ⊗[K] N ≃ₗ[K[G]] N` is `K[G]`-linear, then `n ↦ e (1 ⊗ₜ n)` is an additive
bijection satisfying
* `e (1 ⊗ₜ[K] ((single g 1) • n)) = (single g 1) • e (1 ⊗ₜ[K] n)` for all `g : G`, `n : N`
  (the diagonal action acts on the first factor `K` trivially);
* `e ((c • 1) ⊗ₜ[K] n) = (c • 1) • e (1 ⊗ₜ[K] n)` for all `c : K`, `n : N`

(the first because two left `K[G]`-modules of the same underlying `K`-vector space and the
isomorphism must commute with the group action, the second because the `K`-scalars in `K[G]`
act on `K ⊗[K] N` by the `K`-module structure).  Taking `K = ℂ`, `G = ℤ`, `c = -I` and
`g = 1 ∈ ℤ` in a structure where `c` acts on `N` through the conjugation of `ℂ`, these two
conditions are contradictory.
-/
import Mathlib
import Submission.Work.ORBridgeTor.TrivMod
import Submission.Work.ORHomAlg.JL52.DiagTensorDefs

set_option linter.unnecessarySimpa false

namespace Work.ORBridgeTor

open TensorProduct MulOpposite

universe u

/-- **`K ⊗[K] N ≅ N`** for `N` a left `K[G]`-module whose `K`-module structure is the one
induced by the `K[G]`-action (`IsScalarTower K (MonoidAlgebra K G) N`), the tensor carrying the
diagonal `K[G]`-action of `Work.ORHomAlg.JL52.instDiagModule`.  This is the form of
`trivTensorEquiv` needed by the paper; without `IsScalarTower` the statement is false. -/
theorem trivTensorEquiv (K : Type u) [Field K] (G : Type u) [Group G]
    (N : Type u) [AddCommGroup N] [Module K N] [Module (MonoidAlgebra K G) N]
    [IsScalarTower K (MonoidAlgebra K G) N] [SMulCommClass K (MonoidAlgebra K G) N] :
    Nonempty (TensorProduct K K N ≃ₗ[MonoidAlgebra K G] N) := by
  -- The `SMul` on the tensor is `instDiagSMul` (priority 2000), not the one derived from the
  -- `Module` instance; the two are propositionally, but not syntactically, equal, so the
  -- distributivity/associativity of the diagonal action are recorded separately.
  have hsmul_add : ∀ (a : MonoidAlgebra K G) (b c : TensorProduct K K N),
      a • (b + c) = a • b + a • c := by
    intro a b c
    rw [Work.ORHomAlg.JL52.diag_smul_def, Work.ORHomAlg.JL52.diag_smul_def,
      Work.ORHomAlg.JL52.diag_smul_def, map_add]
  have hadd_smul : ∀ (a b : MonoidAlgebra K G) (c : TensorProduct K K N),
      (a + b) • c = a • c + b • c := by
    intro a b c
    rw [Work.ORHomAlg.JL52.diag_smul_def, Work.ORHomAlg.JL52.diag_smul_def,
      Work.ORHomAlg.JL52.diag_smul_def, map_add]
    rfl
  have hassoc : ∀ (c : K) (r : MonoidAlgebra K G) (z : TensorProduct K K N),
      (c • r) • z = c • (r • z) := by
    intro c r z
    rw [Work.ORHomAlg.JL52.diag_smul_def, Work.ORHomAlg.JL52.diag_smul_def,
      Work.ORHomAlg.JL52.diagRingHom_smul]
    rfl
  have hmain : ∀ (x : MonoidAlgebra K G) (z : TensorProduct K K N),
      TensorProduct.lid K N (x • z) = x • (TensorProduct.lid K N z) := by
    intro x
    induction x using MonoidAlgebra.induction_on with
    | of g =>
      intro z
      rw [MonoidAlgebra.of_apply]
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul k n =>
        rw [Work.ORHomAlg.JL52.diag_smul_single_tmul,
          Work.ORBridgeTor.instTrivLeftModule_single,
          TensorProduct.lid_tmul, TensorProduct.lid_tmul]
        exact smul_comm k (MonoidAlgebra.single g (1 : K)) n
      | add y y' hy hy' =>
        rw [hsmul_add, map_add]
        rw [show TensorProduct.lid K N (y + y')
            = TensorProduct.lid K N y + TensorProduct.lid K N y' from
          map_add (TensorProduct.lid K N) y y']
        rw [smul_add, hy, hy']
    | add x y hx hy =>
      intro z
      rw [hadd_smul, map_add, hx z, hy z]
      exact (add_smul x y (TensorProduct.lid K N z)).symm
    | smul c x hx =>
      intro z
      rw [hassoc c x z, map_smul, hx z]
      exact (IsScalarTower.smul_assoc c x (TensorProduct.lid K N z)).symm
  exact ⟨{ (TensorProduct.lid K N : TensorProduct K K N ≃ₗ[K] N) with
    map_smul' := fun x z => hmain x z }⟩

/-! ## The statement `trivTensorEquiv` is false

Here we build the counterexample.  The instances introduced in this section are `private`, so
they neither clash with nor are visible to anything else in the library. -/

namespace NotIsScalarTower

noncomputable section

/-- `ℤ` written multiplicatively, so that `MonoidAlgebra ℂ ℤ = ℂ[t^{±1}]`. -/
abbrev G : Type := Multiplicative ℤ

/-- The group hom `ℤ →* ℂ` sending the generator to `I`. -/
def chi : G →* ℂ where
  toFun g := Complex.I ^ (Multiplicative.toAdd g)
  map_one' := by simp
  map_mul' a b := by
    show Complex.I ^ (Multiplicative.toAdd a + Multiplicative.toAdd b)
      = Complex.I ^ (Multiplicative.toAdd a) * Complex.I ^ (Multiplicative.toAdd b)
    rw [zpow_add₀ Complex.I_ne_zero]

/-- The (unital, but non-`ℂ`-linear) ring hom `ℂ[G] →+* ℂ`, `∑ c_g g ↦ conj (∑ c_g χ g)`.
Its existence is exactly what violates `IsScalarTower K (MonoidAlgebra K G) N` below: the
`K`-scalars `c • 1` of the group algebra act on `N` through `conj`, not through `c`. -/
def rho : MonoidAlgebra ℂ G →+* ℂ :=
  (starRingEnd ℂ).comp (MonoidAlgebra.lift ℂ ℂ G chi).toRingHom

theorem rho_single (g : G) (c : ℂ) : rho (MonoidAlgebra.single g c) = star (c * chi g) := by
  simp [rho, MonoidAlgebra.lift_single]

theorem rho_smul_one (c : ℂ) : rho (c • (1 : MonoidAlgebra ℂ G)) = star c := by
  rw [show c • (1 : MonoidAlgebra ℂ G) = MonoidAlgebra.single (1 : G) c from by
    rw [show (1 : MonoidAlgebra ℂ G) = MonoidAlgebra.single (1 : G) 1 from rfl,
      MonoidAlgebra.smul_single, smul_eq_mul, mul_one]]
  rw [rho_single, map_one, mul_one]

theorem chi_gen : chi (Multiplicative.ofAdd (1 : ℤ)) = Complex.I := by
  show Complex.I ^ Multiplicative.toAdd (Multiplicative.ofAdd (1 : ℤ)) = Complex.I
  rw [show Multiplicative.toAdd (Multiplicative.ofAdd (1 : ℤ)) = (1 : ℤ) from rfl, zpow_one]

/-- The generator acts on `N := ℂ × ℂ` by `-I`. -/
theorem rho_gen : rho (MonoidAlgebra.single (Multiplicative.ofAdd (1 : ℤ)) (1 : ℂ))
    = - Complex.I := by
  rw [rho_single, chi_gen]
  simp [Complex.conj_I]

/-- The twisted `SMul` on `ℂ × ℂ`: `x • v = rho x • v`. -/
private instance (priority := 2000) twistedSMul : SMul (MonoidAlgebra ℂ G) (ℂ × ℂ) :=
  ⟨fun x v => rho x • v⟩

/-- The twisted `ℂ[G]`-module structure on `ℂ × ℂ`. -/
private instance (priority := 2000) twistedModule : Module (MonoidAlgebra ℂ G) (ℂ × ℂ) where
  smul := (twistedSMul).smul
  one_smul v := by show rho 1 • v = v; rw [map_one, one_smul]
  mul_smul x y v := by show rho (x * y) • v = rho x • (rho y • v); rw [map_mul, mul_smul]
  smul_zero x := by show rho x • (0 : ℂ × ℂ) = 0; rw [smul_zero]
  smul_add x v w := by
    show rho x • (v + w) = rho x • v + rho x • w
    rw [smul_add]
  add_smul x y v := by
    show rho (x + y) • v = rho x • v + rho y • v
    rw [map_add, add_smul]
  zero_smul v := by show rho 0 • v = 0; rw [map_zero, zero_smul]

private instance twistedSMulCommClass : SMulCommClass ℂ (MonoidAlgebra ℂ G) (ℂ × ℂ) where
  smul_comm c x v := by
    show c • (rho x • v) = rho x • (c • v)
    exact smul_comm c (rho x) v

theorem twisted_smul_eq (x : MonoidAlgebra ℂ G) (v : ℂ × ℂ) : x • v = rho x • v := rfl

theorem twisted_smul_apply (x : MonoidAlgebra ℂ G) (a b : ℂ) :
    x • (a, b) = (rho x * a, rho x * b) := by
  rw [twisted_smul_eq]
  show rho x • ((a, b) : ℂ × ℂ) = _
  simp [Prod.smul_mk]

/-- The `K`-scalars of `K[G]` act on `K ⊗[K] N` by the `K`-module structure of the tensor. -/
theorem diag_smul_one_smul (c : ℂ) (z : TensorProduct ℂ ℂ (ℂ × ℂ)) :
    (c • (1 : MonoidAlgebra ℂ G)) • z = c • z := by
  rw [Work.ORHomAlg.JL52.diag_smul_def, Work.ORHomAlg.JL52.diagRingHom_smul]
  simp

/-- First necessary condition: any `ℂ[G]`-linear map commutes with the group action. -/
theorem key_g (e : TensorProduct ℂ ℂ (ℂ × ℂ) ≃ₗ[MonoidAlgebra ℂ G] (ℂ × ℂ)) (g : G)
    (n : ℂ × ℂ) :
    e ((1 : ℂ) ⊗ₜ[ℂ] ((MonoidAlgebra.single g (1 : ℂ)) • n))
      = (MonoidAlgebra.single g (1 : ℂ)) • e ((1 : ℂ) ⊗ₜ[ℂ] n) := by
  have h : (1 : ℂ) ⊗ₜ[ℂ] ((MonoidAlgebra.single g (1 : ℂ)) • n)
      = (MonoidAlgebra.single g (1 : ℂ)) • ((1 : ℂ) ⊗ₜ[ℂ] n) := by
    rw [Work.ORHomAlg.JL52.diag_smul_single_tmul, Work.ORBridgeTor.instTrivLeftModule_single]
  rw [h, e.map_smul]

/-- Second necessary condition: any `ℂ[G]`-linear map is equivariant for the `ℂ`-scalars of
`ℂ[G]`, i.e. it intertwines `c • -` on the tensor with the action of the element `c • 1` of
`ℂ[G]` on `N` (which is the conjugation of `c`, see `rho_smul_one`). -/
theorem key_c (e : TensorProduct ℂ ℂ (ℂ × ℂ) ≃ₗ[MonoidAlgebra ℂ G] (ℂ × ℂ)) (c : ℂ)
    (n : ℂ × ℂ) :
    e ((c • (1 : ℂ)) ⊗ₜ[ℂ] n) = (c • (1 : MonoidAlgebra ℂ G)) • e ((1 : ℂ) ⊗ₜ[ℂ] n) := by
  have h : (c • (1 : ℂ)) ⊗ₜ[ℂ] n = (c • (1 : MonoidAlgebra ℂ G)) • ((1 : ℂ) ⊗ₜ[ℂ] n) := by
    rw [diag_smul_one_smul, TensorProduct.smul_tmul']
  rw [h, e.map_smul]

theorem gen_smul_one :
    (MonoidAlgebra.single (Multiplicative.ofAdd (1 : ℤ)) (1 : ℂ)) • ((1 : ℂ), (1 : ℂ))
      = (-Complex.I, -Complex.I) := by
  rw [twisted_smul_apply, rho_gen]
  ext <;> simp

/-- **The counterexample.**  With `K = ℂ`, `G = ℤ` and `N = ℂ × ℂ` carrying the `ℂ[G]`-structure
`x • v = ρ x • v`, there is no `ℂ[G]`-linear equivalence `ℂ ⊗[ℂ] N ≅ N`.  Hence
`Work.ORBridgeTor.trivTensorEquiv` is false as stated. -/
theorem not_equiv : ¬ Nonempty (TensorProduct ℂ ℂ (ℂ × ℂ) ≃ₗ[MonoidAlgebra ℂ G] (ℂ × ℂ)) := by
  rintro ⟨e⟩
  -- `key_g` with `g = 1` says that `e ∘ (1 ⊗ -)` commutes with `-I`, while `key_c` with
  -- `c = -I` says that it conjugates `-I` to `I`.  Contradiction.
  have hL1 : e ((1 : ℂ) ⊗ₜ[ℂ] ((-Complex.I : ℂ), (-Complex.I : ℂ)))
      = (-Complex.I : ℂ) • e ((1 : ℂ) ⊗ₜ[ℂ] ((1 : ℂ), (1 : ℂ))) := by
    have h := key_g e (Multiplicative.ofAdd (1 : ℤ)) ((1 : ℂ), (1 : ℂ))
    rw [gen_smul_one] at h
    rw [twisted_smul_eq, rho_gen] at h
    exact h
  have hL2 : e (((-Complex.I : ℂ)) ⊗ₜ[ℂ] ((1 : ℂ), (1 : ℂ)))
      = (Complex.I : ℂ) • e ((1 : ℂ) ⊗ₜ[ℂ] ((1 : ℂ), (1 : ℂ))) := by
    have h := key_c e (-Complex.I) ((1 : ℂ), (1 : ℂ))
    rw [show ((-Complex.I : ℂ) • (1 : ℂ)) = (-Complex.I : ℂ) from by simp] at h
    rw [twisted_smul_eq, rho_smul_one] at h
    rw [show star (-Complex.I) = Complex.I from by simp [Complex.conj_I]] at h
    exact h
  have hEq : (((-Complex.I : ℂ)) ⊗ₜ[ℂ] ((1 : ℂ), (1 : ℂ)))
      = ((1 : ℂ) ⊗ₜ[ℂ] ((-Complex.I : ℂ), (-Complex.I : ℂ))) := by
    rw [show (((-Complex.I : ℂ)) ⊗ₜ[ℂ] ((1 : ℂ), (1 : ℂ)))
        = (((-Complex.I : ℂ) • (1 : ℂ)) ⊗ₜ[ℂ] ((1 : ℂ), (1 : ℂ))) from by simp]
    rw [TensorProduct.smul_tmul]
    congr 1
    ext <;> simp
  have hfin : (-Complex.I : ℂ) • e ((1 : ℂ) ⊗ₜ[ℂ] ((1 : ℂ), (1 : ℂ)))
      = (Complex.I : ℂ) • e ((1 : ℂ) ⊗ₜ[ℂ] ((1 : ℂ), (1 : ℂ))) := by
    rw [← hL1, ← hEq, hL2]
  have hy : e ((1 : ℂ) ⊗ₜ[ℂ] ((1 : ℂ), (1 : ℂ))) = 0 := by
    have hfst := congrArg (fun z : ℂ × ℂ => z.1) hfin
    have hsnd := congrArg (fun z : ℂ × ℂ => z.2) hfin
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hfst hsnd
    have key : ∀ w : ℂ, (-Complex.I : ℂ) * w = Complex.I * w → w = 0 := by
      intro w hw
      have h3 : ((-Complex.I : ℂ) - Complex.I) * w = 0 := by rw [sub_mul, hw, sub_self]
      have h4 : ((-Complex.I : ℂ) - Complex.I) = -(2 * Complex.I) := by ring
      rw [h4] at h3
      have h5 : ((-(2 * Complex.I)) : ℂ) ≠ 0 :=
        neg_ne_zero.mpr (mul_ne_zero two_ne_zero Complex.I_ne_zero)
      exact (mul_eq_zero.mp h3).resolve_left h5
    exact Prod.ext (key _ hfst) (key _ hsnd)
  have hx : ((1 : ℂ) ⊗ₜ[ℂ] ((1 : ℂ), (1 : ℂ))) ≠ 0 := by
    intro hzero
    have h := congrArg (TensorProduct.lid ℂ (ℂ × ℂ)) hzero
    rw [TensorProduct.lid_tmul, map_zero] at h
    simpa using h
  exact hx (e.injective (by rw [hy, map_zero]))

end

end NotIsScalarTower

end Work.ORBridgeTor
