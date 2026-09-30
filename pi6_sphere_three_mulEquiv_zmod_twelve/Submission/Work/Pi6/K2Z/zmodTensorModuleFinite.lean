import Mathlib
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# Finite generation is preserved by extension of scalars

If `M` is a finitely generated `R`-module and `f : R →+* S` is a ring homomorphism of commutative
rings, then `S ⊗[R] M` (i.e. `(ModuleCat.extendScalars f).obj M`) is a finitely generated
`S`-module.

Concretely: if `s : Fin n → M` generates `M` over `R`, then `{1 ⊗ s i : Fin n}` generates
`S ⊗[R] M` over `S`, because
* every element of the tensor is an `S`-linear combination of pure tensors `c ⊗ m`, and
  `c ⊗ m = c • (1 ⊗ m)` (`ModuleCat.ExtendScalars.smul_tmul`);
* `1 ⊗ m` is a `ℤ`-linear (hence, via the scalar tower `k • z = f k • z`, an `S`-linear)
  combination of the `1 ⊗ s i` as soon as `m` is an `R`-combination of the `s i`.

The whole argument is by induction on the tensor product and on the `R`-span, and uses the
`ExtendScalars` API together with the left module structure on the tensor product.

A remark on the formalisation: the `R`-module structure carried by the left factor
`S ⊗[R] M` is `Module.compHom` (coming from `ModuleCat.restrictScalars`), which is only
propositionally equal to the "canonical" `R`-module structure on `S`; the local instances
introduced below (`DistribMulAction R`, obtained from `TensorProduct.leftDistribMulAction`) and the
`set_option backward.isDefEq.respectTransparency false` (as in Mathlib's own `ChangeOfRings` file)
are what make these structures line up.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open scoped TensorProduct ChangeOfRings

namespace Work.Pi6.K2Z

/-- Extension of scalars along a ring homomorphism of commutative rings preserves finite
generation of modules. -/
theorem extendScalars_moduleFinite {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (M : ModuleCat R) [Module.Finite R M] :
    Module.Finite S ↥((ModuleCat.extendScalars f).obj M) := by
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := M)
  -- The left (i.e. `R`-)action on `S ⊗[R] M`.
  letI : DistribMulAction R ↥((ModuleCat.extendScalars f).obj M) :=
    TensorProduct.leftDistribMulAction
  -- `R`-multiplication agrees with `S`-multiplication through `f`.
  have tower : ∀ (k : R) (z : ↥((ModuleCat.extendScalars f).obj M)), k • z = f k • z := by
    intro k z
    induction z using TensorProduct.inductionOn with
    | tmul c m =>
      rw [TensorProduct.smul_tmul', ModuleCat.ExtendScalars.smul_tmul]
      simp [smul_eq_mul]
    | add x y hx hy => rw [smul_add, smul_add, hx, hy]
  rw [Module.finite_def]
  refine (Submodule.fg_iff_exists_fin_generating_family).mpr
    ⟨n, fun i : Fin n => ((1 : S) ⊗ₜ[R,f] s i : ↥((ModuleCat.extendScalars f).obj M)), ?_⟩
  -- `1 ⊗ m` lies in the `S`-span of the `1 ⊗ s i` whenever `m` is an `R`-combination of the `s i`.
  have key : ∀ m : M, ((1 : S) ⊗ₜ[R,f] m : ↥((ModuleCat.extendScalars f).obj M)) ∈
      Submodule.span S (Set.range fun i : Fin n =>
        ((1 : S) ⊗ₜ[R,f] s i : ↥((ModuleCat.extendScalars f).obj M))) := by
    intro m
    have hm : m ∈ Submodule.span R (Set.range s) := by rw [hs]; trivial
    induction hm using Submodule.span_induction with
    | mem y hy => obtain ⟨i, rfl⟩ := hy; exact Submodule.subset_span ⟨i, rfl⟩
    | zero => rw [TensorProduct.tmul_zero]; exact Submodule.zero_mem _
    | add y z hy hz ihy ihz => rw [TensorProduct.tmul_add]; exact Submodule.add_mem _ ihy ihz
    | smul k y hy ihy =>
      have h1 : ((1 : S) ⊗ₜ[R,f] (k • y) : ↥((ModuleCat.extendScalars f).obj M)) =
          k • ((1 : S) ⊗ₜ[R,f] y : ↥((ModuleCat.extendScalars f).obj M)) := by
        rw [← TensorProduct.tmul_smul]
      rw [h1, tower k ((1 : S) ⊗ₜ[R,f] y : ↥((ModuleCat.extendScalars f).obj M))]
      exact Submodule.smul_mem _ (f k) ihy
  -- Every element of the tensor is an `S`-combination of the `1 ⊗ s i`.
  rw [Submodule.eq_top_iff']
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul c m =>
    let c' : S := c
    have hc : (c ⊗ₜ[R,f] m : ↥((ModuleCat.extendScalars f).obj M)) =
        c' • ((1 : S) ⊗ₜ[R,f] m : ↥((ModuleCat.extendScalars f).obj M)) := by
      rw [ModuleCat.ExtendScalars.smul_tmul, mul_one]
    rw [hc]
    exact Submodule.smul_mem _ c' (key m)
  | add x y hx hy => exact Submodule.add_mem _ hx hy

theorem zmodTensorModuleFinite (A : Type) [AddCommGroup A] [Module.Finite ℤ A] (p : ℕ) :
    Module.Finite (ZMod p) ↥((ModuleCat.extendScalars (Int.castRingHom (ZMod p))).obj (ModuleCat.of ℤ A)) :=
  extendScalars_moduleFinite (Int.castRingHom (ZMod p)) (ModuleCat.of ℤ A)

end Work.Pi6.K2Z
