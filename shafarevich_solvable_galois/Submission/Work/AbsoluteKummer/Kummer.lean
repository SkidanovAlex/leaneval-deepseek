/-
Copyright (c) 2025. All rights reserved.

# Kummer theory in the absolute-Galois language

For a field `k` and `n > 0` with a primitive `n`-th root of unity `ζ ∈ k`, the Kummer sequence

`1 → μ_n(k̄) → k̄ˣ →^{n} k̄ˣ → 1`

gives a canonical isomorphism `kˣ/(kˣ)^n ≃ H¹(G_k, μ_n)`; the class of `x : kˣ` corresponds to the
crossed homomorphism `σ ↦ σ α / α`, where `α ∈ k̄ˣ` is any `n`-th root of `x`.

## Main definitions

* `Work.AbsoluteKummer.kummerRootUnit x : k̄ˣ` — a choice of `n`-th root of `x`
  (`Work.AbsoluteKummer.kummerRootUnit_pow`);
* `Work.AbsoluteKummer.kummerCocycleFun hζ x` — the `1`-cochain `σ ↦ σ α/α` with values in `μ_n`.

The cocycle properties, the induced map `kˣ/(kˣ)^n → H¹(G_k, μ_n)` and its bijectivity are
`Work.AbsoluteKummer.Kummer.kummerMap_bijective` (in `Submission/Work/AbsoluteKummer/Kummer/`).
-/
import Mathlib
import Submission.Work.AbsoluteKummer.Coefficients
import Submission.Work.AbsoluteKummer.Basic
import Submission.Work.Kummer.All
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

universe u

namespace Work.AbsoluteKummer

open scoped Classical Topology
open Filter

noncomputable section

variable {k : Type u} [Field k] {n : ℕ} [NeZero n] {ζ : k}

/-! ## A choice of an `n`-th root -/

theorem kummerRootUnit_exists (x : kˣ) :
    ∃ z : AlgebraicClosure k, z ^ n = algebraMap k (AlgebraicClosure k) (x : k) :=
  IsAlgClosed.exists_pow_nat_eq _ (Nat.pos_of_ne_zero (NeZero.ne n))

theorem kummerRootUnit_choose_ne_zero (x : kˣ) :
    Classical.choose (kummerRootUnit_exists (n := n) x) ≠ 0 := by
  have hspec : (Classical.choose (kummerRootUnit_exists (n := n) x)) ^ n =
      algebraMap k (AlgebraicClosure k) (x : k) :=
    Classical.choose_spec (kummerRootUnit_exists (n := n) x)
  intro hz
  rw [hz, zero_pow (NeZero.ne n)] at hspec
  exact x.ne_zero ((algebraMap k (AlgebraicClosure k)).injective (by rw [hspec.symm, map_zero]))

/-- A choice of an `n`-th root in `k̄` of a unit `x : kˣ`. -/
noncomputable def kummerRootUnit (x : kˣ) : (AlgebraicClosure k)ˣ :=
  Units.mk0 (Classical.choose (kummerRootUnit_exists (n := n) x))
    (kummerRootUnit_choose_ne_zero (n := n) x)

theorem kummerRootUnit_val (x : kˣ) :
    ((kummerRootUnit (n := n) x : (AlgebraicClosure k)ˣ) : AlgebraicClosure k) =
      Classical.choose (kummerRootUnit_exists (n := n) x) := rfl

theorem kummerRootUnit_pow_val (x : kˣ) :
    ((kummerRootUnit (n := n) x : (AlgebraicClosure k)ˣ) : AlgebraicClosure k) ^ n =
      algebraMap k (AlgebraicClosure k) (x : k) :=
  Classical.choose_spec (kummerRootUnit_exists (n := n) x)

theorem kummerRootUnit_pow (x : kˣ) :
    kummerRootUnit (n := n) x ^ n = Units.map (algebraMap k (AlgebraicClosure k)) x := by
  refine Units.ext ?_
  rw [Units.val_pow_eq_pow_val, Units.coe_map]
  exact kummerRootUnit_pow_val (n := n) x

/-! ## The Kummer cocycle -/

variable (hζ : IsPrimitiveRoot ζ n)

/-- The Kummer `1`-cochain `σ ↦ σ α/α` attached to a choice of `α ^ n = x`, with values in
`μ_n(k̄)`. -/
noncomputable def kummerCocycleFun (x : kˣ) :
    G k → Additive (rootsOfUnity n (AlgebraicClosure k)) :=
  fun σ => Additive.ofMul ⟨Work.Kummer.kummerRatio σ (kummerRootUnit (n := n) x),
    Work.Kummer.kummerRatio_mem_rootsOfUnity hζ (kummerRootUnit_pow_val (n := n) x) σ⟩

@[simp] theorem kummerCocycleFun_toMul (x : kˣ) (σ : G k) :
    Additive.toMul (kummerCocycleFun hζ x σ) =
      Work.Kummer.kummerRatio σ (kummerRootUnit (n := n) x) := rfl

theorem kummerCocycleFun_apply_coe (x : kˣ) (σ : G k) :
    ((Additive.toMul (kummerCocycleFun hζ x σ) : rootsOfUnity n (AlgebraicClosure k)) :
        (AlgebraicClosure k)ˣ) =
      algEquivUnitsMap k σ (kummerRootUnit (n := n) x) / kummerRootUnit (n := n) x := rfl

/-- The ratio of a product is the product of the ratios (the action on `μ_n` being trivial). -/
theorem kummerRatio_mul_ratio {σ : G k} {α β : (AlgebraicClosure k)ˣ}
    {a b : kˣ} (hα : (α : AlgebraicClosure k) ^ n = algebraMap k (AlgebraicClosure k) (a : k))
    (hβ : (β : AlgebraicClosure k) ^ n = algebraMap k (AlgebraicClosure k) (b : k)) :
    Work.Kummer.kummerRatio σ α * Work.Kummer.kummerRatio σ β =
      Work.Kummer.kummerRatio σ (α * β) := by
  refine Units.ext ?_
  rw [Units.val_mul, Work.Kummer.kummerRatio_coe, Work.Kummer.kummerRatio_coe,
    Work.Kummer.kummerRatio_coe, Units.val_mul, map_mul]
  field_simp

/-- The ratio `σ α/α` only depends on `α ^ n`, so the Kummer cochain attached to `x` is additive
in `x`. -/
theorem kummerCocycleFun_add (x y : kˣ) :
    kummerCocycleFun hζ (x * y) = kummerCocycleFun hζ x + kummerCocycleFun hζ y := by
  funext σ
  refine Additive.ext (Subtype.ext ?_)
  rw [Pi.add_apply, toMul_add, Subgroup.coe_mul, kummerCocycleFun_apply_coe,
    kummerCocycleFun_apply_coe, kummerCocycleFun_apply_coe]
  show Work.Kummer.kummerRatio σ (kummerRootUnit (n := n) (x * y)) =
    Work.Kummer.kummerRatio σ (kummerRootUnit (n := n) x) *
      Work.Kummer.kummerRatio σ (kummerRootUnit (n := n) y)
  have h1 : Work.Kummer.kummerRatio σ (kummerRootUnit (n := n) (x * y)) =
      Work.Kummer.kummerRatio σ (kummerRootUnit (n := n) x * kummerRootUnit (n := n) y) := by
    refine Work.Kummer.kummerRatio_congr (hζ := hζ) (a := x * y) ?_ ?_ σ
    · rw [Units.val_mul, mul_pow, kummerRootUnit_pow_val (n := n) x,
        kummerRootUnit_pow_val (n := n) y, Units.val_mul, map_mul]
    · exact kummerRootUnit_pow_val (n := n) (x * y)
  rw [h1, ← kummerRatio_mul_ratio (kummerRootUnit_pow_val (n := n) x)
    (kummerRootUnit_pow_val (n := n) y)]

/-- The ratio `σ ↦ σ α/α` is locally constant: the action of `G k` on `k̄ˣ` is a discrete module
action. -/
theorem isLocallyConstant_kummerRatio (α : (AlgebraicClosure k)ˣ) :
    IsLocallyConstant (fun σ : G k => Work.Kummer.kummerRatio σ α) := by
  intro σ₀
  refine ⟨{σ : G k | σ₀⁻¹ * σ ∈ MulAction.stabilizer (G k)
      (Additive.ofMul α : Additive (AlgebraicClosure k)ˣ)}, ?_, ?_, ?_⟩
  · exact isOpen_smul_stabilizer (isDiscreteModule_addUnits k) σ₀ _
  · exact mem_self_smul_stabilizer σ₀ _
  · intro σ hσ
    have hσ' : (σ : G k) • (Additive.ofMul α : Additive (AlgebraicClosure k)ˣ) =
        σ₀ • (Additive.ofMul α : Additive (AlgebraicClosure k)ˣ) :=
      smul_eq_of_mem_smul_stabilizer hσ
    have h2 : algEquivUnitsMap k σ α = algEquivUnitsMap k σ₀ α := by
      have h3 := congrArg (fun b : Additive (AlgebraicClosure k)ˣ => Additive.toMul b) hσ'
      simpa only [addUnits_smul_toMul, toMul_ofMul] using h3
    exact congrArg (fun u : (AlgebraicClosure k)ˣ => u / α) h2

/-- The Kummer cochain is locally constant. -/
theorem isLocallyConstant_kummerCocycleFun (x : kˣ) :
    IsLocallyConstant (kummerCocycleFun hζ x) := by
  intro σ
  obtain ⟨U, hU, hσU, hUc⟩ := isLocallyConstant_kummerRatio (kummerRootUnit (n := n) x) σ
  refine ⟨U, hU, hσU, fun τ hτ => ?_⟩
  refine Additive.ext (Subtype.ext ?_)
  rw [kummerCocycleFun_apply_coe, kummerCocycleFun_apply_coe]
  exact hUc τ hτ

/-- The Kummer cochain is a crossed homomorphism. -/
theorem isCrossedHom_kummerCocycleFun (x : kˣ) :
    Work.GroupCohomology.IsCrossedHom (G k)
      (Additive (rootsOfUnity n (AlgebraicClosure k))) (kummerCocycleFun hζ x) := by
  have hα := kummerRootUnit_pow_val (n := n) x
  intro σ τ
  refine Additive.ext (Subtype.ext ?_)
  rw [toMul_add, Subgroup.coe_mul, addRootsOfUnity_smul_toMul_val,
    kummerCocycleFun_apply_coe, kummerCocycleFun_apply_coe, kummerCocycleFun_apply_coe]
  show Work.Kummer.kummerRatio (σ * τ) (kummerRootUnit (n := n) x) =
    algEquivUnitsMap k σ (Work.Kummer.kummerRatio τ (kummerRootUnit (n := n) x)) *
      Work.Kummer.kummerRatio σ (kummerRootUnit (n := n) x)
  rw [Work.Kummer.kummerRatio_mul hζ hα σ τ,
    algEquivUnitsMap_eq_self_of_mem_rootsOfUnity k hζ σ
      (Work.Kummer.kummerRatio_mem_rootsOfUnity hζ hα τ)]

/-- The Kummer `1`-cocycle attached to `x : kˣ`, as an element of `Z¹(G_k, μ_n)`. -/
noncomputable def kummerCocycle (x : kˣ) :
    Z1 (G k) (Additive (rootsOfUnity n (AlgebraicClosure k))) :=
  ⟨kummerCocycleFun hζ x, mem_Z1_of (isCrossedHom_kummerCocycleFun hζ x)
    (isLocallyConstant_kummerCocycleFun hζ x)⟩

@[simp] theorem kummerCocycle_coe (x : kˣ) :
    ((kummerCocycle hζ x : Z1 (G k) (Additive (rootsOfUnity n (AlgebraicClosure k)))) :
      G k → Additive (rootsOfUnity n (AlgebraicClosure k))) = kummerCocycleFun hζ x := rfl

/-- The class in `H¹(G_k, μ_n)` of the Kummer cocycle of `x`. -/
noncomputable def kummerClassFun (x : kˣ) :
    H1 (G k) (Additive (rootsOfUnity n (AlgebraicClosure k))) :=
  H1π (G k) (Additive (rootsOfUnity n (AlgebraicClosure k))) (kummerCocycle hζ x)

theorem kummerClassFun_add (x y : kˣ) :
    kummerClassFun hζ (x * y) = kummerClassFun hζ x + kummerClassFun hζ y := by
  rw [kummerClassFun, kummerClassFun, kummerClassFun,
    show kummerCocycle hζ (x * y) = kummerCocycle hζ x + kummerCocycle hζ y from
      Subtype.ext (kummerCocycleFun_add hζ x y)]
  rw [map_add]

theorem kummerCocycleFun_one : kummerCocycleFun hζ (1 : kˣ) = 0 := by
  funext σ
  have hα := kummerRootUnit_pow_val (n := n) (1 : kˣ)
  have h2 : Work.Kummer.kummerRatio σ (kummerRootUnit (n := n) (1 : kˣ)) =
      Work.Kummer.kummerRatio σ (1 : (AlgebraicClosure k)ˣ) := by
    refine Work.Kummer.kummerRatio_congr (hζ := hζ) (a := (1 : kˣ)) ?_ ?_ σ
    · simp
    · rw [hα]
  have h1 : Work.Kummer.kummerRatio σ (kummerRootUnit (n := n) (1 : kˣ)) = 1 := by
    rw [h2]
    refine Units.ext ?_
    rw [Work.Kummer.kummerRatio_coe]
    simp
  refine Additive.ext (Subtype.ext ?_)
  rw [kummerCocycleFun_toMul]
  exact h1

theorem kummerClassFun_one : kummerClassFun hζ (1 : kˣ) = 0 := by
  rw [kummerClassFun,
    show kummerCocycle hζ (1 : kˣ) = 0 from Subtype.ext (kummerCocycleFun_one hζ)]
  rw [map_zero]

/-- The class of an `n`-th power is zero. -/
theorem kummerClassFun_pow (x : kˣ) : kummerClassFun hζ (x ^ n) = 0 := by
  rw [kummerClassFun, H1π_eq_zero_iff, kummerCocycle_coe]
  have hfun : kummerCocycleFun hζ (x ^ n) = 0 := by
    funext σ
    have hα := kummerRootUnit_pow_val (n := n) (x ^ n)
    have h2 : Work.Kummer.kummerRatio σ (kummerRootUnit (n := n) (x ^ n)) =
        Work.Kummer.kummerRatio σ (Units.map (algebraMap k (AlgebraicClosure k)) x) := by
      refine Work.Kummer.kummerRatio_congr (hζ := hζ) (a := x ^ n) ?_ ?_ σ
      · rw [Units.coe_map, Units.val_pow_eq_pow_val]
        exact (map_pow (algebraMap k (AlgebraicClosure k)) (x : k) n).symm
      · exact hα
    have h3 : Work.Kummer.kummerRatio σ (Units.map (algebraMap k (AlgebraicClosure k)) x) = 1 := by
      have h4 : Work.Kummer.kummerRatio σ (Units.map (algebraMap k (AlgebraicClosure k)) x) =
          algEquivUnitsMap k σ (Units.map (algebraMap k (AlgebraicClosure k)) x) /
            Units.map (algebraMap k (AlgebraicClosure k)) x := rfl
      rw [h4, algEquivUnitsMap_eq_self_of_mem_range k (x := x) rfl σ]
      exact div_self' _
    refine Additive.ext (Subtype.ext ?_)
    rw [Pi.zero_apply, kummerCocycleFun_toMul, h2]
    exact h3
  rw [hfun]
  exact AddSubgroup.zero_mem _

/-- The Kummer map on `kˣ`, as a homomorphism into the multiplicative group attached to
`H¹(G_k, μ_n)`. -/
noncomputable def kummerClassHom :
    kˣ →* Multiplicative (H1 (G k) (Additive (rootsOfUnity n (AlgebraicClosure k)))) where
  toFun x := Multiplicative.ofAdd (kummerClassFun hζ x)
  map_one' := by rw [kummerClassFun_one]; rfl
  map_mul' x y := by rw [kummerClassFun_add]; rfl

@[simp] theorem kummerClassHom_apply (x : kˣ) :
    kummerClassHom hζ x = Multiplicative.ofAdd (kummerClassFun hζ x) := rfl

/-- **The Kummer map** `kˣ/(kˣ)^n → H¹(G_k, μ_n)`. -/
noncomputable def kummerMap :
    (kˣ ⧸ Work.Kummer.nthPowerSubgroup n kˣ) →*
      Multiplicative (H1 (G k) (Additive (rootsOfUnity n (AlgebraicClosure k)))) :=
  QuotientGroup.lift (Work.Kummer.nthPowerSubgroup n kˣ) (kummerClassHom hζ) (by
    intro x hx
    obtain ⟨y, hy⟩ := hx
    rw [← hy]
    show Multiplicative.ofAdd (kummerClassFun hζ (y ^ n)) = 1
    rw [kummerClassFun_pow]
    rfl)

theorem kummerMap_mk (x : kˣ) :
    kummerMap hζ (QuotientGroup.mk' (Work.Kummer.nthPowerSubgroup n kˣ) x) =
      Multiplicative.ofAdd (kummerClassFun hζ x) :=
  QuotientGroup.lift_mk' _ _ x

end

end Work.AbsoluteKummer
