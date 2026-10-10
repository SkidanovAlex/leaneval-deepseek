import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Submission.Work.AbsoluteKummer.Basic
import Submission.Work.Kummer.Defs
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

variable (k : Type u) [Field k]

/-- The absolute Galois group of `k`, as the automorphism group of an algebraic closure.  It is
definitionally equal to `Field.absoluteGaloisGroup k`
(`Work.AbsoluteKummer.G_eq_absoluteGaloisGroup`), but the `def` `Field.absoluteGaloisGroup` is
opaque to type class search, so the developments of this chapter use `G k`. -/
abbrev G : Type u := AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k

theorem G_eq_absoluteGaloisGroup : G k = Field.absoluteGaloisGroup k := rfl

/-! ## The action on the units of `k̄` -/

/-- The action of a Galois automorphism on the units of `k̄`. -/
def algEquivUnitsMap (σ : G k) : (AlgebraicClosure k)ˣ →* (AlgebraicClosure k)ˣ :=
  Units.map σ.toAlgHom.toRingHom.toMonoidWithZeroHom

@[simp] theorem algEquivUnitsMap_coe (σ : G k) (u : (AlgebraicClosure k)ˣ) :
    ((algEquivUnitsMap k σ u : (AlgebraicClosure k)ˣ) : AlgebraicClosure k) =
      σ (u : AlgebraicClosure k) := rfl

@[simp] theorem algEquivUnitsMap_mul (σ τ : G k) (u : (AlgebraicClosure k)ˣ) :
    algEquivUnitsMap k σ (algEquivUnitsMap k τ u) = algEquivUnitsMap k (σ * τ) u := rfl

@[simp] theorem algEquivUnitsMap_one (u : (AlgebraicClosure k)ˣ) :
    algEquivUnitsMap k (1 : G k) u = u := rfl

/-- The Galois action on the units of the algebraic closure, transported to the additive group
`Additive (k̄)ˣ`. -/
noncomputable instance instDistribMulActionAddUnits :
    DistribMulAction (G k) (Additive (AlgebraicClosure k)ˣ) where
  smul σ a := Additive.ofMul (algEquivUnitsMap k σ (Additive.toMul a))
  one_smul a := by
    show Additive.ofMul (algEquivUnitsMap k (1 : G k) (Additive.toMul a)) = a
    rw [algEquivUnitsMap_one, ofMul_toMul]
  mul_smul σ τ a := by
    show Additive.ofMul (algEquivUnitsMap k (σ * τ) (Additive.toMul a)) =
      Additive.ofMul (algEquivUnitsMap k σ (algEquivUnitsMap k τ (Additive.toMul a)))
    rw [algEquivUnitsMap_mul]
  smul_zero σ := by
    show Additive.ofMul (algEquivUnitsMap k σ (1 : (AlgebraicClosure k)ˣ)) = 0
    rw [map_one, ofMul_one]
  smul_add σ a b := by
    show Additive.ofMul (algEquivUnitsMap k σ
      ((Additive.toMul a : (AlgebraicClosure k)ˣ) * (Additive.toMul b : (AlgebraicClosure k)ˣ))) =
      Additive.ofMul (algEquivUnitsMap k σ (Additive.toMul a)) +
        Additive.ofMul (algEquivUnitsMap k σ (Additive.toMul b))
    rw [map_mul, ofMul_mul]

/-- **The units of `k̄` form a discrete `G k`-module**: the stabiliser of `Additive.ofMul u` is
the stabiliser of the underlying field element `u`, which is open by
`stabilizer_isOpen_of_isIntegral`. -/
@[simp] theorem addUnits_smul_toMul (σ : G k) (a : Additive (AlgebraicClosure k)ˣ) :
    Additive.toMul (σ • a) = algEquivUnitsMap k σ (Additive.toMul a) := rfl

theorem stabilizer_addUnits_ofMul (u : (AlgebraicClosure k)ˣ) :
    (MulAction.stabilizer (G k) (Additive.ofMul u) : Set (G k)) =
      (MulAction.stabilizer (G k) (u : AlgebraicClosure k) : Set (G k)) := by
  ext σ
  simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
  constructor
  · intro h
    have h0 : Additive.ofMul (algEquivUnitsMap k σ u) = Additive.ofMul u := h
    have h2 : algEquivUnitsMap k σ u = u := Additive.ofMul.injective h0
    have h3 := congrArg (fun w : (AlgebraicClosure k)ˣ => (w : AlgebraicClosure k)) h2
    rwa [algEquivUnitsMap_coe] at h3
  · intro h
    have h2 : ((algEquivUnitsMap k σ u : (AlgebraicClosure k)ˣ) : AlgebraicClosure k) =
        (u : AlgebraicClosure k) := by
      rw [algEquivUnitsMap_coe]
      exact h
    exact Additive.ofMul.injective (Units.ext h2)

/-- **The units of `k̄` form a discrete `G k`-module.** -/
theorem isDiscreteModule_addUnits : IsDiscreteModule (G k) (Additive (AlgebraicClosure k)ˣ) := by
  intro a
  show IsOpen (MulAction.stabilizer (G k) (Additive.ofMul (Additive.toMul a)) : Set (G k))
  rw [stabilizer_addUnits_ofMul k (Additive.toMul a)]
  exact stabilizer_isOpen_of_isIntegral _

/-! ## The roots of unity -/

/-- The Galois action on `μ_n(k̄)`. -/
def rootsOfUnityMap (n : ℕ) (σ : G k) :
    (rootsOfUnity n (AlgebraicClosure k)) →* (rootsOfUnity n (AlgebraicClosure k)) where
  toFun u := ⟨algEquivUnitsMap k σ (u : (AlgebraicClosure k)ˣ), by
    rw [mem_rootsOfUnity']
    show ((algEquivUnitsMap k σ (u : (AlgebraicClosure k)ˣ) : (AlgebraicClosure k)ˣ) :
      AlgebraicClosure k) ^ n = 1
    rw [algEquivUnitsMap_coe, ← map_pow,
      (mem_rootsOfUnity' n (u : (AlgebraicClosure k)ˣ)).mp u.2, map_one]⟩
  map_one' := Subtype.ext (by simp)
  map_mul' u v := Subtype.ext (by simp)

@[simp] theorem rootsOfUnityMap_coe (n : ℕ) (σ : G k)
    (u : rootsOfUnity n (AlgebraicClosure k)) :
    ((rootsOfUnityMap k n σ u : rootsOfUnity n (AlgebraicClosure k)) :
      (AlgebraicClosure k)ˣ) = algEquivUnitsMap k σ (u : (AlgebraicClosure k)ˣ) := rfl

@[simp] theorem rootsOfUnityMap_mul (n : ℕ) (σ : G k)
    (u : rootsOfUnity n (AlgebraicClosure k)) :
    rootsOfUnityMap k n σ (rootsOfUnityMap k n (1 : G k) u) = rootsOfUnityMap k n σ u := rfl

/-- The Galois action on `μ_n(k̄)`, transported to `Additive (rootsOfUnity n k̄)`. -/
noncomputable instance instDistribMulActionAddRootsOfUnity (n : ℕ) :
    DistribMulAction (G k) (Additive (rootsOfUnity n (AlgebraicClosure k))) where
  smul σ a := Additive.ofMul (rootsOfUnityMap k n σ (Additive.toMul a))
  one_smul a := by
    show Additive.ofMul (rootsOfUnityMap k n (1 : G k) (Additive.toMul a)) = a
    have h : rootsOfUnityMap k n (1 : G k) (Additive.toMul a) = Additive.toMul a :=
      Subtype.ext (by rw [rootsOfUnityMap_coe, algEquivUnitsMap_one])
    rw [h, ofMul_toMul]
  mul_smul σ τ a := by
    show Additive.ofMul (rootsOfUnityMap k n (σ * τ) (Additive.toMul a)) =
      Additive.ofMul (rootsOfUnityMap k n σ (rootsOfUnityMap k n τ (Additive.toMul a)))
    congr 1
  smul_zero σ := by
    show Additive.ofMul (rootsOfUnityMap k n σ (1 : rootsOfUnity n (AlgebraicClosure k))) = 0
    rw [map_one, ofMul_one]
  smul_add σ a b := by
    show Additive.ofMul (rootsOfUnityMap k n σ
      ((Additive.toMul a : rootsOfUnity n (AlgebraicClosure k)) *
        (Additive.toMul b : rootsOfUnity n (AlgebraicClosure k)))) =
      Additive.ofMul (rootsOfUnityMap k n σ (Additive.toMul a)) +
        Additive.ofMul (rootsOfUnityMap k n σ (Additive.toMul b))
    rw [map_mul, ofMul_mul]

/-- Unfolding the action on `μ_n` in terms of the underlying units. -/
theorem addRootsOfUnity_smul_toMul_val (n : ℕ) (σ : G k)
    (a : Additive (rootsOfUnity n (AlgebraicClosure k))) :
    ((Additive.toMul (σ • a) : rootsOfUnity n (AlgebraicClosure k)) : (AlgebraicClosure k)ˣ) =
      algEquivUnitsMap k σ ((Additive.toMul a : rootsOfUnity n (AlgebraicClosure k)) :
        (AlgebraicClosure k)ˣ) := rfl

/-- **`μ_n(k̄)` is a discrete `G k`-module**: the stabiliser of an `n`-th root of unity is the
stabiliser of its underlying field element. -/
theorem stabilizer_addRootsOfUnity (n : ℕ)
    (a : Additive (rootsOfUnity n (AlgebraicClosure k))) :
    (MulAction.stabilizer (G k) a : Set (G k)) =
      (MulAction.stabilizer (G k)
        (((Additive.toMul a : rootsOfUnity n (AlgebraicClosure k)) : (AlgebraicClosure k)ˣ) :
          AlgebraicClosure k) : Set (G k)) := by
  ext σ
  simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
  constructor
  · intro h
    have h0 : Additive.ofMul (rootsOfUnityMap k n σ (Additive.toMul a)) = a := h
    have h2 : rootsOfUnityMap k n σ (Additive.toMul a) = Additive.toMul a :=
      Additive.ofMul.injective h0
    have h3 := congrArg (fun w : rootsOfUnity n (AlgebraicClosure k) =>
      ((w : (AlgebraicClosure k)ˣ) : AlgebraicClosure k)) h2
    rw [rootsOfUnityMap_coe] at h3
    rwa [algEquivUnitsMap_coe] at h3
  · intro h
    have h5 : σ • (((Additive.toMul a : rootsOfUnity n (AlgebraicClosure k)) :
        (AlgebraicClosure k)ˣ) : AlgebraicClosure k) =
        (((Additive.toMul a : rootsOfUnity n (AlgebraicClosure k)) : (AlgebraicClosure k)ˣ) :
          AlgebraicClosure k) := h
    rw [AlgEquiv.smul_def] at h5
    have h3 : algEquivUnitsMap k σ ((Additive.toMul a : rootsOfUnity n (AlgebraicClosure k)) :
        (AlgebraicClosure k)ˣ) =
        ((Additive.toMul a : rootsOfUnity n (AlgebraicClosure k)) : (AlgebraicClosure k)ˣ) := by
      refine Units.ext ?_
      rw [algEquivUnitsMap_coe]
      exact h5
    have h4 : rootsOfUnityMap k n σ (Additive.toMul a) = Additive.toMul a := by
      refine Subtype.ext ?_
      rw [rootsOfUnityMap_coe]
      exact h3
    show Additive.ofMul (rootsOfUnityMap k n σ (Additive.toMul a)) = a
    rw [h4, ofMul_toMul]

/-- **`μ_n(k̄)` is a discrete `G k`-module.** -/
theorem isDiscreteModule_addRootsOfUnity (n : ℕ) :
    IsDiscreteModule (G k) (Additive (rootsOfUnity n (AlgebraicClosure k))) := by
  intro a
  rw [stabilizer_addRootsOfUnity k n a]
  exact stabilizer_isOpen_of_isIntegral _

/-! ## Triviality of the action on `μ_n` when `μ_n ⊆ k` -/

/-- A unit of `k̄` coming from `kˣ` is fixed by the Galois action. -/
theorem algEquivUnitsMap_eq_self_of_mem_range {u : (AlgebraicClosure k)ˣ} {x : kˣ}
    (hx : Units.map (algebraMap k (AlgebraicClosure k)) x = u) (σ : G k) :
    algEquivUnitsMap k σ u = u := by
  refine Units.ext ?_
  rw [algEquivUnitsMap_coe, ← hx, Units.coe_map]
  simpa using AlgEquiv.commutes σ (x : k)

/-- A unit of `k̄` which is an `n`-th root of unity is fixed by the Galois action, whenever `k`
contains a primitive `n`-th root of unity. -/
theorem algEquivUnitsMap_eq_self_of_mem_rootsOfUnity {n : ℕ} [NeZero n] {ζ : k}
    (hζ : IsPrimitiveRoot ζ n) (σ : G k) {u : (AlgebraicClosure k)ˣ}
    (hu : u ∈ rootsOfUnity n (AlgebraicClosure k)) : algEquivUnitsMap k σ u = u := by
  obtain ⟨i, -, hi⟩ := Work.Kummer.exists_primRootUnit_pow_eq_of_pow_eq_one hζ
    ((mem_rootsOfUnity' n u).mp hu)
  rw [hi]
  exact algEquivUnitsMap_eq_self_of_mem_range k rfl σ

/-- **The action of `G k` on `μ_n(k̄)` is trivial when `k` contains a primitive `n`-th root of
unity.** -/
theorem smul_rootsOfUnity {n : ℕ} [NeZero n] {ζ : k} (hζ : IsPrimitiveRoot ζ n)
    (σ : G k) (a : Additive (rootsOfUnity n (AlgebraicClosure k))) : σ • a = a := by
  have hu : (((Additive.toMul a : rootsOfUnity n (AlgebraicClosure k)) :
      (AlgebraicClosure k)ˣ) : AlgebraicClosure k) ^ n = 1 :=
    (mem_rootsOfUnity' n ((Additive.toMul a : rootsOfUnity n (AlgebraicClosure k)) :
      (AlgebraicClosure k)ˣ)).mp (Additive.toMul a : rootsOfUnity n (AlgebraicClosure k)).2
  obtain ⟨i, -, hi⟩ := Work.Kummer.exists_primRootUnit_pow_eq_of_pow_eq_one hζ hu
  have hfix : algEquivUnitsMap k σ ((Additive.toMul a : rootsOfUnity n (AlgebraicClosure k)) :
      (AlgebraicClosure k)ˣ) =
      ((Additive.toMul a : rootsOfUnity n (AlgebraicClosure k)) : (AlgebraicClosure k)ˣ) := by
    rw [hi]
    exact algEquivUnitsMap_eq_self_of_mem_range k rfl σ
  refine Additive.ext (Subtype.ext ?_)
  rw [addRootsOfUnity_smul_toMul_val]
  exact hfix

/-- With a trivial action on the coefficients, `d⁰` vanishes. -/
theorem d0_rootsOfUnity_eq_zero {n : ℕ} [NeZero n] {ζ : k} (hζ : IsPrimitiveRoot ζ n)
    (a : Additive (rootsOfUnity n (AlgebraicClosure k))) :
    Work.GroupCohomology.d0 (G k) (Additive (rootsOfUnity n (AlgebraicClosure k))) a = 0 := by
  funext σ
  rw [Pi.zero_apply, Work.GroupCohomology.d0_apply, smul_rootsOfUnity k hζ σ a, sub_self]

/-- Hence `B¹(G_k, μ_n) = 0`. -/
theorem B1_rootsOfUnity_eq_bot {n : ℕ} [NeZero n] {ζ : k} (hζ : IsPrimitiveRoot ζ n) :
    B1 (G k) (Additive (rootsOfUnity n (AlgebraicClosure k))) = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro f hf
  rw [mem_B1_iff] at hf
  obtain ⟨a, rfl⟩ := hf
  rw [d0_rootsOfUnity_eq_zero k hζ a]
  exact AddSubgroup.zero_mem _

/-- When the action on the coefficients is trivial, the class map `Z¹ → H¹` is injective. -/
theorem H1π_rootsOfUnity_injective {n : ℕ} [NeZero n] {ζ : k} (hζ : IsPrimitiveRoot ζ n) :
    Function.Injective (H1π (G k) (Additive (rootsOfUnity n (AlgebraicClosure k)))) := by
  intro f g hfg
  rw [H1π_eq_iff] at hfg
  rw [B1_rootsOfUnity_eq_bot k hζ] at hfg
  have hzero : ((f - g : Z1 (G k) (Additive (rootsOfUnity n (AlgebraicClosure k)))) :
      G k → Additive (rootsOfUnity n (AlgebraicClosure k))) = 0 := by
    simpa using hfg
  exact sub_eq_zero.mp (Subtype.ext hzero)

/-- With a trivial action on `μ_n`, crossed homomorphisms are group homomorphisms. -/
theorem isCrossedHom_iff_map_mul {n : ℕ} [NeZero n] {ζ : k} (hζ : IsPrimitiveRoot ζ n)
    (f : G k → Additive (rootsOfUnity n (AlgebraicClosure k))) :
    Work.GroupCohomology.IsCrossedHom (G k) (Additive (rootsOfUnity n (AlgebraicClosure k))) f ↔
      ∀ σ τ : G k, f (σ * τ) = f τ + f σ := by
  constructor
  · intro hf σ τ
    rw [hf σ τ, smul_rootsOfUnity k hζ σ (f τ)]
  · intro hf σ τ
    rw [hf σ τ, smul_rootsOfUnity k hζ σ (f τ)]

/-! ## The same structures for the spelling `Field.absoluteGaloisGroup k` -/

/-- `Field.absoluteGaloisGroup k` is definitionally equal to `G k`
(`Work.AbsoluteKummer.G_eq_absoluteGaloisGroup`), but it is a `def` and hence invisible to type
class search; we re-register the module structures for that spelling. -/
noncomputable instance instDistribMulActionAddUnitsAbsolute (k : Type*) [Field k] :
    DistribMulAction (Field.absoluteGaloisGroup k) (Additive (AlgebraicClosure k)ˣ) :=
  instDistribMulActionAddUnits k

/-- The `μ_n`-module structure for the spelling `Field.absoluteGaloisGroup k`. -/
noncomputable instance instDistribMulActionAddRootsOfUnityAbsolute (k : Type*) [Field k] (n : ℕ) :
    DistribMulAction (Field.absoluteGaloisGroup k)
      (Additive (rootsOfUnity n (AlgebraicClosure k))) :=
  instDistribMulActionAddRootsOfUnity k n

theorem isDiscreteModule_addUnits_absolute (k : Type*) [Field k] :
    IsDiscreteModule (Field.absoluteGaloisGroup k) (Additive (AlgebraicClosure k)ˣ) :=
  isDiscreteModule_addUnits k

theorem isDiscreteModule_addRootsOfUnity_absolute (k : Type*) [Field k] (n : ℕ) :
    IsDiscreteModule (Field.absoluteGaloisGroup k)
      (Additive (rootsOfUnity n (AlgebraicClosure k))) :=
  isDiscreteModule_addRootsOfUnity k n

end

end Work.AbsoluteKummer
