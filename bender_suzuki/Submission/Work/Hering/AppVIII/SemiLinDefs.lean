import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The "semilinear" group of maps `(x,y) ↦ (a₁·Φ^i x, η x + a₂·Φ^i y)` on `K × K`

`K` is a finite field of characteristic two, `Φ = x ↦ x ^ 2` the Frobenius automorphism
(viewed as an element of the group `K ≃+* K`), `i : ℤ`, `a₁ a₂ ∈ K^×` and `η : K → K` an
arbitrary function.

The group `semiLin` is an extension of the abelian group `shearLin` of "shear" maps
`(x,y) ↦ (x, η x + y)` by the metabelian group of the data `(a₁,a₂,i)`; in particular it is
solvable (see `Submission.Work.Hering.AppVIII.semiLin_solvable`).
-/

set_option autoImplicit false

noncomputable section

namespace Work.Hering.AppVIII

variable (K : Type*) [Field K] [CharP K 2] [Finite K]

/-- The Frobenius automorphism `x ↦ x ^ 2` of `K`, as an element of the group `K ≃+* K`. -/
def frobK : K ≃+* K := frobeniusEquiv K 2

lemma frobK_pow_apply_add (i : ℤ) (x y : K) :
    (frobK K ^ i) (x + y) = (frobK K ^ i) x + (frobK K ^ i) y :=
  map_add _ x y

lemma frobK_pow_apply_mul (i : ℤ) (x y : K) :
    (frobK K ^ i) (x * y) = (frobK K ^ i) x * (frobK K ^ i) y :=
  map_mul _ x y

lemma frobK_pow_apply_comp (i j : ℤ) (x : K) :
    (frobK K ^ i) ((frobK K ^ j) x) = (frobK K ^ (i + j)) x := by
  rw [show (frobK K ^ i) ((frobK K ^ j) x) = (frobK K ^ i * frobK K ^ j) x from rfl,
    ← zpow_add]

@[simp] lemma frobK_pow_apply_neg_comp (i : ℤ) (x : K) :
    (frobK K ^ i) ((frobK K ^ (-i)) x) = x := by
  rw [frobK_pow_apply_comp, add_neg_cancel, zpow_zero]
  rfl

@[simp] lemma frobK_pow_apply_zero (x : K) : (frobK K ^ (0 : ℤ)) x = x := rfl

lemma frobK_pow_ne_zero (i : ℤ) {a : K} (ha : a ≠ 0) : (frobK K ^ i) a ≠ 0 := by
  intro h
  apply ha
  have h2 := congrArg (⇑((frobK K ^ i).symm)) h
  simpa [RingEquiv.symm_apply_apply] using h2

/-- The set of "shear" permutations `(x,y) ↦ (x, η x + y)`. -/
def shearSet : Set (Equiv.Perm (K × K)) :=
  {f | ∃ η : K → K, ∀ x y : K, f (x, y) = (x, η x + y)}

/-- The set of "diagonal semilinear" permutations `(x,y) ↦ (a₁x, η x + a₂y)` (`a₁ a₂ ≠ 0`). -/
def diagSet : Set (Equiv.Perm (K × K)) :=
  {f | ∃ (a₁ a₂ : K), a₁ ≠ 0 ∧ a₂ ≠ 0 ∧ ∃ η : K → K,
    ∀ x y : K, f (x, y) = (a₁ * x, η x + a₂ * y)}

/-- The set of "semilinear" permutations `(x,y) ↦ (a₁·Φ^i x, η x + a₂·Φ^i y)`. -/
def semiSet : Set (Equiv.Perm (K × K)) :=
  {f | ∃ (a₁ a₂ : K), a₁ ≠ 0 ∧ a₂ ≠ 0 ∧ ∃ (i : ℤ) (η : K → K),
    ∀ x y : K, f (x, y) = (a₁ * (frobK K ^ i) x, η x + a₂ * (frobK K ^ i) y)}

/-- `shearSet` is a subgroup: the abelian group of shear maps. -/
def shearLin : Subgroup (Equiv.Perm (K × K)) where
  carrier := shearSet K
  one_mem' := ⟨fun _ => 0, by intro x y; simp⟩
  mul_mem' := by
    intro f g hf hg
    obtain ⟨η, hf'⟩ := hf
    obtain ⟨ζ, hg'⟩ := hg
    refine ⟨fun x => η x + ζ x, ?_⟩
    intro x y
    rw [Equiv.Perm.mul_def, Equiv.trans_apply, hg', hf']
    refine Prod.ext rfl ?_
    dsimp only
    abel
  inv_mem' := by
    intro f hf
    obtain ⟨η, hf'⟩ := hf
    refine ⟨η, ?_⟩
    intro x y
    change f.symm (x, y) = (x, η x + y)
    rw [Equiv.symm_apply_eq, hf']
    refine Prod.ext rfl ?_
    dsimp only
    rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]

/-- `diagSet` is a subgroup. -/
def diagLin : Subgroup (Equiv.Perm (K × K)) where
  carrier := diagSet K
  one_mem' := ⟨1, 1, one_ne_zero, one_ne_zero, fun _ => 0, by
    intro x y
    simp⟩
  mul_mem' := by
    intro f g hf hg
    obtain ⟨a₁, a₂, ha₁, ha₂, η, hf'⟩ := hf
    obtain ⟨b₁, b₂, hb₁, hb₂, ζ, hg'⟩ := hg
    refine ⟨a₁ * b₁, a₂ * b₂, mul_ne_zero ha₁ hb₁, mul_ne_zero ha₂ hb₂,
      fun x => η (b₁ * x) + a₂ * ζ x, ?_⟩
    intro x y
    rw [Equiv.Perm.mul_def, Equiv.trans_apply, hg', hf']
    refine Prod.ext ?_ ?_ <;> dsimp only
    · ring
    · ring
  inv_mem' := by
    intro f hf
    obtain ⟨a₁, a₂, ha₁, ha₂, η, hf'⟩ := hf
    refine ⟨a₁⁻¹, a₂⁻¹, inv_ne_zero ha₁, inv_ne_zero ha₂,
      fun X => a₂⁻¹ * η (a₁⁻¹ * X), ?_⟩
    intro X Y
    change f.symm (X, Y) = (a₁⁻¹ * X, a₂⁻¹ * η (a₁⁻¹ * X) + a₂⁻¹ * Y)
    rw [Equiv.symm_apply_eq, hf']
    refine Prod.ext ?_ ?_ <;> dsimp only
    · rw [← mul_assoc, mul_inv_cancel₀ ha₁, one_mul]
    · rw [mul_add]
      have h2 : a₂ * (a₂⁻¹ * η (a₁⁻¹ * X)) = η (a₁⁻¹ * X) := by
        rw [← mul_assoc, mul_inv_cancel₀ ha₂, one_mul]
      have h3 : a₂ * (a₂⁻¹ * Y) = Y := by rw [← mul_assoc, mul_inv_cancel₀ ha₂, one_mul]
      rw [h2, h3, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]

/-- `semiSet` is a subgroup. -/
def semiLin : Subgroup (Equiv.Perm (K × K)) where
  carrier := semiSet K
  one_mem' := ⟨1, 1, one_ne_zero, one_ne_zero, 0, fun _ => 0, by
    intro x y
    simp⟩
  mul_mem' := by
    intro f g hf hg
    obtain ⟨a₁, a₂, ha₁, ha₂, i, η, hf'⟩ := hf
    obtain ⟨b₁, b₂, hb₁, hb₂, j, ζ, hg'⟩ := hg
    refine ⟨a₁ * (frobK K ^ i) b₁, a₂ * (frobK K ^ i) b₂,
      mul_ne_zero ha₁ (frobK_pow_ne_zero K i hb₁), mul_ne_zero ha₂ (frobK_pow_ne_zero K i hb₂),
      i + j, fun x => η (b₁ * (frobK K ^ j) x) + a₂ * (frobK K ^ i) (ζ x), ?_⟩
    intro x y
    rw [Equiv.Perm.mul_def, Equiv.trans_apply, hg', hf']
    simp only [map_add, map_mul, frobK_pow_apply_comp]
    refine Prod.ext ?_ ?_ <;> dsimp only <;> ring
  inv_mem' := by
    intro f hf
    obtain ⟨a₁, a₂, ha₁, ha₂, i, η, hf'⟩ := hf
    refine ⟨((frobK K ^ (-i)) a₁)⁻¹, ((frobK K ^ (-i)) a₂)⁻¹,
      inv_ne_zero (frobK_pow_ne_zero K (-i) ha₁), inv_ne_zero (frobK_pow_ne_zero K (-i) ha₂),
      -i, fun X => ((frobK K ^ (-i)) a₂)⁻¹ *
        (frobK K ^ (-i)) (η (((frobK K ^ (-i)) a₁)⁻¹ * (frobK K ^ (-i)) X)), ?_⟩
    intro X Y
    change f.symm (X, Y) = (((frobK K ^ (-i)) a₁)⁻¹ * (frobK K ^ (-i)) X,
      ((frobK K ^ (-i)) a₂)⁻¹ *
        (frobK K ^ (-i)) (η (((frobK K ^ (-i)) a₁)⁻¹ * (frobK K ^ (-i)) X)) +
      ((frobK K ^ (-i)) a₂)⁻¹ * (frobK K ^ (-i)) Y)
    rw [Equiv.symm_apply_eq, hf']
    simp only [map_add, map_mul, map_inv₀, frobK_pow_apply_comp, frobK_pow_apply_neg_comp,
      add_neg_cancel, frobK_pow_apply_zero]
    refine Prod.ext ?_ ?_ <;> dsimp only
    · rw [← mul_assoc, mul_inv_cancel₀ ha₁, one_mul]
    · rw [mul_add]
      have h2 : a₂ * (a₂⁻¹ * η (((frobK K ^ (-i)) a₁)⁻¹ * (frobK K ^ (-i)) X)) =
          η (((frobK K ^ (-i)) a₁)⁻¹ * (frobK K ^ (-i)) X) := by
        rw [← mul_assoc, mul_inv_cancel₀ ha₂, one_mul]
      have h3 : a₂ * (a₂⁻¹ * Y) = Y := by rw [← mul_assoc, mul_inv_cancel₀ ha₂, one_mul]
      rw [h2, h3, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]

end Work.Hering.AppVIII
