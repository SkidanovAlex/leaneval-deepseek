import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThmF.ChV12

/-- If a subgroup `W` of a finite group `A` is invariant under `σ ∈ MulAut A`
(`σ x ∈ W` for all `x ∈ W`), then it is invariant under every integer power of `σ`.

Since `A` is finite, `σ` restricts to an injective self-map of the finite set `W`, hence a
bijection, so also `σ⁻¹` preserves `W`; then induction on `k`. -/
theorem zpow_mem_of_invariant {A : Type*} [Group A] [Finite A]
    (σ : MulAut A) (W : Subgroup A) (hW : ∀ x ∈ W, σ x ∈ W) :
    ∀ (k : ℤ) (x : A), x ∈ W → (σ ^ k) x ∈ W := by
  -- `σ⁻¹` also preserves `W`: `σ` restricts to an injective self-map of the finite `W`,
  -- hence a bijection, so every element of `W` is `σ y` for some `y ∈ W`.
  have hWinv : ∀ x ∈ W, σ⁻¹ x ∈ W := by
    intro x hx
    have hf : Function.Injective (fun y : W => (⟨σ y, hW y y.2⟩ : W)) := by
      intro a b hab
      have h1 : σ a = σ b := congrArg Subtype.val hab
      exact Subtype.ext (σ.injective h1)
    have hsurj := Finite.injective_iff_surjective.mp hf
    obtain ⟨y, hy⟩ := hsurj ⟨x, hx⟩
    have hval : σ y = x := congrArg Subtype.val hy
    have hthis : σ⁻¹ x = y := by rw [← hval]; simp
    rw [hthis]; exact y.2
  -- nonnegative powers preserve `W`
  have hpow : ∀ (n : ℕ) (x : A), x ∈ W → ((σ : MulAut A) ^ n) x ∈ W := by
    intro n
    induction n with
    | zero => intro x hx; simpa using hx
    | succ n ih => intro x hx; rw [pow_succ']; exact hW _ (ih x hx)
  -- nonnegative powers of `σ⁻¹` preserve `W`
  have hpowinv : ∀ (n : ℕ) (x : A), x ∈ W → ((σ⁻¹ : MulAut A) ^ n) x ∈ W := by
    intro n
    induction n with
    | zero => intro x hx; simpa using hx
    | succ n ih => intro x hx; rw [pow_succ']; exact hWinv _ (ih x hx)
  intro k x hx
  rcases lt_or_ge k 0 with hk | hk
  · -- `k < 0`: rewrite `σ ^ k = (σ⁻¹) ^ (-k)` with `-k` a positive natural
    have hpos : (0 : ℤ) < -k := by omega
    have hk'' : k = -(-k) := by ring
    rw [hk'', zpow_neg, ← inv_zpow]
    have hk3 : -k = ((-k).toNat : ℤ) := (Int.toNat_of_nonneg (le_of_lt hpos)).symm
    rw [hk3, zpow_natCast]
    exact hpowinv (-k).toNat x hx
  · -- `k ≥ 0`
    have hk' : k = (k.toNat : ℤ) := (Int.toNat_of_nonneg hk).symm
    rw [hk', zpow_natCast]
    exact hpow k.toNat x hx

end Work.ThmF.ChV12
