import Mathlib
import Submission.Work.ThmF.ChV12.irreducible_pgroup_finrank_ge

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThmF.ChV12

/-!
# The Bender lemma: an odd `p`-subgroup of `Aut(A)` with an irreducible element is abelian

Let `A` be a finite elementary abelian `2`-group (`∀ x, x * x = 1`), of order `A = 2 ^ k`, let
`p` be an odd prime with `k < p`, and let `P ≤ MulAut A` be a `p`-subgroup.  If `P` contains an
element `σ` acting irreducibly on `A` (its only `σ`-invariant subgroups are `⊥` and `⊤`), then
`P` is commutative.

The argument.  Viewing `A` as an `𝔽₂`-vector space (`A = Additive A` as a `ZMod 2`-module), the
element `σ` makes `A` a *cyclic* `𝔽₂[⟨σ⟩]`-module: every nonzero `a` generates `A` under `σ`.
Since `𝔽₂[⟨σ⟩] ⊆ 𝔽₂[P]`, this means that `A` is an irreducible `𝔽₂[P]`-module.  The
representation `P →* (A ≃ₗ[ZMod 2] A)` is faithful and irreducible, so by the dimension bound
`irreducible_pgroup_finrank_ge` a *nonabelian* `p`-group `P` would force
`p ≤ finrank (ZMod 2) A = k`, contradicting `k < p`.  Hence `P` is commutative.
-/

theorem isMulCommutative_of_isPGroup_of_irreducible {A : Type} [Group A] [Finite A]
    (hA2 : ∀ x : A, x * x = 1) (hAc : ∀ x y : A, x * y = y * x) {k p : ℕ}
    (hk : Nat.card A = 2 ^ k) (hp : Nat.Prime p) (hodd : p ≠ 2) (hkp : k < p)
    (P : Subgroup (MulAut A)) (hP : IsPGroup p ↥P)
    (hirr : ∃ σ ∈ P, ∀ W : Subgroup A, W ≠ ⊥ → (∀ x ∈ W, σ x ∈ W) → W = ⊤) :
    IsMulCommutative ↥P := by
  by_contra hnab
  -- `A` is a commutative group, hence `Additive A` is an `𝔽₂`-vector space
  letI : CommGroup A := { ‹Group A› with mul_comm := hAc }
  have h2 : ∀ x : Additive A, (2 : ℕ) • x = 0 := by
    intro x
    rw [← ofMul_toMul x, two_nsmul, ← ofMul_mul, hA2, ofMul_one]
  letI : Module (ZMod 2) (Additive A) := AddCommGroup.zmodModule h2
  -- the faithful irreducible representation of `P` on `A`
  let φ : ↥P →* (Additive A ≃ₗ[ZMod 2] Additive A) :=
    { toFun := fun g => (g : MulAut A).toAdditive.toLinearEquiv (fun c x => by
        change (g : MulAut A).toAdditive ((c.val : ℕ) • x)
          = (c.val : ℕ) • (g : MulAut A).toAdditive x
        exact map_nsmul _ _ _)
      map_one' := by ext x; simp
      map_mul' := by intro g h; ext x; simp }
  have hfaith : Function.Injective φ := by
    intro g h hgh
    apply Subtype.ext
    apply MulEquiv.ext
    intro a
    have h1 : (φ g) (Additive.ofMul a) = Additive.ofMul ((g : MulAut A) a) := rfl
    have h2' : (φ h) (Additive.ofMul a) = Additive.ofMul ((h : MulAut A) a) := rfl
    have := congrArg (fun (e : Additive A ≃ₗ[ZMod 2] Additive A) => e (Additive.ofMul a)) hgh
    rw [h1, h2'] at this
    exact Additive.ofMul.injective this
  -- irreducibility of `A` as an `𝔽₂[P]`-module, transported from `hirr`
  have hirr' : ∀ W : Submodule (ZMod 2) (Additive A), W ≠ ⊥ →
      (∀ g : ↥P, ∀ x ∈ W, φ g x ∈ W) → W = ⊤ := by
    intro W hWne hWinv
    obtain ⟨σ, hσP, hσirr⟩ := hirr
    -- the subgroup of `A` underlying `W`
    let S : Subgroup A :=
      { carrier := {a : A | Additive.ofMul a ∈ W}
        one_mem' := by show Additive.ofMul (1 : A) ∈ W; rw [ofMul_one]; exact W.zero_mem
        mul_mem' := by
          intro a b ha hb
          show Additive.ofMul (a * b) ∈ W
          rw [ofMul_mul]; exact W.add_mem ha hb
        inv_mem' := by
          intro a ha
          show Additive.ofMul a⁻¹ ∈ W
          rw [ofMul_inv]; exact W.neg_mem ha }
    have hSne : S ≠ ⊥ := by
      intro hbot
      apply hWne
      rw [Submodule.eq_bot_iff]
      intro x hx
      have : x.toMul ∈ S := hx
      rw [hbot] at this
      have h1 : x.toMul = 1 := Subgroup.mem_bot.mp this
      rw [← ofMul_toMul x, h1, ofMul_one]
    have hinv : ∀ x ∈ S, σ x ∈ S := by
      intro x hx
      show Additive.ofMul (σ x) ∈ W
      have hx' : φ ⟨σ, hσP⟩ (Additive.ofMul x) = Additive.ofMul (σ x) := rfl
      rw [← hx']
      exact hWinv ⟨σ, hσP⟩ _ hx
    have hStop : S = ⊤ := hσirr S hSne hinv
    rw [Submodule.eq_top_iff']
    intro x
    have : x.toMul ∈ S := hStop ▸ Subgroup.mem_top x.toMul
    show Additive.ofMul x.toMul ∈ W
    exact this
  -- the dimension bound forces `p ≤ k`
  have hcr : p ≤ Module.finrank (ZMod 2) (Additive A) :=
    irreducible_pgroup_finrank_ge hp hodd hP hnab (Additive A) φ hfaith hirr'
  have hfin : Module.finrank (ZMod 2) (Additive A) = k := by
    haveI : Fintype (Additive A) := Fintype.ofFinite _
    have h1 : Fintype.card (Additive A)
        = Fintype.card (ZMod 2) ^ Module.finrank (ZMod 2) (Additive A) :=
      Module.card_eq_pow_finrank
    rw [ZMod.card] at h1
    have h2c : Fintype.card (Additive A) = 2 ^ k := by
      rw [← Nat.card_eq_fintype_card]
      rw [Nat.card_congr (Additive.toMul : Additive A ≃ A), hk]
    rw [h2c] at h1
    exact Nat.pow_right_injective (by norm_num : 1 < 2) h1.symm
  omega

end Work.ThmF.ChV12
