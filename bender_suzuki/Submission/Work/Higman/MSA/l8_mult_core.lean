import Mathlib
import Submission.Work.Higman.core_alt_pairing_new

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Higman.MSA

/-- **Higman's §4 Lemma 6, multiplicative form.**  Let `V`, `W` be finite elementary abelian
`2`-groups of order `2 ^ n` (`n ≥ 2`) with automorphisms `ξV`, `ξW` transitive on the non-identity
elements, let `B : V × V → W` be a non-zero alternating `ξ`-equivariant biadditive map, let
`s : V → W` be `ξ`-equivariant with `s 1 = 1`, trivial kernel and polar form `B`
(`s (a * b) = s a * s b * B a b`), and let `β : V × W → W` be a non-zero `ξ`-equivariant
biadditive map with `β a (s a) = 1`.  Then we reach a contradiction.

This is `Work.Higman.core_alt_pairing` (file `Submission/Work/Higman/core_alt_pairing_new.lean`,
already proved) in the multiplicative language.  Route: transport along `Additive` — `Additive V`
and `Additive W` carry `ZMod 2`-module structures via `AddCommGroup.zmodModule` fed by `hV2`,
`hW2`; `MulEquiv.toAdditive ξV` is an `AddEquiv`, and `AddEquiv.toLinearEquiv` (with a
`rcases zmod2_eq_zero_or_one`/`fin_cases`-style scalar case) makes it a `LinearEquiv`; then
transfer `B`, `s`, `β` through `Additive.ofMul` and apply `Work.Higman.core_alt_pairing`.
Note `hspol` in multiplicative form is `s (a * b) = s a * s b * B a b`, which matches the
additive `s (a + b) + s a + s b = B a b` of the core in characteristic two. -/
theorem l8_mult_core {V W : Type} [CommGroup V] [CommGroup W] [Finite V] [Finite W]
    (hV2 : ∀ v : V, v * v = 1) (hW2 : ∀ w : W, w * w = 1)
    {n : ℕ} (hn : 2 ≤ n) (hVcard : Nat.card V = 2 ^ n) (hWcard : Nat.card W = 2 ^ n)
    (ξV : V ≃* V) (ξW : W ≃* W)
    (hVtrans : ∀ a b : V, a ≠ 1 → b ≠ 1 → ∃ k : ℕ, (ξV ^ k) a = b)
    (hWtrans : ∀ a b : W, a ≠ 1 → b ≠ 1 → ∃ k : ℕ, (ξW ^ k) a = b)
    (B : V → V → W) (hB1 : ∀ a b c : V, B (a * b) c = B a c * B b c)
    (hB2 : ∀ a b c : V, B a (b * c) = B a b * B a c) (hBdiag : ∀ a : V, B a a = 1)
    (hBeq : ∀ a b : V, ξW (B a b) = B (ξV a) (ξV b)) (hBne : ∃ a b : V, B a b ≠ 1)
    (s : V → W) (hs1 : s 1 = 1) (hseq : ∀ a : V, ξW (s a) = s (ξV a))
    (hspol : ∀ a b : V, s (a * b) = s a * s b * B a b)
    (hsne : ∀ a : V, a ≠ 1 → s a ≠ 1)
    (β : V → W → W) (hβ1 : ∀ a a' : V, ∀ b : W, β (a * a') b = β a b * β a' b)
    (hβ2 : ∀ a : V, ∀ b b' : W, β a (b * b') = β a b * β a b')
    (hβeq : ∀ a : V, ∀ b : W, ξW (β a b) = β (ξV a) (ξW b))
    (hβrel : ∀ a : V, β a (s a) = 1) (hβne : ∃ a : V, ∃ b : W, β a b ≠ 1) : False := by
  classical
  -- `ZMod 2` has exactly two elements.
  have hz2 : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by
    intro c
    fin_cases c
    · exact Or.inl rfl
    · exact Or.inr rfl
  -- The exponent-two hypothesis turns `Additive V`, `Additive W` into `ZMod 2`-modules.
  haveI hmodV : Module (ZMod 2) (Additive V) :=
    AddCommGroup.zmodModule fun x => by
      rw [show (2 : ℕ) • x = x + x from two_nsmul x]
      have hx : x + x = Additive.ofMul ((Additive.toMul x) * (Additive.toMul x)) := rfl
      rw [hx, hV2 (Additive.toMul x)]
      rfl
  haveI hmodW : Module (ZMod 2) (Additive W) :=
    AddCommGroup.zmodModule fun x => by
      rw [show (2 : ℕ) • x = x + x from two_nsmul x]
      have hx : x + x = Additive.ofMul ((Additive.toMul x) * (Additive.toMul x)) := rfl
      rw [hx, hW2 (Additive.toMul x)]
      rfl
  have ht0V : Additive.toMul (0 : Additive V) = 1 := rfl
  have ht0W : Additive.toMul (0 : Additive W) = 1 := rfl
  have hzV : ∀ a : Additive V, Additive.toMul a = 1 → a = 0 := by
    intro a h
    rw [← ofMul_toMul a, h, ← ofMul_toMul (0 : Additive V), ht0V]
  have hzW : ∀ a : Additive W, Additive.toMul a = 1 → a = 0 := by
    intro a h
    rw [← ofMul_toMul a, h, ← ofMul_toMul (0 : Additive W), ht0W]
  -- The automorphisms `ξV`, `ξW` as `ZMod 2`-linear automorphisms of `Additive V`, `Additive W`.
  let ζV : (Additive V) ≃ₗ[ZMod 2] (Additive V) :=
    { toFun := fun x => Additive.ofMul (ξV (Additive.toMul x))
      invFun := fun x => Additive.ofMul (ξV.symm (Additive.toMul x))
      left_inv := fun x => by
        show Additive.ofMul (ξV.symm (ξV (Additive.toMul x))) = x
        rw [MulEquiv.symm_apply_apply, ofMul_toMul]
      right_inv := fun x => by
        show Additive.ofMul (ξV (ξV.symm (Additive.toMul x))) = x
        rw [MulEquiv.apply_symm_apply, ofMul_toMul]
      map_add' := fun x y => by
        show Additive.ofMul (ξV (Additive.toMul (x + y)))
          = Additive.ofMul (ξV (Additive.toMul x)) + Additive.ofMul (ξV (Additive.toMul y))
        rw [toMul_add, map_mul, ofMul_mul]
      map_smul' := fun c x => by
        rcases hz2 c with rfl | rfl <;> simp }
  let ζW : (Additive W) ≃ₗ[ZMod 2] (Additive W) :=
    { toFun := fun x => Additive.ofMul (ξW (Additive.toMul x))
      invFun := fun x => Additive.ofMul (ξW.symm (Additive.toMul x))
      left_inv := fun x => by
        show Additive.ofMul (ξW.symm (ξW (Additive.toMul x))) = x
        rw [MulEquiv.symm_apply_apply, ofMul_toMul]
      right_inv := fun x => by
        show Additive.ofMul (ξW (ξW.symm (Additive.toMul x))) = x
        rw [MulEquiv.apply_symm_apply, ofMul_toMul]
      map_add' := fun x y => by
        show Additive.ofMul (ξW (Additive.toMul (x + y)))
          = Additive.ofMul (ξW (Additive.toMul x)) + Additive.ofMul (ξW (Additive.toMul y))
        rw [toMul_add, map_mul, ofMul_mul]
      map_smul' := fun c x => by
        rcases hz2 c with rfl | rfl <;> simp }
  have hζV : ∀ x : Additive V, ζV x = Additive.ofMul (ξV (Additive.toMul x)) := fun _ => rfl
  have hζW : ∀ x : Additive W, ζW x = Additive.ofMul (ξW (Additive.toMul x)) := fun _ => rfl
  have hζVpow : ∀ (k : ℕ) (x : Additive V),
      (ζV ^ k) x = Additive.ofMul ((ξV ^ k) (Additive.toMul x)) := by
    intro k
    induction k with
    | zero => intro x; rfl
    | succ k ih =>
        intro x
        rw [pow_succ, LinearEquiv.mul_apply, ih, hζV, toMul_ofMul, pow_succ]
        rfl
  have hζWpow : ∀ (k : ℕ) (x : Additive W),
      (ζW ^ k) x = Additive.ofMul ((ξW ^ k) (Additive.toMul x)) := by
    intro k
    induction k with
    | zero => intro x; rfl
    | succ k ih =>
        intro x
        rw [pow_succ, LinearEquiv.mul_apply, ih, hζW, toMul_ofMul, pow_succ]
        rfl
  have h1 : ∀ a : Additive V, Additive.toMul (ζV a) = ξV (Additive.toMul a) := by
    intro a; rw [hζV, toMul_ofMul]
  refine Work.Higman.core_alt_pairing (V := Additive V) (W := Additive W) hn hVcard hWcard
    ζV ζW
    (fun a b ha hb => ?_)
    (fun a b ha hb => ?_)
    (fun x y => Additive.ofMul (B (Additive.toMul x) (Additive.toMul y)))
    (fun a b c => ?_) (fun a b c => ?_) (fun a => ?_)
    (fun a b => ?_) (by
      obtain ⟨a, b, hab⟩ := hBne
      exact ⟨Additive.ofMul a, Additive.ofMul b, fun h => hab (by simpa using h)⟩)
    (fun x => Additive.ofMul (s (Additive.toMul x)))
    (by
      show Additive.ofMul (s (Additive.toMul (0 : Additive V))) = 0
      rw [show Additive.toMul (0 : Additive V) = 1 from rfl, hs1]
      rfl)
    (fun a => ?_)
    (fun a b => ?_)
    (fun a ha h0 => ?_)
    (fun x y => Additive.ofMul (β (Additive.toMul x) (Additive.toMul y)))
    (fun a a' b => ?_) (fun a b b' => ?_) (fun a b => ?_)
    (fun a => ?_) (by
      obtain ⟨a, b, hab⟩ := hβne
      exact ⟨Additive.ofMul a, Additive.ofMul b, fun h => hab (by simpa using h)⟩)
  · obtain ⟨k, hk⟩ := hVtrans _ _ (fun h => ha (hzV a h)) (fun h => hb (hzV b h))
    exact ⟨k, by rw [hζVpow k a]; exact congrArg Additive.ofMul hk⟩
  · obtain ⟨k, hk⟩ := hWtrans _ _ (fun h => ha (hzW a h)) (fun h => hb (hzW b h))
    exact ⟨k, by rw [hζWpow k a]; exact congrArg Additive.ofMul hk⟩
  · show Additive.ofMul (B (Additive.toMul (a + b)) (Additive.toMul c))
      = Additive.ofMul (B (Additive.toMul a) (Additive.toMul c))
        + Additive.ofMul (B (Additive.toMul b) (Additive.toMul c))
    rw [toMul_add, hB1, ofMul_mul]
  · show Additive.ofMul (B (Additive.toMul a) (Additive.toMul (b + c)))
      = Additive.ofMul (B (Additive.toMul a) (Additive.toMul b))
        + Additive.ofMul (B (Additive.toMul a) (Additive.toMul c))
    rw [toMul_add, hB2, ofMul_mul]
  · show Additive.ofMul (B (Additive.toMul a) (Additive.toMul a)) = 0
    rw [hBdiag]; rfl
  · show Additive.ofMul (ξW (Additive.toMul (Additive.ofMul (B (Additive.toMul a) (Additive.toMul b)))))
      = Additive.ofMul (B (Additive.toMul (ζV a)) (Additive.toMul (ζV b)))
    rw [toMul_ofMul, h1 a, h1 b, hBeq]
  · show Additive.ofMul (ξW (s (Additive.toMul a))) = Additive.ofMul (s (Additive.toMul (ζV a)))
    rw [h1 a, hseq]
  · rw [← ofMul_mul, ← ofMul_mul]
    congr 1
    rw [toMul_add, hspol (Additive.toMul a) (Additive.toMul b)]
    have key : (s (Additive.toMul a) * s (Additive.toMul b) * B (Additive.toMul a) (Additive.toMul b))
        * s (Additive.toMul a) * s (Additive.toMul b)
        = B (Additive.toMul a) (Additive.toMul b)
          * (s (Additive.toMul a) * s (Additive.toMul a))
          * (s (Additive.toMul b) * s (Additive.toMul b)) := by
      simp only [mul_left_comm, mul_comm, mul_assoc]
    rw [key, hW2 (s (Additive.toMul a)), hW2 (s (Additive.toMul b)), mul_one, mul_one]
  · have hh : Additive.ofMul (s (Additive.toMul a)) = Additive.ofMul (1 : W) := by
      rw [h0, ← ht0W]; rfl
    refine hsne (Additive.toMul a) (fun h1 => ha (hzV a h1)) ?_
    have h2 := congrArg Additive.toMul hh
    rw [toMul_ofMul, toMul_ofMul] at h2
    exact h2
  · show Additive.ofMul (β (Additive.toMul (a + a')) (Additive.toMul b))
      = Additive.ofMul (β (Additive.toMul a) (Additive.toMul b))
        + Additive.ofMul (β (Additive.toMul a') (Additive.toMul b))
    rw [toMul_add, hβ1, ofMul_mul]
  · show Additive.ofMul (β (Additive.toMul a) (Additive.toMul (b + b')))
      = Additive.ofMul (β (Additive.toMul a) (Additive.toMul b))
        + Additive.ofMul (β (Additive.toMul a) (Additive.toMul b'))
    rw [toMul_add, hβ2, ofMul_mul]
  · show Additive.ofMul (ξW (β (Additive.toMul a) (Additive.toMul b)))
      = Additive.ofMul (β (Additive.toMul (ζV a)) (ξW (Additive.toMul b)))
    rw [h1 a, hβeq]
  · show Additive.ofMul (β (Additive.toMul a) (s (Additive.toMul a))) = 0
    rw [hβrel]; rfl

end Work.Higman.MSA
