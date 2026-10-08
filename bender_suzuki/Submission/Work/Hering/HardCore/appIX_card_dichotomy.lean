import Mathlib
import Submission.Work.Hering.GL32.AppIXDefs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The degree/cardinality dichotomy of Appendix IX

A finite irreducible `𝔽₂[GL(3,2)]`-module has dimension `1`, `3` or `8`
(`Work.Hering.AppIXProp`, Appendix IX of Peterfalvi I).  Consequently, if a finite
commutative group `Q` of exponent two carries an irreducible action of `GL(3,2)` by
group automorphisms, then `|Q| = 2^1`, `2^3` or `2^8`, i.e. `|Q| ∈ {2, 8, 256}`.

The bridge from the multiplicative group `Q` to the `𝔽₂`-vector space is the type
synonym `Additive Q`: the additive structure it carries turns `Q` into a `ZMod 2`-module
(`AddCommGroup.zmodModule`), on which every multiplicative automorphism of `Q` acts
linearly.  Under the order isomorphisms
`Subgroup Q ≃o AddSubgroup (Additive Q) ≃o Submodule (ZMod 2) (Additive Q)`
the hypothesis `hirr` is exactly irreducibility of the module.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open Work.Hering

namespace Work.Hering.HardCore

theorem appIX_card_dichotomy {Q : Type} [CommGroup Q] [Finite Q]
    (hIX : Work.Hering.AppIXProp) (hexp : ∀ x : Q, x * x = 1)
    (ρ : Work.Hering.GL32 →* MulAut Q)
    (hnt : ∃ q : Q, q ≠ 1)
    (hirr : ∀ S : Subgroup Q, (∀ g : Work.Hering.GL32, ∀ x ∈ S, (ρ g) x ∈ S) →
      S = ⊥ ∨ S = ⊤) :
    Nat.card Q = 2 ∨ Nat.card Q = 8 ∨ Nat.card Q = 256 := by
  -- `Q` has exponent two, so `Additive Q` is a `ZMod 2`-module.
  have h2 : ∀ x : Additive Q, 2 • x = 0 := by
    intro x
    induction x using Additive.rec with
    | ofMul q => rw [← ofMul_pow, pow_two, hexp q, ofMul_one]
  letI : Module (ZMod 2) (Additive Q) := AddCommGroup.zmodModule h2
  -- Every multiplicative automorphism of `Q` is `ZMod 2`-linear.
  let toLinHom : MulAut Q →* (Additive Q ≃ₗ[ZMod 2] Additive Q) :=
  { toFun := fun e =>
      let f : Additive Q ≃+ Additive Q := MulEquiv.toAdditive e
      LinearEquiv.mk (AddMonoidHom.toZModLinearMap 2 (f : Additive Q →+ Additive Q))
        (⇑f.symm) f.left_inv f.right_inv
    map_one' := by ext x; rfl
    map_mul' := by intro a b; ext x; rfl }
  let ρL : GL32 →* (Additive Q ≃ₗ[ZMod 2] Additive Q) := toLinHom.comp ρ
  have hrel : ∀ (g : GL32) (x : Q), (ρL g) (Additive.ofMul x) = Additive.ofMul ((ρ g) x) := by
    intro g x; rfl
  -- Non-triviality transfers to the module.
  have hnt' : ∃ m : Additive Q, m ≠ 0 := by
    obtain ⟨q, hq⟩ := hnt
    exact ⟨Additive.ofMul q, fun h => hq (by simpa using congrArg Additive.toMul h)⟩
  -- Subgroup-irreducibility transfers to submodule-irreducibility.
  have hirr' : ∀ W : Submodule (ZMod 2) (Additive Q),
      (∀ g : GL32, ∀ w ∈ W, ρL g w ∈ W) → W = ⊥ ∨ W = ⊤ := by
    intro W hW
    let φ : Subgroup Q ≃o Submodule (ZMod 2) (Additive Q) :=
      Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule 2)
    let S : Subgroup Q := φ.symm W
    have hφS : φ S = W := OrderIso.apply_symm_apply φ W
    have hmem : ∀ x : Q, x ∈ S ↔ Additive.ofMul x ∈ W := by
      intro x
      rw [← hφS]
      show x ∈ S ↔ Additive.ofMul x ∈ φ S
      exact (AddSubgroup.mem_toZModSubmodule 2).trans
        (Additive.mem_toAddSubgroup S (Additive.ofMul x))
    have hinvS : ∀ g : GL32, ∀ x ∈ S, (ρ g) x ∈ S := by
      intro g x hx
      rw [hmem] at hx ⊢
      rw [← hrel g x]
      exact hW g (Additive.ofMul x) hx
    rcases hirr S hinvS with hbot | htop
    · left
      have : W = φ ⊥ := by rw [← hφS, hbot]
      rw [this, OrderIso.map_bot]
    · right
      have : W = φ ⊤ := by rw [← hφS, htop]
      rw [this, OrderIso.map_top]
  -- Appendix IX.
  have hdim := hIX ρL hnt' hirr'
  haveI : Module.Finite (ZMod 2) (Additive Q) :=
    Module.Finite.of_finite (R := ZMod 2) (M := Additive Q)
  have hcard : Nat.card Q = 2 ^ Module.finrank (ZMod 2) (Additive Q) :=
    calc Nat.card Q = Nat.card (Additive Q) := Nat.card_congr Additive.ofMul
      _ = Nat.card (ZMod 2) ^ Module.finrank (ZMod 2) (Additive Q) :=
            Module.natCard_eq_pow_finrank
      _ = 2 ^ Module.finrank (ZMod 2) (Additive Q) := by rw [Nat.card_zmod]
  rcases hdim with h | h | h
  · left; rw [hcard, h]; norm_num
  · right; left; rw [hcard, h]; norm_num
  · right; right; rw [hcard, h]; norm_num

end Work.Hering.HardCore
