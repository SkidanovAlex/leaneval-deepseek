import Mathlib.GroupTheory.Nilpotent
import Mathlib.Tactic.Have
import Mathlib.Algebra.Field.ZMod
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Data.Int.Star
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.extH_natCard_smul_eq_zero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! Guidance from the project lead (the requester): read `DESIGN_FIX.md` §1 ("E5s").

# `H²(G, 𝔽_p)` at levels of degree prime to `p`

Two elementary inputs of the dévissage `Work.SSGRoute.phi1_mono_step_in` (node E5s):

* `extH_trivial_zmodp_smul_eq_zero` — `Hⁿ(G, 𝔽_p)` is killed by `p`, because the coefficients
  `ZMod p` are;
* `subsingleton_extH_trivial_two_of_not_dvd_card` — hence `H²(G, 𝔽_p) = 0` when `p ∤ |G|` (Bézout
  with `|G| • y = 0`, `Work.SSGRoute.extH_natCard_smul_eq_zero`).

`DESIGN_FIX.md` §1 step 2 uses the second statement to say that the levels `L` with `p ∤ [L : k]`
"contribute nothing" to the colimit of the `H²(Gal(L/k), 𝔽_p)`. -/

universe u₁ v₁

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory

attribute [local instance 10000] Rep.hV2 Rep.hV1 Submodule.module

/-- Bilinearity of `Abelian.Ext.comp` in the second variable, in `ℕ`-multiples
(the companion of `Work.SSGRoute.nsmul_comp_aux`). -/
lemma comp_nsmul_aux {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasExt.{0} C]
    {X Y Z : C} {a b c : ℕ} (n : ℕ) (α : Abelian.Ext X Y a) (β : Abelian.Ext Y Z b)
    (h : a + b = c) : α.comp (n • β) h = n • (α.comp β h) := by
  induction n with
  | zero => rw [zero_nsmul, zero_nsmul, Abelian.Ext.comp_zero]
  | succ k ih =>
      rw [succ_nsmul', succ_nsmul', Abelian.Ext.comp_add, ih]

/-- **`Hⁿ(G, 𝔽_p)` is killed by `p`.**  The coefficients `ZMod p` are annihilated by `p`, so the
identity of the trivial representation is, and `p • x = x.comp (mk₀ (p • 𝟙 _))` by bilinearity. -/
theorem extH_trivial_zmodp_smul_eq_zero (p : ℕ) {G : Type} [Group G] {n : ℕ}
    (y : extH (Rep.trivial Coeff G (ZMod p)) n) : p • y = 0 := by
  have hone : (p : ℕ) • (𝟙 (Rep.trivial Coeff G (ZMod p))) = 0 := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    rw [Rep.nsmul_hom]
    rw [show (p • Rep.Hom.hom (𝟙 (Rep.trivial Coeff G (ZMod p)))).toLinearMap v
        = p • ((Rep.Hom.hom (𝟙 (Rep.trivial Coeff G (ZMod p)))).toLinearMap v) from rfl]
    simpa using (show p • v = 0 by rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul])
  have hid : p • y
      = y.comp (Abelian.Ext.mk₀ (p • (𝟙 (Rep.trivial Coeff G (ZMod p))))) (add_zero n) := by
    rw [mk₀_nsmul_aux p (𝟙 (Rep.trivial Coeff G (ZMod p)))]
    rw [comp_nsmul_aux p y (Abelian.Ext.mk₀ (𝟙 (Rep.trivial Coeff G (ZMod p)))) (add_zero n)]
    rw [Abelian.Ext.comp_mk₀_id]
  rw [hid, hone, Abelian.Ext.mk₀_zero]
  exact Abelian.Ext.comp_zero y _ 0 n (add_zero n)

/-- **`H²(G, 𝔽_p) = 0` when `p ∤ |G|`.**  `y` is killed both by `p`
(`extH_trivial_zmodp_smul_eq_zero`) and by `|G|` (`Work.SSGRoute.extH_natCard_smul_eq_zero`),
which are coprime; Bézout finishes. -/
theorem subsingleton_extH_trivial_two_of_not_dvd_card (p : ℕ) [Fact p.Prime] {G : Type}
    [Group G] [Fintype G] (hp : ¬ p ∣ Nat.card G) :
    Subsingleton (extH (Rep.trivial Coeff G (ZMod p)) 2) := by
  have hzero : ∀ y : extH (Rep.trivial Coeff G (ZMod p)) 2, y = 0 := by
    intro y
    have hpy : p • y = 0 := extH_trivial_zmodp_smul_eq_zero p y
    have hGy : Nat.card G • y = 0 :=
      extH_natCard_smul_eq_zero (Rep.trivial Coeff G (ZMod p)) (by norm_num) y
    have hcop : Nat.Coprime p (Nat.card G) := (Fact.out : p.Prime).coprime_iff_not_dvd.mpr hp
    have hbez : (p : ℤ) * (Nat.gcdA p (Nat.card G))
        + (Nat.card G : ℤ) * (Nat.gcdB p (Nat.card G)) = 1 := by
      have h := Nat.gcd_eq_gcd_ab p (Nat.card G)
      rw [hcop.gcd_eq_one, Nat.cast_one] at h
      linarith [h]
    have hpy' : (p : ℤ) • y = 0 := by
      rw [Nat.cast_smul_eq_nsmul ℤ p]; exact hpy
    have hGy' : (Nat.card G : ℤ) • y = 0 := by
      rw [Nat.cast_smul_eq_nsmul ℤ (Nat.card G)]; exact hGy
    calc y = (1 : ℤ) • y := (one_smul _ _).symm
      _ = ((p : ℤ) * (Nat.gcdA p (Nat.card G))
            + (Nat.card G : ℤ) * (Nat.gcdB p (Nat.card G))) • y := by rw [hbez]
      _ = (Nat.gcdA p (Nat.card G)) • ((p : ℤ) • y)
            + (Nat.gcdB p (Nat.card G)) • ((Nat.card G : ℤ) • y) := by
            rw [add_smul, mul_smul, mul_smul,
              smul_comm (p : ℤ) (Nat.gcdA p (Nat.card G)) y,
              smul_comm (Nat.card G : ℤ) (Nat.gcdB p (Nat.card G)) y]
      _ = 0 := by rw [hpy', hGy']; simp
  exact ⟨fun a b => by rw [hzero a, hzero b]⟩

/-- **The level form of `subsingleton_extH_trivial_two_of_not_dvd_card`.**  If `L` is a finite
Galois level over `k` of degree prime to `p` (equivalently, `p ∤ |Gal(L/k)|`), then
`H²(Gal(L/k), 𝔽_p) = 0`; this is why the levels of degree prime to `p` "contribute nothing" to the
colimit of `DESIGN_FIX.md` §1. -/
theorem subsingleton_extH_trivial_two_of_level (p : ℕ) [Fact p.Prime] {k K Ω : Type} [Field k]
    [NumberField k] [Field K] [NumberField K] [Algebra k K] [Field Ω] [Algebra K Ω] [Algebra k Ω]
    [IsScalarTower k K Ω] (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L]
    [IsGalois k L] (hp : ¬ p ∣ Nat.card (↥L ≃ₐ[k] ↥L)) :
    Subsingleton (extH (Rep.trivial Coeff (↥L ≃ₐ[k] ↥L) (ZMod p)) 2) :=
  subsingleton_extH_trivial_two_of_not_dvd_card p hp

end Work.SSGRoute
