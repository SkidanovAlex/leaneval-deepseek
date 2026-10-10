import Mathlib
import Submission.Work.MotV5.Nodes.valuationSubringLyingOver
import Submission.Work.MotV5.Nodes.maxValueAttainedTwice
import Submission.Work.MotV5.Nodes.powFactorialMemValueGroup

set_option linter.unusedVariables false -- v435-speed

namespace Work.MotV5.Nodes

open Valuation MonoidWithZeroHom

universe u

/-!
# Extension of a valuation to a finite extension

A complete proof of Krull/Chevalley-type extension of valuations.  The mathematical statement
proved here (see `valuation_extends_finiteDimensional_gen`) is:

given a valuation `v : F →₀ Γ₀` on a field `F` and a finite extension `L/F`, there is a value
group `Γ₁`, a strictly monotone monoid-with-zero hom `f : Γ₀ →*₀ Γ₁` and a valuation `w` on `L`
with `w (algebraMap F L x) = f (v x)` for all `x : F`.

The construction is: take a valuation subring `B ⊆ L` lying over the valuation ring of `v`
(`valuationSubringLyingOver`), use the valuation `B.valuation : L → B.ValueGroup`, and normalise
by an `E := (finrank F L)!`-th power so that the restricted valuation on `F` becomes equivalent
to an actual `E`-th power of `v`; then `Γ₁ := Γ₀` and `f := (· ^ E)`.

## A note on universes

`Type*`-polymorphism matters here: the value group `Γ₁` built below is literally `Γ₀`, hence lives
in the *same* universe as `Γ₀`.  The statement with `∃ (Γ₁ : Type)` (i.e. `Γ₁` confined to
`Type 0`, as in the formally more restrictive version) is not true for `Γ₀` in a higher universe:
`StrictMono` on a linear order is injective, so it would assert an injection of every linearly
ordered commutative group-with-zero into a type of `Type 0`, which is impossible for large `Γ₀`.
-/

/-- A valuation on a field extends to a finite extension of fields, with an order embedding of
value groups (the value group `Γ₁` may be taken to be `Γ₀` itself, enlarged by an `E`-th power). -/
theorem valuation_extends_finiteDimensional_gen {Γ₀ : Type u} {F L : Type*}
    [Field F] [Field L] [Algebra F L] [FiniteDimensional F L]
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation F Γ₀) :
    ∃ (Γ₁ : Type u) (_ : LinearOrderedCommGroupWithZero Γ₁) (f : Γ₀ →*₀ Γ₁)
      (_ : StrictMono f) (w : Valuation L Γ₁),
      ∀ x : F, w (algebraMap F L x) = f (v x) := by
  classical
  obtain ⟨B, hB⟩ := valuationSubringLyingOver (L := L) v
  -- ## Step 1: `B.valuation` restricts to a valuation equivalent to `v` on `F`.
  have hsub : (B.valuation.comap (algebraMap F L)).valuationSubring = v.valuationSubring := by
    ext x
    rw [Valuation.mem_valuationSubring_iff, Valuation.mem_valuationSubring_iff]
    show B.valuation (algebraMap F L x) ≤ 1 ↔ v x ≤ 1
    rw [ValuationSubring.valuation_le_one_iff, hB x, Valuation.mem_valuationSubring_iff]
  have hiso : (B.valuation.comap (algebraMap F L)).IsEquiv v :=
    (Valuation.isEquiv_iff_valuationSubring _ v).mpr hsub
  -- ## Step 2: the order isomorphism `Φ` of the value groups, and `Ψ := embedding ∘ Φ`.
  have hΦ0 : hiso.orderMonoidIso 0 = 0 := by
    refine le_antisymm ?_ zero_le
    have h : hiso.orderMonoidIso 0 ≤ hiso.orderMonoidIso (hiso.orderMonoidIso.symm 0) :=
      hiso.orderMonoidIso.map_le_map_iff'.mpr zero_le
    simpa using h
  let Ψ : (MonoidWithZeroHom.ofClass (B.valuation.comap (algebraMap F L))).ValueGroup₀ →*₀ Γ₀ :=
    MonoidWithZeroHom.mk
      ⟨fun x => ValueGroup₀.embedding (hiso.orderMonoidIso x), by
        show ValueGroup₀.embedding (hiso.orderMonoidIso 0) = 0
        rw [hΦ0]
        exact map_zero _⟩
      (by
        show ValueGroup₀.embedding (hiso.orderMonoidIso 1) = 1
        rw [show hiso.orderMonoidIso 1 = 1 from map_one _]
        exact map_one _)
      (by
        intro x y
        show ValueGroup₀.embedding (hiso.orderMonoidIso (x * y)) =
          ValueGroup₀.embedding (hiso.orderMonoidIso x) * ValueGroup₀.embedding (hiso.orderMonoidIso y)
        rw [show hiso.orderMonoidIso (x * y) = hiso.orderMonoidIso x * hiso.orderMonoidIso y
          from map_mul _ _ _]
        rw [map_mul])
  have hΨspec : ∀ a : F,
      Ψ (ValueGroup₀.restrict₀ (MonoidWithZeroHom.ofClass (B.valuation.comap (algebraMap F L))) a)
        = v a := by
    intro a
    show ValueGroup₀.embedding
      (hiso.orderMonoidIso (ValueGroup₀.restrict₀
        (MonoidWithZeroHom.ofClass (B.valuation.comap (algebraMap F L))) a)) = v a
    erw [Valuation.IsEquiv.orderMonoidIso_spec₀ hiso a]
    simpa using ValueGroup₀.embedding_restrict₀ (f := MonoidWithZeroHom.ofClass v) a
  have hΨmono : Monotone Ψ := by
    intro x y hxy
    change ValueGroup₀.embedding (hiso.orderMonoidIso x) ≤
      ValueGroup₀.embedding (hiso.orderMonoidIso y)
    exact ValueGroup₀.embedding_strictMono.monotone
      (hiso.orderMonoidIso.map_le_map_iff'.mpr hxy)
  -- ## Step 3: `E`-th powers of values lie in the value group of the restriction.
  have hmem : ∀ (b : B.ValueGroup) (hb : b ≠ 0),
      (Units.mk0 b hb) ^ (Module.finrank F L).factorial ∈
        MonoidWithZeroHom.valueGroup
          (MonoidWithZeroHom.ofClass (B.valuation.comap (algebraMap F L))) := by
    intro b hb
    obtain ⟨x, hx⟩ := ValuationSubring.valuation_surjective B b
    subst hx
    exact powFactorialMemValueGroup (F := F) B.valuation hb
  -- ## Step 4: the hom `ψ : B.ValueGroup →*₀ Γ₀`.
  let ψfun : B.ValueGroup → Γ₀ := fun b => if hb : b = 0 then 0 else
    Ψ ↑(⟨(Units.mk0 b hb) ^ (Module.finrank F L).factorial, hmem b hb⟩ :
      (MonoidWithZeroHom.ofClass (B.valuation.comap (algebraMap F L))).valueGroup)
  have hψ0 : ψfun 0 = 0 := by simp [ψfun]
  have hψ1 : ψfun 1 = 1 := by
    simp only [ψfun, one_ne_zero, dif_neg, not_false_eq_true]
    have hone : (⟨(Units.mk0 (1 : B.ValueGroup) one_ne_zero) ^ (Module.finrank F L).factorial,
          hmem 1 one_ne_zero⟩ :
          (MonoidWithZeroHom.ofClass (B.valuation.comap (algebraMap F L))).valueGroup)
        = ⟨1, one_mem _⟩ := by
      apply Subtype.ext
      apply Units.ext
      simp only [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one, one_pow]
    rw [hone]
    show ValueGroup₀.embedding (hiso.orderMonoidIso 1) = 1
    rw [show hiso.orderMonoidIso 1 = 1 from map_one _]
    exact map_one _
  have hψmul : ∀ x y : B.ValueGroup, ψfun (x * y) = ψfun x * ψfun y := by
    intro x y
    by_cases hx : x = 0
    · subst hx; simp [ψfun]
    · by_cases hy : y = 0
      · subst hy; simp [ψfun]
      · have hxy : x * y ≠ 0 := mul_ne_zero hx hy
        rw [show ψfun (x * y) = Ψ (↑(⟨(Units.mk0 (x*y) hxy) ^ (Module.finrank F L).factorial,
              hmem (x*y) hxy⟩ : (MonoidWithZeroHom.ofClass (B.valuation.comap (algebraMap F L))).valueGroup))
            from by simp only [ψfun, hxy, dif_neg, not_false_eq_true]]
        rw [show ψfun x = Ψ (↑(⟨(Units.mk0 x hx) ^ (Module.finrank F L).factorial,
              hmem x hx⟩ : (MonoidWithZeroHom.ofClass (B.valuation.comap (algebraMap F L))).valueGroup))
            from by simp only [ψfun, hx, dif_neg, not_false_eq_true]]
        rw [show ψfun y = Ψ (↑(⟨(Units.mk0 y hy) ^ (Module.finrank F L).factorial,
              hmem y hy⟩ : (MonoidWithZeroHom.ofClass (B.valuation.comap (algebraMap F L))).valueGroup))
            from by simp only [ψfun, hy, dif_neg, not_false_eq_true]]
        rw [← map_mul]
        congr 1
        have hunits : (Units.mk0 (x * y) hxy) ^ (Module.finrank F L).factorial
            = (Units.mk0 x hx) ^ (Module.finrank F L).factorial
              * (Units.mk0 y hy) ^ (Module.finrank F L).factorial := by
          apply Units.ext
          simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0, mul_pow]
        have hkey : (⟨(Units.mk0 (x * y) hxy) ^ (Module.finrank F L).factorial, hmem (x*y) hxy⟩ :
              (MonoidWithZeroHom.ofClass (B.valuation.comap (algebraMap F L))).valueGroup)
            = (⟨(Units.mk0 x hx) ^ (Module.finrank F L).factorial, hmem x hx⟩ :
                (MonoidWithZeroHom.ofClass (B.valuation.comap (algebraMap F L))).valueGroup)
              * (⟨(Units.mk0 y hy) ^ (Module.finrank F L).factorial, hmem y hy⟩ :
                (MonoidWithZeroHom.ofClass (B.valuation.comap (algebraMap F L))).valueGroup) := by
          apply Subtype.ext
          change (Units.mk0 (x * y) hxy) ^ (Module.finrank F L).factorial
            = (Units.mk0 x hx) ^ (Module.finrank F L).factorial
              * (Units.mk0 y hy) ^ (Module.finrank F L).factorial
          exact hunits
        rw [hkey, WithZero.coe_mul]
  let ψ : B.ValueGroup →*₀ Γ₀ := MonoidWithZeroHom.mk ⟨ψfun, hψ0⟩ hψ1 hψmul
  have ψ_apply : ∀ b : B.ValueGroup, ψ b = ψfun b := fun b => rfl
  have hψmono : Monotone ψ := by
    intro x y hxy
    rw [ψ_apply, ψ_apply]
    by_cases hx : x = 0
    · subst hx; rw [hψ0]; exact zero_le
    · by_cases hy : y = 0
      · subst hy
        have : x = 0 := le_antisymm hxy zero_le
        exact absurd this hx
      · have h1u : (Units.mk0 x hx) ^ (Module.finrank F L).factorial
            ≤ (Units.mk0 y hy) ^ (Module.finrank F L).factorial := by
          rw [← Units.val_le_val, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val,
            Units.val_mk0, Units.val_mk0]
          exact pow_le_pow_left₀ zero_le hxy _
        have h1 : (⟨(Units.mk0 x hx) ^ (Module.finrank F L).factorial, hmem x hx⟩ :
            (MonoidWithZeroHom.ofClass (B.valuation.comap (algebraMap F L))).valueGroup)
            ≤ (⟨(Units.mk0 y hy) ^ (Module.finrank F L).factorial, hmem y hy⟩ :
            (MonoidWithZeroHom.ofClass (B.valuation.comap (algebraMap F L))).valueGroup) :=
          h1u
        have h3 : (↑(⟨(Units.mk0 x hx) ^ (Module.finrank F L).factorial, hmem x hx⟩ :
              (MonoidWithZeroHom.ofClass (B.valuation.comap (algebraMap F L))).valueGroup) :
              (MonoidWithZeroHom.ofClass (B.valuation.comap (algebraMap F L))).ValueGroup₀)
            ≤ (↑(⟨(Units.mk0 y hy) ^ (Module.finrank F L).factorial, hmem y hy⟩ :
              (MonoidWithZeroHom.ofClass (B.valuation.comap (algebraMap F L))).valueGroup) :
              (MonoidWithZeroHom.ofClass (B.valuation.comap (algebraMap F L))).ValueGroup₀) := by
          rw [WithZero.coe_le_coe]
          exact h1
        rw [show ψfun x = Ψ (↑(⟨(Units.mk0 x hx) ^ (Module.finrank F L).factorial,
              hmem x hx⟩ : (MonoidWithZeroHom.ofClass (B.valuation.comap (algebraMap F L))).valueGroup))
            from by simp only [ψfun, hx, dif_neg, not_false_eq_true]]
        rw [show ψfun y = Ψ (↑(⟨(Units.mk0 y hy) ^ (Module.finrank F L).factorial,
              hmem y hy⟩ : (MonoidWithZeroHom.ofClass (B.valuation.comap (algebraMap F L))).valueGroup))
            from by simp only [ψfun, hy, dif_neg, not_false_eq_true]]
        exact hΨmono h3
  -- ## Step 5: `w := ψ ∘ B.valuation` and the compatibility check.
  have hψspec : ∀ a : F,
      ψ (B.valuation (algebraMap F L a)) = (v a) ^ (Module.finrank F L).factorial := by
    intro a
    by_cases ha : B.valuation (algebraMap F L a) = 0
    · have ha0 : a = 0 := by
        apply FaithfulSMul.algebraMap_injective F L
        rw [(Valuation.zero_iff B.valuation).mp ha, map_zero]
      subst ha0
      rw [map_zero, map_zero, ψ_apply, hψ0]
      rw [map_zero, zero_pow (Nat.factorial_ne_zero _)]
    · change ψfun ((MonoidWithZeroHom.ofClass (B.valuation.comap (algebraMap F L))) a)
        = (v a) ^ (Module.finrank F L).factorial
      have hb : (MonoidWithZeroHom.ofClass (B.valuation.comap (algebraMap F L))) a ≠ 0 := ha
      rw [show ψfun ((MonoidWithZeroHom.ofClass (B.valuation.comap (algebraMap F L))) a) =
            Ψ (↑(⟨(Units.mk0 ((MonoidWithZeroHom.ofClass
                  (B.valuation.comap (algebraMap F L))) a) hb) ^ (Module.finrank F L).factorial,
                hmem _ hb⟩ : (MonoidWithZeroHom.ofClass
                  (B.valuation.comap (algebraMap F L))).valueGroup))
          from by simp only [ψfun, hb, dif_neg, not_false_eq_true]]
      have harg : (↑(⟨(Units.mk0 ((MonoidWithZeroHom.ofClass
                (B.valuation.comap (algebraMap F L))) a) hb) ^ (Module.finrank F L).factorial,
                hmem _ hb⟩ : (MonoidWithZeroHom.ofClass
                (B.valuation.comap (algebraMap F L))).valueGroup) :
              (MonoidWithZeroHom.ofClass (B.valuation.comap (algebraMap F L))).ValueGroup₀)
          = (ValueGroup₀.restrict₀
              (MonoidWithZeroHom.ofClass (B.valuation.comap (algebraMap F L))) a)
            ^ (Module.finrank F L).factorial := by
        rw [ValueGroup₀.restrict₀_of_ne_zero (f := MonoidWithZeroHom.ofClass
          (B.valuation.comap (algebraMap F L))) hb]
        rw [← WithZero.coe_pow, WithZero.coe_inj]
        rw [SubmonoidClass.mk_pow]
      rw [harg, map_pow, hΨspec a]
  refine ⟨Γ₀, inferInstance, ⟨⟨fun γ => γ ^ (Module.finrank F L).factorial,
      zero_pow (Nat.factorial_ne_zero _)⟩, one_pow _, fun a b => mul_pow a b _⟩, ?_,
    B.valuation.map ⟨ψ, hψmono⟩, ?_⟩
  · intro a b hab
    change a ^ (Module.finrank F L).factorial < b ^ (Module.finrank F L).factorial
    rcases eq_or_lt_of_le (zero_le (a := a)) with h0 | ha
    · rw [show a = 0 from h0.symm, zero_pow (Nat.factorial_ne_zero _)]
      exact pow_pos (h0.symm ▸ hab) _
    · exact pow_lt_pow_left₀ hab (le_of_lt ha) (Nat.factorial_ne_zero _)
  · intro x
    rw [Valuation.map_apply]
    exact hψspec x

/-- The *requested* statement, in the only case in which it can hold: when the given value
group `Γ₀` lives in `Type 0` (which is the case in every application in this development).
This follows immediately from `valuation_extends_finiteDimensional_gen`. -/
theorem valuation_extends_finiteDimensional_type0 {F L : Type*} {Γ₀ : Type}
    [Field F] [Field L] [Algebra F L] [FiniteDimensional F L]
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation F Γ₀) :
    ∃ (Γ₁ : Type) (_ : LinearOrderedCommGroupWithZero Γ₁) (f : Γ₀ →*₀ Γ₁)
      (_ : StrictMono f) (w : Valuation L Γ₁),
      ∀ x : F, w (algebraMap F L x) = f (v x) :=
  valuation_extends_finiteDimensional_gen (Γ₀ := Γ₀) v

/-- **The unrestricted statement** (value groups `Type*`-polymorphic, with `Γ₁` in the *same*
universe as `Γ₀`).  The version of this declaration that confined `Γ₁` to `Type 0` is *false* for a
`Γ₀` in a higher universe (a strictly monotone map is injective), see the universe note at the top
of the file; this is the honest form, and it is literally `valuation_extends_finiteDimensional_gen`
(the earlier proof produced `Γ₁ = Γ₀` enlarged by an `E`-th power, so nothing is lost). -/
theorem valuation_extends_finiteDimensional {Γ₀ : Type u} {F L : Type*}
    [Field F] [Field L] [Algebra F L] [FiniteDimensional F L]
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation F Γ₀) :
    ∃ (Γ₁ : Type u) (_ : LinearOrderedCommGroupWithZero Γ₁) (f : Γ₀ →*₀ Γ₁)
      (_ : StrictMono f) (w : Valuation L Γ₁),
      ∀ x : F, w (algebraMap F L x) = f (v x) :=
  valuation_extends_finiteDimensional_gen v

end Work.MotV5.Nodes
