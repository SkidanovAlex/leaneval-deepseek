/-
# Extending a unit endomorphism of the fixed field to `Eˣ`

Stage A of the case-c analysis needs the following: given a monoid endomorphism `φ` of the
multiplicative group of the field `F` of order `q = 2ⁿ` embedded in `E = GF(q²)` as the fixed
field of the Frobenius involution `σE`, there is an endomorphism `nm` of `Eˣ` extending
`ι ∘ φ ∘ ι⁻¹` on the fixed units, and `nm` maps `σE`-fixed units to `σE`-fixed units.

Both properties are obtained by a single observation: **the multiplicative group of a finite
field is cyclic**, hence (`MonoidHom.map_cyclic`) *every* monoid endomorphism of `Fˣ` is a
power map `c ↦ c ^ m` for some `m : ℤ`.  Taking `nm` to be the same power map on `Eˣ` gives
the extension on `ι '' Fˣ` at once, and the second condition is automatic because `σE` is a
ring homomorphism: `σE (a ^ m) = (σE a) ^ m = a ^ m` whenever `σE a = a`.

The remaining hypotheses (`hn`, `hcard`, `hι`, `hfix`) only serve to place `F` and `ι` in the
geometric situation; the existence statement itself needs no cardinality hypothesis.
-/
import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.PSU3.GaloisField

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false

namespace Work.PSU3.StageA

/-- The `m`-th power map on a commutative group, as a monoid endomorphism.  (For a
commutative group this is a homomorphism, by `mul_zpow`.) -/
noncomputable def zpowMonoidHom {G : Type*} [CommGroup G] (m : ℤ) : G →* G where
  toFun := fun a => a ^ m
  map_one' := by simp
  map_mul' := fun a b => by simp [mul_zpow]

@[simp] lemma zpowMonoidHom_apply {G : Type*} [CommGroup G] (m : ℤ) (a : G) :
    zpowMonoidHom m a = a ^ m := rfl

/-- Every monoid endomorphism of the units of a finite field is a power map: the unit group of
a finite field is cyclic (`IsCyclic Fˣ`, from `isCyclic_of_injective_ringHom`). -/
theorem units_endo_eq_zpow (F : Type) [Field F] [Fintype F] (φ : Fˣ →* Fˣ) :
    ∃ m : ℤ, ∀ c : Fˣ, φ c = c ^ m :=
  MonoidHom.map_cyclic φ

theorem nm_extend {n : ℕ} (hn : 1 ≤ n) (F : Type) [Field F] [Fintype F]
    (hcard : Nat.card F = 2 ^ n) (ι : F →+* Work.PSU3.E n)
    (hfix : ∀ c : F, Work.PSU3.σE (ι c) = ι c) (hι : Function.Injective ι)
    (φ : Fˣ →* Fˣ) :
    ∃ nm : (Work.PSU3.E n)ˣ →* (Work.PSU3.E n)ˣ,
      (∀ c : Fˣ, nm (Units.map ι.toMonoidWithZeroHom c) =
        Units.map ι.toMonoidWithZeroHom (φ c)) ∧
      (∀ a : (Work.PSU3.E n)ˣ, Work.PSU3.σE (a : Work.PSU3.E n) = a →
        Work.PSU3.σE (nm a : Work.PSU3.E n) = nm a) := by
  obtain ⟨m, hm⟩ := units_endo_eq_zpow F φ
  refine ⟨zpowMonoidHom (G := (Work.PSU3.E n)ˣ) m, ?_, ?_⟩
  · intro c
    rw [zpowMonoidHom_apply, ← map_zpow, ← hm c]
  · intro a ha
    rw [zpowMonoidHom_apply, Units.val_zpow_eq_zpow_val, map_zpow₀, ha]

end Work.PSU3.StageA
