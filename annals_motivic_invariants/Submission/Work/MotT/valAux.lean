import Mathlib
import Submission.Work.MotT.Defs
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Auxiliary lemmas for `Work.MotT.exists_kleinData_val` (node T7)

This module collects the *elementary* (valuation-theoretic and rescaling) ingredients of the
route to `Work.MotT.exists_kleinData_val`, so that they can be used by the colleagues proving
the remaining (hard) pieces without importing the target theorem.

The normalisation convention of `Work.MotT.vOne` is `ofAdd (-1) ∈ ℤᵐ⁰`, i.e. `v π = vOne` says
that `π` is a uniformizer and that `v` is normalised so that `v u = 1` means "`u` is a unit".

## Contents

* `vOne_pow_eq` : `vOne ^ m = ofAdd (-m)`.
* `vOne_pow_lt_one` : `vOne ^ m < 1` for `0 < m`.
* `v_one_add_pow_pi` : **`v (1 + π^m) = 1`** for `0 < m` — the *unit* condition of T7: the
  Klein parameter `u = 1 + π^m` is a unit.
* `exists_good_val_one_of_val_eq` : if a Good Klein model has `v D.a = v D.b`, then the
  rescaled model `(1, b/a)` is Good **and** has unit parameters.  (The rescaling
  `(a, b) → (u a, u b)` preserves `Good` — `kleinP` is homogeneous of degree two in `(a, b)`
  (`kleinP_smul_ab`) — and it preserves `v a - v b`, so a *common* rescale can only make both
  parameters units if they already have equal valuation; the normalisation `b ↦ b/a` achieves
  it.)
-/

set_option autoImplicit false
open scoped WithZero
open WeierstrassCurve WeierstrassCurve.Affine

namespace Work.MotT

noncomputable section

/-! ## §1 The value of `1 + π^m` -/

/-- `vOne ^ m = ofAdd (-m)`. -/
lemma vOne_pow_eq (m : ℕ) :
    vOne ^ m = ((Multiplicative.ofAdd (-(m : ℤ)) : Multiplicative ℤ) : ℤᵐ⁰) := by
  rw [vOne, ← WithZero.coe_pow]
  congr 1
  rw [← ofAdd_nsmul]
  congr 1
  simp

/-- `vOne ^ m < 1` for `0 < m`. -/
lemma vOne_pow_lt_one {m : ℕ} (hm : 0 < m) : vOne ^ m < (1 : ℤᵐ⁰) := by
  rw [vOne_pow_eq m, ← WithZero.coe_one, ← ofAdd_zero, WithZero.coe_lt_coe,
    Multiplicative.ofAdd_lt]
  omega

/-- **Units.**  If `v π = vOne` then `1 + π^m` is a unit for every `m ≥ 1`.  This is the
condition under which the T7 Klein parameter `u = 1 + π^m` may be used. -/
theorem v_one_add_pow_pi {K : Type} [Field K] (v : Valuation K ℤᵐ⁰) {π : K}
    (hπ : v π = vOne) (m : ℕ) (hm : 0 < m) : v (1 + π ^ m) = 1 := by
  have hpow : v (π ^ m) = vOne ^ m := by rw [Valuation.map_pow, hπ]
  have hne : v (1 : K) ≠ v (π ^ m) := by
    rw [Valuation.map_one, hpow]
    exact ne_of_gt (vOne_pow_lt_one hm)
  rw [Valuation.map_add_of_distinct_val (v := v) hne, Valuation.map_one, hpow, max_eq_left]
  exact le_of_lt (vOne_pow_lt_one hm)

/-! ## §2 Common rescaling of the Klein parameters -/

/-- The Klein coordinates depend only on `D.E` and `D.coord`, so a rescaling of `(D.a, D.b)`
leaves them unchanged. -/
theorem kleinCoord_rescale {K : Type} [Field K] (D : Work.MotV.KleinData K) (u : K) :
    ∀ (L : Type) [Field L] [Algebra K L],
      Work.MotV.kleinCoord (⟨u * D.a, u * D.b, D.E, D.coord⟩ : Work.MotV.KleinData K) L
        = Work.MotV.kleinCoord D L := fun _ _ _ => rfl

/-- **Rescaling.**  If a Good Klein model has `v D.a = v D.b`, then the normalised model
`(1, b/a)` is Good and has *unit* Klein parameters `(v a = v b = 1)`.  The rescaling
`(a, b) → (u a, u b)` preserves `Good` for any `u ≠ 0` (the Klein Pfaffians are homogeneous of
degree two in `(a, b)`), and it multiplies both valuations by `v u`; a *common* rescale therefore
cannot change `v a - v b`, which is why the hypothesis `v D.a = v D.b` is needed. -/
theorem exists_good_val_one_of_val_eq {K : Type} [Field K] (v : Valuation K ℤᵐ⁰)
    (D : Work.MotV.KleinData K) (hD : D.Good) (hval : v D.a = v D.b) :
    ∃ D' : Work.MotV.KleinData K, D'.Good ∧ v D'.a = 1 ∧ v D'.b = 1 := by
  have ha : D.a ≠ 0 := fun h => hD.ab_ne (by rw [h, zero_mul])
  have hb : D.b ≠ 0 := fun h => hD.ab_ne (by rw [h, mul_zero])
  have hva : v D.a ≠ 0 := (Valuation.ne_zero_iff v).mpr ha
  have hvinv : v (D.a)⁻¹ = (v D.a)⁻¹ := by
    have h1 : v (D.a) * v (D.a)⁻¹ = 1 := by
      rw [← Valuation.map_mul, mul_inv_cancel₀ ha, Valuation.map_one]
    exact (inv_eq_of_mul_eq_one_right h1).symm
  set u : K := (D.a)⁻¹ with hu
  have hua : u * D.a = 1 := by rw [hu]; exact inv_mul_cancel₀ ha
  have hcoe : ∀ (L : Type) [Field L] [Algebra K L],
      Work.MotV.kleinCoord (⟨u * D.a, u * D.b, D.E, D.coord⟩ : Work.MotV.KleinData K) L
        = Work.MotV.kleinCoord D L := fun L _ _ => rfl
  refine ⟨⟨u * D.a, u * D.b, D.E, D.coord⟩, ?_, ?_, ?_⟩
  · obtain ⟨hel, hab, hj0, hj, hke, hc0, htd, hsp⟩ := hD
    refine ⟨hel, ?_, hj0, hj, ?_, ?_, ?_, ?_⟩
    · show (u * D.a) * (u * D.b) ≠ 0
      rw [hua, one_mul]
      exact mul_ne_zero (by rw [hu]; exact inv_ne_zero ha) hb
    · intro L _ _ k
      rw [hcoe L, map_mul, map_mul, kleinP_smul_ab, hke L k]
      first | refl_ring1 | ring
    · intro L _ _
      rw [hcoe L]
      exact hc0 L
    · intro L _ _ ζ hζ
      obtain ⟨σ, hσ⟩ := htd L ζ hζ
      exact ⟨σ, fun i => by simpa only [hcoe L] using hσ i⟩
    · obtain ⟨e, he⟩ := hsp
      exact ⟨e, fun L _ _ m => by simpa only [hcoe L, Work.MotV.kleinBas] using he L m⟩
  · show v (u * D.a) = 1
    rw [Valuation.map_mul, hu, hvinv, inv_mul_cancel₀ hva]
  · show v (u * D.b) = 1
    rw [Valuation.map_mul, hu, hvinv, ← hval, inv_mul_cancel₀ hva]

end

end Work.MotT
