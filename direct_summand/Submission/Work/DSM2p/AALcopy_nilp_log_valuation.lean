-- Redirected copy of `Submission.Work.DSM2p.nilp_log_valuation` (imports re-pointed to the `AALvaln` vocabulary layer so that
-- `area_AAL_proved.lean` can import the result without an import cycle).  The original
-- file is untouched; this copy is generated mechanically.
import Mathlib
import Submission.Work.DSM2p.AALvaln
import Submission.Work.DSM2p.nilp_log_core

/-!
# `Work.DSM2p.nilp_log_valuation`

From a valuation `v₀ : B → Γ` which is *continuous* for the `ϖ`-adic topology (the values of the
powers of `ϖ` become smaller than every prescribed non-zero value), we produce a valuation with
values in `WithZero (Multiplicative ℝ)` which still is continuous, is `≤ 1` on any given unit ball
`IsUnitBall v₀ s` of `v₀`, and is `≥ 1` at an element `a` with `1 ≤ v₀ a`.

## The construction

The key input is a *logarithm* attached to the cofinal element `g = v₀ ϖ`: the hypothesis
`IsContinuousValuation ϖ v₀` says exactly that the powers of `g` are cofinal below every non-zero
element of `Γ`, and this is what makes the archimedean logarithm

`ψ x = sup { m / n : n > 0, x ^ n ≤ g ^ m }`

well defined, additive on the non-zero part of `Γ` and order-reversing (`ψ g = 1`). This is the
content of `Work.DSM2p.cofinal_log_real_aux` (module `Submission.Work.DSM2p.nilp_log_core`); the
same statement is also available from the delegated lemma `Work.DSM2p.cofinal_log_real`.

The rest is a purely formal step: from an additive, order-reversing `ψ` with `ψ g = 1`, the map
`x ↦ (if x = 0 then 0 else ↑(ofAdd (-(ψ x))))` is a monotone monoid-with-zero homomorphism into
`WithZero (Multiplicative ℝ)` with `φ g = ↑(ofAdd (-1)) < 1`, and composing it with `v₀` (using
`Valuation.map`) gives the required valuation.  Monotonicity gives the unit ball and the lower
bound at `a`; the fact that `(φ g) ^ n = ↑(ofAdd (-n))` tends to `0` gives continuity.
-/

namespace Work.DSM2p

open scoped Classical

/-! ## The logarithmic encoding -/

section Enc

variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]

/-- The "logarithmic" encoding of a real-valued additive logarithm as a map into
`WithZero (Multiplicative ℝ)`: `x ↦ ofAdd (-(ψ x))` on the non-zero part and `0 ↦ 0`. -/
noncomputable def encFun (ψ : Γ → ℝ) (x : Γ) : WithZero (Multiplicative ℝ) :=
  if x = 0 then 0
  else ((Multiplicative.ofAdd (-(ψ x)) : Multiplicative ℝ) : WithZero (Multiplicative ℝ))

lemma encFun_zero (ψ : Γ → ℝ) : encFun ψ 0 = 0 := by
  simp [encFun]

lemma encFun_eq (ψ : Γ → ℝ) {x : Γ} (hx : x ≠ 0) :
    encFun ψ x
      = ((Multiplicative.ofAdd (-(ψ x)) : Multiplicative ℝ) : WithZero (Multiplicative ℝ)) := by
  rw [encFun, ite_eq_right hx]

/-- The encoding is multiplicative as soon as `ψ` is additive on the non-zero part. -/
lemma encFun_mul (ψ : Γ → ℝ) (hadd : ∀ x y : Γ, x ≠ 0 → y ≠ 0 → ψ (x * y) = ψ x + ψ y)
    (x y : Γ) : encFun ψ (x * y) = encFun ψ x * encFun ψ y := by
  by_cases hx : x = 0
  · subst hx
    simp [encFun]
  · by_cases hy : y = 0
    · subst hy
      simp [encFun]
    · have hxy : x * y ≠ 0 := mul_ne_zero hx hy
      rw [encFun_eq ψ hxy, encFun_eq ψ hx, encFun_eq ψ hy, hadd x y hx hy, neg_add,
        ← WithZero.coe_mul, ← ofAdd_add]

/-- The encoding as a monoid-with-zero homomorphism. -/
noncomputable def encHom (ψ : Γ → ℝ) (h1 : ψ 1 = 0)
    (hadd : ∀ x y : Γ, x ≠ 0 → y ≠ 0 → ψ (x * y) = ψ x + ψ y) :
    Γ →*₀ WithZero (Multiplicative ℝ) where
  toFun := encFun ψ
  map_zero' := encFun_zero ψ
  map_one' := by
    rw [encFun_eq ψ one_ne_zero, h1, neg_zero, ofAdd_zero, WithZero.coe_one]
  map_mul' := encFun_mul ψ hadd

@[simp]
lemma encHom_apply (ψ : Γ → ℝ) (h1 : ψ 1 = 0)
    (hadd : ∀ x y : Γ, x ≠ 0 → y ≠ 0 → ψ (x * y) = ψ x + ψ y) (x : Γ) :
    encHom ψ h1 hadd x = encFun ψ x := rfl

/-- The encoding is monotone as soon as `ψ` is order-reversing on the non-zero part. -/
lemma encHom_mono (ψ : Γ → ℝ) (h1 : ψ 1 = 0)
    (hadd : ∀ x y : Γ, x ≠ 0 → y ≠ 0 → ψ (x * y) = ψ x + ψ y)
    (hmono : ∀ x y : Γ, x ≠ 0 → y ≠ 0 → x ≤ y → ψ y ≤ ψ x) :
    Monotone (encHom ψ h1 hadd) := by
  intro x y hxy
  by_cases hx : x = 0
  · subst hx
    rw [encHom_apply, encFun_zero]
    exact zero_le
  · by_cases hy : y = 0
    · subst hy
      exact absurd (le_antisymm hxy zero_le) hx
    · rw [encHom_apply, encHom_apply, encFun_eq ψ hx, encFun_eq ψ hy, WithZero.coe_le_coe,
        Multiplicative.ofAdd_le]
      have h := hmono x y hx hy hxy
      linarith

/-- At the cofinal element (where `ψ` takes the value `1`) the encoding is the explicit value
`↑(ofAdd (-1))`. -/
lemma encHom_apply_of_eq_one (ψ : Γ → ℝ) (h1 : ψ 1 = 0)
    (hadd : ∀ x y : Γ, x ≠ 0 → y ≠ 0 → ψ (x * y) = ψ x + ψ y) {g : Γ} (hg : g ≠ 0)
    (hg1 : ψ g = 1) :
    encHom ψ h1 hadd g
      = ((Multiplicative.ofAdd (-1) : Multiplicative ℝ) : WithZero (Multiplicative ℝ)) := by
  rw [encHom_apply, encFun_eq ψ hg, hg1]

lemma ofAdd_neg_one_lt_one :
    ((Multiplicative.ofAdd (-1) : Multiplicative ℝ) : WithZero (Multiplicative ℝ)) < 1 := by
  rw [← WithZero.coe_one, WithZero.coe_lt_coe, ← ofAdd_zero, Multiplicative.ofAdd_lt]
  norm_num

/-- Powers of `↑(ofAdd (-1))` tend to `0`: they are cofinal below every non-zero element. -/
lemma ofAdd_neg_one_pow_cofinal (γ : WithZero (Multiplicative ℝ)) (hγ : γ ≠ 0) :
    ∃ n : ℕ, (((Multiplicative.ofAdd (-1) : Multiplicative ℝ) :
      WithZero (Multiplicative ℝ)) ^ n) < γ := by
  set u : Multiplicative ℝ := WithZero.unzero hγ with hu
  have hcoe : (↑u : WithZero (Multiplicative ℝ)) = γ := WithZero.coe_unzero hγ
  obtain ⟨n, hn⟩ := exists_nat_gt (-(u.toAdd))
  refine ⟨n, ?_⟩
  have hns : (n : ℕ) • (-1 : ℝ) = -(n : ℝ) := by simp
  rw [← hcoe, ← WithZero.coe_pow, ← ofAdd_nsmul, hns, WithZero.coe_lt_coe,
    ← ofAdd_toAdd u, Multiplicative.ofAdd_lt]
  linarith

end Enc

/-! ## The main theorem -/

theorem nilp_log_valuation {B : Type*} [CommRing B] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (v₀ : Valuation B Γ) (ϖ : B) (hcont : IsContinuousValuation ϖ v₀) (hϖ0 : v₀ ϖ ≠ 0)
    (hnat : ∀ n : ℕ, v₀ (n : B) ≤ 1) (s : Set B) (hball : IsUnitBall v₀ s) {a : B}
    (ha : 1 ≤ v₀ a) :
    ∃ v : Valuation B (WithZero (Multiplicative ℝ)),
      IsContinuousValuation ϖ v ∧ IsUnitBall v s ∧ 1 ≤ v a := by
  have _hnat := hnat
  obtain ⟨ψ, hψ1, hψg, hadd, hmono⟩ := cofinal_log_real_aux (v₀ ϖ) hϖ0 hcont
  let φo : Γ →*₀o WithZero (Multiplicative ℝ) :=
    ⟨encHom ψ hψ1 hadd, encHom_mono ψ hψ1 hadd hmono⟩
  have hφg : φo (v₀ ϖ)
      = ((Multiplicative.ofAdd (-1) : Multiplicative ℝ) : WithZero (Multiplicative ℝ)) := by
    show encHom ψ hψ1 hadd (v₀ ϖ) = _
    exact encHom_apply_of_eq_one ψ hψ1 hadd hϖ0 hψg
  refine ⟨v₀.map φo, ?_, ?_, ?_⟩
  · -- continuity: the powers of `v ϖ = ↑(ofAdd (-1))` tend to `0`
    intro γ hγ
    rw [Valuation.map_apply, hφg]
    exact ofAdd_neg_one_pow_cofinal γ hγ
  · -- the unit ball
    intro b hb
    rw [Valuation.map_apply]
    calc φo (v₀ b) ≤ φo 1 := φo.monotone' (hball b hb)
      _ = 1 := map_one φo
  · -- `1 ≤ v a`
    rw [Valuation.map_apply]
    calc (1 : WithZero (Multiplicative ℝ)) = φo 1 := (map_one φo).symm
      _ ≤ φo (v₀ a) := φo.monotone' ha

end Work.DSM2p
