import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# A ring automorphism preserving the valuation ring preserves the valuation

For a field `L` equipped with a valuation `V` with values in `ℤᐟ⁰ = WithZero (Multiplicative ℤ)`
(i.e. the value group is a subgroup of `ℤ`), any ring automorphism `φ` of `L` that preserves the
valuation ring `{x | V x ≤ 1}` preserves `V` itself: `V (φ x) = V x` for every `x`.

The proof goes through the additive "exponent" `valExp V x = (V x).log ∈ ℤ` (with junk value `0`
at `x = 0`), so that `V x = WithZero.exp (valExp V x)` for `x ≠ 0`.  Preservation of the valuation
ring gives an order isomorphism `valExp V ∘ φ ↔ valExp V` (equivalently `V ∘ φ ↔ V` on ordered
pairs of values).  Since the value group is a subgroup of `ℤ`, it has a least positive element `d`,
realised by some `π`; every value is a `ℤ`-multiple of `d`, and the order-isomorphism fixes `d`
(comparing `π` with `φ π` and with `φ⁻¹ π`), whence it is the identity.

(A separate branch treats the trivially valued case, where every nonzero value equals `1`.)
-/

namespace Work.MotV5.RigAS.ValuationAux

/-- The additive `ℤ`-exponent of a value in `ℤᐟ⁰ = WithZero (Multiplicative ℤ)`; the junk value
`0` is used at `0`. -/
noncomputable def valExp {L : Type*} [Field L]
    (V : Valuation L (WithZero (Multiplicative ℤ))) (x : L) : ℤ :=
  WithZero.log (V x)

lemma valExp_one {L : Type*} [Field L] (V : Valuation L (WithZero (Multiplicative ℤ))) :
    valExp V 1 = 0 := by
  show WithZero.log (V 1) = 0
  rw [Valuation.map_one, WithZero.log_one]

lemma valExp_exp {L : Type*} [Field L] (V : Valuation L (WithZero (Multiplicative ℤ)))
    {x : L} (hx : x ≠ 0) : WithZero.exp (valExp V x) = V x :=
  WithZero.exp_log (V.ne_zero_iff.mpr hx)

lemma valExp_le_iff {L : Type*} [Field L] (V : Valuation L (WithZero (Multiplicative ℤ)))
    {x y : L} (hx : x ≠ 0) (hy : y ≠ 0) : V x ≤ V y ↔ valExp V x ≤ valExp V y := by
  rw [← valExp_exp V hx, ← valExp_exp V hy, WithZero.exp_le_exp]

lemma valExp_inv {L : Type*} [Field L] (V : Valuation L (WithZero (Multiplicative ℤ))) (x : L) :
    valExp V x⁻¹ = - valExp V x := by
  show WithZero.log (V x⁻¹) = - WithZero.log (V x)
  rw [Valuation.map_inv, WithZero.log_inv]

lemma valExp_mul {L : Type*} [Field L] (V : Valuation L (WithZero (Multiplicative ℤ)))
    {x y : L} (hx : x ≠ 0) (hy : y ≠ 0) :
    valExp V (x * y) = valExp V x + valExp V y := by
  show WithZero.log (V (x * y)) = WithZero.log (V x) + WithZero.log (V y)
  rw [Valuation.map_mul, WithZero.log_mul (V.ne_zero_iff.mpr hx) (V.ne_zero_iff.mpr hy)]

lemma valExp_zpow {L : Type*} [Field L] (V : Valuation L (WithZero (Multiplicative ℤ)))
    (x : L) (n : ℤ) : valExp V (x ^ n) = n * valExp V x := by
  show WithZero.log (V (x ^ n)) = n * WithZero.log (V x)
  rw [map_zpow₀ V x n, WithZero.log_zpow, smul_eq_mul]

/-- A ring automorphism of a field preserving the valuation ring `{x | V x ≤ 1}` of a
`ℤᐟ⁰`-valued valuation preserves the valuation itself. -/
theorem val_eq_of_ring_stable {L : Type*} [Field L]
    (V : Valuation L (WithZero (Multiplicative ℤ))) (φ : L ≃+* L)
    (hφ : ∀ x : L, V (φ x) ≤ 1 ↔ V x ≤ 1) :
    ∀ x : L, V (φ x) = V x := by
  classical
  -- a ring automorphism sends nonzero elements to nonzero elements
  have eqv_ne : ∀ (ψ : L ≃+* L) {x : L}, x ≠ 0 → ψ x ≠ 0 := by
    intro ψ x hx h
    exact hx (ψ.injective (h.trans (map_zero ψ).symm))
  -- preserving the valuation ring means the two valuations are equivalent
  have hE : (V.comap (φ : L →+* L)).IsEquiv V := by
    rw [Valuation.isEquiv_iff_val_le_one]
    intro x
    rw [Valuation.comap_apply]
    exact hφ x
  have hisoV : ∀ x y : L, V (φ x) ≤ V (φ y) ↔ V x ≤ V y := by
    intro x y
    have h := hE.le_iff_le (x := x) (y := y)
    change V ((φ : L →+* L) x) ≤ V ((φ : L →+* L) y) ↔ V x ≤ V y
    simpa only [Valuation.comap_apply] using h
  have hiso : ∀ x y : L, x ≠ 0 → y ≠ 0 →
      (valExp V (φ x) ≤ valExp V (φ y) ↔ valExp V x ≤ valExp V y) := by
    intro x y hx hy
    rw [← valExp_le_iff V (eqv_ne φ hx) (eqv_ne φ hy), ← valExp_le_iff V hx hy]
    exact hisoV x y
  by_cases hA : ∃ k : ℕ, 0 < k ∧ ∃ x : L, x ≠ 0 ∧ valExp V x = (k : ℤ)
  · -- there is a positive value; take the least one
    set d : ℕ := Nat.find hA with hd_def
    have hd_spec : 0 < d ∧ ∃ x : L, x ≠ 0 ∧ valExp V x = (d : ℤ) := by
      rw [hd_def]; exact Nat.find_spec hA
    have hdpos : 0 < d := hd_spec.1
    obtain ⟨π, hπne, hπd⟩ := hd_spec.2
    -- `d` is the least positive exponent occurring as a value
    have hmin : ∀ x : L, x ≠ 0 → 0 < valExp V x → (d : ℤ) ≤ valExp V x := by
      intro x hx hpos
      have hmem : 0 < (valExp V x).toNat ∧
          ∃ y : L, y ≠ 0 ∧ valExp V y = (((valExp V x).toNat : ℕ) : ℤ) := by
        refine ⟨?_, x, hx, ?_⟩
        · rw [Int.lt_toNat]; exact hpos
        · exact (Int.toNat_of_nonneg (le_of_lt hpos)).symm
      have hle : d ≤ (valExp V x).toNat := by
        rw [hd_def]; exact Nat.find_min' hA hmem
      have hle' : (d : ℤ) ≤ ((valExp V x).toNat : ℤ) := by exact_mod_cast hle
      rwa [Int.toNat_of_nonneg (le_of_lt hpos)] at hle'
    -- every exponent is a `ℤ`-multiple of `d`
    have hdvd : ∀ x : L, x ≠ 0 → ∃ q : ℤ, valExp V x = q * (d : ℤ) := by
      intro x hx
      have hdZ : (d : ℤ) ≠ 0 := by exact_mod_cast ne_of_gt hdpos
      have hdZpos : (0 : ℤ) < (d : ℤ) := by exact_mod_cast hdpos
      by_cases hr : valExp V x % (d : ℤ) = 0
      · refine ⟨valExp V x / (d : ℤ), ?_⟩
        have h := Int.ediv_mul_add_emod (valExp V x) (d : ℤ)
        rw [hr, add_zero] at h
        exact h.symm
      · exfalso
        have hrpos : 0 < valExp V x % (d : ℤ) :=
          lt_of_le_of_ne (Int.emod_nonneg _ hdZ) (Ne.symm hr)
        have hrlt : valExp V x % (d : ℤ) < (d : ℤ) := Int.emod_lt_of_pos _ hdZpos
        set q : ℤ := valExp V x / (d : ℤ) with hq_def
        set y : L := x * π ^ (-q) with hy_def
        have hyne : y ≠ 0 := by
          rw [hy_def]; exact mul_ne_zero hx (zpow_ne_zero _ hπne)
        have hyv : valExp V y = valExp V x % (d : ℤ) := by
          rw [hy_def, valExp_mul V hx (zpow_ne_zero _ hπne), valExp_zpow]
          rw [hπd]
          have h := Int.ediv_mul_add_emod (valExp V x) (d : ℤ)
          rw [← hq_def] at h
          linarith
        have hmem : 0 < (valExp V x % (d : ℤ)).toNat ∧
            ∃ z : L, z ≠ 0 ∧
              valExp V z = (((valExp V x % (d : ℤ)).toNat : ℕ) : ℤ) := by
          refine ⟨?_, y, hyne, ?_⟩
          · rw [Int.lt_toNat]; exact hrpos
          · rw [Int.toNat_of_nonneg (le_of_lt hrpos), hyv]
        have hle : d ≤ (valExp V x % (d : ℤ)).toNat := by
          rw [hd_def]; exact Nat.find_min' hA hmem
        have hlt : (valExp V x % (d : ℤ)).toNat < d := by
          rw [Int.toNat_lt (le_of_lt hrpos)]; exact hrlt
        omega
    -- the order isomorphism fixes the least positive value `d`
    have hφπ : valExp V (φ π) = valExp V π := by
      have hd0 : (0 : ℤ) < (d : ℤ) := by exact_mod_cast hdpos
      have hnotd : ¬ ((d : ℤ) ≤ 0) := not_le.mpr hd0
      have hpos : 0 < valExp V (φ π) := by
        have h := hiso π 1 hπne one_ne_zero
        simp only [map_one, valExp_one] at h
        rw [hπd] at h
        exact not_le.mp (fun hc => hnotd (h.mp hc))
      have hposinv : 0 < valExp V (φ.symm π) := by
        have h := hiso (φ.symm π) 1 (eqv_ne φ.symm hπne) one_ne_zero
        have h1 : φ (φ.symm π) = π := φ.apply_symm_apply π
        simp only [h1, map_one, valExp_one] at h
        rw [hπd] at h
        exact not_le.mp (h.not.mp hnotd)
      -- both `φ π` and `φ.symm π` have positive value, hence value at least `d`
      have hle1 : valExp V π ≤ valExp V (φ π) := by
        rw [hπd]; exact hmin (φ π) (eqv_ne φ hπne) hpos
      have hle2 : valExp V π ≤ valExp V (φ.symm π) := by
        rw [hπd]; exact hmin (φ.symm π) (eqv_ne φ.symm hπne) hposinv
      -- order preservation turns the second one into `valExp V (φ π) ≤ valExp V π`
      have hle3 : valExp V (φ π) ≤ valExp V π := by
        have hh2 := hiso π (φ.symm π) hπne (eqv_ne φ.symm hπne)
        rw [φ.apply_symm_apply π] at hh2
        exact hh2.mpr hle2
      omega
    have hVφπ : V (φ π) = V π := by
      rw [← valExp_exp V (eqv_ne φ hπne), ← valExp_exp V hπne, hφπ]
    intro x
    by_cases hx : x = 0
    · subst hx; simp
    · obtain ⟨q, hq⟩ := hdvd x hx
      set y : L := π ^ q with hy_def
      have hyne : y ≠ 0 := by rw [hy_def]; exact zpow_ne_zero q hπne
      have hxy : V y = V x := by
        rw [hy_def, map_zpow₀ V π q, ← valExp_exp V hπne, hπd, ← WithZero.exp_zsmul,
          smul_eq_mul, ← hq, valExp_exp V hx]
      have hφy : V (φ y) = V y := by
        rw [hy_def, map_zpow₀ φ π q, map_zpow₀ V (φ π) q, hVφπ,
          map_zpow₀ V π q]
      have h1 : V (φ x) ≤ V (φ y) := (hisoV x y).mpr (le_of_eq hxy.symm)
      have h2 : V (φ y) ≤ V (φ x) := (hisoV y x).mpr (le_of_eq hxy)
      exact (le_antisymm h1 h2).trans (hφy.trans hxy)
  · -- no positive value: the valuation is trivial
    push Not at hA
    have hnonpos : ∀ x : L, x ≠ 0 → valExp V x ≤ 0 := by
      intro x hx
      by_contra h
      rw [not_le] at h
      have hk : 0 < (valExp V x).toNat := by rw [Int.lt_toNat]; exact h
      have heq : valExp V x = (((valExp V x).toNat : ℕ) : ℤ) :=
        (Int.toNat_of_nonneg (le_of_lt h)).symm
      exact hA (valExp V x).toNat hk x hx heq
    have htriv : ∀ x : L, x ≠ 0 → V x = 1 := by
      intro x hx
      have h1 : valExp V x ≤ 0 := hnonpos x hx
      have h2 : 0 ≤ valExp V x := by
        have hh := hnonpos x⁻¹ (inv_ne_zero hx)
        rw [valExp_inv] at hh
        omega
      rw [← valExp_exp V hx, le_antisymm h1 h2, WithZero.exp_zero]
    intro x
    by_cases hx : x = 0
    · subst hx; simp
    · rw [htriv (φ x) (eqv_ne φ hx), htriv x hx]

end Work.MotV5.RigAS.ValuationAux
