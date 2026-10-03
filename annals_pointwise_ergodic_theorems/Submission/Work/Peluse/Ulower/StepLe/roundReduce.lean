import Mathlib
import Submission.Work.Peluse.Ulower.StepLe.aggr_round
import Submission.Work.Peluse.Ulower.StepLe.blindConvertK_frac

/-!
# Rounding the phases of the aggregate, with a quantitative grid mesh

The aggregate `aggr σ D B F β` (the average, over the pair box `[1,D]^σ × [1,D]^σ`, of the squared
moduli of the `B⁻¹`-normalised correlations of the level-`σ` cube terms of `F` at the phases `β`)
is stable under rounding the phases to the rational grid `(1/T)ℤ`, provided the mesh `1/T` is
small compared with `√γ` (`aggr_round`, `aggr_round_aux`).

This file records the *quantitative* form needed downstream: from `γ ≤ aggr β` one can extract a
mesh `T` with

* `4π(2B+1)/T ≤ √γ` (so that the rounding loses only a factor `2`), and
* `T ≤ 2 + 4π(2B+1)/√γ` (so that `T` is the *smallest* such mesh up to an additive `2`),

together with a phase family `β'` which is `T`-grid-valued, takes values in `[0,1]`, and still
satisfies `γ/2 ≤ aggr β'`.

The range constraint `0 ≤ β' ≤ 1` is obtained by first replacing `β` by its fractional part
(`cubeCorr_frac`: the aggregate only sees the phases modulo `1`) and then rounding; the mesh is
`T = max 1 ⌈4π(2B+1)/√γ⌉₊`.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.Ulower.StepLe

noncomputable section

theorem roundReduce {σ D B S : ℕ} {F : ℤ → ℂ}
    (β : (Fin σ → ℤ) → (Fin σ → ℤ) → ℝ) (hB : 1 ≤ B) (hD : 1 ≤ D)
    (hF1 : ∀ x : ℤ, ‖F x‖ ≤ 1) (hFs : Work.Peluse.SupportIn F S)
    (hSB : S + σ * D ≤ B) {γ : ℝ} (hγ : 0 < γ)
    (haggr : γ ≤ Work.Peluse.Ulower.StepLe.aggr σ D B F β) :
    ∃ (T : ℕ) (β' : (Fin σ → ℤ) → (Fin σ → ℤ) → ℝ),
      1 ≤ T ∧ 4 * Real.pi * ((2 * B + 1 : ℕ) : ℝ) / (T : ℝ) ≤ Real.sqrt γ ∧
      (T : ℝ) ≤ 2 + 4 * Real.pi * ((2 * B + 1 : ℕ) : ℝ) / Real.sqrt γ ∧
      (∀ u v, ∃ m : ℤ, β' u v = (m : ℝ) / (T : ℝ)) ∧
      (∀ u v, 0 ≤ β' u v) ∧ (∀ u v, β' u v ≤ 1) ∧
      γ / 2 ≤ Work.Peluse.Ulower.StepLe.aggr σ D B F β' := by
  classical
  -- The mesh `T` and the auxiliary constant `c = 4π(2B+1)`.
  set c : ℝ := 4 * Real.pi * ((2 * B + 1 : ℕ) : ℝ) with hc
  -- The aggregate only depends on the phases modulo `1`: pass to fractional parts.
  set β₀ : (Fin σ → ℤ) → (Fin σ → ℤ) → ℝ := fun u v => β u v - (⌊β u v⌋ : ℝ) with hβ₀
  have haggr₀ : γ ≤ aggr σ D B F β₀ := by
    have h : aggr σ D B F β₀ = aggr σ D B F β := by
      rw [aggr, aggr]
      congr 1
      refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
      exact cubeCorr_frac F β u v
    rw [h]; exact haggr
  have hγpos : 0 < Real.sqrt γ := Real.sqrt_pos.mpr hγ
  have hcpos : 0 < c := by rw [hc]; positivity
  set T : ℕ := max 1 ⌈c / Real.sqrt γ⌉₊ with hT
  have hT1 : 1 ≤ T := le_max_left _ _
  have hTpos : (0 : ℝ) < (T : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hT1)
  -- The mesh is large enough.
  have hTge : c / Real.sqrt γ ≤ (T : ℝ) := by
    refine le_trans (Nat.le_ceil _) ?_
    exact_mod_cast le_max_right 1 ⌈c / Real.sqrt γ⌉₊
  have hTbig : c / (T : ℝ) ≤ Real.sqrt γ := by
    rw [div_le_iff₀ hTpos]
    have h := (div_le_iff₀ hγpos).mp hTge
    linarith
  -- and not larger than needed (up to the additive `2`).
  have hTle : (T : ℝ) ≤ 2 + c / Real.sqrt γ := by
    have hc0 : 0 ≤ c / Real.sqrt γ := by positivity
    have hceil : ((⌈c / Real.sqrt γ⌉₊ : ℕ) : ℝ) < c / Real.sqrt γ + 1 := Nat.ceil_lt_add_one hc0
    have hcast : (T : ℝ) = max 1 ((⌈c / Real.sqrt γ⌉₊ : ℕ) : ℝ) := by
      rw [hT, Nat.cast_max]
      norm_num
    rw [hcast]
    exact max_le (by linarith) (by linarith)
  -- The rounded phase family.
  set β' : (Fin σ → ℤ) → (Fin σ → ℤ) → ℝ :=
    fun u v => (round ((T : ℝ) * β₀ u v) : ℝ) / (T : ℝ) with hβ'
  have hcloseness : ∀ u v : Fin σ → ℤ, |β₀ u v - β' u v| ≤ 1 / (2 * (T : ℝ)) := by
    intro u v
    have h := abs_sub_round ((T : ℝ) * β₀ u v)
    have h2 : β₀ u v - (round ((T : ℝ) * β₀ u v) : ℝ) / (T : ℝ)
        = ((T : ℝ) * β₀ u v - (round ((T : ℝ) * β₀ u v) : ℝ)) / (T : ℝ) := by
      field_simp
    simp only [hβ']
    rw [h2, abs_div, abs_of_pos hTpos]
    rw [div_le_iff₀ hTpos]
    have harith : (1 / (2 * (T : ℝ))) * (T : ℝ) = 1 / 2 := by field_simp
    linarith [h, harith]
  have hmid : γ / 2 ≤ aggr σ D B F β' :=
    aggr_round_aux β₀ β' hB hD hF1 hFs hSB hγ haggr₀ hT1 hcloseness (by simpa [hc] using hTbig)
  refine ⟨T, β', hT1, ?_, ?_, ?_, ?_, ?_, hmid⟩
  · simpa [hc] using hTbig
  · simpa [hc] using hTle
  · -- grid-valued
    intro u v
    exact ⟨round ((T : ℝ) * β₀ u v), by simp only [hβ']⟩
  · -- nonnegativity
    intro u v
    have hb0 : 0 ≤ β₀ u v := by
      simp only [hβ₀]
      have := Int.floor_le (β u v)
      linarith
    have hw : (0 : ℝ) ≤ (T : ℝ) * β₀ u v := mul_nonneg hTpos.le hb0
    have : (0 : ℤ) ≤ round ((T : ℝ) * β₀ u v) := by
      rw [round_eq, Int.le_floor]; linarith
    simp only [hβ']
    exact div_nonneg (by exact_mod_cast this) hTpos.le
  · -- bounded by `1`
    intro u v
    have hb1 : β₀ u v ≤ 1 := by
      simp only [hβ₀]
      have := Int.lt_floor_add_one (β u v)
      linarith
    have hle : round ((T : ℝ) * β₀ u v) ≤ (T : ℤ) := by
      rw [round_eq, Int.floor_le_iff]
      push_cast
      have hw : (T : ℝ) * β₀ u v ≤ (T : ℝ) :=
        by simpa using mul_le_mul_of_nonneg_left hb1 hTpos.le
      linarith
    simp only [hβ']
    rw [div_le_one hTpos]
    exact_mod_cast hle

end

end Work.Peluse.Ulower.StepLe
