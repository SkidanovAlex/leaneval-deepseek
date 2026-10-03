/-
# Non-aliasing of the exact-height frequency sets `diffFreqs ρ l` (Lemma `ssu`, non-aliasing)

This module proves `Work.KMTPlan.A6.ssuNonAliasing`: the exact-height Ionescu--Wainger
frequency sets `diffFreqs ρ l` are non-aliasing at any arc radius `2^k` with

`k ≤ -(C · (1 + l · 2^{ρ l/2} + l) + 2)`,

for a constant `C > 0` depending only on `ρ ∈ (0,1]`.

The mathematics is the sharp separation of the arithmetic frequency set `(ℚ/ℤ)_{≤l}`,
`Work.KMTPlan.A6.iwArithFreqs_separated`: two distinct elements of `(ℚ/ℤ)_{≤l}` are at
circle distance at least `2^{-C(1 + l 2^{ρ l / 2} + l)}`.  Since `diffFreqs ρ l ⊆ (ℚ/ℤ)_{≤l}`,
any two distinct exact-height frequencies at the same level are separated by that amount, and
a separated set is non-aliasing at any scale whose arc has half-width below half the separation.

The two elementary steps are localised in

* `ssuNonAliasing_of_sep` — a *separated* set of frequencies is non-aliasing (with the extra
  hypothesis that the arc `ℝ_{≤k}` has `2·2^k < 1`, which is what makes the real parameter of
  an arc element unique on the arc);
* `ssuNonAliasing_coe_injective_of_abs_lt_one` — the coefficient map `ℝ → ℝ/ℤ` is injective
  on a set of diameter `< 1`.

## Main result

* `Work.KMTPlan.A6.ssuNonAliasing`
-/
import Mathlib
import Submission.Work.KMTPlan.A6.SsuDefs

namespace Work.KMTPlan.A6

open MeasureTheory Polynomial Finset
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger Work.KMTAreas.A7

/-- **The coefficient map `ℝ → ℝ/ℤ` is injective on a set of diameter `< 1`.**  If two reals
have the same class modulo `ℤ` and `|θ - θ'| < 1`, then `θ = θ'`. -/
private lemma ssuNonAliasing_coe_injective_of_abs_lt_one {θ θ' : ℝ}
    (h : ((θ : Work.Analysis.IonescuWainger.Circle)
        = (θ' : Work.Analysis.IonescuWainger.Circle)))
    (hbd : |θ - θ'| < 1) : θ = θ' := by
  have h2 : ((θ - θ' : ℝ) : Work.Analysis.IonescuWainger.Circle) = 0 := by
    rw [AddCircle.coe_sub, h, sub_self]
  have hz : θ - θ' ∈ AddSubgroup.zmultiples (1 : ℝ) :=
    (QuotientAddGroup.eq_zero_iff (θ - θ')).mp h2
  obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp hz
  rw [zsmul_eq_mul, mul_one] at hn
  have habs : |(n : ℝ)| < 1 := by rw [hn]; exact hbd
  have hn0 : n = 0 := by
    have := abs_lt.mp habs
    have h1 : (-1 : ℤ) < n := by exact_mod_cast this.1
    have h2' : n < (1 : ℤ) := by exact_mod_cast this.2
    omega
  rw [hn0] at hn
  push_cast at hn
  linarith

/-- **A separated frequency set is non-aliasing.**  If every two distinct elements of `A` are at
circle distance `> 2 · 2^k`, and the arc `ℝ_{≤k}` is short enough that the coefficient map is
injective on it (`2 · 2^k < 1`), then `A` is non-aliasing at scale `k`. -/
private lemma ssuNonAliasing_of_sep {k : ℤ} {A : Finset Work.Analysis.IonescuWainger.Circle}
    (harc : 2 * (2 : ℝ) ^ k < 1)
    (h : ∀ α ∈ A, ∀ β ∈ A, α ≠ β → 2 * (2 : ℝ) ^ k < ‖α - β‖) :
    Work.Analysis.IonescuWainger.NonAliasing k A := by
  intro α hα β hβ θ hθ θ' hθ' heq
  have hθmem : θ ∈ Set.Icc (-(2 : ℝ) ^ k) ((2 : ℝ) ^ k) := hθ
  have hθ'mem : θ' ∈ Set.Icc (-(2 : ℝ) ^ k) ((2 : ℝ) ^ k) := hθ'
  have hθabs : |θ| ≤ (2 : ℝ) ^ k := abs_le.mpr ⟨hθmem.1, hθmem.2⟩
  have hθ'abs : |θ'| ≤ (2 : ℝ) ^ k := abs_le.mpr ⟨hθ'mem.1, hθ'mem.2⟩
  -- the two arc parameters differ by at most `2 · 2^k`
  have hsub : |θ' - θ| ≤ 2 * (2 : ℝ) ^ k := by
    have h1 : |θ' - θ| ≤ |θ'| + |θ| := by
      simpa [sub_eq_add_neg] using abs_add_le θ' (-θ)
    linarith
  by_cases hne : α = β
  · -- then the arc parameters agree, by injectivity of the coefficient map on the short arc
    refine ⟨hne, ?_⟩
    have heqc : (θ : Work.Analysis.IonescuWainger.Circle)
        = (θ' : Work.Analysis.IonescuWainger.Circle) := by
      have hh := heq
      rw [hne] at hh
      exact add_left_cancel hh
    have hbd : |θ - θ'| < 1 := by rw [abs_sub_comm]; linarith
    exact ssuNonAliasing_coe_injective_of_abs_lt_one heqc hbd
  · -- otherwise the two arcs overlap: contradiction with the separation
    exfalso
    have h1 : ((θ' - θ : ℝ) : Work.Analysis.IonescuWainger.Circle) = α - β := by
      rw [AddCircle.coe_sub, sub_eq_sub_iff_add_eq_add]
      rw [add_comm ((θ' : ℝ) : Work.Analysis.IonescuWainger.Circle) β]
      exact heq.symm
    have hle : ‖α - β‖ ≤ 2 * (2 : ℝ) ^ k := by
      calc ‖α - β‖
          = ‖((θ' - θ : ℝ) : Work.Analysis.IonescuWainger.Circle)‖ := by rw [← h1]
        _ ≤ |θ' - θ| := by
            simpa [Real.norm_eq_abs, AddCircle] using
              (@QuotientAddGroup.norm_mk_le_norm ℝ _ (AddSubgroup.zmultiples (1 : ℝ))
                (θ' - θ))
        _ ≤ 2 * (2 : ℝ) ^ k := hsub
    linarith [h α hα β hβ hne]

/-- **Non-aliasing of the exact-height frequency sets.**  Let `0 < ρ ≤ 1`.  There is a constant
`C > 0` such that for every level `l` and every scale `k` with
`C * (1 + l 2^{ρ l/2} + l) + 2 ≤ -k`, the exact-height frequency set `diffFreqs ρ l` is
non-aliasing at scale `k`. -/
theorem ssuNonAliasing (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (l : ℕ) (k : ℤ),
      C * (1 + (l : ℝ) * (2 : ℝ) ^ (ρ * (l : ℝ) / 2) + (l : ℝ)) + 2 ≤ -(k : ℝ) →
      NonAliasing k (Work.KMTAreas.A7.diffFreqs ρ l) := by
  -- the sharp separation of `(ℚ/ℤ)_{≤l}`
  obtain ⟨C₀, hC₀pos, hsep⟩ := iwArithFreqs_separated ρ hρ hρ1
  refine ⟨C₀, hC₀pos, ?_⟩
  intro l k hk
  set S : ℝ := 1 + (l : ℝ) * (2 : ℝ) ^ (ρ * (l : ℝ) / 2) + (l : ℝ) with hS
  have hS1 : 1 ≤ S := by
    rw [hS]
    have ht : (0 : ℝ) ≤ (l : ℝ) * (2 : ℝ) ^ (ρ * (l : ℝ) / 2) :=
      mul_nonneg (Nat.cast_nonneg l) (Real.rpow_nonneg (by norm_num) _)
    linarith [Nat.cast_nonneg (α := ℝ) l]
  have hk' : (k : ℝ) + 1 < -(C₀ * S) := by linarith
  -- the arc half-width `2 · 2^k` is below the separation `2^{-C₀ S}`
  have hkey : 2 * (2 : ℝ) ^ k < (2 : ℝ) ^ (-(C₀ * S)) := by
    have h2k : 2 * (2 : ℝ) ^ k = (2 : ℝ) ^ (k + 1) := by
      rw [zpow_add₀ (show (2 : ℝ) ≠ 0 from by norm_num) k (1 : ℤ), zpow_one]
      ring
    rw [h2k]
    have hcast : (((k + 1 : ℤ)) : ℝ) < -(C₀ * S) := by push_cast; linarith
    rw [← Real.rpow_intCast (2 : ℝ) (k + 1)]
    exact (Real.rpow_lt_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mpr hcast
  have hle1 : (2 : ℝ) ^ (-(C₀ * S)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
      (by nlinarith [hC₀pos.le, hS1])
  refine ssuNonAliasing_of_sep (by linarith) ?_
  intro α hα β hβ hne
  -- the exact-height set sits inside the height-`≤ l` set
  have hsub : Work.KMTAreas.A7.diffFreqs ρ l ⊆ iwArithFreqs ρ l := by
    intro x hx
    by_cases h0 : l = 0
    · subst h0
      rwa [Work.KMTAreas.A7.diffFreqs, if_pos rfl] at hx
    · rw [Work.KMTAreas.A7.diffFreqs, if_neg h0, Finset.mem_sdiff] at hx
      exact hx.1
  have h1 := hsep l α β (hsub hα) (hsub hβ) hne
  have h1' : (2 : ℝ) ^ (-(C₀ * S)) ≤ ‖α - β‖ := by rw [hS]; exact h1
  exact lt_of_lt_of_le hkey h1'

end Work.KMTPlan.A6
