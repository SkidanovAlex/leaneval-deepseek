/-
# Non-aliasing of the exact-height IW frequencies at the repaired window

`Work.Analysis.LoMixedPorts.nonAliasLeOne`: for `0 < ρ ≤ 1`, `d ≥ 2` and all `l₂, k₁, k₂`, the
exact-height Ionescu–Wainger frequency set `diffFreqs ρ l₂` is **non-aliased** at the arc radius
`2^{-2·d·u}` of the repaired window

`u = loMixedU ρ d l₂ k₁ k₂ = max (uScale ρ L) (d·l₂ + 3)`,  `L = max l₂ (max k₁ k₂)`
(`Work.KMTAreas.A7.loMixedU`), i.e. the arcs `α + ℝ_{≤k}`, `α ∈ diffFreqs ρ l₂`, of radius
`2^k`, `k = -(2·d·u)`, are pairwise disjoint in `ℝ/ℤ`.

## How this is proved here

The statement is a specialisation of the *repaired-window* non-aliasing
`Work.KMTAreas.A7.uRep_nonAliasing`, which is proved for **every** `0 < ρ ≤ 1` (the sibling
`Work.KMTAreas.A7.LpNonAliasAtWindow` is the same statement for the same window but only for
`ρ ≤ 1/8`).  The `uRep` window is

`uRep ρ l₁ l₂ k₁ k₂ = max (uScale ρ (max (max l₁ l₂) (max k₁ k₂))) (max l₁ l₂ + 3)`

and the two reductions are:

* **Window comparison.**  At `l₁ = l₂` the `uScale` arguments coincide,
  `max (max l l) (max k₁ k₂) = max (max 0 l) (max k₁ k₂)`, while `l + 3 ≤ d·l + 3` for `1 ≤ d`;
  hence `uRep ρ l l k₁ k₂ ≤ loMixedU ρ d l k₁ k₂` (`uRep_le_loMixedU`).
* **Monotonicity in the radius.**  `NonAliasing k A` becomes *easier* as `k` decreases
  (`realArc k ⊆ realArc k'` for `k ≤ k'`), so non-aliasing at the larger arc
  `1 - 2·uRep ρ l l k₁ k₂` of `uRep_nonAliasing` transfers to the smaller arc
  `-(2·d·u) = -(d·2·loMixedU ρ d l₂ k₁ k₂)` of `loMixedU`
  (`nonAliasing_mono` + the integer comparison `2·uRep ≤ d·2·loMixedU`, which is immediate from
  `uRep ≤ loMixedU` and `2 ≤ d`).

The quantitative separation of the exact-height fibres (the two regimes `l ≤ iwC0 ρ` and
`l > iwC0 ρ` of `iwP ρ l`, with the denominator bound `T = Q_0^{(l)}·(2^l)^{D_ρ²}` and the
separations `1/T²`, respectively `2^{-2l}`) is entirely contained in `uRep_nonAliasing`; nothing
here re-derives it.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.uRep_nonAliasing

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Work.Analysis.LoMixedPorts

open Work.KMTAreas.A7

noncomputable section

/-- **Monotonicity of non-aliasing in the arc radius.**  Non-aliasing at a *wider* arc implies
non-aliasing at every narrower one: `NonAliasing k' A → k ≤ k' → NonAliasing k A`.

Indeed `realArc k ⊆ realArc k'` for `k ≤ k'`, so the injectivity statement for the larger arc
applies verbatim. -/
lemma nonAliasing_mono {k k' : ℤ} (hkk : k ≤ k')
    {A : Finset Work.Analysis.IonescuWainger.Circle}
    (hA : Work.Analysis.IonescuWainger.NonAliasing k' A) :
    Work.Analysis.IonescuWainger.NonAliasing k A := by
  intro α hα β hβ θ hθ θ' hθ' heq
  have hpow : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ k' := zpow_le_zpow_right₀ (by norm_num) hkk
  have h1 : θ ∈ Work.Analysis.IonescuWainger.realArc k' := by
    rw [Work.Analysis.IonescuWainger.realArc, Set.mem_Icc] at hθ ⊢
    exact ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  have h2 : θ' ∈ Work.Analysis.IonescuWainger.realArc k' := by
    rw [Work.Analysis.IonescuWainger.realArc, Set.mem_Icc] at hθ' ⊢
    exact ⟨by linarith [hθ'.1], by linarith [hθ'.2]⟩
  exact hA α hα β hβ θ h1 θ' h2 heq

/-- **The `uRep` window is dominated by the repaired window `loMixedU`** at equal arithmetic
heights `l₁ = l₂`: for `1 ≤ d`,
`uRep ρ l l k₁ k₂ ≤ loMixedU ρ d l k₁ k₂`.

The `uScale` parts agree (since `max l l = l = max 0 l`) and the additive repairs satisfy
`l + 3 ≤ d·l + 3`. -/
lemma uRep_le_loMixedU (ρ : ℝ) (d l k₁ k₂ : ℕ) (hd : 1 ≤ d) :
    uRep ρ l l k₁ k₂ ≤ loMixedU ρ d l k₁ k₂ := by
  have harg : max (max l l) (max k₁ k₂) = max (max 0 l) (max k₁ k₂) := by
    rw [max_self, max_eq_right (Nat.zero_le l)]
  rw [uRep, loMixedU, harg]
  refine max_le_max le_rfl ?_
  have hl : l ≤ d * l := Nat.le_mul_of_pos_left l (by omega)
  rw [max_self]
  omega

/-- **Non-aliasing of the exact-height IW frequencies at the repaired window.**  This is the
hypothesis `hNA₂` of `Work.KMTPlan.A6.lpSymC_sub_symMWin_eq_symD`. -/
theorem nonAliasLeOne (ρ : ℝ) (d : ℕ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hd : 2 ≤ d)
    (l₂ k₁ k₂ : ℕ) :
    Work.Analysis.IonescuWainger.NonAliasing (-((d : ℤ) * 2 * (Work.KMTAreas.A7.loMixedU ρ d l₂ k₁ k₂ : ℤ)))
      (Work.KMTAreas.A7.diffFreqs ρ l₂) := by
  refine nonAliasing_mono ?_
    (uRep_nonAliasing ρ hρ hρ1 l₂ l₂ k₁ k₂ l₂ (le_max_left l₂ l₂))
  have hu : uRep ρ l₂ l₂ k₁ k₂ ≤ loMixedU ρ d l₂ k₁ k₂ :=
    uRep_le_loMixedU ρ d l₂ k₁ k₂ (by omega)
  have hkey : 2 * uRep ρ l₂ l₂ k₁ k₂ ≤ d * 2 * loMixedU ρ d l₂ k₁ k₂ := by
    calc 2 * uRep ρ l₂ l₂ k₁ k₂ ≤ 2 * loMixedU ρ d l₂ k₁ k₂ := Nat.mul_le_mul_left 2 hu
      _ ≤ d * 2 * loMixedU ρ d l₂ k₁ k₂ := Nat.mul_le_mul_right _ (by omega)
  have hkeyZ : ((2 * uRep ρ l₂ l₂ k₁ k₂ : ℕ) : ℤ)
      ≤ ((d * 2 * loMixedU ρ d l₂ k₁ k₂ : ℕ) : ℤ) := by exact_mod_cast hkey
  push_cast at hkeyZ
  linarith

end

end Work.Analysis.LoMixedPorts
