import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLContract.Interfaces
import Submission.Work.EKLC6Core.uniform_injective_V_X3
import Submission.Work.EKLC6Core.V_inv_mul_linear
import Submission.Work.Misiurewicz.exists_null_frontier_Vball_radius

/-!
# `Work.EKLC6Core.InjRadius` — the injectivity radius of the orbit maps on `X₃`

`X₃ = SL₃(ℝ)/SL₃(ℤ)` is not injective "uniformly": the entrywise displacement neighbourhood
`V ρ` of the identity acts injectively on `V ρ • x` only for `ρ` below the *injectivity radius*
of `x`, which tends to `0` in the cusp.  Every point `x`, however, *does* have a positive
injectivity radius (the stabiliser of `x` is a conjugate of the discrete group `Γ₃`), and that
radius is *lower semicontinuous* in the quantitative sense proved here
(`injCap_mem_V_le`): moving `x` by a small `w ∈ V a` can only lower the (capped) injectivity
radius by a bounded factor.

This is the geometric input of `Work.EKLC6Core.cell_cover_exists`: it is what makes the
"good" balls around the points of a countable dense set cover all of `X₃`.

## Main definitions

* `InjAt x ρ` — the orbit map `v ↦ v • x` is injective on `V ρ`;
* `injS x` — the injectivity radius of `x`, capped at `1` (the supremum of the `ρ` with
  `InjAt x ρ`);
* `injCap x = min (injS x) (1/2)` — the capped radius used for the cell construction.

## Main results

* `exists_injAt` — every point has a positive injectivity radius (from the frozen component
  `P_X3`, via `Work.EKLC6Core.uniform_injective_V_X3` at a singleton);
* `V_mul_subset_V` — `V s * V t ⊆ V (s + t + 3 s t)` (entrywise, from
  `Work.EKLRelCross.entries_mul_sub_one_le`);
* `InjAt.transfer` — injectivity at `x` for `V r` transfers to injectivity at `w • x` for
  `V (r/4)` whenever `w ∈ V a` with `a ≤ r/2`;
* `injCap_mem_V_le` — the quantitative lower semicontinuity of `injCap`.
-/

namespace Work.EKLC6Core

open Work.EKLContract

noncomputable section

/-! ## Injectivity of the orbit maps -/

/-- `InjAt x ρ`: the orbit map `v ↦ v • x` is injective on the displacement neighbourhood
`V ρ = {v : SL₃(ℝ) | |v i j - 1 i j| < ρ ∀ i j}`. -/
def InjAt (x : X3) (ρ : ℝ) : Prop :=
  ∀ v₁ v₂ : SL3, v₁ ∈ V ρ → v₂ ∈ V ρ → v₁ • x = v₂ • x → v₁ = v₂

/-- Injectivity is monotone in the radius. -/
theorem InjAt.mono {x : X3} {ρ ρ' : ℝ} (h : InjAt x ρ) (hρ : ρ' ≤ ρ) : InjAt x ρ' :=
  fun v₁ v₂ h₁ h₂ hxy =>
    h v₁ v₂ (Work.Misiurewicz.V_mono hρ h₁) (Work.Misiurewicz.V_mono hρ h₂) hxy

/-- **Every point of `X₃` has a positive injectivity radius.**  This is the uniform injectivity
of the orbit maps on the compact set `{x}` (the fourth conjunct of the frozen `P_X3`). -/
theorem exists_injAt (x : X3) : ∃ ρ : ℝ, 0 < ρ ∧ InjAt x ρ := by
  obtain ⟨δ, hδ, huniq⟩ := uniform_injective_V_X3 ({x} : Set X3) isCompact_singleton
  refine ⟨δ / 4, by linarith, fun v₁ v₂ h₁ h₂ hxy =>
    huniq x rfl v₁ (Work.Misiurewicz.V_mono (by linarith) h₁) v₂
      (Work.Misiurewicz.V_mono (by linarith) h₂) hxy⟩

/-! ## The (capped) injectivity radius -/

/-- The injectivity radius of `x`, capped at `1` so that it is a bounded quantity. -/
def injS (x : X3) : ℝ := sSup {t : ℝ | 0 < t ∧ t ≤ 1 ∧ InjAt x t}

/-- The capped injectivity radius used for the cells: `min (injS x) (1/2)`. -/
def injCap (x : X3) : ℝ := min (injS x) (1 / 2)

theorem injSet_nonempty (x : X3) : ({t : ℝ | 0 < t ∧ t ≤ 1 ∧ InjAt x t}).Nonempty := by
  obtain ⟨ρ, hρ, h⟩ := exists_injAt x
  exact ⟨min ρ 1, lt_min hρ one_pos, min_le_right _ _, h.mono (min_le_left _ _)⟩

theorem injSet_bddAbove (x : X3) : BddAbove {t : ℝ | 0 < t ∧ t ≤ 1 ∧ InjAt x t} :=
  ⟨1, fun t ht => ht.2.1⟩

theorem injS_pos (x : X3) : 0 < injS x := by
  obtain ⟨t, ht⟩ := injSet_nonempty x
  exact lt_of_lt_of_le ht.1 (le_csSup (injSet_bddAbove x) ht)

theorem injS_le_one (x : X3) : injS x ≤ 1 :=
  csSup_le (injSet_nonempty x) fun t ht => ht.2.1

theorem injCap_pos (x : X3) : 0 < injCap x := lt_min (injS_pos x) (by norm_num)

theorem injCap_le_half (x : X3) : injCap x ≤ 1 / 2 := min_le_right _ _

theorem injCap_le_injS (x : X3) : injCap x ≤ injS x := min_le_left _ _

/-- Any radius strictly below the injectivity radius is injective. -/
theorem injAt_of_lt_injS {x : X3} {t : ℝ} (ht : 0 < t) (h : t < injS x) : InjAt x t := by
  by_contra hcon
  have hle : injS x ≤ t := by
    refine csSup_le (injSet_nonempty x) fun s hs => ?_
    by_contra hs'
    exact hcon (hs.2.2.mono (le_of_lt (lt_of_not_ge hs')))
  linarith

/-- Any radius strictly below the capped injectivity radius is injective. -/
theorem injAt_of_lt_injCap {x : X3} {t : ℝ} (ht : 0 < t) (h : t < injCap x) : InjAt x t :=
  injAt_of_lt_injS ht (lt_of_lt_of_le h (injCap_le_injS x))

/-! ## The product estimate for `V` -/

/-- **The entrywise product estimate**: `V s * V t ⊆ V (s + t + 3 s t)`.

If `A = 1 + A'` and `B = 1 + B'` with `|A'| < s`, `|B'| < t` entrywise, then
`A B - 1 = A' B' + A' + B'`, and the three entries of `A' B'` are each bounded by `s t`. -/
theorem V_mul_subset_V {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) {a b : SL3} (ha : a ∈ V s)
    (hb : b ∈ V t) : a * b ∈ V (s + t + 3 * s * t) := by
  intro i j
  exact Work.EKLRelCross.entries_mul_sub_one_le (A := (a : Matrix (Fin 3) (Fin 3) ℝ))
    (B := (b : Matrix (Fin 3) (Fin 3) ℝ)) i j ha hb hs ht

/-! ## Transfer of injectivity and lower semicontinuity of `injCap` -/

/-- **Injectivity transfers under small perturbations.**  If `V r` acts injectively at `x` and
`w ∈ V a` with `a ≤ r/2`, `a ≤ 1/2`, `r ≤ 1/2`, then `V (r/4)` acts injectively at `w • x`.

Indeed if `v₁, v₂ ∈ V (r/4)` and `v₁ w • x = v₂ w • x`, then `v_i w ∈ V (r/4) V a ⊆ V r` because
`r/4 + a + 3 (r/4) a ≤ r`, so injectivity at `x` gives `v₁ w = v₂ w`, i.e. `v₁ = v₂`. -/
theorem InjAt.transfer {x : X3} {r a : ℝ} (h : InjAt x r) (hr : r ≤ 1 / 2) (ha : 0 ≤ a)
    (ha2 : a ≤ 1 / 2) (har : a ≤ r / 2) {w : SL3} (hw : w ∈ V a) : InjAt (w • x) (r / 4) := by
  have hr0 : 0 ≤ r := by linarith
  intro v₁ v₂ h₁ h₂ hxy
  have hra : r * a ≤ r * (r / 2) := mul_le_mul_of_nonneg_left har hr0
  have hmem : ∀ {v : SL3}, v ∈ V (r / 4) → v * w ∈ V r := by
    intro v hv
    refine Work.Misiurewicz.V_mono ?_ (V_mul_subset_V (s := r / 4) (t := a) (by linarith) ha hv hw)
    nlinarith [hra, hr, ha, har]
  have heq : (v₁ * w) • x = (v₂ * w) • x := by
    rw [mul_smul, mul_smul]
    exact hxy
  exact mul_right_cancel (h (v₁ * w) (v₂ * w) (hmem h₁) (hmem h₂) heq)

/-- **Quantitative lower semicontinuity of the injectivity radius.**  A perturbation of `x` by
`w ∈ V a` with `a ≤ injCap x / 8` (and `a ≤ 1/2`) drops the capped injectivity radius by at most
a factor `8`. -/
theorem injCap_mem_V_le {x : X3} {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 1 / 2)
    (ha8 : a ≤ injCap x / 8) {w : SL3} (hw : w ∈ V a) : injCap x / 16 ≤ injCap (w • x) := by
  have hP : 0 < injCap x := injCap_pos x
  have h1 : InjAt x (injCap x / 4) := injAt_of_lt_injCap (by linarith) (by linarith)
  have h2 : InjAt (w • x) (injCap x / 16) := by
    have h := h1.transfer (r := injCap x / 4) (a := a) (by linarith [injCap_le_half x])
      (le_of_lt ha) ha2 (by linarith) hw
    rwa [show injCap x / 4 / 4 = injCap x / 16 by ring] at h
  have h3 : injCap x / 16 ≤ injS (w • x) := by
    refine le_csSup (injSet_bddAbove _) ?_
    exact ⟨by linarith, by linarith [injCap_le_half x], h2⟩
  exact le_min h3 (by linarith [injCap_le_half x])

end

end Work.EKLC6Core
