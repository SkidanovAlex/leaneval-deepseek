import Mathlib
import Submission.Work.KMTAreas.A7.SmallExcBound
import Submission.Work.KMTAreas.A7.goodRegime

/-!
# Monotonicity of the core index condition `core` in the parameter `ρ`

The core index condition `Work.KMTAreas.A7.core ρ C₀ l₁ l₂ k₁ k₂ a n` is the conjunction of

* the admissibility `inIndexSet C₀ (max l₁ l₂) k₁ k₂ ⌊a n⌋` (independent of `ρ`),
* the large-scale cut `splitCut ρ L < ⌊a n⌋`, with `L = max (max l₁ l₂) (max k₁ k₂)`, and
* the main regime `mainRegime ρ k₁ k₂ ⌊a n⌋`, i.e. `k + 2 u ≤ Log ⌊a n⌋` with
  `u = uScale ρ (max k₁ k₂)`.

Both `ρ`-dependent clauses are *monotone in `ρ`*: `splitCut ρ L = 2^{2^{⌊2^{2ρL}}⌋}}` and
`uScale ρ L = ⌊2^{2ρL}⌋` are non-decreasing in `ρ` (the exponent `2ρL` is non-decreasing because
`L ≥ 0`; `x ↦ 2^x` is non-decreasing on `ℝ`; floor and `Int.toNat` are monotone).  Hence `core` is
antitone in `ρ`: decreasing the parameter `ρ` can only make the cutoff smaller and the main regime
easier, so the core condition persists.

This is the (elementary) bookkeeping monotonicity needed to pass the area-`A6` estimates at a
parameter `ρ` down to a smaller parameter `ρ' ≤ ρ`.
-/

namespace Work.KMTPlan.A6.LowModApproxBoundedH

/-- The auxiliary scale `u = uScale ρ L = ⌊2^{2ρL}⌋` is monotone in `ρ`.  (Restatement of
`Work.KMTAreas.A7.uScale_mono_rho` in the local namespace.) -/
theorem uScale_mono_rho' (L : ℕ) : Monotone (fun ρ : ℝ => Work.KMTAreas.A7.uScale ρ L) :=
  Work.KMTAreas.A7.uScale_mono_rho L

/-- The large-scale threshold `splitCut ρ L = 2^{2^{uScale ρ L}}` is monotone in `ρ`. -/
theorem splitCut_mono_rho (L : ℕ) : Monotone (fun ρ : ℝ => Work.KMTAreas.A7.splitCut ρ L) := by
  intro ρ' ρ h
  have hsc : Work.Analysis.EndVar.scaleCount 1 ρ' L ≤ Work.Analysis.EndVar.scaleCount 1 ρ L :=
    (Work.KMTAreas.A7.uScale_mono_rho L) h
  simp only [Work.KMTAreas.A7.splitCut]
  exact Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by norm_num) hsc)

/-- The main regime `mainRegime ρ k₁ k₂ N` persists when `ρ` is decreased. -/
theorem mainRegime_mono_rho {ρ ρ' : ℝ} (h : ρ' ≤ ρ) (k₁ k₂ N : ℕ) :
    Work.KMTAreas.A7.mainRegime ρ k₁ k₂ N → Work.KMTAreas.A7.mainRegime ρ' k₁ k₂ N := by
  intro hm
  obtain ⟨h1, h2⟩ := hm
  have hu : Work.KMTAreas.A7.uScale ρ' (max k₁ k₂) ≤ Work.KMTAreas.A7.uScale ρ (max k₁ k₂) :=
    (Work.KMTAreas.A7.uScale_mono_rho (max k₁ k₂)) h
  have hu2 : 2 * Work.KMTAreas.A7.uScale ρ' (max k₁ k₂)
      ≤ 2 * Work.KMTAreas.A7.uScale ρ (max k₁ k₂) :=
    Nat.mul_le_mul_left 2 hu
  exact ⟨le_trans (Nat.add_le_add_left hu2 k₁) h1, le_trans (Nat.add_le_add_left hu2 k₂) h2⟩

theorem lvl0CoreMono {ρ ρ' : ℝ} (h : ρ' ≤ ρ) (C₀ : ℕ) (l₁ l₂ k₁ k₂ : ℕ) (a : ℕ → NNReal) (n : ℕ) :
    Work.KMTAreas.A7.core ρ C₀ l₁ l₂ k₁ k₂ a n → Work.KMTAreas.A7.core ρ' C₀ l₁ l₂ k₁ k₂ a n := by
  intro hn
  obtain ⟨hin, hcut, hmain⟩ := hn
  exact ⟨hin, lt_of_le_of_lt (splitCut_mono_rho _ h) hcut,
    mainRegime_mono_rho h k₁ k₂ _ hmain⟩

end Work.KMTPlan.A6.LowModApproxBoundedH
