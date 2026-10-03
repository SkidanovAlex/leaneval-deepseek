/-
# The main regime of the large-scale analysis is automatic above a threshold in `L`

This module proves `Work.KMTPlan.A6.mainRegimeOfHeightScale`, the small combinatorial input of
area A6: **on the admissible index set and for large enough `L = max(max l₁ l₂)(max k₁ k₂)`, the
scale `N` is automatically in the main regime `k + 2u ≤ Log N`.**

Concretely, with `N ∈ I^{max(l₁,l₂),k₁,k₂}`, i.e. `lᵢ, kᵢ ≤ l_{(N)} = C₀ LogLog N`, and
`L = lcL l₁ l₂ k₁ k₂ = max(max l₁ l₂)(max k₁ k₂) ≥ B`, one has

  `k + 2 ⌊2^{2ρ max k₁ k₂}⌋ ≤ Log N`  for `k = k₁, k₂`  (`Work.KMTAreas.A7.mainRegime`).

## The mathematics

Write `R = Log N = ⌊log₂ N⌋` and `q = LogLog N = ⌊log₂ (R+2)⌋`, so that `2^q ≤ R + 2`, i.e.
`R ≥ 2^q - 2`.  Admissibility gives `kᵢ ≤ C₀ q` and, since `max k₁ k₂ ≤ L ≤ C₀ q`,

  `⌊2^{2ρ max k₁ k₂}⌋ ≤ 2^{2ρL} ≤ 2^{2ρC₀q} ≤ 2^{q/2}`,

the last step because `ρC₀ ≤ 1/4`.  Hence it suffices that

  `C₀ q + 2·2^{q/2} ≤ 2^q - 2`,

which holds as soon as `C₀ ≤ q` and `q ≥ 8` (indeed `C₀q ≤ q² ≤ 2^q/4` and `2·2^{q/2} ≤ 2^q/4`).
Finally `L ≥ B` with `L ≤ C₀ q` forces `q ≥ B/C₀`: taking `B = C₀·max C₀ 8` gives `q ≥ max C₀ 8`,
which is exactly the required threshold.  Thus `B := C₀ · max C₀ 8` works.

The two numerical ingredients are delegated:
* `Work.KMTPlan.A6.mainRegimeArith` — the pure inequality `C₀ q + 2y ≤ 2^q - 2` for `C₀ ≤ q`,
  `q ≥ 8`, `k ≤ C₀ q`, `y ≤ 2^{q/2}`;
* `Work.KMTPlan.A6.uScaleHalfPow` — the floor/rpow bound `⌊2^{2ρm}⌋ ≤ 2^{q/2}` for `m ≤ L ≤ C₀ q`
  and `ρC₀ ≤ 1/4`.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.LowSmallDefs
import Submission.Work.KMTPlan.A6.mainRegimeArith
import Submission.Work.KMTPlan.A6.uScaleHalfPow

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6

open Work.Analysis.EndVar

theorem mainRegimeOfHeightScale (ρ : ℝ) (hρ : 0 < ρ) (C₀ : ℕ) (hC₀ : 1 ≤ C₀)
    (hρC : ρ * (C₀ : ℝ) ≤ 1 / 4) :
    ∃ B : ℕ, ∀ (l₁ l₂ k₁ k₂ N : ℕ),
      Work.Analysis.EndVar.inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ)) (k₁ : ℤ) (k₂ : ℤ) N →
      B ≤ Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂ →
      Work.KMTAreas.A7.mainRegime ρ k₁ k₂ N := by
  refine ⟨C₀ * max C₀ 8, ?_⟩
  intro l₁ l₂ k₁ k₂ N hidx hB
  set n := Nat.log 2 (max N 2) with hn
  set q := Work.Analysis.EndVar.logLogN N with hqdef
  have hq : q = Nat.log 2 (n + 2) := by
    rw [hqdef, hn]
    rfl
  have hheight : Work.Analysis.EndVar.heightScale C₀ N = C₀ * q := by
    rw [Work.Analysis.EndVar.heightScale, hqdef]
  rw [Work.Analysis.EndVar.inIndexSet] at hidx
  have hl₁H : l₁ ≤ Work.Analysis.EndVar.heightScale C₀ N := by
    have h : (l₁ : ℤ) ≤ (Work.Analysis.EndVar.heightScale C₀ N : ℤ) :=
      le_trans (le_max_left _ _) hidx.1
    exact_mod_cast h
  have hl₂H : l₂ ≤ Work.Analysis.EndVar.heightScale C₀ N := by
    have h : (l₂ : ℤ) ≤ (Work.Analysis.EndVar.heightScale C₀ N : ℤ) :=
      le_trans (le_max_right _ _) hidx.1
    exact_mod_cast h
  have hk₁H : k₁ ≤ Work.Analysis.EndVar.heightScale C₀ N := by
    have h : (k₁ : ℤ) ≤ (Work.Analysis.EndVar.heightScale C₀ N : ℤ) := hidx.2.1
    exact_mod_cast h
  have hk₂H : k₂ ≤ Work.Analysis.EndVar.heightScale C₀ N := by
    have h : (k₂ : ℤ) ≤ (Work.Analysis.EndVar.heightScale C₀ N : ℤ) := hidx.2.2
    exact_mod_cast h
  have hLle : lcL l₁ l₂ k₁ k₂ ≤ C₀ * q := by
    have hh : lcL l₁ l₂ k₁ k₂ ≤ Work.Analysis.EndVar.heightScale C₀ N := by
      rw [lcL]
      exact max_le (max_le hl₁H hl₂H) (max_le hk₁H hk₂H)
    rwa [hheight] at hh
  have hQle : max C₀ 8 ≤ q := by
    have h1 : C₀ * max C₀ 8 ≤ C₀ * q := le_trans hB hLle
    exact Nat.le_of_mul_le_mul_left h1 (by omega)
  have hCq : C₀ ≤ q := le_trans (le_max_left _ _) hQle
  have hq8 : 8 ≤ q := le_trans (le_max_right _ _) hQle
  have hpow : 2 ^ q ≤ n + 2 := by
    rw [hq]
    exact Nat.pow_log_le_self 2 (by omega)
  have hmL : max k₁ k₂ ≤ lcL l₁ l₂ k₁ k₂ := by
    rw [lcL]; exact le_max_right _ _
  have key : ∀ k : ℕ, k ≤ C₀ * q →
      k + 2 * Work.KMTAreas.A7.uScale ρ (max k₁ k₂) ≤ n := by
    intro k hk
    have hy := uScaleHalfPow ρ hρ C₀ q (lcL l₁ l₂ k₁ k₂) (max k₁ k₂) hρC hmL hLle
    have h1 : (k : ℝ) + 2 * (Work.KMTAreas.A7.uScale ρ (max k₁ k₂) : ℝ) ≤
        (2 : ℝ) ^ q - 2 :=
      mainRegimeArith C₀ q k _ hC₀ hCq hq8 hk hy
    have h2 : (2 : ℝ) ^ q - 2 ≤ (n : ℝ) := by
      have h3 : (2 : ℝ) ^ q ≤ (n : ℝ) + 2 := by exact_mod_cast hpow
      linarith
    have h4 : ((k + 2 * Work.KMTAreas.A7.uScale ρ (max k₁ k₂) : ℕ) : ℝ) ≤ (n : ℝ) := by
      push_cast
      linarith
    exact_mod_cast h4
  have hk₁q : k₁ ≤ C₀ * q := le_trans hk₁H (le_of_eq hheight)
  have hk₂q : k₂ ≤ C₀ * q := le_trans hk₂H (le_of_eq hheight)
  have hlog : (Work.Analysis.EndVar.logN N).toNat = n := by
    simp only [Work.Analysis.EndVar.logN, hn, Int.toNat_natCast]
  rw [Work.KMTAreas.A7.mainRegime, hlog]
  exact ⟨key k₁ hk₁q, key k₂ hk₂q⟩

end Work.KMTPlan.A6
