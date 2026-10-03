import Mathlib
import Submission.Work.FIArea6Hecke.StripCoreDefs
import Submission.Work.FITop4.Bridge.area5_6_defs
import Submission.Work.FIFinal.CL.FIArea6Hecke.heckeStripZFR
import Submission.Work.FIFinal.CL.FIArea6Hecke.heckeStripLogDeriv

/-!
# `Work.FIArea6Hecke.heckeStripCore` — the strip inputs of *FI* (16.20)/(16.21)/(16.23)

`StripCore ε` (`StripCoreDefs.lean`) bundles the two deep analytic inputs of *FI* §16 in the
half-strip `s.re ≤ 2`:

* the zero-free region (16.20) together with Lemma 16.1 (Siegel) on the real axis, in the sharpened
  `ε`-form (16.24) `s.re ≥ 1 - c/(d^ε·log(|m|+|s.im|+3))`, and
* the logarithmic-derivative bound `‖L'/L‖ ≤ K(log(4d(|m|+|s.im|+3)) + d^ε)` in that region.

Here `Lval d m Lam = Lam s / heckeArch d m s` is the Hecke `L`-value read off an entire
completion `Lam` of `Λ(s,ψ_m) = (4d/π)^s Γ(s+|m|/2) L(s,ψ_m)`.

The statement is split into its two conjuncts and each is delegated:

* `Work.FIArea6Hecke.heckeStripZFR` — the non-vanishing (`Lval ≠ 0`) in the region;
* `Work.FIArea6Hecke.heckeStripLogDeriv` — the logarithmic-derivative bound in the region.

The two region constants `c₁, c₂` are independent (as in *FI* (16.23)/(16.24)), so in the
intersection of the two regions, i.e. with `c = min c₁ c₂`, both conclusions hold and
`Lval s ≠ 0 ∧ ‖Lval'(s)/Lval(s)‖ ≤ K(...)` follows.
-/

set_option autoImplicit false

namespace Work.FIArea6Hecke

open scoped BigOperators

noncomputable section

/-- **The strip inputs (16.20)/(16.21)/(16.23)**: from the zero-free region in the sharpened
`ε`-form and the logarithmic-derivative bound inside it, `StripCore ε` follows.  The region
constants of the two clauses are independent, so the smaller one is used throughout. -/
theorem heckeStripCore (ε : ℝ) (hε : 0 < ε) (hε4 : ε ≤ 1 / 4) :
    Work.FIArea6Hecke.StripCore ε := by
  obtain ⟨c₁, hc₁, hZFR⟩ := heckeStripZFR ε hε hε4
  obtain ⟨c₂, K, hc₂, hK, hLog⟩ := heckeStripLogDeriv ε hε hε4
  refine ⟨min c₁ c₂, K, lt_min hc₁ hc₂, hK, ?_⟩
  intro d chi m Lam hd hchi hAn hagr s hreg hs2
  have hDpos : 0 < (d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3) := by
    have hd1 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    have hdp : 0 < (d : ℝ) ^ ε := Real.rpow_pos_of_pos hd1 ε
    have hl : 0 < Real.log (|(m : ℝ)| + |s.im| + 3) :=
      Real.log_pos (by have h1 := abs_nonneg (m : ℝ); have h2 := abs_nonneg s.im; linarith)
    exact mul_pos hdp hl
  have hreg₁ : 1 - c₁ / ((d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3)) ≤ s.re := by
    have hle : min c₁ c₂ / ((d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3))
        ≤ c₁ / ((d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3)) :=
      div_le_div_of_nonneg_right (min_le_left _ _) hDpos.le
    linarith
  have hreg₂ : 1 - c₂ / ((d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3)) ≤ s.re := by
    have hle : min c₁ c₂ / ((d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3))
        ≤ c₂ / ((d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3)) :=
      div_le_div_of_nonneg_right (min_le_right _ _) hDpos.le
    linarith
  exact ⟨hZFR d chi m Lam hd hchi hAn hagr s hreg₁ hs2,
    hLog d chi m Lam hd hchi hAn hagr s hreg₂ hs2⟩

end

end Work.FIArea6Hecke
