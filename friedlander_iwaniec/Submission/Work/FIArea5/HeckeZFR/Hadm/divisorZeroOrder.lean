import Mathlib

namespace Work.FIArea5.HeckeZFR.Hadm

/-- Auxiliary computation: for `a : ℕ∞`, applying `WithTop.map` with the coercion `ℕ → ℤ` and then
taking `untop₀` (which sends `⊤` to `0`) agrees with the natural-number cast of `a.toNat`
(which also sends `⊤` to `0`). -/
private lemma untop₀_map_natCast_toNat (a : ℕ∞) :
    (ENat.map Nat.cast a).untop₀ = (a.toNat : ℤ) := by
  cases a with
  | top => simp [ENat.map_top]
  | coe n => simp [ENat.map_natCast]

/-- If `Λ` is meromorphic on `U`, `0 ∈ U`, and `Λ` is analytic at the origin, then the divisor of
`Λ` on `U` at the origin equals the natural-number order of vanishing of `Λ` at `0`
(this is `0` when `Λ` vanishes identically near `0`, i.e. when the analytic order is `⊤`). -/
theorem divisorZeroOrder {Λ : ℂ → ℂ} {U : Set ℂ}
    (hΛ : MeromorphicOn Λ U) (h0 : (0 : ℂ) ∈ U) (han : AnalyticAt ℂ Λ 0) :
    (MeromorphicOn.divisor Λ U) 0 = (analyticOrderNatAt Λ 0 : ℤ) := by
  rw [hΛ.divisor_apply h0, han.meromorphicOrderAt_eq, analyticOrderNatAt]
  exact untop₀_map_natCast_toNat (analyticOrderAt Λ 0)

end Work.FIArea5.HeckeZFR.Hadm
