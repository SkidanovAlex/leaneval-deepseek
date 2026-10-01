import Mathlib

namespace Work.ZeroDensity.Ingham

open scoped BigOperators

noncomputable section

/-- `∫_A^∞ sin v · v^{-s-1} dv` (the tail sine integral of the sawtooth computation). -/
def afeT (s : ℂ) (A : ℝ) : ℂ :=
  ∫ v in Set.Ioi A, ((Real.sin v : ℝ) : ℂ) * (v : ℂ) ^ (-s - 1)

/-- `∫_0^A sin v · v^{-s-1} dv` (the truncated sine integral). -/
def afeL (s : ℂ) (A : ℝ) : ℂ :=
  ∫ v in Set.Ioc 0 A, ((Real.sin v : ℝ) : ℂ) * (v : ℂ) ^ (-s - 1)

/-- The resonance constant `c₀ = Γ(-s)·sin(-πs/2) = ∫_0^∞ sin v · v^{-s-1} dv`. -/
def afeC0 (s : ℂ) : ℂ := Complex.Gamma (-s) * Complex.sin (-(Real.pi : ℂ) * s / 2)

/-- Main truncation length `⌊√(t/2π)⌋ + 1` of the target. -/
def afeNt (t : ℝ) : ℕ := ⌊Real.sqrt (t / (2 * Real.pi))⌋₊ + 1

/-- Dual truncation length `⌊t/(2π·afeNt t)⌋`. -/
def afeMt (t : ℝ) : ℕ := ⌊t / (2 * Real.pi * (afeNt t))⌋₊

end

end Work.ZeroDensity.Ingham
