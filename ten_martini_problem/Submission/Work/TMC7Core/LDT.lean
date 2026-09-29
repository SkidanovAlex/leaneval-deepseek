import Submission.Work.TMC7Core.Cocycle

/-!
# TMC7Core: the large deviation interface

`HasLDTAt lam E c C` is the conclusion of the Bourgain--Goldstein / Bourgain--Jitomirskaya
large deviation theorem for the almost Mathieu cocycle at coupling `lam` and energy `E`, with
constants `c, C`.  `HasLDTOn lam K c C` is the same estimate *uniformly* over energies in `K`
(the constants in the paper depend only on the coupling and on a bounded energy range), and
`large_deviation` (in `Fourier/large_deviation.lean`) proves that for every `(lam, E₀)` there
are `c, C, r > 0` with `HasLDTOn lam (Icc (E₀ - r) (E₀ + r)) c C`.
-/

open MeasureTheory Filter Topology Set
open LeanEval.Analysis.TenMartini

noncomputable section

namespace Work.TMC7Core

/-- The large deviation estimate at a single energy: for `|α − a/q| < 1/q²`, `(a,q) = 1`,
`κ ∈ (0,1]`, `q ≥ C κ^{-2}` and `N ≥ C κ^{-2} q`, the set of phases where the finite-scale
exponent `u_N` deviates from its mean `L_N` by more than `κ` has measure at most `e^{-cκq}`. -/
def HasLDTAt (lam E c C : ℝ) : Prop :=
  0 < c ∧ 1 ≤ C ∧
    ∀ (α : ℝ) (a : ℤ) (q N : ℕ) (κ : ℝ), 1 ≤ q → 0 < κ → κ ≤ 1 →
      Nat.Coprime (Int.natAbs a) q → |α - (a : ℝ) / (q : ℝ)| < 1 / ((q : ℝ) ^ 2) →
      C * (κ ^ 2)⁻¹ ≤ (q : ℝ) → C * (κ ^ 2)⁻¹ * (q : ℝ) ≤ (N : ℝ) →
      MeasureTheory.volume {x : ℝ | x ∈ Set.Icc (0 : ℝ) 1 ∧
        κ < |uAvg α lam (E : ℂ) N x - lyapAvg α lam (E : ℂ) N|} ≤
        ENNReal.ofReal (Real.exp (-(c * κ * (q : ℝ))))

/-- The large deviation estimate uniformly over the energies in `K`. -/
def HasLDTOn (lam : ℝ) (K : Set ℝ) (c C : ℝ) : Prop :=
  0 < c ∧ 1 ≤ C ∧
    ∀ E ∈ K, ∀ (α : ℝ) (a : ℤ) (q N : ℕ) (κ : ℝ), 1 ≤ q → 0 < κ → κ ≤ 1 →
      Nat.Coprime (Int.natAbs a) q → |α - (a : ℝ) / (q : ℝ)| < 1 / ((q : ℝ) ^ 2) →
      C * (κ ^ 2)⁻¹ ≤ (q : ℝ) → C * (κ ^ 2)⁻¹ * (q : ℝ) ≤ (N : ℝ) →
      MeasureTheory.volume {x : ℝ | x ∈ Set.Icc (0 : ℝ) 1 ∧
        κ < |uAvg α lam (E : ℂ) N x - lyapAvg α lam (E : ℂ) N|} ≤
        ENNReal.ofReal (Real.exp (-(c * κ * (q : ℝ))))

/-- The paper's standing boundedness of the finite-scale exponent (B1):
`u_N(x) = (1/N) ln ‖A_N(x)‖ ≤ C₀` for every `E` in the energy set `K`, every `α`, `N`, `x`.
This is *not* part of the LDT statement but is needed when the exceptional set of the LDT is
integrated against the (a priori unbounded) function `u_N` — see `DESIGN.md`. -/
def HasLEBound (lam : ℝ) (K : Set ℝ) (C₀ : ℝ) : Prop :=
  0 < C₀ ∧ ∀ E ∈ K, ∀ (α : ℝ) (N : ℕ) (x : ℝ), uAvg α lam (E : ℂ) N x ≤ C₀

theorem HasLDTOn.mono_const {lam c C : ℝ} {K : Set ℝ} (h : HasLDTOn lam K c C) {c' : ℝ}
    (hc : 0 < c') (hcc : c' ≤ c) : HasLDTOn lam K c' C :=
  ⟨hc, h.2.1, fun E hE α a q N κ hq hκ hκ1 hcop hα hqC hN => by
    refine le_trans (h.2.2 E hE α a q N κ hq hκ hκ1 hcop hα hqC hN) ?_
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have hq0 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
    nlinarith [mul_nonneg hκ.le hq0]⟩

theorem HasLEBound.mono {lam C₀ : ℝ} {K K' : Set ℝ} (h : HasLEBound lam K C₀) (hK : K' ⊆ K) :
    HasLEBound lam K' C₀ :=
  ⟨h.1, fun E hE => h.2 E (hK hE)⟩

end Work.TMC7Core
