/-
# The parameters of the colour-degree nibble iteration

This module fixes the numerical data consumed by the iteration of the one-round step of
`Submission/Work/Deep/Kahn/NibbleRoundDefs.lean` (the reduction
`Work.Deep.Kahn.kahnCore_of_roundStepB : RoundStepStatement → KahnCoreStatement`).

A state of the iteration is `(𝓗, L, Λ, D)` — a linear hypergraph of rank `≤ C`, a list
assignment of common size `Λ`, colour degrees at most `D`.  Writing `ρ := Λ/D`:

* one round multiplies `ρ` by at least `1 + γ` with `γ = ε/(4K)` (`retention_gain`,
  `retention_recurrence`), while
* `D` drops by a factor `(1/K)(1 + (C-1)/ρ)`, which is *not* uniform in the round because
  `ρ` grows.

The iteration therefore tracks the potential `Ψ = log Λ - b (D/Λ)` with `b = 32 C/ε + 1`:
the `1/ρ`-losses of `D` telescope against the geometric growth of `ρ`, so `Ψ` decreases by at
most `8 η` per round.  Hence after `T` rounds `Λ` has dropped by at most the *constant*
factor `exp (-(8 η T + b))`, and (because `ρ ≤ 10 C` throughout) so has `D`.

`mkIt C ε D` is the concrete choice of the parameters for a hypergraph whose degree bound is
`D`: it is designed so that `mkIt C ε D` satisfies `It.Cond` as soon as `D` is large enough
(`D ≥ exp (10^10 (1 + C + 1/ε + C/ε))` is more than sufficient).
-/
import Submission.Work.ConeSwitch.MathlibNoHG

set_option autoImplicit false

namespace Work.Deep.Kahn

noncomputable section

/-- The numerical data of the iteration. -/
structure It where
  /-- rank bound -/
  C : ℕ
  /-- slack parameter of the round -/
  ε : ℝ
  /-- the parameter `K` (activation probability `1/K`) -/
  K : ℕ
  /-- the error parameter of the round -/
  η : ℝ
  /-- the certified one-round ratio gain, `γ = ε/(4K)` -/
  γ : ℝ
  /-- the coefficient of the potential `log Λ - b (D/Λ)` -/
  b : ℝ
  /-- the number of rounds -/
  T : ℕ
  /-- the initial colour-degree bound -/
  Di0 : ℕ
  /-- the initial common list size -/
  Λ0 : ℕ

namespace It

/-- The per-round growth factor of the ratio, `γ/2`. -/
def γ₁ (it : It) : ℝ := it.γ / 2

/-- The initial ratio `Λ₀/D₀`. -/
def ρ0 (it : It) : ℝ := (it.Λ0 : ℝ) / (it.Di0 : ℝ)

/-- The guaranteed lower bound for the colour-degree bound after any number of rounds.

It is derived from the potential `Ψ = log Λ - b (D/Λ)`: `Λ` drops by at most the factor
`exp (-(8 η T + b))` and `D ≥ Λ/(10 C)` throughout, so `D` drops at most by
`exp (-(34 C/ε + 4))`, uniformly over the number of rounds. -/
def Dlow (it : It) : ℝ :=
  (it.Di0 : ℝ) * Real.exp (-(34 * (it.C : ℝ) / it.ε + 4)) / (20 * (it.C : ℝ))

end It

/-- The numerical conditions under which the iteration runs. -/
abbrev It.Cond (it : It) (Dm : ℝ) : Prop :=
  2 ≤ it.C ∧ 0 < it.ε ∧ it.ε ≤ 1 ∧ 2 ≤ it.K ∧ 0 < it.η ∧ 0 < it.γ ∧
  1 ≤ it.Di0 ∧ 1 ≤ it.Λ0 ∧
  (16 : ℝ) * it.C ≤ (1 + it.ε) * (it.K : ℝ) ∧
  2 * (2 * (it.C : ℝ) - 1) ≤ it.ε * (it.K : ℝ) ∧
  16 * it.η * (it.K : ℝ) ≤ 1 ∧ 32 * it.η ≤ it.γ ∧
  32 * (it.C : ℝ) / it.ε + 1 ≤ it.b ∧
  8 * (it.C : ℝ) / (1 + it.ε) ≤ (1 + it.γ₁) ^ it.T ∧
  (1 + it.ε) * (it.Di0 : ℝ) ≤ (it.Λ0 : ℝ) ∧
  (it.Λ0 : ℝ) ≤ 10 * (it.C : ℝ) * (it.Di0 : ℝ) ∧
  Real.log (it.Di0 : ℝ) ≤ (it.K : ℝ) ∧
  8 * it.η * (it.T : ℝ) + it.b ≤ 34 * (it.C : ℝ) / it.ε + 4 ∧
  Dm ≤ it.Dlow ∧ ((it.C : ℝ) + (it.K : ℝ) + it.η⁻¹) ^ (9 : ℕ) ≤ it.Dlow ∧
  Real.exp (2 * Real.sqrt (it.K : ℝ)) ≤ it.Dlow ∧ 16 * (it.K : ℝ) ≤ it.Dlow ∧
  it.η⁻¹ ≤ it.Dlow

/-- The number `K` of activation classes. -/
def mkK (C : ℕ) (ε Dk : ℝ) : ℕ :=
  ⌈Real.log Dk⌉₊ + ⌈10 ^ 6 * ((C : ℝ) + 1) / ε⌉₊ + 10 ^ 6

/-- The concrete parameter choice for a hypergraph of degree bound `Dk`. -/
def mkIt (C : ℕ) (ε Dk : ℝ) : It where
  C := C
  ε := ε
  K := mkK C ε Dk
  η := ε / (10 ^ 6 * (mkK C ε Dk : ℝ))
  γ := ε / (4 * (mkK C ε Dk : ℝ))
  b := 32 * (C : ℝ) / ε + 1
  T := ⌈64 * (C : ℝ) * (mkK C ε Dk : ℝ) / (ε * (1 + ε))⌉₊ + 1
  Di0 := ⌊Dk⌋₊
  Λ0 := ⌈(1 + ε) * (⌊Dk⌋₊ : ℝ)⌉₊

/-! ### The fields of `mkIt`, and of the derived quantities -/

@[simp] theorem mkIt_C (C : ℕ) (ε Dk : ℝ) : (mkIt C ε Dk).C = C := rfl
@[simp] theorem mkIt_ε (C : ℕ) (ε Dk : ℝ) : (mkIt C ε Dk).ε = ε := rfl
@[simp] theorem mkIt_K (C : ℕ) (ε Dk : ℝ) : (mkIt C ε Dk).K = mkK C ε Dk := rfl
@[simp] theorem mkIt_η (C : ℕ) (ε Dk : ℝ) :
    (mkIt C ε Dk).η = ε / (10 ^ 6 * (mkK C ε Dk : ℝ)) := rfl
@[simp] theorem mkIt_γ (C : ℕ) (ε Dk : ℝ) :
    (mkIt C ε Dk).γ = ε / (4 * (mkK C ε Dk : ℝ)) := rfl
@[simp] theorem mkIt_b (C : ℕ) (ε Dk : ℝ) : (mkIt C ε Dk).b = 32 * (C : ℝ) / ε + 1 := rfl
@[simp] theorem mkIt_T (C : ℕ) (ε Dk : ℝ) :
    (mkIt C ε Dk).T = ⌈64 * (C : ℝ) * (mkK C ε Dk : ℝ) / (ε * (1 + ε))⌉₊ + 1 := rfl
@[simp] theorem mkIt_Di0 (C : ℕ) (ε Dk : ℝ) : (mkIt C ε Dk).Di0 = ⌊Dk⌋₊ := rfl
@[simp] theorem mkIt_Λ0 (C : ℕ) (ε Dk : ℝ) :
    (mkIt C ε Dk).Λ0 = ⌈(1 + ε) * (⌊Dk⌋₊ : ℝ)⌉₊ := rfl
@[simp] theorem It.γ₁_eq (it : It) : it.γ₁ = it.γ / 2 := rfl
@[simp] theorem It.ρ0_eq (it : It) : it.ρ0 = (it.Λ0 : ℝ) / (it.Di0 : ℝ) := rfl
@[simp] theorem It.Dlow_eq (it : It) :
    it.Dlow = (it.Di0 : ℝ) * Real.exp (-(34 * (it.C : ℝ) / it.ε + 4)) / (20 * (it.C : ℝ)) :=
  rfl

end

end Work.Deep.Kahn
