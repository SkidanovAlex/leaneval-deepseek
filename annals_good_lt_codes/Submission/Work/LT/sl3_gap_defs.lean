import Mathlib
import Submission.Work.LT.Defs

/-! Local definitions for `Work.LT.sl3_gap` (Job: spectral gap of `Cay(SL₃(ℤ/p), {E_ij(±1)})`).

These are *my own* definitions (not shared `Defs.lean`); children working on the lemmas I
delegate may import this file and state their results in this vocabulary. -/

namespace Work.LT

/-- The Dirichlet form of `f : SL₃(ℤ/p) → ℝ` over the 12 elementary generators
`E_ij(±1)`: `D(f) = ∑_k ∑_g (f (S_k * g) - f g)^2`. -/
noncomputable def sl3DF (p : ℕ) [Fact p.Prime] (f : Matrix.SpecialLinearGroup (Fin 3) (ZMod p) → ℝ) : ℝ :=
  ∑ k : Fin 6 × Bool, ∑ g, (f (sl3Gen p k * g) - f g) ^ 2

/-- The Dirichlet form of `f` over the *column subgroup* `U = {E_ac(s) * E_bc(t)} ≅ (ℤ/p)²`
(`a`, `b`, `c` pairwise distinct), i.e. `∑_{s,t} ‖L_{u(s,t)} f - f‖²`. -/
noncomputable def sl3ColDF (p : ℕ) [Fact p.Prime] (a b c : Fin 3)
    (f : Matrix.SpecialLinearGroup (Fin 3) (ZMod p) → ℝ) : ℝ :=
  ∑ s : ZMod p, ∑ t : ZMod p, ∑ g, (f (sl3E p a c s * sl3E p b c t * g) - f g) ^ 2

/-- **Relative property (T) for the column subgroup**, finite form, with constant `K`
(uniform in the odd prime `p`): a function almost invariant under the 12 generators is almost
invariant under all of `U`, on average. -/
def sl3RelT (K : ℝ) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ a b c : Fin 3, a ≠ b → a ≠ c → b ≠ c →
    ∀ f : Matrix.SpecialLinearGroup (Fin 3) (ZMod p) → ℝ,
      sl3ColDF p a b c f ≤ K * (p : ℝ) ^ 2 * sl3DF p f

/-- **Bounded elementary generation** with length bound `L`: every element of `SL₃(ℤ/p)` is a
product of at most `L` elementary transvections `E_ij(t)` (`i ≠ j`, `t` arbitrary). -/
def sl3BoundedGen (L : ℕ) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod p)),
    ∃ l : List (Fin 3 × Fin 3 × ZMod p), l.length ≤ L ∧ (∀ x ∈ l, x.1 ≠ x.2.1) ∧
      g = (l.map (fun x => sl3E p x.1 x.2.1 x.2.2)).prod

end Work.LT
