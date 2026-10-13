/-
# `FamLopAux.Defs` — the trigonometric form of the Gegenbauer family

Auxiliary definitions for the proof of `Work.FTS.PhiStar.FamLopIterBound`.

`famC k = (3/2)_k / k!` is the coefficient sequence of the binomial series
`(1-z)^{-3/2} = Σ_k famC k · z^k` (extended by `0` to the negative integers, so that the
trigonometric sums below can be shifted without boundary corrections), and

`famTrig n ψ = Σ_{j ≤ n} famC j · famC (n - j) · cos ((2j - n) ψ)`

is the trigonometric form of the Gegenbauer polynomial `gC n`:

`gC n (cos ψ) = famTrig n ψ`      (the delegated lemma `TrigGegen`).
-/
import Mathlib.Analysis.Complex.Trigonometric
import Submission.Work.FTS.PhiStar.Gegenbauer.Defs
import Submission.Work.FTS.PhiStar.StarDefs
import Submission.Work.Spaces.DthIter_mul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar

set_option autoImplicit false

/-- `famC k = (∏_{i<k} (3/2 + i)) / k!` for `k ≥ 0`, and `0` for `k < 0`. -/
noncomputable def famC (k : ℤ) : ℝ :=
  if 0 ≤ k then (∏ i ∈ Finset.range k.toNat, ((3 : ℝ) / 2 + i)) / ((Nat.factorial k.toNat : ℕ) : ℝ) else 0

/-- The angular eigenfunction of index `m`: `θ ↦ eFam m θ`. -/
noncomputable abbrev famAng (m : ℕ) : ℝ → ℝ :=
  fun θ => Work.FTS.PhiStar.Gegenbauer.eFam m θ

/-- The `σ`-normalised inverse `Linv (λ_m e_m)`. -/
noncomputable abbrev famInv (m : ℕ) : ℝ → ℝ :=
  Work.FTS.PhiStar.Linv
    (fun θ' : ℝ => Work.FTS.PhiStar.Gegenbauer.lam m * Work.FTS.PhiStar.Gegenbauer.eFam m θ')

/-- The trigonometric form of the `n`-th Gegenbauer polynomial:
`famTrig n ψ = Σ_{j ≤ n} famC j · famC (n - j) · cos ((2j - n) ψ)`. -/
noncomputable def famTrig (n : ℕ) (ψ : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1),
    famC (j : ℤ) * famC ((n : ℤ) - (j : ℤ)) * Real.cos (((2 : ℝ) * (j : ℝ) - (n : ℝ)) * ψ)

end Work.FTS.PhiStar
