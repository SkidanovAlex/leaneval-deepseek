import Mathlib
import Submission.Work.Bottcher.Defs
import Submission.Work.Bottcher.Green.green_eq_zero_iff_bounded
import Submission.Work.Bottcher.Green.green_nonneg
import Submission.Work.Bottcher.Green.green_comm

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The critical value `c` lies in its own critical domain iff `c ∉ M*`

The Böttcher coordinate of the tricorn family `T_c(z) = z̄² + c` is the true one on
the domain `CritDomain c = {z | G_c(0) < G_c(z)}`.  The critical value is `c = T_c 0`;
the Green function satisfies `G_c ∘ T_c = 2 G_c` (`Green.green_comm`), hence

`G_c(c) = G_c(T_c 0) = 2 G_c(0) = 2 * greenParam c`.

Therefore `c ∈ CritDomain c ↔ greenParam c < 2 * greenParam c ↔ 0 < greenParam c`,
and `0 < greenParam c ↔ c ∉ M*` because `greenParam c = G_c(0)` vanishes exactly when
the critical orbit is bounded, i.e. exactly on the mandelbar (`Green.green_eq_zero_iff_bounded`
and `Green.green_nonneg`).
-/

namespace Work.Bottcher.Critical

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- The parameter potential vanishes exactly on the mandelbar: the critical orbit is bounded
iff `greenParam c = G_c(0) = 0`. -/
theorem greenParam_eq_zero_iff (c : ℂ) : Work.Bottcher.greenParam c = 0 ↔ c ∈ Mandelbar := by
  rw [Work.Bottcher.greenParam_def]
  exact Work.Bottcher.Green.green_eq_zero_iff_bounded c 0

/-- The parameter potential is positive exactly outside the mandelbar. -/
theorem greenParam_pos_iff (c : ℂ) : 0 < Work.Bottcher.greenParam c ↔ c ∉ Mandelbar := by
  have hnn : 0 ≤ Work.Bottcher.greenParam c := by
    rw [Work.Bottcher.greenParam_def]
    exact Work.Bottcher.Green.green_nonneg c 0
  constructor
  · intro h hmem
    have : Work.Bottcher.greenParam c = 0 := (greenParam_eq_zero_iff c).mpr hmem
    linarith
  · intro h
    rcases lt_or_eq_of_le hnn with h' | h'
    · exact h'
    · exact absurd ((greenParam_eq_zero_iff c).mp h'.symm) h

/-- The Green function of the critical value `c = T_c 0` is twice the parameter potential. -/
theorem green_self_eq (c : ℂ) :
    Work.Bottcher.green c c = 2 * Work.Bottcher.greenParam c := by
  have h := Work.Bottcher.Green.green_comm c 0
  rw [Work.Bottcher.Tantibar_zero] at h
  rwa [Work.Bottcher.greenParam_def]

/-- **The critical value lies in its own critical domain exactly when the parameter escapes.** -/
theorem mem_CritDomain_self_iff (c : ℂ) :
    c ∈ Work.Bottcher.CritDomain c ↔ c ∉ LeanEval.ComplexAnalysis.Mandelbar := by
  rw [Work.Bottcher.mem_CritDomain, green_self_eq]
  have hlt : Work.Bottcher.greenParam c < 2 * Work.Bottcher.greenParam c ↔
      0 < Work.Bottcher.greenParam c := by
    constructor <;> intro h <;> linarith
  rw [hlt]
  exact greenParam_pos_iff c

end Work.Bottcher.Critical
