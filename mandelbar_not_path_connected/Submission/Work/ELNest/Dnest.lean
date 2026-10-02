/-
# EL nest, part 10 (N4): the assembled statement of the nest at `b₂`

The contract's item N4
(`NOTES_LEAD_mandelbar_EL_F_contracts.md` §6) asks for a single statement about the nest
`Δ̂ₙ = S.D n` at the branch point `b₂`.  Every clause is proved in this area:

* `Work.ELNest.Dnest_iInter` (`Dnest_limit.lean`): `⋂ n, closure Δ̂ₙ = {b₂}`;
* `Work.ELNest.Dnest_diam` (`Dnest_limit.lean`): `diam Δ̂ₙ → 0`;
* `NestData.b2_lands` (the data of the interface, certificate C2 of ELPull): the three tripod
  angles `22/63`, `25/63`, `37/63` land at `b₂`;
* `NestData.b2_not_int`: `b₂` is not an interior point of the filled Julia set `K c`;
* `NestData.b2_fix`: `b₂` is fixed by the holomorphic second return map
  `Tsq c = (z ↦ (z² + c̄)² + c) = (T_c)^2`; this is the precise form of the contract's
  `(Tantibar c)^[2] b₂ = b₂` — the two are *not* the same map (the holomorphic second iterate
  `Tsq c` of the tricorn map is `Tantibar_{c̄} ∘ Tantibar_c`, so its formula is `(z²+c̄)² + c` and
  not `(z²+c̄)² + c̄`), and `Tsq c` is what the consuming structure `Work.EL.B2Data` of ELRig
  (and `Work.ELNest.NestData`) records.  `Work.ELNest.b2_fix_of_lands` derives it from the three
  tripod rays and the `T²`-cycle `22/63 ↦ 25/63 ↦ 37/63` of the angle doubling;
* `NestData.b2_mem_D`: `b₂ ∈ Δ̂ₙ` for every `n`.

The shrinking form `∀ ε > 0, ∃ N, ∀ n ≥ N, Δ̂ₙ ⊆ ball b₂ ε` is
`Work.ELNest.Dnest_shrinks` (the field `B2Data.Δ_shrinks` of ELRig), whose corollaries are the
first two clauses below.
-/
import Mathlib
import Submission.Work.ELNest.Dnest_limit
import Submission.Work.ELNest.b2_fix_of_lands

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter Set Topology Function
open scoped Topology ComplexConjugate

set_option linter.unusedVariables false

noncomputable section

namespace Work.ELNest

open Work.EL

variable {c : ℂ}

/-- **N4, assembled.**  The nest at the branch point `b₂`: single-point intersection of the
closures of its levels, diameters tending to `0`, the three tripod rays landing at `b₂`, `b₂`
outside the interior of `K c`, `b₂` fixed by the second return map and `b₂` in every level. -/
theorem Dnest (S : NestData c) :
    (⋂ n : ℕ, closure (S.D n)) = {S.b2} ∧
    Tendsto (fun n : ℕ => Metric.diam (S.D n)) atTop (𝓝 0) ∧
    (∀ θ ∈ ({22 / 63, 25 / 63, 37 / 63} : Set ℝ), LandsN S.d.hN θ S.b2) ∧
    S.b2 ∉ interior (K c) ∧
    Work.Landing.Tsq c S.b2 = S.b2 ∧
    (∀ n : ℕ, S.b2 ∈ S.D n) :=
  ⟨Dnest_iInter S, Dnest_diam S,
   fun θ hθ => by
     simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hθ
     rcases hθ with h | h | h
     · rw [h]; exact S.b2_lands.1
     · rw [h]; exact S.b2_lands.2.1
     · rw [h]; exact S.b2_lands.2.2,
   S.b2_not_int, S.b2_fix, S.b2_mem_D⟩

end Work.ELNest
