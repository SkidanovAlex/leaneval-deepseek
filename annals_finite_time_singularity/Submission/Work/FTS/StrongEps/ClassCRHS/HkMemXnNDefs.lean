/-
# `HkMemXnNDefs` — the twenty §8 pieces of `N`, as finitely indexed families

`PB α w Φs Φg k` is the `k`-th piece of the split of `N α (F_*+w) (Φs+Φg)` (the paper's
`N_i^{ab}`), in the order `N1gg, N1gs, N1sg, N1ss, N2gg, …, N5ss`, and `NBlk α w Φs Φg k` is the
corresponding *product form* — the function actually bounded in the proof of `HkMemXnN`
(each is a scalar times a product of a `ℋ⁴`-honest coefficient with an `ℋ⁴`-honest factor,
the star coefficients being paired with the scaled factor `(z/(1+z))·F`).
-/
import Mathlib.Analysis.Complex.Trigonometric
import Submission.Work.Construction.Defs
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.Nonlinear.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology

namespace Work.FTS.StrongEps.ClassCRHS

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- The `k`-th §8 piece of `N α (F_*+w) (Φs+Φg)` (order `N1gg, N1gs, …, N5ss`). -/
def PB (α : ℝ) (w Φs Φg : Fn) : ℕ → Fn
  | 0 => Work.FTS.Nonlin.N1gg α w Φg
  | 1 => Work.FTS.Nonlin.N1gs α w Φg
  | 2 => Work.FTS.Nonlin.N1sg α Φs w
  | 3 => Work.FTS.Nonlin.N1ss α Φs
  | 4 => Work.FTS.Nonlin.N2gg α w Φg
  | 5 => Work.FTS.Nonlin.N2gs α w Φg
  | 6 => Work.FTS.Nonlin.N2sg α Φs w
  | 7 => Work.FTS.Nonlin.N2ss α Φs
  | 8 => Work.FTS.Nonlin.N3gg α w Φg
  | 9 => Work.FTS.Nonlin.N3gs α w Φg
  | 10 => Work.FTS.Nonlin.N3sg α Φs w
  | 11 => Work.FTS.Nonlin.N3ss α Φs
  | 12 => Work.FTS.Nonlin.N4gg α w
  | 13 => Work.FTS.Nonlin.N4gs α w
  | 14 => Work.FTS.Nonlin.N4sg α w
  | 15 => Work.FTS.Nonlin.N4ss α
  | 16 => Work.FTS.Nonlin.N5gg w
  | 17 => Work.FTS.Nonlin.N5gs α w
  | 18 => Work.FTS.Nonlin.N5sg α w
  | _ => Work.FTS.Nonlin.N5ss α

/-- The `k`-th *product form* of the §8 pieces: a scalar times a product of a coefficient with a
factor.  `(z+1)/z`-weighted star coefficients are paired with the `z/(1+z)`-scaled factor, so
that the two factors of each product are separately `ℋ⁴`-honest (or one is `𝒲^{4,∞}`). -/
def NBlk (α : ℝ) (w Φs Φg : Fn) : ℕ → Fn
  | 0 => fun z θ => 2 * (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α w Φg) z θ * w z θ)
  | 1 => fun z θ => 2 * (Work.Construction.Fstar α z θ
      * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α w Φg) z θ)
  | 2 => fun z θ => 2 * ((z + 1) / z * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ
      * (z / (1 + z) * w z θ))
  | 3 => fun z θ => 2 * ((z + 1) / z * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ
      * (z / (1 + z) * Work.Construction.Fstar α z θ))
  | 4 => fun z θ => (-2) * (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α w Φg) z θ
      / Work.Construction.s2 θ * Work.Spaces.Dth w z θ)
  | 5 => fun z θ => (-2) * (Work.Spaces.Dth (Work.Construction.Fstar α) z θ
      * (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α w Φg) z θ / Work.Construction.s2 θ))
  | 6 => fun z θ => (-2) * ((z + 1) / z * (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ
      / Work.Construction.s2 θ) * (z / (1 + z) * Work.Spaces.Dth w z θ))
  | 7 => fun z θ => (-2) * ((z + 1) / z * (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ
      / Work.Construction.s2 θ) * (z / (1 + z) * Work.Spaces.Dth (Work.Construction.Fstar α) z θ))
  | 8 => fun z θ => (-(2 * α)) * (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α w Φg) z θ
      * Work.Spaces.Dz w z θ)
  | 9 => fun z θ => (-(2 * α)) * (Work.Spaces.Dz (Work.Construction.Fstar α) z θ
      * Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α w Φg) z θ)
  | 10 => fun z θ => (-(2 * α)) * ((z + 1) / z * Work.Construction.Vop
      (Work.FTS.Nonlin.PhiTs α Φs) z θ * (z / (1 + z) * Work.Spaces.Dz w z θ))
  | 11 => fun z θ => (-(2 * α)) * ((z + 1) / z * Work.Construction.Vop
      (Work.FTS.Nonlin.PhiTs α Φs) z θ
      * (z / (1 + z) * Work.Spaces.Dz (Work.Construction.Fstar α) z θ))
  | 12 => fun z θ => (-(1 / 2)) * (Work.Construction.FK w z * Work.Spaces.Dth w z θ)
  | 13 => fun z θ => (-(1 / 2)) * (Work.Spaces.Dth (Work.Construction.Fstar α) z θ
      * Work.Construction.FK w z)
  | 14 => fun z θ => (1 / 2) * (((-(2 * α)) * Work.Spaces.hKer z)
      * Work.Spaces.Dth w z θ)
  | 15 => fun z θ => (-(1 / 2)) * (Work.Construction.FK (Work.Construction.Fstar α) z
      * Work.Spaces.Dth (Work.Construction.Fstar α) z θ)
  | 16 => fun z θ => -(Real.sin θ) ^ 2 * (Work.Construction.FK w z * w z θ)
  | 17 => fun z θ => -(Real.sin θ) ^ 2 * (Work.Construction.Fstar α z θ * Work.Construction.FK w z)
  | 18 => fun z θ => -(Real.sin θ) ^ 2 * (Work.Construction.FK (Work.Construction.Fstar α) z
      * w z θ)
  | _ => fun z θ => -(Real.sin θ) ^ 2 * (Work.Construction.FK (Work.Construction.Fstar α) z
      * Work.Construction.Fstar α z θ)

/-- `PB` enumerates the pieces in the order of the split of `N`. -/
theorem PB_sum_eq (α : ℝ) (w Φs Φg : Fn) (z θ : ℝ) :
    (∑ k ∈ Finset.range 20, PB α w Φs Φg k z θ)
      = (Work.FTS.Nonlin.N1gg α w Φg z θ + Work.FTS.Nonlin.N1gs α w Φg z θ
          + Work.FTS.Nonlin.N1sg α Φs w z θ + Work.FTS.Nonlin.N1ss α Φs z θ)
        + (Work.FTS.Nonlin.N2gg α w Φg z θ + Work.FTS.Nonlin.N2gs α w Φg z θ
          + Work.FTS.Nonlin.N2sg α Φs w z θ + Work.FTS.Nonlin.N2ss α Φs z θ)
        + (Work.FTS.Nonlin.N3gg α w Φg z θ + Work.FTS.Nonlin.N3gs α w Φg z θ
          + Work.FTS.Nonlin.N3sg α Φs w z θ + Work.FTS.Nonlin.N3ss α Φs z θ)
        + (Work.FTS.Nonlin.N4gg α w z θ + Work.FTS.Nonlin.N4gs α w z θ
          + Work.FTS.Nonlin.N4sg α w z θ + Work.FTS.Nonlin.N4ss α z θ)
        + (Work.FTS.Nonlin.N5gg w z θ + Work.FTS.Nonlin.N5gs α w z θ
          + Work.FTS.Nonlin.N5sg α w z θ + Work.FTS.Nonlin.N5ss α z θ) := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, PB]
  ring

end Work.FTS.StrongEps.ClassCRHS
