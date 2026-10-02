import Mathlib
import Submission.Work.FatouParabolic.Defs
import Submission.Work.FatouParabolic.Poly.tsq_iterate_isPolynomialMap
import Submission.Work.FatouParabolic.Critical.deriv_iterate_tsq_eq_zero_iff
import Submission.Work.Landing.Core
import Submission.Work.Landing.Family.deriv_tsq
import Submission.Work.FSeed.API.mem_Mandelbar

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedCertNum

open Filter Function
open scoped Topology
open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

noncomputable section

/-! ## Auxiliary facts

The two lemmas below are the elementary ingredients of the boundedness argument: a critical
point of the holomorphic fifth iterate `(Tsq c)^[5] = (T_c)^[10]` has a point of its `T_c`-orbit
equal to the critical point `0`, at a time before `10`. -/

/-- `(Tsq c)^[j]` is the `2j`-th iterate of the antiholomorphic quadratic `T_c`. -/
theorem tsq_iterate_eq_tantibar_iterate (c : ℂ) (j : ℕ) :
    (Work.Landing.Tsq c)^[j] = (Tantibar c)^[2 * j] :=
  funext (Work.LANDCL.Critical.Tsq_iterate_apply c j)

/-- **Critical points of `(Tsq c)^[5]` reach the critical point.**  If `deriv ((Tsq c)^[5]) w = 0`
then some point `(T_c)^[j] w`, `j < 10`, of the `T_c`-orbit of `w` is the critical point `0`.

Indeed the derivative of an iterate is the product of the derivatives along the orbit
(`Work.ELRig.deriv_iterate_eq_prod`) and `deriv (Tsq c) u = 4·u·conj(T_c u)`
(`Work.LANDCL.Critical.Tsq_deriv`), so a critical point of `(Tsq c)^[5]` is a point whose orbit
hits a critical point of `Tsq c`, i.e. `0` or a `T_c`-preimage of `0`; in both cases the
`T_c`-orbit hits `0` at a time `≤ 2·4 + 1 = 9 < 10`. -/
theorem exists_Tantibar_iterate_eq_zero_of_deriv_five {c w : ℂ}
    (h : deriv ((Work.Landing.Tsq c)^[5]) w = 0) :
    ∃ j : ℕ, j < 10 ∧ (Tantibar c)^[j] w = 0 := by
  obtain ⟨j, hj, hcase⟩ :=
    (Work.FatouParabolic.Critical.deriv_iterate_tsq_eq_zero_iff (c := c) (w := w) (m := 5)).mp h
  rw [Finset.mem_range] at hj
  rcases hcase with h0 | hpre
  · refine ⟨2 * j, by omega, ?_⟩
    rw [← tsq_iterate_eq_tantibar_iterate c j]
    exact h0
  · refine ⟨2 * j + 1, by omega, ?_⟩
    have h2 : (Tantibar c)^[2 * j + 1] w = Tantibar c ((Tantibar c)^[2 * j] w) :=
      Function.iterate_succ_apply' (f := Tantibar c) (2 * j) w
    rw [h2, ← tsq_iterate_eq_tantibar_iterate c j]
    exact hpre

/-- **A4 of the `SeedCertNum` contract** (`NOTES_LEAD_mandelbar_noncusp.md` §2.2): a parameter of
the tricorn family which has a *parabolic* point of period `5` (`(T_c)^[5] z = z`,
`multiplier2 c 5 z = 1`, i.e. `deriv ((Tsq c)^[5]) z = 1` with `(Tsq c)^[5] = (T_c)^[10]`) lies in
the mandelbar, **given** `Work.FatouParabolic.FatouParabolicInput` (Fatou's theorem: a parabolic
fixed point of a polynomial of degree `≥ 2` has a critical point in its basin).

Proof sketch (mirroring `Work.FSeed.API.mem_Mandelbar`, which does the same thing from the
hypothesis that the critical orbit converges to `z` under `(Tsq c)^[5]`):
let `F := (Tsq c)^[5] = (Tantibar c)^[10]`, a polynomial map of `z` of degree `1024`
(`Work.FatouParabolic.IsPolynomialMapOfDegreeAtLeastTwo`, with the explicit polynomial built from
`Tsq c z = (z^2 + star c)^2 + c`); then `F z = z` (from `hfix`) and `deriv F z = 1` (that is
`hmult` by definition), so `FatouParabolicInput F z` gives a critical point `w` of `F` with
`w ∈ basin F z`.
* `deriv F w = 0`, with the chain rule for `F = (Tsq c)^[5]` and
  `deriv (Tsq c) u = 4u·conj(T_c u)` (from `Work.Landing.Family.deriv_tsq` and the product formula
  `Submission.Work.ELRig.deriv_iterate_eq_prod`), shows that `(Tantibar c)^[j] w = 0` for some
  `j < 10`.
* `w ∈ basin F z` gives a bound `B` on `‖F^[q] w‖`; `T_c^[m] w = T_c^[r] (F^[q] w)` for
  `m = 10q + r`, `r < 10`, so the norm-growth estimate `‖T_c v‖ ≤ ‖v‖² + ‖c‖`
  (`Work.FSeed.API.growthBound`, `Work.FSeed.API.growthBound` bounds) bounds the whole
  `T_c`-orbit of `w` by the ten values `growthBound c B r`, `r < 10`.
* `(Tantibar c)^[j] w = 0` for some `j < 10` makes the `T_c`-orbit of `0` a *tail* of that of `w`,
  hence bounded, so `c ∈ Mandelbar`. -/
theorem mem_Mandelbar_of_parabolic {c z : ℂ}
    (hfat : Work.FatouParabolic.FatouParabolicInput)
    (hfix : (LeanEval.ComplexAnalysis.Tantibar c)^[5] z = z)
    (hmult : Work.Landing.multiplier2 c 5 z = 1) :
    c ∈ LeanEval.ComplexAnalysis.Mandelbar := by
  -- `F := (Tsq c)^[5] = T_c^[10]` is the holomorphic tenth iterate of `T_c`.
  have hten : ((Work.Landing.Tsq c)^[5] : ℂ → ℂ) = (Tantibar c)^[10] := by
    rw [Work.LANDCL.Critical.Tsq_eq_Tantibar_iterate_two, ← Function.iterate_mul]
  -- `z` is a parabolic fixed point of `F`.
  have hfixF : (Work.Landing.Tsq c)^[5] z = z := by
    rw [congrFun hten z]
    rw [show (10 : ℕ) = 5 + 5 from rfl,
      Function.iterate_add_apply (f := Tantibar c) 5 5 z, hfix, hfix]
  have hderivF : deriv ((Work.Landing.Tsq c)^[5]) z = 1 := hmult
  have hpoly : Work.FatouParabolic.IsPolynomialMapOfDegreeAtLeastTwo ((Work.Landing.Tsq c)^[5]) :=
    Work.FatouParabolic.Poly.tsq_iterate_isPolynomialMap c (m := 5) (by norm_num)
  -- Fatou's theorem: a critical point of `F` lies in the basin of the parabolic fixed point.
  obtain ⟨w, hcrit, hwbasin⟩ := hfat ((Work.Landing.Tsq c)^[5]) z hpoly hfixF hderivF
  -- A point of the `T_c`-orbit of `w` is the critical point `0`.
  obtain ⟨j, _hj, hj0⟩ := exists_Tantibar_iterate_eq_zero_of_deriv_five (c := c) (w := w) hcrit
  -- The `F`-orbit of `w` is bounded.
  have hconv : Tendsto (fun q : ℕ => ((Work.Landing.Tsq c)^[5])^[q] w) atTop (𝓝 z) := hwbasin
  obtain ⟨B, hB⟩ := isBounded_iff_forall_norm_le.mp
    (Metric.isBounded_range_of_tendsto _ hconv)
  have hBq : ∀ q : ℕ, ‖((Work.Landing.Tsq c)^[5])^[q] w‖ ≤ B := fun q => hB _ ⟨q, rfl⟩
  have hB0 : 0 ≤ B := le_trans (norm_nonneg w) (by simpa using hBq 0)
  -- The `F`-orbit of `w` is the `10`-step subsequence of its `T_c`-orbit.
  have hGq : ∀ q : ℕ, Work.ParamRays.orbit c w (10 * q) = ((Work.Landing.Tsq c)^[5])^[q] w := by
    intro q
    show (Tantibar c)^[10 * q] w = ((Work.Landing.Tsq c)^[5])^[q] w
    rw [hten, Function.iterate_mul]
  -- Every `T_c`-iterate of `w` is bounded by one of the ten growth bounds.
  have key : ∀ m : ℕ, ‖Work.ParamRays.orbit c w m‖ ≤ Work.FSeed.API.growthBound c B (m % 10) := by
    intro m
    have hsplit : Work.ParamRays.orbit c w m =
        Work.ParamRays.orbit c (((Work.Landing.Tsq c)^[5])^[m / 10] w) (m % 10) := by
      conv_lhs => rw [show m = 10 * (m / 10) + m % 10 from (Nat.div_add_mod m 10).symm]
      rw [Work.ParamRays.orbit_add, hGq (m / 10)]
    rw [hsplit]
    exact Work.FSeed.API.norm_orbit_le_growthBound (c := c) hB0 (m % 10) _
      (hBq (m / 10))
  -- The critical orbit of `T_c` is a tail of the orbit of `w`.
  refine ⟨∑ r ∈ Finset.range 10, Work.FSeed.API.growthBound c B r, fun n => ?_⟩
  have htail : (Tantibar c)^[n] 0 = Work.ParamRays.orbit c w (n + j) := by
    rw [Work.ParamRays.orbit, ← hj0]
    exact (Function.iterate_add_apply (f := Tantibar c) n j w).symm
  rw [htail]
  exact le_trans (key (n + j))
    (Finset.single_le_sum (fun r _ => Work.FSeed.API.growthBound_nonneg (c := c) hB0 r)
      (Finset.mem_range.mpr (Nat.mod_lt (n + j) (by norm_num))))

end

end Work.SeedCertNum
