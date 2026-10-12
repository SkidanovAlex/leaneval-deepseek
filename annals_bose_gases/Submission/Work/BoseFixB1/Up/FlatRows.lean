import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1.Up.FlatFree
import Submission.Work.BoseFixB1.Up.FrowSharp
import Submission.Work.BoseFixB1.Up.KinSupply
import Submission.Work.BoseFixB1S.w1MassB_le_flatPairMassB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.Up.FlatRows` — the flat branch as **rows**, with the kinetic allowance

## ⛔ WARNING — read `Submission/Work/BoseFixB1/FINDING_K2lever_and_flatRows.md` first

⚠ **SUPERSEDED IN PART (2026-10-11) — read
`Submission/Work/BoseFixB1/ADJUDICATION_frozen_vs_cube.md` before acting on this warning.**
The correlation-hole / Jastrow refutations cited below compute with `a v = R/2`, which is **not**
the corpus/FS convention; under the correct `a v = R(1 − √2 tanh(κR/√2)/(κR))` the dip family's
supply fraction exceeds `1` for every `κR > 0`, so those refutations are **void**, and the corner
objection is void too (`chiSmallB ≲ d^N` on the corner).  What survives from this warning is only
the **count-cap** obstruction, which kills the *route* `FlatWordKin` (and every *split* spelling),
**not** the joint residual `FlatRowsDeltaKin` / `Up.FlatFreeResidual`, which is **open, not false**.

The residual of `Work.BoseFixB1.perBoxFWeight_holds` (`Up.flatFreeResidual`) is **FALSE as stated**:
the *unconditional* per-box statement is refuted by the correlation-hole / Jastrow family
(`BoseFixB1B/FINDING_perBoxF_refuted_lowB_survives.md`, `BoseFixB1B/FINDING_flatBranch_refuted_ledger.md`,
and the machine-checked table of `BoseFixB1B/FINDING_lowCountWindowWeak_session2.md`); the correct
statement carries FS's low-energy hypothesis `IsLowB` (`PerBoxSmooth`, `flatBranchLowB`,
`PerBoxFLow`).  Consequently `FlatRowsSplit` below — and in particular its **fibre deviation row** —
is *not* expected to be provable: in the band `n₊(B)` is bounded only **above** by `γ n ‖Φ‖²`, while
the fibre deviation is `≍ √(S·n₊)`, which the scalar allowance `K₁·μ(a v)·n₊(B)` cannot pay (see
`FINDING_flatFib_row.md` §1 and the counterexample family of `FINDING_flatBranchAlt.md`).

What is *proved* in this module and remains useful is: `flatVar_nonneg`, `nPlusB_nonneg`,
`band_normB_pos`, `flatTau_nonneg`, `flatSlackB_nonneg`, the named error bracket `flatErrB` and
slack `flatSlackB`, and the implications `flatRows_of_split` / `flatFreeResidual_of_flatRows` /
`flatFreeResidual_of_split` (whose *hypotheses* are the questionable part).

## (superseded) the row decomposition

The residual of `Work.BoseFixB1.perBoxFWeight_holds` is `Up.FlatFreeResidual` — the *flat
(condensed)* branch of FS `thm:smallbox` at the sliding box, in its weakest known form
(`∃ γ > 0, PerBoxFlatFree v h R γ`).

This module states a **sufficient condition** `FlatRows v h R` for it and *proves* the implication
`FlatRows ⟹ FlatFreeResidual`.  `FlatRows` splits the analytic content into exactly the rows FS's
flat ledger is built from:

* `(fib)`  the **fibre row** `μ·flatFibSum ≤ μ W₁ τ N + Efib`;
* `(PQ₂)`  the **quadratic mean-field pair row** `½ W₂ (τ²N + V) ≤ flatPairSum + Epair`;
* `(bud)`  the **budget** `Efib + Epair ≤ C·(PerBoxF error bracket) + W₁·(arithmetic slack)
  + K₂·μ·(a v)·n₊(B)`;

at the *free-threshold* band `n₊(B) < γ n N` on the good set, thick boxes, for some
`ε₀ K₂ γ C`.  Everything else is proved and is supplied by the implication:

* the sharp `F`-row `(Fsharp)` — `Up.flatFterm_sharp_row` (cycle-free copy of
  `Work.BoseFixB1B.flatFterm_sharp_row`), with `V := Up.flatVar`;
* `0 ≤ V` — `flatVar_nonneg` below;
* the split `sbPot = −μ·fibSum + pairSum` — `Up.sbPot_split`;
* the kinetic supply `K₂·μ·(a v)·n₊(B) ≤ sbKin` — `Up.sbKin_ge_K2_mu_av_nPlus`;
* the arithmetic — the ledger `Up.perBoxF_of_ledger_kin`, which is
  `Work.BoseFixB1S.perBoxF_of_ledger_sharp` **with the kinetic allowance in the budget**
  (the skeleton takes `hkin : 0 ≤ sbKin` and so discards the whole `ε_T`-gap payment).

`K₂ = 0` in `(bud)` gives back the skeleton's budget verbatim, so `FlatRows` is a *weakening* of
the four-row hypotheses of `perBoxF_of_ledger_sharp` in the only direction that matters — the
budget row — while `(fib)` and `(PQ₂)` are stated at the free-threshold band.

The band restriction is what makes the rows true: on the exactly flat states (`n₊(B) = 0`) both
`(fib)` and `(PQ₂)` are *identities* (`Up.FlatFibreFlat`,
`Work.BoseFixB1B.flatPairMeanFieldCorrectedB1BF`), and off them the deviations from the mean-field
values are bounded by a constant times the excited count `n₊(B)` — which is exactly what the
`K₂·μ·(a v)·n₊(B)` allowance is for.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseFixB1.Up

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding Work.BoseFixB1

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. `flatVar ≥ 0` -/

/-- **The variance is nonnegative.**  `flatVar v μ Φ u = ∫_{abox} Φ² (t − τ)²` where
`t = nCountB/chiMass` is the smooth local density and `τ = flatTau` its `Φ²`-weighted mean,
so it is `≥ 0` by inspection.  The hypothesis `0 < normB v μ n Φ` (which holds in the flat band,
where `n₊(B) < γ n N` forces `N > 0`) removes the degenerate `Φ ≡ 0` case, in which `flatTau` is
the junk value `0/0 = 0` and `flatVar = flatT2 ≥ 0` anyway. -/
theorem flatVar_nonneg {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ} {n : ℕ}
    {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ)
    (hN : 0 < Work.BoseBoxFix.normB v μ n Φ) (u : EuclideanSpace ℝ (Fin 3)) :
    0 ≤ flatVar v μ Φ u := by
  -- the integrands
  have hnc_cont : Continuous (fun x : Submission.BoseGases.X n =>
      Work.BoseFixB1.nCountB (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
        (Work.BoseFixB1.pD v μ) u x) := by
    have hchi : Continuous (fun z : E3 => Submission.BoseGases.chiSmallB
        (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u z) := by
      rw [show (fun z : E3 => Submission.BoseGases.chiSmallB
            (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u z)
          = fun z => Submission.BoseGases.chiScale (Work.BoseFixB1.pL v μ) z
              * Submission.BoseGases.chiSmall (Work.BoseFixB1.pM v μ)
                  ((Work.BoseFixB1.pL v μ * Work.BoseFixB1.pD v μ)⁻¹ • z - u) from by
        funext z; rw [Submission.BoseGases.chiSmallB]]
      exact (Submission.BoseGases.chiScale_continuous _).mul
        ((Work.SmallBoxSliding.chiSmall_continuous_all _).comp (by fun_prop))
    rw [show (fun x : Submission.BoseGases.X n => Work.BoseFixB1.nCountB
          (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u x)
        = fun x => ∑ i : Fin n, (Submission.BoseGases.chiSmallB
            (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u
            (x i)) ^ 2 from by
      funext x; rw [Work.BoseFixB1.nCountB]]
    exact continuous_finsetSum _ fun i _ => (hchi.comp (continuous_apply i)).pow 2
  have ht_cont : Continuous (fun x : Submission.BoseGases.X n =>
      Work.BoseFixB1.nCountB (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
        (Work.BoseFixB1.pD v μ) u x
      / Work.SmallBoxSliding.chiMass (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
          (Work.BoseFixB1.pD v μ) u) := hnc_cont.div_const _
  have hI1 : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n => (Φ x) ^ 2)
      (Submission.BoseGases.abox n (Work.BoseFixB1.pL v μ)) MeasureTheory.volume :=
    Work.UBBInputs9.B.integrableOn_abox_of_continuous' (hΦc.pow 2)
  have hI2 : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n => (Φ x) ^ 2 *
      (Work.BoseFixB1.nCountB (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
        (Work.BoseFixB1.pD v μ) u x
      / Work.SmallBoxSliding.chiMass (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
          (Work.BoseFixB1.pD v μ) u))
      (Submission.BoseGases.abox n (Work.BoseFixB1.pL v μ)) MeasureTheory.volume :=
    Work.UBBInputs9.B.integrableOn_abox_of_continuous' ((hΦc.pow 2).mul ht_cont)
  have hI3 : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n => (Φ x) ^ 2 *
      (Work.BoseFixB1.nCountB (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
        (Work.BoseFixB1.pD v μ) u x
      / Work.SmallBoxSliding.chiMass (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
          (Work.BoseFixB1.pD v μ) u) ^ 2)
      (Submission.BoseGases.abox n (Work.BoseFixB1.pL v μ)) MeasureTheory.volume :=
    Work.UBBInputs9.B.integrableOn_abox_of_continuous' ((hΦc.pow 2).mul (ht_cont.pow 2))
  -- the mass is positive in the flat band
  have hmass_eq : Work.BoseBoxFix.normB v μ n Φ = flatMass (Work.BoseFixB1.pL v μ) Φ := rfl
  have hMne : flatMass (Work.BoseFixB1.pL v μ) Φ ≠ 0 := by
    rw [← hmass_eq]; exact ne_of_gt hN
  -- the `t`-integral is `flatScountB / chiMass`
  have hIdiv : (∫ x in Submission.BoseGases.abox n (Work.BoseFixB1.pL v μ), (Φ x) ^ 2 *
      (Work.BoseFixB1.nCountB (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
        (Work.BoseFixB1.pD v μ) u x
      / Work.SmallBoxSliding.chiMass (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
          (Work.BoseFixB1.pD v μ) u))
      = flatScountB (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
          (Work.BoseFixB1.pD v μ) u Φ
        / Work.SmallBoxSliding.chiMass (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
            (Work.BoseFixB1.pD v μ) u := by
    rw [flatScountB]
    rw [show (fun x : Submission.BoseGases.X n => (Φ x) ^ 2 *
          (Work.BoseFixB1.nCountB (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
            (Work.BoseFixB1.pD v μ) u x
          / Work.SmallBoxSliding.chiMass (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
              (Work.BoseFixB1.pD v μ) u))
        = fun x => ((Φ x) ^ 2 * Work.BoseFixB1.nCountB (Work.BoseFixB1.pM v μ)
            (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u x)
          / Work.SmallBoxSliding.chiMass (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
              (Work.BoseFixB1.pD v μ) u from by
      funext x; ring]
    rw [MeasureTheory.integral_div]
  -- the weighted-mean identity
  have hmean : flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
        (Work.BoseFixB1.pD v μ) u Φ
        * (∫ x in Submission.BoseGases.abox n (Work.BoseFixB1.pL v μ), (Φ x) ^ 2)
      = ∫ x in Submission.BoseGases.abox n (Work.BoseFixB1.pL v μ), (Φ x) ^ 2 *
          (Work.BoseFixB1.nCountB (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
            (Work.BoseFixB1.pD v μ) u x
          / Work.SmallBoxSliding.chiMass (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
              (Work.BoseFixB1.pD v μ) u) := by
    rw [show (∫ x in Submission.BoseGases.abox n (Work.BoseFixB1.pL v μ), (Φ x) ^ 2)
        = flatMass (Work.BoseFixB1.pL v μ) Φ from rfl, hIdiv, flatTau]
    rw [(show flatScountB (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
            (Work.BoseFixB1.pD v μ) u Φ
          / (Work.SmallBoxSliding.chiMass (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
              (Work.BoseFixB1.pD v μ) u * flatMass (Work.BoseFixB1.pL v μ) Φ)
        = (flatScountB (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
              (Work.BoseFixB1.pD v μ) u Φ
            / Work.SmallBoxSliding.chiMass (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                (Work.BoseFixB1.pD v μ) u)
          / flatMass (Work.BoseFixB1.pL v μ) Φ from (div_div _ _ _).symm)]
    rw [div_mul_cancel₀ _ hMne]
  -- the mean–variance identity
  have hkey := integral_mul_sq_sub_mean (ν := MeasureTheory.volume.restrict
      (Submission.BoseGases.abox n (Work.BoseFixB1.pL v μ)))
    (f := fun x : Submission.BoseGases.X n => (Φ x) ^ 2)
    (g := fun x : Submission.BoseGases.X n => Work.BoseFixB1.nCountB (Work.BoseFixB1.pM v μ)
        (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u x
      / Work.SmallBoxSliding.chiMass (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
          (Work.BoseFixB1.pD v μ) u)
    (τ := flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u Φ)
    hI1 hI2 hI3 hmean
  have hleft : (∫ x, (Φ x) ^ 2 *
        (Work.BoseFixB1.nCountB (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
            (Work.BoseFixB1.pD v μ) u x
          / Work.SmallBoxSliding.chiMass (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
              (Work.BoseFixB1.pD v μ) u
          - flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
              (Work.BoseFixB1.pD v μ) u Φ) ^ 2
        ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox n (Work.BoseFixB1.pL v μ))))
      = flatVar v μ Φ u := by
    rw [hkey]
    rw [show (∫ x, (Φ x) ^ 2 * (Work.BoseFixB1.nCountB (Work.BoseFixB1.pM v μ)
            (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u x
          / Work.SmallBoxSliding.chiMass (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
              (Work.BoseFixB1.pD v μ) u) ^ 2
        ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox n (Work.BoseFixB1.pL v μ))))
        = flatT2 v μ Φ u from rfl,
      show (∫ x, (Φ x) ^ 2
        ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox n (Work.BoseFixB1.pL v μ))))
        = flatMass (Work.BoseFixB1.pL v μ) Φ from rfl,
      flatVar]
    rw [hmass_eq]
  rw [← hleft]
  exact MeasureTheory.integral_nonneg fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _)

/-! ## 2. The named error bracket and arithmetic slack of the flat ledger -/

/-- The `PerBoxF` error bracket, in the exact spelling used by the ledger
`Up.perBoxF_of_ledger_kin` (so that a residual hypothesis stated with `flatErrB` is *definitionally*
the ledger's budget slot). -/
noncomputable def flatErrB (v : EuclideanSpace ℝ (Fin 3) → ℝ) (R μ : ℝ) {n : ℕ}
    (Φ : Submission.BoseGases.X n → ℝ) (u : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  μ ^ 2 * (_root_.BoseGases.a v)
      * ((R / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
            * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)) ^ 2
          + (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
            * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ))
      * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
      * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
    + μ * (_root_.BoseGases.a v) * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)

/-- The arithmetic slack of the sharp flat ledger at `c₁ = 1/8`, in the exact spelling used by the
ledger `Up.perBoxF_of_ledger_kin` (with `V := Up.flatVar`). -/
noncomputable def flatSlackB (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) (μ : ℝ)
    {n : ℕ} (Φ : Submission.BoseGases.X n → ℝ) (u : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  Work.BoseFixB1.w1MassB h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
      (Work.BoseFixB1.pD v μ) u
    * ((Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
            (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) - μ) ^ 2
        * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
        * (1 / 2 - (1 / 8) * μ
            / (Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) + μ))
      + flatVar v μ (Φ : Submission.BoseGases.X n → ℝ) u
        * (1 / 2 - 4 * (1 / 8) * μ ^ 2
            / (Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) + μ) ^ 2))

/-- **The flat branch decomposed into rows.**  There are constants `ε₀`, `K₂ ≥ 0`, `γ > 0` and
`C ≥ 0` such that, at every admissible `μ`, every box state of the good set whose box is thick and
whose box excited count is inside the free-threshold band `n₊(B) < γ n ‖Φ‖²`, the fibre deviation
`Efib`, the pair deviation `Epair` and the budget can be exhibited.  See the module docstring. -/
def FlatRows (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) (R : ℝ) : Prop :=
  ∃ ε₀ K₂ γ C : ℝ, 0 < ε₀ ∧ 0 ≤ K₂ ∧ 0 < γ ∧ 0 ≤ C ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
        (u : EuclideanSpace ℝ (Fin 3)),
        u ∈ Work.SmallBoxSliding.goodSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ →
        ¬ IsThinBox v h μ u →
        nPlusB v μ u n (Φ : Submission.BoseGases.X n → ℝ)
            < γ * (n : ℝ) * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) →
        ∃ Efib Epair : ℝ,
          (μ * Work.BoseFixB1.flatFibSum h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ)
              ≤ μ * Work.BoseFixB1.w1MassB h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                    (Work.BoseFixB1.pD v μ) u
                  * Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                      (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ)
                  * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) + Efib)
          ∧ ((1 / 2) * Work.BoseFixB1.flatPairMass v (Work.BoseFixB1.pM v μ)
                  (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u
                * (Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                      (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) ^ 2
                    * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
                  + flatVar v μ (Φ : Submission.BoseGases.X n → ℝ) u)
              ≤ Work.BoseFixB1.flatPairSum v (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                    (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) + Epair)
          ∧ Efib + Epair
              ≤ C * flatErrB v R μ (Φ : Submission.BoseGases.X n → ℝ) u
                + flatSlackB v h μ (Φ : Submission.BoseGases.X n → ℝ) u
                + K₂ * μ * (_root_.BoseGases.a v) * nPlusB v μ u n
                    (Φ : Submission.BoseGases.X n → ℝ)

/-! ## 3. `FlatRows ⟹ FlatFreeResidual` -/

/-- **The rows imply the flat branch.**  Everything the ledger
`Up.perBoxF_of_ledger_kin` needs besides the rows is proved:

* the sharp `F`-row at `V := flatVar` — `Up.flatFterm_sharp_row`;
* `0 ≤ flatVar` — `flatVar_nonneg` (and the band forces `0 < normB`);
* the split `sbPot = −μ·fibSum + pairSum` — `Up.sbPot_split` (with `R ≤ ℓd/16`, `R ≤ ℓ·chiR0`
  from `Work.BoseFixB1.regime_sideAt_ge`, at a smaller `ε₀`);
* the kinetic supply — `Up.sbKin_ge_K2_mu_av_nPlus` (at a smaller `ε₀`). -/
theorem flatFreeResidual_of_flatRows {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v)
    (hrows : FlatRows v h R) : FlatFreeResidual v h R := by
  obtain ⟨ε₀r, K₂, γ, C, hε₀r, hK₂, hγ, hC, H⟩ := hrows
  obtain ⟨εr, hεr, hreg⟩ := Work.BoseFixB1.regime_sideAt_ge (v := v) hav hR
  obtain ⟨εk, hεk, hk⟩ := sbKin_ge_K2_mu_av_nPlus (v := v) hav K₂ hK₂
  refine ⟨γ, hγ, min (min ε₀r εr) εk, 1 / 8, C, lt_min (lt_min hε₀r hεr) hεk,
    by norm_num, hC, ?_⟩
  intro μ hAdm n Φ u hu hthin hband
  have hAdm_r : Work.BoseBoxFix.Adm v ε₀r μ :=
    Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_left _ _) (min_le_left _ _))
  have hAdm_R : Work.BoseBoxFix.Adm v εr μ :=
    Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_left _ _) (min_le_right _ _))
  have hAdm_k : Work.BoseBoxFix.Adm v εk μ := Work.BoseFixB1.Adm.mono hAdm (min_le_right _ _)
  have hμ : 0 < μ := hAdm.1
  have hℓ : 0 < Work.BoseFixB1.pL v μ := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < Work.BoseFixB1.pD v μ := Work.BoseFixB1.adm_d_pos hAdm
  have hM1 : 1 ≤ Work.BoseFixB1.pM v μ := by
    change 1 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
    rw [Work.BoseFixB1.M_eq_mValue]; norm_num [Work.BoseBox.mValue]
  obtain ⟨hR16, hRχ⟩ := hreg μ hAdm_R.1 hAdm_R.2.1
  have hΦc : Continuous (Φ : Submission.BoseGases.X n → ℝ) := Φ.contDiff.continuous
  -- the band forces a nonzero mass
  have hnplus0 : 0 ≤ nPlusB v μ u n (Φ : Submission.BoseGases.X n → ℝ) := by
    rw [nPlusB, Work.UBBInputs8.cnPlusBoxInd]
    exact Finset.sum_nonneg fun i _ => MeasureTheory.integral_nonneg fun x => sq_nonneg _
  have hnpos : 0 < (n : ℝ) := by
    rcases lt_or_ge (0 : ℝ) (n : ℝ) with hpos | hle
    · exact hpos
    · exfalso
      have hz : (n : ℝ) = 0 := le_antisymm hle (Nat.cast_nonneg n)
      have h2 : 0 < γ * (n : ℝ) * Work.BoseBoxFix.normB v μ n
          (Φ : Submission.BoseGases.X n → ℝ) := lt_of_le_of_lt hnplus0 hband
      simp only [hz, mul_zero, zero_mul] at h2
      exact absurd h2 (lt_irrefl (0 : ℝ))
  have hNpos : 0 < Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) := by
    have h2 : 0 < γ * (n : ℝ) * Work.BoseBoxFix.normB v μ n
        (Φ : Submission.BoseGases.X n → ℝ) := lt_of_le_of_lt hnplus0 hband
    exact pos_of_mul_pos_right h2 (le_of_lt (mul_pos hγ hnpos))
  obtain ⟨Efib, Epair, hfib, hpair, hbud⟩ := H μ hAdm_r n Φ u hu hthin hband
  -- the proved ingredients
  have hF := flatFterm_sharp_row (v := v) h hAdm_r Φ u
  have hN0 : 0 ≤ Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) := le_of_lt hNpos
  have hV : 0 ≤ flatVar v μ (Φ : Submission.BoseGases.X n → ℝ) u := flatVar_nonneg hΦc hNpos u
  have hW1 : 0 ≤ Work.BoseFixB1.w1MassB h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
      (Work.BoseFixB1.pD v μ) u :=
    w1MassB_nonneg (M := Work.BoseFixB1.pM v μ) (ℓ := Work.BoseFixB1.pL v μ)
      (d := Work.BoseFixB1.pD v μ) h hv hvrad hR hv_supp hℓ hd u
  have hW12 := Work.BoseFixB1S.w1MassB_le_flatPairMassB1 (v := v) h hv hvrad hv1 hR hv_supp
    hM1 hℓ hd hR16 hRχ u
  have hτ : 0 ≤ Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
      (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) := by
    rw [Work.BoseFixB1.flatTau]
    refine div_nonneg ?_ ?_
    · rw [Work.BoseFixB1.flatScountB]
      refine MeasureTheory.integral_nonneg fun x => mul_nonneg (sq_nonneg _) ?_
      rw [Work.BoseFixB1.nCountB]
      exact Finset.sum_nonneg fun i _ => sq_nonneg _
    · exact mul_nonneg (chiMass_nonneg _ _ _ _) (by
        rw [Work.BoseFixB1.flatMass]
        exact MeasureTheory.integral_nonneg fun x => sq_nonneg _)
  have hsplit : Work.BoseFixB1.sbPot h μ u (Φ : Submission.BoseGases.X n → ℝ)
      = -(μ * Work.BoseFixB1.flatFibSum h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
              (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ))
        + Work.BoseFixB1.flatPairSum v (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
              (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) := by
    have hsp := sbPot_split (v := v) (h := h) (R := R) hv_supp hR hv hvrad hv1 hAdm_r hΦc u hR16 hRχ
    simpa only [Work.BoseFixB1.flatFibSum, fibSum, Work.BoseFixB1.flatPairSum, pairSum] using hsp
  have hkin := hk μ hAdm_k n Φ u
  refine perBoxF_of_ledger_kin (v := v) h (R := R) (C := C) (μ := μ) (c₁ := 1 / 8) (K₂ := K₂)
    hμ (by norm_num) le_rfl hK₂ hN0 hW1 hW12 hτ hV hF hfib hpair hsplit hkin ?_
  simpa only [flatErrB, flatSlackB] using hbud


/-! ## 4. The nonnegativity of the slack, and the **split** residual -/

/-- The box excited count is nonnegative. -/
theorem nPlusB_nonneg (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ)
    (u : EuclideanSpace ℝ (Fin 3)) (n : ℕ) (Φ : Submission.BoseGases.X n → ℝ) :
    0 ≤ nPlusB v μ u n Φ := by
  rw [nPlusB, Work.UBBInputs8.cnPlusBoxInd]
  exact Finset.sum_nonneg fun i _ => MeasureTheory.integral_nonneg fun x => sq_nonneg _

/-- Inside the flat band the state's mass is positive. -/
theorem band_normB_pos {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ γ : ℝ} (hγ : 0 < γ)
    {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ} (u : EuclideanSpace ℝ (Fin 3))
    (hband : nPlusB v μ u n Φ < γ * (n : ℝ) * Work.BoseBoxFix.normB v μ n Φ) :
    0 < Work.BoseBoxFix.normB v μ n Φ := by
  have h2 : 0 < γ * (n : ℝ) * Work.BoseBoxFix.normB v μ n Φ :=
    lt_of_le_of_lt (nPlusB_nonneg v μ u n Φ) hband
  have hnpos : 0 < (n : ℝ) := by
    rcases lt_or_ge (0 : ℝ) (n : ℝ) with hpos | hle
    · exact hpos
    · exfalso
      have hz : (n : ℝ) = 0 := le_antisymm hle (Nat.cast_nonneg n)
      simp only [hz, mul_zero, zero_mul] at h2
      exact absurd h2 (lt_irrefl (0 : ℝ))
  exact pos_of_mul_pos_right h2 (le_of_lt (mul_pos hγ hnpos))

/-- The state's mean smooth density `τ` is nonnegative. -/
theorem flatTau_nonneg {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ} {n : ℕ}
    (Φ : Submission.BoseGases.X n → ℝ) (u : EuclideanSpace ℝ (Fin 3)) :
    0 ≤ Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
      (Work.BoseFixB1.pD v μ) u Φ := by
  rw [Work.BoseFixB1.flatTau]
  refine div_nonneg ?_ ?_
  · rw [Work.BoseFixB1.flatScountB]
    refine MeasureTheory.integral_nonneg fun x => mul_nonneg (sq_nonneg _) ?_
    rw [Work.BoseFixB1.nCountB]
    exact Finset.sum_nonneg fun i _ => sq_nonneg _
  · exact mul_nonneg (chiMass_nonneg _ _ _ _) (by
      rw [Work.BoseFixB1.flatMass]
      exact MeasureTheory.integral_nonneg fun x => sq_nonneg _)

/-- **The arithmetic slack is nonnegative** at `c₁ = 1/8`: both bracketed factors are
`1/2 − (1/8)μ/(τ+μ) ≥ 1/8 > 0` and `1/2 − μ²/(2(τ+μ)²) ≥ 0` for `μ > 0`, `τ ≥ 0`.  (This is why
the two deviation rows below may be stated **without** the slack: adding them and dropping the
slack only weakens the budget.) -/
theorem flatSlackB_nonneg {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {μ : ℝ}
    (hμ : 0 < μ) {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ}
    (u : EuclideanSpace ℝ (Fin 3))
    (hW1 : 0 ≤ Work.BoseFixB1.w1MassB h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
      (Work.BoseFixB1.pD v μ) u)
    (hN : 0 ≤ Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ))
    (hτ : 0 ≤ Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
      (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ))
    (hV : 0 ≤ flatVar v μ (Φ : Submission.BoseGases.X n → ℝ) u) :
    0 ≤ flatSlackB v h μ (Φ : Submission.BoseGases.X n → ℝ) u := by
  rw [flatSlackB]
  refine mul_nonneg hW1 (add_nonneg ?_ ?_)
  · refine mul_nonneg (mul_nonneg (sq_nonneg _) hN) ?_
    rw [sub_nonneg, div_le_iff₀ (by linarith)]
    nlinarith
  · refine mul_nonneg hV ?_
    rw [sub_nonneg, div_le_iff₀ (by positivity)]
    nlinarith [hμ.le, hτ]

/-- **The flat branch split into its two deviation rows.**  This is the *same* content as
`FlatRows`, but with the two state functionals

* `μ·(flatFibSum − W₁·τ·‖Φ‖²)`  — the deviation of the fibre (chemical-potential) term from its
  mean-field value,
* `½W₂(τ²‖Φ‖² + V) − flatPairSum`  — the deviation of the pair term from its mean-field value,

required to be small *separately*, each with its own error constant `Cᵢ` and **kinetic coefficient
`Kᵢ`** (the price of `Kᵢ` is a smaller `ε₀`, see `Up.sbKin_ge_K2_mu_av_nPlus`).  No slack term
appears: it is nonnegative (`flatSlackB_nonneg`) and may be dropped. -/
def FlatRowsSplit (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) (R : ℝ) : Prop :=
  ∃ ε₀ γ C₁ C₂ K₁ K₂ : ℝ, 0 < ε₀ ∧ 0 < γ ∧ 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ 0 ≤ K₁ ∧ 0 ≤ K₂ ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
        (u : EuclideanSpace ℝ (Fin 3)),
        u ∈ Work.SmallBoxSliding.goodSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ →
        ¬ IsThinBox v h μ u →
        nPlusB v μ u n (Φ : Submission.BoseGases.X n → ℝ)
            < γ * (n : ℝ) * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) →
        (μ * (Work.BoseFixB1.flatFibSum h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ)
              - Work.BoseFixB1.w1MassB h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                    (Work.BoseFixB1.pD v μ) u
                  * Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                      (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ)
                  * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ))
            ≤ C₁ * flatErrB v R μ (Φ : Submission.BoseGases.X n → ℝ) u
              + K₁ * μ * (_root_.BoseGases.a v) * nPlusB v μ u n
                  (Φ : Submission.BoseGases.X n → ℝ))
        ∧ ((1 / 2) * Work.BoseFixB1.flatPairMass v (Work.BoseFixB1.pM v μ)
                  (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u
                * (Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                      (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) ^ 2
                    * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
                  + flatVar v μ (Φ : Submission.BoseGases.X n → ℝ) u)
              - Work.BoseFixB1.flatPairSum v (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                  (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ)
            ≤ C₂ * flatErrB v R μ (Φ : Submission.BoseGases.X n → ℝ) u
              + flatSlackB v h μ (Φ : Submission.BoseGases.X n → ℝ) u
              + K₂ * μ * (_root_.BoseGases.a v) * nPlusB v μ u n
                  (Φ : Submission.BoseGases.X n → ℝ))

/-- **The split residual implies `FlatRows`** — the deviations themselves serve as `Efib`, `Epair`
(the two "rows" then hold with equality) and the budget follows by adding the two inequalities and
dropping the nonnegative slack `flatSlackB_nonneg`. -/
theorem flatRows_of_split {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {R : ℝ}
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hsp : FlatRowsSplit v h R) : FlatRows v h R := by
  obtain ⟨ε₀, γ, C₁, C₂, K₁, K₂, hε₀, hγ, hC₁, hC₂, hK₁, hK₂, H⟩ := hsp
  refine ⟨ε₀, K₁ + K₂, γ, C₁ + C₂, hε₀, add_nonneg hK₁ hK₂, hγ, add_nonneg hC₁ hC₂, ?_⟩
  intro μ hAdm n Φ u hu hthin hband
  obtain ⟨hfib, hpair⟩ := H μ hAdm n Φ u hu hthin hband
  have hμ : 0 < μ := hAdm.1
  have hℓ : 0 < Work.BoseFixB1.pL v μ := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < Work.BoseFixB1.pD v μ := Work.BoseFixB1.adm_d_pos hAdm
  have hW1 : 0 ≤ Work.BoseFixB1.w1MassB h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
      (Work.BoseFixB1.pD v μ) u :=
    w1MassB_nonneg (M := Work.BoseFixB1.pM v μ) (ℓ := Work.BoseFixB1.pL v μ)
      (d := Work.BoseFixB1.pD v μ) h hv hvrad hR hv_supp hℓ hd u
  set FibDev : ℝ := Work.BoseFixB1.flatFibSum h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
        (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ)
      - Work.BoseFixB1.w1MassB h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
            (Work.BoseFixB1.pD v μ) u
          * Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
              (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ)
          * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) with hFibDev
  set PairDev : ℝ := (1 / 2) * Work.BoseFixB1.flatPairMass v (Work.BoseFixB1.pM v μ)
          (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u
        * (Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
              (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) ^ 2
            * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
          + flatVar v μ (Φ : Submission.BoseGases.X n → ℝ) u)
      - Work.BoseFixB1.flatPairSum v (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
          (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) with hPairDev
  refine ⟨μ * FibDev, PairDev, ?_, ?_, ?_⟩
  · rw [hFibDev]; linarith
  · rw [hPairDev]; linarith
  · linarith [hfib, hpair]

/-- **The split residual implies the flat branch directly** — the chain
`FlatRowsSplit ⟹ FlatRows ⟹ FlatFreeResidual`.  This is the theorem a prover of the two deviation
rows should cite: proving `FlatRowsSplit` discharges `Up.flatFreeResidual`, hence
`Work.BoseFixB1.perBoxFWeight_holds`. -/
theorem flatFreeResidual_of_split {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v)
    (hsp : FlatRowsSplit v h R) : FlatFreeResidual v h R :=
  flatFreeResidual_of_flatRows h hv hv1 hvrad hR hv_supp hav
    (flatRows_of_split hv hvrad hR hv_supp hsp)


end Work.BoseFixB1.Up
