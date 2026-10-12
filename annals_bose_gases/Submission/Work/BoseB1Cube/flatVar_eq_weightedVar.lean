import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.Up.FrowSharp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB1Cube.flatVar_eq_weightedVar`

The state's smooth-count variance is the squared deviation of the smooth density from its
`Φ²`-weighted mean:

    `flatVar v μ Φ u = ∫_{abox n ℓ} Φ² (t − τ)²`,

with `t := nCountB pM pL pD u / chiMass pM pL pD u` the smooth local density and
`τ := flatTau pM pL pD u Φ` its `Φ²`-weighted mean.

`flatVar` is *defined* as `∫Φ²t² − τ²‖Φ‖²`; the point of the identity is that `τ` is exactly the
weighted mean of `t`, so the two cross terms of the expansion of `(t − τ)²` cancel.  This is the
computation inside `Work.BoseFixB1.Up.flatVar_nonneg`
(`Submission/Work/BoseFixB1/Up/FlatRows.lean`), extracted here as a public identity — it is the
"variance = weighted squared deviation" reading used whenever the variance slot of the flat ledger
is estimated by a pointwise deviation of the density.

The proof is the mean–variance identity `Work.BoseFixB1.Up.integral_mul_sq_sub_mean`
(`∫ f (g − τ)² = ∫ f g² − τ² ∫ f` at a weighted mean `τ ∫f = ∫ f g`) applied to `f := Φ²`,
`g := t`, `τ := flatTau`, together with the definiteness of `normB = ∫_{abox n ℓ} Φ²` and
`flatT2 = ∫ Φ² t²`.  No hypothesis on the cutoff, on `μ` or on the box side is needed; the only
hypothesis is `normB ≠ 0`, which (through `τ = S/(chiMass·normB)`) makes the mean identity hold as
an honest division.

Since `Φ` is continuous and `abox n ℓ` is compact, all three integrability inputs of the
mean–variance identity are supplied by `Work.UBBInputs9.B.integrableOn_abox_of_continuous'`.
-/

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseB1Cube

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1000000

theorem flatVar_eq_weightedVar {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ} {n : ℕ}
    (Φ : Submission.BoseGases.X n → ℝ) (hΦc : Continuous Φ) (u : EuclideanSpace ℝ (Fin 3))
    (hN : Work.BoseBoxFix.normB v μ n Φ ≠ 0) :
    Work.BoseFixB1.Up.flatVar v μ Φ u
      = ∫ x in Submission.BoseGases.abox n (Work.BoseFixB1.pL v μ),
          (Φ x) ^ 2 * (Work.BoseFixB1.nCountB (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                (Work.BoseFixB1.pD v μ) u x
              / Work.SmallBoxSliding.chiMass (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                  (Work.BoseFixB1.pD v μ) u
            - Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                (Work.BoseFixB1.pD v μ) u Φ) ^ 2 := by
  -- continuity of the smooth local density `t = nCountB/chiMass`
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
  -- the three integrability inputs
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
  -- the mass is the `flatMass`, and nonzero
  have hmass_eq : Work.BoseBoxFix.normB v μ n Φ
      = Work.BoseFixB1.flatMass (Work.BoseFixB1.pL v μ) Φ := rfl
  have hMne : Work.BoseFixB1.flatMass (Work.BoseFixB1.pL v μ) Φ ≠ 0 := by
    rw [← hmass_eq]; exact hN
  -- the `t`-integral is `flatScountB / chiMass`
  have hIdiv : (∫ x in Submission.BoseGases.abox n (Work.BoseFixB1.pL v μ), (Φ x) ^ 2 *
      (Work.BoseFixB1.nCountB (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
        (Work.BoseFixB1.pD v μ) u x
      / Work.SmallBoxSliding.chiMass (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
          (Work.BoseFixB1.pD v μ) u))
      = Work.BoseFixB1.flatScountB (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
          (Work.BoseFixB1.pD v μ) u Φ
        / Work.SmallBoxSliding.chiMass (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
            (Work.BoseFixB1.pD v μ) u := by
    rw [Work.BoseFixB1.flatScountB]
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
  -- `flatTau` is the `Φ²`-weighted mean of `t`
  have hmean : Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
        (Work.BoseFixB1.pD v μ) u Φ
        * (∫ x in Submission.BoseGases.abox n (Work.BoseFixB1.pL v μ), (Φ x) ^ 2)
      = ∫ x in Submission.BoseGases.abox n (Work.BoseFixB1.pL v μ), (Φ x) ^ 2 *
          (Work.BoseFixB1.nCountB (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
            (Work.BoseFixB1.pD v μ) u x
          / Work.SmallBoxSliding.chiMass (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
              (Work.BoseFixB1.pD v μ) u) := by
    rw [show (∫ x in Submission.BoseGases.abox n (Work.BoseFixB1.pL v μ), (Φ x) ^ 2)
        = Work.BoseFixB1.flatMass (Work.BoseFixB1.pL v μ) Φ from rfl, hIdiv,
      Work.BoseFixB1.flatTau]
    rw [(show Work.BoseFixB1.flatScountB (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
            (Work.BoseFixB1.pD v μ) u Φ
          / (Work.SmallBoxSliding.chiMass (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
              (Work.BoseFixB1.pD v μ) u * Work.BoseFixB1.flatMass (Work.BoseFixB1.pL v μ) Φ)
        = (Work.BoseFixB1.flatScountB (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
              (Work.BoseFixB1.pD v μ) u Φ
            / Work.SmallBoxSliding.chiMass (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                (Work.BoseFixB1.pD v μ) u)
          / Work.BoseFixB1.flatMass (Work.BoseFixB1.pL v μ) Φ from (div_div _ _ _).symm)]
    rw [div_mul_cancel₀ _ hMne]
  -- the mean–variance identity
  have hkey := Work.BoseFixB1.Up.integral_mul_sq_sub_mean
    (ν := MeasureTheory.volume.restrict (Submission.BoseGases.abox n (Work.BoseFixB1.pL v μ)))
    (f := fun x : Submission.BoseGases.X n => (Φ x) ^ 2)
    (g := fun x : Submission.BoseGases.X n => Work.BoseFixB1.nCountB (Work.BoseFixB1.pM v μ)
        (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u x
      / Work.SmallBoxSliding.chiMass (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
          (Work.BoseFixB1.pD v μ) u)
    (τ := Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
        (Work.BoseFixB1.pD v μ) u Φ) hI1 hI2 hI3 hmean
  have hleft : (∫ x, (Φ x) ^ 2 *
        (Work.BoseFixB1.nCountB (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
            (Work.BoseFixB1.pD v μ) u x
          / Work.SmallBoxSliding.chiMass (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
              (Work.BoseFixB1.pD v μ) u
          - Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
              (Work.BoseFixB1.pD v μ) u Φ) ^ 2
        ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox n (Work.BoseFixB1.pL v μ))))
      = Work.BoseFixB1.Up.flatVar v μ Φ u := by
    rw [hkey]
    rw [show (∫ x, (Φ x) ^ 2 * (Work.BoseFixB1.nCountB (Work.BoseFixB1.pM v μ)
            (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u x
          / Work.SmallBoxSliding.chiMass (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
              (Work.BoseFixB1.pD v μ) u) ^ 2
        ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox n (Work.BoseFixB1.pL v μ))))
        = Work.BoseFixB1.Up.flatT2 v μ Φ u from rfl,
      show (∫ x, (Φ x) ^ 2
        ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox n (Work.BoseFixB1.pL v μ))))
        = Work.BoseFixB1.flatMass (Work.BoseFixB1.pL v μ) Φ from rfl,
      Work.BoseFixB1.Up.flatVar]
    rw [hmass_eq]
  exact hleft.symm

end Work.BoseB1Cube
