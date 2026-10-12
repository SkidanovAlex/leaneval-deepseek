import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.slotSum_gapWord_eq_b_cnPlus
import Submission.Work.BoseFixB2.Sector.integrableOn_fsT_fibre_smooth
import Submission.Work.BoseKinLoc.Word.kinFormB_nonneg
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.kinFormB_ge_gapColumn_smooth` — the gap column of `kinFormB` at **smooth** states

The sibling assignment `Work.BoseFixB1S.kinFormB_ge_gapColumn` asks for

    `b * ℓ ^ (-2) * cnPlusBoxInd ℓ (acube ℓ) (ℓ³) Φ ≤ kinFormB n ℓ d s ε_T b Φ`

under the *only* hypothesis `hΦ2 : IntegrableOn (Φ²) (abox n ℓ)` — i.e. for a merely `L²` state.
**That statement is false** (`FINDING_kinFormB_ge_gapColumn.md` in this directory): `kinFormB`'s
slot integrand is a *Bochner* integral, and for a merely `L²` `Φ` the integrand

    `x ↦ 1_{Λ(0)}(xᵢ) · 𝒯(fibreᵢ Φ x)`

need not be integrable: all its values are finite, but its `lintegral` can be `+∞` (the slot
fibres of an `L²`-but-not-`H¹` state can be smooth with a.e. finite yet non-integrable
`H¹`-energy, and `fsT`'s fourth piece `mainWord` contains exactly that energy).  Lean's
Bochner convention (`MeasureTheory.integral_undef`) then returns `0` for the slot integral,
while the left-hand side is a positive number.  The corpus records the same phenomenon for the
whole `fsT` family: every statement about it in the workspace assumes *smoothness* (or compact
support), see `Work.BoseKinLoc.Word.fsT_nonneg_of_continuous`,
`Work.BoseFixB2.Sector.integrableOn_fsT_fibre_smooth`,
`Work.BoseFixB1.slotSum_gapWord_eq_b_cnPlus` — all of them carry `ContDiff ℝ ∞ Φ`.

This file provides the **repaired statement**, with `hΦ2` replaced by smoothness (which is
exactly the state class of FS's box energy: `Work.BoseKinLoc.BoxState` has
`contDiff : ContDiff ℝ ∞ toFun`).

## Proof

* `cnPlusBoxInd_acube_eq_cnPlus`: FS's faithful box count at the *anchored* cube `acube ℓ` with
  normalisation `ℓ³ = |acube ℓ|` is the corpus's `cnPlus` — the two integrands agree
  *pointwise on the box* (`boxQInd ℓ³ (acube ℓ) i Φ x = aQ ℓ i Φ x` there, because the box
  indicator is `1` and `boxPInd`'s normalised slice mean is `aP`), so
  `MeasureTheory.setIntegral_congr_fun` gives the identity **with no integrability hypothesis**.
* `Work.BoseFixB1.slotSum_gapWord_eq_b_cnPlus`: for smooth `Φ`, the slot sum of the gap word
  is exactly `bℓ⁻²·cnPlus ℓ Φ` (the corpus's `n₊` identity).
* per slot: `∫_{abox} 1_{Λ(0)}(xᵢ)·gapWord(fibreᵢ) ≤ ∫_{abox} 1_{Λ(0)}(xᵢ)·fsT(fibreᵢ)`.
  The integrand of the right-hand side is integrable
  (`Work.BoseFixB2.Sector.integrableOn_fsT_fibre_smooth`, smoothness of `Φ`), the left-hand
  integrand is pointwise nonnegative and pointwise dominated by it
  (`gapWord ≤ fsT`: `fsT = fsT(b=0) + gapWord + momWord` with `fsT(b=0) ≥ 0` by
  `fsT_nonneg_of_continuous` and `momWord ≥ 0`), so `MeasureTheory.integral_mono_of_nonneg`
  applies — no measurability of the left integrand is needed.
* sum over the slots and factor `ℓ⁻³ ≥ 0`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Work.BoseFixB1S

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## 1. The FS-faithful box count at the anchored cube is the corpus's `cnPlus` -/

/-- **`cnPlusBoxInd ℓ (acube ℓ) (ℓ³) Φ = cnPlus ℓ Φ`** for every `Φ`.

This needs no integrability assumption: on the configuration box the box indicator is `1` and
`boxPInd`'s normalised `A`-fibre mean is exactly `aP`, so the two integrands agree pointwise on
`abox n ℓ` and `MeasureTheory.setIntegral_congr_fun` applies. -/
theorem cnPlusBoxInd_acube_eq_cnPlus (ℓ : ℝ) {n : ℕ} (Φ : Submission.BoseGases.X n → ℝ) :
    Work.UBBInputs8.cnPlusBoxInd ℓ (Submission.BoseGases.acube ℓ) (ℓ ^ 3) Φ
      = Submission.BoseGases.cnPlus ℓ Φ := by
  rw [Work.UBBInputs8.cnPlusBoxInd, Submission.BoseGases.cnPlus]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.abox_measurable n ℓ)
    (fun x hx => ?_)
  have hind : (Submission.BoseGases.acube ℓ).indicator (fun _ => (1 : ℝ)) (x i) = 1 :=
    Set.indicator_of_mem (hx i) _
  have hp : Work.UBBInputs8.boxQInd (ℓ ^ 3) (Submission.BoseGases.acube ℓ) i Φ x
      = Submission.BoseGases.aQ ℓ i Φ x := by
    rw [Work.UBBInputs8.boxQInd, Work.UBBInputs8.boxPInd, Submission.BoseGases.aQ,
      Submission.BoseGases.aP, hind, one_mul, mul_one]
  rw [hp]

/-! ## 2. The gap word is dominated by the full kinetic word -/

/-- **`gapWord ≤ fsT` at the anchored box**, for a continuous one-body state.

`fsT(…,b) = fsT(…,0) + gapWord(b) + momWord(b)` (`gapWord(0) = momWord(0) = 0`) and the two
extra pieces are nonnegative at a continuous state: `fsT(…,0) ≥ 0` by
`Work.BoseKinLoc.Word.fsT_nonneg_of_continuous` (`b = 0`) and `momWord ≥ 0` by
`Work.BoseKinLoc.momWord_nonneg`. -/
theorem gapWord_le_fsT_of_continuous {ℓ d s εT b : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hs : 0 < s)
    (hεT : 0 ≤ εT) (hεT1 : εT ≤ 1) (hb : 0 ≤ b)
    {ψ : ℝ³ → ℝ} (hψ : Continuous ψ) :
    Work.BoseKinLoc.gapWord ℓ b 0 ψ
      ≤ Work.BoseKinLoc.fsT ℓ d s εT b 0 ψ := by
  have hdℓ : 0 ≤ d * ℓ := (mul_pos hd hℓ).le
  have hsplit : Work.BoseKinLoc.fsT ℓ d s εT b 0 ψ
      = Work.BoseKinLoc.fsT ℓ d s εT 0 0 ψ + Work.BoseKinLoc.gapWord ℓ b 0 ψ
        + Work.BoseKinLoc.momWord ℓ d εT b 0 ψ := by
    rw [Work.BoseKinLoc.fsT_eq_sum (ℓ := ℓ) (d := d) (s := s) (εT := εT) (b := b) (u := 0)
        (ψ := ψ),
      Work.BoseKinLoc.fsT_eq_sum (ℓ := ℓ) (d := d) (s := s) (εT := εT) (b := 0) (u := 0)
        (ψ := ψ)]
    simp only [Work.BoseKinLoc.gapWord, Work.BoseKinLoc.momWord]
    ring
  have h0 : 0 ≤ Work.BoseKinLoc.fsT ℓ d s εT 0 0 ψ :=
    Work.BoseKinLoc.Word.fsT_nonneg_of_continuous hℓ hd hs hεT hεT1 (le_refl 0) 0 hψ
  have hmom : 0 ≤ Work.BoseKinLoc.momWord ℓ d εT b 0 ψ :=
    Work.BoseKinLoc.momWord_nonneg hb hεT hdℓ 0 ψ
  linarith [hsplit, h0, hmom]

/-! ## 3. The repaired gap column -/

/-- **The gap column of the localised box kinetic word at smooth states.**

For a smooth `Φ` and `0 < ℓ`, `0 < d`, `0 < s`, `0 ≤ ε_T ≤ 1`, `b ≥ 0`:

    `b ℓ⁻² · cnPlusBoxInd ℓ (acube ℓ) (ℓ³) Φ ≤ kinFormB n ℓ d s ε_T b Φ` .

This is the repaired form of the requested `Work.BoseFixB1S.kinFormB_ge_gapColumn`, whose only
hypothesis `hΦ2 : IntegrableOn (Φ²) (abox n ℓ)` is *not* enough: without smoothness the
`kinFormB` slot integrand need not be integrable and Lean's `∫` returns `0` by
`MeasureTheory.integral_undef`, so the inequality fails for `L² \\ H¹` states (see
`FINDING_kinFormB_ge_gapColumn.md`).  Every consumer in the corpus works on
`Work.BoseKinLoc.BoxState`, which carries `ContDiff ℝ ∞`, so smoothness loses nothing. -/
theorem kinFormB_ge_gapColumn_smooth {ℓ d s εT b : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hs : 0 < s)
    (hεT : 0 ≤ εT) (hεT1 : εT ≤ 1) (hb : 0 ≤ b) {n : ℕ} (Φ : Submission.BoseGases.X n → ℝ)
    (hΦ : ContDiff ℝ (⊤ : ENat) Φ) :
    b * ℓ ^ (-2 : ℤ)
        * Work.UBBInputs8.cnPlusBoxInd ℓ (Submission.BoseGases.acube ℓ) (ℓ ^ 3) Φ
      ≤ Work.BoseKinLoc.kinFormB n ℓ d s εT b Φ := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp [Work.UBBInputs8.cnPlusBoxInd, Work.BoseKinLoc.kinFormB]
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hn)
    rw [cnPlusBoxInd_acube_eq_cnPlus]
    -- the corpus identity: the slot sum of the gap word is `bℓ⁻²·cnPlus`
    have hId := Work.BoseFixB1.slotSum_gapWord_eq_b_cnPlus (n := m) (ℓ := ℓ) (b := b) hℓ Φ hΦ
    -- per slot: the gap integrand is pointwise dominated by the (integrable) `fsT` integrand
    have hslot : ∀ i : Fin (m + 1),
        (∫ x in Submission.BoseGases.abox (m + 1) ℓ,
            Work.BoseKinLoc.indU ℓ 0 (x i)
              * Work.BoseKinLoc.gapWord ℓ b 0 (Work.BoseKinLoc.fibre (m + 1) i Φ x))
          ≤ ∫ x in Submission.BoseGases.abox (m + 1) ℓ,
              Work.BoseKinLoc.indU ℓ 0 (x i)
                * Work.BoseKinLoc.fsT ℓ d s εT b 0
                    (Work.BoseKinLoc.fibre (m + 1) i Φ x) := by
      intro i
      have hInt : Integrable (fun x : Submission.BoseGases.X (m + 1) =>
          Work.BoseKinLoc.indU ℓ 0 (x i)
            * Work.BoseKinLoc.fsT ℓ d s εT b 0
                (Work.BoseKinLoc.fibre (m + 1) i Φ x))
          ((volume : Measure (Submission.BoseGases.X (m + 1))).restrict
            (Submission.BoseGases.abox (m + 1) ℓ)) :=
        Work.BoseFixB2.Sector.integrableOn_fsT_fibre_smooth (ℓ := ℓ) (d := d) (s := s)
          (εT := εT) (b := b) hℓ i hΦ
      refine MeasureTheory.integral_mono_of_nonneg ?_ hInt ?_
      · refine Filter.Eventually.of_forall (fun x => ?_)
        exact mul_nonneg (Work.BoseKinLoc.Word.kinFormB_indU_nonneg ℓ 0 (x i))
          (Work.BoseKinLoc.gapWord_nonneg hb hℓ.le 0 _)
      · refine Filter.Eventually.of_forall (fun x => ?_)
        exact mul_le_mul_of_nonneg_left
          (gapWord_le_fsT_of_continuous hℓ hd hs hεT hεT1 hb
            (Work.BoseKinLoc.Word.kinFormB_fibre_continuous i x hΦ.continuous))
          (Work.BoseKinLoc.Word.kinFormB_indU_nonneg ℓ 0 (x i))
    calc b * ℓ ^ (-2 : ℤ) * Submission.BoseGases.cnPlus ℓ Φ
        = ℓ ^ (-3 : ℤ) * (∑ i : Fin (m + 1),
            ∫ x in Submission.BoseGases.abox (m + 1) ℓ,
              Work.BoseKinLoc.indU ℓ 0 (x i)
                * Work.BoseKinLoc.gapWord ℓ b 0
                    (Work.BoseKinLoc.fibre (m + 1) i Φ x)) := hId.symm
      _ ≤ ℓ ^ (-3 : ℤ) * (∑ i : Fin (m + 1),
            ∫ x in Submission.BoseGases.abox (m + 1) ℓ,
              Work.BoseKinLoc.indU ℓ 0 (x i)
                * Work.BoseKinLoc.fsT ℓ d s εT b 0
                    (Work.BoseKinLoc.fibre (m + 1) i Φ x)) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hslot i))
            (zpow_nonneg hℓ.le _)
      _ = Work.BoseKinLoc.kinFormB (m + 1) ℓ d s εT b Φ := rfl

/-- **The gap column at FS's box states** (`Work.BoseKinLoc.BoxState`), the exact state class of
the corpus's consumers (`EΛ`, `PerBoxF`, `PerBoxFlatAt`, `IsLowB`): the box-state field
`contDiff` discharges the smoothness hypothesis of `kinFormB_ge_gapColumn_smooth`. -/
theorem kinFormB_ge_gapColumn_boxState {ℓ d s εT b : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hs : 0 < s)
    (hεT : 0 ≤ εT) (hεT1 : εT ≤ 1) (hb : 0 ≤ b) {n : ℕ}
    (Φ : Work.BoseKinLoc.BoxState n ℓ) :
    b * ℓ ^ (-2 : ℤ)
        * Work.UBBInputs8.cnPlusBoxInd ℓ (Submission.BoseGases.acube ℓ) (ℓ ^ 3)
            (Φ : Submission.BoseGases.X n → ℝ)
      ≤ Work.BoseKinLoc.kinFormB n ℓ d s εT b (Φ : Submission.BoseGases.X n → ℝ) :=
  kinFormB_ge_gapColumn_smooth hℓ hd hs hεT hεT1 hb
    (Φ : Submission.BoseGases.X n → ℝ) Φ.contDiff

end Work.BoseFixB1S
