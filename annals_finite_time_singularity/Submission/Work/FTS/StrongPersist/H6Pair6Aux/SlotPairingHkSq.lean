/-
Copyright: work module for the Elgindi finite-time singularity project.

# The `ℋ⁶`-Cauchy–Schwarz (AM–GM) bound for a single leaf slot

`Work.FTS.TransportS.slotPairing ρ a b u f = ∫_z ∫_θ ρ · D_z^bD_θ^a u · D_z^bD_θ^a f` is the
elementary slot pairing out of which the coercive pairing `IP6` is assembled.  Every leaf
weight `ρ` of the slot `a` (`ρ = leafEta = w² sin(2θ)^{-η}`, `ρ = leafOne = w²`, or
`ρ = leafGam α = w² sin(2θ)^{-γ}` at a slot with `a ≥ 1`) is pointwise dominated by the slot
weight `slotW α a`, whose square root is the block weight of the `a`-th slot of
`HkIntegrand α 6`; hence `ρ z θ · (D_z^bD_θ^a h z θ)² ≤ HkIntegrand α 6 h z θ`
(`domLeaf_all`, `T5bPrep`).  The pointwise AM–GM inequality then gives

  `|ρ X Y| ≤ (ρ X² + ρ Y²)/2 ≤ (HkIntegrand α 6 u + HkIntegrand α 6 f)/2`

for `θ` in the open interval (the two endpoints are null), and two monotone-integration steps
(one in `θ`, one in `z`, against the honest slices supplied by `HkMem α 6`) yield

  `|slotPairing ρ a b u f| ≤ (HkSq α 6 u + HkSq α 6 f)/2`.

No smoothness of `u`, `f` is needed: this is the pure `L²` (AM–GM) half of the slot estimate,
the level-six counterpart of `Work.FTS.IPGen.slotPairing_abs_le`, in the additive
`(HkSq u + HkSq f)/2` form consumed by the rows of `StrongPersist`.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T3Row
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bPrep
import Submission.Work.Spaces.PairIntegralLe

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The two endpoints `0`, `π/2` are null for `volume.restrict Iθ`: `θ` lies in the *open*
interval `(0, π/2)` almost everywhere. -/
private lemma ae_mem_Ioo_Iθ :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo (0 : ℝ) (π / 2) := by
  show ∀ᵐ θ ∂(volume.restrict (Set.Icc 0 (π / 2))), θ ∈ Set.Ioo (0 : ℝ) (π / 2)
  rw [← MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := π / 2))]
  exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => hθ)

/-- **The level-six slot pairing is dominated by the average of the two `ℋ⁶`-squares.**

For every leaf weight `ρ` attached to the slot `a`, every slot `(a,b)` with `a + b ≤ 6`, and
any two `ℋ⁶`-data `u`, `f` (no smoothness assumed),

  `|∫_z ∫_θ ρ · D_z^bD_θ^a u · D_z^bD_θ^a f| ≤ (|u|²_{ℋ⁶} + |f|²_{ℋ⁶})/2`.

Route: at every `z ∈ [0,∞)` and almost every angle, `ρ` is nonnegative and each of the two
weighted squares is a slot of the `ℋ⁶`-integrand (`domLeaf_all`); AM–GM splits the product,
and the two integrations in the honest slices (`HkMem`) preserve the bound. -/
theorem SlotPairingHkSq {α : ℝ} (hα : 0 < α) {a b : ℕ} (hab : a + b ≤ 6)
      {ρ : ℝ → ℝ → ℝ} (hρ : Work.FTS.TransportS.IsLeafW α a ρ)
      {u f : ℝ → ℝ → ℝ} (mu : Work.Spaces.HkMem α 6 u) (mf : Work.Spaces.HkMem α 6 f) :
      |Work.FTS.TransportS.slotPairing ρ a b u f|
        ≤ (Work.Spaces.HkSq α 6 u + Work.Spaces.HkSq α 6 f) / 2 := by
  -- ## the pointwise AM–GM bound, almost everywhere in `θ`, for every `z ∈ Iz`
  have hpt : ∀ z ∈ Work.Spaces.Iz, ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      |ρ z θ * Work.Spaces.mixed b a u z θ * Work.Spaces.mixed b a f z θ|
        ≤ (Work.Spaces.HkIntegrand α 6 u z θ
            + Work.Spaces.HkIntegrand α 6 f z θ) / 2 := by
    intro z hz
    filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have hρ0 : 0 ≤ ρ z θ := leaf_nonneg hρ z hθI
    have hu : ρ z θ * (Work.Spaces.mixed b a u z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α 6 u z θ :=
      domLeaf_all hα hρ (f := u) (b' := b) (n := 6) (z := z) (θ := θ) hθ hab
    have hf : ρ z θ * (Work.Spaces.mixed b a f z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α 6 f z θ :=
      domLeaf_all hα hρ (f := f) (b' := b) (n := 6) (z := z) (θ := θ) hθ hab
    have ham : |ρ z θ * Work.Spaces.mixed b a u z θ * Work.Spaces.mixed b a f z θ|
        ≤ (ρ z θ * (Work.Spaces.mixed b a u z θ) ^ 2
            + ρ z θ * (Work.Spaces.mixed b a f z θ) ^ 2) / 2 := by
      rw [abs_mul, abs_mul, abs_of_nonneg hρ0]
      have h1 : |Work.Spaces.mixed b a u z θ| * |Work.Spaces.mixed b a f z θ|
          ≤ ((Work.Spaces.mixed b a u z θ) ^ 2
              + (Work.Spaces.mixed b a f z θ) ^ 2) / 2 :=
        Work.Spaces.abs_mul_abs_le_half_add_sq _ _
      calc ρ z θ * |Work.Spaces.mixed b a u z θ| * |Work.Spaces.mixed b a f z θ|
          = ρ z θ * (|Work.Spaces.mixed b a u z θ|
              * |Work.Spaces.mixed b a f z θ|) := by ring
        _ ≤ ρ z θ * (((Work.Spaces.mixed b a u z θ) ^ 2
              + (Work.Spaces.mixed b a f z θ) ^ 2) / 2) :=
            mul_le_mul_of_nonneg_left h1 hρ0
        _ = (ρ z θ * (Work.Spaces.mixed b a u z θ) ^ 2
              + ρ z θ * (Work.Spaces.mixed b a f z θ) ^ 2) / 2 := by ring
    linarith [ham, hu, hf]
  -- ## the `θ`-integration at a fixed `z`
  have hslice : ∀ z ∈ Work.Spaces.Iz,
      |∫ θ in Work.Spaces.Iθ,
          ρ z θ * Work.Spaces.mixed b a u z θ * Work.Spaces.mixed b a f z θ|
        ≤ ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 u z θ)
            + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ)) / 2 := by
    intro z hz
    have hmaj : Integrable (fun θ => (Work.Spaces.HkIntegrand α 6 u z θ
        + Work.Spaces.HkIntegrand α 6 f z θ) / 2) (volume.restrict Work.Spaces.Iθ) :=
      ((mu.1 z hz).add (mf.1 z hz)).div_const 2
    have hnn : 0 ≤ᵐ[volume.restrict Work.Spaces.Iθ] fun θ =>
        (Work.Spaces.HkIntegrand α 6 u z θ + Work.Spaces.HkIntegrand α 6 f z θ) / 2 :=
      Filter.Eventually.of_forall fun θ => div_nonneg (add_nonneg
        (Work.Spaces.HkIntegrand_nonneg α 6 u z θ)
        (Work.Spaces.HkIntegrand_nonneg α 6 f z θ)) (by norm_num)
    calc |∫ θ in Work.Spaces.Iθ,
            ρ z θ * Work.Spaces.mixed b a u z θ * Work.Spaces.mixed b a f z θ|
        ≤ ∫ θ in Work.Spaces.Iθ,
            |ρ z θ * Work.Spaces.mixed b a u z θ * Work.Spaces.mixed b a f z θ| :=
          MeasureTheory.abs_integral_le_integral_abs
      _ ≤ ∫ θ in Work.Spaces.Iθ, (Work.Spaces.HkIntegrand α 6 u z θ
            + Work.Spaces.HkIntegrand α 6 f z θ) / 2 :=
          Work.Spaces.integral_le_integral_of_ae_le_of_nonneg hmaj hnn (hpt z hz)
      _ = ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 u z θ)
            + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ)) / 2 := by
          rw [MeasureTheory.integral_div,
            MeasureTheory.integral_add (mu.1 z hz) (mf.1 z hz)]
  -- ## the `z`-integration
  have hmajz : Integrable (fun z => ((∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 6 u z θ)
      + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ)) / 2)
      (volume.restrict Work.Spaces.Iz) := (mu.2.add mf.2).div_const 2
  have hnnz : 0 ≤ᵐ[volume.restrict Work.Spaces.Iz] fun z =>
      ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 u z θ)
        + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ)) / 2 :=
    Filter.Eventually.of_forall fun z => div_nonneg (add_nonneg
      (integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 6 u z θ)
      (integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 6 f z θ)) (by norm_num)
  have hmain : |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        ρ z θ * Work.Spaces.mixed b a u z θ * Work.Spaces.mixed b a f z θ|
      ≤ (Work.Spaces.HkSq α 6 u + Work.Spaces.HkSq α 6 f) / 2 := by
    calc |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          ρ z θ * Work.Spaces.mixed b a u z θ * Work.Spaces.mixed b a f z θ|
        ≤ ∫ z in Work.Spaces.Iz, |∫ θ in Work.Spaces.Iθ,
            ρ z θ * Work.Spaces.mixed b a u z θ * Work.Spaces.mixed b a f z θ| :=
          MeasureTheory.abs_integral_le_integral_abs
      _ ≤ ∫ z in Work.Spaces.Iz, ((∫ θ in Work.Spaces.Iθ,
              Work.Spaces.HkIntegrand α 6 u z θ)
            + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ)) / 2 :=
          Work.Spaces.integral_le_integral_of_ae_le_of_nonneg hmajz hnnz
            (MeasureTheory.ae_restrict_of_forall_mem
              (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici)
              fun z hz => hslice z hz)
      _ = (Work.Spaces.HkSq α 6 u + Work.Spaces.HkSq α 6 f) / 2 := by
          rw [MeasureTheory.integral_div, MeasureTheory.integral_add mu.2 mf.2]
          rfl
  rw [Work.FTS.TransportS.slotPairing]
  exact hmain

end Work.FTS.StrongPersist.H6Pair6Aux
