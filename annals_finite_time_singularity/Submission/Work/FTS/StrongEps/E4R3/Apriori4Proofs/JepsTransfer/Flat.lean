import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Defs
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.LogInt
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.leaf_pairIntegral_le_HkSq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `JepsTransfer/Flat.lean` — the flat (`wip`) form of the slot pairings

`Work.Coercivity.wip ρ A B = ∫_z ∫_θ A z θ * B z θ * ρ z θ` is the flat pairing out of which
`H1IP` is built, while `Work.FTS.TransportS.slotPairing ρ a b u v` is the `ρ · D_z^bD_θ^a u ·
D_z^bD_θ^a v` slot pairing.  Here we record

* `wip_eq_flat` — the same integral with the weight in front (the form in which the transfer
  estimate is stated);
* `slotPairing_eq_wip` — the slot pairing is the flat pairing of the two slots;
* `sqrt_wip_self_le_HkNorm` — the diagonal of a leaf pairing is bounded by the `ℋ¹`-norm
  (`JepsTransfer.leaf_pairIntegral_le_HkSq`);
* `lintegral_leaf_le_HkSq` — the corresponding `∫⁻`-bound, which gives the log-side
  integrability;
* `logW_nonneg_of_leaf` — nonnegativity of the log weight of a leaf.
-/

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.JT

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- For `volume.restrict Iθ` the two endpoints `0`, `π/2` are null. -/
private theorem ae_mem_Ioo_Iθ :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo (0 : ℝ) (π / 2) := by
  have h : volume.restrict Work.Spaces.Iθ = volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) :=
    Measure.restrict_congr_set (MeasureTheory.Ioo_ae_eq_Icc (μ := volume)).symm
  rw [h]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioo

/-- The flat pairing, with the weight put in front. -/
theorem wip_eq_flat (ρ A B : ℝ → ℝ → ℝ) :
    Work.Coercivity.wip ρ A B
      = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, ρ z θ * A z θ * B z θ := by
  rw [Work.Coercivity.wip]
  refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun z => ?_)
  refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun θ => ?_)
  ring

/-- The slot pairing of a weight at the slot `(a,b)` is the flat pairing of the two slots. -/
theorem slotPairing_eq_wip (ρ : ℝ → ℝ → ℝ) (a b : ℕ) (X Y : Fn) :
    Work.FTS.TransportS.slotPairing ρ a b X Y
      = Work.Coercivity.wip ρ (Work.Spaces.mixed b a X) (Work.Spaces.mixed b a Y) := by
  rw [wip_eq_flat]
  rfl

/-- The diagonal of a leaf pairing is dominated by the squared `ℋ¹`-norm. -/
theorem sqrt_wip_self_le_HkNorm {α : ℝ} (hα : 0 < α) {u : Fn}
    (hmem : Work.Spaces.HkMem α 1 u) {a b : ℕ} (hab : a + b ≤ 1)
    {ρ : ℝ → ℝ → ℝ} (hρ : Work.FTS.TransportS.IsLeafW α a ρ) :
    Real.sqrt (Work.Coercivity.wip ρ (Work.Spaces.mixed b a u) (Work.Spaces.mixed b a u))
      ≤ Work.Spaces.HkNorm α 1 u := by
  have h := Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.leaf_pairIntegral_le_HkSq
    hα hmem hab hρ
  have h' : Work.FTS.TransportS.slotPairing ρ a b u u ≤ Work.Spaces.HkSq α 1 u := by
    rw [Work.FTS.TransportS.slotPairing]
    have heq : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          ρ z θ * Work.Spaces.mixed b a u z θ * Work.Spaces.mixed b a u z θ)
        = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            ρ z θ * (Work.Spaces.mixed b a u z θ) ^ 2 := by
      refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun z => ?_)
      refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun θ => ?_)
      ring
    rw [heq]
    exact h
  have he : Work.Coercivity.wip ρ (Work.Spaces.mixed b a u) (Work.Spaces.mixed b a u)
      = Work.FTS.TransportS.slotPairing ρ a b u u :=
    (slotPairing_eq_wip ρ a b u u).symm
  rw [Work.Spaces.HkNorm, he]
  exact Real.sqrt_le_sqrt h'

/-- **The `∫⁻`-domination of a leaf pairing at level one.** -/
theorem lintegral_leaf_le_HkSq {α : ℝ} (hα : 0 < α) {u : Fn}
    (hmem : Work.Spaces.HkMem α 1 u) {a b : ℕ} (hab : a + b ≤ 1)
    {ρ : ℝ → ℝ → ℝ} (hρ : Work.FTS.TransportS.IsLeafW α a ρ) :
    (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (ρ z θ * (Work.Spaces.mixed b a u z θ) ^ 2))
      ≤ ENNReal.ofReal (Work.Spaces.HkSq α 1 u) := by
  have hHk : ENNReal.ofReal (Work.Spaces.HkSq α 1 u)
      = ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α 1 u z θ) := by
    rw [Work.Spaces.HkSq]
    rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hmem.2
      (Eventually.of_forall fun z =>
        MeasureTheory.integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 1 u z θ)]
    refine MeasureTheory.setLIntegral_congr_fun measurableSet_Ici (fun z hz => ?_)
    exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hmem.1 z hz)
      (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 1 u z θ)
  rw [hHk]
  refine MeasureTheory.lintegral_mono_ae ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
  refine MeasureTheory.lintegral_mono_ae ?_
  filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
  exact ENNReal.ofReal_le_ofReal
    (Work.FTS.StrongPersist.H6Pair6Aux.domLeaf_all hα hρ (f := u) hθ hab)

/-- The log weight of a leaf is nonnegative. -/
theorem logW_nonneg_of_leaf {α : ℝ} {a : ℕ} {w : ℝ → ℝ → ℝ}
    (hw : Work.FTS.TransportS.IsLeafW α a w) :
    ∀ y : ℝ × ℝ, 0 ≤ Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y := by
  intro y
  rw [Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW_apply]
  refine mul_nonneg (Work.FTS.StrongEps.HkSqAux.logJac_nonneg y.1 y.2) ?_
  exact Work.FTS.StrongPersist.H6Pair6Aux.leaf_nonneg hw (Real.exp y.1)
    ⟨le_of_lt (Real.arctan_pos.mpr (Real.exp_pos y.2)),
      le_of_lt (Real.arctan_lt_pi_div_two _)⟩

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.JT
