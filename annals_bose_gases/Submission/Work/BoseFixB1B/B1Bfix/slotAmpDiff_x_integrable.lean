import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB1B.B1Bfix.Basic
import Submission.Work.BoseFixB1B.B1Bfix.FibreAlg
import Submission.Work.BoseFixB1B.cutFibreMass_facts
import Submission.Work.BoseFixB1B.fibreSideConditions_cut
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1B.B1Bfix

noncomputable section

open MeasureTheory Filter
open scoped Topology Real BigOperators ENNReal

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## The windowed amplitude: measurability and a uniform bound

The slot amplitude of `Defs.slotAmpF` is the windowed exponential amplitude
`tBamp χ p Φ i x = ∫_z χ(z)e^{−i⟪p,z⟫}Φ(x_{i←z})dz` of the mean-free projection `Φ = Q_{B,i}v`.
For the two states of the sharp-fibre program (`v = cutProd (γ δ) ψ`, `v = sharpBoxState B ψ`)
the projection `Q_{B,i}v` is measurable (`Work.BoseFixB1B.measurable_boxQ`) and bounded on the
ambient box (`boxQ_le_bound_of_bdd` below), which is all that is needed to make the *square* of
the amplitude integrable over the box: the box has finite measure, and the amplitude is dominated
by the window mass times the pointwise bound.

The two ingredients are

* `tBamp_stronglyMeasurable` — the parametric Bochner integral of the jointly strongly
  measurable integrand `(x,z) ↦ χ(z)e^{−i⟪p,z⟫}Φ(x_{i←z})`
  (`MeasureTheory.StronglyMeasurable.integral_prod_right'`);
* `tBamp_norm_le` — the pointwise bound `‖tBamp χ p Φ i x‖ ≤ Cχ·M·|tsupport χ|` on the box,
  obtained from the set-integral bound `‖∫_{z∈tsupport χ}…‖ ≤ C·|tsupport χ|`
  (`MeasureTheory.norm_setIntegral_le_of_norm_le_const`), the window being compactly supported
  inside the cube so that its (topological) support has finite measure. -/

/-- Replacing one coordinate of a point of the ambient box by a point of a set `A ⊆ acube a`
keeps the configuration in the ambient box. -/
theorem update_mem_abox {N : ℕ} {a : ℝ} {A : Set E3} (hAsub : A ⊆ Submission.BoseGases.acube a)
    {x : Submission.BoseGases.X N} (hx : x ∈ Submission.BoseGases.abox N a) {z : E3} (hz : z ∈ A)
    (i : Fin N) : Function.update x i z ∈ Submission.BoseGases.abox N a := by
  rw [Submission.BoseGases.mem_abox_iff] at hx ⊢
  intro j
  by_cases hj : j = i
  · subst hj; rw [Function.update_self]; exact hAsub hz
  · rw [Function.update_of_ne hj]; exact hx j

/-- **Strong measurability of the windowed amplitude.**  For a continuous window `χ` and a
measurable state `Φ`, the amplitude `x ↦ tBamp χ p Φ i x` is the parametric Bochner integral of
the jointly strongly measurable integrand `(x,z) ↦ χ(z)e^{−i⟪p,z⟫}Φ(x_{i←z})`, hence strongly
measurable in `x` (`StronglyMeasurable.integral_prod_right'`). -/
theorem tBamp_stronglyMeasurable {N : ℕ} {χ : E3 → ℝ} (hχc : Continuous χ)
    (Φ : Submission.BoseGases.X N → ℝ) (hΦm : Measurable Φ) (i : Fin N) (p : E3) :
    StronglyMeasurable (fun x : Submission.BoseGases.X N =>
      Work.SmallBoxTBWord.tBamp χ p Φ i x) := by
  have hχ2 : Continuous (fun q : Submission.BoseGases.X N × E3 => χ q.2) :=
    hχc.comp continuous_snd
  have h1 : StronglyMeasurable (fun q : Submission.BoseGases.X N × E3 => (χ q.2 : ℂ)) :=
    (Complex.continuous_ofReal.comp hχ2).stronglyMeasurable
  have h2 : StronglyMeasurable (fun q : Submission.BoseGases.X N × E3 =>
      Complex.exp (-(Complex.I * (inner ℝ p q.2 : ℂ)))) := by
    have hc : Continuous (fun q : Submission.BoseGases.X N × E3 =>
        Complex.exp (-(Complex.I * (inner ℝ p q.2 : ℂ)))) := by
      have hinner : Continuous fun q : Submission.BoseGases.X N × E3 => inner ℝ p q.2 :=
        continuous_const.inner continuous_snd
      fun_prop
    exact hc.stronglyMeasurable
  have h3 : StronglyMeasurable (fun q : Submission.BoseGases.X N × E3 =>
      (Φ (Function.update q.1 i q.2) : ℂ)) :=
    Complex.continuous_ofReal.comp_stronglyMeasurable
      (hΦm.stronglyMeasurable.comp_measurable (by fun_prop))
  have hAll : StronglyMeasurable (fun q : Submission.BoseGases.X N × E3 =>
      (χ q.2 : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p q.2 : ℂ))) *
        (Φ (Function.update q.1 i q.2) : ℂ)) := (h1.mul h2).mul h3
  have hint := hAll.integral_prod_right' (ν := (volume : Measure E3))
  simpa only [Work.SmallBoxTBWord.tBamp] using hint

/-- **The uniform norm bound on the windowed amplitude.**  If the window `χ` is bounded by `Cχ`
on its (topological) support, if that support lies in the cube `acube a`, and if `Φ` is bounded by
`M` on the ambient box `abox N a`, then the amplitude of `Φ` at any box configuration is bounded
by `Cχ·M·|tsupport χ|`. -/
theorem tBamp_norm_le {N : ℕ} {a : ℝ} (ha : 0 < a) {χ : E3 → ℝ}
    {Φ : Submission.BoseGases.X N → ℝ} {Cχ M : ℝ} (hCχ : 0 ≤ Cχ)
    (hχb : ∀ z ∈ tsupport χ, |χ z| ≤ Cχ)
    (hχsub : tsupport χ ⊆ Submission.BoseGases.acube a)
    (hΦb : ∀ y ∈ Submission.BoseGases.abox N a, |Φ y| ≤ M)
    (i : Fin N) (p : E3) {x : Submission.BoseGases.X N}
    (hx : x ∈ Submission.BoseGases.abox N a) :
    ‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ≤ Cχ * M * (volume.real (tsupport χ)) := by
  have hfin : (volume : Measure E3) (tsupport χ) < ⊤ :=
    lt_of_le_of_lt (measure_mono hχsub) (Submission.BoseGases.acube_lt_top a ha.le)
  rw [Work.SmallBoxTBWord.tBamp_eq_setIntegral_tsupport]
  refine norm_setIntegral_le_of_norm_le_const (μ := (volume : Measure E3)) hfin ?_
  intro z hz
  have hexp : ‖Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))‖ = 1 := by
    rw [Complex.norm_exp]; simp
  have hΦz : |Φ (Function.update x i z)| ≤ M :=
    hΦb _ (update_mem_abox hχsub hx hz i)
  calc ‖(χ z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
        (Φ (Function.update x i z) : ℂ)‖
      = |χ z| * |Φ (Function.update x i z)| := by
        rw [norm_mul, norm_mul, hexp, mul_one]
        simp
    _ ≤ Cχ * M := mul_le_mul (hχb z hz) hΦz (abs_nonneg _) hCχ

/-- **The existence form of the amplitude bound.**  A continuous compactly supported window `χ`
with support in the cube, and a state `Φ` bounded by `C` on the box, give a constant bound on the
amplitude over the box. -/
theorem tBamp_bound {N : ℕ} {a : ℝ} (ha : 0 < a) {χ : E3 → ℝ} (hχc : Continuous χ)
    (hcs : HasCompactSupport χ) (hχsub : tsupport χ ⊆ Submission.BoseGases.acube a)
    (Φ : Submission.BoseGases.X N → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hΦb : ∀ y ∈ Submission.BoseGases.abox N a, |Φ y| ≤ C) (i : Fin N) (p : E3) :
    ∃ K, 0 ≤ K ∧ ∀ x ∈ Submission.BoseGases.abox N a,
      ‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ≤ K := by
  obtain ⟨Cχ, hCχ⟩ := hcs.isCompact.exists_bound_of_continuousOn hχc.continuousOn
  refine ⟨max Cχ 0 * C * (volume.real (tsupport χ)),
    mul_nonneg (mul_nonneg (le_max_right _ _) hC) measureReal_nonneg, fun x hx => ?_⟩
  refine tBamp_norm_le ha (le_max_right _ _) (fun z hz => ?_) hχsub hΦb i p hx
  exact le_trans (by simpa [Real.norm_eq_abs] using hCχ z hz) (le_max_left _ _)

/-- **Boundedness of the box mean-free projection.**  `boxQ volA A i v = v − boxP volA A i v`,
where the box mean is `(1/volA)∫_{z∈A} v(x_{i←z})dz`; for `A ⊆ acube a` and `|v| ≤ C` on the
ambient box, the mean is bounded by `|1/volA|·|C|·|A|` (`A` has finite measure since it sits in
the cube), so `boxQ` is bounded by `C + |1/volA|·|C|·|A|`. -/
theorem boxQ_le_bound_of_bdd {N : ℕ} {a : ℝ} (ha : 0 < a) {A : Set E3}
    (hAsub : A ⊆ Submission.BoseGases.acube a) {volA : ℝ} (i : Fin N)
    {v : Submission.BoseGases.X N → ℝ} {C : ℝ}
    (hvb : ∀ x ∈ Submission.BoseGases.abox N a, |v x| ≤ C) :
    ∀ x ∈ Submission.BoseGases.abox N a,
      |Work.SmallBoxTBWord.boxQ volA A i v x| ≤ C + |1 / volA| * (|C| * volume.real A) := by
  intro x hx
  have hfin : (volume : Measure E3) A < ⊤ :=
    lt_of_le_of_lt (measure_mono hAsub) (Submission.BoseGases.acube_lt_top a ha.le)
  have hint : ‖∫ z in A, v (Function.update x i z)‖ ≤ |C| * volume.real A := by
    refine norm_setIntegral_le_of_norm_le_const (μ := (volume : Measure E3)) hfin ?_
    intro z hz
    rw [Real.norm_eq_abs]
    exact le_trans (hvb _ (update_mem_abox hAsub hx hz i)) (le_abs_self C)
  have hP : |Work.SmallBoxTBWord.boxP volA A i v x| ≤ |1 / volA| * (|C| * volume.real A) := by
    rw [Work.SmallBoxTBWord.boxP, abs_mul]
    exact mul_le_mul_of_nonneg_left hint (abs_nonneg _)
  calc |Work.SmallBoxTBWord.boxQ volA A i v x|
        = |v x - Work.SmallBoxTBWord.boxP volA A i v x| := rfl
    _ ≤ |v x| + |Work.SmallBoxTBWord.boxP volA A i v x| := abs_sub _ _
    _ ≤ C + |1 / volA| * (|C| * volume.real A) :=
        add_le_add (hvb x hx) hP

/-- **The amplitude of a state is bounded on the box.**  Combining the bound on the mean-free
projection with the window bound. -/
theorem amp_bound {n : ℕ} {a : ℝ} (ha : 0 < a) {A : Set E3}
    (hAsub : A ⊆ Submission.BoseGases.acube a) {volA : ℝ} {χ : E3 → ℝ} (hχc : Continuous χ)
    (hcs : HasCompactSupport χ) (hχsub : tsupport χ ⊆ Submission.BoseGases.acube a)
    {v : Submission.BoseGases.X (n+1) → ℝ} (hvm : Measurable v) {C : ℝ} (hC : 0 ≤ C)
    (hvb : ∀ x ∈ Submission.BoseGases.abox (n+1) a, |v x| ≤ C) (i : Fin (n+1)) (p : E3) :
    ∃ K, 0 ≤ K ∧ ∀ x ∈ Submission.BoseGases.abox (n+1) a,
      ‖slotAmpF a A volA χ i v p x‖ ≤ K := by
  have hMnn : (0:ℝ) ≤ C + |1 / volA| * (|C| * volume.real A) :=
    add_nonneg hC (mul_nonneg (abs_nonneg _) (mul_nonneg (abs_nonneg _) measureReal_nonneg))
  have hb := tBamp_bound (N := n+1)
    (C := C + |1 / volA| * (|C| * volume.real A)) ha hχc hcs hχsub
    (Work.SmallBoxTBWord.boxQ volA A i v) hMnn
    (boxQ_le_bound_of_bdd (N := n+1) ha hAsub i hvb) i p
  simpa only [slotAmpF] using hb

/-! ## The target -/

/-- **The `x`-integrability of the squared amplitude difference of the approximant and the sharp
state.**

`x ↦ ‖slotAmpF L (dlBox L d u) (boxMass L d u) (chiB L d u) i (cutProd (γ δ) ψ) p x
− slotAmpF L (dlBox L d u) (boxMass L d u) (chiB L d u) i (sharpBoxState (dlBox L d u) ψ) p x‖²`
is integrable over the ambient box, for every `δ > 0`, slot `i` and frequency `p`.  This is the
last `x`-level input of the assembly of `Work.BoseFixB1B.tendsto_tBdiagFormInd_cut`: it lets the
slot-energy comparison `slotY_diff_le` (in `Submission/Work/BoseFixB1B/B1Bfix/_asm.lean`) be
applied to the pair `(Ψ_δ, Ψ₀) = (cutProd (γ δ) ψ, sharpBoxState (dlBox L d u) ψ)`.

Intended route (the same as the sibling `Work.BoseFixB1B.slotAmp_x_integrable`, which should be
importable or reproducible): the map `(p,x) ↦ slotAmpF … p x` is jointly measurable for a
measurable state `v` (the amplitude is a parametric `z`-integral of a jointly measurable integrand
over the compactly supported window — `StronglyMeasurable.integral_prod_right'`), both
`v = cutProd (γ δ) ψ` (smooth) and `v = sharpBoxState (dlBox L d u) ψ` (indicator of the
measurable set `dlBox` times the smooth `ψ`) are measurable, so the difference is measurable in
`x`; each of the two amplitudes is pointwise bounded on the box (`boxQ = id − boxP`, the box mean
controlled by `hψb` and `volA ≥ 0`), and the box has finite measure, so
`MeasureTheory.Integrable.of_bound` closes. -/
theorem slotAmpDiff_x_integrable {n : ℕ} {L d : ℝ} (hL : 0 < L) (hd : 0 < d)
    (u : EuclideanSpace ℝ (Fin 3)) {ψ : Submission.BoseGases.X (n+1) → ℝ}
    (hψ : ContDiff ℝ (⊤ : ENat) ψ)
    {Cb : ℝ} (hCb : 0 ≤ Cb)
    (hψb : ∀ x ∈ Submission.BoseGases.abox (n+1) L, |ψ x| ≤ Cb)
    {K : ℝ} {γ : ℝ → EuclideanSpace ℝ (Fin 3) → ℝ} (hcut : Work.BoseFixB1B.IsCutFamily L d u K γ) :
    ∀ (δ : ℝ), 0 < δ → ∀ (i : Fin (n+1)) (p : EuclideanSpace ℝ (Fin 3)),
      MeasureTheory.Integrable (fun x : Submission.BoseGases.X (n+1) =>
        ‖Work.BoseFixB1B.slotAmpF L (Submission.BoseGases.dlBox L d u)
            (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiB L d u) i
            (Work.BoseFixB1B.cutProd (γ δ) ψ) p x
          - Work.BoseFixB1B.slotAmpF L (Submission.BoseGases.dlBox L d u)
            (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiB L d u) i
            (Work.BoseFixB1B.sharpBoxState (Submission.BoseGases.dlBox L d u) ψ) p x‖ ^ 2)
        (MeasureTheory.volume.restrict (Submission.BoseGases.abox (n+1) L)) := by
  intro δ hδ i p
  -- the geometric data of the sliding box
  have hAc : Submission.BoseGases.dlBox L d u ⊆ Submission.BoseGases.acube L :=
    Work.SmallBoxSliding.dlBox_subset_acube L d u
  have hχc : Continuous (Submission.BoseGases.chiB L d u) :=
    (Work.SmallBoxTBWord.contDiff_chiB hL hd u).continuous
  have hcs : HasCompactSupport (Submission.BoseGases.chiB L d u) :=
    Work.SmallBoxTBWord.hasCompactSupport_chiB hL hd u
  have hχsub : tsupport (Submission.BoseGases.chiB L d u) ⊆ Submission.BoseGases.acube L :=
    Work.SmallBoxTBWord.tsupport_chiB_subset_acube hL hd u
  -- the two states and their mean-free projections
  obtain ⟨hcd, -, h01, -, -⟩ := hcut.2 δ hδ
  have hv1m : Measurable (Work.BoseFixB1B.cutProd (γ δ) ψ) :=
    Work.BoseFixB1B.cutFibre_measurable_cutProd hcd.continuous hψ.continuous
  have hv1b : ∀ x ∈ Submission.BoseGases.abox (n+1) L,
      |Work.BoseFixB1B.cutProd (γ δ) ψ x| ≤ Cb :=
    Work.BoseFixB1B.abs_cutProd_le h01 hψb
  have hv0m : Measurable
      (Work.BoseFixB1B.sharpBoxState (Submission.BoseGases.dlBox L d u) ψ) :=
    Work.BoseFixB1B.sharpBoxState_measurable
      (Work.SmallBoxSliding.measurableSet_dlBox L d u) hψ.continuous.measurable
  have hv0b : ∀ x ∈ Submission.BoseGases.abox (n+1) L,
      |Work.BoseFixB1B.sharpBoxState (Submission.BoseGases.dlBox L d u) ψ x| ≤ Cb :=
    Work.BoseFixB1B.abs_sharpBoxState_le hCb hψb
  -- the pointwise bounds of the two amplitudes on the box
  obtain ⟨K1, hK1nn, hK1⟩ := amp_bound hL hAc hχc hcs hχsub hv1m hCb hv1b i p
  obtain ⟨K0, hK0nn, hK0⟩ := amp_bound hL hAc hχc hcs hχsub hv0m hCb hv0b i p
  -- strong measurability of the two amplitudes
  have hm1 : StronglyMeasurable (fun x : Submission.BoseGases.X (n+1) =>
      Work.BoseFixB1B.slotAmpF L (Submission.BoseGases.dlBox L d u)
        (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiB L d u) i
        (Work.BoseFixB1B.cutProd (γ δ) ψ) p x) := by
    simpa only [slotAmpF] using
      tBamp_stronglyMeasurable hχc (Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
        (Submission.BoseGases.dlBox L d u) i (Work.BoseFixB1B.cutProd (γ δ) ψ))
        (Work.BoseFixB1B.measurable_boxQ (Work.SmallBoxSliding.boxMass L d u) i hv1m) i p
  have hm0 : StronglyMeasurable (fun x : Submission.BoseGases.X (n+1) =>
      Work.BoseFixB1B.slotAmpF L (Submission.BoseGases.dlBox L d u)
        (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiB L d u) i
        (Work.BoseFixB1B.sharpBoxState (Submission.BoseGases.dlBox L d u) ψ) p x) := by
    simpa only [slotAmpF] using
      tBamp_stronglyMeasurable hχc (Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass L d u)
        (Submission.BoseGases.dlBox L d u) i
        (Work.BoseFixB1B.sharpBoxState (Submission.BoseGases.dlBox L d u) ψ))
        (Work.BoseFixB1B.measurable_boxQ (Work.SmallBoxSliding.boxMass L d u) i hv0m) i p
  -- the box has finite measure
  haveI : IsFiniteMeasure ((volume : Measure (Submission.BoseGases.X (n+1))).restrict
      (Submission.BoseGases.abox (n+1) L)) :=
    MeasureTheory.isFiniteMeasure_restrict.mpr
      (ne_of_lt (Submission.BoseGases.abox_lt_top (n+1) L hL.le))
  refine MeasureTheory.Integrable.of_bound ((hm1.sub hm0).norm.pow 2).aestronglyMeasurable
    ((K1 + K0) ^ 2) ?_
  rw [MeasureTheory.ae_restrict_iff' (Submission.BoseGases.abox_measurable (n+1) L)]
  refine Filter.Eventually.of_forall (fun x hx => ?_)
  have hsub : ‖Work.BoseFixB1B.slotAmpF L (Submission.BoseGases.dlBox L d u)
        (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiB L d u) i
        (Work.BoseFixB1B.cutProd (γ δ) ψ) p x
      - Work.BoseFixB1B.slotAmpF L (Submission.BoseGases.dlBox L d u)
        (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiB L d u) i
        (Work.BoseFixB1B.sharpBoxState (Submission.BoseGases.dlBox L d u) ψ) p x‖
      ≤ K1 + K0 :=
    le_trans (norm_sub_le _ _) (add_le_add (hK1 x hx) (hK0 x hx))
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) hsub 2

end

end Work.BoseFixB1B.B1Bfix
