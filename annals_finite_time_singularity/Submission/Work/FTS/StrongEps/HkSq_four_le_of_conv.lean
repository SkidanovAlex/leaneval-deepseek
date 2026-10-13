/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Work.FTS.StrongEps.HkSq_four_le_of_conv` — lower semicontinuity of the `ℋ⁴`-energy

The level-`4` energy `HkSq α 4` is *lower semicontinuous* along a `ConvLocUnifH6`-convergent
sequence: if every slot `D_z^jD_θ^i` (`i + j ≤ 4`) of a sequence of profiles `G n` converges to
that of `f` locally uniformly on the open quadrant, and each `G n` has `HkSq α 4 (G n) ≤ B4`, then
`HkSq α 4 f ≤ B4`.  This is the `ℋ⁴` analogue of `LocUnif.HkSq_le` (which does the level-`6`
energy, but with an a.e. level-`5` convergence hypothesis instead of the slotwise one), and it is
the brick that lets the `ℋ⁴`-bound of the `ε`-scheme pass to the limit family at each fake time.

## The proof

Everything is a double application of Fatou's lemma in `ℝ≥0∞`; no uniform per-slice bound on the
approximants is needed, because the *plain* Fatou lemma for the `lintegral` requires only
measurability.

* On the open quadrant `Q0 = (0,∞) × (0,π/2)` the slotwise local uniform convergence gives the
  pointwise convergence of every slot at every point (a singleton is compact), hence, through
  `HkIntegrand_tendsto_of_mixed`, that of the whole integrand `HkIntegrand α 4`.
* `HkIntegrand α k F` vanishes on the boundary `{z = 0} ∪ {θ = 0} ∪ {θ = π/2}` of `Iz ×ˢ Iθ`
  (both weights `w` and `w·sin(2θ)^{-γ/2}` degenerate there), so the pointwise comparison
  `HkIntegrand α 4 f ≤ liminf HkIntegrand α 4 (G n)` — an *equality* on `Q0` and a trivial one on
  the boundary — holds on all of `Iz ×ˢ Iθ`.
* `ofReal_le_liminf_ofReal` transfers this to `ℝ≥0∞`, and Fatou at the `θ`-slice
  (`lintegral_liminf_le'`) and then at the `z`-level gives
  `∫⁻_z ∫⁻_θ ofReal (HkIntegrand α 4 f) ≤ liminf_n ∫⁻_z ∫⁻_θ ofReal (HkIntegrand α 4 (G n))`.
* For each `n` the double `lintegral` of `ofReal ∘ HkIntegrand α 4 (G n)` is
  `ofReal (HkSq α 4 (G n))` (`ofReal_integral_eq_lintegral_ofReal` at both levels, using the
  `HkMem` of the approximants for the integrability), and `HkSq α 4 (G n) ≤ B4`; the `liminf` of
  a sequence bounded by `ofReal B4` is bounded by `ofReal B4`.
* Finally the Bochner integral defining `HkSq α 4 f` is compared with the double `lintegral`: if
  the `z`-integral is integrable this is `integral_eq_lintegral_of_nonneg_ae` together with the
  pointwise `ofReal (∫_θ g) ≤ ∫⁻_θ ofReal g` (which holds with equality when the slice is
  integrable and is `0 ≤ _` otherwise); if it is *not* integrable, then `HkSq α 4 f = 0`
  (`integral_undef`) and `0 ≤ B4` since `B4` dominates the nonnegative energies `HkSq α 4 (G n)`.

The file rests only on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongEps.ConvLev0Defs
import Submission.Work.FTS.StrongEps.HkMem_of_tendsto

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- **The `ℋ⁴`-energy of the limit is bounded by the uniform bound of the sequence.**  From the
slotwise locally uniform convergence of the `ConvLocUnifH6`-package (`Q0`-compactness, no bound on
the boundary behaviour of the approximants is needed), the `ℋ⁴`-membership and the uniform
`ℋ⁴`-bound of the sequence, the limit `f` satisfies `HkSq α 4 f ≤ B4`.

Proof: Fatou's lemma, twice (see the module documentation). -/
theorem HkSq_four_le_of_conv {α B B4 : ℝ} {G : ℕ → Work.FTS.Galerkin.Fn}
    {f : Work.FTS.Galerkin.Fn}
    (hconv : Work.FTS.StrongEps.ConvLocUnifH6 α B G f)
    (hmem : ∀ n : ℕ, Work.Spaces.HkMem α 4 (G n))
    (hbsq : ∀ n : ℕ, Work.Spaces.HkSq α 4 (G n) ≤ B4) :
    Work.Spaces.HkSq α 4 f ≤ B4 := by
  -- `B4` dominates the nonnegative energy `HkSq α 4 (G 0)`
  have hB4 : 0 ≤ B4 := le_trans (Work.Spaces.HkSq_nonneg α 4 (G 0)) (hbsq 0)
  -- the slotwise convergence is pointwise on the open quadrant: a singleton is compact
  have hslot : ∀ (j i : ℕ), j + i ≤ 4 → ∀ z θ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Tendsto (fun n : ℕ => Work.Spaces.mixed j i (G n) z θ) atTop
        (nhds (Work.Spaces.mixed j i f z θ)) := by
    intro j i hji z θ hzθ
    have hK : IsCompact ({(z, θ)} : Set (ℝ × ℝ)) := isCompact_singleton
    have hsub : ({(z, θ)} : Set (ℝ × ℝ)) ⊆ Work.FTS.EllipticEst.Q0 := by
      intro p hp
      rw [Set.mem_singleton_iff] at hp
      rw [hp]
      exact hzθ
    exact (hconv.1 _ hK hsub j i hji).tendsto_at (Set.mem_singleton _)
  -- **the angular Fatou step**: for every `z ∈ Iz` the `θ`-slice of the integrand of `f` is
  -- dominated in `lintegral` by the `liminf` of the slices of the approximants
  have hslice : ∀ z ∈ Work.Spaces.Iz,
      (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Work.Spaces.HkIntegrand α 4 f z θ))
        ≤ Filter.liminf (fun n : ℕ => ∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal (Work.Spaces.HkIntegrand α 4 (G n) z θ)) Filter.atTop := by
    intro z hz
    rcases lt_or_eq_of_le (show (0 : ℝ) ≤ z from hz) with hzpos | hz0
    · -- `z > 0`: the comparison holds for a.e. `θ`, and Fatou's lemma applies
      have hae : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
          ENNReal.ofReal (Work.Spaces.HkIntegrand α 4 f z θ)
            ≤ Filter.liminf (fun n : ℕ =>
                ENNReal.ofReal (Work.Spaces.HkIntegrand α 4 (G n) z θ)) Filter.atTop := by
        -- it suffices to test the open interval, the two endpoints being null
        have hμ : MeasureTheory.volume.restrict Work.Spaces.Iθ
            = MeasureTheory.volume.restrict (Set.Ioo 0 (π/2)) :=
          (MeasureTheory.Measure.restrict_congr_set
            (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
              (b := (π/2)))).symm
        rw [hμ]
        refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo fun θ hθ => ?_
        -- pointwise convergence of the integrands, hence `liminf = HkIntegrand α 4 f`
        have hlim : Filter.liminf (fun n : ℕ => Work.Spaces.HkIntegrand α 4 (G n) z θ)
            Filter.atTop = Work.Spaces.HkIntegrand α 4 f z θ :=
          (Work.FTS.StrongEps.HkIntegrand_tendsto_of_mixed (α := α) (k := 4) (F := f) (Fs := G)
            (z := z) (θ := θ) (fun j i hji => hslot j i hji z θ
              (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hzpos, hθ.1, hθ.2⟩))).liminf_eq
        exact Work.FTS.EllExist.Honesty.ofReal_le_liminf_ofReal
          (fun n => Work.Spaces.HkIntegrand_nonneg α 4 (G n) z θ) (le_of_eq hlim.symm)
      refine le_trans (MeasureTheory.lintegral_mono_ae hae) ?_
      exact MeasureTheory.lintegral_liminf_le'
        (fun n => (((hmem n).1 z hz).aemeasurable).ennreal_ofReal)
    · -- `z = 0` (or `z < 0`): both sides degenerate, the integrand vanishing at `z = 0`
      subst hz0
      have hzero : (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α 4 f 0 θ)) = 0 := by
        simp [Work.Spaces.HkIntegrand_zero_z]
      rw [hzero]
      exact zero_le
  -- **the outer Fatou step**
  have hstep1 : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α 4 f z θ))
      ≤ ∫⁻ z in Work.Spaces.Iz, Filter.liminf (fun n : ℕ => ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α 4 (G n) z θ)) Filter.atTop :=
    MeasureTheory.lintegral_mono_ae
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici hslice)
  have hstep2 : (∫⁻ z in Work.Spaces.Iz, Filter.liminf (fun n : ℕ => ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α 4 (G n) z θ)) Filter.atTop)
      ≤ Filter.liminf (fun n : ℕ => ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α 4 (G n) z θ)) Filter.atTop :=
    MeasureTheory.lintegral_liminf_le' (fun n => by
      -- the `z`-function `∫⁻_θ ofReal (HkIntegrand α 4 (G n) z θ)` is measurable, being the
      -- `ofReal`-image of the (integrable) angular integral of `HkIntegrand α 4 (G n)`
      have h1 : AEMeasurable (fun z => ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 4 (G n) z θ) (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
        ((hmem n).2).aemeasurable
      refine (h1.ennreal_ofReal).congr ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
      exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal ((hmem n).1 z hz)
        (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 4 (G n) z θ))
  -- the double `lintegral` of an approximant is `ofReal` of its energy
  have hEq : ∀ n : ℕ, (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α 4 (G n) z θ))
      = ENNReal.ofReal (Work.Spaces.HkSq α 4 (G n)) := by
    intro n
    have h1 : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α 4 (G n) z θ))
        = ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 4 (G n) z θ) := by
      refine MeasureTheory.lintegral_congr_ae ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
      exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal ((hmem n).1 z hz)
        (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 4 (G n) z θ)).symm
    rw [h1, Work.Spaces.HkSq]
    exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal ((hmem n).2)
      (Filter.Eventually.of_forall fun z => MeasureTheory.integral_nonneg fun θ =>
        Work.Spaces.HkIntegrand_nonneg α 4 (G n) z θ)).symm
  -- the `liminf` of a sequence bounded by `ofReal B4` is bounded by `ofReal B4`
  have hliminf_le : Filter.liminf (fun n : ℕ => ∫⁻ z in Work.Spaces.Iz,
        ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α 4 (G n) z θ)) Filter.atTop
      ≤ ENNReal.ofReal B4 := by
    refine Filter.liminf_le_of_le ⟨0, ?_⟩ ?_
    · rw [Filter.eventually_map]
      exact Filter.Eventually.of_forall fun n => zero_le
    · intro b hb
      obtain ⟨n, hn⟩ := hb.exists
      exact le_trans (hEq n ▸ hn) (ENNReal.ofReal_le_ofReal (hbsq n))
  have hmain : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
      ENNReal.ofReal (Work.Spaces.HkIntegrand α 4 f z θ)) ≤ ENNReal.ofReal B4 :=
    le_trans hstep1 (le_trans hstep2 hliminf_le)
  -- **comparison of the Bochner integral with the double `lintegral`**
  by_cases hint : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 4 f z θ) Work.Spaces.Iz
  · have h1 : Work.Spaces.HkSq α 4 f = (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)).toReal := by
      rw [Work.Spaces.HkSq]
      exact MeasureTheory.integral_eq_lintegral_of_nonneg_ae
        (Filter.Eventually.of_forall fun z => MeasureTheory.integral_nonneg fun θ =>
          Work.Spaces.HkIntegrand_nonneg α 4 f z θ) hint.aestronglyMeasurable
    have hpt : ∀ z : ℝ, ENNReal.ofReal (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 4 f z θ)
        ≤ ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Work.Spaces.HkIntegrand α 4 f z θ) := by
      intro z
      by_cases hz : IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 4 f z θ) Work.Spaces.Iθ
      · exact le_of_eq (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hz
          (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 4 f z θ))
      · rw [MeasureTheory.integral_undef hz]; simp
    rw [h1]
    calc (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal
            (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)).toReal
        ≤ (ENNReal.ofReal B4).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top
            ((MeasureTheory.lintegral_mono hpt).trans hmain)
      _ = B4 := ENNReal.toReal_ofReal hB4
  · -- the energy is the junk value `0`, and `B4` is nonnegative
    have h0 : Work.Spaces.HkSq α 4 f = 0 := by
      rw [Work.Spaces.HkSq]
      exact MeasureTheory.integral_undef hint
    rw [h0]
    exact hB4

end Work.FTS.StrongEps
