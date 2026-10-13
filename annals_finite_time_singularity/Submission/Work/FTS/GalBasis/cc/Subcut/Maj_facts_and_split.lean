import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.GalBasis.cc.Subcut.MajDefs
import Submission.Work.FTS.GalBasis.cc.Subcut.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.Galerkin.Defs
import Submission.Work.FTS.GalBasis.cc.SlotDefs
import Submission.Work.FTS.StrongLWP.Xn6Limit.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.GalBasis.cc.Subcut.Maj_aesm
import Submission.Work.FTS.GalBasis.cc.Subcut.Maj_slice_integrable
import Submission.Work.FTS.GalBasis.cc.Subcut.Maj_integral_integrable

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.GalBasis.cc.Subcut

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- **The analytic facts about the majorant `Maj` and the identification of its iterated integral.**

`Maj α C κN N f z θ = C · (1_{UN N}(z,θ) · HkIntegrand α 4 f z θ + 1_{LN N}(θ) · ∑_{b<4} (zslotW α b f z θ)²)`
is the localised majorant of the pointwise product bound for `χ_N f = f - ψ N · f`
(`Subcut.HkIntegrand_sub_psiCut_le_sharp`); here `zslotW α b f z θ = DzIter b f z θ * Wt α z θ`.

The four bundled properties are exactly what is needed to apply the transfer lemma
`Subcut.HkSq_le_of_ae_dominated` to `Maj` and to compute the resulting integral.

1. `AEStronglyMeasurable` of the uncurried majorant for `(volume.restrict Iz).prod (volume.restrict Iθ)`:
   the pieces are the indicator of the measurable set `UN N`, `HkIntegrand` (continuous on the open
   quadrant, `Work.Spaces.aesm_of_continuousOn_Qd`), `LN N`'s indicator pulled back along `Prod.snd`,
   and the squares of `DzIter b f · Wt α` (continuous on the open quadrant; `Wt` continuity from
   `Work.FTS.StrongLWP.Xn6Limit.continuousOn_Wt_Qd`), for `b < 4`.
2. `θ ↦ Maj … z θ` is integrable for a.e. `z`: dominated by `C (1 + κN) HkIntegrand α 4 f z ·` via
   `hcap`, which is integrable for a.e. `z` by `hmem`; the a.e. strong measurability of the slices comes
   from `Work.Spaces.aesm_slice_of_continuousOn_Qd`.
3. `z ↦ ∫_θ Maj … z θ` is integrable, by the same domination and `hmem.2`, with a.e. strong
   measurability from `MeasureTheory.AEStronglyMeasurable.integral_prod_right`.
4. The iterated integral splits (move the indicator inside the sum with `Finset.mul_sum`, then the
   finite-sum integral identity `MeasureTheory.integral_finsetSum`); this is in fact an equality, and
   the stated `≤` makes the Bochner junk values harmless. -/
theorem Maj_facts_and_split {α : ℝ} {f : Work.FTS.Galerkin.Fn}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    {C κN : ℝ} (N : ℕ) (hN : 1 ≤ N) (hC : 0 < C)
    (hcap : ∀ z θ : ℝ, 0 < z → θ ∈ Work.Spaces.Iθ →
      Work.FTS.GalBasis.cc.Maj α C κN N f z θ
        ≤ C * (1 + κN) * Work.Spaces.HkIntegrand α 4 f z θ) :
    MeasureTheory.AEStronglyMeasurable
        (Function.uncurry (Work.FTS.GalBasis.cc.Maj α C κN N f))
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
    (∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
        MeasureTheory.IntegrableOn
          (fun θ => Work.FTS.GalBasis.cc.Maj α C κN N f z θ) Work.Spaces.Iθ) ∧
    MeasureTheory.Integrable
        (fun z => ∫ θ in Work.Spaces.Iθ, Work.FTS.GalBasis.cc.Maj α C κN N f z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) ∧
    (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        Work.FTS.GalBasis.cc.Maj α C κN N f z θ)
      ≤ C * ((∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
                Work.Spaces.HkIntegrand α 4 f z θ *
                  (Work.FTS.GalBasis.cc.UN N).indicator (fun _ => (1 : ℝ)) (z, θ))
            + ∑ b ∈ Finset.range 4, ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
                (Work.FTS.GalBasis.cc.LN N).indicator (fun _ => (1 : ℝ)) θ *
                  (Work.Spaces.DzIter b f z θ * Work.Spaces.Wt α z θ) ^ 2) := by
  set AU : ℝ → ℝ → ℝ := fun z θ => Work.Spaces.HkIntegrand α 4 f z θ
      * (Work.FTS.GalBasis.cc.UN N).indicator (fun _ => (1 : ℝ)) (z, θ) with hAU
  set BL : ℕ → ℝ → ℝ → ℝ := fun b z θ =>
      (Work.FTS.GalBasis.cc.LN N).indicator (fun _ => (1 : ℝ)) θ
        * (Work.Spaces.DzIter b f z θ * Work.Spaces.Wt α z θ) ^ 2 with hBL
  set BS : ℝ → ℝ → ℝ := fun z θ => ∑ b ∈ Finset.range 4, BL b z θ with hBS
  set GG : ℝ → ℝ → ℝ := fun z θ => AU z θ + BS z θ with hGG
  have hAaesm := Maj_aesm (α := α) hsm C κN N
  have hAslice := Maj_slice_integrable (α := α) hsm hmem N hC hcap
  have hAmarg := Maj_integral_integrable (α := α) hsm hmem N hC hAaesm.1 hcap
  -- nonnegativity of the pieces
  have hAUnn : ∀ z θ, 0 ≤ AU z θ := by
    intro z θ
    simp only [hAU]
    exact mul_nonneg (Work.Spaces.HkIntegrand_nonneg α 4 f z θ)
      (Set.indicator_nonneg (fun _ _ => zero_le_one) (z, θ))
  have hBLnn : ∀ b z θ, 0 ≤ BL b z θ := by
    intro b z θ
    simp only [hBL]
    exact mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) θ) (sq_nonneg _)
  -- the pointwise identity relating `Maj` to the pieces
  have hMajGG : ∀ z θ, Work.FTS.GalBasis.cc.Maj α C κN N f z θ = C * GG z θ := by
    intro z θ
    rw [Work.FTS.GalBasis.cc.Maj_eq_sum_form]
    simp only [hGG, hBS, hBL, Work.FTS.GalBasis.cc.zslotW]
    ring
  -- `0 < z` a.e.
  have hzpos : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), 0 < z := by
    have hset : Set.Ioi (0 : ℝ) =ᵐ[MeasureTheory.volume] Work.Spaces.Iz :=
      MeasureTheory.Ioi_ae_eq_Ici
    rw [← MeasureTheory.Measure.restrict_congr_set hset]
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
    exact Filter.Eventually.of_forall fun z hz => hz
  -- slice integrability of `GG`
  have hsliceGG : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.IntegrableOn (fun θ => GG z θ) Work.Spaces.Iθ := by
    filter_upwards [hAslice] with z hz
    refine (hz.const_mul C⁻¹).congr (Filter.Eventually.of_forall fun θ => ?_)
    show C⁻¹ * Work.FTS.GalBasis.cc.Maj α C κN N f z θ = GG z θ
    rw [hMajGG z θ, ← mul_assoc, inv_mul_cancel₀ hC.ne', one_mul]
  -- slice integrability of `AU`
  have hsliceAU : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.IntegrableOn (fun θ => AU z θ) Work.Spaces.Iθ := by
    filter_upwards [hzpos, hsliceGG] with z hz hzG
    refine MeasureTheory.Integrable.mono' hzG ?_ ?_
    · simpa only [hAU] using hAaesm.2.2.2.1 z hz
    · filter_upwards with θ
      simp only [hGG, hBS, Real.norm_eq_abs, abs_of_nonneg (hAUnn z θ)]
      exact le_add_of_nonneg_right (Finset.sum_nonneg fun b hb => hBLnn b z θ)
  -- slice integrability of the `BL b`
  have hsliceBL : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      ∀ b ∈ Finset.range 4, MeasureTheory.IntegrableOn (fun θ => BL b z θ) Work.Spaces.Iθ := by
    filter_upwards [hzpos, hsliceGG] with z hz hzG
    intro b hb
    refine MeasureTheory.Integrable.mono' hzG ?_ ?_
    · simpa only [hBL] using hAaesm.2.2.2.2 z hz b
    · filter_upwards with θ
      simp only [hGG, hBS, Real.norm_eq_abs, abs_of_nonneg (hBLnn b z θ)]
      have h1 : BL b z θ ≤ ∑ i ∈ Finset.range 4, BL i z θ :=
        Finset.single_le_sum (fun i _ => hBLnn i z θ) hb
      have h2 : (0 : ℝ) ≤ AU z θ := hAUnn z θ
      linarith
  -- a.e. strong measurability of the marginals
  have ha_aesm : MeasureTheory.AEStronglyMeasurable
      (fun z => ∫ θ in Work.Spaces.Iθ, AU z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have h := (hAaesm.2.1).integral_prod_right'
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
    simpa only [hAU, Function.uncurry] using h
  have hv_aesm : ∀ b : ℕ, MeasureTheory.AEStronglyMeasurable
      (fun z => ∫ θ in Work.Spaces.Iθ, BL b z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    intro b
    have h := (hAaesm.2.2.1 b).integral_prod_right'
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
    simpa only [hBL, Function.uncurry] using h
  -- integrability of the marginal of `GG`
  have hCGG : MeasureTheory.Integrable
      (fun z => C * (∫ θ in Work.Spaces.Iθ, GG z θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    refine hAmarg.congr (Filter.Eventually.of_forall fun z => ?_)
    show (∫ θ in Work.Spaces.Iθ, Work.FTS.GalBasis.cc.Maj α C κN N f z θ)
        = C * (∫ θ in Work.Spaces.Iθ, GG z θ)
    simp only [hMajGG]
    exact MeasureTheory.integral_const_mul C (fun θ => GG z θ)
  have hcint : MeasureTheory.Integrable
      (fun z => ∫ θ in Work.Spaces.Iθ, GG z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    refine (hCGG.const_mul C⁻¹).congr (Filter.Eventually.of_forall fun z => ?_)
    show C⁻¹ * (C * (∫ θ in Work.Spaces.Iθ, GG z θ))
        = ∫ θ in Work.Spaces.Iθ, GG z θ
    rw [← mul_assoc, inv_mul_cancel₀ hC.ne', one_mul]
  -- integrability of the marginal of `AU`
  have haint : MeasureTheory.Integrable
      (fun z => ∫ θ in Work.Spaces.Iθ, AU z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    refine MeasureTheory.Integrable.mono' hcint ha_aesm ?_
    filter_upwards [hsliceGG] with z hzG
    have hle : (∫ θ in Work.Spaces.Iθ, AU z θ) ≤ ∫ θ in Work.Spaces.Iθ, GG z θ :=
      MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall fun θ => hAUnn z θ) hzG
        (Filter.Eventually.of_forall fun θ => by
          simp only [hGG, hBS]
          exact le_add_of_nonneg_right (Finset.sum_nonneg fun b hb => hBLnn b z θ))
    rw [Real.norm_eq_abs,
      abs_of_nonneg (MeasureTheory.integral_nonneg fun θ => hAUnn z θ)]
    exact hle
  -- integrability of the marginal of each `BL b`
  have hvint : ∀ b ∈ Finset.range 4, MeasureTheory.Integrable
      (fun z => ∫ θ in Work.Spaces.Iθ, BL b z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    intro b hb
    refine MeasureTheory.Integrable.mono' hcint (hv_aesm b) ?_
    filter_upwards [hsliceGG] with z hzG
    have hle : (∫ θ in Work.Spaces.Iθ, BL b z θ) ≤ ∫ θ in Work.Spaces.Iθ, GG z θ :=
      MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall fun θ => hBLnn b z θ) hzG
        (Filter.Eventually.of_forall fun θ => by
          simp only [hGG, hBS]
          have h1 : BL b z θ ≤ ∑ i ∈ Finset.range 4, BL i z θ :=
            Finset.single_le_sum (fun i _ => hBLnn i z θ) hb
          have h2 : (0 : ℝ) ≤ AU z θ := hAUnn z θ
          linarith)
    rw [Real.norm_eq_abs,
      abs_of_nonneg (MeasureTheory.integral_nonneg fun θ => hBLnn b z θ)]
    exact hle
  have hsumint : MeasureTheory.Integrable
      (fun z => ∑ b ∈ Finset.range 4, ∫ θ in Work.Spaces.Iθ, BL b z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    MeasureTheory.integrable_finsetSum' _ (fun b hb => hvint b hb)
  -- the `θ`-level identity
  have hGG_sum : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (∫ θ in Work.Spaces.Iθ, GG z θ)
        = (∫ θ in Work.Spaces.Iθ, AU z θ)
          + ∑ b ∈ Finset.range 4, ∫ θ in Work.Spaces.Iθ, BL b z θ := by
    filter_upwards [hsliceAU, hsliceBL] with z hzA hzBL
    have hzSum : MeasureTheory.Integrable
        (fun θ => ∑ b ∈ Finset.range 4, BL b z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      MeasureTheory.integrable_finsetSum' _ (fun b hb => hzBL b hb)
    calc (∫ θ in Work.Spaces.Iθ, GG z θ)
        = ∫ θ in Work.Spaces.Iθ, (AU z θ + ∑ b ∈ Finset.range 4, BL b z θ) := by
          refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
          simp only [hGG, hBS]
      _ = (∫ θ in Work.Spaces.Iθ, AU z θ)
            + ∫ θ in Work.Spaces.Iθ, (∑ b ∈ Finset.range 4, BL b z θ) :=
          MeasureTheory.integral_add hzA hzSum
      _ = (∫ θ in Work.Spaces.Iθ, AU z θ)
            + ∑ b ∈ Finset.range 4, ∫ θ in Work.Spaces.Iθ, BL b z θ := by
          rw [MeasureTheory.integral_finsetSum (f := fun b θ => BL b z θ) (Finset.range 4)
            (fun b hb => hzBL b hb)]
  have hX1 : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, GG z θ)
      = ∫ z in Work.Spaces.Iz, ((∫ θ in Work.Spaces.Iθ, AU z θ)
          + ∑ b ∈ Finset.range 4, ∫ θ in Work.Spaces.Iθ, BL b z θ) :=
    MeasureTheory.integral_congr_ae hGG_sum
  have hX2 : (∫ z in Work.Spaces.Iz, ((∫ θ in Work.Spaces.Iθ, AU z θ)
        + ∑ b ∈ Finset.range 4, ∫ θ in Work.Spaces.Iθ, BL b z θ))
      = (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, AU z θ)
        + ∫ z in Work.Spaces.Iz, (∑ b ∈ Finset.range 4,
            ∫ θ in Work.Spaces.Iθ, BL b z θ) :=
    MeasureTheory.integral_add haint hsumint
  have hX : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, GG z θ)
      = (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, AU z θ)
        + ∑ b ∈ Finset.range 4, ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, BL b z θ := by
    rw [hX1, hX2, MeasureTheory.integral_finsetSum (Finset.range 4)
      (f := fun b z => ∫ θ in Work.Spaces.Iθ, BL b z θ) (fun b hb => hvint b hb)]
  -- relate the iterated integral of `Maj` to that of `GG`
  have hmajGGint : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        Work.FTS.GalBasis.cc.Maj α C κN N f z θ)
      = C * (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, GG z θ) := by
    calc (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            Work.FTS.GalBasis.cc.Maj α C κN N f z θ)
        = ∫ z in Work.Spaces.Iz, C * (∫ θ in Work.Spaces.Iθ, GG z θ) := by
          refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
          show (∫ θ in Work.Spaces.Iθ, Work.FTS.GalBasis.cc.Maj α C κN N f z θ)
              = C * (∫ θ in Work.Spaces.Iθ, GG z θ)
          simp only [hMajGG]
          exact MeasureTheory.integral_const_mul C (fun θ => GG z θ)
      _ = C * (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, GG z θ) :=
          MeasureTheory.integral_const_mul C _
  have hfin : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        Work.FTS.GalBasis.cc.Maj α C κN N f z θ)
      = C * ((∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
                Work.Spaces.HkIntegrand α 4 f z θ *
                  (Work.FTS.GalBasis.cc.UN N).indicator (fun _ => (1 : ℝ)) (z, θ))
            + ∑ b ∈ Finset.range 4, ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
                (Work.FTS.GalBasis.cc.LN N).indicator (fun _ => (1 : ℝ)) θ *
                  (Work.Spaces.DzIter b f z θ * Work.Spaces.Wt α z θ) ^ 2) := by
    rw [hmajGGint, hX]
  exact ⟨hAaesm.1, hAslice, hAmarg, le_of_eq hfin⟩

end Work.FTS.GalBasis.cc.Subcut
