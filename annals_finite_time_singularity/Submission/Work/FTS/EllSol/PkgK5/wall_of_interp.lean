import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Tactic.Have
import Submission.Work.FTS.EllSol.PkgK5.WallDefs
import Submission.Work.FTS.EllSol.PkgK5.HkMem_Dz_pth_of_diag
import Submission.Work.Blocks.StripMajorantAux.mixIntS_dzIter_integrable
import Submission.Work.EllipticEst.Core.HkSqLHS_le_summands_v2
import Submission.Work.EllipticEst.Core.mixedFamily_le
import Submission.Work.EllipticEst.Core.i0Aux.Basic
import Submission.Work.FTS.EllipticEst.HkNorm_const_mul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The wall: `α D_z∂_θV ∈ ℋ^k` from the `i = 0` family of the interpolation estimate

This module proves `Work.FTS.EllSol.PkgK5.wall_of_interp`: **conditional on the `i = 0` family
`InterpFam k` of the paper's §7 mixed-derivative interpolation** (`Submission/Work/FTS/EllSol/
PkgK5/i0Family_le_openTrace.lean`, whose statement is recorded as the `abbrev` `InterpFam` in
`WallDefs.lean`), the open-class `ℋ^k`-estimate for the mixed radial-angular derivative holds:

  `HkMem α k (D_z∂_θV)  ∧  α |D_z∂_θV|_{ℋ^k} ≤ C (α² |D_z²V|_{ℋ^k} + |∂_θ²V|_{ℋ^k}
      + α |D_zV|_{ℋ^k})`.

The assembly is a verbatim adaptation of the *strip*-class proof
`Work.Blocks.alphaDz_pth_core_strip`, with two changes forced by the open-class setting:

* the strip interpolation `ADZW.i0Family_le_strip` is replaced by the hypothesis `InterpFam k`
  (same statement, open class, with the `D_z^jV`-traces at the two angular endpoints);
* the fourth membership `HkMem α k (D_z∂_θV)` — which the strip statement takes as a hypothesis,
  and which is what makes the majorant of the interpolation family integrable — is here
  *derived* from `HkMem α k (D_z∂_θ²V)` by the angular Hardy descent
  `Work.FTS.EllSol.PkgK5.HkMem_Dz_pth_of_diag`, and then used both for the majorant integrability
  (`Work.Blocks.StripMajorantAux.mixIntS_dzIter_integrable`) and as the first conjunct of the
  conclusion.

Everything else is the proven decomposition of `HkSq α k (α · D_z∂_θV)` into the two families
(`Work.EllipticEst.Core.HkSqLHS_le_summands_v2`), the mixed-family bound
(`Work.EllipticEst.Core.mixedFamily_le`), the scalar homogeneity of the norm
(`Work.FTS.EllipticEst.HkNorm_const_mul`) and the square-root arithmetic.
-/

namespace Work.FTS.EllSol.PkgK5

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 3200000

/-! ## Elementary facts -/

/-- `√(a+b) ≤ √a + √b` for `a, b ≥ 0`. -/
private theorem sqrt_add_le_aux {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  have h0 : 0 ≤ Real.sqrt a + Real.sqrt b := by positivity
  have hle : a + b ≤ (Real.sqrt a + Real.sqrt b) ^ 2 := by
    nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb, Real.sqrt_nonneg a, Real.sqrt_nonneg b]
  calc Real.sqrt (a + b) ≤ Real.sqrt ((Real.sqrt a + Real.sqrt b) ^ 2) := Real.sqrt_le_sqrt hle
    _ = Real.sqrt a + Real.sqrt b := Real.sqrt_sq h0

/-! ## Integrability of the majorant of the interpolation estimate -/

/-- **Integrability of a mixed-family summand** (`Work.EllipticEst.Core.mixedIntS_integrableOn`,
inlined here so that this module's import cone stays free of `sorry`): for `1 ≤ i`, `i+j ≤ k`
the slice functional `mixedIntS α i j V` is integrable in `z`.

The proof is the domination of `mixedIntS_le_slice` by the `θ`-integral of
`HkIntegrand α k (∂_θ²V)` (integrable in `z` by `HkMem α k (∂_θ²V)`) together with the
a.e. measurability of the slice functional as a function of `z`. -/
private theorem mixedIntS_integrable_aux {k : ℕ} {α : ℝ} {V : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hV : Work.FTS.EllipticEst.SmoothOpen V)
    (hmem : Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 V))
    {i j : ℕ} (hi : 1 ≤ i) (hij : i + j ≤ k) :
    MeasureTheory.IntegrableOn (fun z : ℝ => Work.EllipticEst.Core.mixedIntS α i j V z)
      Work.Spaces.Iz := by
  obtain ⟨K, hKpos, hK⟩ := Work.FTS.EllipticEst.sd_lop_iter_sin_bound k
  have hV' : ContDiffOn ℝ ∞ (Function.uncurry V) Work.EllipticEst.Core.sliceU := hV
  set Cc : ℝ := ((i : ℝ) * 4 ^ (i - 1) * K ^ 2) * ((i : ℝ) + 1) with hCc
  have hCcnn : 0 ≤ Cc := by rw [hCc]; positivity
  -- the pointwise (in `z`) bound
  have hle : ∀ z ∈ Work.Spaces.Iz,
      Work.EllipticEst.Core.mixedIntS α i j V z ≤ Cc * (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k (Work.Spaces.pthIter 2 V) z θ) := by
    intro z hz
    rw [hCc]
    exact Work.EllipticEst.Core.mixedIntS_le_slice hKpos.le hK hα hα1 hV' hmem hi hij z hz
  -- measurability
  have haesm : AEStronglyMeasurable (fun z : ℝ => Work.EllipticEst.Core.mixedIntS α i j V z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have h := Work.EllipticEst.Core.v2_aesm_integral ((hV.pth).mixed (j + 1) i)
      (-(Work.Spaces.gam α))
    simpa only [Work.EllipticEst.Core.mixedIntS, Work.FTS.EllipticEst.thGam]
      using h.aestronglyMeasurable
  -- the domination by an integrable function
  have hmono : MeasureTheory.IntegrableOn (fun z : ℝ => Cc * (∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k (Work.Spaces.pthIter 2 V) z θ)) Work.Spaces.Iz :=
    hmem.2.const_mul Cc
  refine MeasureTheory.Integrable.mono' hmono haesm ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
  have hnn : 0 ≤ Work.EllipticEst.Core.mixedIntS α i j V z := by
    rw [Work.EllipticEst.Core.mixedIntS]
    exact mul_nonneg (sq_nonneg _) (MeasureTheory.integral_nonneg_of_ae
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
        (fun θ hθ => mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thGam_nonneg hθ))))
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  exact hle z hz

/-- **Integrability of the majorant of the interpolation estimate.**

For `0 < α ≤ 1/4` and `V` smooth on the open quadrant with the four memberships
`D_zV, D_z²V, ∂_θ²V, D_z∂_θV ∈ ℋ^k`, the function

`z ↦ α² Σ_{r≤k} mixIntS (D_z^rV) z + α² Σ_{1≤i, i+j≤k} mixedIntS α i j V z`

is integrable on `[0,∞)`.

This is `Work.Blocks.alphaDz_pth_core_strip`'s private `majorant_integrable_strip_aux` with the
public (and open-class) radial integrability `StripMajorantAux.mixIntS_dzIter_integrable`; the
mixed family is `Work.EllipticEst.Core.mixedIntS_integrableOn`. -/
private theorem majorant_integrable_open (k : ℕ) :
    ∀ (α : ℝ) (V : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.SmoothOpen V →
      (∀ z : ℝ, V z 0 = 0) → (∀ z : ℝ, V z (Real.pi / 2) = 0) →
      Work.Spaces.HkMem α k (Work.Spaces.Dz V) →
      Work.Spaces.HkMem α k (Work.Spaces.DzIter 2 V) →
      Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 V) →
      Work.Spaces.HkMem α k (Work.Spaces.Dz (Work.Spaces.pth V)) →
      MeasureTheory.IntegrableOn (fun z : ℝ =>
          α ^ 2 * (∑ r ∈ Finset.range (k + 1),
              Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z)
          + α ^ 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
              if 1 ≤ i ∧ i + j ≤ k then
                Work.EllipticEst.Core.mixedIntS α i j V z
              else 0)) Work.Spaces.Iz := by
  intro α V hα hα4 hV h0 hpi hmd hmdd hmtt hmix
  have hα1 : α ≤ 1 := by linarith
  -- the radial family
  have hA : MeasureTheory.IntegrableOn (fun z : ℝ => ∑ r ∈ Finset.range (k + 1),
      Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z) Work.Spaces.Iz := by
    refine MeasureTheory.integrable_finsetSum _ (fun r hr => ?_)
    exact Work.Blocks.StripMajorantAux.mixIntS_dzIter_integrable hV hmix
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hr))
  -- the mixed family
  have hB : MeasureTheory.IntegrableOn (fun z : ℝ => ∑ i ∈ Finset.range (k + 1),
      ∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k then Work.EllipticEst.Core.mixedIntS α i j V z else 0))
      Work.Spaces.Iz := by
    refine MeasureTheory.integrable_finsetSum _ (fun i hi => ?_)
    refine MeasureTheory.integrable_finsetSum _ (fun j hj => ?_)
    by_cases hc : 1 ≤ i ∧ i + j ≤ k
    · simp only [if_pos hc]
      exact mixedIntS_integrable_aux hα hα1 hV hmtt hc.1 hc.2
    · simp only [if_neg hc]
      exact MeasureTheory.integrableOn_zero
  have h1 : MeasureTheory.IntegrableOn (fun z : ℝ => α ^ 2 *
      (∑ r ∈ Finset.range (k + 1), Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z))
      Work.Spaces.Iz :=
    MeasureTheory.Integrable.const_mul hA _
  have h2 : MeasureTheory.IntegrableOn (fun z : ℝ => α ^ 2 *
      (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k then Work.EllipticEst.Core.mixedIntS α i j V z else 0)))
      Work.Spaces.Iz :=
    MeasureTheory.Integrable.const_mul hB _
  refine (h1.add h2).congr_fun ?_ measurableSet_Ici
  intro z _
  simp only [Pi.add_apply]

/-! ## The wall -/

theorem wall_of_interp (k : ℕ) (hk : 2 ≤ k) (hI : InterpFam k) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (V : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.SmoothOpen V →
      (∀ z : ℝ, V z 0 = 0) → (∀ z : ℝ, V z (Real.pi / 2) = 0) →
      (∀ j : ℕ, j ≤ k + 1 → ∀ z : ℝ, 0 < z →
        Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j V z θ)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
        Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j V z θ)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) →
      Work.Spaces.HkMem α k (Work.Spaces.Dz V) →
      Work.Spaces.HkMem α k (Work.Spaces.DzIter 2 V) →
      Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 V) →
      Work.Spaces.HkMem α k (Work.Spaces.Dz (Work.Spaces.pthIter 2 V)) →
      Work.Spaces.HkMem α k (Work.Spaces.Dz (Work.Spaces.pth V)) ∧
      α * Work.Spaces.HkNorm α k (Work.Spaces.Dz (Work.Spaces.pth V))
        ≤ C * (α ^ 2 * Work.Spaces.HkNorm α k (Work.Spaces.DzIter 2 V)
            + Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 V)
            + α * Work.Spaces.HkNorm α k (Work.Spaces.Dz V)) := by
  obtain ⟨C2, hC2pos, h2⟩ := hI
  obtain ⟨C1, hC1pos, h1⟩ := Work.EllipticEst.Core.HkSqLHS_le_summands_v2 k
  obtain ⟨C3, hC3pos, h3⟩ := Work.EllipticEst.Core.mixedFamily_le k
  refine ⟨Real.sqrt (C1 * (C2 + C3) + C2), Real.sqrt_pos.mpr (by positivity), ?_⟩
  intro α V hα hα4 hV h0 hpi htr hmd hmdd hmtt hmix
  have hk1 : 1 ≤ k := by omega
  -- the missing membership, by the angular Hardy descent from `D_z∂_θ²V`
  have hmixpth : Work.Spaces.HkMem α k (Work.Spaces.Dz (Work.Spaces.pth V)) :=
    Work.FTS.EllSol.PkgK5.HkMem_Dz_pth_of_diag k hk1 α V hα hα4 hV h0 hpi htr hmix
  refine ⟨hmixpth, ?_⟩
  -- the two families of the decomposition and the right-hand side
  set A : ℝ := ∑ r ∈ Finset.range (k + 1),
      ∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z with hAdef
  set B : ℝ := ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
      if 1 ≤ i ∧ i + j ≤ k then
        ∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixedIntS α i j V z else 0 with hBdef
  set R : ℝ := α ^ 4 * Work.Spaces.HkSq α k (Work.Spaces.DzIter 2 V)
      + Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 V)
      + α ^ 2 * Work.Spaces.HkSq α k (Work.Spaces.Dz V) with hRdef
  have hR0 : 0 ≤ R := by
    rw [hRdef]
    have hdd := Work.Spaces.HkSq_nonneg α k (Work.Spaces.DzIter 2 V)
    have htt := Work.Spaces.HkSq_nonneg α k (Work.Spaces.pthIter 2 V)
    have hd := Work.Spaces.HkSq_nonneg α k (Work.Spaces.Dz V)
    have hα4' : 0 ≤ α ^ 4 := by positivity
    have hα2' : 0 ≤ α ^ 2 := by positivity
    linarith [mul_nonneg hα4' hdd, mul_nonneg hα2' hd]
  -- the `i = 0` family: this is the hypothesis `InterpFam k`
  have h2' : α ^ 2 * A ≤ C2 * R := by
    rw [hAdef, hRdef]
    exact h2 α V hα hα4 hV h0 hpi htr hmdd hmtt hmd
  -- the mixed (`D_θ`) family
  have h3' : α ^ 2 * B ≤ C3 * R := by
    rw [hBdef, hRdef]
    exact h3 α V hα hα4 hV h0 hpi hmdd hmtt hmd
  -- the decomposition of the left-hand side
  have key : Work.Spaces.HkSq α k (fun z θ => α * Work.Spaces.Dz (Work.Spaces.pth V) z θ)
      ≤ (C1 * (C2 + C3) + C2) * R := by
    have hmaj := majorant_integrable_open k α V hα hα4 hV h0 hpi hmd hmdd hmtt hmixpth
    have hSq1 : Work.Spaces.HkSq α k (fun z θ => α * Work.Spaces.Dz (Work.Spaces.pth V) z θ)
        ≤ C1 * (α ^ 2 * A + α ^ 2 * B) := by
      rw [hAdef, hBdef]
      exact h1 α V hα hV hmaj
    have hsum : α ^ 2 * A + α ^ 2 * B ≤ (C2 + C3) * R := by linarith [h2', h3']
    calc Work.Spaces.HkSq α k (fun z θ => α * Work.Spaces.Dz (Work.Spaces.pth V) z θ)
        ≤ C1 * (α ^ 2 * A + α ^ 2 * B) := hSq1
      _ ≤ C1 * ((C2 + C3) * R) := mul_le_mul_of_nonneg_left hsum hC1pos.le
      _ ≤ (C1 * (C2 + C3) + C2) * R := by
          calc C1 * ((C2 + C3) * R) = (C1 * (C2 + C3)) * R := by ring
            _ ≤ (C1 * (C2 + C3) + C2) * R :=
                mul_le_mul_of_nonneg_right (by linarith [hC2pos.le]) hR0
  -- the square-root step
  have hDpos : 0 ≤ C1 * (C2 + C3) + C2 := by
    linarith [hC2pos.le, mul_nonneg hC1pos.le (add_nonneg hC2pos.le hC3pos.le)]
  have hNorm : Work.Spaces.HkNorm α k (fun z θ => α * Work.Spaces.Dz (Work.Spaces.pth V) z θ)
      ≤ Real.sqrt (C1 * (C2 + C3) + C2) * Real.sqrt R := by
    rw [Work.Spaces.HkNorm]
    calc Real.sqrt (Work.Spaces.HkSq α k _)
        ≤ Real.sqrt ((C1 * (C2 + C3) + C2) * R) := Real.sqrt_le_sqrt key
      _ = Real.sqrt (C1 * (C2 + C3) + C2) * Real.sqrt R := Real.sqrt_mul hDpos R
  have h1' : Real.sqrt (α ^ 4 * Work.Spaces.HkSq α k (Work.Spaces.DzIter 2 V))
      = α ^ 2 * Work.Spaces.HkNorm α k (Work.Spaces.DzIter 2 V) := by
    rw [Work.Spaces.HkNorm]
    rw [show α ^ 4 * Work.Spaces.HkSq α k (Work.Spaces.DzIter 2 V)
        = (α ^ 2) ^ 2 * Work.Spaces.HkSq α k (Work.Spaces.DzIter 2 V) by ring]
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  have h3'' : Real.sqrt (α ^ 2 * Work.Spaces.HkSq α k (Work.Spaces.Dz V))
      = α * Work.Spaces.HkNorm α k (Work.Spaces.Dz V) := by
    rw [Work.Spaces.HkNorm]
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hα.le]
  have hsqrtR : Real.sqrt R
      ≤ α ^ 2 * Work.Spaces.HkNorm α k (Work.Spaces.DzIter 2 V)
        + Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 V)
        + α * Work.Spaces.HkNorm α k (Work.Spaces.Dz V) := by
    have hb1 : 0 ≤ α ^ 4 * Work.Spaces.HkSq α k (Work.Spaces.DzIter 2 V) :=
      mul_nonneg (by positivity) (Work.Spaces.HkSq_nonneg α k (Work.Spaces.DzIter 2 V))
    have hb2 : 0 ≤ Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 V) :=
      Work.Spaces.HkSq_nonneg α k (Work.Spaces.pthIter 2 V)
    have hb3 : 0 ≤ α ^ 2 * Work.Spaces.HkSq α k (Work.Spaces.Dz V) :=
      mul_nonneg (by positivity) (Work.Spaces.HkSq_nonneg α k (Work.Spaces.Dz V))
    have hs2 : Real.sqrt (α ^ 4 * Work.Spaces.HkSq α k (Work.Spaces.DzIter 2 V)
          + Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 V)
          + α ^ 2 * Work.Spaces.HkSq α k (Work.Spaces.Dz V))
        ≤ Real.sqrt (α ^ 4 * Work.Spaces.HkSq α k (Work.Spaces.DzIter 2 V)
            + Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 V))
          + Real.sqrt (α ^ 2 * Work.Spaces.HkSq α k (Work.Spaces.Dz V)) :=
      sqrt_add_le_aux (add_nonneg hb1 hb2) hb3
    have hs1 : Real.sqrt (α ^ 4 * Work.Spaces.HkSq α k (Work.Spaces.DzIter 2 V)
          + Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 V))
        ≤ Real.sqrt (α ^ 4 * Work.Spaces.HkSq α k (Work.Spaces.DzIter 2 V))
          + Real.sqrt (Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 V)) :=
      sqrt_add_le_aux hb1 hb2
    rw [hRdef]
    calc Real.sqrt (α ^ 4 * Work.Spaces.HkSq α k (Work.Spaces.DzIter 2 V)
            + Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 V)
            + α ^ 2 * Work.Spaces.HkSq α k (Work.Spaces.Dz V))
        ≤ Real.sqrt (α ^ 4 * Work.Spaces.HkSq α k (Work.Spaces.DzIter 2 V)
            + Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 V))
          + Real.sqrt (α ^ 2 * Work.Spaces.HkSq α k (Work.Spaces.Dz V)) := hs2
      _ ≤ (Real.sqrt (α ^ 4 * Work.Spaces.HkSq α k (Work.Spaces.DzIter 2 V))
            + Real.sqrt (Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 V)))
          + Real.sqrt (α ^ 2 * Work.Spaces.HkSq α k (Work.Spaces.Dz V)) := by linarith [hs1]
      _ = α ^ 2 * Work.Spaces.HkNorm α k (Work.Spaces.DzIter 2 V)
          + Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 V)
          + α * Work.Spaces.HkNorm α k (Work.Spaces.Dz V) := by
        rw [h1', h3'']
        simp only [Work.Spaces.HkNorm]
  -- the left-hand side, as a scalar multiple
  have hsmul : Work.Spaces.HkNorm α k (fun z θ => α * Work.Spaces.Dz (Work.Spaces.pth V) z θ)
      = α * Work.Spaces.HkNorm α k (Work.Spaces.Dz (Work.Spaces.pth V)) := by
    rw [Work.FTS.EllipticEst.HkNorm_const_mul α k α (f := Work.Spaces.Dz (Work.Spaces.pth V))
      (fun n => (hV.pth).Dz.forall n)]
    rw [abs_of_pos hα]
  rw [← hsmul]
  calc Work.Spaces.HkNorm α k (fun z θ => α * Work.Spaces.Dz (Work.Spaces.pth V) z θ)
      ≤ Real.sqrt (C1 * (C2 + C3) + C2) * Real.sqrt R := hNorm
    _ ≤ Real.sqrt (C1 * (C2 + C3) + C2) *
          (α ^ 2 * Work.Spaces.HkNorm α k (Work.Spaces.DzIter 2 V)
          + Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 V)
          + α * Work.Spaces.HkNorm α k (Work.Spaces.Dz V)) :=
        mul_le_mul_of_nonneg_left hsqrtR (Real.sqrt_nonneg _)

end

end Work.FTS.EllSol.PkgK5
