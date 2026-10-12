import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SmallBoxA0.abs_integral_mul_le_sqrt
import Submission.Work.SmallBoxA0.aesm_fibre_integral
import Submission.Work.SmallBoxA0.pair_const_fibre_data
import Submission.Work.SmallBoxA0.pair_pullback_integrable
import Submission.Work.SmallBoxA0.peel_fibre_sq
import Submission.Work.SmallBoxA0.sq_integral_mul_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SmallBoxA0

open MeasureTheory Metric
open scoped ContDiff Topology Real BigOperators
open Submission BoseGases
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- Per-pair Cauchy–Schwarz bound on a single `q4PairWord` summand.  For `i ≠ j`
in `Fin (p+2)`, the pairing integrand `(PᵢPⱼΦ)·(QⱼQᵢΦ)·w₁(xᵢ,xⱼ)` is bounded in
absolute value by `s⁻³·‖PᵢPⱼΦ‖₂·‖QⱼQᵢΦ‖₂·‖w₁‖₂`, where the `s⁻³` is exactly the
factor by which the two-slot peel dilates the `L²`-norm of a slot-constant
function (`∫_{abox (p+2) s} A² = s⁶·∫_{abox p s} (A∘rest2)²`).

Route: pick `j' : Fin (p+1)` with `i.succAbove j' = j`, peel with
`abox_integral_peel2`, use `aP_pair_fiber_const` to replace
`aP s i (aP s j Φ)` by its value on `rest2 i j' r2`; Cauchy–Schwarz (Hölder
`p = q = 2`, `integral_mul_norm_le_Lp_mul_Lq`) in `(y,z)` then in `r2`;
`prod_setIntegral_eq_iter2` identifies `∫_z∫_y (w1 (y,z))²` with
`∫ q in acube s ×ˢ acube s, (w1 q)²`; the peel identity
`∫_{abox (p+2) s} A² = s⁶·∫_{abox p s} (A∘rest2)²` (again `abox_integral_peel2`
plus `integral_const_acube`) supplies the `s⁻³`. -/
lemma pair_slot_cs_bound {p : ℕ} {s : ℝ} (hs : 0 < s)
    (i j : Fin (p + 2)) (hij : i ≠ j)
    {Φ : X (p + 2) → ℝ} (hΦc : Continuous Φ)
    {w1 : ℝ³ × ℝ³ → ℝ}
    (hw1m : AEStronglyMeasurable w1 (volume.restrict (acube s ×ˢ acube s)))
    (hw1sq : IntegrableOn (fun q : ℝ³ × ℝ³ => (w1 q) ^ 2) (acube s ×ˢ acube s) volume) :
    |∫ x in abox (p + 2) s,
        (aP s i (aP s j Φ) x) * (aQ s j (aQ s i Φ) x) * w1 (x i, x j)|
      ≤ (s ^ 3)⁻¹
          * Real.sqrt (∫ x in abox (p + 2) s, (aP s i (aP s j Φ) x) ^ 2)
          * Real.sqrt (∫ x in abox (p + 2) s, (aQ s j (aQ s i Φ) x) ^ 2)
          * Real.sqrt (∫ q in acube s ×ˢ acube s, (w1 q) ^ 2) := by
  classical
  rcases Fin.exists_succAbove_eq (x := j) (y := i) hij.symm with ⟨j', hj'⟩
  set A : X (p + 2) → ℝ := aP s i (aP s j Φ) with hAdef
  set B : X (p + 2) → ℝ := aQ s j (aQ s i Φ) with hBdef
  have hAj : Continuous (aP s j Φ) := aP_continuous hs j hΦc
  have hAcont : Continuous A := by rw [hAdef]; exact aP_continuous hs i hAj
  have hQcont : Continuous (fun x => aQ s i Φ x) := by
    unfold aQ; exact hΦc.sub (aP_continuous hs i hΦc)
  have hBcont : Continuous B := by
    rw [hBdef]; unfold aQ; exact hQcont.sub (aP_continuous hs j hQcont)
  have hAfib : ∀ (y z : ℝ³) (r2 : X p), A (ins2 i j' y z r2) = A (rest2 i j' r2) := by
    intro y z r2
    rw [hAdef]
    exact aP_pair_fiber_const hs i j hij j' hj' hΦc y z r2
  have hfin : IsFiniteMeasure (volume.restrict (acube s ×ˢ acube s)) := by
    constructor
    rw [Measure.restrict_apply_univ]
    rw [Measure.volume_eq_prod]
    rw [Measure.prod_prod (acube s) (acube s)]
    exact ENNReal.mul_lt_top (acube_lt_top s hs.le) (acube_lt_top s hs.le)
  haveI := hfin
  have hw1MemLp : MemLp w1 2 (volume.restrict (acube s ×ˢ acube s)) :=
    (memLp_two_iff_integrable_sq hw1m).mpr hw1sq
  have hw1L1 : IntegrableOn w1 (acube s ×ˢ acube s) volume := hw1MemLp.integrable (by norm_num)
  obtain ⟨hw1pull, -⟩ := pair_pullback_integrable (p := p) (s := s) hs i j hij hw1m hw1L1
  obtain ⟨C, hC⟩ := (abox_compact (p + 2) hs).exists_bound_of_continuousOn
    (f := fun x : X (p + 2) => A x * B x) (hAcont.mul hBcont).continuousOn
  have hFint : IntegrableOn (fun x : X (p + 2) => A x * B x * w1 (x i, x j))
      (abox (p + 2) s) volume := by
    refine MeasureTheory.Integrable.mono' (g := fun x : X (p + 2) => C * |w1 (x i, x j)|) ?_ ?_ ?_
    · exact (hw1pull.abs).const_mul C
    · exact (((hAcont.mul hBcont).measurable.aestronglyMeasurable).mul hw1pull.aestronglyMeasurable)
    · rw [MeasureTheory.ae_restrict_iff' (abox_measurable (p + 2) s)]
      filter_upwards with x hx
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      have h1 : |A x| * |B x| ≤ C := by
        have := hC x hx
        rwa [Real.norm_eq_abs, abs_mul] at this
      exact mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
  -- the fibre objects and their basic structure
  set A₂ : X p → ℝ := fun r2 => A (rest2 i j' r2) with hA₂def
  set β : X p → ℝ := fun r2 => ∫ q in acube s ×ˢ acube s, B (ins2 i j' q.1 q.2 r2) * w1 q with hβdef
  set γ : X p → ℝ := fun r2 => ∫ q in acube s ×ˢ acube s, (B (ins2 i j' q.1 q.2 r2)) ^ 2 with hγdef
  set W : ℝ := ∫ q in acube s ×ˢ acube s, (w1 q) ^ 2 with hWdef
  have hBc : ∀ r2 : X p, Continuous (fun q : ℝ³ × ℝ³ => B (ins2 i j' q.1 q.2 r2)) := by
    intro r2
    have h1 : Continuous (fun q : ℝ³ × ℝ³ => kcInsN p j' (q.2, r2)) :=
      (kcInsN_cont j').comp (continuous_snd.prodMk continuous_const)
    have h2 : Continuous (fun q : ℝ³ × ℝ³ => (q.1, kcInsN p j' (q.2, r2))) :=
      continuous_fst.prodMk h1
    exact hBcont.comp ((kcInsN_cont i).comp h2)
  have hKK : IsCompact (acube s ×ˢ acube s) := (acube_compact hs).prod (acube_compact hs)
  have hfib_int : ∀ r2 : X p,
      IntegrableOn (fun q : ℝ³ × ℝ³ => B (ins2 i j' q.1 q.2 r2) * w1 q)
        (acube s ×ˢ acube s) volume := by
    intro r2
    obtain ⟨CB, hCB⟩ := hKK.exists_bound_of_continuousOn
      (f := fun q : ℝ³ × ℝ³ => B (ins2 i j' q.1 q.2 r2)) (hBc r2).continuousOn
    refine MeasureTheory.Integrable.mono' (g := fun q : ℝ³ × ℝ³ => CB * |w1 q|) ?_ ?_ ?_
    · exact hw1L1.abs.const_mul CB
    · exact ((hBc r2).measurable.aestronglyMeasurable.mul hw1m)
    · rw [MeasureTheory.ae_restrict_iff' ((acube_measurable s).prod (acube_measurable s))]
      filter_upwards with q hq
      rw [Real.norm_eq_abs, abs_mul]
      have h' : |B (ins2 i j' q.1 q.2 r2)| ≤ CB := by
        simpa [Real.norm_eq_abs] using hCB q hq
      exact mul_le_mul_of_nonneg_right h' (abs_nonneg _)
  have hβiter : ∀ r2 : X p,
      (∫ z in acube s, ∫ y in acube s, B (ins2 i j' y z r2) * w1 (y, z)) = β r2 := by
    intro r2
    rw [hβdef]
    exact prod_setIntegral_eq_iter2_ae (ℓ := s)
      (w := fun q : ℝ³ × ℝ³ => B (ins2 i j' q.1 q.2 r2) * w1 q) (hfib_int r2)
  -- the peel: the box integral is the fibre integral of `A₂ · β`
  have hpeel := abox_integral_peel2 (p := p) (ℓ := s) i j'
    (fun x : X (p + 2) => A x * B x * w1 (x i, x j)) hFint
  have hstep : ∀ r2 : X p, (∫ z in acube s, ∫ y in acube s,
        A (ins2 i j' y z r2) * B (ins2 i j' y z r2) *
          w1 (ins2 i j' y z r2 i, ins2 i j' y z r2 j)) = A₂ r2 * β r2 := by
    intro r2
    have h1 : (∫ z in acube s, ∫ y in acube s,
        A (ins2 i j' y z r2) * B (ins2 i j' y z r2) *
          w1 (ins2 i j' y z r2 i, ins2 i j' y z r2 j))
        = ∫ z in acube s, ∫ y in acube s, A₂ r2 * (B (ins2 i j' y z r2) * w1 (y, z)) := by
      apply integral_congr_ae
      filter_upwards with z
      apply integral_congr_ae
      filter_upwards with y
      rw [hAfib y z r2, ins2_apply_i i j' y z r2]
      have hj2 : ins2 i j' y z r2 j = z := by
        rw [← hj']; exact ins2_apply_succ i j' y z r2
      rw [hj2]
      ring
    have h2 : (∫ z in acube s, ∫ y in acube s, A₂ r2 * (B (ins2 i j' y z r2) * w1 (y, z)))
        = A₂ r2 * β r2 := by
      rw [show (∫ z in acube s, ∫ y in acube s,
            A₂ r2 * (B (ins2 i j' y z r2) * w1 (y, z)))
          = ∫ z in acube s, A₂ r2 * (∫ y in acube s, B (ins2 i j' y z r2) * w1 (y, z)) from ?_]
      · rw [MeasureTheory.integral_const_mul, hβiter r2]
      · apply integral_congr_ae
        filter_upwards with z
        rw [MeasureTheory.integral_const_mul]
    rw [h1, h2]
  have hmain1 : (∫ x in abox (p + 2) s, A x * B x * w1 (x i, x j))
      = ∫ r2 in abox p s, A₂ r2 * β r2 := by
    rw [hpeel]
    apply integral_congr_ae
    filter_upwards with r2
    exact hstep r2
  -- the fibre `L²`-masses
  set X1 : ℝ := ∫ r2 in abox p s, (A₂ r2) ^ 2 with hX1def
  set X2 : ℝ := ∫ r2 in abox p s, (β r2) ^ 2 with hX2def
  set X3 : ℝ := ∫ r2 in abox p s, γ r2 with hX3def
  have hfin' : IsFiniteMeasure ((volume : Measure (X p)).restrict (abox p s)) := by
    constructor
    rw [Measure.restrict_apply_univ]
    exact abox_lt_top p s hs.le
  haveI := hfin'
  have hWnn : 0 ≤ W := by
    rw [hWdef]
    exact MeasureTheory.integral_nonneg (fun q => sq_nonneg (w1 q))
  have hAint : IntegrableOn (fun x : X (p + 2) => (A x) ^ 2) (abox (p + 2) s) volume :=
    integrableOn_abox_of_continuous hs (hAcont.pow 2)
  have hpc := pair_const_fibre_data (p := p) (s := s) hs i j' (A := A) hAint hAfib
  have hA₂sq_int : IntegrableOn (fun r2 : X p => (A₂ r2) ^ 2) (abox p s) volume := hpc.1
  have hApeel : (∫ x in abox (p + 2) s, (A x) ^ 2) = s ^ 6 * X1 := by
    rw [hX1def]; exact hpc.2
  have hps := peel_fibre_sq (p := p) (s := s) hs i j' (B := B) hBcont
  have hγint : Integrable γ ((volume : Measure (X p)).restrict (abox p s)) := hps.1
  have hX3eq : X3 = (∫ x in abox (p + 2) s, (B x) ^ 2) := by
    rw [hX3def]; exact hps.2.symm
  have hRest2cont : Continuous (fun r2 : X p => rest2 i j' r2) := by
    have h1 : Continuous (fun r2 : X p => kcInsN p j' ((0 : ℝ³), r2)) :=
      (kcInsN_cont j').comp (continuous_const.prodMk continuous_id)
    have h2 : Continuous (fun r2 : X p => ((0 : ℝ³), kcInsN p j' ((0 : ℝ³), r2))) :=
      continuous_const.prodMk h1
    exact (kcInsN_cont i).comp h2
  have hA₂cont : Continuous A₂ := by rw [hA₂def]; exact hAcont.comp hRest2cont
  have hA₂aesm : AEStronglyMeasurable A₂ ((volume : Measure (X p)).restrict (abox p s)) :=
    hA₂cont.aestronglyMeasurable
  have hA₂MemLp : MemLp A₂ 2 ((volume : Measure (X p)).restrict (abox p s)) :=
    (memLp_two_iff_integrable_sq hA₂aesm).mpr hA₂sq_int
  have hβaesm : AEStronglyMeasurable β ((volume : Measure (X p)).restrict (abox p s)) :=
    aesm_fibre_integral (p := p) (s := s) i j' (B := B) hBcont hw1m
  -- pointwise Cauchy–Schwarz in the pair variables
  have hpt : ∀ r2 : X p, (β r2) ^ 2 ≤ γ r2 * W := by
    intro r2
    obtain ⟨CB, hCB⟩ := hKK.exists_bound_of_continuousOn
      (f := fun q : ℝ³ × ℝ³ => B (ins2 i j' q.1 q.2 r2)) (hBc r2).continuousOn
    have hfb : MemLp (fun q : ℝ³ × ℝ³ => B (ins2 i j' q.1 q.2 r2)) 2
        (volume.restrict (acube s ×ˢ acube s)) :=
      MemLp.of_bound ((hBc r2).measurable.aestronglyMeasurable) CB (by
        rw [MeasureTheory.ae_restrict_iff' ((acube_measurable s).prod (acube_measurable s))]
        filter_upwards with q hq
        simpa [Real.norm_eq_abs] using hCB q hq)
    have hcs := sq_integral_mul_le (μ := volume.restrict (acube s ×ˢ acube s))
      (f := fun q : ℝ³ × ℝ³ => B (ins2 i j' q.1 q.2 r2)) (g := w1) hfb hw1MemLp
    simpa only [hβdef, hγdef, hWdef] using hcs
  have hβsq_int : Integrable (fun r2 : X p => (β r2) ^ 2)
      ((volume : Measure (X p)).restrict (abox p s)) := by
    refine MeasureTheory.Integrable.mono' (g := fun r2 : X p => γ r2 * W) ?_ ?_ ?_
    · exact hγint.mul_const W
    · exact hβaesm.pow 2
    · filter_upwards with r2
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (β r2))]
      exact hpt r2
  have hβMemLp : MemLp β 2 ((volume : Measure (X p)).restrict (abox p s)) :=
    (memLp_two_iff_integrable_sq hβaesm).mpr hβsq_int
  have hβbnd : X2 ≤ W * X3 := by
    have h := MeasureTheory.integral_mono_ae hβsq_int (hγint.mul_const W) (ae_of_all _ hpt)
    have h2 : (∫ r2 in abox p s, γ r2 * W) = X3 * W := by
      rw [MeasureTheory.integral_mul_const, hX3def]
    rw [h2] at h
    rw [hX2def]
    calc (∫ r2 in abox p s, (β r2) ^ 2) ≤ X3 * W := h
      _ = W * X3 := by ring
  have hAbs := abs_integral_mul_le_sqrt (μ := (volume : Measure (X p)).restrict (abox p s))
    (f := A₂) (g := β) hA₂MemLp hβMemLp
  -- the two dilation factors
  have hsqrtA : Real.sqrt (∫ x in abox (p + 2) s, (A x) ^ 2) = s ^ 3 * Real.sqrt X1 := by
    rw [hApeel, show s ^ 6 = (s ^ 3) ^ 2 by ring, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by positivity)]
  have hsqrtX1 : Real.sqrt X1 = (s ^ 3)⁻¹ * Real.sqrt (∫ x in abox (p + 2) s, (A x) ^ 2) := by
    rw [hsqrtA, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 3 (ne_of_gt hs)), one_mul]
  have hsqrtX3 : Real.sqrt X3 = Real.sqrt (∫ x in abox (p + 2) s, (B x) ^ 2) := by rw [hX3eq]
  calc |∫ x in abox (p + 2) s, A x * B x * w1 (x i, x j)|
      = |∫ r2 in abox p s, A₂ r2 * β r2| := by rw [hmain1]
    _ ≤ Real.sqrt X1 * Real.sqrt X2 := by
        rw [hX1def, hX2def]; exact hAbs
    _ ≤ Real.sqrt X1 * Real.sqrt (W * X3) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hβbnd) (Real.sqrt_nonneg X1)
    _ = Real.sqrt X1 * (Real.sqrt W * Real.sqrt X3) := by rw [Real.sqrt_mul hWnn]
    _ = (s ^ 3)⁻¹ * Real.sqrt (∫ x in abox (p + 2) s, (A x) ^ 2) *
          Real.sqrt (∫ x in abox (p + 2) s, (B x) ^ 2) * Real.sqrt W := by
        rw [hsqrtX1, hsqrtX3]; ring


end Work.SmallBoxA0
