import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.Nonlinear.Pieces.Rl1.rl1Main
import Submission.Work.FTS.Nonlinear.Pieces.Rows
import Submission.Work.FTS.Nonlinear.Pieces.Basic
import Submission.Work.FTS.Nonlinear.Pieces.L12_zero_le_weak
import Submission.Work.FTS.H2.L12ZeroQ
import Submission.Work.FTS.H2.L12HQ
import Submission.Work.FTS.H2.WProdQ
import Submission.Work.FTS.H2.WtoHQ
import Submission.Work.FTS.Nonlinear.FstarPkgAll
import Submission.Work.Blocks.HkMul_ang_le
import Submission.Work.Spaces.ProductRuleInW
import Submission.Work.FTS.Nonlinear.Pieces.splitsDiff
import Submission.Work.FTS.Nonlinear.Pieces.L12FK_add_ge0
import Submission.Work.Construction.GammaN0
import Submission.Work.Construction.H4N_GammaTerm_le
import Submission.Work.Spaces.Gamma_WlInf
import Submission.Work.FTS.LocData.angMaj_mem
import Submission.Work.FTS.LocDataExt.SepFactor
import Submission.Work.FTS.Nonlinear.Pieces.AuxSep

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Pieces

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000

/-! ## The master tool: `|L₁₂(f)(0)| ≤ 3|f|_{ℋ⁴}` from `SmoothQuad` + `HkMem`

This is `Work.FTS.H2.L12ZeroQ` with the `RegQ` hypothesis weakened to its two usable halves
(`SmoothQuad` and `HkMem α 4`); the `BdryTraces` component of `RegQ` is never used in that
proof.  It is the form in which the L₁₂-estimates of `rak`/`rl0`/`rl1`/`rl2` are consumed. -/
theorem L12_zero_le_HkNorm {α : ℝ} {f : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hsm : Work.FTS.LocData.SmoothQuad f) (hmem : Work.Spaces.HkMem α 4 f) :
    |Work.Construction.L12 f 0| ≤ 3 * Work.FTS.Nonlin.Xn α f := by
  set μ : MeasureTheory.Measure ℝ := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) with hμdef
  have hslice : ∀ z : ℝ, 0 < z →
      MeasureTheory.IntegrableOn (fun θ : ℝ => (f z θ) ^ 2) Work.Spaces.Iθ :=
    fun z hz => Work.FTS.H2.l12q_slice_sq_integrableOn α f hsm hmem hz
  have hdens : ∀ r : ℝ, 0 < r → |Work.Elliptic.L12dens f r|
      ≤ Real.sqrt 3 * Real.sqrt (∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2) / r :=
    fun r hr => Work.FTS.H2.l12q_l12dens_slice f hr (hslice r hr)
  have hPhiw_le := Work.FTS.H2.l12q_phiWeight_le α f hmem
  have hPhiw_int := Work.FTS.H2.l12q_phiWeight_integrable α f hsm hmem
  have hPhi_aesm := Work.FTS.H2.l12q_aesm f hsm
  have hPhi0 : ∀ r : ℝ, 0 ≤ ∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2 := fun r =>
    MeasureTheory.integral_nonneg_of_ae (Filter.Eventually.of_forall fun θ => sq_nonneg _)
  set A : ℝ → ℝ := fun r => Real.sqrt (3 * ((∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2)
      * ((1 + r) / r) ^ 2)) with hAdef
  set B : ℝ → ℝ := fun r => 1 / (1 + r) with hBdef
  have hAe0 : ∀ᵐ r ∂μ, 0 ≤ A r := by
    filter_upwards [MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume) measurableSet_Ioi]
      with r hr
    rw [hAdef]
    exact Real.sqrt_nonneg _
  have hBe0 : ∀ᵐ r ∂μ, 0 ≤ B r := by
    filter_upwards [MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume) measurableSet_Ioi]
      with r hr
    rw [hBdef]
    have hr' : (0 : ℝ) < r := Set.mem_Ioi.mp hr
    exact div_nonneg zero_le_one (by linarith)
  have hAmeas : MeasureTheory.AEStronglyMeasurable A μ := by
    rw [hμdef, hAdef]
    exact Real.continuous_sqrt.comp_aestronglyMeasurable
      ((aestronglyMeasurable_const.mul hPhi_aesm))
  have hpt : ∀ r : ℝ,
      A r ^ 2 = 3 * ((∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2) * ((1 + r) / r) ^ 2) := by
    intro r
    rw [hAdef]
    exact Real.sq_sqrt (mul_nonneg (by norm_num)
      (mul_nonneg (hPhi0 r) (sq_nonneg _)))
  have h33 : MeasureTheory.Integrable
      (fun r : ℝ => 3 * ((∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2) * ((1 + r) / r) ^ 2)) μ := by
    rw [hμdef]
    exact hPhiw_int.const_mul 3
  have hAint : MeasureTheory.Integrable (fun r => A r ^ 2) μ := by
    refine h33.congr ?_
    filter_upwards with r
    exact (hpt r).symm
  have hmemA : MeasureTheory.MemLp A 2 μ :=
    (MeasureTheory.memLp_two_iff_integrable_sq hAmeas).mpr hAint
  obtain ⟨hB_int, hB_le⟩ := Work.FTS.H2.InvOneAddSq
  have hBmeas : MeasureTheory.AEStronglyMeasurable B μ := by
    rw [hμdef, hBdef]
    have h2 : MeasureTheory.AEStronglyMeasurable (fun r : ℝ => 1 / (1 + r))
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
      (ContinuousOn.div continuousOn_const (continuousOn_const.add continuousOn_id)
        (fun r hr => by
          have hr' : (0 : ℝ) < r := Set.mem_Ioi.mp hr
          exact ne_of_gt (by show (0 : ℝ) < 1 + r; linarith))).aestronglyMeasurable
        measurableSet_Ioi
    simpa only using h2
  have hBint : MeasureTheory.Integrable (fun r => B r ^ 2) μ := by
    rw [hμdef, hBdef]
    exact hB_int
  have hmemB : MeasureTheory.MemLp B 2 μ :=
    (MeasureTheory.memLp_two_iff_integrable_sq hBmeas).mpr hBint
  have hbd : ∀ᵐ r ∂μ, |Work.Elliptic.L12dens f r| ≤ A r * B r := by
    filter_upwards [MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume) measurableSet_Ioi]
      with r hr
    have h5 := hdens r (Set.mem_Ioi.mp hr)
    have hr1 : 1 + r ≠ 0 := by have h := Set.mem_Ioi.mp hr; linarith
    have h5' : |Work.Elliptic.L12dens f r|
        ≤ Real.sqrt 3 * Real.sqrt (∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2) * r⁻¹ := by
      simpa only [div_eq_mul_inv] using h5
    have hkey : ((1 + r) / r) * (1 / (1 + r)) = r⁻¹ := by
      field_simp
    have hAval : A r = Real.sqrt 3 * Real.sqrt (∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2)
        * ((1 + r) / r) := by
      have hr' : (0 : ℝ) < r := Set.mem_Ioi.mp hr
      have hy : (0 : ℝ) ≤ (1 + r) / r := div_nonneg (by linarith) (le_of_lt hr')
      rw [hAdef]
      dsimp only
      rw [Real.sqrt_mul (show (0 : ℝ) ≤ 3 from by norm_num),
        Real.sqrt_mul (hPhi0 r) (((1 + r) / r) ^ 2), Real.sqrt_sq hy]
      ring
    rw [hAval, hBdef]
    calc |Work.Elliptic.L12dens f r|
        ≤ Real.sqrt 3 * Real.sqrt (∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2) * r⁻¹ := h5'
      _ = Real.sqrt 3 * Real.sqrt (∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2)
            * (((1 + r) / r) * (1 / (1 + r))) := by rw [hkey]
      _ = Real.sqrt 3 * Real.sqrt (∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2)
            * ((1 + r) / r) * (1 / (1 + r)) := by ring
  have hcs := Work.FTS.H2.CS1D (μ := μ) (g := fun r => Work.Elliptic.L12dens f r)
    hmemA hmemB hAe0 hBe0 hbd
  have hA2le : ∫ r, A r ^ 2 ∂μ ≤ 3 * Work.Spaces.HkSq α 4 f := by
    rw [hμdef]
    have hpt' : ∀ r ∈ Set.Ioi (0 : ℝ),
        A r ^ 2 = 3 * ((∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2) * ((1 + r) / r) ^ 2) :=
      fun r _ => hpt r
    calc ∫ r in Set.Ioi (0 : ℝ), A r ^ 2
        = ∫ r in Set.Ioi (0 : ℝ),
            3 * ((∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2) * ((1 + r) / r) ^ 2) :=
          MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hpt'
      _ = 3 * ∫ r in Set.Ioi (0 : ℝ),
            (∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2) * ((1 + r) / r) ^ 2 :=
          MeasureTheory.integral_const_mul 3 _
      _ ≤ 3 * Work.Spaces.HkSq α 4 f := mul_le_mul_of_nonneg_left hPhiw_le (by norm_num)
  have hB2le : ∫ r, B r ^ 2 ∂μ ≤ 2 := by
    rw [hμdef]
    have hfun : (fun r : ℝ => B r ^ 2) = fun r : ℝ => (1 / (1 + r)) ^ 2 := by
      funext r
      rw [hBdef]
    rw [hfun]
    exact hB_le
  have hfinal : |Work.Elliptic.L12 f 0| ≤ Real.sqrt (3 * Work.Spaces.HkSq α 4 f) * Real.sqrt 2 := by
    have h1 : (∫ r, Work.Elliptic.L12dens f r ∂μ) = Work.Elliptic.L12 f 0 := rfl
    rw [← h1]
    refine hcs.trans ?_
    exact mul_le_mul (Real.sqrt_le_sqrt hA2le) (Real.sqrt_le_sqrt hB2le)
      (Real.sqrt_nonneg (∫ r, B r ^ 2 ∂μ)) (Real.sqrt_nonneg _)
  have hsqrt : Real.sqrt (3 * Work.Spaces.HkSq α 4 f) * Real.sqrt 2
      = Real.sqrt 6 * Work.Spaces.HkNorm α 4 f := by
    rw [Real.sqrt_mul (show (0 : ℝ) ≤ 3 by norm_num) (Work.Spaces.HkSq α 4 f),
      Work.Spaces.HkNorm]
    rw [show Real.sqrt 3 * Real.sqrt (Work.Spaces.HkSq α 4 f) * Real.sqrt 2
        = (Real.sqrt 3 * Real.sqrt 2) * Real.sqrt (Work.Spaces.HkSq α 4 f) from by ring]
    rw [show Real.sqrt 3 * Real.sqrt 2 = Real.sqrt 6 from by
      rw [← Real.sqrt_mul (show (0 : ℝ) ≤ 3 by norm_num) (2 : ℝ)]
      norm_num]
  have h6le : Real.sqrt 6 ≤ 3 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num), Real.sqrt_nonneg 6]
  calc |Work.Elliptic.L12 f 0| ≤ Real.sqrt (3 * Work.Spaces.HkSq α 4 f) * Real.sqrt 2 := hfinal
    _ = Real.sqrt 6 * Work.Spaces.HkNorm α 4 f := hsqrt
    _ ≤ 3 * Work.Spaces.HkNorm α 4 f :=
        mul_le_mul_of_nonneg_right h6le (Work.Spaces.HkNorm_nonneg α 4 f)
    _ = 3 * Work.FTS.Nonlin.Xn α f := rfl

/-! ## Two measure-theoretic wrappers

* `aesm_weighted_energy_of_continuousOn`: the weighted angular energy
  `r ↦ (∫_θ f r θ²)·((1+r)/r)²` is a.e. strongly measurable on `(0,∞)` as soon as `f` is
  continuous on the open quadrant (Fubini from the joint continuity, then multiplication by the
  continuous Hardy weight).
* `L12_zero_le_of_weight_bound`: the "trivial observation" of the paper,
  `|L₁₂(f)(0)| ≤ C‖((1+z)/z)f‖_{L²}`, in the form in which the pieces are consumed: an a.e.
  bound on the weighted angular energy by an integrable `Φ` gives
  `|L₁₂(f)(0)| ≤ 3√(∫Φ)`. -/
theorem aesm_weighted_energy_of_continuousOn {f : ℝ → ℝ → ℝ}
    (hc : ContinuousOn (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) :
    MeasureTheory.AEStronglyMeasurable
      (fun r => (∫ θ in Work.Spaces.Iθ, f r θ ^ 2) * ((1 + r) / r) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
  have hsq : ContinuousOn (fun p : ℝ × ℝ => (f p.1 p.2) ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    change ContinuousOn (fun p : ℝ × ℝ => (Function.uncurry f p) ^ 2) _
    exact hc.pow 2
  have hquad : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => (f p.1 p.2) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ hsq
  have hslice : MeasureTheory.AEStronglyMeasurable
      (fun r : ℝ => ∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    MeasureTheory.AEStronglyMeasurable.integral_prod_right' hquad
  have hmono : MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))
      ≤ MeasureTheory.volume.restrict Work.Spaces.Iz :=
    MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume Set.Ioi_subset_Ici_self
  have h1 : MeasureTheory.AEStronglyMeasurable
      (fun r : ℝ => ∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := hslice.mono_measure hmono
  have hw : MeasureTheory.AEStronglyMeasurable (fun r : ℝ => ((1 + r) / r) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    ((ContinuousOn.div (continuousOn_const.add continuousOn_id) continuousOn_id
      (fun r hr => ne_of_gt (Set.mem_Ioi.mp hr))).pow 2).aestronglyMeasurable measurableSet_Ioi
  exact h1.mul hw

theorem L12_zero_le_of_weight_bound {f : ℝ → ℝ → ℝ} {Φ : ℝ → ℝ}
    (hsl : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      MeasureTheory.IntegrableOn (fun θ => f r θ ^ 2) Work.Spaces.Iθ)
    (hmeas : MeasureTheory.AEStronglyMeasurable
      (fun r => (∫ θ in Work.Spaces.Iθ, f r θ ^ 2) * ((1 + r) / r) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))))
    (hΦ : MeasureTheory.IntegrableOn Φ (Set.Ioi (0 : ℝ)))
    (hbd : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      (∫ θ in Work.Spaces.Iθ, f r θ ^ 2) * ((1 + r) / r) ^ 2 ≤ Φ r) :
    |Work.Construction.L12 f 0| ≤ 3 * Real.sqrt (∫ r in Set.Ioi (0 : ℝ), Φ r) := by
  have hnn : ∀ r : ℝ, 0 ≤ (∫ θ in Work.Spaces.Iθ, f r θ ^ 2) * ((1 + r) / r) ^ 2 :=
    fun r => mul_nonneg (integral_nonneg fun θ => sq_nonneg _) (sq_nonneg _)
  have hfin : MeasureTheory.IntegrableOn
      (fun r => (∫ θ in Work.Spaces.Iθ, f r θ ^ 2) * ((1 + r) / r) ^ 2)
      (Set.Ioi (0 : ℝ)) := by
    refine hΦ.mono' hmeas ?_
    filter_upwards [hbd] with r hr
    rw [Real.norm_of_nonneg (hnn r)]
    exact hr
  have hle := L12_zero_le_weak 0 f hsl hfin
  have hmono : (∫ r in Set.Ioi (0 : ℝ),
        (∫ θ in Work.Spaces.Iθ, f r θ ^ 2) * ((1 + r) / r) ^ 2)
      ≤ ∫ r in Set.Ioi (0 : ℝ), Φ r :=
    MeasureTheory.integral_mono_of_nonneg
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun r _ => hnn r)) hΦ hbd
  calc |Work.Construction.L12 f 0|
      ≤ 3 * Real.sqrt (∫ r in Set.Ioi (0 : ℝ),
          (∫ θ in Work.Spaces.Iθ, f r θ ^ 2) * ((1 + r) / r) ^ 2) := hle
    _ ≤ 3 * Real.sqrt (∫ r in Set.Ioi (0 : ℝ), Φ r) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hmono) (by norm_num)

/-! ## Slot bounds inside the `ℋ^k`-integrand -/

private lemma ite_sq_nonneg {c : Prop} [Decidable c] (a : ℝ) :
    0 ≤ (if c then a ^ 2 else (0 : ℝ)) := by
  split_ifs with h
  · exact sq_nonneg _
  · exact le_refl 0

theorem slot_z_le_HkIntegrand (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ) (z θ : ℝ) (n : ℕ) (hn : n ≤ k) :
    (Work.Spaces.DzIter n F z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ Work.Spaces.HkIntegrand α k F z θ := by
  have hmem : n ∈ Finset.range (k + 1) := Finset.mem_range.mpr (by omega)
  have h2 : (0 : ℝ) ≤ ∑ i ∈ Finset.range (k + 1),
      ∑ j ∈ Finset.range (k + 1), if 1 ≤ i ∧ i + j ≤ k
        then (Work.Spaces.mixed j i F z θ * Work.Spaces.Wt α z θ) ^ 2 else 0 :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => ite_sq_nonneg _))
  rw [Work.Spaces.HkIntegrand]
  exact le_trans (Finset.single_le_sum
    (f := fun i => (Work.Spaces.DzIter i F z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
    (fun i _ => sq_nonneg _) hmem) (le_add_of_nonneg_right h2)

theorem slot_mixed_le_HkIntegrand (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ) (z θ : ℝ) (j i : ℕ)
    (hi : 1 ≤ i) (hij : i + j ≤ k) :
    (Work.Spaces.mixed j i F z θ * Work.Spaces.Wt α z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α k F z θ := by
  have h1 : (0 : ℝ) ≤ ∑ i ∈ Finset.range (k + 1),
      (Work.Spaces.DzIter i F z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hmemj : j ∈ Finset.range (k + 1) := Finset.mem_range.mpr (by omega)
  have hinner : ∀ j' ∈ Finset.range (k + 1),
      (0 : ℝ) ≤ (if 1 ≤ i ∧ i + j' ≤ k
        then (Work.Spaces.mixed j' i F z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) :=
    fun j' _ => ite_sq_nonneg _
  have hmemi : i ∈ Finset.range (k + 1) := Finset.mem_range.mpr (by omega)
  have hkey : (if 1 ≤ i ∧ i + j ≤ k
      then (Work.Spaces.mixed j i F z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
      = (Work.Spaces.mixed j i F z θ * Work.Spaces.Wt α z θ) ^ 2 := if_pos ⟨hi, hij⟩
  rw [Work.Spaces.HkIntegrand]
  refine le_trans ?_ (le_add_of_nonneg_left h1)
  calc (Work.Spaces.mixed j i F z θ * Work.Spaces.Wt α z θ) ^ 2
      = (if 1 ≤ i ∧ i + j ≤ k
          then (Work.Spaces.mixed j i F z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) := hkey.symm
    _ ≤ ∑ j' ∈ Finset.range (k + 1), (if 1 ≤ i ∧ i + j' ≤ k
          then (Work.Spaces.mixed j' i F z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) :=
        Finset.single_le_sum hinner hmemj
    _ ≤ ∑ i' ∈ Finset.range (k + 1), ∑ j' ∈ Finset.range (k + 1), (if 1 ≤ i' ∧ i' + j' ≤ k
          then (Work.Spaces.mixed j' i' F z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) :=
        Finset.single_le_sum
          (f := fun i' => ∑ j' ∈ Finset.range (k + 1), (if 1 ≤ i' ∧ i' + j' ≤ k
            then (Work.Spaces.mixed j' i' F z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
          (fun i' _ => Finset.sum_nonneg (fun j' _ => ite_sq_nonneg _)) hmemi

/-! ## Smoothness of a `SmoothQuad` datum on the open quadrant -/

theorem continuousOn_uncurry_of_smoothQuad {f : ℝ → ℝ → ℝ}
    (h : Work.FTS.LocData.SmoothQuad f) :
    ContinuousOn (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  have h' := h
  rw [Work.FTS.LocData.SmoothQuad] at h'
  exact h'.continuousOn.mono (fun p hp => by
    simp only [Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] at hp ⊢
    exact ⟨by linarith [hp.1], hp.2⟩)

/-! ## The `D_θ`- and `D_z`-slice energies are dominated by the `ℋ⁴`-integrand -/

private lemma one_le_rpow_neg {t γ : ℝ} (h0 : 0 < t) (h1 : t ≤ 1) (hg : 0 ≤ γ) :
    1 ≤ t ^ (-γ) := by
  rw [Real.rpow_neg h0.le]
  exact (one_le_inv₀ (Real.rpow_pos_of_pos h0 γ)).mpr (Real.rpow_le_one h0.le h1 hg)

private lemma mul_shape_le {w s : ℝ} (h1 : 1 ≤ w) (h2 : 1 ≤ s) : w ≤ w * (w * s) := by
  have h3 : 1 ≤ w * s := by nlinarith
  calc w = w * 1 := by ring
    _ ≤ w * (w * s) := mul_le_mul_of_nonneg_left h3 (by linarith)

private lemma dth_mul_Wt_sq {α z θ : ℝ} (F : ℝ → ℝ → ℝ) (hs0 : 0 < Real.sin (2 * θ)) :
    (Work.Spaces.Dth F z θ * Work.Spaces.Wt α z θ) ^ 2
      = Work.Spaces.Dth F z θ ^ 2 * (Work.Spaces.w z
          * (Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))) := by
  have hsin2 : ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
      = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hs0.le]
    ring_nf
  rw [Work.Spaces.Wt, Work.Spaces.wTheta, mul_pow, mul_pow, hsin2]
  ring

private lemma dzIter_mul_div_sq {η : ℝ} (z θ : ℝ) (F : ℝ → ℝ → ℝ)
    (hs0 : 0 < Real.sin (2 * θ)) :
    (Work.Spaces.DzIter 1 F z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (η / 2))) ^ 2
      = Work.Spaces.Dz F z θ ^ 2 * (Work.Spaces.w z
          * (Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-η))) := by
  have hsin2 : ((Real.sin (2 * θ)) ^ (η / 2))⁻¹ ^ 2
      = (Real.sin (2 * θ)) ^ (-η) := by
    rw [← Real.rpow_neg hs0.le]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hs0.le]
    ring_nf
  simp only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero]
  rw [div_eq_mul_inv, mul_pow, mul_pow, hsin2]
  ring

theorem slice_energy_le_HkIntegrand (α : ℝ) (g : ℝ → ℝ → ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hmem : Work.Spaces.HkMem α 4 g) :
    (∀ z : ℝ, 0 < z →
        (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dth g z θ) ^ 2) * ((1 + z) / z) ^ 2
          ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ) ∧
    (∀ z : ℝ, 0 < z →
        (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz g z θ) ^ 2) * ((1 + z) / z) ^ 2
          ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ) := by
  have hwm : ∀ z : ℝ, 0 < z → 1 ≤ Work.Spaces.w z := fun z hz => by
    rw [Work.Spaces.w, one_le_div (by positivity)]
    nlinarith
  have hw_eq : ∀ z : ℝ, ((1 + z) / z) ^ 2 = Work.Spaces.w z := fun z => by
    rw [Work.Spaces.w, div_pow]
  have hIoo : Work.Spaces.Iθ =ᵐ[MeasureTheory.volume] Set.Ioo (0 : ℝ) (π / 2) :=
    MeasureTheory.Ioo_ae_eq_Icc.symm
  have hgam : 0 ≤ Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
  have heta : 0 ≤ Work.Spaces.eta := le_of_lt Work.Spaces.eta_pos
  constructor
  · intro z hz
    have hpt : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
        (Work.Spaces.Dth g z θ) ^ 2 * Work.Spaces.w z
          ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
      intro θ hθ
      have hs0 : 0 < Real.sin (2 * θ) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
      have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
      have hsin : 1 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
        one_le_rpow_neg hs0 hs1 hgam
      have h2 : Work.Spaces.w z ≤ Work.Spaces.w z
          * (Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) :=
        mul_shape_le (hwm z hz) hsin
      refine le_trans (mul_le_mul_of_nonneg_left h2 (sq_nonneg _)) ?_
      rw [← dth_mul_Wt_sq (α := α) g hs0]
      have h3 := slot_mixed_le_HkIntegrand α 4 g z θ 0 1 (by norm_num) (by norm_num)
      simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_succ,
        Work.Spaces.DthIter_zero] using h3
    have hmono : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dth g z θ) ^ 2) * Work.Spaces.w z
        ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ := by
      rw [← MeasureTheory.integral_mul_const]
      have hIoo2 : MeasureTheory.volume.restrict Work.Spaces.Iθ
          = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) :=
        MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc.symm
      refine MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun θ =>
          mul_nonneg (sq_nonneg _) (le_trans zero_le_one (hwm z hz)))
        (hmem.1 z (le_of_lt hz)) ?_
      rw [hIoo2]
      exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => hpt θ hθ)
    rw [hw_eq z]
    exact hmono
  · intro z hz
    have hpt : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
        (Work.Spaces.Dz g z θ) ^ 2 * Work.Spaces.w z
          ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
      intro θ hθ
      have hs0 : 0 < Real.sin (2 * θ) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
      have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
      have hsin : 1 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
        one_le_rpow_neg hs0 hs1 heta
      have h2 : Work.Spaces.w z ≤ Work.Spaces.w z
          * (Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) :=
        mul_shape_le (hwm z hz) hsin
      refine le_trans (mul_le_mul_of_nonneg_left h2 (sq_nonneg _)) ?_
      rw [← dzIter_mul_div_sq (η := Work.Spaces.eta) z θ g hs0]
      exact slot_z_le_HkIntegrand α 4 g z θ 1 (by norm_num)
    have hmono : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz g z θ) ^ 2) * Work.Spaces.w z
        ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ := by
      rw [← MeasureTheory.integral_mul_const]
      have hIoo2 : MeasureTheory.volume.restrict Work.Spaces.Iθ
          = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) :=
        MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc.symm
      refine MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun θ =>
          mul_nonneg (sq_nonneg _) (le_trans zero_le_one (hwm z hz)))
        (hmem.1 z (le_of_lt hz)) ?_
      rw [hIoo2]
      exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => hpt θ hθ)
    rw [hw_eq z]
    exact hmono

/-! ## Pointwise domination of the `g`-slots by the `ℋ⁴`-integrand -/

theorem g_sq_le_HkIntegrand (α : ℝ) (g : ℝ → ℝ → ℝ) (hα : 0 < α) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    (g z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
  have hs0 : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hwm : 1 ≤ Work.Spaces.w z := by
    rw [Work.Spaces.w, one_le_div (by positivity)]; nlinarith
  have heta2 : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) ≤ 1 :=
    Real.rpow_le_one hs0.le hs1 (by have := Work.Spaces.eta_pos; linarith)
  have heta2pos : 0 < (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) :=
    Real.rpow_pos_of_pos hs0 _
  have h1 : 1 ≤ Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) := by
    rw [one_le_div heta2pos]; linarith
  have hA : (g z θ) ^ 2 ≤ (g z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    calc (g z θ) ^ 2 = (g z θ) ^ 2 * 1 := by ring
      _ ≤ (g z θ) ^ 2 * (Work.Spaces.w z
            / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2 := by
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
          nlinarith [h1]
      _ = (g z θ * (Work.Spaces.w z
            / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by ring
  exact le_trans hA (slot_z_le_HkIntegrand α 4 g z θ 0 (by norm_num))

theorem dth_sq_le_HkIntegrand (α : ℝ) (g : ℝ → ℝ → ℝ) (hα : 0 < α) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    (Work.Spaces.Dth g z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
  have hs0 : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hwm : 1 ≤ Work.Spaces.w z := by
    rw [Work.Spaces.w, one_le_div (by positivity)]; nlinarith
  have hsin : 1 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
    one_le_rpow_neg hs0 hs1 (by rw [Work.Spaces.gam]; linarith)
  have h2 := mul_shape_le hwm hsin
  have hA : (Work.Spaces.Dth g z θ) ^ 2 ≤ (Work.Spaces.Dth g z θ) ^ 2
      * (Work.Spaces.w z * (Work.Spaces.w z
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))) := by
    calc (Work.Spaces.Dth g z θ) ^ 2 = (Work.Spaces.Dth g z θ) ^ 2 * 1 := by ring
      _ ≤ (Work.Spaces.Dth g z θ) ^ 2 * Work.Spaces.w z :=
          mul_le_mul_of_nonneg_left hwm (sq_nonneg _)
      _ ≤ (Work.Spaces.Dth g z θ) ^ 2 * (Work.Spaces.w z
            * (Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))) :=
          mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
  rw [← dth_mul_Wt_sq (α := α) g hs0] at hA
  exact le_trans hA (by
    have h3 := slot_mixed_le_HkIntegrand α 4 g z θ 0 1 (by norm_num) (by norm_num)
    simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_succ,
      Work.Spaces.DthIter_zero] using h3)

theorem dz_sq_le_HkIntegrand (α : ℝ) (g : ℝ → ℝ → ℝ) (hα : 0 < α) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    (Work.Spaces.Dz g z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
  have hs0 : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hwm : 1 ≤ Work.Spaces.w z := by
    rw [Work.Spaces.w, one_le_div (by positivity)]; nlinarith
  have heta : 0 ≤ Work.Spaces.eta := le_of_lt Work.Spaces.eta_pos
  have hsin : 1 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
    one_le_rpow_neg hs0 hs1 heta
  have h2 := mul_shape_le hwm hsin
  have hA : (Work.Spaces.Dz g z θ) ^ 2 ≤ (Work.Spaces.Dz g z θ) ^ 2
      * (Work.Spaces.w z * (Work.Spaces.w z
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) := by
    calc (Work.Spaces.Dz g z θ) ^ 2 = (Work.Spaces.Dz g z θ) ^ 2 * 1 := by ring
      _ ≤ (Work.Spaces.Dz g z θ) ^ 2 * Work.Spaces.w z :=
          mul_le_mul_of_nonneg_left hwm (sq_nonneg _)
      _ ≤ (Work.Spaces.Dz g z θ) ^ 2 * (Work.Spaces.w z
            * (Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) :=
          mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
  rw [← dzIter_mul_div_sq (η := Work.Spaces.eta) z θ g hs0] at hA
  exact le_trans hA (slot_z_le_HkIntegrand α 4 g z θ 1 (by norm_num))

/-! ## The explicit shapes of `F_*` and its two first derivatives -/

theorem Fstar_shape {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    (∀ z : ℝ, 0 ≤ z → ∀ θ ∈ Work.Spaces.Iθ,
        |Work.Construction.Fstar α z θ| ≤ 20 * α * (z / (1 + z) ^ 2)) ∧
    (∀ z : ℝ, 0 ≤ z → ∀ θ ∈ Work.Spaces.Iθ,
        |Work.Spaces.Dth (Work.Construction.Fstar α) z θ| ≤ 40 * α ^ 2 * (z / (1 + z) ^ 2)) ∧
    (∀ z : ℝ, 0 ≤ z → ∀ θ ∈ Work.Spaces.Iθ,
        |Work.Spaces.Dz (Work.Construction.Fstar α) z θ| ≤ 40 * α * (z / (1 + z) ^ 2)) := by
  obtain ⟨hc1, hc2⟩ := Work.Spaces.c_bounds α hα hα1
  have hc0 : 0 < Work.Spaces.c α := by linarith
  have hzc : ∀ z : ℝ, 0 ≤ z → 0 ≤ z / (1 + z) ^ 2 := fun z hz =>
    div_nonneg hz (by positivity)
  have h2zc : ∀ z : ℝ, 0 ≤ z → 0 ≤ 2 * z / (1 + z) ^ 2 := fun z hz => by
    rw [show 2 * z / (1 + z) ^ 2 = 2 * (z / (1 + z) ^ 2) from by ring]
    exact mul_nonneg (by norm_num) (hzc z hz)
  have hGc : ∀ θ ∈ Work.Spaces.Iθ, Work.Spaces.Gam α θ / Work.Spaces.c α ≤ 10 := by
    intro θ hθ
    obtain ⟨hG0, hG1⟩ := Work.Spaces.Gam_bounds α θ hα hθ
    rw [div_le_iff₀ hc0]; nlinarith
  have hdth_bound : ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ| ≤ α * (4 / 3) := by
    intro θ hθ
    rcases eq_or_lt_of_le hθ.1 with h0 | h0
    · rw [← h0]
      simp only [Work.Spaces.dthU]
      rw [show 2 * (0:ℝ) = 0 from by ring, Real.sin_zero, zero_mul, abs_zero]
      positivity
    rcases lt_or_eq_of_le hθ.2 with h1 | h1
    · rw [Work.Spaces.dthU_Gam α θ hα ⟨h0, h1⟩]
      have hq : |Work.Spaces.qfun θ| ≤ 4 / 3 := by
        rw [Work.Spaces.qfun, abs_le]
        constructor <;> linarith [Real.neg_one_le_cos (2 * θ), Real.cos_le_one (2 * θ)]
      obtain ⟨hG0, hG1⟩ := Work.Spaces.Gam_bounds α θ hα hθ
      rw [abs_mul, abs_mul, abs_of_pos hα, abs_of_nonneg hG0]
      calc α * |Work.Spaces.qfun θ| * Work.Spaces.Gam α θ ≤ α * (4 / 3) * 1 :=
            mul_le_mul (mul_le_mul_of_nonneg_left hq hα.le) hG1 hG0 (by positivity)
        _ = α * (4 / 3) := by ring
    · rw [h1]
      simp only [Work.Spaces.dthU]
      rw [show 2 * (Real.pi / 2) = Real.pi from by ring, Real.sin_pi, zero_mul, abs_zero]
      positivity
  refine ⟨?_, ?_, ?_⟩
  · intro z hz θ hθ
    obtain ⟨hG0, hG1⟩ := Work.Spaces.Gam_bounds α θ hα hθ
    have h2 := h2zc z hz
    have h3 : (0 : ℝ) ≤ α * (Work.Spaces.Gam α θ / Work.Spaces.c α) :=
      mul_nonneg hα.le (div_nonneg hG0 hc0.le)
    have hfac : Work.Construction.Fstar α z θ
        = α * (Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z / (1 + z) ^ 2) := by
      simp only [Work.Construction.Fstar, Work.FM.Fstar]
    rw [hfac, abs_of_nonneg (mul_nonneg h3 h2)]
    calc α * (Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z / (1 + z) ^ 2)
        ≤ α * 10 * (2 * z / (1 + z) ^ 2) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hGc θ hθ) hα.le) h2
      _ = 20 * α * (z / (1 + z) ^ 2) := by ring
  · intro z hz θ hθ
    have hshape : (0 : ℝ) ≤ z / (1 + z) ^ 2 := hzc z hz
    have hfac : Work.Spaces.Dth (Work.Construction.Fstar α) z θ
        = (α * (2 * z / (1 + z) ^ 2) / Work.Spaces.c α)
            * Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ := by
      simp only [Work.Spaces.Dth, Work.Spaces.pth, Work.Spaces.dthU, Work.Construction.Fstar,
        Work.FM.Fstar]
      rw [show (fun θ' => α * (Work.Spaces.Gam α θ' / Work.Spaces.c α)
            * (2 * z / (1 + z) ^ 2))
          = fun θ' => (α * (2 * z / (1 + z) ^ 2) / Work.Spaces.c α)
              * Work.Spaces.Gam α θ' from by funext θ'; ring]
      rw [Work.FTS.Nonlinear.Pieces.RowsN0Aux.deriv_const_mul']
      ring
    rw [hfac, abs_mul]
    have h1 : |α * (2 * z / (1 + z) ^ 2) / Work.Spaces.c α| ≤ 20 * α * (z / (1 + z) ^ 2) := by
      rw [abs_div, abs_of_pos hc0, div_le_iff₀ hc0]
      have habs : |α * (2 * z / (1 + z) ^ 2)| = 2 * α * (z / (1 + z) ^ 2) := by
        rw [abs_of_nonneg (mul_nonneg hα.le (h2zc z hz))]; ring
      rw [habs]
      nlinarith [mul_nonneg hα.le hshape, hc1]
    refine le_trans (mul_le_mul h1 (hdth_bound θ hθ) (abs_nonneg _) (by positivity)) ?_
    nlinarith [mul_nonneg hα.le hshape, hα.le, sq_nonneg α]
  · intro z hz θ hθ
    obtain ⟨hG0, hG1⟩ := Work.Spaces.Gam_bounds α θ hα hθ
    have hshape : (0 : ℝ) ≤ z / (1 + z) ^ 2 := hzc z hz
    have hfac : Work.Spaces.Dz (Work.Construction.Fstar α) z θ
        = z * (α * (Work.Spaces.Gam α θ / Work.Spaces.c α))
            * deriv (fun z' => Work.FM.Fstar z') z := by
      rw [Work.Spaces.Dz, Work.Spaces.pz]
      rw [show (fun z' => Work.Construction.Fstar α z' θ)
          = fun z' => (α * (Work.Spaces.Gam α θ / Work.Spaces.c α)) * Work.FM.Fstar z' from by
            funext z'; simp only [Work.Construction.Fstar]]
      rw [Work.FTS.Nonlinear.Pieces.RowsN0Aux.deriv_const_mul']
      ring
    have hd : |deriv (fun z' => Work.FM.Fstar z') z| ≤ 2 / (1 + z) ^ 2 := by
      rw [Work.FM.deriv_Fstar z (by linarith)]
      have h1 : |1 - z| ≤ 1 + z := by
        rw [abs_le]; constructor <;> linarith
      rw [abs_div, abs_of_nonneg (pow_nonneg (by linarith : (0 : ℝ) ≤ 1 + z) 3),
        abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), div_le_iff₀ (by positivity)]
      calc 2 * |1 - z| ≤ 2 * (1 + z) := by linarith
        _ = 2 / (1 + z) ^ 2 * (1 + z) ^ 3 := by field_simp; try ring
    have h1 : abs α * abs (Work.Spaces.Gam α θ / Work.Spaces.c α) ≤ 10 * α := by
      have h2 : abs (Work.Spaces.Gam α θ / Work.Spaces.c α) ≤ 10 := by
        rw [abs_of_nonneg (div_nonneg hG0 hc0.le)]
        exact hGc θ hθ
      calc abs α * abs (Work.Spaces.Gam α θ / Work.Spaces.c α) = α * abs (Work.Spaces.Gam α θ / Work.Spaces.c α) := by
            rw [abs_of_pos hα]
        _ ≤ α * 10 := mul_le_mul_of_nonneg_left h2 hα.le
        _ = 10 * α := by ring
    rw [hfac, abs_mul, abs_mul, abs_mul, abs_of_nonneg hz]
    refine le_trans (mul_le_mul (mul_le_mul_of_nonneg_left h1 hz) hd (abs_nonneg _)
      (by positivity)) ?_
    rw [show z * (10 * α) * (2 / (1 + z) ^ 2) = 20 * α * (z / (1 + z) ^ 2) from by
      field_simp; ring]
    nlinarith [hshape, hα.le]

/-! ## `rl2`: the zero mode of `3 D_θg/(1+z)` -/

theorem rl2_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g : ℝ → ℝ → ℝ}, 0 < α → α ≤ 1 →
      Work.FTS.LocData.SmoothQuad g → Work.Spaces.HkMem α 4 g →
      |Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth g z θ / (1 + z)) 0|
        ≤ K * Work.FTS.Nonlin.Xn α g := by
  refine ⟨9, by norm_num, ?_⟩
  intro α g hα hα1 hsq hmem
  set f : ℝ → ℝ → ℝ := fun z θ => 3 * Work.Spaces.Dth g z θ / (1 + z) with hf
  have hDth : Work.FTS.LocData.SmoothQuad (Work.Spaces.Dth g) := by
    simpa only [Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero] using hsq.DthIter 1
  have hc : ContinuousOn (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    have h1 : ContinuousOn (Function.uncurry (Work.Spaces.Dth g))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := continuousOn_uncurry_of_smoothQuad hDth
    have h2 : ContinuousOn (fun p : ℝ × ℝ => 3 / (1 + p.1))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
      refine ContinuousOn.div continuousOn_const
        (continuousOn_const.add continuous_fst.continuousOn) ?_
      intro p hp
      have hp1 : 0 < p.1 := hp.1
      exact ne_of_gt (by positivity)
    have h3 : ContinuousOn (fun p : ℝ × ℝ =>
        (3 / (1 + p.1)) * Function.uncurry (Work.Spaces.Dth g) p)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := h2.mul h1
    refine h3.congr (fun p hp => ?_)
    simp only [Function.uncurry, hf]
    ring
  have hsl : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      MeasureTheory.IntegrableOn (fun θ => f r θ ^ 2) Work.Spaces.Iθ := by
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun r hr => ?_)
    have haesm : MeasureTheory.AEStronglyMeasurable (fun θ => f r θ ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      Work.Spaces.aesm_slice_of_continuousOn_Qd (fun p : ℝ × ℝ => f p.1 p.2 ^ 2)
        (by change ContinuousOn (fun p : ℝ × ℝ => (Function.uncurry f p) ^ 2) _
            exact hc.pow 2) hr
    refine MeasureTheory.Integrable.mono'
      ((hmem.1 r (Set.mem_Ici.mpr (le_of_lt hr))).const_mul 9) haesm ?_
    have hIoo2 : MeasureTheory.volume.restrict Work.Spaces.Iθ
        = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) :=
      MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc.symm
    rw [hIoo2]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    have hsqle : (Work.Spaces.Dth g r θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g r θ :=
      dth_sq_le_HkIntegrand α g hα hr hθ
    have hfe : f r θ = (3 / (1 + r)) * Work.Spaces.Dth g r θ := by rw [hf]; ring
    have h3 : (3 / (1 + r)) ^ 2 ≤ 9 := by
      have hr' : (0 : ℝ) < 1 + r := by linarith [Set.mem_Ioi.mp hr]
      rw [div_pow, div_le_iff₀ (pow_pos hr' 2)]
      nlinarith [sq_nonneg r, le_of_lt (Set.mem_Ioi.mp hr)]
    rw [Real.norm_of_nonneg (sq_nonneg _), hfe, mul_pow]
    exact mul_le_mul h3 hsqle (sq_nonneg _) (by norm_num)
  have hbd : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      (∫ θ in Work.Spaces.Iθ, f r θ ^ 2) * ((1 + r) / r) ^ 2
        ≤ 9 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g r θ := by
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun r hr => ?_)
    have hslice := (slice_energy_le_HkIntegrand α g hα hα1 hmem).1 r hr
    have hint : (∫ θ in Work.Spaces.Iθ, f r θ ^ 2)
        = (3 / (1 + r)) ^ 2 * ∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dth g r θ) ^ 2 := by
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
      rw [hf]; ring
    have h3 : (3 / (1 + r)) ^ 2 ≤ 9 := by
      have hr' : (0 : ℝ) < 1 + r := by linarith [Set.mem_Ioi.mp hr]
      rw [div_pow, div_le_iff₀ (pow_pos hr' 2)]
      nlinarith [sq_nonneg r, le_of_lt (Set.mem_Ioi.mp hr)]
    have hnn : (0 : ℝ) ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g r θ :=
      integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 4 g r θ
    calc (∫ θ in Work.Spaces.Iθ, f r θ ^ 2) * ((1 + r) / r) ^ 2
        = (3 / (1 + r)) ^ 2 * ((∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dth g r θ) ^ 2)
            * ((1 + r) / r) ^ 2) := by rw [hint]; ring
      _ ≤ (3 / (1 + r)) ^ 2 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g r θ :=
          mul_le_mul_of_nonneg_left hslice (sq_nonneg _)
      _ ≤ 9 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g r θ :=
          mul_le_mul_of_nonneg_right h3 hnn
  have hΦint : MeasureTheory.IntegrableOn
      (fun z => 9 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ)
      (Set.Ioi (0 : ℝ)) :=
    (hmem.2.mono_set Set.Ioi_subset_Ici_self).const_mul 9
  have hmain := L12_zero_le_of_weight_bound hsl
    (aesm_weighted_energy_of_continuousOn hc) hΦint hbd
  have hsqeval : (∫ r in Set.Ioi (0 : ℝ),
        9 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g r θ)
      = 9 * Work.Spaces.HkSq α 4 g := by
    rw [MeasureTheory.integral_const_mul, Work.Spaces.HkSq]
    congr 1
    exact MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))
  have hsqrt : Real.sqrt (∫ r in Set.Ioi (0 : ℝ),
        9 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g r θ)
      = 3 * Work.FTS.Nonlin.Xn α g := by
    rw [hsqeval, Work.FTS.Nonlin.Xn]
    congr 1
    have h1 : (3 * Work.Spaces.HkNorm α 4 g) ^ 2 = 9 * Work.Spaces.HkSq α 4 g := by
      rw [Work.Spaces.HkNorm, mul_pow, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 4 g)]
      norm_num
    rw [← h1]
    exact Real.sqrt_sq (mul_nonneg (by norm_num) (Work.Spaces.HkNorm_nonneg α 4 g))
  calc |Work.Construction.L12 f 0|
      ≤ 3 * Real.sqrt (∫ r in Set.Ioi (0 : ℝ),
          9 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g r θ) := hmain
    _ = 3 * (3 * Work.FTS.Nonlin.Xn α g) := by rw [hsqrt]
    _ = 9 * Work.FTS.Nonlin.Xn α g := by ring

/-! ## A pointwise (sup) bound for `L₁₂(g)` -/

theorem supAbs_L12_le {α : ℝ} {g : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hsm : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 4 g) :
    ∀ z : ℝ, 0 ≤ z → |Work.Construction.L12 g z| ≤ 3 * Work.FTS.Nonlin.Xn α g := by
  intro z hz
  have hslice0 : ∀ r : ℝ, 0 < r →
      MeasureTheory.IntegrableOn (fun θ : ℝ => (g r θ) ^ 2) Work.Spaces.Iθ :=
    fun r hr => Work.FTS.H2.l12q_slice_sq_integrableOn α g hsm hmem hr
  have hdens : ∀ r : ℝ, 0 < r → |Work.Elliptic.L12dens g r|
      ≤ Real.sqrt 3 * Real.sqrt (∫ θ in Work.Spaces.Iθ, (g r θ) ^ 2) / r :=
    fun r hr => Work.FTS.H2.l12q_l12dens_slice g hr (hslice0 r hr)
  have hIoi_meas := Work.FTS.H2.l12q_phi_aesm g hsm
  have hZ : Work.Construction.L12 g z
      = ∫ r, Work.Elliptic.L12dens g r ∂(MeasureTheory.volume.restrict (Set.Ioi z)) := rfl
  rw [hZ]
  set μ : MeasureTheory.Measure ℝ := MeasureTheory.volume.restrict (Set.Ioi z) with hμdef
  have hsub : Set.Ioi z ⊆ Set.Ioi (0 : ℝ) := Set.Ioi_subset_Ioi hz
  -- the two factors of Cauchy–Schwarz
  set A : ℝ → ℝ := fun r => Real.sqrt 3 * Real.sqrt (∫ θ in Work.Spaces.Iθ, (g r θ) ^ 2)
      * ((1 + r) / r) with hAdef
  set B : ℝ → ℝ := fun r => 1 / (1 + r) with hBdef
  have hAe0 : ∀ᵐ r ∂μ, 0 ≤ A r := by
    filter_upwards [MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume) measurableSet_Ioi]
      with r hr
    rw [hAdef]
    have hr' : (0 : ℝ) < r := lt_of_le_of_lt hz hr
    exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg _))
      (div_nonneg (by linarith) (le_of_lt hr'))
  have hBe0 : ∀ᵐ r ∂μ, 0 ≤ B r := by
    filter_upwards [MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume) measurableSet_Ioi]
      with r hr
    rw [hBdef]
    have hr' : (0 : ℝ) < r := lt_of_le_of_lt hz hr
    exact div_nonneg zero_le_one (by linarith)
  have hAmeas : MeasureTheory.AEStronglyMeasurable A μ := by
    rw [hμdef, hAdef]
    have h1 : MeasureTheory.AEStronglyMeasurable
        (fun r : ℝ => Real.sqrt 3 * Real.sqrt (∫ θ in Work.Spaces.Iθ, (g r θ) ^ 2))
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
      aestronglyMeasurable_const.mul (Real.continuous_sqrt.comp_aestronglyMeasurable hIoi_meas)
    have h2 : MeasureTheory.AEStronglyMeasurable (fun r : ℝ => (1 + r) / r)
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
      (ContinuousOn.div (continuousOn_const.add continuousOn_id) continuousOn_id
        (fun r hr => ne_of_gt hr)).aestronglyMeasurable measurableSet_Ioi
    exact (h1.mul h2).mono_measure (MeasureTheory.Measure.restrict_mono_set _ hsub)
  have hA2 : MeasureTheory.Integrable (fun r => A r ^ 2) μ := by
    rw [hμdef]
    refine (MeasureTheory.Integrable.mono_measure
      ((Work.FTS.H2.l12q_phiWeight_integrable α g hsm hmem).const_mul 3)
      (MeasureTheory.Measure.restrict_mono_set _ hsub)).congr ?_
    filter_upwards with r
    rw [hAdef, mul_pow, mul_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num),
      Real.sq_sqrt (MeasureTheory.integral_nonneg fun θ => sq_nonneg _)]
    ring
  have hmemA : MeasureTheory.MemLp A 2 μ :=
    (MeasureTheory.memLp_two_iff_integrable_sq hAmeas).mpr hA2
  obtain ⟨hB_int, hB_le⟩ := Work.FTS.H2.InvOneAddSq
  have hBmeas : MeasureTheory.AEStronglyMeasurable B μ := by
    rw [hμdef, hBdef]
    have h2 : MeasureTheory.AEStronglyMeasurable (fun r : ℝ => 1 / (1 + r))
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
      (ContinuousOn.div continuousOn_const (continuousOn_const.add continuousOn_id)
        (fun r hr => by
          have hr' : (0 : ℝ) < r := Set.mem_Ioi.mp hr
          exact ne_of_gt (by show (0 : ℝ) < 1 + r; linarith))).aestronglyMeasurable
        measurableSet_Ioi
    exact h2.mono_measure (MeasureTheory.Measure.restrict_mono_set _ hsub)
  have hB2 : MeasureTheory.Integrable (fun r => B r ^ 2) μ := by
    rw [hμdef]
    refine (MeasureTheory.Integrable.mono_measure hB_int
      (MeasureTheory.Measure.restrict_mono_set _ hsub)).congr ?_
    filter_upwards with r
    rw [hBdef]
  have hmemB : MeasureTheory.MemLp B 2 μ :=
    (MeasureTheory.memLp_two_iff_integrable_sq hBmeas).mpr hB2
  have hbd : ∀ᵐ r ∂μ, |Work.Elliptic.L12dens g r| ≤ A r * B r := by
    filter_upwards [MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume) measurableSet_Ioi]
      with r hr
    have hr' : (0 : ℝ) < r := lt_of_le_of_lt hz hr
    have h5' : |Work.Elliptic.L12dens g r|
        ≤ Real.sqrt 3 * Real.sqrt (∫ θ in Work.Spaces.Iθ, (g r θ) ^ 2) * r⁻¹ := by
      simpa only [div_eq_mul_inv] using hdens r hr'
    have hkey : ((1 + r) / r) * (1 / (1 + r)) = r⁻¹ := by
      have hr0 : r ≠ 0 := ne_of_gt hr'
      have h1r : (1 : ℝ) + r ≠ 0 := by linarith
      field_simp
    rw [hAdef, hBdef]
    dsimp only
    calc |Work.Elliptic.L12dens g r|
        ≤ Real.sqrt 3 * Real.sqrt (∫ θ in Work.Spaces.Iθ, (g r θ) ^ 2) * r⁻¹ := h5'
      _ = Real.sqrt 3 * Real.sqrt (∫ θ in Work.Spaces.Iθ, (g r θ) ^ 2)
            * (((1 + r) / r) * (1 / (1 + r))) := by rw [hkey]
      _ = Real.sqrt 3 * Real.sqrt (∫ θ in Work.Spaces.Iθ, (g r θ) ^ 2)
            * ((1 + r) / r) * (1 / (1 + r)) := by ring
  have hcs := Work.FTS.H2.CS1D (μ := μ) (g := fun r => Work.Elliptic.L12dens g r)
    hmemA hmemB hAe0 hBe0 hbd
  -- the two `L²` norms
  have hA2le : ∫ r, A r ^ 2 ∂μ ≤ 3 * Work.Spaces.HkSq α 4 g := by
    have hcongr : ∫ r, A r ^ 2 ∂μ = ∫ r in Set.Ioi z,
        3 * ((∫ θ in Work.Spaces.Iθ, (g r θ) ^ 2) * ((1 + r) / r) ^ 2) := by
      rw [hμdef]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun r hr => ?_)
      rw [hAdef, mul_pow, mul_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num),
        Real.sq_sqrt (MeasureTheory.integral_nonneg fun θ => sq_nonneg _)]
      ring
    rw [hcongr]
    have h1 : (∫ r in Set.Ioi z,
          3 * ((∫ θ in Work.Spaces.Iθ, (g r θ) ^ 2) * ((1 + r) / r) ^ 2))
        ≤ ∫ r in Set.Ioi (0 : ℝ),
          3 * ((∫ θ in Work.Spaces.Iθ, (g r θ) ^ 2) * ((1 + r) / r) ^ 2) :=
      MeasureTheory.setIntegral_mono_set
        ((Work.FTS.H2.l12q_phiWeight_integrable α g hsm hmem).const_mul 3)
        (Filter.Eventually.of_forall fun r => by positivity)
        (Filter.Eventually.of_forall fun r hr => hsub hr)
    refine h1.trans ?_
    rw [MeasureTheory.integral_const_mul]
    exact mul_le_mul_of_nonneg_left (Work.FTS.H2.l12q_phiWeight_le α g hmem) (by norm_num)
  have hB2le : ∫ r, B r ^ 2 ∂μ ≤ 2 := by
    show (∫ r in Set.Ioi z, (1 / (1 + r)) ^ 2) ≤ 2
    exact (MeasureTheory.setIntegral_mono_set hB_int
      (Filter.Eventually.of_forall fun r => sq_nonneg _)
      (Filter.Eventually.of_forall fun r hr => hsub hr)).trans hB_le
  have hfinal : |Work.Elliptic.L12 g z| ≤ Real.sqrt (3 * Work.Spaces.HkSq α 4 g) * Real.sqrt 2 := by
    refine hcs.trans ?_
    exact mul_le_mul (Real.sqrt_le_sqrt hA2le) (Real.sqrt_le_sqrt hB2le)
      (Real.sqrt_nonneg (∫ r, B r ^ 2 ∂μ)) (Real.sqrt_nonneg _)
  have hsqrt : Real.sqrt (3 * Work.Spaces.HkSq α 4 g) * Real.sqrt 2
      = Real.sqrt 6 * Work.Spaces.HkNorm α 4 g := by
    rw [Real.sqrt_mul (show (0 : ℝ) ≤ 3 by norm_num) (Work.Spaces.HkSq α 4 g),
      Work.Spaces.HkNorm]
    rw [show Real.sqrt 3 * Real.sqrt (Work.Spaces.HkSq α 4 g) * Real.sqrt 2
        = (Real.sqrt 3 * Real.sqrt 2) * Real.sqrt (Work.Spaces.HkSq α 4 g) from by ring]
    rw [show Real.sqrt 3 * Real.sqrt 2 = Real.sqrt 6 from by
      rw [← Real.sqrt_mul (show (0 : ℝ) ≤ 3 by norm_num) (2 : ℝ)]
      norm_num]
  have h6le : Real.sqrt 6 ≤ 3 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num), Real.sqrt_nonneg 6]
  calc |Work.Elliptic.L12 g z|
      ≤ Real.sqrt (3 * Work.Spaces.HkSq α 4 g) * Real.sqrt 2 := hfinal
    _ = Real.sqrt 6 * Work.Spaces.HkNorm α 4 g := hsqrt
    _ ≤ 3 * Work.Spaces.HkNorm α 4 g :=
        mul_le_mul_of_nonneg_right h6le (Work.Spaces.HkNorm_nonneg α 4 g)
    _ = 3 * Work.FTS.Nonlin.Xn α g := rfl

private lemma abs_mul_le_mul' {a c b d : ℝ} (h1 : |a| ≤ b) (h2 : |c| ≤ d) (hb : 0 ≤ b)
    (hd : 0 ≤ d) : |a * c| ≤ b * d := by
  rw [abs_mul]
  exact mul_le_mul h1 h2 (abs_nonneg _) hb

/-! ## Continuity of the factors of `N₀` on the open quadrant

The zero-mode estimate `rl0` needs the weighted angular energy of `N₀` to be a.e. strongly
measurable and its `θ`-slices integrable.  Both follow from the joint continuity of
`(z,θ) ↦ N₀(z,θ)` on the open quadrant, which the lemmas below establish.  The only
non-elementary input is the continuity of `z ↦ L₁₂ g z`: it is the interface field
`N4Norm.l12diff` (the density `L₁₂dens g` lies in `L¹((0,∞))`, so `L₁₂ g` is its primitive).
-/

/-- `(0,∞) × (0,π/2) ⊆ quadU`: the open quadrant of `N₄` sits inside the strip on which
`SmoothQuad` is stated. -/
theorem Ioi_prod_Ioo_subset_quadU :
    (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)) ⊆ Work.Spaces.quadU := by
  intro p hp
  simp only [Work.Spaces.quadU, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] at hp ⊢
  exact ⟨by linarith [hp.1], hp.2⟩

/-- `L₁₂ g` is continuous on `(0,∞)` for `SmoothQuad g`, `HkMem α 4 g` and `α ∈ (0,α₂]`. -/
theorem continuousOn_L12_of_N4Norm {Ci α₂ α : ℝ} {g : ℝ → ℝ → ℝ}
    (hN : Work.FTS.Nonlin.N4Norm Ci α₂) (hαI : α ∈ Set.Ioc 0 α₂)
    (hsq : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 4 g) :
    ContinuousOn (fun z => Work.Construction.L12 g z) (Set.Ioi 0) :=
  DifferentiableOn.continuousOn
    (fun z hz => (hN.l12diff α hαI g hsq hmem z hz).differentiableWithinAt)

/-- `L₁₂(F_*) = 2α/(1+z)` on `z > 0`, hence continuous there. -/
theorem continuousOn_L12_Fstar {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ContinuousOn (fun z => Work.Construction.L12 (Work.Construction.Fstar α) z) (Set.Ioi 0) := by
  refine ContinuousOn.congr (f := fun z : ℝ => 2 * α / (1 + z)) ?_ (fun z hz => ?_)
  · exact continuousOn_const.div (continuousOn_const.add continuousOn_id) (fun z hz => by
      have h := Set.mem_Ioi.mp hz
      linarith)
  · exact Work.Construction.L12_Fstar_eq hα hα1 (le_of_lt (Set.mem_Ioi.mp hz))

/-- `∂_θ f` is continuous on the open quadrant for `SmoothQuad f`. -/
theorem continuousOn_uncurry_pth {f : ℝ → ℝ → ℝ} (h : Work.FTS.LocData.SmoothQuad f) :
    ContinuousOn (Function.uncurry (Work.Spaces.pth f)) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
  ((Work.FTS.LocData.contDiffOn_pth Work.FTS.LocData.isOpen_quadU h).continuousOn).mono
    Ioi_prod_Ioo_subset_quadU

/-- `∂_z f` is continuous on the open quadrant for `SmoothQuad f`. -/
theorem continuousOn_uncurry_pz {f : ℝ → ℝ → ℝ} (h : Work.FTS.LocData.SmoothQuad f) :
    ContinuousOn (Function.uncurry (Work.Spaces.pz f)) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
  ((Work.FTS.LocData.contDiffOn_pz Work.FTS.LocData.isOpen_quadU h).continuousOn).mono
    Ioi_prod_Ioo_subset_quadU

/-- **Joint continuity of the first two terms of `N₀`** (the `F_*`-quadratic part),
with `L₁₂(F_*)` replaced by its explicit value `2α/(1+z)`. -/
theorem continuousOn_uncurry_N0fix {α : ℝ} :
    ContinuousOn (fun p : ℝ × ℝ =>
      (3 / (2 * α)) * Work.Construction.s2 p.2
          * (2 * α / (1 + p.1)) * Work.Spaces.pth (Work.Construction.Fstar α) p.1 p.2
        - Work.Construction.c2m p.2 * (2 * α / (1 + p.1))
          * Work.Spaces.Dz (Work.Construction.Fstar α) p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  have hFsq : Work.FTS.LocData.SmoothQuad (Work.Construction.Fstar α) :=
    Work.FTS.LocData.Fstar_smoothQuad α
  have hpthF : ContinuousOn (Function.uncurry (Work.Spaces.pth (Work.Construction.Fstar α)))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := continuousOn_uncurry_pth hFsq
  have hpzF : ContinuousOn (Function.uncurry (Work.Spaces.pz (Work.Construction.Fstar α)))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := continuousOn_uncurry_pz hFsq
  have hsin : ContinuousOn (fun p : ℝ × ℝ => Work.Construction.s2 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    simp only [Work.Construction.s2]
    exact (Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn
  have hc2m : ContinuousOn (fun p : ℝ × ℝ => Work.Construction.c2m p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    simp only [Work.Construction.c2m]
    exact (((Real.continuous_cos.comp (continuous_const.mul continuous_snd)).sub
      ((Real.continuous_sin.comp continuous_snd).pow 2))).continuousOn
  have hz : ContinuousOn (fun p : ℝ × ℝ => 2 * α / (1 + p.1))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    continuousOn_const.div (continuousOn_const.add continuousOn_fst) (fun p hp => by
      have h := Set.mem_Ioi.mp hp.1; linarith)
  have h1 : ContinuousOn (fun p : ℝ × ℝ =>
      (3 / (2 * α)) * Work.Construction.s2 p.2 * (2 * α / (1 + p.1))
        * Work.Spaces.pth (Work.Construction.Fstar α) p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    refine ((((continuousOn_const : ContinuousOn (fun _ : ℝ × ℝ => (3 / (2 * α)))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))).mul hsin).mul hz).mul hpthF).congr ?_
    intro p hp; simp only [Function.uncurry, Pi.mul_apply]
  have h2 : ContinuousOn (fun p : ℝ × ℝ =>
      Work.Construction.c2m p.2 * (2 * α / (1 + p.1))
        * Work.Spaces.Dz (Work.Construction.Fstar α) p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    refine ((hc2m.mul hz).mul (continuousOn_fst.mul hpzF)).congr ?_
    intro p hp; simp only [Function.uncurry, Work.Spaces.Dz, Pi.mul_apply]
  refine (h1.sub h2).congr ?_
  intro p hp; simp only [Pi.sub_apply]

/-- **Joint continuity of `N₀`** on the open quadrant, for `SmoothQuad g` with `HkMem α 4 g`. -/
theorem continuousOn_uncurry_N0 {Ci α₂ α : ℝ} {g : ℝ → ℝ → ℝ}
    (hN : Work.FTS.Nonlin.N4Norm Ci α₂) (hαI : α ∈ Set.Ioc 0 α₂) (hα1 : α ≤ 1)
    (hsq : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 4 g) :
    ContinuousOn (Function.uncurry (Work.Construction.N0 α (Work.Construction.Ftot α g) g))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  have hFsq : Work.FTS.LocData.SmoothQuad (Work.Construction.Fstar α) :=
    Work.FTS.LocData.Fstar_smoothQuad α
  have hTsq : Work.FTS.LocData.SmoothQuad (Work.Construction.Ftot α g) :=
    Work.FTS.LocData.smoothQuad_add hFsq hsq
  have hLg : ContinuousOn (fun z => Work.Construction.L12 g z) (Set.Ioi 0) :=
    continuousOn_L12_of_N4Norm hN hαI hsq hmem
  have hLF : ContinuousOn (fun z => Work.Construction.L12 (Work.Construction.Fstar α) z)
      (Set.Ioi 0) := continuousOn_L12_Fstar hαI.1 hα1
  have hpthg : ContinuousOn (Function.uncurry (Work.Spaces.pth g))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := continuousOn_uncurry_pth hsq
  have hpzg : ContinuousOn (Function.uncurry (Work.Spaces.pz g))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := continuousOn_uncurry_pz hsq
  have hpthF : ContinuousOn (Function.uncurry (Work.Spaces.pth (Work.Construction.Fstar α)))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := continuousOn_uncurry_pth hFsq
  have hpzF : ContinuousOn (Function.uncurry (Work.Spaces.pz (Work.Construction.Fstar α)))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := continuousOn_uncurry_pz hFsq
  have hpthT : ContinuousOn (Function.uncurry (Work.Spaces.pth (Work.Construction.Ftot α g)))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := continuousOn_uncurry_pth hTsq
  have hpzT : ContinuousOn (Function.uncurry (Work.Spaces.pz (Work.Construction.Ftot α g)))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := continuousOn_uncurry_pz hTsq
  have hg : ContinuousOn (Function.uncurry g) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    continuousOn_uncurry_of_smoothQuad hsq
  have hsin : ContinuousOn (fun p : ℝ × ℝ => Work.Construction.s2 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    simp only [Work.Construction.s2]
    exact (Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn
  have hc2m : ContinuousOn (fun p : ℝ × ℝ => Work.Construction.c2m p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    simp only [Work.Construction.c2m]
    exact (((Real.continuous_cos.comp (continuous_const.mul continuous_snd)).sub
      ((Real.continuous_sin.comp continuous_snd).pow 2))).continuousOn
  have hLg' : ContinuousOn (fun p : ℝ × ℝ => Work.Construction.L12 g p.1)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    hLg.comp continuousOn_fst (fun p hp => hp.1)
  have hLF' : ContinuousOn (fun p : ℝ × ℝ => Work.Construction.L12 (Work.Construction.Fstar α) p.1)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    hLF.comp continuousOn_fst (fun p hp => hp.1)
  have h1 : ContinuousOn (fun p : ℝ × ℝ =>
      (3 / (2 * α)) * Work.Construction.s2 p.2
        * Work.Construction.L12 (Work.Construction.Fstar α) p.1
        * Work.Spaces.pth (Work.Construction.Fstar α) p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    refine ((((continuousOn_const : ContinuousOn (fun _ : ℝ × ℝ => (3 / (2 * α)))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))).mul hsin).mul hLF').mul hpthF).congr ?_
    intro p hp; simp only [Function.uncurry, Pi.mul_apply]
  have h2 : ContinuousOn (fun p : ℝ × ℝ =>
      Work.Construction.c2m p.2 * Work.Construction.L12 (Work.Construction.Fstar α) p.1
        * Work.Spaces.Dz (Work.Construction.Fstar α) p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    refine ((hc2m.mul hLF').mul (continuousOn_fst.mul hpzF)).congr ?_
    intro p hp; simp only [Function.uncurry, Work.Spaces.Dz, Pi.mul_apply]
  have h3 : ContinuousOn (fun p : ℝ × ℝ =>
      (1 / α) * Work.Construction.L12 g p.1 * g p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    refine (((continuousOn_const : ContinuousOn (fun _ : ℝ × ℝ => (1 / α))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))).mul hLg').mul hg).congr ?_
    intro p hp; simp only [Function.uncurry, Pi.mul_apply]
  have h4 : ContinuousOn (fun p : ℝ × ℝ =>
      (3 / (2 * α)) * Work.Construction.s2 p.2 * Work.Construction.L12 g p.1
        * Work.Spaces.pth (Work.Construction.Ftot α g) p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    refine ((((continuousOn_const : ContinuousOn (fun _ : ℝ × ℝ => (3 / (2 * α)))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))).mul hsin).mul hLg').mul hpthT).congr ?_
    intro p hp; simp only [Function.uncurry, Pi.mul_apply]
  have h5 : ContinuousOn (fun p : ℝ × ℝ =>
      Work.Construction.c2m p.2 * Work.Construction.L12 g p.1
        * Work.Spaces.Dz (Work.Construction.Ftot α g) p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    refine ((hc2m.mul hLg').mul (continuousOn_fst.mul hpzT)).congr ?_
    intro p hp; simp only [Function.uncurry, Work.Spaces.Dz, Pi.mul_apply]
  have h6 : ContinuousOn (fun p : ℝ × ℝ =>
      Work.Construction.c2m p.2 * Work.Construction.L12 (Work.Construction.Fstar α) p.1
        * Work.Spaces.Dz g p.1 p.2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    refine ((hc2m.mul hLF').mul (continuousOn_fst.mul hpzg)).congr ?_
    intro p hp; simp only [Function.uncurry, Work.Spaces.Dz, Pi.mul_apply]
  have key : ContinuousOn (fun p : ℝ × ℝ =>
      (3 / (2 * α)) * Work.Construction.s2 p.2
          * Work.Construction.L12 (Work.Construction.Fstar α) p.1
          * Work.Spaces.pth (Work.Construction.Fstar α) p.1 p.2
        - Work.Construction.c2m p.2 * Work.Construction.L12 (Work.Construction.Fstar α) p.1
          * Work.Spaces.Dz (Work.Construction.Fstar α) p.1 p.2
        + (1 / α) * Work.Construction.L12 g p.1 * g p.1 p.2
        + (3 / (2 * α)) * Work.Construction.s2 p.2 * Work.Construction.L12 g p.1
          * Work.Spaces.pth (Work.Construction.Ftot α g) p.1 p.2
        - Work.Construction.c2m p.2 * Work.Construction.L12 g p.1
          * Work.Spaces.Dz (Work.Construction.Ftot α g) p.1 p.2
        - Work.Construction.c2m p.2 * Work.Construction.L12 (Work.Construction.Fstar α) p.1
          * Work.Spaces.Dz g p.1 p.2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    refine ((((h1.sub h2).add h3).add h4).sub h5).sub h6 |>.congr ?_
    intro p hp
    simp only [Pi.sub_apply, Pi.add_apply]
  refine key.congr ?_
  intro p hp
  simp only [Function.uncurry, Work.Construction.N0]

/-! ## Weighted pointwise bounds for the `ℋ⁴`-integrand

The zero-mode estimate integrates the *weighted* angular energy `(∫_θ f²)·w` against the
`ℋ⁴`-integrand; the three pointwise bounds below (`g²w² ≤ HkIntegrand`, and the `D_θ`/`D_z`
versions with a single factor of `w`) are what converts the `sin(2θ)^{-η}`/`sin(2θ)^{-γ}`
weights present in `HkIntegrand` into the Hardy weight `w` of the `L₁₂`-estimate. -/

/-- `∫_θ c = (π/2)·c` over `Iθ`. -/
theorem integral_const_Iθ_ra (c : ℝ) : (∫ θ in Work.Spaces.Iθ, c) = c * (π / 2) := by
  rw [MeasureTheory.setIntegral_const, smul_eq_mul]
  have hvol : MeasureTheory.volume.real Work.Spaces.Iθ = π / 2 := by
    rw [MeasureTheory.measureReal_def, Work.Spaces.Iθ, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith [Real.pi_pos]), sub_zero]
  rw [hvol]
  ring

/-- `g z θ ^ 2 · w z ^ 2 ≤ HkIntegrand α 4 g z θ` on the open quadrant (the `i = 0` radial
slot of the integrand, using `sin(2θ)^{-η} ≥ 1`). -/
theorem g_sq_mul_w_sq_le_HkIntegrand (α : ℝ) (g : ℝ → ℝ → ℝ) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    (g z θ) ^ 2 * (Work.Spaces.w z) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
  have hs0 : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have heta : 1 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
    one_le_rpow_neg hs0 hs1 (le_of_lt Work.Spaces.eta_pos)
  have h := slot_z_le_HkIntegrand α 4 g z θ 0 (by norm_num)
  rw [Work.Spaces.DzIter_zero] at h
  have hsplit : (g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = (g z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    have hsin2 : ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))⁻¹ ^ 2
        = (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
      rw [← Real.rpow_neg hs0.le, ← Real.rpow_natCast, ← Real.rpow_mul hs0.le]
      ring_nf
    rw [div_eq_mul_inv, mul_pow, mul_pow, hsin2]
    ring
  rw [hsplit] at h
  calc (g z θ) ^ 2 * (Work.Spaces.w z) ^ 2
      = (g z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * 1 := by ring
    _ ≤ (g z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
        mul_le_mul_of_nonneg_left heta (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    _ ≤ Work.Spaces.HkIntegrand α 4 g z θ := h

/-- `(D_θ g z θ)² · w z ≤ HkIntegrand α 4 g z θ` on the open quadrant. -/
theorem dth_sq_mul_w_le_HkIntegrand (α : ℝ) (g : ℝ → ℝ → ℝ) (hα : 0 < α) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    (Work.Spaces.Dth g z θ) ^ 2 * Work.Spaces.w z ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
  have hs0 : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hwm : 1 ≤ Work.Spaces.w z := by
    rw [Work.Spaces.w, one_le_div (by positivity)]
    nlinarith
  have hsin : 1 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
    one_le_rpow_neg hs0 hs1 (by rw [Work.Spaces.gam]; linarith)
  have h2 : Work.Spaces.w z ≤ Work.Spaces.w z
      * (Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) :=
    mul_shape_le hwm hsin
  refine le_trans (mul_le_mul_of_nonneg_left h2 (sq_nonneg _)) ?_
  rw [← dth_mul_Wt_sq (α := α) g hs0]
  have h3 := slot_mixed_le_HkIntegrand α 4 g z θ 0 1 (by norm_num) (by norm_num)
  simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_succ,
    Work.Spaces.DthIter_zero] using h3

/-- `(D_z g z θ)² · w z ≤ HkIntegrand α 4 g z θ` on the open quadrant. -/
theorem dz_sq_mul_w_le_HkIntegrand (α : ℝ) (g : ℝ → ℝ → ℝ) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    (Work.Spaces.Dz g z θ) ^ 2 * Work.Spaces.w z ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
  have hs0 : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hwm : 1 ≤ Work.Spaces.w z := by
    rw [Work.Spaces.w, one_le_div (by positivity)]
    nlinarith
  have hsin : 1 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
    one_le_rpow_neg hs0 hs1 (le_of_lt Work.Spaces.eta_pos)
  have h2 : Work.Spaces.w z ≤ Work.Spaces.w z
      * (Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) :=
    mul_shape_le hwm hsin
  refine le_trans (mul_le_mul_of_nonneg_left h2 (sq_nonneg _)) ?_
  rw [← dzIter_mul_div_sq (η := Work.Spaces.eta) z θ g hs0]
  exact slot_z_le_HkIntegrand α 4 g z θ 1 (by norm_num)

/-- The exact cancellation `(r/(1+r)²)²·w r = (1/(1+r))²`. -/
private lemma sq_div_shape_eq {c r : ℝ} (hr : 0 < r) :
    c ^ 2 * (r / (1 + r) ^ 2) ^ 2 * Work.Spaces.w r = c ^ 2 * (1 / (1 + r)) ^ 2 := by
  rw [Work.Spaces.w]
  field_simp

/-- `√(a + b + c) ≤ √a + √b + √c` for nonnegative `a, b, c`. -/
private lemma sqrt_add_le_sum_sqrt {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    Real.sqrt (a + b + c) ≤ Real.sqrt a + Real.sqrt b + Real.sqrt c := by
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb, Real.sq_sqrt hc,
    Real.sqrt_nonneg a, Real.sqrt_nonneg b, Real.sqrt_nonneg c]

/-- The bound `(r²/(1+r)⁴)²·w r ≤ (1/(1+r))²`. -/
private lemma sq_div_shape_le {c r : ℝ} (hr : 0 < r) :
    c ^ 2 * (r ^ 2 / (1 + r) ^ 4) ^ 2 * Work.Spaces.w r ≤ c ^ 2 * (1 / (1 + r)) ^ 2 := by
  rw [Work.Spaces.w]
  have h1r : 0 < 1 + r := by linarith
  have h4 : r ^ 2 ≤ (1 + r) ^ 4 := by
    nlinarith [sq_nonneg r, sq_nonneg (1 + r), hr.le, sq_nonneg ((1 + r) ^ 2 - r)]
  have hgoal : r ^ 2 / (1 + r) ^ 6 ≤ (1 / (1 + r)) ^ 2 := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (1 + r) ^ 6)]
    have hsimp : (1 / (1 + r)) ^ 2 * (1 + r) ^ 6 = (1 + r) ^ 4 := by field_simp
    rw [hsimp]
    exact h4
  calc c ^ 2 * (r ^ 2 / (1 + r) ^ 4) ^ 2 * ((1 + r) ^ 2 / r ^ 2)
      = c ^ 2 * (r ^ 2 / (1 + r) ^ 6) := by field_simp
    _ ≤ c ^ 2 * (1 / (1 + r)) ^ 2 := mul_le_mul_of_nonneg_left hgoal (sq_nonneg _)

/-! ## `rl0`: the zero mode of `N₀` -/

theorem rl0_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ {Ci α₂ α : ℝ} {g : ℝ → ℝ → ℝ},
      0 < α → α ≤ 1 → Work.FTS.Nonlin.N4Norm Ci α₂ → α ≤ α₂ →
      Work.FTS.Nonlin.GalClass α g →
      |Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α g) g) 0|
        ≤ K * (α ^ 2 + Real.sqrt α * Work.FTS.Nonlin.Xn α g
            + α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2) := by
  refine ⟨10 ^ 5, by norm_num, ?_⟩
  intro Ci α₂ α g hα hα1 hN hαα₂ hg
  obtain ⟨hreg, hvanish, haxis, hdecay, hl12⟩ := hg
  have hmem : Work.Spaces.HkMem α 4 g :=
    (Work.FTS.GalerkinFix.RegQ.regQ_mono hreg (by norm_num)).2.1
  obtain ⟨hsq, hmem6, hbdry⟩ := hreg
  have hFsq : Work.FTS.LocData.SmoothQuad (Work.Construction.Fstar α) :=
    Work.FTS.LocData.Fstar_smoothQuad α
  obtain ⟨hc1, hc2⟩ := Work.Spaces.c_bounds α hα hα1
  have hc0 : 0 < Work.Spaces.c α := by linarith
  set X : ℝ := Work.FTS.Nonlin.Xn α g with hX
  have hX0 : 0 ≤ X := Work.Spaces.HkNorm_nonneg α 4 g
  set Ψ : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ with hΨ
  have hΨint : MeasureTheory.IntegrableOn Ψ (Set.Ioi (0 : ℝ)) := hmem.2.mono_set Set.Ioi_subset_Ici_self
  -- the two additivity identities on the quadrant
  have hI1 : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      Work.Construction.s2 θ * Work.Spaces.pth (Work.Construction.Ftot α g) z θ
        = Work.Spaces.Dth (Work.Construction.Fstar α) z θ + Work.Spaces.Dth g z θ := by
    intro z hz θ hθ
    have hz' : z ∈ Set.Ioi (-1 : ℝ) := by simp only [Set.mem_Ioi] at hz ⊢; linarith
    have hp : Work.Spaces.pth (Work.Construction.Ftot α g) z θ
        = Work.Spaces.pth (Work.Construction.Fstar α) z θ + Work.Spaces.pth g z θ :=
      Work.FTS.Nonlinear.Pieces.pth_add_of_smoothQuad hFsq hsq hz' hθ
    rw [hp]
    simp only [Work.Spaces.Dth, Work.Construction.s2]
    ring
  have hI2 : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      Work.Spaces.Dz (Work.Construction.Ftot α g) z θ
        = Work.Spaces.Dz (Work.Construction.Fstar α) z θ + Work.Spaces.Dz g z θ := by
    intro z hz θ hθ
    have hz' : z ∈ Set.Ioi (-1 : ℝ) := by simp only [Set.mem_Ioi] at hz ⊢; linarith
    have hp : Work.Spaces.pz (Work.Construction.Ftot α g) z θ
        = Work.Spaces.pz (Work.Construction.Fstar α) z θ + Work.Spaces.pz g z θ :=
      Work.FTS.Nonlinear.Pieces.pz_add_of_smoothQuad hFsq hsq hz' hθ
    rw [Work.Spaces.Dz, hp]
    simp only [Work.Spaces.Dz]
    ring
  -- the additivity identities and the pieces
  have hpth : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      Work.Spaces.pth (Work.Construction.Ftot α g) z θ
        = Work.Spaces.pth (Work.Construction.Fstar α) z θ + Work.Spaces.pth g z θ := by
    intro z hz θ hθ
    have hz' : z ∈ Set.Ioi (-1 : ℝ) := by simp only [Set.mem_Ioi] at hz ⊢; linarith
    exact Work.FTS.Nonlinear.Pieces.pth_add_of_smoothQuad hFsq hsq hz' hθ
  have hL12F : ∀ z : ℝ, 0 ≤ z →
      Work.Construction.L12 (Work.Construction.Fstar α) z = 2 * α / (1 + z) :=
    fun z hz => Work.Construction.L12_Fstar_eq hα hα1 hz
  have hL12g : ∀ z : ℝ, 0 ≤ z → |Work.Construction.L12 g z| ≤ 3 * X :=
    fun z hz => supAbs_L12_le hα hα1 hsq hmem z hz
  have hDthF : ∀ z : ℝ, 0 ≤ z → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.Dth (Work.Construction.Fstar α) z θ| ≤ 40 * α ^ 2 * (z / (1 + z) ^ 2) :=
    (Fstar_shape hα hα1).2.1
  have hDzF : ∀ z : ℝ, 0 ≤ z → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.Dz (Work.Construction.Fstar α) z θ| ≤ 40 * α * (z / (1 + z) ^ 2) :=
    (Fstar_shape hα hα1).2.2
  have hc2m : ∀ θ : ℝ, |Work.Construction.c2m θ| ≤ 2 := fun θ => by
    have hs1 : Real.sin θ ^ 2 ≤ 1 := by
      nlinarith [Real.sin_le_one θ, Real.neg_one_le_sin θ, sq_nonneg (Real.sin θ)]
    rw [Work.Construction.c2m, abs_le]
    constructor
    · nlinarith [Real.neg_one_le_cos (2 * θ), hs1]
    · nlinarith [Real.cos_le_one (2 * θ), sq_nonneg (Real.sin θ)]
  have hN0bd : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |(3 / (2 * α)) * Work.Construction.s2 θ * Work.Construction.L12 (Work.Construction.Fstar α) z
          * Work.Spaces.pth (Work.Construction.Fstar α) z θ
        - Work.Construction.c2m θ * Work.Construction.L12 (Work.Construction.Fstar α) z
          * Work.Spaces.Dz (Work.Construction.Fstar α) z θ|
        ≤ 160 * α ^ 2 * (z ^ 2 / (1 + z) ^ 4) := by
    intro z hz θ hθ
    have hz0 : 0 ≤ z := le_of_lt hz
    have h1z : 0 < 1 + z := by linarith
    have hden : 0 < Work.Spaces.c α * (1 + z) ^ 4 := mul_pos hc0 (pow_pos h1z 4)
    obtain ⟨hG0, hG1⟩ := Work.Spaces.Gam_bounds α θ hα ⟨hθ.1.le, hθ.2.le⟩
    have hnum : |8 * α ^ 2 * Work.Construction.c2m θ * z ^ 2 * Work.Spaces.Gam α θ|
        ≤ 16 * α ^ 2 * z ^ 2 := by
      have hΓ : |Work.Spaces.Gam α θ| ≤ 1 := by rw [abs_of_nonneg hG0]; exact hG1
      calc |8 * α ^ 2 * Work.Construction.c2m θ * z ^ 2 * Work.Spaces.Gam α θ|
          = 8 * α ^ 2 * |Work.Construction.c2m θ| * z ^ 2 * |Work.Spaces.Gam α θ| := by
            rw [show 8 * α ^ 2 * Work.Construction.c2m θ * z ^ 2 * Work.Spaces.Gam α θ
                = (8 * α ^ 2) * Work.Construction.c2m θ * z ^ 2 * Work.Spaces.Gam α θ
                  from by ring]
            simp only [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 8 * α ^ 2),
              abs_of_nonneg (sq_nonneg z)]
            try ring
        _ ≤ 8 * α ^ 2 * 2 * z ^ 2 * 1 := by
            calc 8 * α ^ 2 * |Work.Construction.c2m θ| * z ^ 2 * |Work.Spaces.Gam α θ|
                ≤ 8 * α ^ 2 * 2 * z ^ 2 * |Work.Spaces.Gam α θ| :=
                  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_left (hc2m θ) (by positivity)) (sq_nonneg z))
                    (abs_nonneg _)
              _ ≤ 8 * α ^ 2 * 2 * z ^ 2 * 1 := mul_le_mul_of_nonneg_left hΓ (by positivity)
        _ = 16 * α ^ 2 * z ^ 2 := by ring
    have hfin : 160 * α ^ 2 * (z ^ 2 / (1 + z) ^ 4) * (Work.Spaces.c α * (1 + z) ^ 4)
        = 160 * α ^ 2 * z ^ 2 * Work.Spaces.c α := by
      field_simp
      try ring
    rw [Work.Construction.N0_first_two_eq' (α := α) (z := z) (θ := θ) hα hα1 hz0
        ⟨hθ.1.le, hθ.2.le⟩,
      abs_div, abs_of_pos hden, div_le_iff₀ hden]
    rw [hfin]
    have hnn : (0 : ℝ) ≤ α ^ 2 * z ^ 2 := by positivity
    nlinarith [hnum, hc1, hnn, sq_nonneg α, sq_nonneg z, hα.le]
  -- the pieces of `N₀` (on the quadrant) and their pointwise square bounds
  have hP1sq : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      ((1 / α) * Work.Construction.L12 g z * g z θ) ^ 2
        ≤ ((9 * X / α) ^ 2) * Work.Spaces.HkIntegrand α 4 g z θ := by
    intro z hz θ hθ
    have h2 : |Work.Construction.L12 g z| ≤ 3 * X := hL12g z (le_of_lt hz)
    have h3 : (Work.Construction.L12 g z) ^ 2 ≤ (3 * X) ^ 2 := by
      nlinarith [h2, abs_nonneg (Work.Construction.L12 g z), sq_abs (Work.Construction.L12 g z)]
    have h4 : (1 / α) ^ 2 ≤ (3 / α) ^ 2 := by
      rw [div_pow, div_pow]
      exact div_le_div_of_nonneg_right (by norm_num : (1 : ℝ) ^ 2 ≤ 3 ^ 2) (by positivity)
    have h5 : (g z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
      g_sq_le_HkIntegrand α g hα hz hθ
    calc ((1 / α) * Work.Construction.L12 g z * g z θ) ^ 2
        = (1 / α) ^ 2 * (Work.Construction.L12 g z) ^ 2 * (g z θ) ^ 2 := by ring
      _ ≤ (3 / α) ^ 2 * (3 * X) ^ 2 * Work.Spaces.HkIntegrand α 4 g z θ := by
          refine mul_le_mul (mul_le_mul h4 h3 (sq_nonneg _) (by positivity)) h5 (sq_nonneg _)
            (by positivity)
      _ = ((9 * X / α) ^ 2) * Work.Spaces.HkIntegrand α 4 g z θ := by ring
  have hP2sq : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      ((3 / (2 * α)) * Work.Construction.L12 g z * Work.Spaces.Dth (Work.Construction.Fstar α) z θ) ^ 2
        ≤ (180 * α * X * (z / (1 + z) ^ 2)) ^ 2 := by
    intro z hz θ hθ
    have h2 : |Work.Construction.L12 g z| ≤ 3 * X := hL12g z (le_of_lt hz)
    have h3 : (Work.Construction.L12 g z) ^ 2 ≤ (3 * X) ^ 2 := by
      nlinarith [h2, abs_nonneg (Work.Construction.L12 g z), sq_abs (Work.Construction.L12 g z)]
    have h4 : (3 / (2 * α)) ^ 2 ≤ (3 / (2 * α)) ^ 2 := le_refl _
    have h5 : (Work.Spaces.Dth (Work.Construction.Fstar α) z θ) ^ 2
        ≤ (40 * α ^ 2 * (z / (1 + z) ^ 2)) ^ 2 := by
      have h := hDthF z (le_of_lt hz) θ ⟨hθ.1.le, hθ.2.le⟩
      nlinarith [h, abs_nonneg (Work.Spaces.Dth (Work.Construction.Fstar α) z θ),
        sq_abs (Work.Spaces.Dth (Work.Construction.Fstar α) z θ)]
    calc ((3 / (2 * α)) * Work.Construction.L12 g z * Work.Spaces.Dth (Work.Construction.Fstar α) z θ) ^ 2
        = (3 / (2 * α)) ^ 2 * (Work.Construction.L12 g z) ^ 2
          * (Work.Spaces.Dth (Work.Construction.Fstar α) z θ) ^ 2 := by ring
      _ ≤ (3 / (2 * α)) ^ 2 * (3 * X) ^ 2
            * (40 * α ^ 2 * (z / (1 + z) ^ 2)) ^ 2 := by
          refine mul_le_mul (mul_le_mul h4 h3 (sq_nonneg _) (by positivity)) h5 (sq_nonneg _)
            (by positivity)
      _ = (180 * α * X * (z / (1 + z) ^ 2)) ^ 2 := by
          field_simp
          ring
  have hP3sq : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      ((3 / (2 * α)) * Work.Construction.L12 g z * Work.Spaces.Dth g z θ) ^ 2
        ≤ ((9 * X / (2 * α)) ^ 2) * Work.Spaces.HkIntegrand α 4 g z θ := by
    intro z hz θ hθ
    have h2 : |Work.Construction.L12 g z| ≤ 3 * X := hL12g z (le_of_lt hz)
    have h3 : (Work.Construction.L12 g z) ^ 2 ≤ (3 * X) ^ 2 := by
      nlinarith [h2, abs_nonneg (Work.Construction.L12 g z), sq_abs (Work.Construction.L12 g z)]
    have h5 : (Work.Spaces.Dth g z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
      dth_sq_le_HkIntegrand α g hα hz hθ
    calc ((3 / (2 * α)) * Work.Construction.L12 g z * Work.Spaces.Dth g z θ) ^ 2
        = (3 / (2 * α)) ^ 2 * (Work.Construction.L12 g z) ^ 2 * (Work.Spaces.Dth g z θ) ^ 2 := by
          ring
      _ ≤ (3 / (2 * α)) ^ 2 * (3 * X) ^ 2 * Work.Spaces.HkIntegrand α 4 g z θ := by
          refine mul_le_mul (mul_le_mul (le_refl _) h3 (sq_nonneg _) (by positivity)) h5
            (sq_nonneg _) (by positivity)
      _ = ((9 * X / (2 * α)) ^ 2) * Work.Spaces.HkIntegrand α 4 g z θ := by ring
  have hP4sq : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      ((-Work.Construction.c2m θ) * Work.Construction.L12 g z
          * Work.Spaces.Dz (Work.Construction.Fstar α) z θ) ^ 2
        ≤ (240 * α * X * (z / (1 + z) ^ 2)) ^ 2 := by
    intro z hz θ hθ
    have h1 : (Work.Construction.c2m θ) ^ 2 ≤ (2 : ℝ) ^ 2 := by
      have h := hc2m θ
      nlinarith [h, abs_nonneg (Work.Construction.c2m θ), sq_abs (Work.Construction.c2m θ)]
    have h2 : |Work.Construction.L12 g z| ≤ 3 * X := hL12g z (le_of_lt hz)
    have h3 : (Work.Construction.L12 g z) ^ 2 ≤ (3 * X) ^ 2 := by
      nlinarith [h2, abs_nonneg (Work.Construction.L12 g z), sq_abs (Work.Construction.L12 g z)]
    have h5 : (Work.Spaces.Dz (Work.Construction.Fstar α) z θ) ^ 2
        ≤ (40 * α * (z / (1 + z) ^ 2)) ^ 2 := by
      have h := hDzF z (le_of_lt hz) θ ⟨hθ.1.le, hθ.2.le⟩
      nlinarith [h, abs_nonneg (Work.Spaces.Dz (Work.Construction.Fstar α) z θ),
        sq_abs (Work.Spaces.Dz (Work.Construction.Fstar α) z θ)]
    calc ((-Work.Construction.c2m θ) * Work.Construction.L12 g z
          * Work.Spaces.Dz (Work.Construction.Fstar α) z θ) ^ 2
        = (Work.Construction.c2m θ) ^ 2 * (Work.Construction.L12 g z) ^ 2
          * (Work.Spaces.Dz (Work.Construction.Fstar α) z θ) ^ 2 := by ring
      _ ≤ (2 : ℝ) ^ 2 * (3 * X) ^ 2 * (40 * α * (z / (1 + z) ^ 2)) ^ 2 := by
          refine mul_le_mul (mul_le_mul h1 h3 (sq_nonneg _) (by norm_num)) h5 (sq_nonneg _)
            (by positivity)
      _ = (240 * α * X * (z / (1 + z) ^ 2)) ^ 2 := by ring
  have hP5sq : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      ((-Work.Construction.c2m θ) * Work.Construction.L12 g z * Work.Spaces.Dz g z θ) ^ 2
        ≤ ((6 * X) ^ 2) * Work.Spaces.HkIntegrand α 4 g z θ := by
    intro z hz θ hθ
    have h1 : (Work.Construction.c2m θ) ^ 2 ≤ (2 : ℝ) ^ 2 := by
      have h := hc2m θ
      nlinarith [h, abs_nonneg (Work.Construction.c2m θ), sq_abs (Work.Construction.c2m θ)]
    have h2 : |Work.Construction.L12 g z| ≤ 3 * X := hL12g z (le_of_lt hz)
    have h3 : (Work.Construction.L12 g z) ^ 2 ≤ (3 * X) ^ 2 := by
      nlinarith [h2, abs_nonneg (Work.Construction.L12 g z), sq_abs (Work.Construction.L12 g z)]
    have h5 : (Work.Spaces.Dz g z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
      dz_sq_le_HkIntegrand α g hα hz hθ
    calc ((-Work.Construction.c2m θ) * Work.Construction.L12 g z * Work.Spaces.Dz g z θ) ^ 2
        = (Work.Construction.c2m θ) ^ 2 * (Work.Construction.L12 g z) ^ 2
          * (Work.Spaces.Dz g z θ) ^ 2 := by ring
      _ ≤ (2 : ℝ) ^ 2 * (3 * X) ^ 2 * Work.Spaces.HkIntegrand α 4 g z θ := by
          refine mul_le_mul (mul_le_mul h1 h3 (sq_nonneg _) (by norm_num)) h5 (sq_nonneg _)
            (by positivity)
      _ = ((6 * X) ^ 2) * Work.Spaces.HkIntegrand α 4 g z θ := by ring
  have hP6sq : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      ((-Work.Construction.c2m θ) * (2 * α / (1 + z)) * Work.Spaces.Dz g z θ) ^ 2
        ≤ ((4 * α) ^ 2) * Work.Spaces.HkIntegrand α 4 g z θ := by
    intro z hz θ hθ
    have h1 : (Work.Construction.c2m θ) ^ 2 ≤ (2 : ℝ) ^ 2 := by
      have h := hc2m θ
      nlinarith [h, abs_nonneg (Work.Construction.c2m θ), sq_abs (Work.Construction.c2m θ)]
    have h4 : (2 * α / (1 + z)) ^ 2 ≤ (2 * α) ^ 2 := by
      have h1z : 0 < 1 + z := by linarith [Set.mem_Ioi.mp hz]
      have h : |2 * α / (1 + z)| ≤ 2 * α := by
        rw [abs_div, abs_of_nonneg (mul_nonneg (by norm_num) hα.le),
          abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 + z), div_le_iff₀ h1z]
        nlinarith [mul_nonneg hα.le (le_of_lt (Set.mem_Ioi.mp hz)), hα.le]
      nlinarith [h, abs_nonneg (2 * α / (1 + z)), sq_abs (2 * α / (1 + z)),
        mul_nonneg hα.le hα.le]
    have h5 : (Work.Spaces.Dz g z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
      dz_sq_le_HkIntegrand α g hα hz hθ
    calc ((-Work.Construction.c2m θ) * (2 * α / (1 + z)) * Work.Spaces.Dz g z θ) ^ 2
        = (Work.Construction.c2m θ) ^ 2 * (2 * α / (1 + z)) ^ 2 * (Work.Spaces.Dz g z θ) ^ 2 := by
          ring
      _ ≤ (2 : ℝ) ^ 2 * (2 * α) ^ 2 * Work.Spaces.HkIntegrand α 4 g z θ := by
          refine mul_le_mul (mul_le_mul h1 h4 (sq_nonneg _) (by norm_num)) h5 (sq_nonneg _)
            (by positivity)
      _ = ((4 * α) ^ 2) * Work.Spaces.HkIntegrand α 4 g z θ := by ring
  -- ## the weighted pointwise bound for `N₀`
  have hw1 : ∀ r : ℝ, 0 < r → 1 ≤ Work.Spaces.w r := fun r hr => by
    rw [Work.Spaces.w, one_le_div (by positivity)]
    nlinarith
  set A : ℝ := 9 * X ^ 2 / α ^ 2 + 81 * X ^ 2 / (4 * α ^ 2) + 36 * X ^ 2
    + 16 * α ^ 2 with hAdef
  set B : ℝ := (160 * α ^ 2) ^ 2 + (180 * α * X) ^ 2 + (240 * α * X) ^ 2 with hBdef
  have hA0 : 0 ≤ A := by
    rw [hAdef]
    have h1 : (0 : ℝ) ≤ 9 * X ^ 2 / α ^ 2 := div_nonneg (by positivity) (by positivity)
    have h2 : (0 : ℝ) ≤ 81 * X ^ 2 / (4 * α ^ 2) := div_nonneg (by positivity) (by positivity)
    have h3 : (0 : ℝ) ≤ 36 * X ^ 2 := by positivity
    have h4 : (0 : ℝ) ≤ 16 * α ^ 2 := by positivity
    linarith
  have hB0 : 0 ≤ B := by
    rw [hBdef]
    nlinarith [sq_nonneg (160 * α ^ 2), sq_nonneg (180 * α * X), sq_nonneg (240 * α * X)]
  have hpt : ∀ r ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      (Work.Construction.N0 α (Work.Construction.Ftot α g) g r θ) ^ 2 * Work.Spaces.w r
        ≤ 7 * (A * Work.Spaces.HkIntegrand α 4 g r θ + B * (1 / (1 + r)) ^ 2) := by
    intro r hr θ hθ
    have hr0 : 0 ≤ r := le_of_lt hr
    have h1r : 0 < 1 + r := by linarith
    set W : ℝ := Work.Spaces.w r with hWdef
    have hW1 : 1 ≤ W := by rw [hWdef]; exact hw1 r hr
    have hW0 : 0 ≤ W := le_trans zero_le_one hW1
    set Hk : ℝ := Work.Spaces.HkIntegrand α 4 g r θ with hHkdef
    have hHk0 : 0 ≤ Hk := by
      rw [hHkdef]; exact Work.Spaces.HkIntegrand_nonneg α 4 g r θ
    set T0 : ℝ := (3 / (2 * α)) * Work.Construction.s2 θ
          * Work.Construction.L12 (Work.Construction.Fstar α) r
          * Work.Spaces.pth (Work.Construction.Fstar α) r θ
        - Work.Construction.c2m θ * Work.Construction.L12 (Work.Construction.Fstar α) r
          * Work.Spaces.Dz (Work.Construction.Fstar α) r θ with hT0def
    set T1 : ℝ := (1 / α) * Work.Construction.L12 g r * g r θ with hT1def
    set T2 : ℝ := (3 / (2 * α)) * Work.Construction.s2 θ * Work.Construction.L12 g r
          * Work.Spaces.pth (Work.Construction.Fstar α) r θ with hT2def
    set T3 : ℝ := (3 / (2 * α)) * Work.Construction.s2 θ * Work.Construction.L12 g r
          * Work.Spaces.pth g r θ with hT3def
    set T4 : ℝ := -(Work.Construction.c2m θ) * Work.Construction.L12 g r
          * Work.Spaces.Dz (Work.Construction.Fstar α) r θ with hT4def
    set T5 : ℝ := -(Work.Construction.c2m θ) * Work.Construction.L12 g r
          * Work.Spaces.Dz g r θ with hT5def
    set T6 : ℝ := -(Work.Construction.c2m θ)
          * Work.Construction.L12 (Work.Construction.Fstar α) r
          * Work.Spaces.Dz g r θ with hT6def
    have hexp : Work.Construction.N0 α (Work.Construction.Ftot α g) g r θ
        = T0 + T1 + T2 + T3 + T4 + T5 + T6 := by
      rw [hT0def, hT1def, hT2def, hT3def, hT4def, hT5def, hT6def]
      simp only [Work.Construction.N0]
      rw [hpth r hr θ hθ, hI2 r hr θ hθ]
      ring
    have h3L : (Work.Construction.L12 g r) ^ 2 ≤ (3 * X) ^ 2 := by
      have h := hL12g r hr0
      nlinarith [h, abs_nonneg (Work.Construction.L12 g r),
        sq_abs (Work.Construction.L12 g r)]
    have hc2sq : (Work.Construction.c2m θ) ^ 2 ≤ (2 : ℝ) ^ 2 := by
      have h := hc2m θ
      nlinarith [h, abs_nonneg (Work.Construction.c2m θ), sq_abs (Work.Construction.c2m θ)]
    have hb0 : T0 ^ 2 * W ≤ (160 * α ^ 2) ^ 2 * (1 / (1 + r)) ^ 2 := by
      have h := hN0bd r hr θ hθ
      rw [← hT0def] at h
      have h2 : T0 ^ 2 ≤ (160 * α ^ 2 * (r ^ 2 / (1 + r) ^ 4)) ^ 2 := by
        nlinarith [h, abs_nonneg T0, sq_abs T0]
      calc T0 ^ 2 * W ≤ (160 * α ^ 2 * (r ^ 2 / (1 + r) ^ 4)) ^ 2 * W :=
            mul_le_mul_of_nonneg_right h2 hW0
        _ = (160 * α ^ 2) ^ 2 * (r ^ 2 / (1 + r) ^ 4) ^ 2 * W := by ring
        _ ≤ (160 * α ^ 2) ^ 2 * (1 / (1 + r)) ^ 2 := by
            rw [hWdef]
            exact sq_div_shape_le hr
    have hb1 : T1 ^ 2 * W ≤ (9 * X ^ 2 / α ^ 2) * Hk := by
      rw [hT1def]
      have hg2 : (g r θ) ^ 2 * W ≤ Hk := by
        have h := g_sq_mul_w_sq_le_HkIntegrand α g hr hθ
        rw [← hWdef, ← hHkdef] at h
        nlinarith [h, hW1, sq_nonneg (g r θ)]
      have hkey : ((1 / α) * Work.Construction.L12 g r * g r θ) ^ 2 * W
          = (1 / α) ^ 2 * (Work.Construction.L12 g r) ^ 2 * ((g r θ) ^ 2 * W) := by ring
      rw [hkey]
      calc (1 / α) ^ 2 * (Work.Construction.L12 g r) ^ 2 * ((g r θ) ^ 2 * W)
          ≤ (1 / α) ^ 2 * (3 * X) ^ 2 * Hk := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left h3L (sq_nonneg _)) hg2
              (mul_nonneg (sq_nonneg _) hW0)
              (mul_nonneg (sq_nonneg (1 / α)) (sq_nonneg (3 * X)))
        _ = (9 * X ^ 2 / α ^ 2) * Hk := by ring_nf
    have hb2 : T2 ^ 2 * W ≤ (180 * α * X) ^ 2 * (1 / (1 + r)) ^ 2 := by
      have hw : (Work.Spaces.Dth (Work.Construction.Fstar α) r θ) ^ 2 * W
          ≤ (40 * α ^ 2) ^ 2 * (1 / (1 + r)) ^ 2 := by
        have h := hDthF r hr0 θ ⟨hθ.1.le, hθ.2.le⟩
        have h5 : (Work.Spaces.Dth (Work.Construction.Fstar α) r θ) ^ 2
            ≤ (40 * α ^ 2 * (r / (1 + r) ^ 2)) ^ 2 := by
          nlinarith [h, abs_nonneg (Work.Spaces.Dth (Work.Construction.Fstar α) r θ),
            sq_abs (Work.Spaces.Dth (Work.Construction.Fstar α) r θ)]
        calc (Work.Spaces.Dth (Work.Construction.Fstar α) r θ) ^ 2 * W
            ≤ (40 * α ^ 2 * (r / (1 + r) ^ 2)) ^ 2 * W :=
              mul_le_mul_of_nonneg_right h5 hW0
          _ = (40 * α ^ 2) ^ 2 * (r / (1 + r) ^ 2) ^ 2 * W := by ring
          _ ≤ (40 * α ^ 2) ^ 2 * (1 / (1 + r)) ^ 2 := by
              rw [hWdef]
              exact le_of_eq (sq_div_shape_eq (c := 40 * α ^ 2) hr)
      have hkey : T2 ^ 2 * W = (3 / (2 * α)) ^ 2 * (Work.Construction.L12 g r) ^ 2
            * ((Work.Spaces.Dth (Work.Construction.Fstar α) r θ) ^ 2 * W) := by
        rw [hT2def]
        simp only [Work.Spaces.Dth, Work.Construction.s2]
        ring
      rw [hkey]
      calc (3 / (2 * α)) ^ 2 * (Work.Construction.L12 g r) ^ 2
              * ((Work.Spaces.Dth (Work.Construction.Fstar α) r θ) ^ 2 * W)
          ≤ (3 / (2 * α)) ^ 2 * (3 * X) ^ 2 * ((40 * α ^ 2) ^ 2 * (1 / (1 + r)) ^ 2) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left h3L (sq_nonneg _)) hw
              (mul_nonneg (sq_nonneg _) hW0)
              (mul_nonneg (sq_nonneg (3 / (2 * α))) (sq_nonneg (3 * X)))
        _ = (180 * α * X) ^ 2 * (1 / (1 + r)) ^ 2 := by
            have hαne : α ≠ 0 := ne_of_gt hα
            field_simp
            ring
    have hb3 : T3 ^ 2 * W ≤ (81 * X ^ 2 / (4 * α ^ 2)) * Hk := by
      have hw : (Work.Spaces.Dth g r θ) ^ 2 * W ≤ Hk := by
        have h := dth_sq_mul_w_le_HkIntegrand α g hα hr hθ
        rw [← hWdef, ← hHkdef] at h
        exact h
      have hkey : T3 ^ 2 * W = (3 / (2 * α)) ^ 2 * (Work.Construction.L12 g r) ^ 2
            * ((Work.Spaces.Dth g r θ) ^ 2 * W) := by
        rw [hT3def]
        simp only [Work.Spaces.Dth, Work.Construction.s2]
        ring
      rw [hkey]
      calc (3 / (2 * α)) ^ 2 * (Work.Construction.L12 g r) ^ 2
              * ((Work.Spaces.Dth g r θ) ^ 2 * W)
          ≤ (3 / (2 * α)) ^ 2 * (3 * X) ^ 2 * Hk := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left h3L (sq_nonneg _)) hw
              (mul_nonneg (sq_nonneg _) hW0)
              (mul_nonneg (sq_nonneg (3 / (2 * α))) (sq_nonneg (3 * X)))
        _ = (81 * X ^ 2 / (4 * α ^ 2)) * Hk := by ring_nf
    have hb4 : T4 ^ 2 * W ≤ (240 * α * X) ^ 2 * (1 / (1 + r)) ^ 2 := by
      have hw : (Work.Spaces.Dz (Work.Construction.Fstar α) r θ) ^ 2 * W
          ≤ (40 * α) ^ 2 * (1 / (1 + r)) ^ 2 := by
        have h := hDzF r hr0 θ ⟨hθ.1.le, hθ.2.le⟩
        have h5 : (Work.Spaces.Dz (Work.Construction.Fstar α) r θ) ^ 2
            ≤ (40 * α * (r / (1 + r) ^ 2)) ^ 2 := by
          nlinarith [h, abs_nonneg (Work.Spaces.Dz (Work.Construction.Fstar α) r θ),
            sq_abs (Work.Spaces.Dz (Work.Construction.Fstar α) r θ)]
        calc (Work.Spaces.Dz (Work.Construction.Fstar α) r θ) ^ 2 * W
            ≤ (40 * α * (r / (1 + r) ^ 2)) ^ 2 * W :=
              mul_le_mul_of_nonneg_right h5 hW0
          _ = (40 * α) ^ 2 * (r / (1 + r) ^ 2) ^ 2 * W := by ring
          _ ≤ (40 * α) ^ 2 * (1 / (1 + r)) ^ 2 := by
              rw [hWdef]
              exact le_of_eq (sq_div_shape_eq (c := 40 * α) hr)
      have hkey : T4 ^ 2 * W = (Work.Construction.c2m θ) ^ 2
            * (Work.Construction.L12 g r) ^ 2
            * ((Work.Spaces.Dz (Work.Construction.Fstar α) r θ) ^ 2 * W) := by
        rw [hT4def]
        ring
      rw [hkey]
      calc (Work.Construction.c2m θ) ^ 2 * (Work.Construction.L12 g r) ^ 2
              * ((Work.Spaces.Dz (Work.Construction.Fstar α) r θ) ^ 2 * W)
          ≤ (2 : ℝ) ^ 2 * (3 * X) ^ 2 * ((40 * α) ^ 2 * (1 / (1 + r)) ^ 2) := by
            refine mul_le_mul (mul_le_mul hc2sq h3L (sq_nonneg _) (by norm_num)) hw
              (mul_nonneg (sq_nonneg _) hW0)
              (mul_nonneg (sq_nonneg (2 : ℝ)) (sq_nonneg (3 * X)))
        _ = (240 * α * X) ^ 2 * (1 / (1 + r)) ^ 2 := by ring_nf
    have hb5 : T5 ^ 2 * W ≤ (36 * X ^ 2) * Hk := by
      have hw : (Work.Spaces.Dz g r θ) ^ 2 * W ≤ Hk := by
        have h := dz_sq_mul_w_le_HkIntegrand α g hr hθ
        rw [← hWdef, ← hHkdef] at h
        exact h
      have hkey : T5 ^ 2 * W = (Work.Construction.c2m θ) ^ 2
            * (Work.Construction.L12 g r) ^ 2
            * ((Work.Spaces.Dz g r θ) ^ 2 * W) := by
        rw [hT5def]
        ring
      rw [hkey]
      calc (Work.Construction.c2m θ) ^ 2 * (Work.Construction.L12 g r) ^ 2
              * ((Work.Spaces.Dz g r θ) ^ 2 * W)
          ≤ (2 : ℝ) ^ 2 * (3 * X) ^ 2 * Hk := by
            refine mul_le_mul (mul_le_mul hc2sq h3L (sq_nonneg _) (by norm_num)) hw
              (mul_nonneg (sq_nonneg _) hW0)
              (mul_nonneg (sq_nonneg (2 : ℝ)) (sq_nonneg (3 * X)))
        _ = (36 * X ^ 2) * Hk := by ring
    have hb6 : T6 ^ 2 * W ≤ (16 * α ^ 2) * Hk := by
      have hw : (Work.Spaces.Dz g r θ) ^ 2 * W ≤ Hk := by
        have h := dz_sq_mul_w_le_HkIntegrand α g hr hθ
        rw [← hWdef, ← hHkdef] at h
        exact h
      have hlam : Work.Construction.L12 (Work.Construction.Fstar α) r
          = 2 * α / (1 + r) := hL12F r hr0
      have h2a : (2 * α / (1 + r)) ^ 2 ≤ (2 * α) ^ 2 := by
        have h0 : 0 ≤ 1 / (1 + r) := div_nonneg zero_le_one h1r.le
        have hle : 1 / (1 + r) ≤ 1 := by rw [div_le_one h1r]; linarith
        have hsq : (1 / (1 + r)) ^ 2 ≤ 1 := by nlinarith [h0, hle]
        calc (2 * α / (1 + r)) ^ 2 = (2 * α) ^ 2 * (1 / (1 + r)) ^ 2 := by ring_nf
          _ ≤ (2 * α) ^ 2 * 1 := mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
          _ = (2 * α) ^ 2 := by ring
      have hkey : T6 ^ 2 * W = (Work.Construction.c2m θ) ^ 2 * (2 * α / (1 + r)) ^ 2
            * ((Work.Spaces.Dz g r θ) ^ 2 * W) := by
        rw [hT6def, hlam]
        ring
      rw [hkey]
      calc (Work.Construction.c2m θ) ^ 2 * (2 * α / (1 + r)) ^ 2
              * ((Work.Spaces.Dz g r θ) ^ 2 * W)
          ≤ (2 : ℝ) ^ 2 * (2 * α) ^ 2 * Hk := by
            refine mul_le_mul (mul_le_mul hc2sq h2a (sq_nonneg _) (by norm_num)) hw
              (mul_nonneg (sq_nonneg _) hW0)
              (mul_nonneg (sq_nonneg (2 : ℝ)) (sq_nonneg (2 * α)))
        _ = (16 * α ^ 2) * Hk := by ring
    have hcs7 : (T0 + T1 + T2 + T3 + T4 + T5 + T6) ^ 2
        ≤ 7 * (T0 ^ 2 + T1 ^ 2 + T2 ^ 2 + T3 ^ 2 + T4 ^ 2 + T5 ^ 2 + T6 ^ 2) := by
      have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
        (f := fun i : Fin 7 => ![T0, T1, T2, T3, T4, T5, T6] i)
      simpa [Fin.sum_univ_seven, Matrix.cons_val_zero, Matrix.cons_val_succ] using h
    calc (Work.Construction.N0 α (Work.Construction.Ftot α g) g r θ) ^ 2 * W
        = (T0 + T1 + T2 + T3 + T4 + T5 + T6) ^ 2 * W := by rw [hexp]
      _ ≤ 7 * ((T0 ^ 2 + T1 ^ 2 + T2 ^ 2 + T3 ^ 2 + T4 ^ 2 + T5 ^ 2 + T6 ^ 2) * W) := by
          calc (T0 + T1 + T2 + T3 + T4 + T5 + T6) ^ 2 * W
              ≤ (7 * (T0 ^ 2 + T1 ^ 2 + T2 ^ 2 + T3 ^ 2 + T4 ^ 2 + T5 ^ 2 + T6 ^ 2)) * W :=
                mul_le_mul_of_nonneg_right hcs7 hW0
            _ = 7 * ((T0 ^ 2 + T1 ^ 2 + T2 ^ 2 + T3 ^ 2 + T4 ^ 2 + T5 ^ 2 + T6 ^ 2) * W) := by
                ring
      _ ≤ 7 * (A * Hk + B * (1 / (1 + r)) ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          rw [hAdef, hBdef]
          nlinarith [hb0, hb1, hb2, hb3, hb4, hb5, hb6]
  -- ## the weighted angular-energy bound
  have hbd : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      (∫ θ in Work.Spaces.Iθ,
          (Work.Construction.N0 α (Work.Construction.Ftot α g) g r θ) ^ 2)
          * ((1 + r) / r) ^ 2
        ≤ 7 * (A * Ψ r + ((π / 2) * B) * (1 / (1 + r)) ^ 2) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
    have hr0 : 0 ≤ r := le_of_lt hr
    have hW1 : 1 ≤ Work.Spaces.w r := hw1 r hr
    have hweq : ((1 + r) / r) ^ 2 = Work.Spaces.w r := by rw [Work.Spaces.w, div_pow]
    rw [hweq, ← MeasureTheory.integral_mul_const]
    have hIoo2 : MeasureTheory.volume.restrict Work.Spaces.Iθ
        = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) :=
      MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc.symm
    have hstep : (∫ θ in Work.Spaces.Iθ,
          (Work.Construction.N0 α (Work.Construction.Ftot α g) g r θ) ^ 2
            * Work.Spaces.w r)
        ≤ ∫ θ in Work.Spaces.Iθ,
          7 * (A * Work.Spaces.HkIntegrand α 4 g r θ
            + B * (1 / (1 + r)) ^ 2) := by
      refine MeasureTheory.integral_mono_of_nonneg ?_ ?_ ?_
      · exact Filter.Eventually.of_forall (fun θ =>
          mul_nonneg (sq_nonneg _) (le_trans zero_le_one hW1))
      · refine (((hmem.1 r hr0).const_mul A).add ?_).const_mul 7
        refine MeasureTheory.integrableOn_const ?_
        rw [Work.Spaces.Iθ, Real.volume_Icc]
        exact ENNReal.ofReal_ne_top
      · rw [hIoo2]
        exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
          (fun θ hθ => hpt r hr θ hθ)
    refine hstep.trans ?_
    have hintA : MeasureTheory.IntegrableOn
        (fun θ => A * Work.Spaces.HkIntegrand α 4 g r θ) Work.Spaces.Iθ :=
      (hmem.1 r hr0).const_mul A
    have hintB : MeasureTheory.IntegrableOn
        (fun θ => B * (1 / (1 + r)) ^ 2) Work.Spaces.Iθ := by
      refine MeasureTheory.integrableOn_const ?_
      rw [Work.Spaces.Iθ, Real.volume_Icc]
      exact ENNReal.ofReal_ne_top
    have hvalPsi : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g r θ) = Ψ r := rfl
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add hintA hintB,
      MeasureTheory.integral_const_mul, integral_const_Iθ_ra, hvalPsi]
    exact le_of_eq (by ring_nf)
  -- ## the master estimate
  have hαI : α ∈ Set.Ioc 0 α₂ := ⟨hα, hαα₂⟩
  have hcontN0 := continuousOn_uncurry_N0 hN hαI hα1 hsq hmem
  have hmeas : MeasureTheory.AEStronglyMeasurable
      (fun r => (∫ θ in Work.Spaces.Iθ,
          (Work.Construction.N0 α (Work.Construction.Ftot α g) g r θ) ^ 2)
          * ((1 + r) / r) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    aesm_weighted_energy_of_continuousOn hcontN0
  have hΦint : MeasureTheory.IntegrableOn
      (fun r => 7 * (A * Ψ r + ((π / 2) * B) * (1 / (1 + r)) ^ 2))
      (Set.Ioi (0 : ℝ)) := by
    have h1 : MeasureTheory.IntegrableOn (fun r => A * Ψ r) (Set.Ioi (0 : ℝ)) :=
      hΨint.const_mul A
    have h2 : MeasureTheory.IntegrableOn
        (fun r => ((π / 2) * B) * (1 / (1 + r)) ^ 2) (Set.Ioi (0 : ℝ)) :=
      Work.FTS.H2.InvOneAddSq.1.const_mul ((π / 2) * B)
    exact (h1.add h2).const_mul 7
  have hsl : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      MeasureTheory.IntegrableOn
        (fun θ => (Work.Construction.N0 α (Work.Construction.Ftot α g) g r θ) ^ 2)
        Work.Spaces.Iθ := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
    have hr0 : 0 ≤ r := le_of_lt hr
    have hW1 : 1 ≤ Work.Spaces.w r := hw1 r hr
    have hIoo2 : MeasureTheory.volume.restrict Work.Spaces.Iθ
        = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) :=
      MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc.symm
    have hslice : MeasureTheory.AEStronglyMeasurable
        (fun θ => Work.Construction.N0 α (Work.Construction.Ftot α g) g r θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      Work.Spaces.aesm_slice_of_continuousOn_Qd _ hcontN0 hr
    have hmaj : MeasureTheory.Integrable
        (fun θ => 7 * (A * Work.Spaces.HkIntegrand α 4 g r θ + B * (1 / (1 + r)) ^ 2))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      refine (((hmem.1 r hr0).const_mul A).add ?_).const_mul 7
      refine MeasureTheory.integrableOn_const ?_
      rw [Work.Spaces.Iθ, Real.volume_Icc]
      exact ENNReal.ofReal_ne_top
    refine MeasureTheory.Integrable.mono' hmaj (hslice.pow 2) ?_
    · rw [hIoo2]
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      calc (Work.Construction.N0 α (Work.Construction.Ftot α g) g r θ) ^ 2
          ≤ (Work.Construction.N0 α (Work.Construction.Ftot α g) g r θ) ^ 2
            * Work.Spaces.w r := by
            nlinarith [hW1,
              sq_nonneg (Work.Construction.N0 α (Work.Construction.Ftot α g) g r θ)]
        _ ≤ 7 * (A * Work.Spaces.HkIntegrand α 4 g r θ
            + B * (1 / (1 + r)) ^ 2) := hpt r hr θ hθ
  have hmain := L12_zero_le_of_weight_bound hsl hmeas hΦint hbd
  -- ## the arithmetic
  have hIntPhi : (∫ r in Set.Ioi (0 : ℝ),
        7 * (A * Ψ r + ((π / 2) * B) * (1 / (1 + r)) ^ 2))
      = 7 * (A * X ^ 2
          + ((π / 2) * B) * (∫ r in Set.Ioi (0 : ℝ), (1 / (1 + r)) ^ 2)) := by
    have h1 : MeasureTheory.IntegrableOn (fun r => A * Ψ r) (Set.Ioi (0 : ℝ)) :=
      hΨint.const_mul A
    have h2 : MeasureTheory.IntegrableOn
        (fun r => ((π / 2) * B) * (1 / (1 + r)) ^ 2) (Set.Ioi (0 : ℝ)) :=
      Work.FTS.H2.InvOneAddSq.1.const_mul ((π / 2) * B)
    have hX2 : (∫ r in Set.Ioi (0 : ℝ), Ψ r) = X ^ 2 := by
      have hA2 : (∫ r in Set.Ioi (0 : ℝ), Ψ r) = Work.Spaces.HkSq α 4 g := by
        rw [hΨ, Work.Spaces.HkSq, Work.Spaces.Iz]
        exact MeasureTheory.setIntegral_congr_set MeasureTheory.Ioi_ae_eq_Ici
      have hB2 : X ^ 2 = Work.Spaces.HkSq α 4 g := by
        rw [hX, Work.FTS.Nonlin.Xn]
        show (Work.FTS.Nonlin.Xn α g) ^ 2 = Work.Spaces.HkSq α 4 g
        rw [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm,
          Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 4 g)]
      rw [hA2, hB2]
    have h3 : (∫ r in Set.Ioi (0 : ℝ), ((π / 2) * B) * (1 / (1 + r)) ^ 2)
        = ((π / 2) * B) * (∫ r in Set.Ioi (0 : ℝ), (1 / (1 + r)) ^ 2) :=
      MeasureTheory.integral_const_mul ((π / 2) * B) (fun r : ℝ => (1 / (1 + r)) ^ 2)
    have h4 : (∫ r in Set.Ioi (0 : ℝ), A * Ψ r) = A * (∫ r in Set.Ioi (0 : ℝ), Ψ r) :=
      MeasureTheory.integral_const_mul A Ψ
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add h1 h2, h4, h3, hX2]
  have hInt_le : (∫ r in Set.Ioi (0 : ℝ),
        7 * (A * Ψ r + ((π / 2) * B) * (1 / (1 + r)) ^ 2))
      ≤ 7 * (A * X ^ 2 + π * B) := by
    rw [hIntPhi]
    have h2 := Work.FTS.H2.InvOneAddSq.2
    have hB2 : ((π / 2) * B) * (∫ r in Set.Ioi (0 : ℝ), (1 / (1 + r)) ^ 2)
        ≤ ((π / 2) * B) * 2 :=
      mul_le_mul_of_nonneg_left h2 (mul_nonneg (by positivity) hB0)
    calc 7 * (A * X ^ 2
            + ((π / 2) * B) * (∫ r in Set.Ioi (0 : ℝ), (1 / (1 + r)) ^ 2))
        ≤ 7 * (A * X ^ 2 + ((π / 2) * B) * 2) := by nlinarith [hB2]
      _ = 7 * (A * X ^ 2 + π * B) := by ring
  -- ## the final bound
  set Y : ℝ := α ^ (-(3 / 2 : ℝ)) with hYdef
  have hY1 : 1 ≤ Y := by
    rw [hYdef]
    exact one_le_rpow_neg hα hα1 (by norm_num)
  have hY0 : 0 ≤ Y := le_trans zero_le_one hY1
  have hYinv : α⁻¹ ≤ Y := by
    rw [hYdef]
    simpa only [Real.rpow_neg_one] using
      Real.rpow_le_rpow_of_exponent_ge hα hα1 (show (-(3 / 2 : ℝ)) ≤ -1 by norm_num)
  have hY2 : 1 ≤ Y ^ 2 := by nlinarith [hY1]
  have hYinv2 : (α⁻¹) ^ 2 ≤ Y ^ 2 := by
    have h0 : 0 ≤ α⁻¹ := inv_nonneg.mpr hα.le
    nlinarith [hYinv, h0, hY0]
  have hsqrtale : α ≤ Real.sqrt α :=
    (Real.le_sqrt hα.le hα.le).mpr (by nlinarith [hα.le, hα1])
  have hX4le : X ^ 4 / α ^ 2 ≤ Y ^ 2 * X ^ 4 := by
    have hX40 : 0 ≤ X ^ 4 := by positivity
    have heq : X ^ 4 / α ^ 2 = X ^ 4 * (α⁻¹) ^ 2 := by
      rw [div_eq_mul_inv, inv_pow]
    rw [heq]
    nlinarith [hYinv2, hX40]
  have hX4le' : X ^ 4 ≤ Y ^ 2 * X ^ 4 := by
    have hX40 : 0 ≤ X ^ 4 := by positivity
    calc X ^ 4 = 1 * X ^ 4 := by ring
      _ ≤ Y ^ 2 * X ^ 4 := mul_le_mul_of_nonneg_right hY2 hX40
  have hRb : 7 * (A * X ^ 2 + π * B)
      ≤ 500 * Y ^ 2 * X ^ 4 + 3000000 * α ^ 2 * X ^ 2 + 800000 * α ^ 4 := by
    rw [hAdef, hBdef]
    have hpid : π ≤ 3.15 := le_of_lt Real.pi_lt_d2
    have hα2 : α ^ 2 ≤ 1 := by nlinarith [hα.le, hα1]
    have hX40 : 0 ≤ X ^ 4 := by positivity
    have hY20 : 0 ≤ Y ^ 2 := by positivity
    have hpart1 : 7 * ((9 * X ^ 2 / α ^ 2 + 81 * X ^ 2 / (4 * α ^ 2) + 36 * X ^ 2
          + 16 * α ^ 2) * X ^ 2)
        ≤ 500 * Y ^ 2 * X ^ 4 + 1000000 * α ^ 2 * X ^ 2 := by
      have hαne : α ≠ 0 := ne_of_gt hα
      have hkey : 7 * ((9 * X ^ 2 / α ^ 2 + 81 * X ^ 2 / (4 * α ^ 2) + 36 * X ^ 2
            + 16 * α ^ 2) * X ^ 2)
          = 63 * (X ^ 4 / α ^ 2) + 141.75 * (X ^ 4 / α ^ 2) + 252 * X ^ 4
            + 112 * α ^ 2 * X ^ 2 := by
        field_simp
        ring
      rw [hkey]
      have hA1 : 63 * (X ^ 4 / α ^ 2) ≤ 63 * (Y ^ 2 * X ^ 4) :=
        mul_le_mul_of_nonneg_left hX4le (by norm_num)
      have hA2 : 141.75 * (X ^ 4 / α ^ 2) ≤ 141.75 * (Y ^ 2 * X ^ 4) :=
        mul_le_mul_of_nonneg_left hX4le (by norm_num)
      have hA3 : 252 * X ^ 4 ≤ 252 * (Y ^ 2 * X ^ 4) :=
        mul_le_mul_of_nonneg_left hX4le' (by norm_num)
      have hA4 : 112 * α ^ 2 * X ^ 2 ≤ 1000000 * α ^ 2 * X ^ 2 := by
        nlinarith [sq_nonneg α, sq_nonneg X]
      linarith [hA1, hA2, hA3, hA4, mul_nonneg hY20 hX40,
        mul_nonneg (sq_nonneg α) (sq_nonneg X)]
    have hpart2 : 7 * (π * ((160 * α ^ 2) ^ 2 + (180 * α * X) ^ 2 + (240 * α * X) ^ 2))
        ≤ 2000000 * α ^ 2 * X ^ 2 + 800000 * α ^ 4 := by
      nlinarith [hpid, hα2, hα.le, sq_nonneg α, sq_nonneg X, hX0,
        mul_nonneg hα.le hX0]
    linarith [hpart1, hpart2]
  have hsqrtR : Real.sqrt (7 * (A * X ^ 2 + π * B))
      ≤ 2651 * (α ^ 2 + Real.sqrt α * X + Y * X ^ 2) := by
    have h1 : Real.sqrt (7 * (A * X ^ 2 + π * B))
        ≤ Real.sqrt (500 * Y ^ 2 * X ^ 4) + Real.sqrt (3000000 * α ^ 2 * X ^ 2)
          + Real.sqrt (800000 * α ^ 4) := by
      refine le_trans (Real.sqrt_le_sqrt hRb) ?_
      have h0 := sqrt_add_le_sum_sqrt (a := 500 * Y ^ 2 * X ^ 4)
        (b := 3000000 * α ^ 2 * X ^ 2) (c := 800000 * α ^ 4)
        (by positivity) (by positivity) (by positivity)
      exact h0
    have h3 : Real.sqrt (500 * Y ^ 2 * X ^ 4)
        ≤ 23 * (α ^ 2 + Real.sqrt α * X + Y * X ^ 2) := by
      have heq : Real.sqrt (500 * Y ^ 2 * X ^ 4) = Real.sqrt 500 * Y * X ^ 2 := by
        rw [show (500 : ℝ) * Y ^ 2 * X ^ 4 = 500 * (Y * X ^ 2) ^ 2 from by ring]
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 500),
          Real.sqrt_sq (mul_nonneg hY0 (sq_nonneg X))]
        ring
      rw [heq]
      have hs500 : Real.sqrt 500 ≤ 23 := by
        rw [Real.sqrt_le_iff]
        exact ⟨by norm_num, by norm_num⟩
      have hYX : Y * X ^ 2 ≤ α ^ 2 + Real.sqrt α * X + Y * X ^ 2 := by
        linarith [sq_nonneg α, mul_nonneg (Real.sqrt_nonneg α) hX0]
      calc Real.sqrt 500 * Y * X ^ 2 = Real.sqrt 500 * (Y * X ^ 2) := by ring
        _ ≤ 23 * (Y * X ^ 2) := mul_le_mul_of_nonneg_right hs500 (mul_nonneg hY0 (sq_nonneg X))
        _ ≤ 23 * (α ^ 2 + Real.sqrt α * X + Y * X ^ 2) :=
            mul_le_mul_of_nonneg_left hYX (by norm_num)
    have h4 : Real.sqrt (3000000 * α ^ 2 * X ^ 2)
        ≤ 1733 * (α ^ 2 + Real.sqrt α * X + Y * X ^ 2) := by
      have heq : Real.sqrt (3000000 * α ^ 2 * X ^ 2) = Real.sqrt 3000000 * α * X := by
        rw [show (3000000 : ℝ) * α ^ 2 * X ^ 2 = 3000000 * (α * X) ^ 2 from by ring]
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3000000),
          Real.sqrt_sq (mul_nonneg hα.le hX0)]
        ring
      rw [heq]
      have hs : Real.sqrt 3000000 ≤ 1733 := by
        rw [Real.sqrt_le_iff]
        exact ⟨by norm_num, by norm_num⟩
      have hYX : α * X ≤ α ^ 2 + Real.sqrt α * X + Y * X ^ 2 := by
        have h1 : α * X ≤ Real.sqrt α * X :=
          mul_le_mul_of_nonneg_right hsqrtale hX0
        linarith [h1, sq_nonneg α, mul_nonneg (Real.sqrt_nonneg α) hX0,
          mul_nonneg hY0 (sq_nonneg X)]
      calc Real.sqrt 3000000 * α * X = Real.sqrt 3000000 * (α * X) := by ring
        _ ≤ 1733 * (α * X) := mul_le_mul_of_nonneg_right hs (mul_nonneg hα.le hX0)
        _ ≤ 1733 * (α ^ 2 + Real.sqrt α * X + Y * X ^ 2) :=
            mul_le_mul_of_nonneg_left hYX (by norm_num)
    have h5 : Real.sqrt (800000 * α ^ 4)
        ≤ 895 * (α ^ 2 + Real.sqrt α * X + Y * X ^ 2) := by
      have heq : Real.sqrt (800000 * α ^ 4) = Real.sqrt 800000 * α ^ 2 := by
        rw [show (800000 : ℝ) * α ^ 4 = 800000 * (α ^ 2) ^ 2 from by ring]
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 800000),
          Real.sqrt_sq (by positivity : (0 : ℝ) ≤ α ^ 2)]
      rw [heq]
      have hs : Real.sqrt 800000 ≤ 895 := by
        rw [Real.sqrt_le_iff]
        exact ⟨by norm_num, by norm_num⟩
      have hYX : α ^ 2 ≤ α ^ 2 + Real.sqrt α * X + Y * X ^ 2 := by
        linarith [mul_nonneg (Real.sqrt_nonneg α) hX0, mul_nonneg hY0 (sq_nonneg X)]
      calc Real.sqrt 800000 * α ^ 2 ≤ 895 * α ^ 2 :=
            mul_le_mul_of_nonneg_right hs (sq_nonneg α)
        _ ≤ 895 * (α ^ 2 + Real.sqrt α * X + Y * X ^ 2) :=
            mul_le_mul_of_nonneg_left hYX (by norm_num)
    calc Real.sqrt (7 * (A * X ^ 2 + π * B))
        ≤ Real.sqrt (500 * Y ^ 2 * X ^ 4) + Real.sqrt (3000000 * α ^ 2 * X ^ 2)
          + Real.sqrt (800000 * α ^ 4) := h1
      _ ≤ 23 * (α ^ 2 + Real.sqrt α * X + Y * X ^ 2)
          + 1733 * (α ^ 2 + Real.sqrt α * X + Y * X ^ 2)
          + 895 * (α ^ 2 + Real.sqrt α * X + Y * X ^ 2) := by linarith [h3, h4, h5]
      _ = 2651 * (α ^ 2 + Real.sqrt α * X + Y * X ^ 2) := by ring
  have henv0 : 0 ≤ α ^ 2 + Real.sqrt α * X + Y * X ^ 2 := by
    linarith [sq_nonneg α, mul_nonneg (Real.sqrt_nonneg α) hX0,
      mul_nonneg hY0 (sq_nonneg X)]
  have hsqrtInt : Real.sqrt (∫ r in Set.Ioi (0 : ℝ),
        7 * (A * Ψ r + ((π / 2) * B) * (1 / (1 + r)) ^ 2))
      ≤ 2651 * (α ^ 2 + Real.sqrt α * X + Y * X ^ 2) :=
    le_trans (Real.sqrt_le_sqrt hInt_le) hsqrtR
  calc |Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α g) g) 0|
      ≤ 3 * Real.sqrt (∫ r in Set.Ioi (0 : ℝ),
          7 * (A * Ψ r + ((π / 2) * B) * (1 / (1 + r)) ^ 2)) := hmain
    _ ≤ 3 * (2651 * (α ^ 2 + Real.sqrt α * X + Y * X ^ 2)) :=
        mul_le_mul_of_nonneg_left hsqrtInt (by norm_num)
    _ ≤ 10 ^ 5 * (α ^ 2 + Real.sqrt α * X + Y * X ^ 2) := by
        nlinarith [henv0]

/-! ## `rak`: the `ℋ⁴`-bound of the profile `AK α = (Γ(θ)/c(α))·2z²/(1+z)³`

`AK α` is a *product* of an angular and a radial factor, so its `ℋ⁴`-integrand splits into

* the `D_z`-block `(D_z^j ψ(z)·w z)²·Γ(θ)²·sin(2θ)^{-η}` and
* the mixed block `(D_z^j ψ(z)·w z)²·(D_θ^iΓ(θ))²·sin(2θ)^{-γ}`,

with `ψ(z) = 2z²/(1+z)³`.  The radial jets are bounded explicitly
(`(D_z^jψ·w)² ≤ 117000/(1+z)²`, `j ≤ 4`), the angular jets by `dthU_Gam_le`
(`(D_θ^iΓ)² ≤ (α·tB)²Γ²`), and the two angular weights are integrable with
`∫_θ Γ²sin(2θ)^{-η} ≤ 10000` (`sin_two_rpow`) and `∫_θ Γ²sin(2θ)^{-γ} ≤ 1000/(3α)+10001`
(`angMaj_mem`).  The `α²` of the angular jets cancels the `1/α` of the second integral, so the
resulting bound is uniform in `α ∈ (0,1]`. -/

/-- The `j`-th `D_z`-jet of `2z²/(1+z)³` weighted by the Hardy weight `w`. -/
private noncomputable def akRho (j : ℕ) (z : ℝ) : ℝ :=
  match j with
  | 0 => 2 / (1 + z)
  | 1 => 2 * (2 - z) / (1 + z) ^ 2
  | 2 => 2 * (z ^ 2 - 7 * z + 4) / (1 + z) ^ 3
  | 3 => 2 * (-z ^ 3 + 18 * z ^ 2 - 33 * z + 8) / (1 + z) ^ 4
  | _ => (2 * z ^ 4 - 82 * z ^ 3 + 342 * z ^ 2 - 262 * z + 32) / (1 + z) ^ 5

private def akNum : ℕ → ℕ → ℝ
  | 0, i => if i = 0 then 2 else 0
  | 1, i => if i = 0 then 4 else if i = 1 then -2 else 0
  | 2, i => if i = 0 then 8 else if i = 1 then -14 else if i = 2 then 2 else 0
  | 3, i => if i = 0 then 16 else if i = 1 then -66 else if i = 2 then 36
              else if i = 3 then -2 else 0
  | _, i => if i = 0 then 32 else if i = 1 then -262 else if i = 2 then 342
              else if i = 3 then -82 else if i = 4 then 2 else 0

private lemma akRho_eq (j : ℕ) (hj : j ≤ 4) (z : ℝ) :
    akRho j z = (∑ i ∈ Finset.range (j + 1), akNum j i * z ^ i) / (1 + z) ^ (j + 1) := by
  interval_cases j <;>
    · simp only [akRho, akNum]
      norm_num [Finset.sum_range_succ]
      try ring

private lemma akNum_sum_le (j : ℕ) (hj : j ≤ 4) :
    (∑ i ∈ Finset.range (j + 1), |akNum j i|) ≤ 720 := by
  interval_cases j <;> simp [akNum, Finset.sum_range_succ] <;> norm_num

private lemma akRho_abs_le (j : ℕ) (hj : j ≤ 4) {z : ℝ} (hz : 0 ≤ z) :
    |akRho j z| ≤ 720 / (1 + z) := by
  have h1 : (0 : ℝ) < 1 + z := by linarith
  have h1' : (1 : ℝ) ≤ 1 + z := by linarith
  have hsum : |∑ i ∈ Finset.range (j + 1), akNum j i * z ^ i| ≤ 720 * (1 + z) ^ j := by
    calc |∑ i ∈ Finset.range (j + 1), akNum j i * z ^ i|
        ≤ ∑ i ∈ Finset.range (j + 1), |akNum j i * z ^ i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range (j + 1), |akNum j i| * (1 + z) ^ j := by
          refine Finset.sum_le_sum (fun i hi => ?_)
          rw [Finset.mem_range] at hi
          have h2 : |z| ^ i ≤ (1 + z) ^ i := by
            refine pow_le_pow_left₀ (abs_nonneg z) ?_ i
            rw [abs_of_nonneg hz]; linarith
          have h3 : (1 + z) ^ i ≤ (1 + z) ^ j := pow_le_pow_right₀ h1' (by omega)
          rw [abs_mul, abs_pow]
          exact mul_le_mul_of_nonneg_left (le_trans h2 h3) (abs_nonneg _)
      _ = (∑ i ∈ Finset.range (j + 1), |akNum j i|) * (1 + z) ^ j := by rw [Finset.sum_mul]
      _ ≤ 720 * (1 + z) ^ j := mul_le_mul_of_nonneg_right (akNum_sum_le j hj) (by positivity)
  rw [akRho_eq j hj z, abs_div, abs_of_nonneg (by positivity : (0:ℝ) ≤ (1 + z) ^ (j + 1))]
  rw [div_le_div_iff₀ (by positivity) h1]
  calc |∑ i ∈ Finset.range (j + 1), akNum j i * z ^ i| * (1 + z)
      ≤ (720 * (1 + z) ^ j) * (1 + z) := mul_le_mul_of_nonneg_right hsum h1.le
    _ = 720 * (1 + z) ^ (j + 1) := by rw [mul_assoc, ← pow_succ]

private lemma hasDerivAt_one_add_pow (n : ℕ) (z : ℝ) :
    HasDerivAt (fun w : ℝ => (1 + w) ^ n) (n * (1 + z) ^ (n - 1)) z := by
  have h := (hasDerivAt_pow n (1 + z)).comp z
    ((hasDerivAt_const (x := z) 1).add (hasDerivAt_id z))
  simpa [Function.comp_def] using h

private lemma hasDerivAt_akPsi {z : ℝ} (hz : z ≠ -1) :
    HasDerivAt (fun z' : ℝ => 2 * z' ^ 2 / (1 + z') ^ 3)
      (2 * z * (2 - z) / (1 + z) ^ 4) z := by
  have h1 : HasDerivAt (fun z' : ℝ => 2 * z' ^ 2) (4 * z) z := by
    have h := (hasDerivAt_pow 2 z).const_mul (2 : ℝ)
    convert h using 1
    push_cast
    ring
  have h2 : HasDerivAt (fun z' : ℝ => (1 + z') ^ 3) (3 * (1 + z) ^ 2) z := by
    simpa using hasDerivAt_one_add_pow 3 z
  have h3 : (1 + z) ^ 3 ≠ 0 :=
    pow_ne_zero 3 (by intro hc; exact hz (by linarith))
  have hd := h1.div h2 h3
  convert hd using 1
  field_simp <;> ring_nf <;> norm_num

private lemma akJet1 {z : ℝ} (hz : z ≠ -1) (θ : ℝ) :
    Work.Spaces.DzIter 1 (fun z _ => 2 * z ^ 2 / (1 + z) ^ 3) z θ
      = 2 * z ^ 2 * (2 - z) / (1 + z) ^ 4 := by
  rw [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.Dz, Work.Spaces.pz]
  have h : (fun z' : ℝ => (fun z _ => 2 * z ^ 2 / (1 + z) ^ 3 : ℝ → ℝ → ℝ) z' θ)
      = fun z' : ℝ => 2 * z' ^ 2 / (1 + z') ^ 3 := rfl
  rw [h, (hasDerivAt_akPsi hz).deriv]
  ring

private lemma akJet2 {z : ℝ} (hz : z ≠ -1) (θ : ℝ) :
    Work.Spaces.DzIter 2 (fun z _ => 2 * z ^ 2 / (1 + z) ^ 3) z θ
      = 2 * z ^ 2 * (z ^ 2 - 7 * z + 4) / (1 + z) ^ 5 := by
  rw [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
  have hev : (fun z' : ℝ => Work.Spaces.DzIter 1 (fun z _ => 2 * z ^ 2 / (1 + z) ^ 3) z' θ)
      =ᶠ[𝓝 z] fun z' : ℝ => 2 * z' ^ 2 * (2 - z') / (1 + z') ^ 4 := by
    filter_upwards [isOpen_ne.mem_nhds hz] with z' hz'
    exact akJet1 hz' θ
  rw [hev.deriv_eq]
  have hd : HasDerivAt (fun z' : ℝ => 2 * z' ^ 2 * (2 - z') / (1 + z') ^ 4)
      (2 * z * (4 - 7 * z + z ^ 2) / (1 + z) ^ 5) z := by
    have h1 : HasDerivAt (fun z' : ℝ => 2 * z' ^ 2 * (2 - z')) (2 * z * (4 - 3 * z)) z := by
      have h := (hasDerivAt_pow 2 z).const_mul (2 : ℝ)
      have h' := h.mul ((hasDerivAt_const (x := z) (c := (2 : ℝ))).sub (hasDerivAt_id z))
      convert h' using 1
      · funext z'; simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Function.const_apply, id_eq]
      · simp only [Nat.reduceSub, Nat.cast_ofNat, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Function.const_apply, id_eq]; push_cast; ring
    have h2 : HasDerivAt (fun z' : ℝ => (1 + z') ^ 4) (4 * (1 + z) ^ 3) z := by
      simpa using hasDerivAt_one_add_pow 4 z
    have h3 : (1 + z) ^ 4 ≠ 0 :=
      pow_ne_zero 4 (by intro hc; exact hz (by linarith))
    have hd := h1.div h2 h3
    convert hd using 1
    field_simp <;> ring_nf <;> norm_num
  rw [hd.deriv]
  ring

private lemma akJet3 {z : ℝ} (hz : z ≠ -1) (θ : ℝ) :
    Work.Spaces.DzIter 3 (fun z _ => 2 * z ^ 2 / (1 + z) ^ 3) z θ
      = 2 * z ^ 2 * (-z ^ 3 + 18 * z ^ 2 - 33 * z + 8) / (1 + z) ^ 6 := by
  rw [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
  have hev : (fun z' : ℝ => Work.Spaces.DzIter 2 (fun z _ => 2 * z ^ 2 / (1 + z) ^ 3) z' θ)
      =ᶠ[𝓝 z] fun z' : ℝ => 2 * z' ^ 2 * (z' ^ 2 - 7 * z' + 4) / (1 + z') ^ 5 := by
    filter_upwards [isOpen_ne.mem_nhds hz] with z' hz'
    exact akJet2 hz' θ
  rw [hev.deriv_eq]
  have hd : HasDerivAt (fun z' : ℝ => 2 * z' ^ 2 * (z' ^ 2 - 7 * z' + 4) / (1 + z') ^ 5)
      (2 * z * (-z ^ 3 + 18 * z ^ 2 - 33 * z + 8) / (1 + z) ^ 6) z := by
    have h1 : HasDerivAt (fun z' : ℝ => 2 * z' ^ 2 * (z' ^ 2 - 7 * z' + 4))
        (2 * z * (8 - 21 * z + 4 * z ^ 2)) z := by
      have h := (hasDerivAt_pow 2 z).const_mul (2 : ℝ)
      have h2 : HasDerivAt (fun z' : ℝ => z' ^ 2 - 7 * z' + 4) (2 * z - 7) z := by
        have a := (hasDerivAt_pow 2 z)
        have b := (hasDerivAt_id z).const_mul (7 : ℝ)
        have c := (a.sub b).add_const 4
        convert c using 1
        · funext z'; simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Function.const_apply, id_eq]
        · simp only [Nat.reduceSub, Nat.cast_ofNat, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Function.const_apply, id_eq]; push_cast; ring
      have h' := h.mul h2
      convert h' using 1
      simp only [Nat.reduceSub, Nat.cast_ofNat, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Function.const_apply, id_eq]
      ; push_cast; ring
    have h2 : HasDerivAt (fun z' : ℝ => (1 + z') ^ 5) (5 * (1 + z) ^ 4) z := by
      simpa using hasDerivAt_one_add_pow 5 z
    have h3 : (1 + z) ^ 5 ≠ 0 :=
      pow_ne_zero 5 (by intro hc; exact hz (by linarith))
    have hd := h1.div h2 h3
    convert hd using 1
    field_simp <;> ring_nf <;> norm_num
  rw [hd.deriv]
  ring

private lemma akJet4 {z : ℝ} (hz : z ≠ -1) (θ : ℝ) :
    Work.Spaces.DzIter 4 (fun z _ => 2 * z ^ 2 / (1 + z) ^ 3) z θ
      = z ^ 2 * (2 * z ^ 4 - 82 * z ^ 3 + 342 * z ^ 2 - 262 * z + 32) / (1 + z) ^ 7 := by
  rw [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
  have hev : (fun z' : ℝ => Work.Spaces.DzIter 3 (fun z _ => 2 * z ^ 2 / (1 + z) ^ 3) z' θ)
      =ᶠ[𝓝 z] fun z' : ℝ => 2 * z' ^ 2 * (-z' ^ 3 + 18 * z' ^ 2 - 33 * z' + 8) / (1 + z') ^ 6 := by
    filter_upwards [isOpen_ne.mem_nhds hz] with z' hz'
    exact akJet3 hz' θ
  rw [hev.deriv_eq]
  have hd : HasDerivAt
      (fun z' : ℝ => 2 * z' ^ 2 * (-z' ^ 3 + 18 * z' ^ 2 - 33 * z' + 8) / (1 + z') ^ 6)
      (z * (2 * z ^ 4 - 82 * z ^ 3 + 342 * z ^ 2 - 262 * z + 32) / (1 + z) ^ 7) z := by
    have h1 : HasDerivAt (fun z' : ℝ => 2 * z' ^ 2 * (-z' ^ 3 + 18 * z' ^ 2 - 33 * z' + 8))
        (2 * z * (-5 * z ^ 3 + 72 * z ^ 2 - 99 * z + 16)) z := by
      have h := (hasDerivAt_pow 2 z).const_mul (2 : ℝ)
      have h2 : HasDerivAt (fun z' : ℝ => -z' ^ 3 + 18 * z' ^ 2 - 33 * z' + 8)
          (-3 * z ^ 2 + 36 * z - 33) z := by
        have a := (hasDerivAt_pow 3 z).neg
        have b := (hasDerivAt_pow 2 z).const_mul (18 : ℝ)
        have c := (hasDerivAt_id z).const_mul (33 : ℝ)
        have h' := ((a.add b).sub c).add_const 8
        convert h' using 1
        · funext z'; simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Function.const_apply, id_eq]
        · simp only [Nat.reduceSub, Nat.cast_ofNat, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Function.const_apply, id_eq]; push_cast; ring
      have h' := h.mul h2
      convert h' using 1
      simp only [Nat.reduceSub, Nat.cast_ofNat, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Function.const_apply, id_eq]
      ; push_cast; ring
    have h2 : HasDerivAt (fun z' : ℝ => (1 + z') ^ 6) (6 * (1 + z) ^ 5) z := by
      simpa using hasDerivAt_one_add_pow 6 z
    have h3 : (1 + z) ^ 6 ≠ 0 :=
      pow_ne_zero 6 (by intro hc; exact hz (by linarith))
    have hd := h1.div h2 h3
    convert hd using 1
    field_simp <;> ring_nf <;> norm_num
  rw [hd.deriv]
  ring

private lemma akJet_mul_w (j : ℕ) (hj : j ≤ 4) {z : ℝ} (hz0 : z ≠ 0) (hz1 : z ≠ -1) (θ : ℝ) :
    Work.Spaces.DzIter j (fun z _ => 2 * z ^ 2 / (1 + z) ^ 3) z θ * Work.Spaces.w z
      = akRho j z := by
  have h1z : (1 : ℝ) + z ≠ 0 := by intro hc; exact hz1 (by linarith)
  interval_cases j
  · simp only [akRho, Work.Spaces.DzIter_zero]
    rw [Work.Spaces.w]
    field_simp <;> ring_nf <;> norm_num
  · rw [akJet1 hz1 θ, akRho, Work.Spaces.w]
    field_simp <;> ring_nf <;> norm_num
  · rw [akJet2 hz1 θ, akRho, Work.Spaces.w]
    field_simp <;> ring_nf <;> norm_num
  · rw [akJet3 hz1 θ, akRho, Work.Spaces.w]
    field_simp <;> ring_nf <;> norm_num
  · rw [akJet4 hz1 θ, akRho, Work.Spaces.w] <;> try norm_num
    field_simp <;> ring_nf <;> norm_num

private lemma akJet_bound (j : ℕ) (hj : j ≤ 4) {z : ℝ} (hz : 0 < z) (θ : ℝ) :
    (Work.Spaces.DzIter j (fun z _ => 2 * z ^ 2 / (1 + z) ^ 3) z θ * Work.Spaces.w z) ^ 2
      ≤ 720 ^ 2 / (1 + z) ^ 2 := by
  have hz0 : z ≠ 0 := ne_of_gt hz
  have hz1 : z ≠ -1 := by intro hc; linarith
  rw [akJet_mul_w j hj hz0 hz1 θ]
  have h := akRho_abs_le j hj hz.le
  have h2 : akRho j z ^ 2 ≤ (720 / (1 + z)) ^ 2 := by
    have h3 := pow_le_pow_left₀ (abs_nonneg (akRho j z)) h 2
    rwa [sq_abs] at h3
  calc akRho j z ^ 2 ≤ (720 / (1 + z)) ^ 2 := h2
    _ = 720 ^ 2 / (1 + z) ^ 2 := by rw [div_pow]

private theorem gamJet_sq_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (i : ℕ) (hi1 : 1 ≤ i)
    (hi4 : i ≤ 4) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) ^ 2
      ≤ (α * (∑ m ∈ Finset.range 5, Work.Spaces.tBound m 0 + 1)) ^ 2
        * (Work.Spaces.Gam α θ) ^ 2 := by
  have hbridge : Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ
      = (Work.Spaces.dthU^[i]) (fun t => Work.Spaces.Gam α t) θ := by
    have h := Work.Spaces.DthIter_decomp i (fun θ' : ℝ => Work.Spaces.Gam α θ')
      (fun _ : ℝ => (1:ℝ)) 0 θ
    simpa using h
  have hb := Work.Spaces.dthU_Gam_le i hi1 α hα hα1 θ hθ
  rw [hbridge] at *
  have htB : Work.Spaces.tBound (i - 1) 0 ≤ ∑ m ∈ Finset.range 5, Work.Spaces.tBound m 0 + 1 := by
    have h1 : Work.Spaces.tBound (i - 1) 0 ≤ ∑ m ∈ Finset.range 5, Work.Spaces.tBound m 0 := by
      refine Finset.single_le_sum (f := fun m => Work.Spaces.tBound m 0)
        (fun m _ => Work.Spaces.tBound_nonneg m 0) ?_
      simp only [Finset.mem_range]; omega
    linarith
  have hG0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
  have h2 : |(Work.Spaces.dthU^[i]) (fun t => Work.Spaces.Gam α t) θ|
      ≤ α * (∑ m ∈ Finset.range 5, Work.Spaces.tBound m 0 + 1) * Work.Spaces.Gam α θ := by
    refine le_trans hb ?_
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left htB hα.le) hG0
  have h3 := pow_le_pow_left₀ (abs_nonneg _) h2 2
  rw [sq_abs, mul_pow, mul_pow] at h3
  simpa only [mul_pow] using h3

private theorem gam_sq_eta_int_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Gam α θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) ≤ 10000 := by
  obtain ⟨hint, hbd⟩ := Work.Spaces.sin_two_rpow (-(Work.Spaces.eta))
    (by rw [Work.Spaces.eta]; norm_num) (by rw [Work.Spaces.eta]; norm_num)
  have hbd' : (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      ≤ 10000 := by
    refine le_trans hbd ?_
    rw [Work.Spaces.eta]
    norm_num
  refine le_trans (MeasureTheory.integral_mono_of_nonneg ?_ hint ?_) hbd'
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Work.Spaces.sin_two_nonneg_of_Iθ hθ) _)
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    have hG := Work.Spaces.Gam_bounds α θ hα hθ
    have hsin : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
      Real.rpow_nonneg (Work.Spaces.sin_two_nonneg_of_Iθ hθ) _
    have hle : (Work.Spaces.Gam α θ) ^ 2 ≤ 1 := by nlinarith [hG.1, hG.2]
    nlinarith [hle, hsin]

private theorem gam_sq_gam_int_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Gam α θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) ≤ 1000 / (3 * α) + 10001 := by
  obtain ⟨hint, hbd⟩ := Work.FTS.LocData.angMaj_mem α hα hα1
  refine le_trans (MeasureTheory.integral_mono_of_nonneg ?_ hint ?_) hbd
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Work.Spaces.sin_two_nonneg_of_Iθ hθ) _)
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    have hsin : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
      Real.rpow_nonneg (Work.Spaces.sin_two_nonneg_of_Iθ hθ) _
    have hsinE : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
      Real.rpow_nonneg (Work.Spaces.sin_two_nonneg_of_Iθ hθ) _
    have hG0 : 0 ≤ (Work.Spaces.Gam α θ) ^ 2 := sq_nonneg _
    have h1 : 0 ≤ (Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
      mul_nonneg hG0 hsinE
    simp only [Work.FTS.LocData.angMaj]
    linarith [mul_nonneg hG0 hsin, h1]

private theorem sepGam_split (α : ℝ) (hα : 0 < α) (k : ℕ) {ρ : ℝ → ℝ} {R Rθ : ℝ}
    (hR : 0 ≤ R) (hRθ : 0 ≤ Rθ)
    (hB : ∀ j ≤ k, ∀ z ∈ Work.Spaces.Iz, ∀ θ' : ℝ,
      (Work.Spaces.DzIter j (fun z _ => ρ z) z θ' * Work.Spaces.w z) ^ 2 ≤ R / (1 + z) ^ 2)
    (hΓ : ∀ i, 1 ≤ i → i ≤ k → ∀ θ' ∈ Work.Spaces.Iθ,
      (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ') ^ 2
        ≤ Rθ * (Work.Spaces.Gam α θ') ^ 2)
    {z : ℝ} (hz : z ∈ Work.Spaces.Iz) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α k (fun z θ => ρ z * Work.Spaces.Gam α θ) z θ
      ≤ ((k + 1 : ℕ) : ℝ) * R / (1 + z) ^ 2
          * ((Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        + (((k + 1) ^ 2 : ℕ) : ℝ) * (R * Rθ) / (1 + z) ^ 2
          * ((Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
  have hs0 : 0 ≤ Real.sin (2 * θ) := Work.FTS.LocData.ZFBase.sin_two_nonneg_Iθ hθ
  have hden : 0 ≤ (1 + z) ^ 2 := by positivity
  have hG0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
  have hG2 : 0 ≤ (Work.Spaces.Gam α θ) ^ 2 := sq_nonneg _
  have hsinE : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := Real.rpow_nonneg hs0 _
  have hsinG : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := Real.rpow_nonneg hs0 _
  have hT1 : (∑ i ∈ Finset.range (k + 1),
        (Work.Spaces.DzIter i (fun z θ => ρ z * Work.Spaces.Gam α θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ≤ ∑ _i ∈ Finset.range (k + 1),
          (R / (1 + z) ^ 2 * ((Work.Spaces.Gam α θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) := by
    refine Finset.sum_le_sum (fun i hi => ?_)
    have hik : i ≤ k := by rw [Finset.mem_range] at hi; omega
    rw [congrFun (congrFun (Work.FTS.LocDataExt.DzIter_sepGam α ρ i) z) θ,
      Work.FTS.Nonlinear.Pieces.sep_sq1_loc (Work.Spaces.DzIter i (fun z _ => ρ z) z θ)
        (Work.Spaces.Gam α θ) (Work.Spaces.w z) (Real.sin (2 * θ)) (Work.Spaces.eta) hs0]
    exact mul_le_mul_of_nonneg_right (hB i hik z hz θ) (mul_nonneg hG2 hsinE)
  have hT2 : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k then
          (Work.Spaces.mixed j i (fun z θ => ρ z * Work.Spaces.Gam α θ) z θ
            * Work.Spaces.Wt α z θ) ^ 2 else 0))
      ≤ ∑ _i ∈ Finset.range (k + 1), ∑ _j ∈ Finset.range (k + 1),
          (R * Rθ / (1 + z) ^ 2 * ((Work.Spaces.Gam α θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))) := by
    refine Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun j hj => ?_))
    by_cases hc : 1 ≤ i ∧ i + j ≤ k
    · rw [if_pos hc]
      rw [Finset.mem_range] at hi hj
      rw [congrFun (congrFun (Work.FTS.LocDataExt.mixed_sepGam α ρ j i) z) θ,
        Work.Spaces.Wt, Work.Spaces.wTheta,
        Work.FTS.Nonlinear.Pieces.sep_sq2_loc (Work.Spaces.DzIter j (fun z _ => ρ z) z θ)
          (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) (Work.Spaces.w z)
          (Real.sin (2 * θ)) (Work.Spaces.gam α) hs0]
      have h1 := hB j (by omega) z hz θ
      have h2 := hΓ i hc.1 (by omega) θ hθ
      calc (Work.Spaces.DzIter j (fun z _ => ρ z) z θ * Work.Spaces.w z) ^ 2
            * ((Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
          ≤ (R / (1 + z) ^ 2) * (Rθ * (Work.Spaces.Gam α θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
            refine mul_le_mul h1 ?_ (mul_nonneg (sq_nonneg _) hsinG) (by positivity)
            exact mul_le_mul_of_nonneg_right h2 hsinG
        _ = R * Rθ / (1 + z) ^ 2 * ((Work.Spaces.Gam α θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by ring
    · rw [if_neg hc]
      exact mul_nonneg (div_nonneg (mul_nonneg hR hRθ) hden)
        (mul_nonneg hG2 hsinG)
  have hHk : Work.Spaces.HkIntegrand α k (fun z θ => ρ z * Work.Spaces.Gam α θ) z θ
      = (∑ i ∈ Finset.range (k + 1),
          (Work.Spaces.DzIter i (fun z θ => ρ z * Work.Spaces.Gam α θ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k then
              (Work.Spaces.mixed j i (fun z θ => ρ z * Work.Spaces.Gam α θ) z θ
                * Work.Spaces.Wt α z θ) ^ 2 else 0) := rfl
  rw [hHk]
  refine le_trans (add_le_add hT1 hT2) ?_
  have h1 : (∑ _i ∈ Finset.range (k + 1),
        (R / (1 + z) ^ 2 * ((Work.Spaces.Gam α θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))))
      = ((k + 1 : ℕ) : ℝ) * (R / (1 + z) ^ 2 * ((Work.Spaces.Gam α θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have h2 : (∑ _i ∈ Finset.range (k + 1), ∑ _j ∈ Finset.range (k + 1),
        (R * Rθ / (1 + z) ^ 2 * ((Work.Spaces.Gam α θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))))
      = (((k + 1) ^ 2 : ℕ) : ℝ) * (R * Rθ / (1 + z) ^ 2
          * ((Work.Spaces.Gam α θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))) := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]
    push_cast
    ring
  rw [h1, h2]
  exact le_of_eq (by ring)

private theorem sepGam_int (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {ρ : ℝ → ℝ} {R Rθ : ℝ}
    (hR : 0 ≤ R) (hRθ : 0 ≤ Rθ)
    (hB : ∀ j ≤ 4, ∀ z ∈ Work.Spaces.Iz, ∀ θ' : ℝ,
      (Work.Spaces.DzIter j (fun z _ => ρ z) z θ' * Work.Spaces.w z) ^ 2 ≤ R / (1 + z) ^ 2)
    (hΓ : ∀ i, 1 ≤ i → i ≤ 4 → ∀ θ' ∈ Work.Spaces.Iθ,
      (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ') ^ 2
        ≤ Rθ * (Work.Spaces.Gam α θ') ^ 2) :
    Work.Spaces.HkSq α 4 (fun z θ => ρ z * Work.Spaces.Gam α θ)
      ≤ 2 * (5 * R * 10000 + 25 * (R * Rθ) * (1000 / (3 * α) + 10001)) := by
  obtain ⟨hintE, hbdE⟩ := Work.Spaces.sin_two_rpow (-(Work.Spaces.eta))
    (by rw [Work.Spaces.eta]; norm_num) (by rw [Work.Spaces.eta]; norm_num)
  obtain ⟨hintM, hbdM⟩ := Work.FTS.LocData.angMaj_mem α hα hα1
  have hEta1 : (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) ≤ 10000 := by
    refine le_trans hbdE ?_
    rw [Work.Spaces.eta]; norm_num
  have hinner : ∀ z : ℝ, 0 ≤ z →
      (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 4 (fun z θ => ρ z * Work.Spaces.Gam α θ) z θ)
      ≤ (5 * R * 10000 + 25 * (R * Rθ) * (1000 / (3 * α) + 10001)) * (1 / (1 + z)) ^ 2 := by
    intro z hz
    have h1z : 0 < 1 + z := by linarith
    have hden : (0 : ℝ) ≤ (1 + z) ^ 2 := by positivity
    have hmaj : MeasureTheory.IntegrableOn
        (fun θ : ℝ => 5 * R / (1 + z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
          + 25 * (R * Rθ) / (1 + z) ^ 2 * Work.FTS.LocData.angMaj α θ) Work.Spaces.Iθ := by
      have h1 : MeasureTheory.IntegrableOn
          (fun θ : ℝ => 5 * R / (1 + z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
          Work.Spaces.Iθ := hintE.const_mul _
      have h2 : MeasureTheory.IntegrableOn
          (fun θ : ℝ => 25 * (R * Rθ) / (1 + z) ^ 2 * Work.FTS.LocData.angMaj α θ)
          Work.Spaces.Iθ := hintM.const_mul _
      exact h1.add h2
    refine le_trans (MeasureTheory.integral_mono_of_nonneg ?_ hmaj ?_) ?_
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      exact Work.Spaces.HkIntegrand_nonneg α 4 _ z θ
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      have hs0 : 0 ≤ Real.sin (2 * θ) := Work.FTS.LocData.ZFBase.sin_two_nonneg_Iθ hθ
      have hG := Work.Spaces.Gam_bounds α θ hα hθ
      have hG2 : 0 ≤ (Work.Spaces.Gam α θ) ^ 2 := sq_nonneg _
      have hsinE : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := Real.rpow_nonneg hs0 _
      have hsinG : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := Real.rpow_nonneg hs0 _
      have hsplit := sepGam_split α hα 4 hR hRθ hB hΓ (z := z) hz (θ := θ) hθ
      refine le_trans hsplit ?_
      have hA : 5 * R / (1 + z) ^ 2 * ((Work.Spaces.Gam α θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
          ≤ 5 * R / (1 + z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
        have hle : (Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
            ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
          have hle1 : (Work.Spaces.Gam α θ) ^ 2 ≤ 1 := by nlinarith [hG.1, hG.2]
          calc (Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
              ≤ 1 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
                mul_le_mul_of_nonneg_right hle1 hsinE
            _ = (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := one_mul _
        exact mul_le_mul_of_nonneg_left hle (div_nonneg (by linarith) hden)
      have hB' : 25 * (R * Rθ) / (1 + z) ^ 2 * ((Work.Spaces.Gam α θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
          ≤ 25 * (R * Rθ) / (1 + z) ^ 2 * Work.FTS.LocData.angMaj α θ := by
        have hle := Work.FTS.Nonlinear.Pieces.Gam_sq_rpow_le_angMaj_gam_loc α hθ
        exact mul_le_mul_of_nonneg_left hle (div_nonneg (by nlinarith [hR, hRθ]) hden)
      linarith [hA, hB']
    · have hnum : 5 * R * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
            + 25 * (R * Rθ) * (∫ θ in Work.Spaces.Iθ, Work.FTS.LocData.angMaj α θ)
          ≤ 5 * R * 10000 + 25 * (R * Rθ) * (1000 / (3 * α) + 10001) := by
        have h1 : 5 * R * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
            ≤ 5 * R * 10000 := mul_le_mul_of_nonneg_left hEta1 (by linarith)
        have h2 : 25 * (R * Rθ) * (∫ θ in Work.Spaces.Iθ, Work.FTS.LocData.angMaj α θ)
            ≤ 25 * (R * Rθ) * (1000 / (3 * α) + 10001) :=
          mul_le_mul_of_nonneg_left hbdM (by nlinarith [hR, hRθ])
        linarith
      have hX : 5 * R / (1 + z) ^ 2
            * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
          + 25 * (R * Rθ) / (1 + z) ^ 2
            * (∫ θ in Work.Spaces.Iθ, Work.FTS.LocData.angMaj α θ)
          = (5 * R * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
              + 25 * (R * Rθ) * (∫ θ in Work.Spaces.Iθ, Work.FTS.LocData.angMaj α θ))
            / (1 + z) ^ 2 := by
        field_simp
        try ring
      have hY : (5 * R * 10000 + 25 * (R * Rθ) * (1000 / (3 * α) + 10001))
            * (1 / (1 + z)) ^ 2
          = (5 * R * 10000 + 25 * (R * Rθ) * (1000 / (3 * α) + 10001))
            / (1 + z) ^ 2 := by
        field_simp
        try ring
      rw [MeasureTheory.integral_add (hintE.const_mul _) (hintM.const_mul _),
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, hX, hY]
      exact div_le_div_of_nonneg_right hnum hden
  rw [Work.Spaces.HkSq, Work.Spaces.Iz,
    MeasureTheory.setIntegral_congr_set MeasureTheory.Ioi_ae_eq_Ici.symm]
  have hInt2 : MeasureTheory.IntegrableOn
      (fun z : ℝ => (5 * R * 10000 + 25 * (R * Rθ) * (1000 / (3 * α) + 10001))
        * (1 / (1 + z)) ^ 2) (Set.Ioi 0) :=
    Work.FTS.H2.InvOneAddSq.1.const_mul _
  have hmono : (∫ z in Set.Ioi (0 : ℝ), ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 4 (fun z θ => ρ z * Work.Spaces.Gam α θ) z θ)
      ≤ ∫ z in Set.Ioi (0 : ℝ),
          (5 * R * 10000 + 25 * (R * Rθ) * (1000 / (3 * α) + 10001))
            * (1 / (1 + z)) ^ 2 := by
    refine MeasureTheory.integral_mono_of_nonneg ?_ hInt2 ?_
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
      exact MeasureTheory.integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 4 _ z θ
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
      have hz0 : (0:ℝ) < z := hz
      exact hinner z hz0.le
  refine le_trans hmono ?_
  have hval : (∫ z in Set.Ioi (0 : ℝ),
        (5 * R * 10000 + 25 * (R * Rθ) * (1000 / (3 * α) + 10001)) * (1 / (1 + z)) ^ 2)
      = (5 * R * 10000 + 25 * (R * Rθ) * (1000 / (3 * α) + 10001))
        * (∫ z in Set.Ioi (0 : ℝ), (1 / (1 + z)) ^ 2) :=
    MeasureTheory.integral_const_mul _ _
  rw [hval]
  have h2 : (∫ z in Set.Ioi (0 : ℝ), (1 / (1 + z)) ^ 2) ≤ 2 :=
    Work.FTS.H2.InvOneAddSq.2
  have hC0 : 0 ≤ 5 * R * 10000 + 25 * (R * Rθ) * (1000 / (3 * α) + 10001) := by
    have h1 : 0 ≤ 5 * R * 10000 := by positivity
    have h2' : 0 ≤ 25 * (R * Rθ) * (1000 / (3 * α) + 10001) := by
      refine mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg hR hRθ)) ?_
      have : 0 < 3 * α := by linarith
      positivity
    linarith
  calc (5 * R * 10000 + 25 * (R * Rθ) * (1000 / (3 * α) + 10001))
        * (∫ z in Set.Ioi (0 : ℝ), (1 / (1 + z)) ^ 2)
      ≤ (5 * R * 10000 + 25 * (R * Rθ) * (1000 / (3 * α) + 10001)) * 2 :=
        mul_le_mul_of_nonneg_left h2 hC0
    _ = 2 * (5 * R * 10000 + 25 * (R * Rθ) * (1000 / (3 * α) + 10001)) := by ring

theorem rak_bound : ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ}, 0 < α → α ≤ 1 →
    Work.FTS.Nonlin.Xn α (Work.Construction.AK α) ≤ K := by
  set tB : ℝ := (∑ m ∈ Finset.range 5, Work.Spaces.tBound m 0) + 1 with htBdef
  have htB0 : 0 ≤ tB := by
    rw [htBdef]
    have h : 0 ≤ ∑ m ∈ Finset.range 5, Work.Spaces.tBound m 0 :=
      Finset.sum_nonneg (fun m _ => Work.Spaces.tBound_nonneg m 0)
    linarith
  refine ⟨Real.sqrt (2 * (5 * (720 ^ 2 * 100) * 10000
      + 25 * (720 ^ 2 * 100) * tB ^ 2 * (1000 / 3 + 10001))) + 1, by positivity, ?_⟩
  intro α hα hα1
  obtain ⟨hc1, hc2⟩ := Work.Spaces.c_bounds α hα hα1
  have hc0 : (0 : ℝ) < Work.Spaces.c α := by linarith
  have hform : Work.Construction.AK α
      = fun z θ => (2 * z ^ 2 / (1 + z) ^ 3 / Work.Spaces.c α) * Work.Spaces.Gam α θ := by
    funext z θ
    rw [Work.Construction.AK]
    ring
  set c : ℝ := Work.Spaces.c α with hcdef
  have hc0' : (0 : ℝ) < c := hcdef ▸ hc0
  set Rθ : ℝ := (α * tB) ^ 2 with hRθdef
  have hRθ0 : 0 ≤ Rθ := by rw [hRθdef]; positivity
  set R : ℝ := 720 ^ 2 / c ^ 2 with hRdef
  have hR0 : 0 ≤ R := by rw [hRdef]; positivity
  rw [hform]
  have hB : ∀ j ≤ 4, ∀ z ∈ Work.Spaces.Iz, ∀ θ' : ℝ,
      (Work.Spaces.DzIter j (fun z _ => 2 * z ^ 2 / (1 + z) ^ 3 / c) z θ'
        * Work.Spaces.w z) ^ 2 ≤ R / (1 + z) ^ 2 := by
    intro j hj z hz θ'
    rcases eq_or_lt_of_le (show (0:ℝ) ≤ z from hz) with hz0 | hzpos
    · subst hz0
      have hw0 : Work.Spaces.w 0 = 0 := by simp [Work.Spaces.w]
      rw [hw0, mul_zero, sq, zero_mul]
      exact div_nonneg hR0 (by positivity)
    · have hsplit : Work.Spaces.DzIter j (fun z _ => 2 * z ^ 2 / (1 + z) ^ 3 / c) z θ'
          = (1 / c) * Work.Spaces.DzIter j (fun z _ => 2 * z ^ 2 / (1 + z) ^ 3) z θ' := by
        have hfun : (fun z' θ'' : ℝ => 2 * z' ^ 2 / (1 + z') ^ 3 / c)
            = fun z' θ'' : ℝ => (1 / c) * (2 * z' ^ 2 / (1 + z') ^ 3) := by
          funext z' θ''; ring
        rw [hfun]
        exact congrFun (congrFun (Work.FTS.Nonlinear.Pieces.RowsN0Aux.DzIter_const_mul j (1 / c)
          (fun z _ => 2 * z ^ 2 / (1 + z) ^ 3)) z) θ'
      rw [hsplit, mul_assoc, mul_pow]
      have hReq : R = (1 / c) ^ 2 * 720 ^ 2 := by
        rw [hRdef]
        ring
      rw [hReq]
      calc (1 / c) ^ 2 * (Work.Spaces.DzIter j (fun z _ => 2 * z ^ 2 / (1 + z) ^ 3) z θ'
              * Work.Spaces.w z) ^ 2
          ≤ (1 / c) ^ 2 * (720 ^ 2 / (1 + z) ^ 2) :=
            mul_le_mul_of_nonneg_left (akJet_bound j hj hzpos θ') (sq_nonneg _)
        _ = (1 / c) ^ 2 * 720 ^ 2 / (1 + z) ^ 2 := by ring
  have hΓ : ∀ i, 1 ≤ i → i ≤ 4 → ∀ θ' ∈ Work.Spaces.Iθ,
      (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ') ^ 2
        ≤ Rθ * (Work.Spaces.Gam α θ') ^ 2 := by
    intro i hi1 hi4 θ' hθ'
    rw [hRθdef, htBdef]
    exact gamJet_sq_le α hα hα1 i hi1 hi4 hθ'
  have hmain := sepGam_int α hα hα1 hR0 hRθ0 hB hΓ
  have hRle : R ≤ 720 ^ 2 * 100 := by
    rw [hRdef, div_le_iff₀ (by positivity)]
    nlinarith [hc1, hc0']
  have hkey : Rθ * (1000 / (3 * α) + 10001) ≤ tB ^ 2 * (1000 / 3 + 10001) := by
    have hdiv : α ^ 2 * (1000 / (3 * α)) = α * (1000 / 3) := by
      field_simp
      try ring
    have h1 : (α * tB) ^ 2 * (1000 / (3 * α)) ≤ tB ^ 2 * (1000 / 3) := by
      rw [mul_pow]
      have hle : α ^ 2 * (1000 / (3 * α)) ≤ 1000 / 3 := by
        rw [hdiv]; nlinarith [hα.le, hα1]
      calc α ^ 2 * tB ^ 2 * (1000 / (3 * α))
          = tB ^ 2 * (α ^ 2 * (1000 / (3 * α))) := by ring
        _ ≤ tB ^ 2 * (1000 / 3) := mul_le_mul_of_nonneg_left hle (sq_nonneg tB)
    have h2 : (α * tB) ^ 2 * 10001 ≤ tB ^ 2 * 10001 := by
      rw [mul_pow]
      have hα2 : α ^ 2 ≤ 1 := by nlinarith [hα.le, hα1]
      have hle : α ^ 2 * tB ^ 2 ≤ tB ^ 2 := by
        calc α ^ 2 * tB ^ 2 ≤ 1 * tB ^ 2 := mul_le_mul_of_nonneg_right hα2 (sq_nonneg tB)
          _ = tB ^ 2 := one_mul _
      linarith
    have h12 := add_le_add h1 h2
    rw [hRθdef]
    calc (α * tB) ^ 2 * (1000 / (3 * α) + 10001)
        = (α * tB) ^ 2 * (1000 / (3 * α)) + (α * tB) ^ 2 * 10001 := by ring
      _ ≤ tB ^ 2 * (1000 / 3) + tB ^ 2 * 10001 := h12
      _ = tB ^ 2 * (1000 / 3 + 10001) := by ring
  have hbound : 2 * (5 * R * 10000 + 25 * (R * Rθ) * (1000 / (3 * α) + 10001))
      ≤ 2 * (5 * (720 ^ 2 * 100) * 10000
          + 25 * (720 ^ 2 * 100) * tB ^ 2 * (1000 / 3 + 10001)) := by
    have h1 : 5 * R * 10000 ≤ 5 * (720 ^ 2 * 100) * 10000 := by linarith
    have h2 : 25 * (R * Rθ) * (1000 / (3 * α) + 10001)
        ≤ 25 * (720 ^ 2 * 100) * (tB ^ 2 * (1000 / 3 + 10001)) := by
      have hstep : R * (Rθ * (1000 / (3 * α) + 10001))
          ≤ (720 ^ 2 * 100) * (tB ^ 2 * (1000 / 3 + 10001)) :=
        mul_le_mul hRle hkey (by positivity) (by positivity)
      calc 25 * (R * Rθ) * (1000 / (3 * α) + 10001)
          = 25 * (R * (Rθ * (1000 / (3 * α) + 10001))) := by ring
        _ ≤ 25 * ((720 ^ 2 * 100) * (tB ^ 2 * (1000 / 3 + 10001))) :=
            mul_le_mul_of_nonneg_left hstep (by norm_num)
        _ = 25 * (720 ^ 2 * 100) * (tB ^ 2 * (1000 / 3 + 10001)) := by ring
    linarith
  refine le_trans (Real.sqrt_le_sqrt hmain) ?_
  refine le_trans (Real.sqrt_le_sqrt hbound) ?_
  exact le_add_of_nonneg_right (by norm_num : (0:ℝ) ≤ 1)


/-! ## The four rows of `AuxRows` -/

/-- **`AuxRows`**: the `ℋ⁴`-bound of `AK` and the three zero-mode estimates `rl0`--`rl2`. -/
theorem rowsAux (IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ)
    {α₂ Ci Ct Ce Cs : ℝ} (hN : Work.FTS.Nonlin.N4Norm Ci α₂)
    (hE : Work.FTS.Nonlin.N4Extra IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      Work.FTS.Nonlin.GalClass α g → Work.FTS.Nonlin.StarPkg α Cs Φs →
      Work.FTS.Nonlin.EllPkgG α Ce g Φg → 0 < α → α ≤ 1 → α ≤ α₂ →
      Work.FTS.Nonlinear.Pieces.AuxRows IP α K g Φs Φg := by
  obtain ⟨K1, hK1pos, hK1⟩ := rak_bound
  obtain ⟨K2, hK2pos, hK2⟩ := rl0_bound
  obtain ⟨K4, hK4pos, hK4⟩ := rl2_bound
  obtain ⟨K3, hK3pos, hK3⟩ := Work.FTS.Nonlinear.Pieces.Rl1.rl1Main (α₂ := α₂) (Ci := Ci) (Ce := Ce) (Cs := Cs) hN
  have hpos : (0 : ℝ) < K1 + K2 + K3 + K4 + 1 := by linarith
  refine ⟨K1 + K2 + K3 + K4 + 1, hpos, ?_⟩
  intro α g Φs Φg hg hsp hep hα hα1 hαα₂
  have hK1le : K1 ≤ K1 + K2 + K3 + K4 + 1 := by linarith
  have hK2le : K2 ≤ K1 + K2 + K3 + K4 + 1 := by linarith
  have hK3le : K3 ≤ K1 + K2 + K3 + K4 + 1 := by linarith
  have hK4le : K4 ≤ K1 + K2 + K3 + K4 + 1 := by linarith
  have hX0 : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hbr0 : 0 ≤ α ^ 2 + Real.sqrt α * Work.FTS.Nonlin.Xn α g
      + α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2 := by
    have h2 : 0 ≤ Real.sqrt α * Work.FTS.Nonlin.Xn α g := mul_nonneg (Real.sqrt_nonneg _) hX0
    have h3 : 0 ≤ α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2 :=
      mul_nonneg (Real.rpow_nonneg hα.le _) (sq_nonneg _)
    nlinarith [sq_nonneg α, hX0]
  have hreg4 : Work.FTS.Nonlin.RegQ α 4 g :=
    Work.FTS.GalerkinFix.RegQ.regQ_mono hg.reg (by norm_num)
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact le_trans (hK1 hα hα1) hK1le
  · refine le_trans (hK2 hα hα1 hN hαα₂ hg) ?_
    exact mul_le_mul_of_nonneg_right hK2le hbr0
  · refine le_trans (hK3 hg hsp hep hα hα1 hαα₂) ?_
    exact mul_le_mul_of_nonneg_right hK3le hbr0
  · refine le_trans (hK4 hα hα1 hreg4.1 hreg4.2.1) ?_
    exact mul_le_mul_of_nonneg_right hK4le hX0

end Work.FTS.Nonlinear.Pieces
