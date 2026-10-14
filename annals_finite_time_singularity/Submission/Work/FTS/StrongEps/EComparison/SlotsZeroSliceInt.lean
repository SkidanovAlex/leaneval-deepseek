import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.FTS.CoercivityFix.Transfer.E2norm.A_sq_prod_le
import Submission.Work.FTS.EllipticEst.HarOp_pointwise_sq
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.Galerkin.Inhabit.regPkg_zero
import Submission.Work.FTS.LocData.zero_slice_locG
import Submission.Work.FTS.LocDataExt.oneSubChi_jet_le5
import Submission.Work.FTS.Nonlinear.FstarPkgAll
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.FzFacts
import Submission.Work.FTS.Nonlinear.Pieces.splitsDiff
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongEps.EpsE4Thr.TracesAux.BdryTraces_psi_mul_open
import Submission.Work.FTS.StrongEps.H5.Atoms.SinSqSlot5
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.FKdzIter_sq_le
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS.TransportS.GalSide
import Submission.Work.FTS.VocabO
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_RegExport.RXT.Sys.abs_L12dens_Fstar_add_le
import Submission.Work.FTS_RegExport.RXT.Sys.hasDerivAt_mixed_z
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.SupAbsThOAesm
import Submission.Work.LWP.Main
import Submission.Work.SolutionDelivery.DatumOdd
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Stability.Cutoff
import Submission.Work.Stability.mul_rpow_le
import Submission.Work.StabilityFar.Decay.KernelDefs
import Submission.Work.StabilityFar.Decay.biotSavart_fderiv
import Submission.Work.StabilityFar.Decay.fderiv_timeHolder
import Submission.Work.StabilityFar.FarDerivLipschitz
import Submission.Work.StabilityFar.Holder.holderOnWith_of_norm_le
import Submission.Work.StabilityFar.St5
-- ===== merged: Submission.Work.CoreResiduals.BiotSavart.WindowExtDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Filter Topology MeasureTheory
open scoped Topology

namespace Work.CoreResiduals.BiotSavart

/-- The two-sided time-extension of the vorticity `ω` beyond the strip `Icc 0 S`:
the strip value on `Icc 0 S`, the affine continuation with the endpoint time-derivative below `0`
and above `S`. -/
noncomputable def windowExt (ω : R3 → ℝ → R3) (S : ℝ) : R3 → ℝ → R3 :=
  fun y t => if t ≤ 0 then ω y 0 + t • FiniteTimeSingularity.timeDeriv ω y 0
    else if t ≤ S then ω y t
    else ω y S + (t - S) • FiniteTimeSingularity.timeDeriv ω y S

/-- The "slices of `∂ₜ`" of the extension: `∂ₜω(·,0)` for `t ≤ 0`, `∂ₜω(·,t)` inside the strip and
`∂ₜω(·,S)` above.  It is the time derivative of `windowExt` (`timeDeriv_windowExt`). -/
noncomputable def dtExt (ω : R3 → ℝ → R3) (S : ℝ) : R3 → ℝ → R3 :=
  fun y t => if t ≤ 0 then FiniteTimeSingularity.timeDeriv ω y 0
    else if t ≤ S then FiniteTimeSingularity.timeDeriv ω y t
    else FiniteTimeSingularity.timeDeriv ω y S

variable {ω : R3 → ℝ → R3} {S : ℝ} {y : R3} {t : ℝ}

theorem windowExt_of_nonpos (ht : t ≤ 0) :
    windowExt ω S y t = ω y 0 + t • FiniteTimeSingularity.timeDeriv ω y 0 := by
  unfold windowExt; rw [if_pos ht]

theorem windowExt_of_mem_Icc (ht : t ∈ Set.Icc (0:ℝ) S) : windowExt ω S y t = ω y t := by
  unfold windowExt
  rcases eq_or_lt_of_le ht.1 with h | h
  · subst h; simp
  · rw [if_neg (not_le.mpr h), if_pos ht.2]

theorem windowExt_of_ge (hS : 0 < S) (ht : S ≤ t) :
    windowExt ω S y t = ω y S + (t - S) • FiniteTimeSingularity.timeDeriv ω y S := by
  unfold windowExt
  have h0 : ¬ t ≤ 0 := by linarith
  rw [if_neg h0]
  by_cases h : t ≤ S
  · rw [if_pos h]; have htS : t = S := le_antisymm h ht; rw [htS]; simp
  · rw [if_neg h]

theorem dtExt_of_nonpos (ht : t ≤ 0) :
    dtExt ω S y t = FiniteTimeSingularity.timeDeriv ω y 0 := by
  unfold dtExt; rw [if_pos ht]

theorem dtExt_of_mem_Icc (ht : t ∈ Set.Icc (0:ℝ) S) :
    dtExt ω S y t = FiniteTimeSingularity.timeDeriv ω y t := by
  unfold dtExt
  rcases eq_or_lt_of_le ht.1 with h | h
  · subst h; simp
  · rw [if_neg (not_le.mpr h), if_pos ht.2]

theorem dtExt_of_ge (hS : 0 < S) (ht : S ≤ t) :
    dtExt ω S y t = FiniteTimeSingularity.timeDeriv ω y S := by
  unfold dtExt
  have h0 : ¬ t ≤ 0 := by linarith
  rw [if_neg h0]
  by_cases h : t ≤ S
  · rw [if_pos h]; have htS : t = S := le_antisymm h ht; rw [htS]
  · rw [if_neg h]

/-- `dtExt` is the composition of the `∂ₜ`-slice with the clamping map `t ↦ max 0 (min t S)`. -/
theorem dtExt_eq_clamp (hS : 0 < S) :
    dtExt ω S y t = FiniteTimeSingularity.timeDeriv ω y (max 0 (min t S)) := by
  by_cases h : t ≤ 0
  · rw [dtExt_of_nonpos h]
    congr 1
    rw [min_eq_left (by linarith : t ≤ S), max_eq_left h]
  · by_cases h2 : t ≤ S
    · rw [dtExt_of_mem_Icc ⟨le_of_lt (lt_of_not_ge h), h2⟩]
      congr 1
      rw [min_eq_left h2, max_eq_right (le_of_lt (lt_of_not_ge h))]
    · rw [dtExt_of_ge hS (le_of_lt (lt_of_not_ge h2))]
      congr 1
      rw [min_eq_right (le_of_lt (lt_of_not_ge h2)), max_eq_right (le_of_lt hS)]

/-- **Differentiability of the extension.**  If the strip slices `s ↦ ω y s` are differentiable on
`Icc 0 S` with derivative `∂ₜω(y,·)`, then `windowExt ω S y ·` is differentiable everywhere, with
derivative `dtExt ω S y ·`.  The only non-trivial points are the junctions `0` and `S`, where the
one-sided derivatives agree (they are `∂ₜω(y,0)` resp. `∂ₜω(y,S)`). -/
theorem hasDerivAt_windowExt (hS : 0 < S)
    (hdiff : ∀ t ∈ Set.Icc (0:ℝ) S, ∀ y : R3,
      HasDerivAt (fun s : ℝ => ω y s) (FiniteTimeSingularity.timeDeriv ω y t) t)
    (y : R3) (t : ℝ) :
    HasDerivAt (fun s : ℝ => windowExt ω S y s) (dtExt ω S y t) t := by
  rcases lt_trichotomy t 0 with ht | ht | ht
  · rw [dtExt_of_nonpos (le_of_lt ht)]
    have haff : HasDerivAt (fun s : ℝ => ω y 0 + s • FiniteTimeSingularity.timeDeriv ω y 0)
        (FiniteTimeSingularity.timeDeriv ω y 0) t := by
      have h1 : HasDerivAt (fun s : ℝ => s • FiniteTimeSingularity.timeDeriv ω y 0)
          ((1:ℝ) • FiniteTimeSingularity.timeDeriv ω y 0) t :=
        (hasDerivAt_id t).smul_const _
      simpa using h1.const_add (ω y 0)
    exact haff.congr_of_eventuallyEq (by
      filter_upwards [Iio_mem_nhds ht] with s hs
      exact windowExt_of_nonpos (le_of_lt hs))
  · rw [ht]
    rw [dtExt_of_nonpos (le_refl 0)]
    have haff : HasDerivAt (fun s : ℝ => ω y 0 + s • FiniteTimeSingularity.timeDeriv ω y 0)
        (FiniteTimeSingularity.timeDeriv ω y 0) 0 := by
      have h1 : HasDerivAt (fun s : ℝ => s • FiniteTimeSingularity.timeDeriv ω y 0)
          ((1:ℝ) • FiniteTimeSingularity.timeDeriv ω y 0) 0 :=
        (hasDerivAt_id 0).smul_const _
      simpa using h1.const_add (ω y 0)
    have hL : HasDerivWithinAt (fun s : ℝ => windowExt ω S y s)
        (FiniteTimeSingularity.timeDeriv ω y 0) (Set.Iic 0) 0 :=
      haff.hasDerivWithinAt.congr (fun s hs => windowExt_of_nonpos hs)
        (windowExt_of_nonpos (le_refl 0))
    have hR : HasDerivWithinAt (fun s : ℝ => windowExt ω S y s)
        (FiniteTimeSingularity.timeDeriv ω y 0) (Set.Icc 0 S) 0 :=
      (hdiff 0 ⟨le_refl 0, le_of_lt hS⟩ y).hasDerivWithinAt.congr
        (fun s hs => windowExt_of_mem_Icc hs)
        (windowExt_of_mem_Icc ⟨le_refl 0, le_of_lt hS⟩)
    have hunion := hL.union hR
    have hset : Set.Iic (0:ℝ) ∪ Set.Icc (0:ℝ) S = Set.Iic S := by
      ext x; simp only [Set.mem_union, Set.mem_Iic, Set.mem_Icc]
      constructor
      · rintro (h | ⟨h1, h2⟩) <;> linarith
      · intro hx
        by_cases h : x ≤ 0
        · exact Or.inl h
        · exact Or.inr ⟨le_of_lt (lt_of_not_ge h), hx⟩
    rw [hset] at hunion
    exact hunion.hasDerivAt
      (mem_of_superset (Iio_mem_nhds hS) (fun x hx => le_of_lt (Set.mem_Iio.mp hx)))
  · by_cases hts : t < S
    · rw [dtExt_of_mem_Icc ⟨le_of_lt ht, le_of_lt hts⟩]
      exact (hdiff t ⟨le_of_lt ht, le_of_lt hts⟩ y).congr_of_eventuallyEq (by
        filter_upwards [Ioo_mem_nhds ht hts] with s hs
        exact windowExt_of_mem_Icc ⟨le_of_lt hs.1, le_of_lt hs.2⟩)
    · by_cases htS : t = S
      · rw [htS]
        rw [dtExt_of_ge hS (le_refl S)]
        have hL : HasDerivWithinAt (fun s : ℝ => windowExt ω S y s)
            (FiniteTimeSingularity.timeDeriv ω y S) (Set.Icc 0 S) S :=
          (hdiff S ⟨le_of_lt hS, le_refl S⟩ y).hasDerivWithinAt.congr
            (fun s hs => windowExt_of_mem_Icc hs)
            (windowExt_of_mem_Icc ⟨le_of_lt hS, le_refl S⟩)
        have hR : HasDerivWithinAt (fun s : ℝ => windowExt ω S y s)
            (FiniteTimeSingularity.timeDeriv ω y S) (Set.Ici S) S := by
          have haff : HasDerivAt
              (fun s : ℝ => ω y S + (s - S) • FiniteTimeSingularity.timeDeriv ω y S)
              (FiniteTimeSingularity.timeDeriv ω y S) S := by
            have h1 : HasDerivAt
                (fun s : ℝ => (s - S) • FiniteTimeSingularity.timeDeriv ω y S)
                ((1:ℝ) • FiniteTimeSingularity.timeDeriv ω y S) S :=
              ((hasDerivAt_id S).sub_const S).smul_const _
            simpa using h1.const_add (ω y S)
          exact haff.hasDerivWithinAt.congr (fun s hs => windowExt_of_ge hS hs)
            (windowExt_of_ge hS (le_refl S))
        have hunion := hL.union hR
        have hset : Set.Icc (0:ℝ) S ∪ Set.Ici S = Set.Ici 0 := by
          ext x; simp only [Set.mem_union, Set.mem_Icc, Set.mem_Ici]
          constructor
          · rintro (⟨h1, h2⟩ | h)
            · exact h1
            · exact le_trans (le_of_lt hS) h
          · intro hx
            by_cases h : x ≤ S
            · exact Or.inl ⟨hx, h⟩
            · exact Or.inr (le_of_lt (lt_of_not_ge h))
        rw [hset] at hunion
        exact hunion.hasDerivAt
          (mem_of_superset (Ioi_mem_nhds hS) (fun x hx => le_of_lt (Set.mem_Ioi.mp hx)))
      · have hSt : S < t := lt_of_le_of_ne (le_of_not_gt hts) (Ne.symm htS)
        rw [dtExt_of_ge hS (le_of_lt hSt)]
        have haff : HasDerivAt
            (fun s : ℝ => ω y S + (s - S) • FiniteTimeSingularity.timeDeriv ω y S)
            (FiniteTimeSingularity.timeDeriv ω y S) t := by
          have h1 : HasDerivAt
              (fun s : ℝ => (s - S) • FiniteTimeSingularity.timeDeriv ω y S)
              ((1:ℝ) • FiniteTimeSingularity.timeDeriv ω y S) t :=
            ((hasDerivAt_id t).sub_const S).smul_const _
          simpa using h1.const_add (ω y S)
        exact haff.congr_of_eventuallyEq (by
          filter_upwards [Ioi_mem_nhds hSt] with s hs
          exact windowExt_of_ge hS (le_of_lt hs))

/-- The time derivative of the extension is the glued `∂ₜ`-slice `dtExt`. -/
theorem timeDeriv_windowExt (hS : 0 < S)
    (hdiff : ∀ t ∈ Set.Icc (0:ℝ) S, ∀ y : R3,
      HasDerivAt (fun s : ℝ => ω y s) (FiniteTimeSingularity.timeDeriv ω y t) t)
    (y : R3) (t : ℝ) :
    FiniteTimeSingularity.timeDeriv (windowExt ω S) y t = dtExt ω S y t :=
  (hasDerivAt_windowExt hS hdiff y t).deriv

/-- **The `∂ₜ`-slice vanishes at the strip endpoints off the support ball.**  Off `closedBall 0 R`
the strip slice `s ↦ ω y s` is identically `0` on `Icc 0 S`; the two-sided derivative at `0` (resp.
`S`) is therefore `0` (the one-sided derivative within `Ici 0` resp. `Iic S` of the constant `0`). -/
theorem timeDeriv_eq_zero_of_notMem_closedBall {ω : R3 → ℝ → R3} {R S : ℝ} (hS : 0 < S)
    (hsupp : ∀ t ∈ Set.Icc (0:ℝ) S, ∀ y : R3, ω y t ≠ 0 → y ∈ Metric.closedBall 0 R)
    (hdiff : ∀ t ∈ Set.Icc (0:ℝ) S, ∀ y : R3,
      HasDerivAt (fun s : ℝ => ω y s) (FiniteTimeSingularity.timeDeriv ω y t) t)
    {y : R3} (hy : y ∉ Metric.closedBall 0 R) :
    FiniteTimeSingularity.timeDeriv ω y 0 = 0 ∧ FiniteTimeSingularity.timeDeriv ω y S = 0 := by
  have hstrip : ∀ s ∈ Set.Icc (0:ℝ) S, ω y s = 0 := by
    intro s hs; by_contra h; exact hy (hsupp s hs y h)
  constructor
  · have h1 : HasDerivWithinAt (fun s : ℝ => ω y s) (FiniteTimeSingularity.timeDeriv ω y 0)
        (Set.Ici 0) 0 :=
      (hdiff 0 ⟨le_refl 0, le_of_lt hS⟩ y).hasDerivWithinAt
    have h2 : HasDerivWithinAt (fun s : ℝ => ω y s) 0 (Set.Ici 0) 0 := by
      have hc : HasDerivWithinAt (fun _ : ℝ => (0:R3)) 0 (Set.Ici 0) 0 :=
        (hasDerivAt_const (x := (0:ℝ)) (c := (0:R3))).hasDerivWithinAt
      refine hc.congr_of_eventuallyEq ?_ ?_
      · show ∀ᶠ s in 𝓝[Set.Ici (0:ℝ)] (0:ℝ), ω y s = 0
        rw [eventually_nhdsWithin_iff]
        filter_upwards [Iio_mem_nhds hS] with s hs hsi
        exact hstrip s ⟨hsi, le_of_lt hs⟩
      · exact hstrip 0 ⟨le_refl 0, le_of_lt hS⟩
    rw [← h1.derivWithin (uniqueDiffWithinAt_Ici 0), h2.derivWithin (uniqueDiffWithinAt_Ici 0)]
  · have h1 : HasDerivWithinAt (fun s : ℝ => ω y s) (FiniteTimeSingularity.timeDeriv ω y S)
        (Set.Iic S) S :=
      (hdiff S ⟨le_of_lt hS, le_refl S⟩ y).hasDerivWithinAt
    have h2 : HasDerivWithinAt (fun s : ℝ => ω y s) 0 (Set.Iic S) S := by
      have hc : HasDerivWithinAt (fun _ : ℝ => (0:R3)) 0 (Set.Iic S) S :=
        (hasDerivAt_const (x := S) (c := (0:R3))).hasDerivWithinAt
      refine hc.congr_of_eventuallyEq ?_ ?_
      · show ∀ᶠ s in 𝓝[Set.Iic S] S, ω y s = 0
        rw [eventually_nhdsWithin_iff]
        filter_upwards [Ioi_mem_nhds (show S / 2 < S by linarith)] with s hs hsi
        simp only [Set.mem_Ioi] at hs
        simp only [Set.mem_Iic] at hsi
        exact hstrip s ⟨by linarith, hsi⟩
      · exact hstrip S ⟨le_of_lt hS, le_refl S⟩
    rw [← h1.derivWithin (uniqueDiffWithinAt_Iic S), h2.derivWithin (uniqueDiffWithinAt_Iic S)]

/-- **The extension is supported in `closedBall 0 R`, globally in `t`.** -/
theorem windowExt_eq_zero_of_notMem_closedBall {ω : R3 → ℝ → R3} {R S : ℝ} (hS : 0 < S)
    (hsupp : ∀ t ∈ Set.Icc (0:ℝ) S, ∀ y : R3, ω y t ≠ 0 → y ∈ Metric.closedBall 0 R)
    (hdiff : ∀ t ∈ Set.Icc (0:ℝ) S, ∀ y : R3,
      HasDerivAt (fun s : ℝ => ω y s) (FiniteTimeSingularity.timeDeriv ω y t) t)
    {y : R3} (hy : y ∉ Metric.closedBall 0 R) (t : ℝ) : windowExt ω S y t = 0 := by
  have hz := timeDeriv_eq_zero_of_notMem_closedBall hS hsupp hdiff hy
  have hω : ∀ s ∈ Set.Icc (0:ℝ) S, ω y s = 0 := by
    intro s hs; by_contra h; exact hy (hsupp s hs y h)
  by_cases h : t ≤ 0
  · rw [windowExt_of_nonpos h, hω 0 ⟨le_refl 0, le_of_lt hS⟩, hz.1]; simp
  · by_cases h2 : t ≤ S
    · rw [windowExt_of_mem_Icc ⟨le_of_lt (lt_of_not_ge h), h2⟩]
      exact hω t ⟨le_of_lt (lt_of_not_ge h), h2⟩
    · rw [windowExt_of_ge hS (le_of_lt (lt_of_not_ge h2)), hω S ⟨le_of_lt hS, le_refl S⟩, hz.2]
      simp

end Work.CoreResiduals.BiotSavart
end
end
-- ===== merged: Submission.Work.CoreResiduals.BiotSavart.biotSavart_add =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

open MeasureTheory

/-- The Biot–Savart integrand `bsK` (see `Work.LWP.BiotSavart.bsK`) is additive in the vorticity:
the cross product is additive in its first slot (`Work.StabilityFar.Decay.crossL_add`, via
`Work.StabilityFar.Decay.bsK_eq_crossL`), and the scalar factor `‖x - y‖⁻³` is common. -/
lemma bsK_add (f g : Work.LWP.R3 → Work.LWP.R3) (x y : Work.LWP.R3) :
    Work.LWP.BiotSavart.bsK (fun a => f a + g a) x y
      = Work.LWP.BiotSavart.bsK f x y + Work.LWP.BiotSavart.bsK g x y := by
  rw [Work.StabilityFar.Decay.bsK_eq_crossL, Work.StabilityFar.Decay.bsK_eq_crossL,
    Work.StabilityFar.Decay.bsK_eq_crossL, Work.StabilityFar.Decay.crossL_add, add_apply]

/-- The Biot–Savart operator is additive: for an additively combined vorticity, `biotSavart` splits.  Both inputs are bounded, supported in a common ball and ae-strongly-measurable, so each integrand is dominated by `M·‖x-y‖⁻²` on that ball (integrable in `ℝ³`). -/
theorem biotSavart_add {ω₁ ω₂ : Work.LWP.R3 → Work.LWP.R3} {R M₁ M₂ : ℝ}
    (hω₁ : ∀ a, ‖ω₁ a‖ ≤ M₁) (hω₂ : ∀ a, ‖ω₂ a‖ ≤ M₂)
    (hs₁ : ∀ a, ω₁ a ≠ 0 → a ∈ Metric.closedBall 0 R)
    (hs₂ : ∀ a, ω₂ a ≠ 0 → a ∈ Metric.closedBall 0 R)
    (hm₁ : MeasureTheory.AEStronglyMeasurable ω₁ MeasureTheory.volume)
    (hm₂ : MeasureTheory.AEStronglyMeasurable ω₂ MeasureTheory.volume) (x : Work.LWP.R3) :
    Work.LWP.biotSavart (fun a => ω₁ a + ω₂ a) x
      = Work.LWP.biotSavart ω₁ x + Work.LWP.biotSavart ω₂ x := by
  -- The bounds `M₁, M₂` are non-negative, since they dominate a norm.
  have hM₁ : 0 ≤ M₁ := le_trans (norm_nonneg (ω₁ 0)) (hω₁ 0)
  have hM₂ : 0 ≤ M₂ := le_trans (norm_nonneg (ω₂ 0)) (hω₂ 0)
  -- Each integrand is Bochner-integrable: bounded and supported in `B(0,R)`, the (singular)
  -- kernel is dominated by `M·‖x-y‖⁻²` on that ball, which is integrable in `ℝ³`.
  have hi₁ : Integrable (Work.LWP.BiotSavart.bsK ω₁ x) volume :=
    Work.StabilityFar.Decay.integrable_bsK_supported hM₁ hω₁ hs₁ hm₁ x
  have hi₂ : Integrable (Work.LWP.BiotSavart.bsK ω₂ x) volume :=
    Work.StabilityFar.Decay.integrable_bsK_supported hM₂ hω₂ hs₂ hm₂ x
  -- Unfold `biotSavart` into `(4π)⁻¹ • ∫ bsK`, split the integrand pointwise, use additivity of
  -- the Bochner integral, and distribute the scalar.
  rw [Work.LWP.BiotSavart.biotSavart_apply, Work.LWP.BiotSavart.biotSavart_apply,
    Work.LWP.BiotSavart.biotSavart_apply]
  rw [integral_congr_ae (Filter.Eventually.of_forall fun y => bsK_add ω₁ ω₂ x y)]
  rw [integral_add hi₁ hi₂, smul_add]

end Work.CoreResiduals.BiotSavart
end
-- ===== merged: Submission.Work.CoreResiduals.BiotSavart.biotSavart_centered =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart


end Work.CoreResiduals.BiotSavart
end
-- ===== merged: Submission.Work.CoreResiduals.BiotSavart.biotSavart_contDiffOn_far =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped NNReal

set_option autoImplicit false

namespace Work.CoreResiduals.BiotSavart



end Work.CoreResiduals.BiotSavart
end
-- ===== merged: Submission.Work.CoreResiduals.BiotSavart.biotSavart_smul =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Matrix
open MeasureTheory

namespace Work.CoreResiduals.BiotSavart

/-- The cross product is linear in its first argument (it is Mathlib's bilinear
`Matrix.crossProduct` on `Fin 3 → ℝ`). -/
theorem crossProduct_smul_left (c : ℝ) (v w : Fin 3 → ℝ) : (c • v) ⨯₃ w = c • (v ⨯₃ w) := by
  show crossProduct (c • v) w = c • (crossProduct v w)
  rw [LinearMap.map_smul, LinearMap.smul_apply]

/-- The Biot–Savart operator is homogeneous: `BS(c·ω) = c·BS(ω)`. -/
theorem biotSavart_smul (c : ℝ) {ω : Work.LWP.R3 → Work.LWP.R3} {R M : ℝ}
    (hω : ∀ a, ‖ω a‖ ≤ M) (hs : ∀ a, ω a ≠ 0 → a ∈ Metric.closedBall 0 R)
    (hm : MeasureTheory.AEStronglyMeasurable ω MeasureTheory.volume) (x : Work.LWP.R3) :
    Work.LWP.biotSavart (fun a => c • ω a) x = c • Work.LWP.biotSavart ω x := by
  -- `biotSavart` is `(4π)⁻¹ • ∫ y, ‖x - y‖⁻³ • (ω y × (x - y))`: it is enough to pull `c`
  -- out of the integrand, which uses only the bilinearity of the cross product and the
  -- linearity of the Bochner integral (unconditional in Mathlib).
  unfold Work.LWP.biotSavart
  have hg : (fun y : Work.LWP.R3 =>
        WithLp.toLp 2 ((‖x - y‖ ^ (3 : ℕ))⁻¹ •
          crossProduct ((fun a => c • ω a) y).ofLp (x.ofLp - y.ofLp)))
      = fun y : Work.LWP.R3 =>
        c • WithLp.toLp 2 ((‖x - y‖ ^ (3 : ℕ))⁻¹ •
          crossProduct (ω y).ofLp (x.ofLp - y.ofLp)) := by
    funext y
    rw [WithLp.ofLp_smul, crossProduct_smul_left c (ω y).ofLp (x.ofLp - y.ofLp), smul_comm,
      WithLp.toLp_smul]
  rw [hg, MeasureTheory.integral_smul, smul_comm]

end Work.CoreResiduals.BiotSavart
end
-- ===== merged: Submission.Work.CoreResiduals.BiotSavart.constant_vec_integral_ball_bsK_eq_zero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

open MeasureTheory Matrix Metric


end Work.CoreResiduals.BiotSavart
end
-- ===== merged: Submission.Work.CoreResiduals.BiotSavart.farStrip_estimates_fderiv =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

open MeasureTheory

/-- **The far-field estimates for the spatial block `D(x,t) = fderiv ℝ (BS (ω·t)) x` on the strip**
`Icc 0 S` (one-sided in `t`).

This is the strip version of the three far-field inputs that `Work.StabilityFar.St4` consumes
(`Work.StabilityFar.fderiv_decay`, `Work.StabilityFar.Decay.fderiv_timeHolder`,
`Work.StabilityFar.FarDerivLipschitz`), with the *window* `Icc (-1) (T+1)`-indexed hypotheses
replaced by the strip bundle `BSAdmissibleStripFull α ω R S` restricted to `Icc 0 S` (all three
proofs are per-slice, so they adapt verbatim; the `t`-Hölder clause of the bundle is global in `y`,
which is stronger than the `TimeHolderOnBall` hypothesis of the window version).

* *bound*: `‖D(x,t)‖ ≤ 2^20 · M · R³ / ‖x‖³` for `2R ≤ ‖x‖`, `t ∈ Icc 0 S` — per-slice
  `Work.LWP.BiotSavart.farField_decay_fderiv_const` with the slice's bound and support;
* *`t`-Hölder*: `‖D(x,t) - D(x,τ)‖ ≤ At · |t-τ|^α` for `2R < ‖x‖` and `t,τ ∈ Icc 0 S` — the
  difference of the two kernels is the kernel of the difference vorticity, which is supported in
  `B(0,R)` and bounded by `H|t-τ|^α` there (bundle's time-Hölder clause);
* *`x`-Lipschitz*: `‖D(x,t) - D(y,t)‖ ≤ A‖x-y‖` for `2R < ‖x‖, 2R < ‖y‖` and `t ∈ Icc 0 S` —
  the second-order far-field estimate `Work.StabilityFar.Decay.farField_fderiv_sub_le`, per slice.

No hypothesis `0 < S` is needed (the estimates make sense for every `S`). -/
theorem farStrip_estimates_fderiv {α : NNReal} (hα : 0 < (α : ℝ)) (hα1 : (α : ℝ) < 1)
    {ω : Work.LWP.R3 → ℝ → Work.LWP.R3} {R S : ℝ}
    (hbun : Work.CoreResiduals.BSAdmissibleStripFull α ω R S) :
    ∃ M At A : ℝ, 0 ≤ M ∧ 0 ≤ At ∧ 0 ≤ A ∧
      (∀ t ∈ Set.Icc (0:ℝ) S, ∀ x : Work.LWP.R3, 2 * R ≤ ‖x‖ →
        ‖fderiv ℝ (Work.LWP.biotSavart (fun y => ω y t)) x‖
          ≤ 2 ^ 20 * M * R ^ 3 / ‖x‖ ^ 3) ∧
      (∀ x : Work.LWP.R3, 2 * R < ‖x‖ → ∀ t ∈ Set.Icc (0:ℝ) S, ∀ τ ∈ Set.Icc (0:ℝ) S,
        ‖fderiv ℝ (Work.LWP.biotSavart (fun y => ω y t)) x
          - fderiv ℝ (Work.LWP.biotSavart (fun y => ω y τ)) x‖ ≤ At * |t - τ| ^ (α : ℝ)) ∧
      (∀ t ∈ Set.Icc (0:ℝ) S, ∀ x y : Work.LWP.R3, 2 * R < ‖x‖ → 2 * R < ‖y‖ →
        ‖fderiv ℝ (Work.LWP.biotSavart (fun z => ω z t)) x
          - fderiv ℝ (Work.LWP.biotSavart (fun z => ω z t)) y‖ ≤ A * ‖x - y‖) := by
  obtain ⟨⟨hR, hsupp, ⟨M, hM⟩, ⟨H, hH⟩, ⟨N, hN⟩, hmeas⟩,
    ⟨hdc, ⟨M₁, hM₁⟩, hmeasd⟩, ⟨N₁, hN₁⟩⟩ := hbun
  -- the exponent lies in `(0,1)`; the estimates below are in fact exponent-free
  have hαpos : (0 : ℝ) < (α : ℝ) := hα
  have hαlt : (α : ℝ) < 1 := hα1
  -- positive parts of the two constants the bundle supplies
  set M₀ : ℝ := max M 0 with hM₀def
  have hM₀nn : 0 ≤ M₀ := by rw [hM₀def]; exact le_max_right M 0
  have hMle : M ≤ M₀ := by rw [hM₀def]; exact le_max_left M 0
  set N₀ : ℝ := max N 0 with hN₀def
  have hN₀nn : 0 ≤ N₀ := by rw [hN₀def]; exact le_max_right N 0
  have hNle : N ≤ N₀ := by rw [hN₀def]; exact le_max_left N 0
  -- the uniform bound and the support, per time slice of the strip
  have hslice_bdd : ∀ t ∈ Set.Icc (0:ℝ) S, ∀ a : Work.LWP.R3, ‖ω a t‖ ≤ M₀ :=
    fun t ht a => le_trans (hM t ht a) hMle
  -- the two constants of the statements
  set At : ℝ := (4 * Real.pi)⁻¹ * (N₀ * (4 / R ^ 3) * (R ^ 3 * (Real.pi * 4 / 3))) with hAtdef
  set A : ℝ := (4 * Real.pi)⁻¹ * ((M₀ * 64 / R ^ 4) * (R ^ 3 * (Real.pi * 4 / 3))) with hAdef
  have hAtnn : 0 ≤ At := by
    rw [hAtdef]
    exact mul_nonneg (by positivity)
      (mul_nonneg (mul_nonneg hN₀nn (div_nonneg (by norm_num) (pow_nonneg hR.le 3)))
        (mul_nonneg (pow_nonneg hR.le 3) (by positivity)))
  have hAnn : 0 ≤ A := by
    rw [hAdef]
    exact mul_nonneg (by positivity)
      (mul_nonneg (div_nonneg (by positivity) (pow_nonneg hR.le 4))
        (mul_nonneg (pow_nonneg hR.le 3) (by positivity)))
  refine ⟨M₀, At, A, hM₀nn, hAtnn, hAnn, ?_, ?_, ?_⟩
  · -- far-field decay of the derivative, per slice
    intro t ht x hx
    exact Work.LWP.BiotSavart.farField_decay_fderiv_const hR hM₀nn
      (hslice_bdd t ht) (hsupp t ht) x hx
  · -- time-Hölder continuity of the spatial block
    intro x hx t ht τ hτ
    have hx2 : 2 * R ≤ ‖x‖ := le_of_lt hx
    have hdt := Work.StabilityFar.Decay.biotSavart_hasFDerivAt_far (ω := fun y => ω y t)
      hR hM₀nn (hslice_bdd t ht) (hsupp t ht) (hmeas t ht) hx2
    have hdτ := Work.StabilityFar.Decay.biotSavart_hasFDerivAt_far (ω := fun y => ω y τ)
      hR hM₀nn (hslice_bdd τ hτ) (hsupp τ hτ) (hmeas τ hτ) hx2
    rw [hdt.2.fderiv, hdτ.2.fderiv]
    have hCnn : 0 ≤ N₀ * |t - τ| ^ (α : ℝ) :=
      mul_nonneg hN₀nn (Real.rpow_nonneg (abs_nonneg _) _)
    have hdiff : ∀ a ∈ Metric.closedBall (0 : Work.LWP.R3) R,
        ‖(fun y => ω y t) a - (fun y => ω y τ) a‖ ≤ N₀ * |t - τ| ^ (α : ℝ) := by
      intro a _
      exact le_trans (hN a t ht τ hτ)
        (mul_le_mul_of_nonneg_right hNle (Real.rpow_nonneg (abs_nonneg _) _))
    have hmain := bsDeriv_sub_le_of_close hR hM₀nn hCnn (hslice_bdd t ht) (hslice_bdd τ hτ)
      (hsupp t ht) (hsupp τ hτ) (hmeas t ht) (hmeas τ hτ) hdiff hx2
    calc ‖Work.StabilityFar.Decay.bsDeriv (fun y => ω y t) x
            - Work.StabilityFar.Decay.bsDeriv (fun y => ω y τ) x‖
        ≤ (4 * Real.pi)⁻¹ * ((N₀ * |t - τ| ^ (α : ℝ)) * (4 / R ^ 3))
            * (R ^ 3 * (Real.pi * 4 / 3)) := hmain
      _ = At * |t - τ| ^ (α : ℝ) := by rw [hAtdef]; ring
  · -- the far-field `x`-Lipschitz bound, per slice
    intro t ht x y hx hy
    have hx2 : 2 * R ≤ ‖x‖ := le_of_lt hx
    have hy2 : 2 * R ≤ ‖y‖ := le_of_lt hy
    have hdx := Work.StabilityFar.Decay.biotSavart_hasFDerivAt_far (ω := fun z => ω z t)
      hR hM₀nn (hslice_bdd t ht) (hsupp t ht) (hmeas t ht) hx2
    have hdy := Work.StabilityFar.Decay.biotSavart_hasFDerivAt_far (ω := fun z => ω z t)
      hR hM₀nn (hslice_bdd t ht) (hsupp t ht) (hmeas t ht) hy2
    rw [hdx.2.fderiv, hdy.2.fderiv]
    exact Work.StabilityFar.Decay.norm_bsDeriv_sub_le hR hM₀nn
      (hslice_bdd t ht) (hsupp t ht) (hmeas t ht) hx2 hy2

end Work.CoreResiduals.BiotSavart
end
-- ===== merged: Submission.Work.CoreResiduals.BiotSavart.norm_sub_le_of_timeDeriv_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

/-- **Mean value bound in time.**  If the slices `ω y ·` are differentiable on the convex set `I`
with the time derivative `∂ₜω y ·` bounded by `M₁ ≥ 0`, then `ω` is Lipschitz in `t` with constant
`M₁` on `I`.  Proof: the mean value inequality on a convex set
(`Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le`) applied to `f = ω y ·` with
`f' x = ContinuousLinearMap.toSpanSingleton ℝ (∂ₜω y x)` (`HasDerivAt.hasFDerivAt`), using that
`toSpanSingleton` is an isometry (`ContinuousLinearMap.toSpanSingletonCLE`). -/
theorem norm_sub_le_of_timeDeriv_bound {ω : Work.CoreResiduals.R3 → ℝ → Work.CoreResiduals.R3}
    {I : Set ℝ} {M₁ : ℝ} (hM₁ : 0 ≤ M₁) (hconv : Convex ℝ I)
    (hdc : ∀ t ∈ I, ∀ y : Work.CoreResiduals.R3,
      HasDerivAt (fun s : ℝ => ω y s) (FiniteTimeSingularity.timeDeriv ω y t) t)
    (hbdd : ∀ t ∈ I, ∀ y : Work.CoreResiduals.R3,
      ‖FiniteTimeSingularity.timeDeriv ω y t‖ ≤ M₁) :
    ∀ t ∈ I, ∀ s ∈ I, ∀ y : Work.CoreResiduals.R3,
      ‖ω y t - ω y s‖ ≤ M₁ * |t - s| := by
  intro t ht s hs y
  have hdiff : ∀ x ∈ I, DifferentiableAt ℝ (fun r : ℝ => ω y r) x :=
    fun x hx => (hdc x hx y).differentiableAt
  have hbound : ∀ x ∈ I, ‖deriv (fun r : ℝ => ω y r) x‖ ≤ M₁ :=
    fun x hx => by
      rw [show deriv (fun r : ℝ => ω y r) x = FiniteTimeSingularity.timeDeriv ω y x from rfl]
      exact hbdd x hx y
  have h := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound hconv hs ht
  simpa using h

end Work.CoreResiduals.BiotSavart
end
-- ===== merged: Submission.Work.CoreResiduals.BiotSavart.slicesSupportedStrip_timeDeriv =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

/-- **The `∂ₜ`-slices of a bundled strip vorticity are supported in the support ball.**

Let `ω` satisfy the full strip bundle `BSAdmissibleStripFull α ω R S` (its slices are supported in
`closedBall 0 R`) and let `0 < S`.  Then for every `t ∈ Icc 0 S` the slice `y ↦ ∂ₜω(y,t)` is
supported in `closedBall 0 R`.

**Proof sketch.**  For `R < ‖y‖`, the slice `ω(y,·)` vanishes on all of `Icc 0 S` (support clause),
so for `t ∈ Ioo 0 S` the derivative `∂ₜω(y,t)` vanishes by the two-sided argument of
`Work.StabilityFar.Decay.timeDeriv_eq_zero_of_notMem_closedBall`.  At the endpoint `t = 0` the
bundle's `HasDerivAt (fun s => ω y s) (∂ₜω y 0) 0` (a *two-sided* derivative) restricts to
`HasDerivWithinAt` on `Ioi 0`, where the function is *identically* `0` near `0` (on `(0,S)`, using
the support clause), so `0` is also a derivative there; uniqueness of the derivative within `Ioi 0`
at `0` (`UniqueDiffWithinAt ℝ (Ioi 0) 0`) gives `∂ₜω(y,0) = 0`.  Similarly at `t = S`.

**Note.**  The hypothesis `0 < S` cannot be dropped: for `S = 0` the bundle constrains the slices
only at the single time `0`, so `∂ₜω(·,0)` (the two-sided derivative) may be supported anywhere
(`ω y s := s • c y` satisfies the whole bundle and `∂ₜω y 0 = c y`).  Same caveat as
`Work.CoreResiduals.BiotSavart.timeDeriv_xHolderOn_of_stripBundle`. -/
theorem slicesSupportedStrip_timeDeriv {α : NNReal} {ω : Work.LWP.R3 → ℝ → Work.LWP.R3}
    {R S : ℝ} (hS : 0 < S) (hbun : Work.CoreResiduals.BSAdmissibleStripFull α ω R S) :
    ∀ t ∈ Set.Icc (0:ℝ) S, ∀ y : Work.LWP.R3,
      FiniteTimeSingularity.timeDeriv ω y t ≠ 0 → y ∈ Metric.closedBall 0 R := by
  -- Extract the support clause of the strip bundle.
  have hsupp : ∀ t ∈ Set.Icc (0:ℝ) S, ∀ y : Work.LWP.R3,
      ω y t ≠ 0 → y ∈ Metric.closedBall 0 R := hbun.1.2.1
  intro t ht y hy
  by_contra hmem
  -- Off the support ball the slice `s ↦ ω y s` vanishes on the whole strip.
  have hvan : ∀ s ∈ Set.Icc (0:ℝ) S, ω y s = 0 := by
    intro s hs
    by_contra hne
    exact hmem (hsupp s hs y hne)
  rcases lt_or_eq_of_le ht.2 with hlt | heq
  · -- Interior / left of the right endpoint: `ω y` vanishes on `[t, t + (S-t))`.
    refine hy (Work.StabilityFar.timeDeriv_eq_zero_of_eq_zero_on_Ico (ω := ω) (x := y)
      (t := t) (ε := S - t) (by linarith) ?_)
    intro s hs
    exact hvan s ⟨by linarith [hs.1, ht.1], by linarith [hs.2]⟩
  · -- Right endpoint `t = S`: `ω y` vanishes on `(S - S, S]`.
    rw [heq] at hy
    refine hy (Work.StabilityFar.timeDeriv_eq_zero_of_eq_zero_on_Ioc (ω := ω) (x := y)
      (t := S) (ε := S) (by linarith) ?_)
    intro s hs
    exact hvan s ⟨by linarith [hs.1], by linarith [hs.2]⟩

end Work.CoreResiduals.BiotSavart
end
-- ===== merged: Submission.Work.CoreResiduals.BiotSavart.timeDeriv_xHolderOn_of_stripBundle =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

/-- **The `∂ₜ`-slices of a bundled strip vorticity are Hölder in `x`.**

Let `0 < α < 1`, `S > 0`, and let `ω : ℝ³ × ℝ → ℝ³` satisfy `BSAdmissibleStripFull α ω R S`
(support in `closedBall 0 R`, uniform bound `M`, uniform `x`-Hölder of exponent `α` with constant
`H`, uniform `t`-Hölder of exponent `α`, measurable slices; slices `t`-differentiable with uniformly
bounded `∂ₜω` and measurable `∂ₜ`-slices; and `∂ₜω` `α`-Hölder in `t` on the strip, with constant
`N₁`).  Then the slices `x ↦ ∂ₜω(x,t)` are Hölder in `x`, uniformly on the strip `Icc 0 S`.

(The hypothesis `0 < S` cannot be dropped: for `S = 0` the strip `Icc 0 0 = {0}` is nonempty and
carries no `x`-regularity of `∂ₜω(·,0)` — e.g. `ω(x,t) = t • b(x)` with `b` bounded measurable and
not Hölder of any positive exponent satisfies the whole bundle.)

**Suggested route.**  Fix `t₀ ∈ Icc 0 S` and `a b : ℝ³`, put `ψ(s) := ω a s - ω b s`, so that
`ψ'(s) = ∂ₜω(a,s) - ∂ₜω(b,s)`, `‖ψ(s)‖ ≤ H‖a-b‖^α` for `s ∈ Icc 0 S`, and
`‖ψ'(s) - ψ'(s')‖ ≤ 2N₁|s-s'|^α` for `s,s' ∈ Icc 0 S`.  The mean value inequality
(`Convex.norm_image_sub_le_of_norm_deriv_le`) applied to `s ↦ ψ(s) - (s-t₀)•ψ'(t₀)` on an interval
`[t₀,t₀+h] ⊆ Icc 0 S` gives `h‖ψ'(t₀)‖ ≤ 2H‖a-b‖^α + 2N₁h^{1+α}/(1+α)`, so that with
`h = ‖a-b‖^{α/(1+α)}`: `‖ψ'(t₀)‖ ≤ C‖a-b‖^{α²/(1+α)}`.  This is available as long as some interval
of length `h` inside `Icc 0 S` contains `t₀`: if `h > S/2` use the crude bound
`‖ψ'(t₀)‖ ≤ 2·max M₁ 0` (note `‖a-b‖^c = h^α > (S/2)^α > 0` in that case, `c := α²/(1+α)`), while
if `h ≤ S/2` then `t₀ ≥ h` or `t₀ + h ≤ S`, so the interval may be taken to the left or to the
right of `t₀`. -/
theorem timeDeriv_xHolderOn_of_stripBundle {α : NNReal} (hα : 0 < (α : ℝ)) (hα1 : (α : ℝ) < 1)
    {ω : Work.LWP.R3 → ℝ → Work.LWP.R3} {R S : ℝ} (hS : 0 < S)
    (hbun : BSAdmissibleStripFull α ω R S) :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ a b : Work.LWP.R3, ∀ t ∈ Set.Icc (0:ℝ) S,
      ‖FiniteTimeSingularity.timeDeriv ω a t - FiniteTimeSingularity.timeDeriv ω b t‖
        ≤ C * ‖a - b‖ ^ c := by
  obtain ⟨⟨_, _, ⟨_, _⟩, ⟨H, hH⟩, ⟨_, _⟩, _⟩,
    ⟨hdc, ⟨M₁, hM₁⟩, _⟩, ⟨N₁, hN₁⟩⟩ := hbun
  -- `A = α` as a real, `k = α/(1+α)`, and the Hölder exponent `c = α²/(1+α) = A * k`.
  set A : ℝ := (α : ℝ) with hAdef
  have hApos : 0 < A := by rw [hAdef]; exact hα
  set H₀ : ℝ := (H : ℝ) with hH₀def
  have hH₀nn : 0 ≤ H₀ := by rw [hH₀def]; positivity
  -- the positive parts of the two real bounds
  set N₀ : ℝ := max N₁ 0 with hN₀def
  have hN₀nn : 0 ≤ N₀ := by rw [hN₀def]; exact le_max_right _ _
  set M₀ : ℝ := max M₁ 0 with hM₀def
  have hM₀nn : 0 ≤ M₀ := by rw [hM₀def]; exact le_max_right _ _
  set k : ℝ := A / (1 + A) with hkdef
  have hkpos : 0 < k := by rw [hkdef]; exact div_pos hApos (by linarith)
  have h1A : k * (1 + A) = A := by rw [hkdef]; field_simp
  have hS2 : 0 < S / 2 := by linarith
  have hSpow : 0 < (S / 2) ^ A := Real.rpow_pos_of_pos hS2 A
  set C₀ : ℝ := max (2 * (N₀ + H₀)) (2 * M₀ / (S / 2) ^ A) with hC₀def
  have hC₀nn : 0 ≤ C₀ := by
    rw [hC₀def]; exact le_trans (by linarith) (le_max_left _ _)
  refine ⟨A * k, mul_pos hApos hkpos, C₀, hC₀nn, ?_⟩
  intro a b t ht
  by_cases hab : a = b
  · subst hab
    have hcne : A * k ≠ 0 := (mul_pos hApos hkpos).ne'
    simp [Real.zero_rpow hcne]
  · -- the generic case: `a ≠ b`
    set ψ : ℝ → Work.LWP.R3 := fun s => ω a s - ω b s with hψdef
    set ψ' : ℝ → Work.LWP.R3 := fun s =>
      FiniteTimeSingularity.timeDeriv ω a s - FiniteTimeSingularity.timeDeriv ω b s with hψ'def
    have hne : a - b ≠ 0 := sub_ne_zero.mpr hab
    have hnormpos : 0 < ‖a - b‖ := norm_pos_iff.mpr hne
    -- the step size `hh = ‖a-b‖^k`
    set hh : ℝ := ‖a - b‖ ^ k with hhdef
    have hhpos : 0 < hh := by rw [hhdef]; exact Real.rpow_pos_of_pos hnormpos k
    have hhA : hh ^ A = ‖a - b‖ ^ (A * k) := by
      rw [hhdef, ← Real.rpow_mul hnormpos.le k A, mul_comm k A]
    have hh1A : hh ^ (1 + A) = ‖a - b‖ ^ A := by
      rw [hhdef, ← Real.rpow_mul hnormpos.le k (1 + A), h1A]
    -- the `x`-Hölder bound on the slices of `ψ`
    have hψ_bound : ∀ s ∈ Set.Icc (0:ℝ) S, ‖ψ s‖ ≤ H₀ * ‖a - b‖ ^ A := by
      intro s hs
      rw [hψdef]
      have h2 := (hH s hs).dist_le a b
      rw [dist_eq_norm, dist_eq_norm] at h2
      calc ‖ω a s - ω b s‖ ≤ (H:ℝ) * ‖a - b‖ ^ (α:ℝ) := h2
        _ = H₀ * ‖a - b‖ ^ A := by rw [hH₀def, hAdef]
    -- `ψ` is differentiable in `t` on the strip, with derivative `ψ'`
    have hψderiv : ∀ x ∈ Set.Icc (0:ℝ) S, HasDerivAt ψ (ψ' x) x := by
      intro x hx
      exact (hdc x hx a).sub (hdc x hx b)
    -- the `α`-Hölder bound on `∂ₜω` with the nonnegative constant `N₀`
    have key₁ : ∀ y : Work.LWP.R3, ∀ s ∈ Set.Icc (0:ℝ) S, ∀ s' ∈ Set.Icc (0:ℝ) S,
        ‖FiniteTimeSingularity.timeDeriv ω y s - FiniteTimeSingularity.timeDeriv ω y s'‖
          ≤ N₀ * |s - s'| ^ A := by
      intro y s hs s' hs'
      have h1 := hN₁ y s hs s' hs'
      rcases le_total 0 N₁ with h | h
      · rw [hN₀def, max_eq_left h, hAdef]
        exact h1
      · rw [hN₀def, max_eq_right h, hAdef, zero_mul]
        have hr : 0 ≤ |s - s'| ^ A := Real.rpow_nonneg (abs_nonneg _) _
        have h2 : N₁ * |s - s'| ^ A ≤ 0 := by nlinarith
        exact le_trans h1 h2
    have key₂ : ∀ s ∈ Set.Icc (0:ℝ) S, ∀ s' ∈ Set.Icc (0:ℝ) S,
        ‖ψ' s - ψ' s'‖ ≤ 2 * N₀ * |s - s'| ^ A := by
      intro s hs s' hs'
      have h1 := key₁ a s hs s' hs'
      have h2 := key₁ b s hs s' hs'
      rw [hψ'def]
      calc ‖(FiniteTimeSingularity.timeDeriv ω a s - FiniteTimeSingularity.timeDeriv ω b s)
              - (FiniteTimeSingularity.timeDeriv ω a s' - FiniteTimeSingularity.timeDeriv ω b s')‖
          ≤ ‖FiniteTimeSingularity.timeDeriv ω a s - FiniteTimeSingularity.timeDeriv ω a s'‖
            + ‖FiniteTimeSingularity.timeDeriv ω b s - FiniteTimeSingularity.timeDeriv ω b s'‖ := by
            rw [sub_sub_sub_comm]
            exact norm_sub_le _ _
        _ ≤ N₀ * |s - s'| ^ A + N₀ * |s - s'| ^ A := add_le_add h1 h2
        _ = 2 * N₀ * |s - s'| ^ A := by ring
    -- the mean value step on a small interval around `t` of length `hh`
    have core : ∀ u ∈ Set.Icc (0:ℝ) S, |u - t| = hh →
        (∀ x ∈ Set.uIcc t u, |x - t| ≤ hh) →
        hh * ‖ψ' t‖ ≤ 2 * (N₀ + H₀) * hh ^ (1 + A) := by
      intro u hu hueq hwin
      set f : ℝ → Work.LWP.R3 := fun s => ψ s - (s - t) • ψ' t with hfdef
      have hseg : Set.uIcc t u ⊆ Set.Icc (0:ℝ) S := by
        intro x hx
        exact ⟨le_trans (le_min ht.1 hu.1) hx.1, le_trans hx.2 (max_le ht.2 hu.2)⟩
      have hfd : ∀ x ∈ Set.uIcc t u, HasDerivAt f (ψ' x - ψ' t) x := by
        intro x hx
        have hxS := hseg hx
        have h2 : HasDerivAt (fun s : ℝ => (s - t) • ψ' t) (ψ' t) x := by
          have hh2 := ((hasDerivAt_id x).sub_const t).smul_const (ψ' t)
          rw [one_smul] at hh2
          exact hh2
        exact (hψderiv x hxS).sub h2
      have hdiff : ∀ x ∈ Set.uIcc t u, DifferentiableAt ℝ f x :=
        fun x hx => (hfd x hx).differentiableAt
      have hbound : ∀ x ∈ Set.uIcc t u, ‖deriv f x‖ ≤ 2 * N₀ * hh ^ A := by
        intro x hx
        rw [(hfd x hx).deriv]
        have hxS := hseg hx
        have hk := key₂ x hxS t ht
        have hr : |x - t| ^ A ≤ hh ^ A :=
          Real.rpow_le_rpow (abs_nonneg _) (hwin x hx) hApos.le
        calc ‖ψ' x - ψ' t‖ ≤ 2 * N₀ * |x - t| ^ A := hk
          _ ≤ 2 * N₀ * hh ^ A := mul_le_mul_of_nonneg_left hr (by linarith)
      have hmvt : ‖f u - f t‖ ≤ 2 * N₀ * hh ^ A * ‖u - t‖ :=
        Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound (convex_uIcc t u)
          Set.left_mem_uIcc Set.right_mem_uIcc
      have hmvt' : ‖f u - f t‖ ≤ 2 * N₀ * (hh ^ A * hh) := by
        have hnorm : ‖u - t‖ = hh := by rw [Real.norm_eq_abs, hueq]
        calc ‖f u - f t‖ ≤ 2 * N₀ * hh ^ A * ‖u - t‖ := hmvt
          _ = 2 * N₀ * (hh ^ A * hh) := by rw [hnorm, mul_assoc]
      have hkey : (u - t) • ψ' t = (ψ u - ψ t) - (f u - f t) := by
        simp only [hfdef]
        rw [sub_self, zero_smul, sub_zero]
        abel
      have htri : ‖(u - t) • ψ' t‖ ≤ ‖ψ u - ψ t‖ + ‖f u - f t‖ := by
        rw [hkey]; exact norm_sub_le _ _
      have hLHS : ‖(u - t) • ψ' t‖ = hh * ‖ψ' t‖ := by
        rw [norm_smul, Real.norm_eq_abs, hueq]
      have h1 : ‖ψ u - ψ t‖ ≤ 2 * H₀ * ‖a - b‖ ^ A := by
        have hψu := hψ_bound u hu
        have hψt := hψ_bound t ht
        calc ‖ψ u - ψ t‖ ≤ ‖ψ u‖ + ‖ψ t‖ := norm_sub_le _ _
          _ ≤ H₀ * ‖a - b‖ ^ A + H₀ * ‖a - b‖ ^ A := add_le_add hψu hψt
          _ = 2 * H₀ * ‖a - b‖ ^ A := by ring
      calc hh * ‖ψ' t‖ = ‖(u - t) • ψ' t‖ := hLHS.symm
        _ ≤ ‖ψ u - ψ t‖ + ‖f u - f t‖ := htri
        _ ≤ 2 * H₀ * ‖a - b‖ ^ A + 2 * N₀ * (hh ^ A * hh) := add_le_add h1 hmvt'
        _ = 2 * (N₀ + H₀) * hh ^ (1 + A) := by
            have h3 : hh ^ A * hh = hh ^ (1 + A) := by
              rw [Real.rpow_add hhpos 1 A, Real.rpow_one]; ring
            rw [hh1A.symm, h3]; ring
    by_cases hle : hh ≤ S / 2
    · -- a full interval of length `hh` fits inside the strip around `t`
      have hmain : hh * ‖ψ' t‖ ≤ 2 * (N₀ + H₀) * hh ^ (1 + A) := by
        rcases le_total hh t with hhle | hhle
        · -- the interval `[t-hh, t]`
          have hu : t - hh ∈ Set.Icc (0:ℝ) S := ⟨by linarith, by linarith [ht.2]⟩
          have hueq : |(t - hh) - t| = hh := by
            have h4 : (t - hh) - t = -hh := by ring
            rw [h4, abs_neg, abs_of_pos hhpos]
          have hwin : ∀ x ∈ Set.uIcc t (t - hh), |x - t| ≤ hh := by
            intro x hx
            rw [Set.uIcc_of_ge (by linarith : t - hh ≤ t)] at hx
            rw [abs_le]
            exact ⟨by linarith [hx.1], by linarith [hx.2, hhpos.le]⟩
          exact core (t - hh) hu hueq hwin
        · -- the interval `[t, t+hh]`
          have hu : t + hh ∈ Set.Icc (0:ℝ) S :=
            ⟨by linarith [ht.1], by linarith [hhle, hle]⟩
          have hueq : |(t + hh) - t| = hh := by
            have h4 : (t + hh) - t = hh := by ring
            rw [h4, abs_of_pos hhpos]
          have hwin : ∀ x ∈ Set.uIcc t (t + hh), |x - t| ≤ hh := by
            intro x hx
            rw [Set.uIcc_of_le (by linarith : t ≤ t + hh)] at hx
            rw [abs_le]
            exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
          exact core (t + hh) hu hueq hwin
      have hfinal : ‖ψ' t‖ ≤ 2 * (N₀ + H₀) * ‖a - b‖ ^ (A * k) := by
        have h4 : 2 * (N₀ + H₀) * hh ^ (1 + A) = hh * (2 * (N₀ + H₀) * hh ^ A) := by
          rw [Real.rpow_add hhpos 1 A, Real.rpow_one]; ring
        have h5 := h4 ▸ hmain
        have h6 : ‖ψ' t‖ ≤ 2 * (N₀ + H₀) * hh ^ A := le_of_mul_le_mul_left h5 hhpos
        rwa [hhA] at h6
      calc ‖ψ' t‖ ≤ 2 * (N₀ + H₀) * ‖a - b‖ ^ (A * k) := hfinal
        _ ≤ C₀ * ‖a - b‖ ^ (A * k) :=
            mul_le_mul_of_nonneg_right (by rw [hC₀def]; exact le_max_left _ _)
              (Real.rpow_nonneg (norm_nonneg _) _)
    · -- the step size is large: crudely bound `‖ψ' t‖` by `2 M₀`
      have hcrude : ‖ψ' t‖ ≤ 2 * M₀ := by
        have h1 : ‖FiniteTimeSingularity.timeDeriv ω a t‖ ≤ M₀ := by
          rw [hM₀def]; exact le_trans (hM₁ t ht a) (le_max_left _ _)
        have h2 : ‖FiniteTimeSingularity.timeDeriv ω b t‖ ≤ M₀ := by
          rw [hM₀def]; exact le_trans (hM₁ t ht b) (le_max_left _ _)
        calc ‖ψ' t‖ = ‖FiniteTimeSingularity.timeDeriv ω a t
            - FiniteTimeSingularity.timeDeriv ω b t‖ := rfl
          _ ≤ ‖FiniteTimeSingularity.timeDeriv ω a t‖
              + ‖FiniteTimeSingularity.timeDeriv ω b t‖ := norm_sub_le _ _
          _ ≤ M₀ + M₀ := add_le_add h1 h2
          _ = 2 * M₀ := by ring
      have hb : (S / 2) ^ A ≤ ‖a - b‖ ^ (A * k) := by
        have hlt : S / 2 < hh := lt_of_not_ge hle
        have hrp : (S / 2) ^ A < hh ^ A := Real.rpow_lt_rpow hS2.le hlt hApos
        calc (S / 2) ^ A ≤ hh ^ A := le_of_lt hrp
          _ = ‖a - b‖ ^ (A * k) := hhA
      calc ‖ψ' t‖ ≤ 2 * M₀ := hcrude
        _ = 2 * M₀ / (S / 2) ^ A * (S / 2) ^ A := (div_mul_cancel₀ (2 * M₀) hSpow.ne').symm
        _ ≤ C₀ * ‖a - b‖ ^ (A * k) := by
            rw [hC₀def]
            exact mul_le_mul (le_max_right _ _) hb hSpow.le hC₀nn

end Work.CoreResiduals.BiotSavart
end
-- ===== merged: Submission.Work.CoreResiduals.ProfileData_T_eq_two =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals


end Work.CoreResiduals
end
-- ===== merged: Submission.Work.CoreResiduals.VorticityEquation.vorticityEquation_cylField_iff_scalar =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Work.Cyl
open FiniteTimeSingularity

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Work.CoreResiduals.VorticityEquation

theorem deriv_smul_const_eucl {n : ℕ} (c : ℝ → ℝ) (f : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    deriv (fun s => c s • f) t = deriv c t • f := by
  by_cases hf : f = 0
  · subst hf; simp
  · by_cases hc : DifferentiableAt ℝ c t
    · exact deriv_smul_const hc f
    · have hnorm : ‖f‖ ^ 2 ≠ 0 := by
        have : (0:ℝ) < ‖f‖ := norm_pos_iff.mpr hf
        positivity
      have hg : ¬ DifferentiableAt ℝ (fun s => c s • f) t := by
        intro h
        apply hc
        let T : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := (‖f‖ ^ 2)⁻¹ • innerSL ℝ f
        have hcomp : DifferentiableAt ℝ (fun s => T (c s • f)) t :=
          (T.differentiableAt).comp t h
        have heq : (fun s => T (c s • f)) = c := by
          funext s
          simp only [T, smul_apply, smul_eq_mul, innerSL_apply_apply,
            real_inner_smul_right, real_inner_self_eq_norm_sq, mul_comm]
          field_simp
        rwa [heq] at hcomp
      rw [deriv_zero_of_not_differentiableAt hc, deriv_zero_of_not_differentiableAt hg,
        zero_smul]

lemma differentiableAt_angularVec (x : R3) : DifferentiableAt ℝ (fun y : R3 => angularVec y) x := by
  have h0 : DifferentiableAt ℝ (fun y : R3 => y 0) x :=
    (PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) x 0).differentiableAt
  have h1 : DifferentiableAt ℝ (fun y : R3 => y 1) x :=
    (PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) x 1).differentiableAt
  have hfun : (fun y : R3 => angularVec y) = fun y : R3 => (-y 1) • e0 + (y 0) • e1 := by
    funext y
    apply ext_coord <;> simp [angularVec, e0, e1, FiniteTimeSingularity.e]
  rw [hfun]
  exact ((h1.neg.smul_const e0).add (h0.smul_const e1))

lemma fderiv_eTheta_cylField_eq_zero (ur uz : ℝ → ℝ → ℝ) (x : R3) (hr : 0 < radial x) :
    fderiv ℝ (fun y : R3 => eTheta y) x (cylField ur uz x) = 0 := by
  rw [fderiv_eTheta x (cylField ur uz x) hr]
  set v : R3 := cylField ur uz x with hv
  have hrne : radial x ≠ 0 := ne_of_gt hr
  have hv0 : v 0 = ur (radial x) (axial x) * x 0 / radial x := by rw [hv]; exact cylField_zero ur uz x
  have hv1 : v 1 = ur (radial x) (axial x) * x 1 / radial x := by rw [hv]; exact cylField_one ur uz x
  have hsq : x 0 ^ 2 + x 1 ^ 2 = radial x ^ 2 := (radial_sq x).symm
  have hdot : x 0 * v 0 + x 1 * v 1 = ur (radial x) (axial x) * radial x := by
    rw [hv0, hv1]; field_simp; rw [hsq]
  have hang : angularVec v = (ur (radial x) (axial x) / radial x) • angularVec x := by
    apply ext_coord
    · simp only [angularVec_apply_zero, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, hv1]; ring
    · simp only [angularVec_apply_one, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, hv0]; ring
    · simp only [angularVec_apply_two, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, mul_zero]
  rw [hdot, hang, smul_smul, ← add_smul]
  have : -(ur (radial x) (axial x) * radial x) / radial x ^ 3
      + (radial x)⁻¹ * (ur (radial x) (axial x) / radial x) = 0 := by
    field_simp; ring
  rw [this, zero_smul]

lemma fderiv_cylField_eTheta (ur uz : ℝ → ℝ → ℝ) (x : R3)
    (hur : DiffAt2 ur (radial x) (axial x)) (huz : DiffAt2 uz (radial x) (axial x))
    (hr : 0 < radial x) :
    fderiv ℝ (cylField ur uz) x (eTheta x) = redR ur (radial x) (axial x) • eTheta x := by
  have h3 := fderiv_cylField_angularVec ur uz x hur huz hr
  have he : eTheta x = (radial x)⁻¹ • angularVec x := by simp only [eTheta, one_div]
  rw [he, map_smul, h3]
  simp only [smul_smul]
  congr 1
  ring

lemma timeDeriv_swirl {W : ℝ → ℝ → ℝ → ℝ} (x : R3) (t : ℝ) :
    timeDeriv (fun x t => W (radial x) (axial x) t • eTheta x) x t
      = deriv (fun s : ℝ => W (radial x) (axial x) s) t • eTheta x := by
  simp only [timeDeriv]
  exact deriv_smul_const_eucl (fun s => W (radial x) (axial x) s) (eTheta x) t



/-! ## axis helper -/


/-! ## the corner facts at (r,0,z) -/




/-! ## the main theorem -/



end Work.CoreResiduals.VorticityEquation
end
-- ===== merged: Submission.Work.CoreResiduals.norm_timeDeriv_sub_le_of_secondDeriv_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals

/-- Pointwise-in-`y` mean value bound: if the second time derivative of a spacetime field `ω`
is bounded by `C` on the interval `Icc a b` (and exists there), then the first time derivative
is `C`-Lipschitz in time on `Ioo a b`.  This is the mean value theorem on the convex set
`Icc a b`. -/
theorem norm_timeDeriv_sub_le_of_secondDeriv_bound
    {ω : EuclideanSpace ℝ (Fin 3) → ℝ → EuclideanSpace ℝ (Fin 3)} {a b C : ℝ}
    (hdiff : ∀ y : EuclideanSpace ℝ (Fin 3), ∀ z ∈ Set.Icc a b,
      HasDerivAt (fun s => FiniteTimeSingularity.timeDeriv ω y s)
        (FiniteTimeSingularity.timeDeriv (FiniteTimeSingularity.timeDeriv ω) y z) z)
    (hbd : ∀ y : EuclideanSpace ℝ (Fin 3), ∀ z ∈ Set.Icc a b,
      ‖FiniteTimeSingularity.timeDeriv (FiniteTimeSingularity.timeDeriv ω) y z‖ ≤ C) :
    ∀ t ∈ Set.Ioo a b, ∀ t' ∈ Set.Ioo a b, ∀ y : EuclideanSpace ℝ (Fin 3),
      ‖FiniteTimeSingularity.timeDeriv ω y t - FiniteTimeSingularity.timeDeriv ω y t'‖
        ≤ C * |t - t'| := by
  intro t ht t' ht' y
  have htI : t ∈ Set.Icc a b := Set.Ioo_subset_Icc_self ht
  have ht'I : t' ∈ Set.Icc a b := Set.Ioo_subset_Icc_self ht'
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun s => FiniteTimeSingularity.timeDeriv ω y s)
      (f' := fun z => FiniteTimeSingularity.timeDeriv (FiniteTimeSingularity.timeDeriv ω) y z)
      (s := Set.Icc a b) (C := C)
      (fun z hz => (hdiff y z hz).hasDerivWithinAt)
      (fun z hz => hbd y z hz)
      (convex_Icc a b) ht'I htI
  simpa [Real.norm_eq_abs] using h

end Work.CoreResiduals
end
-- ===== merged: Submission.Work.CoreResiduals.solVort_holder_strip =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

namespace Work.CoreResiduals

/-! ## Uniform Hölder-constant calculus

The three lemmas below are the quantitative form of the chain
`Work.ConstructionInstance.solVort_holder` uses: they expose the *constant* produced at every step
so that it can be bounded uniformly over a time strip. -/

/-- **Monotonicity of `HolderWith` in its constant.** -/
theorem holderWith_le_const {X Y : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y]
    {C C' : NNReal} {r : NNReal} {f : X → Y} (h : HolderWith C r f) (hCC : C ≤ C') :
    HolderWith C' r f :=
  fun x y => le_trans (h x y) (mul_le_mul_left (ENNReal.coe_le_coe.mpr hCC) _)

/-- **Composition with a dilation of the domain.**  Precomposing an `r`-Hölder map with
`x ↦ b • x` (`b ≥ 0`) multiplies the Hölder constant by `b ^ r`. -/
theorem holderWith_comp_smul {α : NNReal} {Y : Type*} [PseudoMetricSpace Y]
    {f : EuclideanSpace ℝ (Fin 3) → Y} {C : NNReal} (hf : HolderWith C α f) {b : ℝ}
    (hb : 0 ≤ b) :
    HolderWith (C * Real.toNNReal (b ^ (α : ℝ))) α (fun x => f (b • x)) := by
  apply Work.Stability.holderWith_of_dist_le
  intro x y
  have h1 := hf.dist_le (b • x) (b • y)
  rw [dist_smul₀, Real.norm_of_nonneg hb, Real.mul_rpow hb dist_nonneg] at h1
  calc dist (f (b • x)) (f (b • y))
      ≤ (C : ℝ) * (b ^ (α : ℝ) * dist x y ^ (α : ℝ)) := h1
    _ = ((C * Real.toNNReal (b ^ (α : ℝ)) : NNReal) : ℝ) * dist x y ^ (α : ℝ) := by
        rw [NNReal.coe_mul, Real.coe_toNNReal (b ^ (α : ℝ)) (Real.rpow_nonneg hb _)]
        ring

/-- **Bounded Lipschitz scalar times bounded Hölder field**, with an *explicit* constant
`Mc·C + MA·max K (2Mc)`.  This is the quantitative companion of
`Work.Stability.holder_smul_of_bounded_lipschitz`, whose constant is existential and therefore
useless for a strip-uniform statement. -/
theorem holderWith_smul_of_bounded_lipschitz {X : Type*} [PseudoMetricSpace X] {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] {α : NNReal} (hα : α ≤ 1) {K : NNReal}
    {c : X → ℝ} {A : X → E} {Mc MA : ℝ} (hMc0 : 0 ≤ Mc) (hc : ∀ x, |c x| ≤ Mc)
    (hcl : LipschitzWith K c) (hMA0 : 0 ≤ MA) (hA : ∀ x, ‖A x‖ ≤ MA) {C : NNReal}
    (hAC : HolderWith C α A) :
    HolderWith ⟨Mc * (C : ℝ) + MA * max (K : ℝ) (2 * Mc),
      add_nonneg (mul_nonneg hMc0 C.coe_nonneg)
        (mul_nonneg hMA0 (le_trans (by linarith) (le_max_right _ _)))⟩ α (c • A) := by
  refine Work.Stability.holderWith_of_dist_le fun x y => ?_
  have hcx : |c x| ≤ Mc := hc x
  have hcy : |c y| ≤ Mc := hc y
  have hAy : ‖A y‖ ≤ MA := hA y
  have hdA : dist (A x) (A y) ≤ (C : ℝ) * dist x y ^ (α : ℝ) := hAC.dist_le x y
  have hdc1 : |c x - c y| ≤ (K : ℝ) * dist x y := by
    have h := hcl.dist_le_mul x y
    rwa [Real.dist_eq] at h
  have hdc2 : |c x - c y| ≤ 2 * Mc := by
    calc |c x - c y| = dist (c x) (c y) := by rw [Real.dist_eq]
      _ ≤ dist (c x) 0 + dist 0 (c y) := dist_triangle _ _ _
      _ = |c x| + |c y| := by rw [Real.dist_eq, Real.dist_eq, sub_zero, zero_sub, abs_neg]
      _ ≤ 2 * Mc := by linarith
  have hK0 : (0 : ℝ) ≤ (K : ℝ) := K.coe_nonneg
  have hmax0 : 0 ≤ max (K : ℝ) (2 * Mc) := le_trans (by linarith) (le_max_right _ _)
  have hdc : |c x - c y| ≤ max (K : ℝ) (2 * Mc) * dist x y ^ (α : ℝ) := by
    rcases lt_or_ge (dist x y) 1 with hd | hd
    · have hs : dist x y ≤ dist x y ^ (α : ℝ) :=
        Real.self_le_rpow_of_le_one dist_nonneg (le_of_lt hd) (by exact_mod_cast hα)
      calc |c x - c y| ≤ (K : ℝ) * dist x y := hdc1
        _ ≤ (K : ℝ) * dist x y ^ (α : ℝ) := mul_le_mul_of_nonneg_left hs hK0
        _ ≤ max (K : ℝ) (2 * Mc) * dist x y ^ (α : ℝ) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg dist_nonneg _)
    · have hs : (1 : ℝ) ≤ dist x y ^ (α : ℝ) := Real.one_le_rpow hd α.coe_nonneg
      calc |c x - c y| ≤ 2 * Mc := hdc2
        _ ≤ (2 * Mc) * dist x y ^ (α : ℝ) := le_mul_of_one_le_right (by linarith) hs
        _ ≤ max (K : ℝ) (2 * Mc) * dist x y ^ (α : ℝ) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg dist_nonneg _)
  have hdec : c x • A x - c y • A y = c x • (A x - A y) + (c x - c y) • A y := by
    rw [smul_sub, sub_smul]; abel
  calc dist (c x • A x) (c y • A y) = ‖c x • (A x - A y) + (c x - c y) • A y‖ := by
        rw [dist_eq_norm, hdec]
    _ ≤ ‖c x • (A x - A y)‖ + ‖(c x - c y) • A y‖ := norm_add_le _ _
    _ = |c x| * dist (A x) (A y) + |c x - c y| * ‖A y‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, dist_eq_norm]
    _ ≤ Mc * ((C : ℝ) * dist x y ^ (α : ℝ))
          + (max (K : ℝ) (2 * Mc) * dist x y ^ (α : ℝ)) * MA :=
        add_le_add (mul_le_mul hcx hdA dist_nonneg hMc0)
          (mul_le_mul hdc hAy (norm_nonneg _) (mul_nonneg hmax0 (Real.rpow_nonneg dist_nonneg _)))
    _ = (Mc * (C : ℝ) + MA * max (K : ℝ) (2 * Mc)) * dist x y ^ (α : ℝ) := by ring

/-! ## The strip statement -/

/-- **Uniform-in-`t` Hölder regularity of the constructed vorticity on a time strip.**
`Work.ConstructionInstance.solVort_holder` gives `Holder α (solVort P · t)` for each `t` with a
`t`-dependent constant; on the strip `[0,S]`, `S < T`, the modulation satisfies `λ̄ ≥ (T-S)/2 > 0`,
and the dilation identity `solVort P x t = b • omegaS p g (b • x)` with `b^p = λ̄(t)^{-1}` makes the
Hölder constant `b^{1+α}·(constant of omegaS)` — bounded on the strip. -/
theorem solVort_holder_strip {α : NNReal} (P : Work.ConstructionInstance.ProfileData α)
    {S : ℝ} (hS : 0 < S) (hST : S < P.T) :
    ∃ H : NNReal, ∀ t ∈ Set.Icc (0 : ℝ) S,
      HolderWith H α (fun x : Work.LWP.R3 => Work.ConstructionInstance.solVort P x t) := by
  have hp : 0 < Work.ConstructionInstance.profExp α :=
    Work.ConstructionInstance.profExp_pos P.hα
  have hp1 : Work.ConstructionInstance.profExp α ≤ 1 := by
    rw [Work.ConstructionInstance.profExp]; linarith [P.hα13]
  have hα1 : α ≤ 1 := by
    rw [← NNReal.coe_le_coe]; push_cast; linarith [P.hα13]
  -- a *fixed* Hölder constant for the self-similar datum
  obtain ⟨C₀, hC₀⟩ : Holder α
      (Work.ConstructionInstance.omegaS (Work.ConstructionInstance.profExp α) P.g) :=
    Work.ConstructionInstance.holder_omegaS_of_data P.hα P.hα13 P.hCv P.hLg P.hLθ
      P.hvt P.hquad0 P.hquad P.hvan P.hzk P.hzth
      (ContDiffOn.of_le P.hsmooth (by simp))
  -- the Lipschitz constant of the cut-off factor
  obtain ⟨Kφ, hKφ⟩ := Work.Stability.cutFactor_lipschitz P.hL
  -- the strip lower bound on the modulation, and the uniform dilation factor it gives
  let δ : ℝ := (P.T - S) / 2
  have hδdef : δ = (P.T - S) / 2 := rfl
  have hδ : 0 < δ := by rw [hδdef]; linarith
  let bmax : ℝ := (δ⁻¹) ^ (1 / Work.ConstructionInstance.profExp α)
  have hbmax0 : 0 ≤ bmax := Real.rpow_nonneg (inv_nonneg.mpr hδ.le) _
  let CAdil : NNReal := C₀ * Real.toNNReal (bmax ^ (α : ℝ))
  let MA : ℝ := 20 * Work.ConstructionInstance.profExp α + P.Cg
  have hMAdef : MA = 20 * Work.ConstructionInstance.profExp α + P.Cg := rfl
  have hMA0 : 0 ≤ MA := by rw [hMAdef]; linarith [hp.le, P.hCg]
  let Hcut : NNReal := ⟨1 * (CAdil : ℝ) + MA * max (Kφ : ℝ) (2 * 1),
    add_nonneg (by norm_num)
      (mul_nonneg hMA0 (le_trans (by linarith) (le_max_right _ _)))⟩
  let δinv : NNReal := ⟨δ⁻¹, inv_nonneg.mpr hδ.le⟩
  refine ⟨Hcut * δinv, fun t ht => ?_⟩
  have htIco : t ∈ Set.Ico 0 P.T := ⟨ht.1, lt_of_le_of_lt ht.2 hST⟩
  have hδle : δ ≤ P.lam t := by
    have h1 : δ ≤ (P.T - t) / 2 := by rw [hδdef]; linarith [ht.2]
    exact le_trans h1 (P.hlam_low t htIco)
  have hlt : 0 < P.lam t := lt_of_lt_of_le hδ hδle
  -- the dilation factor `b = λ̄(t)^{-1/p}`, uniformly bounded by `bmax`
  let b : ℝ := (P.lam t)⁻¹ ^ (1 / Work.ConstructionInstance.profExp α)
  have hb : 0 < b := Real.rpow_pos_of_pos (inv_pos.mpr hlt) _
  have hb_eq : b = (P.lam t)⁻¹ ^ (1 / Work.ConstructionInstance.profExp α) := rfl
  have hbmax_eq : bmax = (δ⁻¹) ^ (1 / Work.ConstructionInstance.profExp α) := rfl
  have hbp : b ^ Work.ConstructionInstance.profExp α = (P.lam t)⁻¹ := by
    rw [hb_eq, ← Real.rpow_mul (inv_nonneg.mpr hlt.le)
        (1 / Work.ConstructionInstance.profExp α) (Work.ConstructionInstance.profExp α),
      div_mul_cancel₀ 1 (ne_of_gt hp), Real.rpow_one]
  have hb_le_bmax : b ≤ bmax := by
    rw [hb_eq, hbmax_eq]
    exact Real.rpow_le_rpow (inv_nonneg.mpr hlt.le)
      ((inv_le_inv₀ hlt hδ).mpr hδle) (by positivity)
  have hbα : b ^ (α : ℝ) ≤ bmax ^ (α : ℝ) :=
    Real.rpow_le_rpow hb.le hb_le_bmax α.coe_nonneg
  -- the dilation identity for the cylindrical coordinates
  have hz : ∀ x : Work.LWP.R3,
      Work.Cyl.rho (b • x) ^ Work.ConstructionInstance.profExp α
        = Work.Cyl.rho x ^ Work.ConstructionInstance.profExp α / P.lam t := by
    intro x
    rw [Work.ConstructionInstance.solVort_holder_rho_smul hb.le,
      Real.mul_rpow hb.le (Work.Cyl.rho_nonneg x), hbp, div_eq_mul_inv, mul_comm ((P.lam t)⁻¹)]
  have hω : ∀ x : Work.LWP.R3,
      Work.ConstructionInstance.omegaS (Work.ConstructionInstance.profExp α) P.g (b • x)
        = Work.ConstructionInstance.omegaSz (Work.ConstructionInstance.profExp α) P.g
            (Work.Cyl.rho x ^ Work.ConstructionInstance.profExp α / P.lam t) x := by
    intro x
    rw [Work.ConstructionInstance.omegaS_apply', Work.ConstructionInstance.omegaSz_apply,
      Work.ConstructionInstance.solVort_holder_theta_smul hb x,
      Work.ConstructionInstance.solVort_holder_eTheta_smul hb x, hz x]
  have hid : ∀ x : Work.LWP.R3, Work.ConstructionInstance.solVort P x t
      = (P.lam t)⁻¹ • (Work.Stability.cutFactor P.L x •
          Work.ConstructionInstance.omegaS (Work.ConstructionInstance.profExp α) P.g (b • x)) := by
    intro x
    rw [Work.ConstructionInstance.solVort_apply, Work.Stability.cutFactor_apply, hω x]
  -- the dilated datum is `α`-Hölder with the uniform constant `CAdil`
  have hH : HolderWith CAdil α (fun x : Work.LWP.R3 =>
      Work.ConstructionInstance.omegaS (Work.ConstructionInstance.profExp α) P.g (b • x)) := by
    have h1 : HolderWith (C₀ * Real.toNNReal (b ^ (α : ℝ))) α
        (fun x : Work.LWP.R3 =>
          Work.ConstructionInstance.omegaS (Work.ConstructionInstance.profExp α) P.g (b • x)) :=
      holderWith_comp_smul hC₀ hb.le
    refine holderWith_le_const h1 ?_
    have hCAdil : CAdil = C₀ * Real.toNNReal (bmax ^ (α : ℝ)) := rfl
    rw [hCAdil]
    exact mul_le_mul_of_nonneg_left (Real.toNNReal_le_toNNReal hbα)
      (zero_le : (0 : NNReal) ≤ C₀)
  -- the dilated datum is uniformly bounded by `MA`
  have hbd : ∀ x : Work.LWP.R3,
      ‖Work.ConstructionInstance.omegaS (Work.ConstructionInstance.profExp α) P.g (b • x)‖ ≤ MA := by
    intro x
    have hMθ : ∀ θ ∈ Work.Spaces.Iθ, 20 * Work.ConstructionInstance.profExp α
        * Work.ConstructionInstance.Gamma (Work.ConstructionInstance.profExp α / 3) θ + P.Cg
          ≤ MA := by
      intro θ hθ
      have hG : Work.ConstructionInstance.Gamma (Work.ConstructionInstance.profExp α / 3) θ ≤ 1 :=
        Work.ConstructionInstance.Gamma_le_one (by positivity) hθ
      have hMA : MA = 20 * Work.ConstructionInstance.profExp α + P.Cg := rfl
      rw [hMA]; nlinarith [hG, hp.le, P.hCg]
    exact Work.ConstructionInstance.omegaS_norm_le hp hp1 (Work.ConstructionInstance.bdd_g P)
      P.hCg hMθ (b • x)
  -- multiplying by the bounded Lipschitz cut-off keeps the constant uniform
  have hcut : HolderWith Hcut α (fun x : Work.LWP.R3 =>
      Work.Stability.cutFactor P.L x •
        Work.ConstructionInstance.omegaS (Work.ConstructionInstance.profExp α) P.g (b • x)) := by
    refine holderWith_smul_of_bounded_lipschitz hα1 (K := Kφ) (Mc := 1) (MA := MA)
      (C := CAdil) (by norm_num) ?_ hKφ hMA0 hbd hH
    intro x
    rw [Work.Stability.cutFactor_apply, abs_of_nonneg (Work.Stability.chi_nonneg _)]
    exact Work.Stability.chi_le_one _
  have hslice : HolderWith (Hcut * ‖(P.lam t)⁻¹‖₊) α
      ((P.lam t)⁻¹ • (fun x : Work.LWP.R3 => Work.Stability.cutFactor P.L x •
        Work.ConstructionInstance.omegaS (Work.ConstructionInstance.profExp α) P.g (b • x))) :=
    HolderWith.smul (P.lam t)⁻¹ hcut
  have hslice' : HolderWith (Hcut * ‖(P.lam t)⁻¹‖₊) α
      (fun x : Work.LWP.R3 => Work.ConstructionInstance.solVort P x t) := by
    rw [funext hid]
    exact hslice
  -- the scalar `λ̄(t)^{-1}` is uniformly bounded by `δ^{-1}` on the strip
  refine holderWith_le_const hslice' ?_
  refine mul_le_mul_of_nonneg_left ?_ (zero_le : (0 : NNReal) ≤ Hcut)
  rw [Real.nnnorm_of_nonneg (inv_nonneg.mpr hlt.le)]
  exact (inv_le_inv₀ hlt hδ).mpr hδle

end Work.CoreResiduals
end
end
-- ===== merged: Submission.Work.CoreResiduals.solVort_localBdd_preWindow =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals

/-- **Local uniform boundedness of the constructed vorticity near every time of `preWindow T`.**

On `preWindow T` the boxed bound `λ̄(t)·‖ω(x,t)‖ ≤ M` holds (`solVort_bdd`), and `λ̄` is locally
bounded below by a positive constant (`exists_eps_min_lam`).  Combining the two gives, around any
`t₀ ∈ preWindow T`, a symmetric neighbourhood on which `‖ω(x,t)‖` is uniformly bounded by
`M / m`, `m > 0` the local lower bound of `λ̄`. -/
theorem solVort_localBdd_preWindow {α : NNReal} (P : Work.ConstructionInstance.ProfileData α) :
    ∀ t₀ ∈ Work.ConstructionInstance.preWindow P.T, ∃ ε : ℝ, 0 < ε ∧ ∃ M : ℝ,
      ∀ t ∈ Set.Ioo (t₀ - ε) (t₀ + ε), ∀ y : Work.CoreResiduals.R3,
        ‖Work.ConstructionInstance.solVort P y t‖ ≤ M := by
  intro t₀ ht₀
  obtain ⟨ε, hεpos, hsub, m, hmpos, hmle⟩ :=
    exists_eps_min_lam P.hlam P.hlamdif ht₀
  refine ⟨ε, hεpos, P.M / m, ?_⟩
  intro t ht y
  have htIcc : t ∈ Set.Icc (t₀ - ε) (t₀ + ε) := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
  have htpre : t ∈ Work.ConstructionInstance.preWindow P.T := hsub htIcc
  have hbdd := Work.ConstructionInstance.solVort_bdd P t htpre y
  have hmle' : m ≤ P.lam t := hmle t htIcc
  rw [le_div_iff₀ hmpos]
  calc ‖Work.ConstructionInstance.solVort P y t‖ * m
      ≤ ‖Work.ConstructionInstance.solVort P y t‖ * P.lam t :=
        mul_le_mul_of_nonneg_left hmle' (norm_nonneg _)
    _ = P.lam t * ‖Work.ConstructionInstance.solVort P y t‖ := mul_comm _ _
    _ ≤ P.M := hbdd

end Work.CoreResiduals
end
-- ===== merged: Submission.Work.CoreResiduals.solVort_timeDeriv_aesm_preWindow =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals

/-- **The time-derivative slice of the constructed vorticity is almost everywhere strongly
measurable on the half-window `preWindow T = Ioo (-2) T`.**

This is the local form of `Work.StabilityFar.Decay.aestronglyMeasurable_timeDeriv_slice`: at each
`t` of the *open* window `Ioo (-2) T` the two-sided window `(t-ε, t+ε)` can be chosen inside the
window, where

* every slice `solVort P · s` is integrable (`solVort_integrable`), hence almost everywhere
  strongly measurable, and
* `s ↦ solVort P y s` is differentiable with derivative `timeDeriv (solVort P) y s`
  (`hasDerivAt_selfSimVort_slice`). -/
theorem solVort_timeDeriv_aesm_preWindow {α : NNReal}
    (P : Work.ConstructionInstance.ProfileData α) :
    ∀ t ∈ Work.ConstructionInstance.preWindow P.T,
      MeasureTheory.AEStronglyMeasurable
        (fun y : Work.CoreResiduals.R3 => FiniteTimeSingularity.timeDeriv
          (Work.ConstructionInstance.solVort P) y t) MeasureTheory.volume := by
  intro t ht
  obtain ⟨ht1, ht2⟩ := ht
  have hpos1 : 0 < t + 2 := by linarith
  have hpos2 : 0 < P.T - t := by linarith
  set ε : ℝ := min (t + 2) (P.T - t) / 2 with hεdef
  have hεpos : 0 < ε := by
    rw [hεdef]
    exact half_pos (lt_min hpos1 hpos2)
  have hεle1 : ε ≤ (t + 2) / 2 := by
    rw [hεdef]
    exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hεle2 : ε ≤ (P.T - t) / 2 := by
    rw [hεdef]
    exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  -- the two-sided window lies inside the half-window `preWindow T`
  have hwin : ∀ s ∈ Set.Ioo (t - ε) (t + ε), s ∈ Work.ConstructionInstance.preWindow P.T := by
    intro s hs
    obtain ⟨hs1, hs2⟩ := hs
    refine ⟨by linarith, by linarith⟩
  refine Work.StabilityFar.Decay.aestronglyMeasurable_timeDeriv_slice hεpos ?_ ?_
  · intro s hs y
    have hd := Work.ConstructionInstance.hasDerivAt_selfSimVort_slice
      (p := Work.ConstructionInstance.profExp α) (g := P.g) (L := P.L) (lam := P.lam)
      (T := P.T) P.hgdiff P.hlam P.hlamdif (hwin s hs) y
    simpa only [Work.ConstructionInstance.solVort] using hd
  · intro s hs
    exact (Work.ConstructionInstance.solVort_integrable P s (hwin s hs)).aestronglyMeasurable

end Work.CoreResiduals
end
-- ===== merged: Submission.Work.CoreResiduals.timeDerivStripHolder_of_locallyLipschitz =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals

/-- **The compactness step of the local-to-strip reduction.**

Let a family of functions `f y : ℝ → E` (`y` ranging over an *arbitrary* type `X`, so that the
constants below are uniform in `y`) be *locally* Lipschitz in `t` at every point of `[a,b]`, with
one neighbourhood `(t₀ - ε, t₀ + ε)` and one constant `N` per point `t₀`, the same for all `y`.
Then there are a *single* `δ > 0` and a *single* `N` such that every pair `t, t' ∈ [a,b]` at
distance `< δ` satisfies the Lipschitz bound, uniformly in `y`.

This is the classical argument: the neighbourhoods `(t₀ - ε t₀, t₀ + ε t₀)` for `t₀ ∈ [a,b]` are
an open cover of the compact interval `[a,b]`, hence have a finite subcover
(`IsCompact.elim_finite_subcover`); the Lebesgue number of that *finite* cover
(`lebesgue_number_lemma_of_metric`) gives `δ > 0` such that every ball `ball t δ` with
`t ∈ [a,b]` lies inside one member of the cover; and the constants of the finitely many members
are bounded by `max 1 (N i₁)`, the maximum of the finitely many chosen `N i`
(`Finset.exists_max_image`).  The finiteness of the cover is what makes the constant uniform —
the `N` of a single point of the infinite cover would depend on the pair `(t, t')` and would not
telescope. -/
theorem exists_step_bound_of_locallyLipschitz {X E : Type*} [NormedAddCommGroup E]
    {f : X → ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hloc : ∀ t ∈ Set.Icc a b, ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℝ,
      ∀ t' ∈ Set.Ioo (t - ε) (t + ε), ∀ t'' ∈ Set.Ioo (t - ε) (t + ε), ∀ y : X,
        ‖f y t' - f y t''‖ ≤ N * |t' - t''|) :
    ∃ (δ : ℝ) (N : ℝ), 0 < δ ∧ ∀ t ∈ Set.Icc a b, ∀ t' ∈ Set.Icc a b, |t - t'| < δ →
      ∀ y : X, ‖f y t - f y t'‖ ≤ N * |t - t'| := by
  classical
  -- the local data, chosen at every point of the compact interval
  have hloc' : ∀ t : Set.Icc a b, ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℝ,
      ∀ t' ∈ Set.Ioo (t.1 - ε) (t.1 + ε), ∀ t'' ∈ Set.Ioo (t.1 - ε) (t.1 + ε), ∀ y : X,
        ‖f y t' - f y t''‖ ≤ N * |t' - t''| := fun t => hloc t t.2
  choose ε hε N hN using hloc'
  -- these neighbourhoods cover `[a,b]`
  have hcover : Set.Icc a b ⊆ ⋃ i : Set.Icc a b, Set.Ioo (i.1 - ε i) (i.1 + ε i) := by
    intro t ht
    exact Set.mem_iUnion.mpr ⟨⟨t, ht⟩, ⟨by linarith [hε ⟨t, ht⟩], by linarith [hε ⟨t, ht⟩]⟩⟩
  -- compactness: a finite subcover
  obtain ⟨tfin, htfin⟩ := isCompact_Icc.elim_finite_subcover
    (fun i : Set.Icc a b => Set.Ioo (i.1 - ε i) (i.1 + ε i)) (fun _ => isOpen_Ioo) hcover
  set c : {i // i ∈ tfin} → Set ℝ := fun i => Set.Ioo (i.1.1 - ε i.1) (i.1.1 + ε i.1) with hc
  have hcopen : ∀ i, IsOpen (c i) := fun i => isOpen_Ioo
  have hccover : Set.Icc a b ⊆ ⋃ i, c i := by
    intro t ht
    obtain ⟨i, hit, hti⟩ := Set.mem_iUnion₂.1 (htfin ht)
    exact Set.mem_iUnion.2 ⟨⟨i, hit⟩, hti⟩
  -- the Lebesgue number of the finite cover
  obtain ⟨δ, hδpos, hδ⟩ := lebesgue_number_lemma_of_metric (s := Set.Icc a b) (c := c)
    isCompact_Icc hcopen hccover
  -- the index finset is nonempty because `[a,b]` is
  have hne : tfin.Nonempty := by
    obtain ⟨i, hi, _⟩ := Set.mem_iUnion₂.1 (htfin ⟨le_rfl, hab⟩)
    exact ⟨i, hi⟩
  -- the largest of the finitely many constants
  obtain ⟨i₁, hit₁, hi₁max⟩ := Finset.exists_max_image tfin N hne
  refine ⟨δ, max 1 (N i₁), hδpos, fun t ht t' ht' hd y => ?_⟩
  -- `ball t δ` lies in one member of the cover, and `t'` is in that ball
  obtain ⟨i, hi⟩ := hδ t ht
  have ht_mem : t ∈ c i := hi (by rw [Metric.mem_ball]; simp [hδpos])
  have ht'_mem : t' ∈ c i := by
    refine hi ?_
    rw [Metric.mem_ball, Real.dist_eq, abs_sub_comm]
    exact hd
  exact (hN i.1 t ht_mem t' ht'_mem y).trans
    (mul_le_mul_of_nonneg_right (le_trans (hi₁max i.1 i.2) (le_max_right _ _)) (abs_nonneg _))

/-- The local Lipschitzness in `t` of the slices of `∂ₜω` (on the half-window) gives the *strip*
form of the second-order time-regularity of the R2 bundle: on the compact strip `[0,S]`,
`S < T`, a finite subcover of `preWindow P.T` by the local neighbourhoods of
`Work.CoreResiduals.TimeDerivLocallyLipschitz` yields a single Lipschitz constant `N` valid for all
`t, t' ∈ Icc 0 S` and all `y`; and a Lipschitz function is `α`-Hölder of every exponent `α ≤ 1` on
a bounded interval (`h ≤ h^α` for `0 ≤ h ≤ 1`, and `h ≤ S ≤ S·h^α` for `1 ≤ h ≤ S`), so a suitable
constant witnesses `Work.CoreResiduals.TimeDerivStripHolder α (solVort P) S`.  The exponent bound
`α ≤ 1` is derived internally from `P.hα13`. -/
theorem timeDerivStripHolder_of_locallyLipschitz {α : NNReal}
    (P : Work.ConstructionInstance.ProfileData α)
    (hlip : Work.CoreResiduals.TimeDerivLocallyLipschitz
      (Work.ConstructionInstance.solVort P) P.T)
    {S : ℝ} (hS : 0 < S) (hST : S < P.T) :
    Work.CoreResiduals.TimeDerivStripHolder α (Work.ConstructionInstance.solVort P) S := by
  -- the exponent range `α ≤ 1` of the profile data
  have hα1 : α ≤ 1 := by
    rw [← NNReal.coe_le_coe]
    push_cast
    linarith [P.hα13]
  have h0S : (0 : ℝ) ≤ S := le_of_lt hS
  -- the half-window contains the strip, so the local data is available at every `t ∈ Icc 0 S`
  have hloc : ∀ t ∈ Set.Icc (0 : ℝ) S, ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℝ,
      ∀ t' ∈ Set.Ioo (t - ε) (t + ε), ∀ t'' ∈ Set.Ioo (t - ε) (t + ε), ∀ y : R3,
        ‖FiniteTimeSingularity.timeDeriv (Work.ConstructionInstance.solVort P) y t'
          - FiniteTimeSingularity.timeDeriv (Work.ConstructionInstance.solVort P) y t''‖
          ≤ N * |t' - t''| := by
    intro t ht
    exact hlip t ⟨by linarith [ht.1], by linarith [ht.2, hST]⟩
  -- a single step size `δ` and a single constant `K` for the strip
  obtain ⟨δ, K, hδpos, hstep⟩ := exists_step_bound_of_locallyLipschitz (a := 0) (b := S)
    (f := fun y t => FiniteTimeSingularity.timeDeriv (Work.ConstructionInstance.solVort P) y t)
    h0S hloc
  -- chaining the steps: global Lipschitzness on the strip
  have hglob : ∀ t ∈ Set.Icc (0 : ℝ) S, ∀ t' ∈ Set.Icc (0 : ℝ) S, ∀ y : R3,
      ‖FiniteTimeSingularity.timeDeriv (Work.ConstructionInstance.solVort P) y t
        - FiniteTimeSingularity.timeDeriv (Work.ConstructionInstance.solVort P) y t'‖
        ≤ K * |t - t'| :=
    norm_sub_le_of_step_bound hδpos hstep
  -- Lipschitzness gives `α`-Hölder regularity on the bounded interval
  obtain ⟨N₁, hN₁⟩ := exists_holder_bound_of_lipschitzOn (S := S) (K := max 1 K) (α := α)
    (f := fun y t => FiniteTimeSingularity.timeDeriv (Work.ConstructionInstance.solVort P) y t)
    h0S (le_trans zero_le_one (le_max_left (1 : ℝ) K)) hα1
    (fun t ht t' ht' y => (hglob t ht t' ht' y).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (abs_nonneg _)))
  exact ⟨N₁, fun y t ht t' ht' => hN₁ y t ht t' ht'⟩

end Work.CoreResiduals
end
-- ===== merged: Submission.Work.FTS.NonlinRows.NRow8 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.NonlinRows

open Work.FTS.Galerkin (Fn)

set_option linter.unusedVariables false


end Work.FTS.NonlinRows
end
-- ===== merged: Submission.Work.FTS.NonlinRows.NRow9 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.NonlinRows

open Work.FTS.Galerkin (Fn)

set_option linter.unusedVariables false


end Work.FTS.NonlinRows
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Open.Row16 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Open

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000


end Work.FTS.Nonlinear.Open
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Open.Row17 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Open

open Work.FTS.Galerkin (Fn)

set_option linter.unusedVariables false


end Work.FTS.Nonlinear.Open
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.Rl1.n2Bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.Rl1

set_option autoImplicit false
set_option linter.unusedVariables false

open Work.FTS.Galerkin (Fn)

/-! ## The density of `N₂` under the context of the `rl1` row

The `rl1` row of `AuxRows` estimates `|L₁₂(N)(0)| ≤ K(α² + √α X + α^{-3/2}X²)` by the sum of the
five density integrals `E_i = ∫_{s>0}‖L₁₂dens(N_i)(s)‖ ds`.  This file proves the `i = 2` term,

  `E₂ ≤ K(α² + √α X + α^{-3/2}X²)`,

under the frozen context `N4Norm Ci α₂`, `GalClass α g`, `StarPkg α Cs Φs`, `EllPkgG α Ce g Φg`,
`0 < α ≤ 1`, `α ≤ α₂`.

**Route.** `N₂ = -2𝒰(Φ̃)∂_θF` with `Φ̃ = Φ̃_* + Φ̃_g` and `F = F_* + g`, so
`N₂ = N₂^{gg} + N₂^{gs} + N₂^{sg} + N₂^{ss}` pointwise on the quadrant (`N2_split`).  The key
device is that the kernel `K(θ) = 3 sin θ cos²θ` satisfies `K = (3/2) cos θ·sin(2θ)`, hence

  `K(θ)·∂_θ f = (3/2)cos θ·D_θ f`   (`K_mul_pth`),

so every term is a product of the *bounded* angular factor `(3/2)cos θ ≤ 3/2` with two of the
quantities `𝒰(Φ̃_*), 𝒰(Φ̃_g)/sin 2θ, D_θF_*, D_θg` (the last two carrying one factor of
`sin 2θ` each).  Those four are controlled by

* `|𝒰(Φ̃_*)| ≤ C·max Cs 0·α` (`StarUBound`),
* `|𝒰(Φ̃_g)/sin 2θ| ≤ 10√(10/α)·max Ce 0·X` (`gPt`),
* `∫_θ |D_θF_*| ≤ C·α²·z/(1+z)²` (`DthFstarPoint`),
* `∫_θ (D_θg)² ≤ (1/w z)∫_θ HkIntegrand α 4 g z θ` (`SliceSlot`),

the last together with Cauchy–Schwarz in `θ` and in `s` (with `1/s = √(w s)/(1+s)` and
`∫_s 1/(1+s)² = 1`) and the identification `√(HkSq α 4 g) = Xn α g`. -/

/-! ## The elementary identity for the kernel -/


/-! ## The four-way split of `N₂` on the open quadrant -/


/-! ## Measurability of the angular slices -/


/-- `mixed 0 1 f = D_θ f`. -/
theorem mixed_zero_one (f : ℝ → ℝ → ℝ) : Work.Spaces.mixed 0 1 f = Work.Spaces.Dth f := by
  funext z θ
  simp only [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_succ,
    Work.Spaces.DthIter_zero]

/-- The open `θ`-interval is a.e. equal to `Iθ`. -/
theorem ae_restrict_Iθ_of_Ioo {p : ℝ → Prop}
    (h : ∀ θ, 0 < θ → θ < π / 2 → p θ) :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), p θ :=
  Work.Elliptic.ae_restrict_Iθ_of_Ioo h

/-! ## The pointwise slot inequality for `D_θ` -/



/-! ## The `θ`-slice of `D_θ g`: integrability and `L¹`-bounds -/





/-! ## The `L₁₂`-density as a divided angular integral -/


/-- `K(θ) ≥ 0` on `Iθ`. -/
theorem K_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Work.Spaces.K θ := by
  rw [Work.Spaces.K]
  have h1 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  positivity




/-- `cos θ ≥ 0` on `Iθ`. -/
theorem cos_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.cos θ :=
  Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩


/-- The generic term estimate: `K θ·2·|X|·|p| ≤ 3M|d|` whenever `|X| ≤ M` and
`K θ·|p| ≤ (3/2)|d|`. -/
theorem term_le {θ M X p d : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) (hM : 0 ≤ M) (hX : |X| ≤ M)
    (hKp : Work.Spaces.K θ * |p| ≤ (3 / 2) * |d|) :
    Work.Spaces.K θ * (2 * (|X| * |p|)) ≤ 3 * M * |d| := by
  calc Work.Spaces.K θ * (2 * (|X| * |p|)) = 2 * |X| * (Work.Spaces.K θ * |p|) := by ring
    _ ≤ 2 * M * ((3 / 2) * |d|) :=
        mul_le_mul (by linarith [hX]) hKp (mul_nonneg (K_nonneg hθ) (abs_nonneg p))
          (by linarith [hM])
    _ = 3 * M * |d| := by ring

/-! ## The pointwise domination of `K·N₂` on the open quadrant -/


/-! ## The bound on the density at fixed `s` -/



/-! ## The `s`-level integration -/

/-- `HkIntegrand` of `SmoothQuad` data is continuous on the open quadrant. -/
theorem continuousOn_HkIntegrand_Qd {f : ℝ → ℝ → ℝ} (hsq : Work.FTS.LocData.SmoothQuad f)
    (α : ℝ) (k : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k f p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
  Work.FTS.EllipticEst.SmoothOpen.continuousOn_HkIntegrand
    (hsq.mono (Set.prod_mono (Set.Ioi_subset_Ioi (by norm_num : (-1 : ℝ) ≤ 0)) subset_rfl)) α k





/-! ## Two elementary `α`-inequalities for the final arithmetic -/

/-- `α²·√(10/α) ≤ √10·√α` for `0 < α ≤ 1`. -/
theorem alpha_sq_mul_sqrt_div_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    α ^ 2 * Real.sqrt (10 / α) ≤ Real.sqrt 10 * Real.sqrt α := by
  rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 10) α]
  have hsp : Real.sqrt α * Real.sqrt α = α := by rw [← sq, Real.sq_sqrt hα.le]
  have hspos : 0 < Real.sqrt α := Real.sqrt_pos.mpr hα
  have hL : α ^ 2 * (Real.sqrt 10 / Real.sqrt α) = Real.sqrt 10 * α ^ 2 / Real.sqrt α := by
    field_simp
  rw [hL, div_le_iff₀ hspos, mul_assoc, hsp]
  exact mul_le_mul_of_nonneg_left (by nlinarith [hα1, hα.le]) (Real.sqrt_nonneg 10)

/-- `√(1/α) ≤ α^{-3/2}` for `0 < α ≤ 1`. -/
theorem sqrt_inv_le_rpow {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    Real.sqrt (1 / α) ≤ α ^ (-(3 / 2 : ℝ)) := by
  have hspos : 0 < Real.sqrt α := Real.sqrt_pos.mpr hα
  have h1 : α ^ (-(3 / 2 : ℝ)) = (α ^ (-(1 / 2 : ℝ))) * α ^ (-(1 : ℝ)) := by
    rw [← Real.rpow_add hα]; norm_num
  rw [h1, Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1) α, Real.sqrt_one, one_div,
    Real.rpow_neg hα.le, Real.rpow_neg hα.le, Real.rpow_one, Real.sqrt_eq_rpow]
  have hinv : 1 ≤ α⁻¹ := by rw [one_le_inv₀ hα]; exact hα1
  have hnn : 0 ≤ (α ^ (1 / 2 : ℝ))⁻¹ := inv_nonneg.mpr (Real.rpow_nonneg hα.le _)
  calc (α ^ (1 / 2 : ℝ))⁻¹ = (α ^ (1 / 2 : ℝ))⁻¹ * 1 := by ring
    _ ≤ (α ^ (1 / 2 : ℝ))⁻¹ * α⁻¹ := mul_le_mul_of_nonneg_left hinv hnn

/-- The final arithmetic: the four terms of the expanded bound are dominated by
`K·(α² + √α X + α^{-3/2}X²)`. -/
theorem final_arith {α c₁ c₂ cs ce X : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hc₁ : 0 < c₁)
    (hc₂ : 0 < c₂) (hcs : 0 ≤ cs) (hce : 0 ≤ ce) (hX : 0 ≤ X) :
    6 * ((Real.pi / 2) * c₂) * (c₁ * cs * α) * α ^ 2
        + 3 * Real.sqrt Real.pi * (c₁ * cs * α) * X
        + 6 * ((Real.pi / 2) * c₂) * (10 * Real.sqrt (10 / α) * ce * X) * α ^ 2
        + 3 * Real.sqrt Real.pi * (10 * Real.sqrt (10 / α) * ce * X) * X
      ≤ (6 * c₁ * cs * ((Real.pi / 2) * c₂) + 3 * Real.sqrt Real.pi * c₁ * cs
          + 60 * Real.sqrt 10 * ce * ((Real.pi / 2) * c₂)
          + 30 * Real.sqrt (10 * Real.pi) * ce + 1)
        * (α ^ 2 + Real.sqrt α * X + α ^ (-(3 / 2 : ℝ)) * X ^ 2) := by
  have hsqa : α ^ 2 ≤ α := by nlinarith
  have hsa : α ≤ Real.sqrt α := by
    rw [Real.le_sqrt hα.le hα.le]; exact hsqa
  have hkey1 : α ^ 2 * Real.sqrt (10 / α) ≤ Real.sqrt 10 * Real.sqrt α :=
    alpha_sq_mul_sqrt_div_le hα hα1
  have hkey2 : Real.sqrt (1 / α) ≤ α ^ (-(3 / 2 : ℝ)) := sqrt_inv_le_rpow hα hα1
  have hkey3 : Real.sqrt (10 / α) = Real.sqrt 10 * Real.sqrt (1 / α) := by
    rw [one_div, Real.sqrt_inv, Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 10)]
    ring
  have h10pi : Real.sqrt Real.pi * Real.sqrt 10 = Real.sqrt (10 * Real.pi) := by
    rw [← Real.sqrt_mul Real.pi_pos.le 10]
    congr 1
    ring
  have hP1 : 0 ≤ (Real.pi / 2) * c₂ := by positivity
  have hspa : 0 ≤ Real.sqrt α := Real.sqrt_nonneg α
  have hX2 : 0 ≤ X ^ 2 := sq_nonneg X
  have hrp : 0 ≤ α ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg hα.le _
  -- the four termwise bounds
  have h1 : 6 * ((Real.pi / 2) * c₂) * (c₁ * cs * α) * α ^ 2
      ≤ 6 * c₁ * cs * ((Real.pi / 2) * c₂) * α ^ 2 := by
    have hcoef : 0 ≤ 6 * ((Real.pi / 2) * c₂) * c₁ * cs := by positivity
    have hcube : α ^ 3 ≤ α ^ 2 := by nlinarith [hsqa, hα.le]
    calc 6 * ((Real.pi / 2) * c₂) * (c₁ * cs * α) * α ^ 2
        = (6 * ((Real.pi / 2) * c₂) * c₁ * cs) * α ^ 3 := by ring
      _ ≤ (6 * ((Real.pi / 2) * c₂) * c₁ * cs) * α ^ 2 := mul_le_mul_of_nonneg_left hcube hcoef
      _ = 6 * c₁ * cs * ((Real.pi / 2) * c₂) * α ^ 2 := by ring
  have h2 : 3 * Real.sqrt Real.pi * (c₁ * cs * α) * X
      ≤ 3 * Real.sqrt Real.pi * c₁ * cs * Real.sqrt α * X := by
    have hcoef : 0 ≤ 3 * Real.sqrt Real.pi * c₁ * cs * X := by positivity
    calc 3 * Real.sqrt Real.pi * (c₁ * cs * α) * X
        = (3 * Real.sqrt Real.pi * c₁ * cs * X) * α := by ring
      _ ≤ (3 * Real.sqrt Real.pi * c₁ * cs * X) * Real.sqrt α :=
          mul_le_mul_of_nonneg_left hsa hcoef
      _ = 3 * Real.sqrt Real.pi * c₁ * cs * Real.sqrt α * X := by ring
  have h3 : 6 * ((Real.pi / 2) * c₂) * (10 * Real.sqrt (10 / α) * ce * X) * α ^ 2
      ≤ 60 * Real.sqrt 10 * ce * ((Real.pi / 2) * c₂) * (Real.sqrt α * X) := by
    have hcoef : 0 ≤ 60 * ((Real.pi / 2) * c₂) * ce * X := by positivity
    calc 6 * ((Real.pi / 2) * c₂) * (10 * Real.sqrt (10 / α) * ce * X) * α ^ 2
        = (60 * ((Real.pi / 2) * c₂) * ce * X) * (α ^ 2 * Real.sqrt (10 / α)) := by ring
      _ ≤ (60 * ((Real.pi / 2) * c₂) * ce * X) * (Real.sqrt 10 * Real.sqrt α) :=
          mul_le_mul_of_nonneg_left hkey1 hcoef
      _ = 60 * Real.sqrt 10 * ce * ((Real.pi / 2) * c₂) * (Real.sqrt α * X) := by ring
  have h4 : 3 * Real.sqrt Real.pi * (10 * Real.sqrt (10 / α) * ce * X) * X
      ≤ 30 * Real.sqrt (10 * Real.pi) * ce * (α ^ (-(3 / 2 : ℝ)) * X ^ 2) := by
    have hcoef : 0 ≤ 30 * ce * X ^ 2 * Real.sqrt Real.pi := by positivity
    calc 3 * Real.sqrt Real.pi * (10 * Real.sqrt (10 / α) * ce * X) * X
        = (30 * ce * X ^ 2 * Real.sqrt Real.pi) * Real.sqrt (10 / α) := by ring
      _ = (30 * ce * X ^ 2 * Real.sqrt Real.pi) * (Real.sqrt 10 * Real.sqrt (1 / α)) := by
          rw [hkey3]
      _ ≤ (30 * ce * X ^ 2 * Real.sqrt Real.pi) * (Real.sqrt 10 * α ^ (-(3 / 2 : ℝ))) := by
          refine mul_le_mul_of_nonneg_left ?_ hcoef
          exact mul_le_mul_of_nonneg_left hkey2 (Real.sqrt_nonneg 10)
      _ = (30 * (Real.sqrt Real.pi * Real.sqrt 10) * ce * X ^ 2) * α ^ (-(3 / 2 : ℝ)) := by
          ring
      _ = 30 * Real.sqrt (10 * Real.pi) * ce * (α ^ (-(3 / 2 : ℝ)) * X ^ 2) := by
          rw [h10pi]; ring
  have hsum : 6 * ((Real.pi / 2) * c₂) * (c₁ * cs * α) * α ^ 2
        + 3 * Real.sqrt Real.pi * (c₁ * cs * α) * X
        + 6 * ((Real.pi / 2) * c₂) * (10 * Real.sqrt (10 / α) * ce * X) * α ^ 2
        + 3 * Real.sqrt Real.pi * (10 * Real.sqrt (10 / α) * ce * X) * X
      ≤ (6 * c₁ * cs * ((Real.pi / 2) * c₂)) * α ^ 2
        + (3 * Real.sqrt Real.pi * c₁ * cs) * (Real.sqrt α * X)
        + (60 * Real.sqrt 10 * ce * ((Real.pi / 2) * c₂)) * (Real.sqrt α * X)
        + (30 * Real.sqrt (10 * Real.pi) * ce) * (α ^ (-(3 / 2 : ℝ)) * X ^ 2) := by
    linarith [h1, h2, h3, h4]
  have hnn : 0 ≤ α ^ 2 + Real.sqrt α * X + α ^ (-(3 / 2 : ℝ)) * X ^ 2 := by
    have h1' : 0 ≤ α ^ 2 := sq_nonneg α
    have h2' : 0 ≤ Real.sqrt α * X := mul_nonneg hspa hX
    have h3' : 0 ≤ α ^ (-(3 / 2 : ℝ)) * X ^ 2 := mul_nonneg hrp hX2
    linarith
  have hfinal : (6 * c₁ * cs * ((Real.pi / 2) * c₂)) * α ^ 2
        + (3 * Real.sqrt Real.pi * c₁ * cs) * (Real.sqrt α * X)
        + (60 * Real.sqrt 10 * ce * ((Real.pi / 2) * c₂)) * (Real.sqrt α * X)
        + (30 * Real.sqrt (10 * Real.pi) * ce) * (α ^ (-(3 / 2 : ℝ)) * X ^ 2)
      ≤ (6 * c₁ * cs * ((Real.pi / 2) * c₂) + 3 * Real.sqrt Real.pi * c₁ * cs
          + 60 * Real.sqrt 10 * ce * ((Real.pi / 2) * c₂)
          + 30 * Real.sqrt (10 * Real.pi) * ce + 1)
        * (α ^ 2 + Real.sqrt α * X + α ^ (-(3 / 2 : ℝ)) * X ^ 2) := by
    have hc1 : 0 ≤ 6 * c₁ * cs * ((Real.pi / 2) * c₂) := by positivity
    have hc2 : 0 ≤ 3 * Real.sqrt Real.pi * c₁ * cs := by positivity
    have hc3 : 0 ≤ 60 * Real.sqrt 10 * ce * ((Real.pi / 2) * c₂) := by positivity
    have hc4 : 0 ≤ 30 * Real.sqrt (10 * Real.pi) * ce := by positivity
    have f1 : 0 ≤ α ^ 2 := sq_nonneg α
    have f2 : 0 ≤ Real.sqrt α * X := mul_nonneg hspa hX
    have f3 : 0 ≤ α ^ (-(3 / 2 : ℝ)) * X ^ 2 := mul_nonneg hrp hX2
    nlinarith [hnn, mul_nonneg hc1 f2, mul_nonneg hc1 f3, mul_nonneg hc2 f1, mul_nonneg hc2 f3,
      mul_nonneg hc3 f1, mul_nonneg hc3 f2, mul_nonneg hc4 f1, mul_nonneg hc4 f2]
  linarith [hsum, hfinal]


end Work.FTS.Nonlinear.Pieces.Rl1
end
end
-- ===== merged: Submission.Work.FTS.OpenPkg.AprioriOpen.Bridge =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.OpenPkg.AprioriOpen

open Work.FTS.Apriori

open Work.FTS.Nonlin
open Work.FTS.Galerkin (Fn Fam slice galFun galFam galField galRHS coeffOf IsSolOn IsGalFam
  ConvLocUnif ConvPoint Slab muDyn lamDyn dynLin dynRHS prof)

set_option autoImplicit false
set_option maxHeartbeats 1000000




end Work.FTS.OpenPkg.AprioriOpen
end
end
-- ===== merged: Submission.Work.FTS.OpenPkg.NormFields =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.OpenPkg

open Work.FTS.Nonlin
open Work.FTS.VocabO
open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The assembly at a common constant -/

/-- **`N4Norm' Ci α₂` from its twelve fields**, each stated with the same constant `Ci`.  This is
the migrated `Work.FTS.Nonlinear.N4Norm` assembly: it is the interface contract, and the twelve
named hypotheses are the lemmas of the table in the module docstring. -/
theorem N4Norm'_of_fields {α₂ Ci : ℝ} (hα₂ : 0 < α₂) (hCi : 0 < Ci)
    (prod : ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Fn, HQo α 4 f → HQo α 4 g →
      Work.Spaces.HkMem α 4 (fun z θ => f z θ * g z θ) ∧
      Xn α (fun z θ => f z θ * g z θ)
        ≤ Ci * α ^ (-(1 / 2 : ℝ)) * Xn α f * Xn α g)
    (wprod : ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Fn, Work.FTS.EllipticEst.SmoothOpen f →
      Work.Spaces.WlInfMem α 4 f → HQo α 4 g →
      Work.Spaces.HkMem α 4 (fun z θ => f z θ * g z θ) ∧
      Xn α (fun z θ => f z θ * g z θ)
        ≤ Ci * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 4 f * Xn α g)
    (wtoh : ∀ α ∈ Set.Ioc 0 α₂, ∀ f : Fn, Work.FTS.EllipticEst.SmoothOpen f →
      Work.Spaces.WlInfMem α 4 (fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ) →
      Xn α f ≤ Ci * Work.Spaces.WlInf α 4 (fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ))
    (l12H : ∀ α ∈ Set.Ioc 0 α₂, ∀ g : Fn, HQo α 4 g → Work.Construction.L12 g 0 = 0 →
      Work.Spaces.HkMem α 4 (fun z θ => Work.Construction.L12 g z) ∧
      Xn α (fun z θ => Work.Construction.L12 g z) ≤ Ci * Xn α g)
    (l12zero : ∀ α ∈ Set.Ioc 0 α₂, ∀ f : Fn, HQo α 4 f →
      |Work.Construction.L12 f 0| ≤ Ci * Xn α f)
    (fkH : ∀ α ∈ Set.Ioc 0 α₂, ∀ g : Fn, HQo α 4 g → Work.Construction.L12 g 0 = 0 →
      Work.Spaces.HkMem α 4 (fun z _ => Work.Construction.FK g z) ∧
      Xn α (fun z _ => Work.Construction.FK g z) ≤ Ci * Xn α g)
    (l12diff : ∀ α ∈ Set.Ioc 0 α₂, ∀ g : Fn, HQo α 4 g → ∀ z ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (fun z' => Work.Construction.L12 g z') z)
    (radialMul : ∀ α ∈ Set.Ioc 0 α₂, ∀ (r : ℝ → ℝ) (g : Fn),
      Work.FTS.EllipticEst.SmoothOpen (fun z _ => r z) → Work.FTS.EllipticEst.SmoothOpen g →
      Work.Spaces.HkMem α 4 (fun z _ => r z) → Work.Spaces.HkMem α 4 g →
      (∀ b : ℕ, b ≤ 4 → Filter.Tendsto
        (fun z : ℝ => Work.Spaces.DzIter b (fun z _ => r z) z 0) Filter.atTop (nhds 0)) →
      (∀ b : ℕ, b ≤ 4 → ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        Filter.Tendsto (fun z : ℝ => Work.Spaces.DzIter b g z θ) Filter.atTop (nhds 0)) →
      Work.Spaces.HkMem α 4 (fun z θ => r z * g z θ) ∧
      Xn α (fun z θ => r z * g z θ) ≤ Ci * Xn α (fun z _ => r z) * Xn α g)
    (angmul : ∀ α ∈ Set.Ioc 0 α₂, ∀ (a : ℝ → ℝ) (f : Fn),
      Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => a θ) →
      (∀ θ ∈ Work.Spaces.Iθ, |a θ| ≤ Ci) →
      (∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
        |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 θ| ≤ Ci * Real.sin (2 * θ)) →
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
      Work.Spaces.HkMem α 4 (fun z θ => a θ * f z θ) ∧
      Xn α (fun z θ => a θ * f z θ) ≤ Ci * Ci * Xn α f)
    (wang : ∀ α ∈ Set.Ioc 0 α₂, ∀ (a : ℝ → ℝ) (h : Fn),
      Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => a θ) →
      Work.FTS.EllipticEst.SmoothOpen h →
      (∀ θ ∈ Work.Spaces.Iθ, |a θ| ≤ Ci) →
      (∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
        |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 θ| ≤ Ci * Real.sin (2 * θ)) →
      WDMem 4 h →
      WDMem 4 (fun z θ => a θ * h z θ) ∧
      WDp 4 (fun z θ => a θ * h z θ) ≤ Ci * Ci * WDp 4 h)
    (wrad : ∀ α ∈ Set.Ioc 0 α₂, ∀ (φ : ℝ → ℝ) (h : Fn),
      Work.FTS.EllipticEst.SmoothOpen (fun z _ => φ z) →
      Work.FTS.EllipticEst.SmoothOpen h →
      WDMem 4 (fun z _ => φ z) → WDMem 4 h →
      WDMem 4 (fun z θ => φ z * h z θ) ∧
      WDp 4 (fun z θ => φ z * h z θ) ≤ Ci * WDp 4 (fun z _ => φ z) * WDp 4 h)
    (wmul : ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Fn,
      Work.FTS.EllipticEst.SmoothOpen f → Work.FTS.EllipticEst.SmoothOpen g →
      WDMem 4 f → WDMem 4 g →
      (∀ k : ℕ, k ≤ 4 → ∀ z : ℝ,
        Work.Spaces.pzIter k g z 0 = 0 ∧ Work.Spaces.pzIter k g z (π / 2) = 0) →
      WDMem 4 (fun z θ => f z θ * g z θ) ∧
      WDp 4 (fun z θ => f z θ * g z θ) ≤ Ci * WDp 4 f * WDp 4 g) :
    N4Norm' Ci α₂ where
  pos := ⟨hCi, hα₂⟩
  prod := prod
  wprod := wprod
  wtoh := wtoh
  l12H := l12H
  l12zero := l12zero
  fkH := fkH
  l12diff := l12diff
  radialMul := radialMul
  angmul := angmul
  wang := wang
  wrad := wrad
  wmul := wmul

end Work.FTS.OpenPkg
end
end
-- ===== merged: Submission.Work.FTS.Regularity.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

set_option autoImplicit false

namespace Work.FTS.Regularity

/-- `ℝ³`, definitionally `Work.Cyl.R3`, `Work.LWP.R3`, `Work.CoreResiduals.R3` and
`Work.FTS.Physical.R3`. -/
abbrev R3 : Type := EuclideanSpace ℝ (Fin 3)

/-! ## The profile exponent and the angular factor -/

/-- The **profile exponent** `p = 3α` of the route (the paper's `α_paper`), so that the paper's
`Γ = (sinθcos²θ)^{α_paper/3}` is `(sinθcos²θ)^α`. -/
def pExp (α : ℝ) : ℝ := 3 * α

@[simp] theorem pExp_eq (α : ℝ) : pExp α = 3 * α := rfl

theorem pExp_pos {α : ℝ} (hα : 0 < α) : 0 < pExp α := by rw [pExp]; linarith

theorem pExp_le_one {α : ℝ} (hα13 : α ≤ 1 / 3) : pExp α ≤ 1 := by rw [pExp]; linarith


/-! ## The explicit Hölder constants of the per-slice transfer

The two constants below are the ones produced by the *existing* proofs of the two quantitative
inputs of the per-slice transfer (`Work.ConstructionInstance.holder_gComp` and
`Work.ConstructionInstance.holder_smul_eTheta`).  They are exposed here as *named* reals so that
the transfer lemmas of this chapter can be stated with an explicit constant — which is what makes
them uniform in the time parameter `τ` (an existential constant produced inside a `∀ τ` cannot be
used uniformly, see the module docstring of `Slice.lean`). -/

/-- The explicit Hölder constant of the composite profile
`x ↦ g (ρ(x)^{3α}) (|θ(x)|)` proved in `Work.ConstructionInstance.holder_gComp`: it is that
proof's `C` in terms of the data constants `Cv` (angular vanishing), `Lg` (radial modulus),
`Lθ` (angular modulus) and `K` (the `z = 0` Taylor/Lipschitz datum). -/
def gCompConst (α Cv Lg Lθ K : ℝ) : ℝ :=
  2 * Cv + (2 * Cv * (3 / 2) ^ α
    + (2 * K * 3 ^ (6 * α) + ((Lg * (3 * α) ^ α + Lθ * (4 * Real.pi) ^ α)
      + (K * (3 / 2) * 3 ^ α * (3 / 2) ^ (2 * α)
        + K * (3 / 2) ^ (3 * α) * (4 * Real.pi) * 2 ^ (3 * α - 1)))))

/-- `gCompConst` as a nonnegative real. -/
def gCompConstNN (α Cv Lg Lθ K : ℝ) : ℝ≥0 :=
  ⟨|gCompConst α Cv Lg Lθ K|, abs_nonneg _⟩

/-- The explicit Hölder constant of `x ↦ A x • e_θ(x)` proved in
`Work.ConstructionInstance.holder_smul_eTheta`: it is `CA + 2·Ca`, the Hölder constant of the
amplitude plus twice its vanishing rate. -/
def smulEThetaConst (CA Ca : ℝ) : ℝ≥0 := ⟨|CA + 2 * Ca|, abs_nonneg _⟩

/-- The angular factor `Γ(θ) = (sinθcos²θ)^α` of the route (this is `Work.ConstructionInstance.Gamma`
at the challenge's exponent `α`; the paper's `Γ` at `α_paper = 3α` is the same function). -/
abbrev Gamma (α θ : ℝ) : ℝ := Work.ConstructionInstance.Gamma α θ

theorem Gamma_eq_Gam (α θ : ℝ) : Gamma α θ = Work.Spaces.Gam (pExp α) θ := by
  simp only [Gamma, Work.ConstructionInstance.Gamma, Work.Spaces.Gam, pExp]
  norm_num

/-! ## The full profile and the perturbation -/

/-- The **full self-similar profile** `F(z,θ,τ) = F_*(z,θ) + g(z,θ,τ)`: the paper's profile
`F_*` plus the modulation `g`.  The physical vorticity is this profile composed with the
self-similar variables. -/
def profFull (α : ℝ) (g : ℝ → ℝ → ℝ → ℝ) (z θ τ : ℝ) : ℝ :=
  Work.Construction.Fstar (pExp α) z θ + g z θ τ

@[simp] theorem profFull_apply (α : ℝ) (g : ℝ → ℝ → ℝ → ℝ) (z θ τ : ℝ) :
    profFull α g z θ τ = Work.Construction.Fstar (pExp α) z θ + g z θ τ := rfl

/-- The `τ`-slice of the perturbation, as a two-variable profile. -/
def gSlice (g : ℝ → ℝ → ℝ → ℝ) (τ : ℝ) : ℝ → ℝ → ℝ := fun z θ => g z θ τ

@[simp] theorem gSlice_apply (g : ℝ → ℝ → ℝ → ℝ) (τ z θ : ℝ) :
    gSlice g τ z θ = g z θ τ := rfl

/-- The `τ`-slice of the full profile. -/
def profSlice (α : ℝ) (g : ℝ → ℝ → ℝ → ℝ) (τ : ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => profFull α g z θ τ

@[simp] theorem profSlice_apply (α : ℝ) (g : ℝ → ℝ → ℝ → ℝ) (τ z θ : ℝ) :
    profSlice α g τ z θ = profFull α g z θ τ := rfl

/-! ## The joint `α`-Hölder data in the self-similar variables -/

/-- **The joint `α`-Hölder class of the self-similar variables.**  `h : ℝ → ℝ → ℝ → ℝ` is
`α`-Hölder for the metric `|Δz| + |Δθ| + |Δτ|` on the domain `z ≥ 0`, `θ ∈ [0,π/2]`, with
constant `N` (`N ≥ 0`).

This is the form in which the route's `𝓗⁴`/`𝓦^{l,∞}` bounds on the profile enter the physical
transfer: the `(z,θ)` part at fixed `τ` gives the two moduli `hzk`/`hzth` of the `St1`-class data
(`Work.ConstructionInstance.holder_gComp`), the `τ` part gives the time-Hölder continuity of the
physical field, and the *joint* form is what makes the composition with `(x,τ) ↦ (z(x,τ),θ(x),τ)`
`α`-Hölder without any separate uniformity argument. -/
def JointHolder (α N : ℝ) (h : ℝ → ℝ → ℝ → ℝ) : Prop :=
  0 ≤ N ∧ ∀ z z' θ θ' τ τ' : ℝ, 0 ≤ z → 0 ≤ z' → θ ∈ Work.Spaces.Iθ → θ' ∈ Work.Spaces.Iθ →
    |h z θ τ - h z' θ' τ'| ≤ N * (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α

/-- **The regularity jet of a self-similar profile on the strip `[0,S]`**: the family
`h : ℝ → ℝ → ℝ → ℝ` is both *bounded* by `N` on the domain `z ≥ 0`, `θ ∈ Iθ`, `τ ∈ [0,S]` **and**
jointly `α`-Hölder there for the metric `|Δz| + |Δθ| + |Δτ|` with the same constant `N`.

The two conjuncts are deliberately bundled with one constant: this is the "`𝓦^{l,∞}` box" form of
the paper's data (a bounded profile with a Hölder modulus), and it is the form in which the
`τ`-regularity of the physical field is transferred — every factor of the chain-rule formula for
`∂_τω` is then *both* bounded and `α`-Hölder, so no separate boundedness hypothesis is needed. -/
def Jet (α S N : ℝ) (h : ℝ → ℝ → ℝ → ℝ) : Prop :=
  0 ≤ N ∧ (∀ z θ τ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → τ ∈ Set.Icc 0 S → |h z θ τ| ≤ N) ∧
    ∀ z z' θ θ' τ τ' : ℝ, 0 ≤ z → 0 ≤ z' → θ ∈ Work.Spaces.Iθ → θ' ∈ Work.Spaces.Iθ →
      τ ∈ Set.Icc 0 S → τ' ∈ Set.Icc 0 S →
        |h z θ τ - h z' θ' τ'| ≤ N * (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α

theorem Jet.nonneg {α S N : ℝ} {h : ℝ → ℝ → ℝ → ℝ} (H : Jet α S N h) : 0 ≤ N := H.1

/-- The uniform bound of a `Jet` at a strip time. -/
theorem Jet.abs_le {α S N : ℝ} {h : ℝ → ℝ → ℝ → ℝ} (H : Jet α S N h)
    {z θ τ : ℝ} (hz : 0 ≤ z) (hθ : θ ∈ Work.Spaces.Iθ) (hτ : τ ∈ Set.Icc 0 S) :
    |h z θ τ| ≤ N := H.2.1 z θ τ hz hθ hτ

/-- The `z`-modulus of a `Jet` at a fixed angle and time. -/
theorem Jet.zmod {α S N : ℝ} {h : ℝ → ℝ → ℝ → ℝ} (H : Jet α S N h)
    {z z' θ τ : ℝ} (hz : 0 ≤ z) (hz' : 0 ≤ z') (hθ : θ ∈ Work.Spaces.Iθ)
    (hτ : τ ∈ Set.Icc 0 S) :
    |h z θ τ - h z' θ τ| ≤ N * |z - z'| ^ α := by
  have h1 := H.2.2 z z' θ θ τ τ hz hz' hθ hθ hτ hτ
  simpa using h1

/-- The `θ`-modulus of a `Jet` at a fixed time. -/
theorem Jet.thmod {α S N : ℝ} {h : ℝ → ℝ → ℝ → ℝ} (H : Jet α S N h)
    {z θ θ' τ : ℝ} (hz : 0 ≤ z) (hθ : θ ∈ Work.Spaces.Iθ) (hθ' : θ' ∈ Work.Spaces.Iθ)
    (hτ : τ ∈ Set.Icc 0 S) :
    |h z θ τ - h z θ' τ| ≤ N * |θ - θ'| ^ α := by
  have h1 := H.2.2 z z θ θ' τ τ hz hz hθ hθ' hτ hτ
  simpa using h1

/-- The `τ`-modulus of a `Jet` at a fixed point of the domain. -/
theorem Jet.tmod {α S N : ℝ} {h : ℝ → ℝ → ℝ → ℝ} (H : Jet α S N h)
    {z θ τ τ' : ℝ} (hz : 0 ≤ z) (hθ : θ ∈ Work.Spaces.Iθ)
    (hτ : τ ∈ Set.Icc 0 S) (hτ' : τ' ∈ Set.Icc 0 S) :
    |h z θ τ - h z θ τ'| ≤ N * |τ - τ'| ^ α := by
  have h1 := H.2.2 z z θ θ τ τ' hz hz hθ hθ hτ hτ'
  simpa using h1

theorem JointHolder.nonneg {α N : ℝ} {h : ℝ → ℝ → ℝ → ℝ} (H : JointHolder α N h) : 0 ≤ N :=
  H.1

/-- The `(z,θ)`-modulus of a joint Hölder family at fixed `τ`. -/
theorem JointHolder.zmod {α N : ℝ} {h : ℝ → ℝ → ℝ → ℝ} (H : JointHolder α N h)
    {z z' θ τ : ℝ} (hz : 0 ≤ z) (hz' : 0 ≤ z') (hθ : θ ∈ Work.Spaces.Iθ) :
    |h z θ τ - h z' θ τ| ≤ N * |z - z'| ^ α := by
  have h1 := H.2 z z' θ θ τ τ hz hz' hθ hθ
  simpa using h1

/-- The `θ`-modulus of a joint Hölder family at fixed `τ`. -/
theorem JointHolder.thmod {α N : ℝ} {h : ℝ → ℝ → ℝ → ℝ} (H : JointHolder α N h)
    {z θ θ' τ : ℝ} (hz : 0 ≤ z) (hθ : θ ∈ Work.Spaces.Iθ) (hθ' : θ' ∈ Work.Spaces.Iθ) :
    |h z θ τ - h z θ' τ| ≤ N * |θ - θ'| ^ α := by
  have h1 := H.2 z z θ θ' τ τ hz hz hθ hθ'
  simpa using h1

/-- The `τ`-modulus of a joint Hölder family at fixed `(z,θ)`. -/
theorem JointHolder.tmod {α N : ℝ} {h : ℝ → ℝ → ℝ → ℝ} (H : JointHolder α N h)
    {z θ τ τ' : ℝ} (hz : 0 ≤ z) (hθ : θ ∈ Work.Spaces.Iθ) :
    |h z θ τ - h z θ τ'| ≤ N * |τ - τ'| ^ α := by
  have h1 := H.2 z z θ θ τ τ' hz hz hθ hθ
  simpa using h1

/-! ## The interface `RegPkg` -/

/-- **THE REGULARITY PACKAGE `RegPkg`** of node N7: the quantitative data of the self-similar
profile (in fake time `τ ∈ [0,S]`) from which the physical regularity of the reconstructed
vorticity and velocity is transferred.

The parameters are the challenge's Hölder exponent `α`, the end `S` of the fake-time strip, the
two clock functions `A, B` (`ω = A(τ)⁻¹·F(ρ^{3α}/B(τ),θ,τ)·e_θ`) and the perturbation
`g = F - F_*`.

The fields are, in order:

* `hα`, `hα13`, `hS`: `0 < α ≤ 1/3` (the paper's regime) and `S > 0`;
* the **clock data**: positivity and two-sided bounds on the strip, differentiability with a
  bounded derivative, and an `α`-Hölder derivative (for the time-Hölder of `∂_τω`);
* the **structural profile data**: vanishing on the angular boundaries `θ = 0, π/2` and at
  `z = 0` (with `∂_z g(0,·) = 0`);
* the **joint `α`-Hölder data** of `g`, of `∂_z g` and of `∂_τ g` in `(z,θ,τ)` (`JointHolder`);
* the **angular vanishing** `|g| ≤ Cv·Γ(θ)` (the `St1`-class datum: it is what makes the physical
  `e_θ`-field vanish fast enough at the axis to be Hölder there);
* the **quadratic vanishing** `|g| ≤ K z²` for `z ≤ 2` (the Taylor datum at `z = 0`: it is what
  makes `|ĝ x| ≤ Ca·r(x)^α`, compensating the `1/r` singularity of `e_θ` at the axis);
* the **compact support** of the full profile `F = F_* + g`;
* the honest **`ℋ⁴`-membership** of each slice (the weighted space of the paper; membership makes
  `HkNorm (3α) 4` the sum of `L²`-norms of the weighted derivatives rather than a junk value);
* the **first-order `τ` data**: the joint `C¹` smoothness of `(z,τ) ↦ g z θ τ` at each fixed `θ`,
  which is what makes `τ ↦ ω(x,τ)` differentiable.

Every field is a statement about the *profile*, never about the physical fields: the transfer
theorems of the sibling modules prove the physical consequences. -/
structure RegPkg (α : ℝ) (S : ℝ) (A B : ℝ → ℝ) (g : ℝ → ℝ → ℝ → ℝ) : Prop where
  /-- `0 < α` (the Hölder exponent of the challenge) -/
  hα : 0 < α
  /-- the paper's regime `α ≤ 1/3` -/
  hα13 : α ≤ 1 / 3
  /-- the fake-time strip is nonempty -/
  hS : 0 < S
  /-- the amplitude of the physical vorticity is positive on the strip -/
  hA : ∀ τ ∈ Set.Icc 0 S, 0 < A τ
  /-- the self-similar scaling is positive on the strip -/
  hB : ∀ τ ∈ Set.Icc 0 S, 0 < B τ
  /-- the amplitude is bounded above and below on the strip -/
  hAb : ∃ a₀ a₁ : ℝ, 0 < a₀ ∧ ∀ τ ∈ Set.Icc 0 S, a₀ ≤ A τ ∧ A τ ≤ a₁
  /-- the scaling is bounded above and below on the strip -/
  hBb : ∃ b₀ b₁ : ℝ, 0 < b₀ ∧ ∀ τ ∈ Set.Icc 0 S, b₀ ≤ B τ ∧ B τ ≤ b₁
  /-- the amplitude is differentiable on the strip, with its `deriv` as derivative -/
  hAdiff : ∀ τ ∈ Set.Icc 0 S, HasDerivAt A (deriv A τ) τ
  /-- the scaling is differentiable on the strip, with its `deriv` as derivative -/
  hBdiff : ∀ τ ∈ Set.Icc 0 S, HasDerivAt B (deriv B τ) τ
  /-- the derivative of the amplitude is bounded on the strip -/
  hAd : ∃ a₂ : ℝ, ∀ τ ∈ Set.Icc 0 S, |deriv A τ| ≤ a₂
  /-- the derivative of the scaling is bounded on the strip -/
  hBd : ∃ b₂ : ℝ, ∀ τ ∈ Set.Icc 0 S, |deriv B τ| ≤ b₂
  /-- the derivative of the amplitude is `α`-Hölder on the strip -/
  hAdh : ∃ a₃ : ℝ, ∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S,
    |deriv A τ - deriv A τ'| ≤ a₃ * |τ - τ'| ^ α
  /-- the derivative of the scaling is `α`-Hölder on the strip -/
  hBdh : ∃ b₃ : ℝ, ∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S,
    |deriv B τ - deriv B τ'| ≤ b₃ * |τ - τ'| ^ α
  /-- the perturbation vanishes on the two angular boundaries -/
  hvt : ∀ τ ∈ Set.Icc 0 S, Work.Spaces.VanishTheta (gSlice g τ)
  /-- the perturbation vanishes at `z = 0` -/
  hquad0 : ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, g 0 θ τ = 0
  /-- `∂_z g` vanishes at `z = 0` -/
  hquad : ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, Work.Spaces.pz (gSlice g τ) 0 θ = 0
  /-- the joint `α`-Hölder data of the perturbation -/
  hg : ∃ Ng : ℝ, Jet α S Ng g
  /-- the joint `α`-Hölder data of `∂_z g` -/
  hpz : ∃ Npz : ℝ, Jet α S Npz (fun z θ τ => Work.Spaces.pz (gSlice g τ) z θ)
  /-- the joint `α`-Hölder data of `∂_τ g` -/
  hgdoth : ∃ Nd : ℝ, Jet α S Nd (fun z θ τ => deriv (fun s => g z θ s) τ)
  /-- the uniform angular vanishing `|g| ≤ Cv·Γ(θ)` of the perturbation -/
  hvan : ∃ Cv : ℝ, 0 ≤ Cv ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
    |g z θ τ| ≤ Cv * Gamma α θ
  /-- the quadratic vanishing of `g` at `z = 0`, with the near-origin `z`- and `θ`-Lipschitz
  bounds of the slice: this is the Taylor datum of the paper's `St1`-class, and it is what makes
  `|ĝ x| ≤ Ca·r(x)^α` (`Work.ConstructionInstance.gComp_abs_le`), compensating the `1/r`
  singularity of `e_θ` at the axis -/
  htay : ∃ K : ℝ, 0 ≤ K ∧ ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ,
    (∀ z : ℝ, 0 ≤ z → z ≤ 2 → |g z θ τ| ≤ K * z ^ 2) ∧
    (∀ z z' : ℝ, 0 ≤ z → z ≤ 2 → 0 ≤ z' → z' ≤ 2 →
      |g z θ τ - g z' θ τ| ≤ K * max z z' * |z - z'|) ∧
    (∀ z : ℝ, 0 ≤ z → z ≤ 2 → ∀ θ' ∈ Work.Spaces.Iθ,
      |g z θ τ - g z θ' τ| ≤ K * z * |θ - θ'|)
  /-- the full profile is compactly supported in the self-similar variable `z` -/
  hsupp : ∃ L : ℝ, 0 < L ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, L ≤ z → profFull α g z θ τ = 0
  /-- the honest `ℋ⁴`-membership of every slice -/
  hH4 : ∀ τ ∈ Set.Icc 0 S, Work.Spaces.HkMem (pExp α) 4 (gSlice g τ)
  /-- the joint `C¹` smoothness of `(z,τ) ↦ g z θ τ` at every fixed angle `θ ∈ Iθ` -/
  hcont : ∀ θ ∈ Work.Spaces.Iθ, ContDiffOn ℝ 1
    (fun q : ℝ × ℝ => g q.1 θ q.2) (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (S + 1))

namespace RegPkg

variable {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}

theorem alpha_pos (h : RegPkg α S A B g) : 0 < α := h.hα

theorem pExp_pos (h : RegPkg α S A B g) : 0 < pExp α :=
  Work.FTS.Regularity.pExp_pos h.hα
theorem pExp_le_one (h : RegPkg α S A B g) : pExp α ≤ 1 :=
  Work.FTS.Regularity.pExp_le_one h.hα13

/-- The `VanishTheta` data, as a `Prop` about the slice. -/
theorem vanish (h : RegPkg α S A B g) {τ : ℝ} (hτ : τ ∈ Set.Icc 0 S) :
    Work.Spaces.VanishTheta (gSlice g τ) := h.hvt τ hτ



/-- **Pointwise boundedness of the perturbation**: `|g| ≤ Cv` on the domain, since `Γ ≤ 1`. -/
theorem abs_le_Cv (h : RegPkg α S A B g) :
    ∃ Cv : ℝ, 0 ≤ Cv ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |g z θ τ| ≤ Cv := by
  obtain ⟨Cv, hCv0, hCv⟩ := h.hvan
  refine ⟨Cv, hCv0, fun τ hτ z θ hz hθ => ?_⟩
  refine le_trans (hCv τ hτ z θ hz hθ) ?_
  have hθ' : θ ∈ Work.Spaces.Iθ := hθ
  have hΓ1 : Gamma α θ ≤ 1 := Work.ConstructionInstance.Gamma_le_one h.hα.le hθ
  have hΓ0 : 0 ≤ Gamma α θ := Work.ConstructionInstance.Gamma_nonneg hθ
  nlinarith





/-- **The radial modulus of the perturbation at a strip time** (`Lg` of the `St1`-class). -/
theorem zmod (h : RegPkg α S A B g) {τ : ℝ} (hτ : τ ∈ Set.Icc 0 S) :
    ∃ Lg : ℝ, 0 ≤ Lg ∧ ∀ z z' θ : ℝ, 0 ≤ z → 0 ≤ z' → θ ∈ Work.Spaces.Iθ →
      |g z θ τ - g z' θ τ| ≤ Lg * |z - z'| ^ α := by
  obtain ⟨N, hN⟩ := h.hg
  exact ⟨N, hN.1, fun z z' θ hz hz' hθ => hN.zmod hz hz' hθ hτ⟩

/-- **The angular modulus of the perturbation at a strip time** (`Lθ` of the `St1`-class). -/
theorem thmod (h : RegPkg α S A B g) {τ : ℝ} (hτ : τ ∈ Set.Icc 0 S) :
    ∃ Lθ : ℝ, 0 ≤ Lθ ∧ ∀ z θ θ' : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → θ' ∈ Work.Spaces.Iθ →
      |g z θ τ - g z θ' τ| ≤ Lθ * |θ - θ'| ^ α := by
  obtain ⟨N, hN⟩ := h.hg
  exact ⟨N, hN.1, fun z θ θ' hz hθ hθ' => hN.thmod hz hθ hθ' hτ⟩


end RegPkg

/-! ## The physical vorticity and velocity -/

/-- **THE PHYSICAL VORTICITY OF A SELF-SIMILAR PROFILE**, in physical time `τ`:

  `physVort α A B g x τ = A(τ)⁻¹ · F(ρ(x)^{3α}/B(τ), θ(x), τ) · e_θ(x)`,

where `F = F_* + g` is the full profile (`profFull`), `ρ(x) = ‖x‖`, `θ(x) = arctan(x₃/r)` and
`e_θ` is the azimuthal unit vector.  Equivalently (and definitionally, up to the odd extension of
the profile in `θ`), `physVort α A B g · τ = A(τ)⁻¹ • omegaSz (3α) (g · · τ) (ρ^{3α}/B(τ))`.

This is the paper's `ω^θ` as an `e_θ`-field: on the symmetry axis `r = 0` both `e_θ` (Lean's
junk `1/0 = 0`) and the `Γ`-factor of the profile vanish, so the field is `0` there — the value
that makes it continuous. -/
noncomputable def physVort (α : ℝ) (A B : ℝ → ℝ) (g : ℝ → ℝ → ℝ → ℝ) : R3 → ℝ → R3 :=
  fun x τ => (A τ)⁻¹ • Work.ConstructionInstance.omegaSz (pExp α) (gSlice g τ)
    (Work.Cyl.rho x ^ pExp α / B τ) x

theorem physVort_apply (α : ℝ) (A B : ℝ → ℝ) (g : ℝ → ℝ → ℝ → ℝ) (x : R3) (τ : ℝ) :
    physVort α A B g x τ = (A τ)⁻¹ • Work.ConstructionInstance.omegaSz (pExp α) (gSlice g τ)
      (Work.Cyl.rho x ^ pExp α / B τ) x := rfl


/-- **THE PHYSICAL VELOCITY**: the Biot–Savart field of the physical vorticity,
`physVel α A B g x τ = BS (physVort α A B g · τ) x`.  This is the object of node N8's
reconstruction and the target of the transfer theorem: `RegPkg` makes it jointly `C^{1,α}` on
`ℝ³ × [0,S]`.

The definition is the same as `Work.FTS.Physical.physVel (physVort α A B g)`; the two are
propositionally equal (`physVel_eq_Physical`). -/
noncomputable def physVel (α : ℝ) (A B : ℝ → ℝ) (g : ℝ → ℝ → ℝ → ℝ) : R3 → ℝ → R3 :=
  fun x τ => Work.LWP.biotSavart (fun y => physVort α A B g y τ) x

theorem physVel_apply (α : ℝ) (A B : ℝ → ℝ) (g : ℝ → ℝ → ℝ → ℝ) (x : R3) (τ : ℝ) :
    physVel α A B g x τ = Work.LWP.biotSavart (fun y => physVort α A B g y τ) x := rfl

theorem physVel_slice (α : ℝ) (A B : ℝ → ℝ) (g : ℝ → ℝ → ℝ → ℝ) (τ : ℝ) :
    (physVel α A B g · τ) = Work.LWP.biotSavart (fun y => physVort α A B g y τ) := rfl

/-- The physical time derivative of the vorticity is the `deriv` of the slice. -/
theorem physVort_timeDeriv (α : ℝ) (A B : ℝ → ℝ) (g : ℝ → ℝ → ℝ → ℝ) (x : R3) (τ : ℝ) :
    FiniteTimeSingularity.timeDeriv (physVort α A B g) x τ
      = deriv (fun s => physVort α A B g x s) τ := rfl

end Work.FTS.Regularity
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EComparison.SlotsZeroSliceInt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EComparison

open scoped Real
open MeasureTheory Set Filter

/-!
# Integrability of the `cos θ`-weighted `θ`-slice of a straightened solution

The `Ω`-comparison layer needs the `z`-slices of the straightened solution `Φ` to be
`L²(Iθ, cos θ dθ)`-integrable: `∀ z > 0, IntegrableOn (fun θ => Φ z θ ^ 2 * cos θ) Iθ`
(the consumer is `Work.FTS.StrongEps.EComparison.HomClsSlotsZero` with `Φ = Uop α w`).

This is a consequence of the *slot* hypothesis `HkMem α 6 (Φ / sin 2θ)`, in the same way as
`Work.FTS.PhiStar.Honesty.integrableOn_sq_cos_of_HkMem`: the level-`0` integrand of `Φ / sin 2θ`
dominates `Φ² cos θ` up to the bounded multiplier `sin²(2·) cos · ≤ 1`, and `HkMem α 6` implies
`HkMem α 0` by the monotonicity of the `ℋ^k`-integrand (the quotient is again `C^∞` on the open
quadrant, where `sin 2θ ≠ 0`).

Concretely: on `Iθ` the identity `Φ² cos θ = (Φ / sin 2θ)² cos θ · sin²(2θ)` holds away from the
two points `{0, π/2}` (which is the null set where `sin (2·)` vanishes), and there
`sin²(2θ) ≤ 1` while `cos θ ≥ 0`.  So the assertion is an a.e.-comparison of two functions, the
dominating one being the `θ`-slice of the level-`0` slot, whose integrability is the content of
`HkMem α 0 (Φ / sin 2θ)`.
-/

theorem SlotsZeroSliceInt {α : ℝ} {Φ : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen Φ)
    (h0 : ∀ z, Φ z 0 = 0)
    (hHk : Work.Spaces.HkMem α 6 (fun z θ => Φ z θ / Work.Construction.s2 θ)) :
    ∀ z, 0 < z → MeasureTheory.IntegrableOn (fun θ => Φ z θ ^ 2 * Real.cos θ)
      Work.Spaces.Iθ := by
  intro z hz
  -- `Φ / sin 2θ` is `C^∞` on the open quadrant, so the level-`6` honesty descends to level `0`.
  have hSO : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Φ z θ / Work.Construction.s2 θ) := by
    rw [Work.FTS.EllipticEst.smoothOpen_iff_forall]
    intro n
    have h1 : ContDiffOn ℝ n (Function.uncurry Φ) Work.FTS.EllipticEst.Q0 :=
      (Work.FTS.EllipticEst.smoothOpen_iff_forall Φ).mp hsm n
    have hs : ContDiffOn ℝ n (fun p : ℝ × ℝ => Real.sin (2 * p.2))
        Work.FTS.EllipticEst.Q0 :=
      ((Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn).of_le le_top
    have hne : ∀ p ∈ Work.FTS.EllipticEst.Q0, Real.sin (2 * p.2) ≠ 0 := by
      intro p hp
      obtain ⟨-, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
      exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos]))
    have hfun : Function.uncurry (fun z θ => Φ z θ / Work.Construction.s2 θ)
        = Function.uncurry Φ / fun p : ℝ × ℝ => Real.sin (2 * p.2) := by
      funext p
      obtain ⟨z, θ⟩ := p
      show Φ z θ / Work.Construction.s2 θ = Φ z θ / Real.sin (2 * θ)
      rw [Work.Construction.s2_eq]
    rw [hfun]
    exact h1.div hs hne
  have hF0 : Work.Spaces.HkMem α 0 (fun z θ => Φ z θ / Work.Construction.s2 θ) :=
    Work.FTS.OpenPkg.HkMem_mono_open hSO 0 (Nat.zero_le 6) hHk
  -- The `cos θ`-weighted `L²`-slice of `Φ / sin 2θ` is integrable.
  have hint : Integrable (fun θ => (Φ z θ / Work.Construction.s2 θ) ^ 2 * Real.cos θ)
      (volume.restrict Work.Spaces.Iθ) :=
    Work.FTS.PhiStar.Honesty.integrableOn_sq_cos_of_HkMem hF0 hz
  -- ## The zeros of `sin (2·)` inside `Iθ` are exactly the two endpoints
  have hmeas_zero : MeasurableSet {θ : ℝ | Work.Construction.s2 θ = 0} := by
    refine (measurableSet_singleton (0 : ℝ)).preimage ?_
    show Measurable fun θ : ℝ => Real.sin (2 * θ)
    exact Real.measurable_sin.comp (measurable_const.mul measurable_id)
  have hnull : volume {θ : ℝ | θ ∈ Work.Spaces.Iθ ∧ Work.Construction.s2 θ = 0} = 0 := by
    have hsub : {θ : ℝ | θ ∈ Work.Spaces.Iθ ∧ Work.Construction.s2 θ = 0} ⊆
        ({0, Real.pi / 2} : Set ℝ) := by
      intro θ hθ
      obtain ⟨hθI, hθ0⟩ := hθ
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      by_contra hcon
      simp only [not_or] at hcon
      obtain ⟨hne0, hnepi⟩ := hcon
      have hθpos : 0 < θ := lt_of_le_of_ne hθI.1 (Ne.symm hne0)
      have hθlt : θ < Real.pi / 2 := lt_of_le_of_ne hθI.2 hnepi
      have hs0 : Real.sin (2 * θ) = 0 := by
        rw [← Work.Construction.s2_eq]; exact hθ0
      have h1 : 0 < 2 * θ := by linarith
      have h2 : 2 * θ < Real.pi := by linarith [Real.pi_pos]
      have h3 := Real.sin_pos_of_pos_of_lt_pi h1 h2
      rw [hs0] at h3
      exact lt_irrefl 0 h3
    refine measure_mono_null hsub ?_
    rw [Set.insert_eq]
    exact measure_union_null (measure_singleton 0) (measure_singleton _)
  have hsin : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), Work.Construction.s2 θ ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    have hset : {a : ℝ | ¬ Work.Construction.s2 a ≠ 0}
        = {a : ℝ | Work.Construction.s2 a = 0} := by
      ext a; simp
    rw [hset, MeasureTheory.Measure.restrict_apply hmeas_zero]
    refine measure_mono_null ?_ hnull
    intro θ hθ
    exact ⟨hθ.2, hθ.1⟩
  -- ## The two functions agree a.e. on `Iθ`
  have hae : (fun θ => Φ z θ ^ 2 * Real.cos θ)
      =ᵐ[volume.restrict Work.Spaces.Iθ]
      (fun θ => ((Φ z θ / Work.Construction.s2 θ) ^ 2 * Real.cos θ)
        * Work.Construction.s2 θ ^ 2) := by
    filter_upwards [hsin] with θ hθ
    have h1 : (Φ z θ / Work.Construction.s2 θ) * Work.Construction.s2 θ = Φ z θ :=
      div_mul_cancel₀ _ hθ
    calc Φ z θ ^ 2 * Real.cos θ
        = (((Φ z θ / Work.Construction.s2 θ) * Work.Construction.s2 θ) ^ 2)
            * Real.cos θ := by rw [h1]
      _ = ((Φ z θ / Work.Construction.s2 θ) ^ 2 * Real.cos θ)
            * Work.Construction.s2 θ ^ 2 := by ring
  -- ## Integrability of the a.e. equal function
  have hprod : Integrable (fun θ => ((Φ z θ / Work.Construction.s2 θ) ^ 2 * Real.cos θ)
      * Work.Construction.s2 θ ^ 2) (volume.restrict Work.Spaces.Iθ) := by
    have hcont : Continuous fun θ : ℝ => Work.Construction.s2 θ ^ 2 := by
      have hfun : (fun θ : ℝ => Work.Construction.s2 θ ^ 2)
          = fun θ : ℝ => Real.sin (2 * θ) ^ 2 := by
        funext θ; rw [Work.Construction.s2_eq]
      rw [hfun]
      exact (Real.continuous_sin.comp (continuous_const.mul continuous_id)).pow 2
    refine Integrable.mono' hint (hint.aestronglyMeasurable.mul hcont.aestronglyMeasurable) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem (s := Work.Spaces.Iθ) measurableSet_Icc]
      with θ hθ
    have hc : 0 ≤ Real.cos θ :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    have hgnn : 0 ≤ (Φ z θ / Work.Construction.s2 θ) ^ 2 * Real.cos θ :=
      mul_nonneg (sq_nonneg _) hc
    have hs2le : Work.Construction.s2 θ ^ 2 ≤ 1 := by
      rw [Work.Construction.s2_eq]
      exact (sq_le_one_iff_abs_le_one _).mpr (Real.abs_sin_le_one _)
    rw [norm_mul, Real.norm_of_nonneg hgnn]
    calc ((Φ z θ / Work.Construction.s2 θ) ^ 2 * Real.cos θ)
            * ‖Work.Construction.s2 θ ^ 2‖
        ≤ ((Φ z θ / Work.Construction.s2 θ) ^ 2 * Real.cos θ) * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ hgnn
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          exact hs2le
      _ = ((Φ z θ / Work.Construction.s2 θ) ^ 2 * Real.cos θ) := mul_one _
  exact hprod.congr hae.symm

end Work.FTS.StrongEps.EComparison
end
