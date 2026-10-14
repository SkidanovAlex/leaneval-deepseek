import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.MetricSpace.Holder
import Submission.Work.FTS.PhiStar.RadialWAux.radPsi_iteratedDeriv
import Submission.Work.FTS.RegPkgGal.RVocab
import Submission.Work.FTS.RegPkgGal.St1Class
import Submission.Work.FTS.Regularity.profFullBounds
import Submission.Work.FTS.StrongEps.EComparison.SlotsZeroSliceInt
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.RowMuAux.SlotDataOpen
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.FKdzIter_sq_le
import Submission.Work.FTS.StrongPersist.Star6
import Submission.Work.FTS.StrongPersist.Vocab
import Submission.Work.FTS.Vocab
import Submission.Work.FTS_MuLipC.RowN.FaSlice
import Submission.Work.FTS_RegExport.RXR5L.L12fAux.C1Jet_L12f_of_support
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.R1G.vecResid_eq_scalar_smul
import Submission.Work.StabilityFar.Decay.hasDerivAt_bsK
-- ===== merged: Submission.Work.CoreResiduals.BiotSavart.biotSavart_contDiffOn_strip =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Metric Filter Topology Set
open scoped Topology

namespace Work.CoreResiduals.BiotSavart

/-- **The `C¹` clause of the space-time statement, for a bundled strip vorticity.**

For `0 < α < 1` and `ω` satisfying the full strip bundle `BSAdmissibleStripFull α ω R S`, the reconstructed velocity `q ↦ BS (ω(·,q.2)) q.1` is `C¹` on the strip `ℝ³ × [0,S]`.

This is one of the three conjuncts of `IsContDiffHolderOn` in the space-time statement (`BiotSavartSpaceTime α`), and it is the qualitative part: the workspace already proves the same `C¹` statement for the bundle `BSAdmissibleOnWindow ω R T` together with `TimeDerivLocallyLipschitz ω T` (`BiotSavart.biotSavartSpacetimeC1_holds`).

**Suggested route.**  `ContDiffOn` on the strip is local, so it suffices to prove `ContDiffWithinAt ℝ 1 f (univ ×ˢ Icc 0 S) (x,t)` for each `t ∈ Icc 0 S`.  Both the `x`-derivative (Calderón–Zygmund, needs support/boundedness/`x`-Hölder of the slice `ω(·,t)`) and the `t`-derivative (differentiation under the integral sign, `Work.StabilityFar.Decay.hasDerivAt_biotSavart`, needs the slices `t`-differentiable with bounded `∂ₜω`) are local in `t` inside the strip, so the endpoints are not a problem: one can re-run the argument of `biotSavartSpacetimeC1_holds` with the strip bundle's clauses restricted to `Icc 0 S` (they all hold there), or extend `ω` in `t` and instantiate the existing window result (the reviewer's note: the extension must make `∂ₜω̃` *locally Lipschitz* in `t` for `TimeDerivLocallyLipschitz`, which is available from `TimeDerivStripHolder` only for `α ≥ 1`, so `β < α` should be used if taking the extension route).  Note that `∂ₜω(·,t)` is supported in `closedBall 0 R` on `Icc 0 S` (`TimeDerivStrip` plus the support clause). -/
theorem biotSavart_contDiffOn_strip {α : NNReal} (hα : 0 < (α : ℝ)) (hα1 : (α : ℝ) < 1)
    {ω : Work.LWP.R3 → ℝ → Work.LWP.R3} {R S : ℝ}
    (hbun : Work.CoreResiduals.BSAdmissibleStripFull α ω R S) :
    ContDiffOn ℝ 1 (fun q : Work.LWP.R3 × ℝ => Work.LWP.biotSavart (fun y => ω y q.2) q.1)
      (Set.univ ×ˢ Set.Icc (0:ℝ) S) := by
  by_cases hSneg : S < 0
  · -- The strip is empty: nothing to prove.
    have hIcc : Set.Icc (0:ℝ) S = ∅ := Set.Icc_eq_empty_iff.mpr (not_le.mpr hSneg)
    rw [hIcc, Set.prod_empty]
    exact contDiffOn_empty
  · rcases lt_or_eq_of_le (not_lt.mp hSneg) with hSpos | hSzero
    · -- `0 < S`: extend `ω` to a two-sided window and apply the window theorem.
      obtain ⟨c, hcpos, Cx, hCxnn, hxH⟩ := timeDeriv_xHolderOn_of_stripBundle hα hα1 hSpos hbun
      obtain ⟨ω_ext, hagree, hadmw, hdtcw⟩ :=
        exists_windowExtension_of_stripBundle hα hα1 hSpos hbun ⟨c, hcpos, Cx, hCxnn, hxH⟩
      have hOn : ContDiffOn ℝ 1 (fun q : Work.LWP.R3 × ℝ =>
          Work.LWP.biotSavart (fun y => ω_ext y q.2) q.1) (Set.univ ×ˢ Set.Icc (0:ℝ) S) := by
        intro q hq
        have hqIcc : q.2 ∈ Set.Icc (0:ℝ) S := hq.2
        have ht : q.2 ∈ Work.ConstructionInstance.preWindow (S + 1) := by
          change q.2 ∈ Set.Ioo (-2) (S + 1)
          exact ⟨by linarith [hqIcc.1], by linarith [hqIcc.2]⟩
        exact (biotSavartSpacetimeC1_of_dtContinuous hadmw hdtcw q.1 q.2 ht).contDiffWithinAt
      refine ContDiffOn.congr hOn ?_
      intro q hq
      have hfun : (fun y : Work.LWP.R3 => ω y q.2) = (fun y => ω_ext y q.2) :=
        funext fun y => (hagree q.2 hq.2 y).symm
      rw [hfun]
    · -- `S = 0`: the strip is the hyperplane `{t = 0}` and the field is a single slice.
      obtain rfl : S = 0 := hSzero.symm
      obtain ⟨⟨hRpos, hsupp, hbdd, hhold, htime, hmeas⟩, ⟨hdc, hbddD, hmeasD⟩, hholdD⟩ := hbun
      obtain ⟨M, hM⟩ := hbdd
      obtain ⟨H, hH⟩ := hhold
      have h0 : (0:ℝ) ∈ Set.Icc (0:ℝ) 0 := Set.left_mem_Icc.mpr le_rfl
      have hbdd0 : ∀ a : Work.LWP.R3, ‖ω a 0‖ ≤ max M 0 :=
        fun a => le_trans (hM 0 h0 a) (le_max_left _ _)
      have hsupp0 : ∀ a : Work.LWP.R3, ω a 0 ≠ 0 → a ∈ Metric.closedBall 0 R :=
        fun a ha => hsupp 0 h0 a ha
      have hmeas0 : MeasureTheory.AEStronglyMeasurable (fun a : Work.LWP.R3 => ω a 0)
          MeasureTheory.volume := hmeas 0 h0
      have hhold0 : ∀ a b : Work.LWP.R3,
          ‖ω a 0 - ω b 0‖ ≤ (H : ℝ) * ‖a - b‖ ^ (α : ℝ) := by
        intro a b
        have hH0 : HolderWith H α (fun x : Work.LWP.R3 => ω x 0) := hH 0 h0
        rw [← dist_eq_norm, ← dist_eq_norm]
        exact hH0.dist_le a b
      have hF : ContDiff ℝ 1 (Work.LWP.biotSavart (fun y => ω y 0)) :=
        biotSavart_contDiff_one hRpos (le_max_right _ _) hα hbdd0 hsupp0 hmeas0 hhold0
      refine ContDiffOn.congr
        (((hF.comp contDiff_fst).contDiffOn).mono (Set.subset_univ _)) ?_
      intro q hq
      have hq0 : q.2 = 0 := by
        obtain ⟨hq1, hq2⟩ := Set.mem_Icc.mp hq.2
        exact le_antisymm hq2 hq1
      rw [hq0]
      rfl

end Work.CoreResiduals.BiotSavart
end
end
-- ===== merged: Submission.Work.CoreResiduals.BiotSavart.windowExt_windowBundle =====
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

/-- **The two-sided time-extension of a bundled strip vorticity satisfies the window bundle.**
This is the statement of the already-proved
`Work.CoreResiduals.BiotSavart.exists_windowExtension_of_stripBundle`
(`Submission/Work/CoreResiduals/BiotSavart/exists_windowExtension_of_stripBundle.lean`), made
*concrete* in the extension (the explicit `windowExt ω S` constructed there, instead of an
existentially quantified `ω_ext`) and with the dead hypothesis `hα1 : (α : ℝ) < 1` deleted (Lean
itself reports `Variable name hα1 is not explicitly referenced` for that file).  The existing proof
already concludes with `refine ⟨windowExt ω S, ?_, ?_, ?_⟩` where the three goals are the agreement
clause, `BSAdmissibleOnWindow (windowExt ω S) R (S+1)` and
`TimeDerivLocallyContinuous (windowExt ω S) (S+1)`; so the proof of the conjunction below is
verbatim the second and third bullets of that proof.  It is NOT derivable from
`exists_windowExtension_of_stripBundle` by taking `.2` of the existential (that gives an
unspecified witness, and the source result assumes `hα1` anyway). -/
theorem windowExt_windowBundle {α : NNReal} (hα : 0 < (α : ℝ))
    {ω : Work.LWP.R3 → ℝ → Work.LWP.R3} {R S : ℝ} (hS : 0 < S)
    (hbun : Work.CoreResiduals.BSAdmissibleStripFull α ω R S)
    (hxH : ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ a b : Work.LWP.R3, ∀ t ∈ Set.Icc (0:ℝ) S,
      ‖FiniteTimeSingularity.timeDeriv ω a t - FiniteTimeSingularity.timeDeriv ω b t‖
        ≤ C * ‖a - b‖ ^ c) :
    Work.CoreResiduals.BSAdmissibleOnWindow (Work.CoreResiduals.BiotSavart.windowExt ω S) R (S + 1) ∧
      Work.CoreResiduals.TimeDerivLocallyContinuous
        (Work.CoreResiduals.BiotSavart.windowExt ω S) (S + 1) := by
  have hstrip := hbun.1
  have hTD := hbun.2.1
  have hTDH := hbun.2.2
  obtain ⟨hRpos, hsupp, _hbdd, _hholder, _htholder, hslices⟩ := hstrip
  have hdiff := hTD.1
  obtain ⟨M₁, hM₁⟩ := hTD.2.1
  have hdtmeas := hTD.2.2
  obtain ⟨N₁, hN₁⟩ := hTDH
  have h0mem : (0:ℝ) ∈ Set.Icc (0:ℝ) S := ⟨le_refl 0, le_of_lt hS⟩
  have hSmem : S ∈ Set.Icc (0:ℝ) S := ⟨le_of_lt hS, le_refl S⟩
  refine ⟨?_, ?_⟩
  · refine ⟨hRpos, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro t y hy
      by_contra hyb
      exact hy (windowExt_eq_zero_of_notMem_closedBall hS hsupp hdiff hyb t)
    · intro t₀ _
      obtain ⟨M', hM'⟩ := windowExt_localBdd hS hbun t₀
      exact ⟨1, one_pos, M', fun t ht y => hM' t ht y⟩
    · intro t₀ _
      obtain ⟨c, hc, C, hC⟩ := windowExt_holder_bound hα hS hbun hxH t₀
      exact ⟨1, one_pos, c, hc, C, fun t ht a b => hC t ht a b⟩
    · intro t₀ _
      refine ⟨1, one_pos, fun t _ => ?_⟩
      by_cases h : t ≤ 0
      · have heq : (fun y : Work.LWP.R3 => windowExt ω S y t)
            = fun y => ω y 0 + t • FiniteTimeSingularity.timeDeriv ω y 0 := by
          funext y; exact windowExt_of_nonpos h
        rw [heq]
        exact (hslices 0 h0mem).add ((hdtmeas 0 h0mem).const_smul t)
      · by_cases h2 : t ≤ S
        · have heq : (fun y : Work.LWP.R3 => windowExt ω S y t) = fun y => ω y t := by
            funext y; exact windowExt_of_mem_Icc ⟨le_of_lt (lt_of_not_ge h), h2⟩
          rw [heq]
          exact hslices t ⟨le_of_lt (lt_of_not_ge h), h2⟩
        · have heq : (fun y : Work.LWP.R3 => windowExt ω S y t)
              = fun y => ω y S + (t - S) • FiniteTimeSingularity.timeDeriv ω y S := by
            funext y; exact windowExt_of_ge hS (le_of_lt (lt_of_not_ge h2))
          rw [heq]
          exact (hslices S hSmem).add ((hdtmeas S hSmem).const_smul (t - S))
    · intro t₀ _
      refine ⟨1, one_pos, fun t _ y => ?_⟩
      rw [timeDeriv_windowExt hS hdiff y t]
      exact hasDerivAt_windowExt hS hdiff y t
    · intro t₀ _
      refine ⟨1, one_pos, max M₁ 0, fun t _ y => ?_⟩
      rw [timeDeriv_windowExt hS hdiff y t]
      by_cases h : t ≤ 0
      · rw [dtExt_of_nonpos h]
        exact le_trans (hM₁ 0 h0mem y) (le_max_left _ _)
      · by_cases h2 : t ≤ S
        · rw [dtExt_of_mem_Icc ⟨le_of_lt (lt_of_not_ge h), h2⟩]
          exact le_trans (hM₁ t ⟨le_of_lt (lt_of_not_ge h), h2⟩ y) (le_max_left _ _)
        · rw [dtExt_of_ge hS (le_of_lt (lt_of_not_ge h2))]
          exact le_trans (hM₁ S hSmem y) (le_max_left _ _)
    · intro t₀ _
      refine ⟨1, one_pos, fun t _ => ?_⟩
      have heq : (fun y : Work.LWP.R3 => FiniteTimeSingularity.timeDeriv (windowExt ω S) y t)
          = fun y => dtExt ω S y t := by
        funext y; exact timeDeriv_windowExt hS hdiff y t
      rw [heq]
      by_cases h : t ≤ 0
      · have heq2 : (fun y : Work.LWP.R3 => dtExt ω S y t)
            = fun y => FiniteTimeSingularity.timeDeriv ω y 0 := by
          funext y; exact dtExt_of_nonpos h
        rw [heq2]
        exact hdtmeas 0 h0mem
      · by_cases h2 : t ≤ S
        · have heq2 : (fun y : Work.LWP.R3 => dtExt ω S y t)
              = fun y => FiniteTimeSingularity.timeDeriv ω y t := by
            funext y; exact dtExt_of_mem_Icc ⟨le_of_lt (lt_of_not_ge h), h2⟩
          rw [heq2]
          exact hdtmeas t ⟨le_of_lt (lt_of_not_ge h), h2⟩
        · have heq2 : (fun y : Work.LWP.R3 => dtExt ω S y t)
              = fun y => FiniteTimeSingularity.timeDeriv ω y S := by
            funext y; exact dtExt_of_ge hS (le_of_lt (lt_of_not_ge h2))
          rw [heq2]
          exact hdtmeas S hSmem
  · intro t₀ _
    refine ⟨1, one_pos, fun t _ y => ?_⟩
    have heq : (fun s : ℝ => FiniteTimeSingularity.timeDeriv (windowExt ω S) y s)
        = fun s => dtExt ω S y s := by
      funext s; exact timeDeriv_windowExt hS hdiff y s
    rw [heq]
    exact continuousAt_dtExt hα hS hN₁ y t

end Work.CoreResiduals.BiotSavart
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Series.SmoothAux.Deleg.radPsi_rec =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.PhiStar.RadialWAux

namespace Work.FTS.PhiStar.Series.SmoothAux.Deleg

set_option autoImplicit false

/-! ### General-order versions of the analytic input

The order-`22` statements of `RadialWAux/radPsi_iteratedDeriv.lean` and the tail
integration by parts `RadialWAux/Aux3.radPsi_tail_ibp_aux` are restated here for an
arbitrary order `N`, which is what `radPsi_rec` needs. -/

/-- On `(0,∞)` a `C^N` function has continuous `k`-th iterated derivative, `k ≤ N`. -/
lemma rpr_contDiffOn_iteratedDeriv {c : ℝ → ℝ} {N : ℕ}
    (hc : ContDiffOn ℝ N c (Set.Ioi 0)) {k : ℕ} (hk : k ≤ N) :
    ContinuousOn (iteratedDeriv k c) (Set.Ioi 0) := by
  have h1 : ContinuousOn (iteratedDerivWithin k c (Set.Ioi 0)) (Set.Ioi 0) :=
    hc.continuousOn_iteratedDerivWithin (by exact_mod_cast hk) isOpen_Ioi.uniqueDiffOn
  exact h1.congr fun x hx => (iteratedDerivWithin_of_isOpen isOpen_Ioi hx).symm

/-- The `(k+1)`-st iterated derivative is the derivative of the `k`-th one. -/
lemma rpr_hasDerivAt_iteratedDeriv {c : ℝ → ℝ} {x : ℝ} {N k : ℕ}
    (hc : ContDiffAt ℝ N c x) (hk : k < N) :
    HasDerivAt (iteratedDeriv k c) (iteratedDeriv (k + 1) c x) x := by
  have hd : DifferentiableAt ℝ (iteratedDeriv k c) x := by
    have h' := hc.contDiffWithinAt.differentiableWithinAt_iteratedDerivWithin (m := k)
      (show ((k : ℕ) : WithTop ℕ∞) < ((N : ℕ) : WithTop ℕ∞) by exact_mod_cast hk)
      (show UniqueDiffOn ℝ (insert x (Set.univ : Set ℝ)) from by
        simpa using (uniqueDiffOn_univ (𝕜 := ℝ) (E := ℝ)))
    rw [differentiableWithinAt_univ] at h'
    simpa using h'
  have h1 : HasDerivAt (iteratedDeriv k c) (deriv (iteratedDeriv k c) x) x := hd.hasDerivAt
  simpa [iteratedDeriv_succ] using h1

/-- **Differentiation under the integral sign for the `Ψ`-kernel**, at order `N`: if `c` is
`C^N` on `(0,∞)` with `|c^{(j)}| ≤ K` there, `k + 1 ≤ N` and `k + 1 < p`, then at every `z > 0`

  `z ↦ ∫_{u > 1} c^{(k)}(z u) u^{k-p-1} du` has derivative `∫_{u>1} c^{(k+1)}(z u) u^{k-p} du`. -/
theorem rpr_kernel_hasDerivAt {c : ℝ → ℝ} {K p : ℝ} {N : ℕ}
    (hc : ContDiffOn ℝ N c (Set.Ioi 0)) (hb : Work.FTS.PhiStar.BddDeriv N c K)
    {k : ℕ} (hkN : k + 1 ≤ N) (hkp : (k : ℝ) + 1 < p) {z : ℝ} (hz : 0 < z) :
    HasDerivAt
      (fun x : ℝ => ∫ u in Set.Ioi 1, iteratedDeriv k c (x * u) * u ^ ((k : ℝ) - p - 1))
      (∫ u in Set.Ioi 1,
        iteratedDeriv (k + 1) c (z * u) * u ^ (((k + 1 : ℕ) : ℝ) - p - 1)) z := by
  have hkN' : k ≤ N := by omega
  have hlt : (k : ℝ) - p < -1 := by linarith
  have hlt' : (k : ℝ) - p - 1 < -1 := by linarith
  have hcont_k : ContinuousOn (iteratedDeriv k c) (Set.Ioi 0) :=
    rpr_contDiffOn_iteratedDeriv hc hkN'
  have hcont_k1 : ContinuousOn (iteratedDeriv (k + 1) c) (Set.Ioi 0) :=
    rpr_contDiffOn_iteratedDeriv hc hkN
  have hne : ∀ u ∈ Set.Ioi (1 : ℝ), u ≠ 0 := fun u hu => ne_of_gt (lt_trans zero_lt_one hu)
  have hrpow : ContinuousOn (fun u : ℝ => u ^ ((k : ℝ) - p - 1)) (Set.Ioi 1) :=
    continuousOn_id.rpow continuousOn_const (fun u hu => Or.inl (hne u hu))
  have hrpow1 : ContinuousOn (fun u : ℝ => u ^ (((k + 1 : ℕ) : ℝ) - p - 1)) (Set.Ioi 1) :=
    continuousOn_id.rpow continuousOn_const (fun u hu => Or.inl (hne u hu))
  have hcomp : ∀ x : ℝ, 0 < x →
      ContinuousOn (fun u : ℝ => iteratedDeriv k c (x * u)) (Set.Ioi 1) :=
    fun x hx => hcont_k.comp ((continuousOn_const.mul continuousOn_id).mono (Set.subset_univ _))
      (fun u hu => mul_pos hx (lt_trans zero_lt_one hu))
  have hcomp1 : ∀ x : ℝ, 0 < x →
      ContinuousOn (fun u : ℝ => iteratedDeriv (k + 1) c (x * u)) (Set.Ioi 1) :=
    fun x hx => hcont_k1.comp ((continuousOn_const.mul continuousOn_id).mono (Set.subset_univ _))
      (fun u hu => mul_pos hx (lt_trans zero_lt_one hu))
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ioi 1)) (s := Set.Ioi (0 : ℝ)) (x₀ := z)
    (F := fun x u : ℝ => iteratedDeriv k c (x * u) * u ^ ((k : ℝ) - p - 1))
    (F' := fun x u : ℝ => iteratedDeriv (k + 1) c (x * u) * u ^ (((k + 1 : ℕ) : ℝ) - p - 1))
    (bound := fun u : ℝ => K * u ^ ((k : ℝ) - p))
    (isOpen_Ioi.mem_nhds hz)
    (by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with x hx
      exact ((hcomp x hx).mul hrpow).aestronglyMeasurable measurableSet_Ioi)
    (by
      refine MeasureTheory.Integrable.mono'
        ((integrableOn_Ioi_rpow_of_lt hlt' zero_lt_one).const_mul K)
        (((hcomp z hz).mul hrpow).aestronglyMeasurable measurableSet_Ioi) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hu' : 0 < u := lt_trans zero_lt_one hu
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hu' _)]
      exact mul_le_mul_of_nonneg_right (hb k hkN' (z * u) (mul_pos hz hu'))
        (le_of_lt (Real.rpow_pos_of_pos hu' _)))
    (by exact ((hcomp1 z hz).mul hrpow1).aestronglyMeasurable measurableSet_Ioi)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha x hx
      have ha' : 0 < a := lt_trans zero_lt_one ha
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos ha' _),
        show (((k + 1 : ℕ) : ℝ) - p - 1) = (k : ℝ) - p from by push_cast; ring]
      exact mul_le_mul_of_nonneg_right (hb (k + 1) hkN (x * a) (mul_pos hx ha'))
        (le_of_lt (Real.rpow_pos_of_pos ha' _)))
    (by exact (integrableOn_Ioi_rpow_of_lt hlt zero_lt_one).const_mul K)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha x hx
      have ha' : 0 < a := lt_trans zero_lt_one ha
      have hid : HasDerivAt (fun y : ℝ => y * a) a x := by
        simpa using (hasDerivAt_id x).mul_const a
      have hca : ContDiffAt ℝ N c (x * a) :=
        hc.contDiffAt (isOpen_Ioi.mem_nhds (mul_pos hx ha'))
      have hd := rpr_hasDerivAt_iteratedDeriv hca (by omega : k < N)
      have hc' := hd.comp x hid
      have hfun : (iteratedDeriv k c ∘ fun y : ℝ => y * a) =
          fun y : ℝ => iteratedDeriv k c (y * a) := rfl
      rw [hfun] at hc'
      have hres := hc'.mul_const (a ^ ((k : ℝ) - p - 1))
      have hval : ((iteratedDeriv (k + 1) c (x * a) * a) * a ^ ((k : ℝ) - p - 1))
          = iteratedDeriv (k + 1) c (x * a) * a ^ (((k + 1 : ℕ) : ℝ) - p - 1) := by
        rw [show (((k + 1 : ℕ) : ℝ) - p - 1) = 1 + ((k : ℝ) - p - 1) from by push_cast; ring,
          Real.rpow_add ha', Real.rpow_one]
        ring
      rw [hval] at hres
      exact hres)
  exact hmain.2

/-! ### The bounding sequence of the recursion -/

/-- The auxiliary sequence bounding the formal derivatives of `Ψ`:
`Bnd p z₀ 0 = 1/p` and `Bnd p z₀ (j+1) = ((p + j) * Bnd p z₀ j + 1)/z₀`. -/
def Bnd (p z₀ : ℝ) : ℕ → ℝ :=
  fun n => Nat.rec (1 / p) (fun j bj => ((p + (j : ℝ)) * bj + 1) / z₀) n

lemma Bnd_zero (p z₀ : ℝ) : Bnd p z₀ 0 = 1 / p := rfl

lemma Bnd_succ (p z₀ : ℝ) (j : ℕ) :
    Bnd p z₀ (j + 1) = ((p + (j : ℝ)) * Bnd p z₀ j + 1) / z₀ := rfl

/-! ### The base case of the recursion -/

/-- The value of the first formal derivative: `psiF 1 z = (p Ψ z - c z)/z`. -/
lemma rpr_psiF_one (α : ℝ) (m : ℕ) (c : ℝ → ℝ) (z : ℝ) :
    psiF α m c 1 z = (radP α m * radPsi α m c z - c z) / z := by
  have h : psiF α m c (0 + 1) =
      fun w => (radP α m * radPsi α m c w - c w) / w := by
    rw [psiF_succ]
    simp only [psiF_zero, iteratedDeriv_zero, Nat.cast_zero, sub_zero]
  rw [show (0 : ℕ) + 1 = 1 from rfl] at h
  exact congrFun h z

/-- The crude integral bound for `Ψ`: `|Ψ z| ≤ K/p` for `z > 0`. -/
lemma rpr_base_bound {α : ℝ} (m : ℕ) {c : ℝ → ℝ} {K : ℝ} {N : ℕ}
    (_hK : 0 ≤ K) (hb : Work.FTS.PhiStar.BddDeriv N c K) (hp : 0 < radP α m) :
    ∀ z : ℝ, 0 < z → |radPsi α m c z| ≤ K / radP α m := by
  intro z hz
  have hlt : -(radP α m) - 1 < -1 := by linarith
  have hbnd : ∀ᵐ u ∂(volume.restrict (Set.Ioi 1)),
      ‖c (z * u) * u ^ (-(radP α m) - 1)‖ ≤ K * u ^ (-(radP α m) - 1) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 < u := lt_trans zero_lt_one hu
    have hrpow : 0 ≤ u ^ (-(radP α m) - 1) := Real.rpow_nonneg hu0.le _
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hrpow]
    exact mul_le_mul_of_nonneg_right
      (by simpa only [iteratedDeriv_zero] using hb 0 (Nat.zero_le N) (z * u) (mul_pos hz hu0))
      hrpow
  have hInt : ∫ u in Set.Ioi 1, u ^ (-(radP α m) - 1) = 1 / radP α m := by
    rw [integral_Ioi_rpow_of_lt (a := -(radP α m) - 1) hlt (c := 1) zero_lt_one, Real.one_rpow,
      show (-(radP α m) - 1) + 1 = -(radP α m) from by ring]
    rw [div_eq_div_iff (by linarith : (-(radP α m)) ≠ 0) (ne_of_gt hp)]
    ring
  have hmain : |∫ u in Set.Ioi 1, c (z * u) * u ^ (-(radP α m) - 1)| ≤ K / radP α m := by
    calc |∫ u in Set.Ioi 1, c (z * u) * u ^ (-(radP α m) - 1)|
        = ‖∫ u in Set.Ioi 1, c (z * u) * u ^ (-(radP α m) - 1)‖ := by rw [Real.norm_eq_abs]
      _ ≤ ∫ u in Set.Ioi 1, K * u ^ (-(radP α m) - 1) :=
          norm_integral_le_of_norm_le
            ((integrableOn_Ioi_rpow_of_lt hlt zero_lt_one).const_mul K) hbnd
      _ = K * (∫ u in Set.Ioi 1, u ^ (-(radP α m) - 1)) := by rw [integral_const_mul]
      _ = K / radP α m := by rw [hInt]; ring
  simpa only [radPsi] using hmain

/-- The base case of the recursion, in the form of a `HasDerivAt` statement:
`z ↦ Ψ z` has derivative `(p Ψ z - c z)/z`.  This is the integration by parts of
`d/du (c(zu) u^{-p})` over `(1,∞)` together with differentiation under the integral sign. -/
lemma rpr_deriv_value {α : ℝ} (m : ℕ) {c : ℝ → ℝ} {K : ℝ} {N : ℕ}
    (hN : 1 ≤ N) (hK : 0 ≤ K) (hc : ContDiffOn ℝ N c (Set.Ioi 0))
    (hb : Work.FTS.PhiStar.BddDeriv N c K) (hp : 1 < radP α m) :
    ∀ z : ℝ, 0 < z →
      HasDerivAt (radPsi α m c) ((radP α m * radPsi α m c z - c z) / z) z := by
  intro z hz
  have hker := rpr_kernel_hasDerivAt (c := c) (K := K) (p := radP α m) (N := N) hc hb
    (k := 0) (by omega) (by push_cast; linarith) hz
  have hΨeq : (fun x : ℝ => ∫ u in Set.Ioi 1,
      iteratedDeriv 0 c (x * u) * u ^ (((0 : ℕ) : ℝ) - radP α m - 1)) = radPsi α m c := by
    funext x
    show (∫ u in Set.Ioi 1, iteratedDeriv 0 c (x * u) * u ^ (((0 : ℕ) : ℝ) - radP α m - 1))
        = ∫ u in Set.Ioi 1, c (x * u) * u ^ (-(radP α m) - 1)
    rw [show iteratedDeriv 0 c = c from iteratedDeriv_zero]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with u
    rw [show (((0 : ℕ)) : ℝ) - radP α m - 1 = -(radP α m) - 1 from by push_cast; ring]
  have hVeq : (∫ u in Set.Ioi 1,
        iteratedDeriv (0 + 1) c (z * u) * u ^ (((0 + 1 : ℕ) : ℝ) - radP α m - 1))
      = ∫ u in Set.Ioi 1, deriv c (z * u) * u ^ (-(radP α m)) := by
    rw [show iteratedDeriv (0 + 1) c = deriv c from by
      rw [iteratedDeriv_succ, iteratedDeriv_zero]]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with u
    rw [show (((0 + 1 : ℕ)) : ℝ) - radP α m - 1 = -(radP α m) from by push_cast; ring]
  have hker' : HasDerivAt (radPsi α m c)
      (∫ u in Set.Ioi 1, deriv c (z * u) * u ^ (-(radP α m))) z := by
    rw [hΨeq, hVeq] at hker
    exact hker
  have hbnd : ∀ j : ℕ, j ≤ 1 → ∀ t : ℝ, 0 < t → |iteratedDeriv j c t| ≤ K := by
    intro j hj t ht
    exact hb j (by omega) t ht
  have hcont1 : ContDiffOn ℝ 1 c (Set.Ioi 0) := hc.of_le (by exact_mod_cast hN)
  have hIBP := radPsi_tail_ibp_aux (c := c) (k := 1) (K := K) (s := -(radP α m)) (z := z)
    le_rfl hz hK (by linarith) hcont1 hbnd
  rw [show (1 : ℕ) - 1 = 0 from rfl, iteratedDeriv_zero] at hIBP
  have hIBP' : (∫ u in Set.Ioi (1 : ℝ), deriv c (z * u) * u ^ (-(radP α m)))
      = -(1 / z) * c z
        - ((-(radP α m)) / z)
            * (∫ u in Set.Ioi (1 : ℝ), c (z * u) * u ^ (-(radP α m) - 1)) := by
    rw [← hIBP]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with u
    rw [iteratedDeriv_one]
  have hode : z * (∫ u in Set.Ioi (1 : ℝ), deriv c (z * u) * u ^ (-(radP α m)))
      = radP α m * radPsi α m c z - c z := by
    rw [hIBP']
    rw [show radPsi α m c z
        = ∫ u in Set.Ioi (1 : ℝ), c (z * u) * u ^ (-(radP α m) - 1) from rfl]
    field_simp
    ring
  have hkey : (∫ u in Set.Ioi (1 : ℝ), deriv c (z * u) * u ^ (-(radP α m)))
      = (radP α m * radPsi α m c z - c z) / z := by
    rw [eq_div_iff (ne_of_gt hz), mul_comm]
    exact hode
  rwa [hkey] at hker'

/-- The base case for the formal-derivative recursion of `Ψ`. -/
lemma rpr_base {α : ℝ} (m : ℕ) {c : ℝ → ℝ} {K : ℝ} {N : ℕ}
    (hN : 1 ≤ N) (hK : 0 ≤ K) (hc : ContDiffOn ℝ N c (Set.Ioi 0))
    (hb : Work.FTS.PhiStar.BddDeriv N c K) (hp : 1 < radP α m) :
    ∀ z : ℝ, 0 < z → HasDerivAt (radPsi α m c) (psiF α m c 1 z) z := by
  intro z hz
  have h := rpr_deriv_value (α := α) m hN hK hc hb hp z hz
  rw [rpr_psiF_one]
  exact h

/-! ### The recursion -/

/-- From the base case, the formal derivatives `psiF j` really are the successive derivatives
of `Ψ`. -/
lemma rpr_psiF_hasDerivAt {α : ℝ} {m : ℕ} {c : ℝ → ℝ} {N : ℕ}
    (hc : ContDiffOn ℝ N c (Set.Ioi 0))
    (hbase : ∀ z : ℝ, 0 < z → HasDerivAt (radPsi α m c) (psiF α m c 1 z) z) :
    ∀ j : ℕ, j + 1 ≤ N → ∀ z : ℝ, 0 < z →
      HasDerivAt (psiF α m c j) (psiF α m c (j + 1) z) z := by
  intro j
  induction j with
  | zero =>
    intro _ z hz
    rw [psiF_zero]
    exact hbase z hz
  | succ j ih =>
    intro hj z hz
    show HasDerivAt (psiF α m c (j + 1)) (psiF α m c (j + 1 + 1) z) z
    have hjN : j + 1 ≤ N := by omega
    have hdF : HasDerivAt (psiF α m c j) (psiF α m c (j + 1) z) z := ih hjN z hz
    have hcderiv : HasDerivAt (iteratedDeriv j c) (iteratedDeriv (j + 1) c z) z :=
      rpr_hasDerivAt_iteratedDeriv (hc.contDiffAt (isOpen_Ioi.mem_nhds hz)) (by omega)
    have hnum : HasDerivAt
        (fun w : ℝ => (radP α m - (j : ℝ)) * psiF α m c j w - iteratedDeriv j c w)
        ((radP α m - (j : ℝ)) * psiF α m c (j + 1) z - iteratedDeriv (j + 1) c z) z :=
      (hdF.const_mul (radP α m - (j : ℝ))).sub hcderiv
    have hdiv := hnum.div (hasDerivAt_id z) (ne_of_gt hz)
    have hv : (((radP α m - (j : ℝ)) * psiF α m c (j + 1) z - iteratedDeriv (j + 1) c z) * z
          - ((radP α m - (j : ℝ)) * psiF α m c j z - iteratedDeriv j c z) * 1) / z ^ 2
        = psiF α m c (j + 1 + 1) z := by
      have hrec := psiF_rec (α := α) (m := m) (c := c) j (z := z) (ne_of_gt hz)
      rw [psiF_succ (α := α) (m := m) (c := c) (j + 1)]
      rw [← hrec]
      field_simp
      push_cast
      ring
    rw [psiF_succ (α := α) (m := m) (c := c) j, ← hv]
    exact hdiv

/-- The formal derivatives `psiF k` coincide with the true iterated derivatives of `Ψ`. -/
lemma rpr_iteratedDeriv_eq_psiF {α : ℝ} {m : ℕ} {c : ℝ → ℝ} {N : ℕ}
    (hc : ContDiffOn ℝ N c (Set.Ioi 0))
    (hbase : ∀ z : ℝ, 0 < z → HasDerivAt (radPsi α m c) (psiF α m c 1 z) z) :
    ∀ k : ℕ, k ≤ N → ∀ z : ℝ, 0 < z →
      iteratedDeriv k (radPsi α m c) z = psiF α m c k z := by
  have hsa := rpr_psiF_hasDerivAt (α := α) (m := m) (c := c) (N := N) hc hbase
  intro k
  induction k with
  | zero =>
    intro _ z _
    rw [psiF_zero]
    rfl
  | succ j ih =>
    intro hk z hz
    show iteratedDeriv (j + 1) (radPsi α m c) z = psiF α m c (j + 1) z
    have hjN : j + 1 ≤ N := by omega
    have hd := hsa j hjN z hz
    have hev : iteratedDeriv j (radPsi α m c) =ᶠ[𝓝 z] psiF α m c j := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with x hx
      exact ih (by omega) x hx
    rw [iteratedDeriv_succ, hev.deriv_eq, hd.deriv]

/-! ### The bounds -/

/-- The arithmetic of the bounding sequence: `Bnd p z₀ j ≤ 2 * M ^ j`. -/
lemma Bnd_le {p z₀ M : ℝ} {N : ℕ} (hp : 1 < p) (hz₀ : 0 < z₀) (hM : 1 ≤ M)
    (hMz : (p + (N : ℝ) + 1) / z₀ ≤ M) :
    ∀ j : ℕ, j ≤ N → Bnd p z₀ j ≤ 2 * M ^ j := by
  intro j
  induction j with
  | zero =>
    intro _
    show 1 / p ≤ 2 * M ^ 0
    rw [pow_zero]
    have h1 : 1 / p ≤ 1 := by
      rw [div_le_one (by linarith : (0 : ℝ) < p)]
      linarith
    linarith
  | succ j ih =>
    intro hj
    have hjN : j ≤ N := by omega
    have hMz' : p + (j : ℝ) + 1 ≤ M * z₀ := by
      have h1 : p + (N : ℝ) + 1 ≤ M * z₀ := (div_le_iff₀ hz₀).mp hMz
      have h2 : (j : ℝ) ≤ (N : ℝ) := by exact_mod_cast hjN
      linarith
    have hpj : (0 : ℝ) ≤ p + (j : ℝ) := by linarith
    have h1e : (1 : ℝ) ≤ M ^ j := one_le_pow₀ hM
    have h2e : (1 : ℝ) ≤ 2 * M ^ j := by linarith
    show ((p + (j : ℝ)) * Bnd p z₀ j + 1) / z₀ ≤ 2 * M ^ (j + 1)
    have ihb : Bnd p z₀ j ≤ 2 * M ^ j := ih hjN
    have step1 : (p + (j : ℝ)) * Bnd p z₀ j + 1 ≤ (p + (j : ℝ)) * (2 * M ^ j) + 1 := by
      have h := mul_le_mul_of_nonneg_left ihb hpj
      linarith
    have stepA : (p + (j : ℝ)) * (2 * M ^ j) + 1 ≤ 2 * M ^ j * (p + (j : ℝ) + 1) := by
      calc (p + (j : ℝ)) * (2 * M ^ j) + 1 ≤ (p + (j : ℝ)) * (2 * M ^ j) + 2 * M ^ j := by
            linarith
        _ = 2 * M ^ j * (p + (j : ℝ) + 1) := by ring
    have stepB : 2 * M ^ j * (p + (j : ℝ) + 1) ≤ 2 * M ^ j * (M * z₀) :=
      mul_le_mul_of_nonneg_left hMz' (by positivity)
    have stepC : 2 * M ^ j * (M * z₀) = 2 * M ^ (j + 1) * z₀ := by
      rw [pow_succ]
      ring
    rw [div_le_iff₀ hz₀]
    linarith

/-- The bound on the formal derivatives of `Ψ` in terms of the sequence `Bnd`. -/
lemma psiF_le_Bnd {α : ℝ} (m : ℕ) {c : ℝ → ℝ} {K : ℝ} {N : ℕ}
    (hK : 0 ≤ K) (hb : Work.FTS.PhiStar.BddDeriv N c K) (hp : 1 < radP α m) {z₀ : ℝ}
    (hz₀ : 0 < z₀) :
    ∀ j : ℕ, j ≤ N → ∀ z : ℝ, z₀ ≤ z → |psiF α m c j z| ≤ Bnd (radP α m) z₀ j * K := by
  intro j
  induction j with
  | zero =>
    intro _ z hz
    have hzpos : 0 < z := lt_of_lt_of_le hz₀ hz
    rw [psiF_zero]
    have hbb := rpr_base_bound (α := α) m (c := c) (K := K) (N := N) hK hb
      (lt_trans zero_lt_one hp) z hzpos
    calc |radPsi α m c z| ≤ K / radP α m := hbb
      _ = (1 / radP α m) * K := by ring
      _ = Bnd (radP α m) z₀ 0 * K := by rw [Bnd_zero]
  | succ j ih =>
    intro hj z hz
    have hjN : j ≤ N := by omega
    have hzpos : 0 < z := lt_of_lt_of_le hz₀ hz
    have hrec := psiF_rec (α := α) (m := m) (c := c) j (z := z) (ne_of_gt hzpos)
    have hval : psiF α m c (j + 1) z
        = ((radP α m - (j : ℝ)) * psiF α m c j z - iteratedDeriv j c z) / z := by
      rw [eq_div_iff (ne_of_gt hzpos), mul_comm]
      exact hrec
    rw [hval]
    have hnum : |(radP α m - (j : ℝ)) * psiF α m c j z - iteratedDeriv j c z|
        ≤ (radP α m + (j : ℝ)) * (Bnd (radP α m) z₀ j * K) + K := by
      have h1 : |(radP α m - (j : ℝ)) * psiF α m c j z - iteratedDeriv j c z|
          ≤ |(radP α m - (j : ℝ)) * psiF α m c j z| + |iteratedDeriv j c z| := by
        simpa only [sub_eq_add_neg, abs_neg] using
          abs_add_le ((radP α m - (j : ℝ)) * psiF α m c j z) (-(iteratedDeriv j c z))
      have habs : |radP α m - (j : ℝ)| ≤ radP α m + (j : ℝ) := by
        have hp0 : 0 < radP α m := lt_trans zero_lt_one hp
        have hj0 : (0 : ℝ) ≤ (j : ℝ) := by positivity
        rw [abs_le]
        constructor <;> linarith
      have hpsi_j : |psiF α m c j z| ≤ Bnd (radP α m) z₀ j * K := ih hjN z hz
      have h2 : |(radP α m - (j : ℝ)) * psiF α m c j z|
          ≤ (radP α m + (j : ℝ)) * (Bnd (radP α m) z₀ j * K) := by
        rw [abs_mul]
        refine mul_le_mul habs hpsi_j (abs_nonneg _) ?_
        have hp0 : 0 < radP α m := lt_trans zero_lt_one hp
        have hj0 : (0 : ℝ) ≤ (j : ℝ) := by positivity
        linarith
      have h3 : |iteratedDeriv j c z| ≤ K := hb j hjN z hzpos
      linarith
    have hbK : 0 ≤ (radP α m + (j : ℝ)) * (Bnd (radP α m) z₀ j * K) + K := by
      have hp0 : 0 < radP α m := lt_trans zero_lt_one hp
      have hj0 : (0 : ℝ) ≤ (j : ℝ) := by positivity
      have hbj := ih hjN z hz
      have h0 : 0 ≤ Bnd (radP α m) z₀ j * K := le_trans (abs_nonneg _) hbj
      nlinarith [hp0, hj0, h0, hK]
    calc |((radP α m - (j : ℝ)) * psiF α m c j z - iteratedDeriv j c z) / z|
        = |(radP α m - (j : ℝ)) * psiF α m c j z - iteratedDeriv j c z| / |z| := abs_div _ _
      _ = |(radP α m - (j : ℝ)) * psiF α m c j z - iteratedDeriv j c z| / z := by
            rw [abs_of_pos hzpos]
      _ ≤ ((radP α m + (j : ℝ)) * (Bnd (radP α m) z₀ j * K) + K) / z :=
            div_le_div_of_nonneg_right hnum hzpos.le
      _ ≤ ((radP α m + (j : ℝ)) * (Bnd (radP α m) z₀ j * K) + K) / z₀ :=
            div_le_div_of_nonneg_left hbK hz₀ hz
      _ = Bnd (radP α m) z₀ (j + 1) * K := by rw [Bnd_succ]; ring

/-- The ODE recursion bound for `radPsi`.  The proof template (order `22` only) is
`Submission/Work/FTS/PhiStar/RadialWAux/radPsi_recursion.lean`: define the formal derivatives
`F_0 = Ψ`, `F_{j+1} z = ((p - j) F_j z - c^{(j)} z)/z` (`p = radP α m`), show
`HasDerivAt (F_j) (F_{j+1} z) z` and `iteratedDeriv j Ψ z = F_j z` on `Ioi 0` (the base case
`z Ψ' = p Ψ - c` comes from differentiating `∫_{Ioi 1} c(zu)u^{-p-1}du` under the integral sign
and integrating `d/du(c(zu)u^{-p})` over `(1,∞)` by parts), and then propagate the bound
`B 0 = 1/p`, `B (j+1) = ((p + j) * B j + 1)/z₀`, which satisfies `B j ≤ 2 * M ^ j`. -/
theorem radPsi_rec {α : ℝ} (hα : 0 < α) (m : ℕ) (N : ℕ) {c : ℝ → ℝ} {K M z₀ : ℝ}
    (hK : 0 ≤ K) (hc : ContDiffOn ℝ N c (Set.Ioi 0)) (hb : Work.FTS.PhiStar.BddDeriv N c K)
    (hp : 1 < Work.FTS.PhiStar.RadialWAux.radP α m) (hz₀ : 0 < z₀) (hM : 1 ≤ M)
    (hMz : (Work.FTS.PhiStar.RadialWAux.radP α m + (N : ℝ) + 1) / z₀ ≤ M) :
    (∀ j : ℕ, j ≤ N → ∀ z : ℝ, z₀ ≤ z →
        |iteratedDeriv j (Work.FTS.PhiStar.RadialWAux.radPsi α m c) z| ≤ 2 * M ^ j * K)
    ∧ (∀ j : ℕ, j + 1 ≤ N → ∀ z : ℝ, 0 < z →
        HasDerivAt (iteratedDeriv j (Work.FTS.PhiStar.RadialWAux.radPsi α m c))
          (iteratedDeriv (j + 1) (Work.FTS.PhiStar.RadialWAux.radPsi α m c) z) z) := by
  have hbound := psiF_le_Bnd (α := α) (m := m) (c := c) (K := K) (N := N) hK hb hp hz₀
  have hB := Bnd_le (p := radP α m) (z₀ := z₀) (M := M) (N := N) hp hz₀ hM hMz
  by_cases hN1 : 1 ≤ N
  · have hbase := rpr_base (α := α) (m := m) (c := c) (K := K) (N := N) hN1 hK hc hb hp
    have hiter := rpr_iteratedDeriv_eq_psiF (α := α) (m := m) (c := c) (N := N) hc hbase
    have hder := rpr_psiF_hasDerivAt (α := α) (m := m) (c := c) (N := N) hc hbase
    refine ⟨?_, ?_⟩
    · intro j hj z hz
      have hzpos : 0 < z := lt_of_lt_of_le hz₀ hz
      calc |iteratedDeriv j (radPsi α m c) z| = |psiF α m c j z| := by rw [hiter j hj z hzpos]
        _ ≤ Bnd (radP α m) z₀ j * K := hbound j hj z hz
        _ ≤ 2 * M ^ j * K := mul_le_mul_of_nonneg_right (hB j hj) hK
    · intro j hj z hz
      have hjN : j ≤ N := by omega
      have h1 : HasDerivAt (psiF α m c j) (psiF α m c (j + 1) z) z := hder j hj z hz
      have hev : iteratedDeriv j (radPsi α m c) =ᶠ[𝓝 z] psiF α m c j := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with w hw
        exact hiter j hjN w hw
      have h2 : HasDerivAt (iteratedDeriv j (radPsi α m c)) (psiF α m c (j + 1) z) z :=
        h1.congr_of_eventuallyEq hev
      have h3 : psiF α m c (j + 1) z = iteratedDeriv (j + 1) (radPsi α m c) z :=
        (hiter (j + 1) hj z hz).symm
      rwa [h3] at h2
  · have hN0 : N = 0 := by omega
    subst hN0
    refine ⟨?_, ?_⟩
    · intro j hj z hz
      have hj0 : j = 0 := by omega
      subst hj0
      have h1 := hbound 0 (by omega) z hz
      rw [psiF_zero, Bnd_zero] at h1
      have h3 : 1 / radP α m ≤ 2 := by
        have h2 := hB 0 (by omega)
        rw [Bnd_zero, pow_zero] at h2
        linarith
      have h5 : (1 / radP α m) * K ≤ 2 * M ^ 0 * K := by
        rw [pow_zero]
        calc (1 / radP α m) * K ≤ 2 * K := mul_le_mul_of_nonneg_right h3 hK
          _ = 2 * 1 * K := by ring
      rw [iteratedDeriv_zero]
      exact le_trans h1 h5
    · intro j hj z hz
      exact absurd hj (by omega)

end Work.FTS.PhiStar.Series.SmoothAux.Deleg
end
end
-- ===== merged: Submission.Work.FTS.RegPkgGal.Der.hzmodp_ext =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.RegPkgGal.Der

set_option autoImplicit false


end Work.FTS.RegPkgGal.Der
end
-- ===== merged: Submission.Work.FTS.RegPkgGal.R4d.van_global =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open Set Filter Topology MeasureTheory
open scoped Topology Real

namespace Work.FTS.RegPkgGal.R4d

set_option autoImplicit false

/-! ## The slice calculus for the weaker smoothness hypothesis -/

/-- **Continuity of a slice at the left endpoint of `[a,b]`**, from the one-sided limit at `a`
from the right.  (`hcont0` of the statement is exactly such a limit.)  The proof splits
`𝓝[Ici a] a = 𝓝[Ioi a] a ⊔ pure a`: the first component is the hypothesis, the second is trivial
because `u` is *evaluated* at `a`. -/
lemma continuousWithinAt_Icc_of_tendsto_nhdsGT {u : ℝ → ℝ} {a b : ℝ}
    (ha : Tendsto u (𝓝[>] a) (𝓝 (u a))) : ContinuousWithinAt u (Set.Icc a b) a := by
  have hIci : ContinuousWithinAt u (Set.Ici a) a := by
    rw [ContinuousWithinAt, ← Set.Ioi_union_left, nhdsWithin_union, nhdsWithin_singleton,
        Filter.tendsto_sup]
    exact ⟨ha, tendsto_pure_nhds u a⟩
  exact hIci.mono_of_mem_nhdsWithin
    (Filter.mem_of_superset self_mem_nhdsWithin Set.Icc_subset_Ici_self)

/-- **Continuity of a slice at the right endpoint of `[a,b]`**, from the one-sided limit at `b`
from the left (the `hcontπ` of the statement). -/
lemma continuousWithinAt_Icc_of_tendsto_nhdsLT {u : ℝ → ℝ} {a b : ℝ}
    (hb : Tendsto u (𝓝[<] b) (𝓝 (u b))) : ContinuousWithinAt u (Set.Icc a b) b := by
  have hIic : ContinuousWithinAt u (Set.Iic b) b := by
    rw [ContinuousWithinAt, ← Set.Iio_union_right, nhdsWithin_union, nhdsWithin_singleton,
        Filter.tendsto_sup]
    exact ⟨hb, tendsto_pure_nhds u b⟩
  exact hIic.mono_of_mem_nhdsWithin
    (Filter.mem_of_superset self_mem_nhdsWithin Set.Icc_subset_Iic_self)

/-- **Continuity on `[a,b]`** from continuity at the two endpoints within `[a,b]` and at the
interior points. -/
lemma continuousOn_Icc_of_interior {u : ℝ → ℝ} {a b : ℝ}
    (hint : ∀ x ∈ Set.Ioo a b, ContinuousAt u x)
    (ha : ContinuousWithinAt u (Set.Icc a b) a)
    (hb : ContinuousWithinAt u (Set.Icc a b) b) :
    ContinuousOn u (Set.Icc a b) := by
  intro x hx
  rcases lt_or_eq_of_le hx.1 with hlt | rfl
  · rcases lt_or_eq_of_le hx.2 with hlt2 | rfl
    · exact (hint x ⟨hlt, hlt2⟩).continuousWithinAt
    · exact hb
  · exact ha

/-- **The angular fundamental theorem of calculus with a one-sided endpoint.**  If `u` is
continuous on `[a,b]` and differentiable on `(a,b)` with `‖u'‖ ≤ maj` there, `maj` being interval
integrable, then `|u b - u a| ≤ ∫_a^b maj`.  Unlike `R4b.slice_ftc_abs_le` this needs no
differentiability *at* the endpoints, so it applies to a slice that is only `C¹` on the open
quadrant and merely *continuous* up to `θ = 0` and `θ = π/2`. -/
lemma abs_sub_le_integral_of_continuousOn {u u' maj : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn u (Set.Icc a b))
    (hderiv : ∀ x ∈ Set.Ioo a b, HasDerivAt u (u' x) x)
    (hmaj_int : IntervalIntegrable maj volume a b)
    (hmaj : ∀ x ∈ Set.Ioo a b, ‖u' x‖ ≤ maj x) :
    |u b - u a| ≤ ∫ x in a..b, maj x := by
  have hb' : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ b := by
    rw [MeasureTheory.ae_iff]
    simp only [ne_eq, not_not, Set.ofPred_eq_eq_singleton]
    exact MeasureTheory.measure_singleton _
  have hae' : ∀ᵐ x ∂(volume.restrict (Set.Ioc a b)), deriv u x = u' x := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [hb'] with x hxb hx
    exact (hderiv x ⟨hx.1, lt_of_le_of_ne hx.2 hxb⟩).deriv
  have hae : ∀ᵐ x ∂(volume.restrict (Set.Ioc a b)), ‖u' x‖ ≤ maj x := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [hb'] with x hxb hx
    exact hmaj x ⟨hx.1, lt_of_le_of_ne hx.2 hxb⟩
  have hmeas : AEStronglyMeasurable u' (volume.restrict (Set.uIoc a b)) := by
    rw [Set.uIoc_of_le hab]
    exact (measurable_deriv u).aestronglyMeasurable.congr hae'
  have hint : IntervalIntegrable u' volume a b := by
    refine IntervalIntegrable.mono_fun' hmaj_int hmeas ?_
    rw [Set.uIoc_of_le hab]
    exact hae
  have hftc : ∫ x in a..b, u' x = u b - u a := by
    refine MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le u u' hab
      Set.countable_empty hc ?_ hint
    intro x hx
    exact hderiv x (by simpa using hx.1)
  have hle : ∫ x in a..b, ‖u' x‖ ≤ ∫ x in a..b, maj x := by
    rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
    refine MeasureTheory.integral_mono_ae ?_ ?_ hae
    · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hint.norm
    · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hmaj_int
  calc |u b - u a| = ‖∫ x in a..b, u' x‖ := by rw [hftc, Real.norm_eq_abs]
    _ ≤ ∫ x in a..b, ‖u' x‖ := intervalIntegral.norm_integral_le_integral_norm hab
    _ ≤ ∫ x in a..b, maj x := hle

/-! ## The analytic core: `|g| ≤ K·z²·Γ` on the whole half-line -/

/-- **The analytic core of R4d.**  From the `Γ`-bound on `D_θg`, the vanishing on the two angular
boundary lines, the one-sided continuity at the endpoints of the slices and the vanishing at
`z = 0`, the profile is dominated by `K·z²·Γ(θ)` on the whole half-line `z ≥ 0`, uniformly in
`τ ∈ [0,S]`.  This is `R4c.van_zsq` with the smoothness hypothesis weakened to the open quadrant
(the endpoint limits being assumed instead). -/
theorem van_zsq_weak {α S Cθ : ℝ} (hα : 0 < α) (hCθ : 0 ≤ Cθ)
    {g : ℝ → ℝ → ℝ → ℝ}
    (hsm : ∀ τ ∈ Set.Icc 0 S,
      ContDiffOn ℝ 1 (Function.uncurry (fun z θ => g z θ τ))
        (Set.prod (Set.Ioi (0:ℝ)) (Set.Ioo (0:ℝ) (Real.pi / 2))))
    (hquad0 : ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, g 0 θ τ = 0)
    (hcont0 : ∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ, 0 ≤ z →
      Filter.Tendsto (fun θ => g z θ τ) (nhdsWithin 0 (Set.Ioi (0:ℝ))) (nhds (g z 0 τ)))
    (hcontπ : ∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ, 0 ≤ z →
      Filter.Tendsto (fun θ => g z θ τ) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
        (nhds (g z (Real.pi / 2) τ)))
    (hd : ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |Work.Spaces.Dth (Work.FTS.Regularity.gSlice g τ) z θ|
        ≤ Cθ * z ^ 2 * Work.FTS.Regularity.Gamma α θ)
    (hvt : ∀ τ ∈ Set.Icc 0 S, Work.Spaces.VanishTheta (Work.FTS.Regularity.gSlice g τ)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |g z θ τ| ≤ K * z ^ 2 * Work.FTS.Regularity.Gamma α θ := by
  obtain ⟨M, hM0, hM⟩ := R4b.primBoundLeft hα
  obtain ⟨N, hN0, hN⟩ := R4b.primBoundRight hα
  set c1 : ℝ := (1 / Real.pi) ^ α with hc1
  set c2 : ℝ := ((Real.sqrt 2 / 2) * (2 / Real.pi) ^ 2) ^ α with hc2
  have hc1pos : 0 < c1 := by rw [hc1]; exact Real.rpow_pos_of_pos (by positivity) _
  have hc2pos : 0 < c2 := by rw [hc2]; exact Real.rpow_pos_of_pos (by positivity) _
  refine ⟨Cθ * max (M / (α * c1)) (N / (2 * α * c2)), ?_, ?_⟩
  · exact mul_nonneg hCθ (le_trans (div_nonneg hM0 (by positivity)) (le_max_left _ _))
  · intro τ hτ z θ hz hθ
    have hzsq : 0 ≤ z ^ 2 := sq_nonneg z
    rcases eq_or_lt_of_le hz with rfl | hzpos
    · rw [hquad0 τ hτ θ hθ]; simp
    rcases lt_or_eq_of_le hθ.1 with hθpos | hθzero
    · rcases lt_or_eq_of_le hθ.2 with hθlt | hθpi2
      · have hzmem : z ∈ Set.Ioi (0:ℝ) := hzpos
        have hslice : ∀ x ∈ Set.Ioo (0:ℝ) (Real.pi / 2),
            HasDerivAt (fun θ' => g z θ' τ)
              (Work.Spaces.pth (Work.FTS.Regularity.gSlice g τ) z x) x :=
          fun x hx => R4b.hasDerivAt_sliceTh isOpen_Ioi isOpen_Ioo (hsm τ hτ) hzmem hx
        rcases le_or_gt θ (Real.pi / 4) with hθle | hθgt
        · -- ## left half: `0 < θ ≤ π/4`, integrate from `0`
          have hθpi2lt : θ < Real.pi / 2 := lt_of_le_of_lt hθle (by linarith [Real.pi_pos])
          have hcontOn : ContinuousOn (fun θ' => g z θ' τ) (Set.Icc 0 θ) := by
            refine continuousOn_Icc_of_interior (fun x hx => ?_)
              (continuousWithinAt_Icc_of_tendsto_nhdsGT (hcont0 τ hτ z hz)) ?_
            · exact (hslice x ⟨hx.1, lt_trans hx.2 hθpi2lt⟩).continuousAt
            · exact (hslice θ ⟨hθpos, hθpi2lt⟩).continuousAt.continuousWithinAt
          have hmaj_int : IntervalIntegrable (fun x : ℝ => Cθ * z ^ 2 * M * x ^ (α - 1))
              volume 0 θ :=
            (intervalIntegral.intervalIntegrable_rpow' (show (-1:ℝ) < α - 1 by linarith)).const_mul _
          have hmaj : ∀ x ∈ Set.Ioo (0:ℝ) θ,
              ‖Work.Spaces.pth (Work.FTS.Regularity.gSlice g τ) z x‖
                ≤ Cθ * z ^ 2 * M * x ^ (α - 1) := by
            intro x hx
            rw [Real.norm_eq_abs]
            exact R4b.pth_le_majorant hCθ (hd τ hτ) hM hz hx.1
              (le_trans (le_of_lt hx.2) hθle)
          have hftc := abs_sub_le_integral_of_continuousOn hθ.1 hcontOn
            (fun x hx => hslice x ⟨hx.1, lt_trans hx.2 hθpi2lt⟩) hmaj_int hmaj
          have hval : ∫ x in (0:ℝ)..θ, Cθ * z ^ 2 * M * x ^ (α - 1)
              = Cθ * z ^ 2 * M * (θ ^ α / α) := by
            rw [intervalIntegral.integral_const_mul,
                integral_rpow (Or.inl (show (-1:ℝ) < α - 1 by linarith)),
                show α - 1 + 1 = α by ring, Real.zero_rpow (ne_of_gt hα), sub_zero]
          have hGam : c1 * θ ^ α ≤ Work.FTS.Regularity.Gamma α θ := by
            rw [hc1]; exact R4b.Gamma_left_lb hα hθpos.le hθle
          have hAc1 : θ ^ α * c1 ≤ Work.FTS.Regularity.Gamma α θ := by
            linarith [hGam, mul_comm c1 (θ ^ α)]
          have hΓ0 : 0 ≤ Work.FTS.Regularity.Gamma α θ :=
            Work.ConstructionInstance.Gamma_nonneg hθ
          have hquot : θ ^ α / α ≤ Work.FTS.Regularity.Gamma α θ / (α * c1) := by
            rw [div_le_iff₀ (by linarith : (0:ℝ) < α),
                show Work.FTS.Regularity.Gamma α θ / (α * c1) * α
                  = Work.FTS.Regularity.Gamma α θ * α / (α * c1) by ring,
                le_div_iff₀ (by positivity : (0:ℝ) < α * c1)]
            nlinarith [hAc1, hα, hc1pos]
          have hstep2 : M * (θ ^ α / α)
              ≤ (M / (α * c1)) * Work.FTS.Regularity.Gamma α θ := by
            have h1 := mul_le_mul_of_nonneg_left hquot hM0
            rwa [show M * (Work.FTS.Regularity.Gamma α θ / (α * c1))
                  = (M / (α * c1)) * Work.FTS.Regularity.Gamma α θ by ring] at h1
          have hstep3 : (M / (α * c1)) * Work.FTS.Regularity.Gamma α θ
              ≤ max (M / (α * c1)) (N / (2 * α * c2)) * Work.FTS.Regularity.Gamma α θ :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) hΓ0
          calc |g z θ τ| = |g z θ τ - g z 0 τ| := by
                  rw [show g z 0 τ = 0 from (hvt τ hτ).1 z, sub_zero]
            _ ≤ ∫ x in (0:ℝ)..θ, Cθ * z ^ 2 * M * x ^ (α - 1) := hftc
            _ = Cθ * z ^ 2 * M * (θ ^ α / α) := hval
            _ = Cθ * z ^ 2 * (M * (θ ^ α / α)) := by ring
            _ ≤ Cθ * z ^ 2 * ((M / (α * c1)) * Work.FTS.Regularity.Gamma α θ) :=
                  mul_le_mul_of_nonneg_left hstep2 (mul_nonneg hCθ hzsq)
            _ ≤ Cθ * z ^ 2 * (max (M / (α * c1)) (N / (2 * α * c2))
                  * Work.FTS.Regularity.Gamma α θ) :=
                  mul_le_mul_of_nonneg_left hstep3 (mul_nonneg hCθ hzsq)
            _ = Cθ * max (M / (α * c1)) (N / (2 * α * c2)) * z ^ 2
                  * Work.FTS.Regularity.Gamma α θ := by ring
        · -- ## right half: `π/4 < θ < π/2`, integrate up to `π/2`
          have hθpi2le : θ ≤ Real.pi / 2 := hθ.2
          have hcontOn : ContinuousOn (fun θ' => g z θ' τ) (Set.Icc θ (Real.pi / 2)) := by
            refine continuousOn_Icc_of_interior (fun x hx => ?_)
              ((hslice θ ⟨hθpos, hθlt⟩).continuousAt.continuousWithinAt)
              (continuousWithinAt_Icc_of_tendsto_nhdsLT (hcontπ τ hτ z hz))
            exact (hslice x ⟨lt_trans hθpos hx.1, hx.2⟩).continuousAt
          have hbase : IntervalIntegrable (fun x : ℝ => x ^ (2 * α - 1)) volume 0
              (Real.pi / 2 - θ) :=
            intervalIntegral.intervalIntegrable_rpow' (show (-1:ℝ) < 2 * α - 1 by linarith)
          have hcomp : IntervalIntegrable (fun x : ℝ => (Real.pi / 2 - x) ^ (2 * α - 1))
              volume (Real.pi / 2) θ := by
            have h' := hbase.comp_sub_left (Real.pi / 2)
            rw [sub_zero, show Real.pi / 2 - (Real.pi / 2 - θ) = θ by ring] at h'
            exact h'
          have hmaj_int : IntervalIntegrable
              (fun x : ℝ => Cθ * z ^ 2 * N * (Real.pi / 2 - x) ^ (2 * α - 1))
              volume θ (Real.pi / 2) :=
            (hcomp.symm).const_mul _
          have hmaj : ∀ x ∈ Set.Ioo θ (Real.pi / 2),
              ‖Work.Spaces.pth (Work.FTS.Regularity.gSlice g τ) z x‖
                ≤ Cθ * z ^ 2 * N * (Real.pi / 2 - x) ^ (2 * α - 1) := by
            intro x hx
            rw [Real.norm_eq_abs]
            exact R4b.pth_le_majorant_right hCθ (hd τ hτ) hN hz
              (le_of_lt (lt_trans hθgt hx.1)) hx.2
          have hftc := abs_sub_le_integral_of_continuousOn hθpi2le hcontOn
            (fun x hx => hslice x ⟨lt_trans hθpos hx.1, hx.2⟩) hmaj_int hmaj
          have hval : ∫ x in θ..(Real.pi / 2), Cθ * z ^ 2 * N * (Real.pi / 2 - x) ^ (2 * α - 1)
              = Cθ * z ^ 2 * N * ((Real.pi / 2 - θ) ^ (2 * α) / (2 * α)) := by
            rw [intervalIntegral.integral_const_mul]
            congr 1
            rw [intervalIntegral.integral_comp_sub_left (fun s : ℝ => s ^ (2 * α - 1))
                  (Real.pi / 2),
                show Real.pi / 2 - Real.pi / 2 = 0 by ring,
                integral_rpow (Or.inl (show (-1:ℝ) < 2 * α - 1 by linarith)),
                show 2 * α - 1 + 1 = 2 * α by ring,
                Real.zero_rpow (by linarith : 2 * α ≠ 0), sub_zero]
          have hσ0 : 0 ≤ Real.pi / 2 - θ := by linarith [hθpi2le]
          have hσle : Real.pi / 2 - θ ≤ Real.pi / 4 := by linarith [hθgt]
          have hGam : c2 * (Real.pi / 2 - θ) ^ (2 * α) ≤ Work.FTS.Regularity.Gamma α θ := by
            have h := R4b.Gamma_right_lb hα hσ0 hσle
            rwa [show Real.pi / 2 - (Real.pi / 2 - θ) = θ by ring] at h
          have hAc2 : (Real.pi / 2 - θ) ^ (2 * α) * c2 ≤ Work.FTS.Regularity.Gamma α θ := by
            linarith [hGam, mul_comm c2 ((Real.pi / 2 - θ) ^ (2 * α))]
          have hΓ0 : 0 ≤ Work.FTS.Regularity.Gamma α θ :=
            Work.ConstructionInstance.Gamma_nonneg hθ
          have hquot : (Real.pi / 2 - θ) ^ (2 * α) / (2 * α)
              ≤ Work.FTS.Regularity.Gamma α θ / (2 * α * c2) := by
            rw [div_le_iff₀ (by linarith : (0:ℝ) < 2 * α),
                show Work.FTS.Regularity.Gamma α θ / (2 * α * c2) * (2 * α)
                  = Work.FTS.Regularity.Gamma α θ * (2 * α) / (2 * α * c2) by ring,
                le_div_iff₀ (by positivity : (0:ℝ) < 2 * α * c2)]
            nlinarith [hAc2, hα, hc2pos]
          have hstep2 : N * ((Real.pi / 2 - θ) ^ (2 * α) / (2 * α))
              ≤ (N / (2 * α * c2)) * Work.FTS.Regularity.Gamma α θ := by
            have h1 := mul_le_mul_of_nonneg_left hquot hN0
            rwa [show N * (Work.FTS.Regularity.Gamma α θ / (2 * α * c2))
                  = (N / (2 * α * c2)) * Work.FTS.Regularity.Gamma α θ by ring] at h1
          have hstep3 : (N / (2 * α * c2)) * Work.FTS.Regularity.Gamma α θ
              ≤ max (M / (α * c1)) (N / (2 * α * c2)) * Work.FTS.Regularity.Gamma α θ :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) hΓ0
          calc |g z θ τ| = |g z (Real.pi / 2) τ - g z θ τ| := by
                  rw [show g z (Real.pi / 2) τ = 0 from (hvt τ hτ).2 z, zero_sub, abs_neg]
            _ ≤ ∫ x in θ..(Real.pi / 2), Cθ * z ^ 2 * N * (Real.pi / 2 - x) ^ (2 * α - 1) := hftc
            _ = Cθ * z ^ 2 * N * ((Real.pi / 2 - θ) ^ (2 * α) / (2 * α)) := hval
            _ = Cθ * z ^ 2 * (N * ((Real.pi / 2 - θ) ^ (2 * α) / (2 * α))) := by ring
            _ ≤ Cθ * z ^ 2 * ((N / (2 * α * c2)) * Work.FTS.Regularity.Gamma α θ) :=
                  mul_le_mul_of_nonneg_left hstep2 (mul_nonneg hCθ hzsq)
            _ ≤ Cθ * z ^ 2 * (max (M / (α * c1)) (N / (2 * α * c2))
                  * Work.FTS.Regularity.Gamma α θ) :=
                  mul_le_mul_of_nonneg_left hstep3 (mul_nonneg hCθ hzsq)
            _ = Cθ * max (M / (α * c1)) (N / (2 * α * c2)) * z ^ 2
                  * Work.FTS.Regularity.Gamma α θ := by ring
      · -- ## the degenerate case `θ = π/2`: `Γ(π/2) = 0 = g`
        rw [hθpi2, show g z (Real.pi / 2) τ = 0 from (hvt τ hτ).2 z]
        simp [Work.FTS.Regularity.Gamma, Work.ConstructionInstance.Gamma,
          Real.zero_rpow (ne_of_gt hα)]
    · -- ## the degenerate case `θ = 0`: `Γ(0) = 0 = g`
      rw [← hθzero, show g z 0 τ = 0 from (hvt τ hτ).1 z]
      simp [Work.FTS.Regularity.Gamma, Work.ConstructionInstance.Gamma,
        Real.zero_rpow (ne_of_gt hα)]

/-! ## R4d -/

/-- **The class lemma R4d.**  On a strip `τ ∈ [0,S]`, a family `g` whose angular derivative
satisfies the `Γ`-bound `|D_θ g| = |sin(2θ)∂_θ g| ≤ Cθ·z²·Γ(θ)`, which vanishes on the two angular
boundary lines (`VanishTheta`) *and* has continuous slices up to those lines (`hcont0`, `hcontπ`),
and which satisfies the far-field bound `|g z θ τ| ≤ Lz·Γ(θ)` for `z ≥ Lz`, is dominated by `Γ` on
the whole half-line `z ≥ 0`. -/
theorem van_global {α S Cθ Lz : ℝ} (hα : 0 < α) (hS : 0 < S) (hCθ : 0 ≤ Cθ) (hLz : 0 ≤ Lz)
    {g : ℝ → ℝ → ℝ → ℝ}
    (hsm : ∀ τ ∈ Set.Icc 0 S,
      ContDiffOn ℝ 1 (Function.uncurry (fun z θ => g z θ τ))
        (Set.prod (Set.Ioi (0:ℝ)) (Set.Ioo (0:ℝ) (Real.pi / 2))))
    (hquad0 : ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, g 0 θ τ = 0)
    (hcont0 : ∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ, 0 ≤ z →
      Filter.Tendsto (fun θ => g z θ τ) (nhdsWithin 0 (Set.Ioi (0:ℝ))) (nhds (g z 0 τ)))
    (hcontπ : ∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ, 0 ≤ z →
      Filter.Tendsto (fun θ => g z θ τ) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
        (nhds (g z (Real.pi / 2) τ)))
    (hd : ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |Work.Spaces.Dth (Work.FTS.Regularity.gSlice g τ) z θ|
        ≤ Cθ * z ^ 2 * Work.FTS.Regularity.Gamma α θ)
    (hvt : ∀ τ ∈ Set.Icc 0 S, Work.Spaces.VanishTheta (Work.FTS.Regularity.gSlice g τ))
    (hfar : ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, Lz ≤ z → θ ∈ Work.Spaces.Iθ →
      |g z θ τ| ≤ Lz * Work.FTS.Regularity.Gamma α θ) :
    ∃ Cv : ℝ, 0 ≤ Cv ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |g z θ τ| ≤ Cv * Work.FTS.Regularity.Gamma α θ := by
  obtain ⟨K, hK0, hzsq⟩ := van_zsq_weak hα hCθ hsm hquad0 hcont0 hcontπ hd hvt
  exact R4c.van_global_of_zsq hLz hK0 hzsq hfar

end Work.FTS.RegPkgGal.R4d
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.RowMuAux.sg_fk_open_rows =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux.RowMuAux

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

open Work.FTS.Galerkin (Fn)
open Work.FTS.Nonlinear.Pieces (Fa)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## The explicit profile coefficient -/

/-- `|FK (F_*) r| ≤ α/2` for `0 < α ≤ 1`, `r > 0` (the profile `FK (F_*) = α·2r/(1+r)²` is
maximal at `r = 1`, where it equals `α/2`). -/
theorem abs_FK_Fstar_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {r : ℝ} (hr : 0 < r) :
    |Work.Construction.FK (Work.Construction.Fstar α) r| ≤ α / 2 := by
  rw [Work.FTS.NonlinRows.Rl1.FK_Fstar_pt hα hα1]
  have h1 : (0 : ℝ) ≤ 2 * r / (1 + r) ^ 2 := div_nonneg (by linarith) (by positivity)
  rw [abs_mul, abs_of_nonneg hα.le, abs_of_nonneg h1]
  have h2 : 2 * r / (1 + r) ^ 2 ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg (1 - r)]
  nlinarith [h2, hα.le]

/-! ## Row `N₄^{sg} = -(1/2)·FK (F_*)·D_θf` -/

/-- **Row `N₄^{sg}` in the open class**, with the explicit constant `3√(π/2)`:
`Fa (N₄^{sg} α f) ≤ ofReal (3√(π/2)·α·|f|_{ℋ⁴})`. -/
theorem row4sg_open {α : ℝ} {f : Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hso : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f) :
    Fa (Work.FTS.Nonlin.N4sg α f)
      ≤ ENNReal.ofReal (3 * Real.sqrt (Real.pi / 2)
          * (α * Work.FTS.Nonlin.Xn α f)) := by
  have hcontD : ContinuousOn (Function.uncurry (Work.Spaces.Dth f))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := hso.Dth.continuousOn
  have hmain := Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux.rl1_slot_le
    (α := α) (C := 3 * α) (g := f)
    (A := fun z _ => -(1 / 2) * Work.Construction.FK (Work.Construction.Fstar α) z)
    (B := Work.Spaces.Dth f)
    (by positivity) hmem
    (fun r hr => Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux.ae_Iθ_of_forall_Ioo fun θ hθ => by
      have hK : |Work.Spaces.K θ| ≤ 3 := Work.FTS.NonlinRows.Rl1.K_abs_le_three' hθ
      have h1 : |Work.Spaces.K θ * (-(1 / 2)
            * Work.Construction.FK (Work.Construction.Fstar α) r)|
          = |Work.Spaces.K θ| * (1 / 2)
            * |Work.Construction.FK (Work.Construction.Fstar α) r| := by
        simp only [abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (1 / 2))]
        ring
      rw [h1]
      have h3 : |Work.Spaces.K θ| * (1 / 2)
          * |Work.Construction.FK (Work.Construction.Fstar α) r| ≤ 3 * (1 / 2) * (α / 2) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hK (by norm_num))
          (abs_FK_Fstar_le hα hα1 hr) (abs_nonneg _) (by norm_num)
      refine h3.trans ?_
      nlinarith [hα.le])
    (fun r hr => Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux.slice_sq_aemeasurable hcontD hr)
    (Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux.slot_aemeasurable hcontD)
    (fun r hr => Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux.ae_Iθ_of_forall_Ioo fun θ hθ =>
      Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux.slot_dth hα hr hθ f)
  have hid : Work.FTS.Nonlin.N4sg α f
      = fun r θ => (-(1 / 2) * Work.Construction.FK (Work.Construction.Fstar α) r)
          * Work.Spaces.Dth f r θ := by
    funext r θ
    simp only [Work.FTS.Nonlin.N4sg]
  rw [hid, Work.FTS.NonlinRows.Rl1.Fa_mul_eq (A := fun z _ =>
      -(1 / 2) * Work.Construction.FK (Work.Construction.Fstar α) z)
    (B := Work.Spaces.Dth f)]
  refine hmain.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
  ring

/-! ## Row `N₅^{sg} = -sin²θ·FK (F_*)·f` -/

/-- **Row `N₅^{sg}` in the open class**, with the explicit constant `6√(π/2)`:
`Fa (N₅^{sg} α f) ≤ ofReal (6√(π/2)·α·|f|_{ℋ⁴})`. -/
theorem row5sg_open {α : ℝ} {f : Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hso : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f) :
    Fa (Work.FTS.Nonlin.N5sg α f)
      ≤ ENNReal.ofReal (6 * Real.sqrt (Real.pi / 2)
          * (α * Work.FTS.Nonlin.Xn α f)) := by
  have hcont : ContinuousOn (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    hso.continuousOn
  have hmain := Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux.rl1_slot_le
    (α := α) (C := 6 * α) (g := f)
    (A := fun z θ => -(Real.sin θ) ^ 2
      * Work.Construction.FK (Work.Construction.Fstar α) z)
    (B := f)
    (by positivity) hmem
    (fun r hr => Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux.ae_Iθ_of_forall_Ioo fun θ hθ => by
      have hK : |Work.Spaces.K θ| ≤ 3 := Work.FTS.NonlinRows.Rl1.K_abs_le_three' hθ
      have hsin : (Real.sin θ) ^ 2 ≤ 1 := by
        nlinarith [Real.neg_one_le_sin θ, Real.sin_le_one θ]
      have h1 : |Work.Spaces.K θ * (-(Real.sin θ) ^ 2
            * Work.Construction.FK (Work.Construction.Fstar α) r)|
          = |Work.Spaces.K θ| * (Real.sin θ) ^ 2
            * |Work.Construction.FK (Work.Construction.Fstar α) r| := by
        simp only [abs_mul, abs_neg, abs_of_nonneg (sq_nonneg (Real.sin θ))]
        ring
      rw [h1]
      have h3 : |Work.Spaces.K θ| * (Real.sin θ) ^ 2
          * |Work.Construction.FK (Work.Construction.Fstar α) r| ≤ 3 * 1 * (α / 2) :=
        mul_le_mul (mul_le_mul hK hsin (sq_nonneg _) (by norm_num))
          (abs_FK_Fstar_le hα hα1 hr) (abs_nonneg _) (by norm_num)
      exact h3.trans (by nlinarith [hα.le]))
    (fun r hr => Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux.slice_sq_aemeasurable hcont hr)
    (Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux.slot_aemeasurable hcont)
    (fun r hr => Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux.ae_Iθ_of_forall_Ioo fun θ hθ =>
      Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux.slot_g hα hr hθ f)
  have hid : Work.FTS.Nonlin.N5sg α f
      = fun r θ => (-(Real.sin θ) ^ 2
          * Work.Construction.FK (Work.Construction.Fstar α) r) * f r θ := by
    funext r θ
    simp only [Work.FTS.Nonlin.N5sg]
  rw [hid, Work.FTS.NonlinRows.Rl1.Fa_mul_eq (A := fun z θ =>
      -(Real.sin θ) ^ 2 * Work.Construction.FK (Work.Construction.Fstar α) z) (B := f)]
  refine hmain.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
  ring

/-! ## Assembly -/

/-- **Rows `N₄^{sg}`, `N₅^{sg}` in the open class, against `Env`.**  The existential constant
`6√(π/2) + 1` works because `α·|f|_{ℋ⁴} ≤ Env α f` (`alpha_mul_Xn_le_Env`). -/
theorem sg_fk_open_rows : ∃ K : ℝ, 0 < K ∧
    ∀ {α : ℝ} {f : Work.FTS.Galerkin.Fn},
      0 < α → α ≤ 1 → Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
      Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N4sg α f)
        ≤ ENNReal.ofReal (K * Work.FTS.NonlinRows.Rl1.Env α f) ∧
      Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N5sg α f)
        ≤ ENNReal.ofReal (K * Work.FTS.NonlinRows.Rl1.Env α f) := by
  refine ⟨6 * Real.sqrt (Real.pi / 2) + 1, by positivity, ?_⟩
  intro α f hα hα1 hso hmem
  have hEnvn : 0 ≤ Work.FTS.NonlinRows.Rl1.Env α f :=
    Work.FTS.NonlinRows.Rl1.Env_nonneg f hα.le
  have hαX : α * Work.FTS.Nonlin.Xn α f ≤ Work.FTS.NonlinRows.Rl1.Env α f :=
    Work.FTS.NonlinRows.Rl1.alpha_mul_Xn_le_Env (g := f) hα hα1
  have hsv : (0 : ℝ) ≤ Real.sqrt (Real.pi / 2) := Real.sqrt_nonneg _
  have hK3 : 3 * Real.sqrt (Real.pi / 2) ≤ 6 * Real.sqrt (Real.pi / 2) + 1 := by
    nlinarith [hsv]
  have hK6 : 6 * Real.sqrt (Real.pi / 2) ≤ 6 * Real.sqrt (Real.pi / 2) + 1 := by
    linarith
  have key : ∀ c : ℝ, 0 ≤ c → c ≤ 6 * Real.sqrt (Real.pi / 2) + 1 →
      c * (α * Work.FTS.Nonlin.Xn α f)
        ≤ (6 * Real.sqrt (Real.pi / 2) + 1) * Work.FTS.NonlinRows.Rl1.Env α f := by
    intro c hc0 hcle
    have h1 : c * (α * Work.FTS.Nonlin.Xn α f) ≤ c * Work.FTS.NonlinRows.Rl1.Env α f :=
      mul_le_mul_of_nonneg_left hαX hc0
    have h2 : c * Work.FTS.NonlinRows.Rl1.Env α f
        ≤ (6 * Real.sqrt (Real.pi / 2) + 1) * Work.FTS.NonlinRows.Rl1.Env α f :=
      mul_le_mul_of_nonneg_right hcle hEnvn
    exact h1.trans h2
  constructor
  · refine (row4sg_open hα hα1 hso hmem).trans (ENNReal.ofReal_le_ofReal ?_)
    exact key (3 * Real.sqrt (Real.pi / 2)) (by positivity) hK3
  · refine (row5sg_open hα hα1 hso hmem).trans (ENNReal.ofReal_le_ofReal ?_)
    exact key (6 * Real.sqrt (Real.pi / 2)) (by positivity) hK6

end

end Work.FTS.StrongPersist.H6Pair6Aux.RowMuAux
end
-- ===== merged: Submission.Work.FTS_RegExport.RX0.sup2_extG_ext_hIS =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open Set MeasureTheory Filter

namespace Work.FTS_RegExport.RX0

set_option autoImplicit false

/-! ## Helpers -/

/-- **Congruence of `∂_z²` between the extension slice and the slice of `g`.**  For `τ ≥ 0` the
two functions `z' ↦ extG g z' θ τ` and `z' ↦ g z' θ τ` agree on the open half line `Ioi 0`
(`extG_of_pos`), and `pz` is a local operator, so their second `z`-derivatives agree at every
`z > 0`. -/
private lemma pz_pz_extG_eq {g : ℝ → ℝ → ℝ → ℝ} {τ z θ : ℝ} (hτ : 0 ≤ τ) (hz : 0 < z) :
    Work.Spaces.pz (Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ)) z θ
      = Work.Spaces.pz (Work.Spaces.pz (fun z θ => g z θ τ)) z θ := by
  have hV : IsOpen (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ
  have hagree : EqOn (Function.uncurry (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ))
      (Function.uncurry (fun z θ => g z θ τ)) (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ)) := by
    rintro ⟨z', θ'⟩ ⟨hz', -⟩
    exact Work.FTS.RegPkgGal.extG_of_pos hz' hτ
  have h1 : EqOn (Function.uncurry (Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ)))
      (Function.uncurry (Work.Spaces.pz (fun z θ => g z θ τ)))
      (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ)) := by
    intro y hy
    exact Work.Spaces.pz_congr_of_isOpen hV hagree hy
  exact Work.Spaces.pz_congr_of_isOpen hV h1 ⟨hz, trivial⟩

/-- **The bridge `D_z² = D_z + z²∂_z²`.**  If the `z`-slice of `pz F` is differentiable at `z`,
then `D_z²F = D_zF + z²∂_z²F` at `(z,θ)`.  (The `n = 2` case of the expansion of `D_z = z∂_z` in
powers of `z^k∂_z^k`, with the Stirling coefficients `S(2,1) = S(2,2) = 1`; only the product rule
is used, so no higher smoothness is required.) -/
private lemma DzIter_two_eq_add (F : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hd : DifferentiableAt ℝ (fun z' => Work.Spaces.pz F z' θ) z) :
    Work.Spaces.DzIter 2 F z θ
      = Work.Spaces.DzIter 1 F z θ + z ^ 2 * Work.Spaces.pz (Work.Spaces.pz F) z θ := by
  have hdmul : deriv (fun z' : ℝ => z' * Work.Spaces.pz F z' θ) z
      = Work.Spaces.pz F z θ + z * Work.Spaces.pz (Work.Spaces.pz F) z θ := by
    have h1 : HasDerivAt (fun z' : ℝ => z') (1 : ℝ) z := hasDerivAt_id' z
    have h2 : HasDerivAt (fun z' : ℝ => Work.Spaces.pz F z' θ)
        (Work.Spaces.pz (Work.Spaces.pz F) z θ) z := hd.hasDerivAt
    have h3 : HasDerivAt (fun z' : ℝ => z' * Work.Spaces.pz F z' θ)
        (1 * Work.Spaces.pz F z θ + z * Work.Spaces.pz (Work.Spaces.pz F) z θ) z :=
      (h1.mul h2).congr_of_eventuallyEq (Filter.EventuallyEq.of_eq (by funext z'; rfl))
    simpa only [one_mul] using h3.deriv
  show z * deriv (fun z' : ℝ => z' * Work.Spaces.pz F z' θ) z
      = z * Work.Spaces.pz F z θ + z ^ 2 * Work.Spaces.pz (Work.Spaces.pz F) z θ
  rw [hdmul]
  ring

/-- **Differentiability of the `∂_z`-slice from `C⁴` on the open quadrant.**  If `F` is `C⁴` on
`Q0 = (0,∞) × (0,π/2)` then the `z`-slice `z' ↦ ∂_zF(z',θ)` is differentiable at every `z > 0`
and interior angle: the slice of `F` is `C⁴` on `Ioi 0` (compose with the smooth injection
`z ↦ (z,θ)`), so its `deriv` is `C³`, hence differentiable. -/
private lemma contDiffOn_pz_slice_four {F : ℝ → ℝ → ℝ} {θ z : ℝ}
    (hc4 : ContDiffOn ℝ 4 (Function.uncurry F) Work.FTS.EllipticEst.Q0)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) (hz : z ∈ Set.Ioi (0 : ℝ)) :
    DifferentiableAt ℝ (fun z' => Work.Spaces.pz F z' θ) z := by
  have hsl : ContDiffOn ℝ 4 (fun z' : ℝ => F z' θ) (Set.Ioi (0 : ℝ)) := by
    have hp : ContDiffOn ℝ 4 (fun z : ℝ => (z, θ)) (Set.Ioi (0 : ℝ)) := by fun_prop
    have h2 := hc4.comp hp (fun z hz => ⟨hz, hθ.1, hθ.2⟩)
    simpa [Function.comp_def, Function.uncurry] using h2
  have hder : ContDiffOn ℝ 3 (deriv (fun z' : ℝ => F z' θ)) (Set.Ioi (0 : ℝ)) :=
    hsl.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hfun : (fun z' : ℝ => Work.Spaces.pz F z' θ) = deriv (fun z' : ℝ => F z' θ) := by
    funext z'; rfl
  rw [hfun]
  exact (hder.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioi.mem_nhds hz)

/-! ## The target -/

theorem sup2_extG_ext_hIS {α S : ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (hα : 0 < α) (hS : 0 < S)
    (hIS : ∃ M : ℝ, 0 ≤ M ∧ ∀ τ ∈ Set.Icc 0 S, ∀ b a : ℕ, a + b ≤ 2 → ∀ z θ : ℝ,
      0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed b a (Work.FTS.Regularity.gSlice g τ) z θ| ≤ M)
    (hc4 : ∀ τ ∈ Set.Icc 0 S, ContDiffOn ℝ 4
      (Function.uncurry (Work.FTS.Regularity.gSlice g τ)) Work.FTS.EllipticEst.Q0)
    (hvan : ∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ, 0 ≤ z → g z 0 τ = 0 ∧ g z (Real.pi / 2) τ = 0)
    (hq2 : ∃ Q₂ : ℝ, 0 ≤ Q₂ ∧ ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z : ℝ,
      0 < z → z ≤ 2 →
      |Work.Spaces.pz (Work.Spaces.pz
        (Work.FTS.Regularity.gSlice (Work.FTS.RegPkgGal.extG g) τ)) z θ| ≤ Q₂) :
    ∃ M₂ : ℝ, 0 ≤ M₂ ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 < z → θ ∈ Work.Spaces.Iθ →
      |Work.Spaces.pz (Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ)) z θ| ≤ M₂ := by
  obtain ⟨M, hM0, hM⟩ := hIS
  obtain ⟨Q₂, hQ₂0, hQ₂bd⟩ := hq2
  refine ⟨max Q₂ M, le_trans hQ₂0 (le_max_left _ _), ?_⟩
  intro τ hτ z θ hz hθI
  rcases lt_or_eq_of_le hθI.1 with hθpos | hθzero
  · rcases lt_or_eq_of_le hθI.2 with hθlt | hθtop
    · -- the interior angle: `hq2` for `z ≤ 2`, the `hIS` bound for `z > 2`
      rcases le_or_gt z 2 with hz2 | hz2
      · exact le_trans (hQ₂bd τ hτ θ hθI z hz hz2) (le_max_left _ _)
      · -- the extension slice agrees with the `g`-slice on `Ioi 0`
        have hcongr :
            Work.Spaces.pz (Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ)) z θ
              = Work.Spaces.pz (Work.Spaces.pz (fun z θ => g z θ τ)) z θ :=
          pz_pz_extG_eq hτ.1 hz
        rw [hcongr]
        -- the two `hIS` slots of order `≤ 2`
        have hm2 : |Work.Spaces.mixed 2 0 (Work.FTS.Regularity.gSlice g τ) z θ| ≤ M :=
          hM τ hτ 2 0 (by norm_num) z θ hz hθpos hθlt
        have hm1 : |Work.Spaces.mixed 1 0 (Work.FTS.Regularity.gSlice g τ) z θ| ≤ M :=
          hM τ hτ 1 0 (by norm_num) z θ hz hθpos hθlt
        simp only [Work.Spaces.mixed_zero_right] at hm2 hm1
        have hdiff : DifferentiableAt ℝ
            (fun z' => Work.Spaces.pz (Work.FTS.Regularity.gSlice g τ) z' θ) z :=
          contDiffOn_pz_slice_four (hc4 τ hτ) ⟨hθpos, hθlt⟩ hz
        have hid := DzIter_two_eq_add (Work.FTS.Regularity.gSlice g τ) hdiff
        have hmul : z ^ 2 * Work.Spaces.pz (Work.Spaces.pz (Work.FTS.Regularity.gSlice g τ)) z θ
            = Work.Spaces.DzIter 2 (Work.FTS.Regularity.gSlice g τ) z θ
              - Work.Spaces.DzIter 1 (Work.FTS.Regularity.gSlice g τ) z θ := by
          linarith [hid]
        have hz2' : (4 : ℝ) ≤ z ^ 2 := by nlinarith
        have hstep :
            z ^ 2 * |Work.Spaces.pz (Work.Spaces.pz (Work.FTS.Regularity.gSlice g τ)) z θ|
              ≤ 2 * M := by
          rw [← abs_of_pos (by positivity : (0 : ℝ) < z ^ 2), ← abs_mul, hmul]
          calc |Work.Spaces.DzIter 2 (Work.FTS.Regularity.gSlice g τ) z θ
                - Work.Spaces.DzIter 1 (Work.FTS.Regularity.gSlice g τ) z θ|
              = |Work.Spaces.DzIter 2 (Work.FTS.Regularity.gSlice g τ) z θ
                  + (-Work.Spaces.DzIter 1 (Work.FTS.Regularity.gSlice g τ) z θ)| := by
                ring_nf
            _ ≤ |Work.Spaces.DzIter 2 (Work.FTS.Regularity.gSlice g τ) z θ|
                  + |-Work.Spaces.DzIter 1 (Work.FTS.Regularity.gSlice g τ) z θ| :=
                abs_add_le _ _
            _ = |Work.Spaces.DzIter 2 (Work.FTS.Regularity.gSlice g τ) z θ|
                  + |Work.Spaces.DzIter 1 (Work.FTS.Regularity.gSlice g τ) z θ| := by
                rw [abs_neg]
            _ ≤ 2 * M := by linarith
        have hfin : |Work.Spaces.pz (Work.Spaces.pz (Work.FTS.Regularity.gSlice g τ)) z θ|
            ≤ M := by
          have h4 : 4 * |Work.Spaces.pz (Work.Spaces.pz (Work.FTS.Regularity.gSlice g τ)) z θ|
              ≤ z ^ 2 * |Work.Spaces.pz (Work.Spaces.pz (Work.FTS.Regularity.gSlice g τ)) z θ| :=
            mul_le_mul_of_nonneg_right hz2' (abs_nonneg _)
          nlinarith [le_trans h4 hstep,
            abs_nonneg (Work.Spaces.pz (Work.Spaces.pz (Work.FTS.Regularity.gSlice g τ)) z θ)]
        exact le_trans hfin (le_max_right _ _)
    · -- the angle `θ = π/2`: the extension slice is identically zero in `z`
      have hzero : (fun z' : ℝ => Work.FTS.RegPkgGal.extG g z' θ τ) = fun _ => (0 : ℝ) := by
        funext z'
        rcases le_or_gt z' 0 with hz' | hz'
        · exact Work.FTS.RegPkgGal.extG_of_nonpos hz'
        · rw [Work.FTS.RegPkgGal.extG_of_pos hz' hτ.1, hθtop]
          exact (hvan τ hτ z' hz'.le).2
      have hpz0 : ∀ z' : ℝ,
          Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ) z' θ = 0 := by
        intro z'
        show deriv (fun z'' => Work.FTS.RegPkgGal.extG g z'' θ τ) z' = 0
        rw [hzero, deriv_const]
      have hpp : Work.Spaces.pz (Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ))
          z θ = 0 := by
        show deriv (fun z' => Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ) z' θ) z
          = 0
        rw [show (fun z' => Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ) z' θ)
            = fun _ => (0 : ℝ) from funext hpz0, deriv_const]
      rw [hpp, abs_zero]
      exact le_trans hQ₂0 (le_max_left _ _)
  · -- the angle `θ = 0`: the extension slice is identically zero in `z`
    have hθ0 : θ = 0 := hθzero.symm
    have hzero : (fun z' : ℝ => Work.FTS.RegPkgGal.extG g z' θ τ) = fun _ => (0 : ℝ) := by
      funext z'
      rcases le_or_gt z' 0 with hz' | hz'
      · exact Work.FTS.RegPkgGal.extG_of_nonpos hz'
      · rw [Work.FTS.RegPkgGal.extG_of_pos hz' hτ.1, hθ0]
        exact (hvan τ hτ z' hz'.le).1
    have hpz0 : ∀ z' : ℝ,
        Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ) z' θ = 0 := by
      intro z'
      show deriv (fun z'' => Work.FTS.RegPkgGal.extG g z'' θ τ) z' = 0
      rw [hzero, deriv_const]
    have hpp : Work.Spaces.pz (Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ))
        z θ = 0 := by
      show deriv (fun z' => Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ) z' θ) z
        = 0
      rw [show (fun z' => Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ) z' θ)
          = fun _ => (0 : ℝ) from funext hpz0, deriv_const]
    rw [hpp, abs_zero]
    exact le_trans hQ₂0 (le_max_left _ _)

end Work.FTS_RegExport.RX0
end
