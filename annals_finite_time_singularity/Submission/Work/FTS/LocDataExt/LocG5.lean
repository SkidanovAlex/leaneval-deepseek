import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.H2W.Slot01W.BslZsq
import Submission.Work.FTS.EllipticEst.Honest.I4UpperHonest
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.Dz_slice_identities
import Submission.Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen
import Submission.Work.FTS.EllipticEst.remov.wsAux
import Submission.Work.FTS.H2.STFacts
import Submission.Work.FTS.LocDataExt.oneSubChi_jet_le5
import Submission.Work.FTS.OpenPkg.ProdOpen.Tools1d
import Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongEps.EpsZero.slice_facts_of_classC
import Submission.Work.FTS.StrongPersist.N6.Swap6
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS.StrongPersist.QangSq6Full
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.VocabO
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_alt_l12fstar
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2W.PsiSlices.weakPos2_dilate
import Submission.Work.SolutionDelivery.DatumEuler
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.pz_mixed_mul_le_4
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
import Submission.Work.StabilityFar.Profile.exists_Fstar_add_ge
-- ===== merged: Submission.Work.FTS.EllipticEst.Dispatch.hkMemGradUD =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology

namespace Work.FTS.EllipticEst.Dispatch

set_option autoImplicit false

theorem hkMem_gradUD (α : ℝ) (u G : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) :
    Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u) := by
  obtain ⟨C, _hC, hmain⟩ := Work.Blocks.DzVamgm.HkNorm_Dz_amgm 0
  have hα1 : α ≤ 1 := by
    have h4 := h.hα4
    linarith
  have hu : Work.Spaces.HkMem α 0 u := hkMem_uM α u G h
  have hgrad : Work.Spaces.HkMem α 0 (Work.Spaces.Dz u) :=
    (hmain α u h.hα hα1 h.smooth hu h.memRad2).1
  exact hgrad

end Work.FTS.EllipticEst.Dispatch
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.AeLeftClean =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The left trace of a slice vanishes a.e., with a self-contained import cone

This module re-proves the almost-everywhere vanishing of the left trace
`lim_{θ→0⁺} u(z,θ)` for a datum `AeData α u G` of the almost-everywhere class of the level-`0`
elliptic estimate (and hence, for a datum of the weak class `TT.EllWeakPos α 0 F Ψ`), following
the route of `H2W/AeProof/AeSliceLeftTendstoAe`:

1. `sliceLimitLeftExists` gives the existence of `L z = lim_{θ→0⁺} u(z,θ)` for every `z > 0`
   (`bdd_of_sqSeta` supplies the boundedness input of the moment identity);
2. the slice moment identity `sliceMomentIdentClean` identifies `L z` with minus the three
   angular moments of `G`, `∂_z²u` and `∂_z u`;
3. the integrated radial moment chain `sliceMomentsZeroClean` (from `F_* u = 0` a.e., using the
   `ℋ⁰`-honesty of `z ∂_z u` for the box integrability of `∂_z u`) shows that the last two
   moments vanish a.e., while the first does by hypothesis;
4. hence `L = 0` a.e.

The point of the re-proof is that the import cone avoids `H2W/Ae/hkMem_gradU` (whose own import
cone contains the `EllHyp`-rescoping casualties), using the self-contained
`AeS1.HkMemGradU` instead.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.AeLeftClean

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "Iθ" => Work.Spaces.Iθ
local notation "sig" => Work.FTS.EllipticEst.sEta
local notation "sg" => Work.Elliptic.sinCos2

/-! ## Boundedness of a slice with `σ`-square-integrable second derivative -/

/-- If `(u'')² σ` is integrable on `Iθ` then `u` and `u'` are bounded on the open interval. -/
theorem bdd_of_sqSeta {u : ℝ → ℝ}
    (hsm : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (h2 : MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun t : ℝ => deriv u t) θ) ^ 2 * sig θ) Iθ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |deriv u θ| ≤ C ∧ |u θ| ≤ C := by
  obtain ⟨M, hM⟩ := Work.FTS.EllipticEst.remov.SourceBound.auxDerivBound (u := u) hsm h2
  have hπ4 : (0 : ℝ) < Real.pi / 4 := by linarith [Real.pi_pos]
  have hπ4lt : Real.pi / 4 < Real.pi / 2 := by linarith [Real.pi_pos]
  have hMnn : 0 ≤ M := (abs_nonneg _).trans (hM (Real.pi / 4) ⟨hπ4, hπ4lt⟩)
  have hcont : ContinuousOn (deriv u) (Set.Ioo 0 (Real.pi / 2)) :=
    hsm.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hder : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), HasDerivAt u (deriv u x) x := by
    intro x hx
    have h1 : ContDiffAt ℝ 2 u x := hsm.contDiffAt (isOpen_Ioo.mem_nhds hx)
    have h2 : ContDiffAt ℝ 1 u x := h1.of_le (by norm_num)
    exact (h2.differentiableAt (by norm_num)).hasDerivAt
  refine ⟨|u (Real.pi / 4)| + M * (Real.pi / 2), by positivity, fun θ hθ => ⟨?_, ?_⟩⟩
  · have h1 : M ≤ M * (Real.pi / 2) := by nlinarith [hMnn, Real.pi_gt_three]
    have h2 : M * (Real.pi / 2) ≤ |u (Real.pi / 4)| + M * (Real.pi / 2) :=
      le_add_of_nonneg_left (abs_nonneg _)
    exact (hM θ hθ).trans (h1.trans h2)
  · have hmem : Set.uIcc (Real.pi / 4) θ ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
      intro x hx
      rw [Set.uIcc] at hx
      exact ⟨lt_of_lt_of_le (lt_min hπ4 hθ.1) hx.1,
        lt_of_le_of_lt hx.2 (max_lt hπ4lt hθ.2)⟩
    have hFTC : (∫ t in Real.pi / 4..θ, deriv u t) = u θ - u (Real.pi / 4) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => hder x (hmem hx))
        ((hcont.mono hmem).intervalIntegrable)
    have hint : |∫ t in Real.pi / 4..θ, deriv u t| ≤ M * (Real.pi / 2) := by
      have h2' : |∫ t in Real.pi / 4..θ, deriv u t| ≤ M * |θ - Real.pi / 4| := by
        simpa only [Real.norm_eq_abs] using
          intervalIntegral.norm_integral_le_of_norm_le_const (f := fun t => deriv u t)
            (C := M) (a := Real.pi / 4) (b := θ) (fun s hs => by
              rw [Set.uIoc] at hs
              rw [Real.norm_eq_abs]
              exact hM s (hmem (by rw [Set.uIcc]; exact ⟨hs.1.le, hs.2⟩)))
      have h3 : |θ - Real.pi / 4| ≤ Real.pi / 2 := by
        rw [abs_le]
        constructor <;> linarith [hθ.1, hθ.2, Real.pi_pos]
      exact h2'.trans (mul_le_mul_of_nonneg_left h3 hMnn)
    have h4 : |u θ| ≤ |u (Real.pi / 4)| + |u θ - u (Real.pi / 4)| := by
      have := abs_add_le (u (Real.pi / 4)) (u θ - u (Real.pi / 4))
      simpa using this
    have h5 : |u θ - u (Real.pi / 4)| ≤ M * (Real.pi / 2) := by
      rw [← hFTC]
      exact hint
    linarith

/-! ## The slice moment identity at the left endpoint -/

/-- `∫_θ (Lzero1 u)·sinθcos²θ = -L` when `u → L` at `0⁺` and `(u'')²σ` is integrable. -/
theorem Lzero1_moment_neg_limit {u : ℝ → ℝ} {L : ℝ}
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (h2 : MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun t : ℝ => deriv u t) θ) ^ 2 * sig θ) Iθ)
    (hL : MeasureTheory.IntegrableOn
      (fun θ => Work.FTS.EllipticEst.Lzero1 u θ * sg θ) Iθ)
    (hlim : Filter.Tendsto u (nhdsWithin 0 (Set.Ioi 0)) (nhds L)) :
    (∫ θ in Iθ, Work.FTS.EllipticEst.Lzero1 u θ * sg θ) = -L := by
  obtain ⟨C, hCnn, hC⟩ := bdd_of_sqSeta hu h2
  exact Work.FTS.EllipticEst.Honest.sliceMoment_eq_neg_limit hCnn hu
    (fun θ hθ => ⟨(hC θ hθ).2, (hC θ hθ).1⟩) hL hlim

/-! ## The radial Agmon certificate in the `AeData` class -/

/-- **`HkMem α 0 (z ∂_z u)` for `AeData` data** (self-contained version of
`H2W.Ae.hkMem_gradU`, using the Agmon certificate of `AeS1.DzAgmonClean`). -/
theorem hkMem_gradUClean (α : ℝ) (u G : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) :
    Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz u z θ) := by
  obtain ⟨C, _hC, hmain⟩ := Work.Blocks.DzVamgm.HkNorm_Dz_amgm 0
  have hα1 : α ≤ 1 := by
    have h4 := h.hα4
    linarith
  have hu : Work.Spaces.HkMem α 0 u :=
    Work.FTS.EllipticEst.H2W.AeProof.AeSigma.AeHkMemU α u G h
  have hgrad : Work.Spaces.HkMem α 0 (Work.Spaces.Dz u) :=
    (hmain α u h.hα hα1 h.smooth hu h.memRad2).1
  exact hgrad

/-! ## Slicewise integrability of a `HkMem` datum -/

/-- `HkMem α 0 g` gives the `σ`-weighted square integrability of every slice. -/
theorem hkMemSliceSqSigma {α : ℝ} {g : ℝ → ℝ → ℝ} (hg : Work.Spaces.HkMem α 0 g) {z : ℝ}
    (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => (g z θ) ^ 2 * sig θ) Iθ := by
  have hw : (Work.Spaces.w z) ^ 2 ≠ 0 := by
    have : Work.Spaces.w z ≠ 0 := by rw [Work.Spaces.w]; positivity
    exact pow_ne_zero 2 this
  have h1 : MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.w z) ^ 2 * ((g z θ) ^ 2 * sig θ)) Iθ :=
    (hg.1 z (Set.mem_Ici.mpr (le_of_lt hz))).congr_fun
      (fun θ hθ => by
        simp only
        rw [Work.FTS.EllipticEst.Endpt.HkIntegrand_zero_eq_sEta α g z hθ]
        ring)
      measurableSet_Icc
  rw [MeasureTheory.IntegrableOn] at h1 ⊢
  exact (MeasureTheory.integrable_const_mul_iff
    (c := (Work.Spaces.w z) ^ 2) (isUnit_iff_ne_zero.mpr hw)
    (fun θ => (g z θ) ^ 2 * sig θ)).mp h1

/-! ## The slice moment identity -/

/-- The `θ`-slice of `Lzero` is `Lzero1` applied to the `θ`-slice. -/
private theorem Lzero1_slice_eq (v : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.FTS.EllipticEst.Lzero1 (fun t : ℝ => v z t) θ = Work.Elliptic.Lzero v z θ := by
  simp only [Work.FTS.EllipticEst.Lzero1, Work.Elliptic.Lzero, Work.Spaces.pthIter_succ,
    Work.Spaces.pthIter_zero, Work.Spaces.pth]

/-- The second `θ`-derivative of a slice is the slice of `pthIter 2`. -/
private theorem pthIter_two_slice_eq (v : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pthIter 2 v z θ = deriv (fun t : ℝ => deriv (fun t' : ℝ => v z t') t) θ := by
  simp only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero, Work.Spaces.pth]

/-- **The slice moment identity of the `AeData` class.** -/
theorem sliceMomentIdentClean (α : ℝ) (u G : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) {z : ℝ} (hz : 0 < z) {L : ℝ}
    (hL : Filter.Tendsto (fun θ : ℝ => u z θ) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds L)) :
    L = -(Work.Elliptic.Fstar G z
        + (α ^ 2 * z ^ 2) * (∫ θ in Iθ,
            Work.Spaces.pzIter 2 u z θ * sg θ)
        + (α * (5 + α) * z) * (∫ θ in Iθ,
            Work.Spaces.pz u z θ * sg θ)) := by
  obtain ⟨hint1, hint2, hint3⟩ :=
    Work.FTS.EllipticEst.H2W.AeProof.AeSliceMomentFinite α u G h hz
  have hU : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hU2 : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 u) := by
    simpa only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero] using (hU.pth).pth
  have hu2 : ContDiffOn ℝ 2 (fun θ : ℝ => u z θ) (Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.EllipticEst.remov.ws_contDiffOn_slice hU hz
  have hθ2 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv (fun t : ℝ => deriv (fun t' : ℝ => u z t') t) θ) ^ 2
        * sig θ) Iθ := by
    have hw := Work.FTS.EllipticEst.remov.ws_slot_slice hU2 h.memAng2 0 (Nat.zero_le 0) hz
    simpa only [Work.Spaces.DzIter_zero, pthIter_two_slice_eq] using hw
  have hmoment : (∫ θ in Iθ,
      Work.FTS.EllipticEst.Lzero1 (fun t : ℝ => u z t) θ * sg θ) = -L :=
    Lzero1_moment_neg_limit hu2 hθ2 hint3 hL
  have hpt : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.FTS.EllipticEst.Lzero1 (fun t : ℝ => u z t) θ * sg θ
        = G z θ * sg θ + α ^ 2 * z ^ 2 * (Work.Spaces.pzIter 2 u z θ * sg θ)
          + α * (5 + α) * z * (Work.Spaces.pz u z θ * sg θ) := by
    intro θ hθ
    have heq := h.eq z hz θ hθ.1 hθ.2
    rw [Work.Elliptic.bslOp_apply] at heq
    have hkey : Work.Elliptic.Lzero u z θ = G z θ + α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 u z θ
        + α * (5 + α) * z * Work.Spaces.pz u z θ := by linarith
    rw [Lzero1_slice_eq u z θ, hkey]
    ring
  have hae : (fun θ : ℝ => Work.FTS.EllipticEst.Lzero1 (fun t : ℝ => u z t) θ * sg θ)
      =ᵐ[MeasureTheory.volume.restrict Iθ]
      (fun θ : ℝ => G z θ * sg θ + α ^ 2 * z ^ 2 * (Work.Spaces.pzIter 2 u z θ * sg θ)
        + α * (5 + α) * z * (Work.Spaces.pz u z θ * sg θ)) :=
    Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => hpt θ hθ)
  have hGint : MeasureTheory.IntegrableOn (fun θ : ℝ => G z θ * sg θ) Iθ := by
    have hsub : MeasureTheory.IntegrableOn
        (fun θ : ℝ => Work.FTS.EllipticEst.Lzero1 (fun t : ℝ => u z t) θ * sg θ
          - (α ^ 2 * z ^ 2 * (Work.Spaces.pzIter 2 u z θ * sg θ)
            + α * (5 + α) * z * (Work.Spaces.pz u z θ * sg θ))) Iθ :=
      hint3.sub ((hint2.const_mul _).add (hint1.const_mul _))
    refine hsub.congr ?_
    filter_upwards [hae] with θ hθ
    linarith
  have hIntegral : (∫ θ in Iθ,
        Work.FTS.EllipticEst.Lzero1 (fun t : ℝ => u z t) θ * sg θ)
      = Work.Elliptic.Fstar G z
        + α ^ 2 * z ^ 2 * (∫ θ in Iθ, Work.Spaces.pzIter 2 u z θ * sg θ)
        + α * (5 + α) * z * (∫ θ in Iθ, Work.Spaces.pz u z θ * sg θ) := by
    have h1 : (∫ θ in Iθ,
          Work.FTS.EllipticEst.Lzero1 (fun t : ℝ => u z t) θ * sg θ)
        = ∫ θ in Iθ, (G z θ * sg θ
            + α ^ 2 * z ^ 2 * (Work.Spaces.pzIter 2 u z θ * sg θ)
            + α * (5 + α) * z * (Work.Spaces.pz u z θ * sg θ)) :=
      MeasureTheory.integral_congr_ae hae
    have hsplit1 : (∫ θ in Iθ, (G z θ * sg θ
          + α ^ 2 * z ^ 2 * (Work.Spaces.pzIter 2 u z θ * sg θ)
          + α * (5 + α) * z * (Work.Spaces.pz u z θ * sg θ)))
        = (∫ θ in Iθ, (G z θ * sg θ
            + α ^ 2 * z ^ 2 * (Work.Spaces.pzIter 2 u z θ * sg θ)))
          + (∫ θ in Iθ, α * (5 + α) * z * (Work.Spaces.pz u z θ * sg θ)) :=
      MeasureTheory.integral_add
        (f := fun θ : ℝ => G z θ * sg θ
          + α ^ 2 * z ^ 2 * (Work.Spaces.pzIter 2 u z θ * sg θ))
        (g := fun θ : ℝ => α * (5 + α) * z * (Work.Spaces.pz u z θ * sg θ))
        (hGint.add (hint2.const_mul (α ^ 2 * z ^ 2))) (hint1.const_mul (α * (5 + α) * z))
    have hsplit2 : (∫ θ in Iθ, (G z θ * sg θ
          + α ^ 2 * z ^ 2 * (Work.Spaces.pzIter 2 u z θ * sg θ)))
        = (∫ θ in Iθ, G z θ * sg θ)
          + (∫ θ in Iθ, α ^ 2 * z ^ 2 * (Work.Spaces.pzIter 2 u z θ * sg θ)) :=
      MeasureTheory.integral_add
        (f := fun θ : ℝ => G z θ * sg θ)
        (g := fun θ : ℝ => α ^ 2 * z ^ 2 * (Work.Spaces.pzIter 2 u z θ * sg θ))
        hGint (hint2.const_mul (α ^ 2 * z ^ 2))
    rw [h1, hsplit1, hsplit2, MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const_mul]
    rfl
  rw [hIntegral] at hmoment
  linarith

/-! ## The integrated radial moment chain -/

/-- **The moment of a function whose box-integral against `sinθcos²θ` converges is locally
integrable on the radial axis.**  This is Fubini on the box `[a,b] × Iθ`. -/
private theorem integrableOn_Fstar_of_box {g : ℝ → ℝ → ℝ} {a b : ℝ}
    (hbox : MeasureTheory.IntegrableOn
      (Function.uncurry (fun s θ : ℝ => g s θ * sg θ)) (Set.Icc a b ×ˢ Iθ)) :
    MeasureTheory.IntegrableOn (Work.Elliptic.Fstar g) (Set.Icc a b) := by
  have h1 : MeasureTheory.Integrable (Function.uncurry (fun s θ : ℝ => g s θ * sg θ))
      ((MeasureTheory.volume.restrict (Set.Icc a b)).prod
        (MeasureTheory.volume.restrict Iθ)) := by
    rw [MeasureTheory.Measure.prod_restrict]
    exact hbox
  have h2 := h1.integral_prod_left
  refine h2.congr (Filter.Eventually.of_forall fun s => ?_)
  show (∫ θ, Function.uncurry (fun s θ : ℝ => g s θ * sg θ) (s, θ)
    ∂(MeasureTheory.volume.restrict Iθ)) = Work.Elliptic.Fstar g s
  simp only [Function.uncurry_apply_pair, Work.Elliptic.Fstar]

/-- **The `θ`-slice of `g` against `sinθcos²θ` is integrable**, from `HkMem α 0 g`. -/
private theorem slice_mul_sinCos2_integrableOn {g : ℝ → ℝ → ℝ}
    (hg : Work.FTS.EllipticEst.SmoothOpen g) {α : ℝ} (hm : Work.Spaces.HkMem α 0 g)
    {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => g z θ * sg θ) Iθ :=
  (Work.FTS.EllipticEst.remov.ws_absMoment (Work.FTS.EllipticEst.remov.ws_aesm_slice hg hz)
    (hkMemSliceSqSigma hm hz)).1

/-- **Both radial moments of a datum of the `AeData` class vanish almost everywhere.** -/
theorem sliceMomentsZeroClean (α : ℝ) (u G : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) :
    (∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
        Work.Elliptic.Fstar (Work.Spaces.pz u) z = 0)
    ∧ (∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
        Work.Elliptic.Fstar (Work.Spaces.pzIter 2 u) z = 0) := by
  have hU : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hmemU : Work.Spaces.HkMem α 0 u :=
    Work.FTS.EllipticEst.H2W.AeProof.AeSigma.AeHkMemU α u G h
  have hmemGrad : Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz u z θ) :=
    hkMem_gradUClean α u G h
  have hbox1 : ∀ a b : ℝ, 0 < a → a < b → MeasureTheory.IntegrableOn
      (Function.uncurry (fun s θ : ℝ => (Work.Spaces.pz u s θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) (Set.Icc a b ×ˢ Iθ) :=
    Work.FTS.EllipticEst.Endpt.boxIntegrable_pzPsi h.smooth hmemGrad
  have hbox2 : ∀ a b : ℝ, 0 < a → a < b → MeasureTheory.IntegrableOn
      (Function.uncurry (fun s θ : ℝ => (Work.Spaces.pzIter 2 u s θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) (Set.Icc a b ×ˢ Iθ) :=
    Work.FTS.EllipticEst.Endpt.boxIntegrable_pzIter2Psi h.smooth h.memRad2
  have hslU : ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn
      (fun θ : ℝ => u z θ * sg θ) Iθ :=
    fun z hz => slice_mul_sinCos2_integrableOn hU hmemU hz
  have hslPz : ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Spaces.pz u z θ * sg θ) Iθ :=
    fun z hz => (Work.FTS.EllipticEst.H2W.AeProof.AeSliceMomentFinite α u G h hz).1
  have hT2 : ∀ a b : ℝ, 0 < a → a < b →
      MeasureTheory.IntegrableOn (Work.Elliptic.Fstar (Work.Spaces.pzIter 2 u)) (Set.Icc a b) :=
    Work.FTS.EllipticEst.Endpt.integrableOn_fstar_pzIter2 h.smooth h.memRad2
  have hrelU : ∀ a b : ℝ, 0 < a → a < b →
      Work.Elliptic.Fstar u b
        = Work.Elliptic.Fstar u a
          + ∫ s in Set.Icc a b, Work.Elliptic.Fstar (Work.Spaces.pz u) s :=
    fun a b ha hab => Work.FTS.EllipticEst.moment_relation u hU hbox1 hslU ha hab
  have hrelPz : ∀ a b : ℝ, 0 < a → a < b →
      Work.Elliptic.Fstar (Work.Spaces.pz u) b
        = Work.Elliptic.Fstar (Work.Spaces.pz u) a
          + ∫ s in Set.Icc a b, Work.Elliptic.Fstar (Work.Spaces.pzIter 2 u) s :=
    fun a b ha hab =>
      Work.FTS.EllipticEst.moment_relation (Work.Spaces.pz u) hU.pz hbox2 hslPz ha hab
  have hchainU : ∀ s t : ℝ, 0 < s → s ≤ t →
      Work.Elliptic.Fstar u t - Work.Elliptic.Fstar u s
        = ∫ r in s..t, Work.Elliptic.Fstar (Work.Spaces.pz u) r := by
    intro s t hs hst
    rcases lt_or_eq_of_le hst with hlt | heq
    · have h0 := hrelU s t hs hlt
      have hconv : (∫ r in s..t, Work.Elliptic.Fstar (Work.Spaces.pz u) r)
          = ∫ r in Set.Icc s t, Work.Elliptic.Fstar (Work.Spaces.pz u) r := by
        rw [intervalIntegral.integral_of_le hlt.le]
        exact MeasureTheory.setIntegral_congr_set
          (MeasureTheory.Ioc_ae_eq_Icc (μ := MeasureTheory.volume))
      rw [hconv]
      linarith
    · subst heq
      simp
  have hchainPz : ∀ s t : ℝ, 0 < s → s ≤ t →
      Work.Elliptic.Fstar (Work.Spaces.pz u) t - Work.Elliptic.Fstar (Work.Spaces.pz u) s
        = ∫ r in s..t, Work.Elliptic.Fstar (Work.Spaces.pzIter 2 u) r := by
    intro s t hs hst
    rcases lt_or_eq_of_le hst with hlt | heq
    · have h0 := hrelPz s t hs hlt
      have hconv : (∫ r in s..t, Work.Elliptic.Fstar (Work.Spaces.pzIter 2 u) r)
          = ∫ r in Set.Icc s t, Work.Elliptic.Fstar (Work.Spaces.pzIter 2 u) r := by
        rw [intervalIntegral.integral_of_le hlt.le]
        exact MeasureTheory.setIntegral_congr_set
          (MeasureTheory.Ioc_ae_eq_Icc (μ := MeasureTheory.volume))
      rw [hconv]
      linarith
    · subst heq
      simp
  have hIntB : ∀ a b : ℝ, 0 < a → a < b →
      IntervalIntegrable (Work.Elliptic.Fstar (Work.Spaces.pz u)) MeasureTheory.volume a b := by
    intro a b ha hab
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab.le]
    exact integrableOn_Fstar_of_box
      (Work.FTS.EllipticEst.integrableOn_pz_mul_sinCos2 u hU hbox1 ha hab)
  have hIntA : ∀ a b : ℝ, 0 < a → a < b →
      IntervalIntegrable (Work.Elliptic.Fstar (Work.Spaces.pzIter 2 u)) MeasureTheory.volume a b := by
    intro a b ha hab
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab.le]
    exact hT2 a b ha hab
  have hB := Work.FTS.EllipticEst.H2W.PsiSlices.ae_eq_zero_of_moment_chain
    (W := Work.Elliptic.Fstar u) (V := Work.Elliptic.Fstar (Work.Spaces.pz u))
    hchainU h.momU hIntB
  exact ⟨hB, Work.FTS.EllipticEst.H2W.PsiSlices.ae_eq_zero_of_moment_chain
    (W := Work.Elliptic.Fstar (Work.Spaces.pz u))
    (V := Work.Elliptic.Fstar (Work.Spaces.pzIter 2 u)) hchainPz hB hIntA⟩

/-! ## The left trace vanishes a.e. -/

/-- **The left trace of a slice of an `AeData` datum vanishes almost everywhere.** -/
theorem sliceLeftTendstoClean (α : ℝ) (u G : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Filter.Tendsto (fun θ => u z θ) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  have hU : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hexists : ∀ z : ℝ, ∃ L : ℝ, z ∈ Set.Ioi (0 : ℝ) →
      Filter.Tendsto (fun θ => u z θ) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds L) := by
    intro z
    by_cases hz : 0 < z
    · have hsmz : ∀ n : ℕ, ContDiffOn ℝ n (fun θ => u z θ) (Set.Ioo 0 (Real.pi / 2)) :=
        fun n => contDiffOn_iff_forall_nat_le.mp (hU.curry_θ hz) n le_top
      have hint0 : MeasureTheory.IntegrableOn
          (fun θ => (Work.Spaces.pthIter 2 u z θ) ^ 2 * sig θ) Iθ :=
        Work.FTS.EllipticEst.remov.ws_slot_slice (hU.pth.pth) h.memAng2 0 (le_refl 0) hz
      have hint : MeasureTheory.IntegrableOn
          (fun θ => deriv (fun t => deriv (fun θ' => u z θ') t) θ ^ 2 * sig θ) Iθ := by
        refine hint0.congr (Filter.Eventually.of_forall (fun θ => ?_))
        simp only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero, Work.Spaces.pth]
      obtain ⟨L₀, hL₀⟩ := Work.FTS.EllipticEst.sliceLimitLeftExists (fun θ => u z θ) hsmz hint
      exact ⟨L₀, fun _ => hL₀⟩
    · exact ⟨0, fun hmem => absurd hmem hz⟩
  let L : ℝ → ℝ := fun z => Classical.choose (hexists z)
  have hL : ∀ z : ℝ, z ∈ Set.Ioi (0 : ℝ) →
      Filter.Tendsto (fun θ => u z θ) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (L z)) :=
    fun z hz => Classical.choose_spec (hexists z) hz
  obtain ⟨hM1, hM2⟩ := sliceMomentsZeroClean α u G h
  have hae : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)), L z = 0 := by
    filter_upwards [h.momG, hM1, hM2,
      MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with z hG h1 h2 hmem
    have hz : 0 < z := hmem
    have h1' : (∫ θ in Iθ,
        Work.Spaces.pz u z θ * sg θ) = 0 := by
      simpa only [Work.Elliptic.Fstar] using h1
    have h2' : (∫ θ in Iθ,
        Work.Spaces.pzIter 2 u z θ * sg θ) = 0 := by
      simpa only [Work.Elliptic.Fstar] using h2
    have hid := sliceMomentIdentClean α u G h hz (hL z hmem)
    rw [hG, h1', h2'] at hid
    linarith [hid]
  filter_upwards [hae, MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with z hz0 hmem
  simpa [hz0] using hL z hmem

/-! ## The weak class -/

/-- The weak hypothesis class `TT.EllWeakPos α 0 F Ψ` is the pointwise-moment form of the
almost-everywhere class `AeData α Ψ F`: every field matches verbatim, and the two *pointwise*
moment conditions imply the a.e. ones. -/
theorem aeData_of_ellWeakPos {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 0 F Ψ) :
    Work.FTS.EllipticEst.H2W.Ae.AeData α Ψ F :=
  ⟨hα, hα4, h.eq, h.zero, h.pi_half, h.smooth, h.memF, h.memA, h.memB,
    (by filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
        exact h.orthPsi z hz),
    (by filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
        exact h.orthF z hz)⟩


end Work.FTS.EllipticEst.H2W.AeLeftClean
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.AeProof.ae.AeSetup =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `AeSetup` — the shared measure/weight/integrability toolkit for `devInfOpen`

This module holds the parts of the proof of `Work.FTS.EllipticEst.H2W.AeProof.ae.devInfOpen`
that are *shared* between that theorem and the auxiliary lemmas proved for it in sibling
modules (`ae/AeJointTheta.lean`, `ae/AeJointPz.lean`, `ae/AeSliceIdent.lean`, the chain
lemmas): the product measure `dν` and its identification with the iterated integrals over
`Iz × Iθ`, the elementary weight facts, the `Tonelli` lemma `hkMem_jointIntegrable`, the
bounds on the cutoff `W`, and the four joint-integrability statements of
`jointIntegrable_basic`.
-/

namespace Work.FTS.EllipticEst.H2W.AeProof.ae

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- The product measure `dz dθ` over the open quadrant `(0,∞) × (0,π/2)`.  All the `a.e.`
statements of this file are stated for this measure; `dν_eq` identifies it with the product of
the restricted measures on the closed sets `Iz`, `Iθ` which occur in the statement. -/
def dν : MeasureTheory.Measure (ℝ × ℝ) :=
  (MeasureTheory.volume.restrict (Set.Ioi 0)).prod
    (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2)))


/-- `dν` is the restriction of `volume × volume` to the open quadrant. -/
theorem dν_quad : dν = (MeasureTheory.volume.prod MeasureTheory.volume).restrict
    (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  rw [dν, ← MeasureTheory.Measure.prod_restrict]

/-- Almost every point of `dν` lies in the open quadrant. -/
theorem ae_mem_quad : ∀ᵐ p ∂dν, p ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2) := by
  rw [dν_quad]
  exact MeasureTheory.ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioo)

/-! ## Elementary facts about the weights -/

/-- The radial weight satisfies `w z ≥ 1` for `z > 0`. -/
theorem one_le_w {z : ℝ} (hz : 0 < z) : 1 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w, le_div_iff₀ (by positivity : (0 : ℝ) < z ^ 2)]
  nlinarith

/-- The angular weight satisfies `thEta θ ≥ 1` on the open interval. -/
theorem one_le_thEta {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    1 ≤ Work.FTS.EllipticEst.thEta θ := by
  rw [Work.FTS.EllipticEst.thEta]
  have hpos : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hle : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have h := Real.rpow_le_rpow_of_nonpos hpos hle
    (show -(Work.Spaces.eta) ≤ 0 by norm_num [Work.Spaces.eta])
  rwa [Real.one_rpow] at h

/-- `thEta` is nonnegative on the angular interval. -/
theorem thEta_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.FTS.EllipticEst.thEta θ := by
  rw [Work.FTS.EllipticEst.thEta]
  refine Real.rpow_nonneg ?_ _
  exact Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

/-- The level-`0` integrand is `w²·g²·thEta` on `Iθ`. -/
theorem hkIntegrand_zero (α : ℝ) (g : ℝ → ℝ → ℝ) {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 0 g z θ
      = (Work.Spaces.w z) ^ 2 * ((g z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) := by
  rw [Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq α g z θ,
    Work.FTS.EllipticEst.Honest.sq_profile_eq g z θ
      (Work.FTS.EllipticEst.Honest.sin_two_nonneg_of_mem_Iθ hθ)]
  simp only [Work.FTS.EllipticEst.thEta, Work.FTS.EllipticEst.sEta]
  ring


/-- The endpoint `0` is the only point of `Iz` where `w` vanishes. -/
theorem w_pos_of_pos {z : ℝ} (hz : 0 < z) : 0 < Work.Spaces.w z :=
  lt_of_lt_of_le zero_lt_one (one_le_w hz)

/-! ## Uniform bounds for the cutoff `W` -/





/-! ## Continuity and measurability of the weights -/





/-! ## Cauchy–Schwarz -/

/-- The product of two functions with square-integrable squares is integrable. -/
theorem integrable_mul_of_sq {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ}
    (hf : MeasureTheory.Integrable (fun x => (f x) ^ 2) μ)
    (hg : MeasureTheory.Integrable (fun x => (g x) ^ 2) μ)
    (hfm : AEMeasurable f μ) (hgm : AEMeasurable g μ) :
    MeasureTheory.Integrable (fun x => f x * g x) μ := by
  have h1 : MeasureTheory.Integrable (fun x => (f x) ^ 2 + (g x) ^ 2) μ := hf.add hg
  refine MeasureTheory.Integrable.mono' (h1.const_mul (1 / 2))
    ((hfm.mul hgm).aestronglyMeasurable) ?_
  filter_upwards with x
  have h2 : |f x| * |g x| ≤ ((f x) ^ 2 + (g x) ^ 2) / 2 := by
    have h := sq_nonneg (|f x| - |g x|)
    rw [sub_sq, sq_abs, sq_abs] at h
    linarith
  rw [Real.norm_eq_abs, abs_mul]
  calc |f x| * |g x| ≤ ((f x) ^ 2 + (g x) ^ 2) / 2 := h2
    _ = (1 / 2) * ((f x) ^ 2 + (g x) ^ 2) := by ring









end

end Work.FTS.EllipticEst.H2W.AeProof.ae
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.AeStep1Leaves.AeHkMemU =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Copy of `H2W.Ae.hkMem_u` in a private namespace

This module is a verbatim copy of `Submission/Work/FTS/EllipticEst/H2W/Ae/hkMem_u.lean`
(whose content is `Work.FTS.EllipticEst.H2W.Ae.hkMem_u`), with two changes:

* the import of `Honest.firstOrderHonest` is dropped (that module currently cannot be built);
* the single lemma taken from it, `Honest.hkIntegrand_eq_w_sq` (an eight-line rewriting), is
  reproved here as `hkIntegrand_zero_thEta`.

Consequently this module, and every module importing it, is independent of
`Honest.firstOrderHonest`; the declaration is renamed `hkMem_u_of_AeData` to avoid any clash
with the original.  The statement of `hkMem_u_of_AeData` is
byte-for-byte the statement of `H2W.Ae.hkMem_u`.
-/

namespace Work.FTS.EllipticEst.H2W.AeStep1Leaves

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-- `σ θ = sin(2θ)^{-η} ≥ 0` on `Iθ`. -/
private lemma sEta_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.FTS.EllipticEst.thEta θ :=
  Real.rpow_nonneg (Work.FTS.EllipticEst.sin_two_nonneg hθ) _

/-!
# `HkMem α 0 u` in the almost-everywhere class

The level-`0` `ℋ`-membership `Work.Spaces.HkMem α 0 u` of the solution of `bslOp α u = G` in the
almost-everywhere class `AeData`.  The class gives `HkMem` of `G`, of `z²∂_zz u` and of `∂_θθ u`
but nothing directly about `u`; the missing ingredient is the *slicewise* bound
`∫_θ u(z,θ)² σ θ ≤ C ∫_θ (∂_θθ u)(z,θ)² σ θ` (`σ = sin(2θ)^{-η}`), which holds for a.e. `z`: the
two a.e. moment conditions of `AeData` kill the only angular mode (the affine one) that the second
angular derivative does not see.

That slice bound is produced by the a.e. version `H2W.Ae.aesliceU_of` of the sibling development,
fed with the *two-derivative weighted Hardy inequality* for slices whose two endpoint limits
vanish (`H2W.Ae.ZeroHardy.sliceZeroLimitHardy`, proved in `H2W/Ae/ZeroHardy/`), and the
`θ → π/2` endpoint behaviour of the slices (`H2W.Ae.AeSliceRightTendsto`).

The last step — from the a.e. *slice* bound to the honest `HkMem α 0 u` — is carried out here:
the a.e. strong measurability of the outer integrand and the slicewise boundedness of `u`
(`Endpt.sliceBdd_of_hmB`) give the two halves of `HkMem`.
-/

/-! ## The level-`0` integrand and its slice integral in the `σ`-form -/

/-- On `Iθ` the level-`0` integrand is `w(z)² · (g z θ)² · σ θ`.

(Self-contained replacement for `Work.FTS.EllipticEst.Honest.hkIntegrand_eq_w_sq`, whose
module is not imported here; the two proofs are the same.) -/
private theorem hkIntegrand_zero_thEta (α : ℝ) (g : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 0 g z θ
      = (Work.Spaces.w z) ^ 2 * ((g z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) := by
  rw [Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq α g z θ,
    Work.FTS.EllipticEst.Honest.sq_profile_eq g z θ
      (Work.FTS.EllipticEst.Honest.sin_two_nonneg_of_mem_Iθ hθ)]
  simp only [Work.FTS.EllipticEst.thEta]
  ring

/-- The `θ`-integral of the level-`0` integrand, with the radial weight `w(z)²` pulled out. -/
private theorem integral_hkIntegrand_zero (α : ℝ) (g : ℝ → ℝ → ℝ) (z : ℝ) :
    (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g z θ)
      = (Work.Spaces.w z) ^ 2
        * ∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ := by
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
  exact hkIntegrand_zero_thEta α g hθ

/-- The `θ`-integral of the level-`0` integrand is nonnegative. -/
private theorem integral_hkIntegrand_zero_nonneg (α : ℝ) (g : ℝ → ℝ → ℝ) (z : ℝ) :
    0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g z θ :=
  MeasureTheory.setIntegral_nonneg measurableSet_Icc
    (fun θ _ => Work.Spaces.HkIntegrand_nonneg α 0 g z θ)

/-! ## From the a.e. `lintegral` slice bound to the a.e. integral slice bound -/

/-- **The a.e. slice bound in real-integral form.**  An a.e. (in `z`) `lintegral` comparison for
the slice integrands upgrades to the comparison of the honest integrals, because the right-hand
side is honest by hypothesis. -/
theorem aeReal_of_aeLintegral {α : ℝ} {u : ℝ → ℝ → ℝ}
    (hsmooth : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hmemB : Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 u))
    {K : ℝ} (hK : 0 < K)
    (hbound : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal ((u z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        ≤ ENNReal.ofReal K * ∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal ((Work.Spaces.pthIter 2 u z θ) ^ 2
              * Work.FTS.EllipticEst.thEta θ)) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        ≤ K * ∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.pthIter 2 u z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ := by
  filter_upwards [hbound, MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz hzpos
  -- the second-derivative slice integrand is honest
  have hint2 : MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.pthIter 2 u z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.Honest.HkMemSliceSqSigma hmemB hzpos
  have hnn2 : 0 ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      fun θ => (Work.Spaces.pthIter 2 u z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _) (sEta_nonneg_Iθ hθ))
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint2 hnn2] at hz
  rw [← ENNReal.ofReal_mul (le_of_lt hK)] at hz
  -- the left-hand side is finite
  have hfin : (∫⁻ θ in Work.Spaces.Iθ,
      ENNReal.ofReal ((u z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)) < ⊤ :=
    lt_of_le_of_lt hz ENNReal.ofReal_lt_top
  -- hence the left integrand is integrable
  have hcontσ : ContinuousOn (fun θ : ℝ => Work.FTS.EllipticEst.thEta θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
    have hsin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo 0 (Real.pi / 2)) :=
      ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn)
    exact hsin.rpow_const (fun θ hθ => Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi
      (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos]))))
  have hcontu : ContinuousOn (fun θ : ℝ => u z θ) (Set.Ioo 0 (Real.pi / 2)) :=
    (Work.FTS.EllipticEst.Endpt.contDiffOn_slice_of_strip hsmooth hzpos 1).continuousOn
  have haesmA : MeasureTheory.AEStronglyMeasurable
      (fun θ => (u z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    have h1 : ContinuousOn (fun θ => (u z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        (Set.Ioo 0 (Real.pi / 2)) := (hcontu.pow 2).mul hcontσ
    have h2 : MeasureTheory.AEStronglyMeasurable
        (fun θ => (u z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
      h1.aestronglyMeasurable measurableSet_Ioo
    rw [MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := 0)
        (b := Real.pi / 2))] at h2
    rw [Work.Spaces.Iθ]
    exact h2
  -- build the `IntegrableOn` statement
  have hnnA : 0 ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      fun θ => (u z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _) (sEta_nonneg_Iθ hθ))
  have hFinA : MeasureTheory.HasFiniteIntegral
      (fun θ => (u z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    refine lt_of_eq_of_lt ?_ hfin
    refine MeasureTheory.lintegral_congr_ae ?_
    filter_upwards [hnnA] with θ hθ
    exact Real.enorm_of_nonneg hθ
  have hintA : MeasureTheory.IntegrableOn
      (fun θ => (u z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ :=
    ⟨haesmA, hFinA⟩
  -- conclude by comparing `ofReal`s
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hintA hnnA] at hz
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (le_of_lt hK)
    (MeasureTheory.integral_nonneg_of_ae hnn2))).mp hz

/-! ## The main body -/

/-- **`HkMem α 0 u` from the a.e. slice inequality.** -/
theorem hkMem_u_of_ae_bound (K : ℝ) (hKpos : 0 < K)
    (α : ℝ) (u G : ℝ → ℝ → ℝ) (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (hbound : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        ≤ K * ∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.pthIter 2 u z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) :
    Work.Spaces.HkMem α 0 u := by
  -- ## the level-`0` integrand is continuous on the open quadrant
  have hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0 u p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have hfun : (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0 u p.1 p.2)
        = fun p : ℝ × ℝ => (u p.1 p.2
            * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
      funext p
      simp [Work.Spaces.HkIntegrand]
    rw [hfun]
    exact (((h.smooth 1).continuousOn).mul
      Work.FTS.EllipticEst.continuousOn_wdivsin_Q0).pow 2
  -- ## a.e. strong measurability of the angular slices
  have haesm_slice : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.AEStronglyMeasurable
      (fun θ => Work.Spaces.HkIntegrand α 0 u z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    intro z hz
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with h0 | hz0
    · rw [← h0]
      refine (MeasureTheory.aestronglyMeasurable_const :
        MeasureTheory.AEStronglyMeasurable (fun _ : ℝ => (0 : ℝ))
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)).congr ?_
      filter_upwards with θ
      simp [Work.Spaces.HkIntegrand, Work.Spaces.w]
    · exact Work.Spaces.aesm_slice_of_continuousOn_Qd _ hcont hz0
  -- ## a.e. strong measurability of the `θ`-integral
  have haesm_outer : MeasureTheory.AEStronglyMeasurable
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 u z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    (Work.Spaces.aesm_of_continuousOn_Qd _ hcont).integral_prod_right'
  -- ## the a.e. slice inequality, transported to `Iz`
  have hslice_bound : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        ≤ K * ∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.pthIter 2 u z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ := by
    change ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ici 0)), _
    rw [MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0)).symm]
    exact hbound
  -- ## the a.e. bound of the outer integrand
  have hFbound : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 u z θ)
        ≤ K * ∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 u) z θ := by
    filter_upwards [hslice_bound] with z hz
    rw [integral_hkIntegrand_zero α u z,
      integral_hkIntegrand_zero α (Work.Spaces.pthIter 2 u) z]
    calc (Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        ≤ (Work.Spaces.w z) ^ 2
            * (K * ∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.pthIter 2 u z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) :=
          mul_le_mul_of_nonneg_left hz (sq_nonneg _)
      _ = K * ((Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.pthIter 2 u z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) := by ring
  refine ⟨?_, ?_⟩
  · -- every angular slice of the integrand is integrable
    intro z hz
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with h0 | hz0
    · rw [← h0]
      have hzero : (fun θ : ℝ => Work.Spaces.HkIntegrand α 0 u 0 θ) = fun _ => (0 : ℝ) := by
        funext θ
        simp [Work.Spaces.HkIntegrand, Work.Spaces.w]
      rw [hzero]
      exact MeasureTheory.integrableOn_zero
    · obtain ⟨Cz, hCzpos, hCz⟩ :=
        Work.FTS.EllipticEst.Endpt.sliceBdd_of_hmB h.smooth h.memAng2 hz0
      refine Integrable.mono'
        ((Work.FTS.EllipticEst.integrableOn_thEta.1).const_mul
          ((Work.Spaces.w z) ^ 2 * Cz ^ 2)) (haesm_slice z hz) ?_
      have hmem : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
          θ ∈ Set.Ioo 0 (Real.pi / 2) := by
        rw [Work.Spaces.Iθ]
        rw [MeasureTheory.Measure.restrict_congr_set
          (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume)
            (a := 0) (b := Real.pi / 2)).symm]
        exact MeasureTheory.ae_restrict_mem measurableSet_Ioo
      filter_upwards [hmem] with θ hθ
      rw [Real.norm_eq_abs, abs_of_nonneg (Work.Spaces.HkIntegrand_nonneg α 0 u z θ)]
      have hθI : θ ∈ Work.Spaces.Iθ :=
        Set.mem_Icc.mpr ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
      have hsq : (u z θ) ^ 2 ≤ Cz ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hCz θ hθ).1 2
      calc Work.Spaces.HkIntegrand α 0 u z θ
          = (Work.Spaces.w z) ^ 2 * ((u z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) :=
            hkIntegrand_zero_thEta α u hθI
        _ ≤ (Work.Spaces.w z) ^ 2 * (Cz ^ 2 * Work.FTS.EllipticEst.thEta θ) := by
            refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
            exact mul_le_mul_of_nonneg_right hsq
              (sEta_nonneg_Iθ hθI)
        _ = ((Work.Spaces.w z) ^ 2 * Cz ^ 2) * Work.FTS.EllipticEst.thEta θ := by ring
  · -- the `z`-integral of the angular slices is integrable
    refine Integrable.mono' (h.memAng2.2.const_mul K) haesm_outer ?_
    filter_upwards [hFbound] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_hkIntegrand_zero_nonneg α u z)]
    exact hz


/-! ## `HkMem α 0 (z ∂_z u)`

The copy of `Work.FTS.EllipticEst.AeS1.hkMem_gradU` (which is itself a copy of
`Work.FTS.EllipticEst.H2W.Ae.hkMem_gradU`), using the self-contained Agmon certificate
`Work.Blocks.DzVamgm.HkNorm_Dz_amgm` of `AeS1.DzAgmonClean`. -/

end

end Work.FTS.EllipticEst.H2W.AeStep1Leaves
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.slot11_aux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W

set_option autoImplicit false


/-- The radial quantity `A = z²∂_z²Ψ` (`z²∂_z² = D_z² − D_z`). -/
def slot11A (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ

/-- `mixed 1 1 (∂_θθΨ) = sin(2θ)·∂_θ³(D_zΨ)` on the open quadrant: Clairaut across the `z`- and
`θ`-derivatives. -/
theorem slot11_mixed_eq {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.mixed 1 1 (Work.Spaces.pthIter 2 Ψ) z θ
        = Real.sin (2 * θ) * Work.Spaces.pthIter 3 (Work.Spaces.DzIter 1 Ψ) z θ := by
  intro z θ hz hθ hθ'
  have hcl : Work.Spaces.pz (Work.Spaces.pthIter 3 Ψ) z θ
      = Work.Spaces.pthIter 3 (Work.Spaces.pz Ψ) z θ :=
    Work.FTS.EllipticEst.remov.pz_pthIter_comm_open Ψ hΨ 3 z θ hz hθ hθ'
  have hmul : Work.Spaces.pthIter 3 (fun z θ => z * Work.Spaces.pz Ψ z θ) z θ
      = z * Work.Spaces.pthIter 3 (Work.Spaces.pz Ψ) z θ := by
    simpa using congrFun (congrFun
      (Work.FTS.EllipticEst.remov.pthIter_mul_fst (Work.Spaces.pz Ψ) 3) z) θ
  have hDz : Work.Spaces.DzIter 1 Ψ = fun z θ => z * Work.Spaces.pz Ψ z θ := by
    rw [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero]
    rfl
  -- (1) `mixed 1 1 (∂_θθΨ) = sin(2θ) · D_z(∂_θ³Ψ)`
  have h1 : Work.Spaces.mixed 1 1 (Work.Spaces.pthIter 2 Ψ) z θ
      = Real.sin (2 * θ) * Work.Spaces.Dz (Work.Spaces.pthIter 3 Ψ) z θ := by
    show Work.Spaces.Dz (Work.Spaces.Dth (Work.Spaces.pthIter 2 Ψ)) z θ = _
    have hfun : Work.Spaces.Dth (Work.Spaces.pthIter 2 Ψ)
        = fun z θ => Real.sin (2 * θ) * Work.Spaces.pthIter 3 Ψ z θ := rfl
    have hfun2 : Work.Spaces.Dz (fun z θ => Real.sin (2 * θ) * Work.Spaces.pthIter 3 Ψ z θ)
        = fun z θ => Real.sin (2 * θ) * Work.Spaces.Dz (Work.Spaces.pthIter 3 Ψ) z θ := by
      funext z' θ'
      show z' * deriv (fun z'' => Real.sin (2 * θ') * Work.Spaces.pthIter 3 Ψ z'' θ') z'
        = Real.sin (2 * θ') * (z' * deriv (fun z'' => Work.Spaces.pthIter 3 Ψ z'' θ') z')
      rw [deriv_const_mul_field]
      ring
    rw [hfun, hfun2]
  -- (2) `D_z(∂_θ³Ψ) = ∂_θ³(D_zΨ)`
  have h2 : Work.Spaces.Dz (Work.Spaces.pthIter 3 Ψ) z θ
      = Work.Spaces.pthIter 3 (Work.Spaces.DzIter 1 Ψ) z θ := by
    show z * Work.Spaces.pz (Work.Spaces.pthIter 3 Ψ) z θ = _
    rw [hcl, hDz, hmul]
  rw [h1, h2]


/-- The two `z`-identities relating the shifted slice to `A = z²∂_z²Ψ` and to `D_z²Ψ`. -/
theorem slot11_z_identities {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.DzIter 1 (slot11A Ψ) z θ
        = z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ)
    ∧ (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      z * Work.Spaces.pz (Work.Spaces.DzIter 1 Ψ) z θ
        = Work.Spaces.DzIter 2 Ψ z θ) := by
  constructor
  · intro z θ hz hθ hθ'
    exact (Work.FTS.EllipticEst.remov.Dz_slice_identities Ψ hΨ).1 z θ hz hθ hθ'
  · intro z θ hz hθ hθ'
    rw [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero]
    rfl


/-! ## The algebra of the two weights

The `(1,1)`-mixed slot of `∂_θθ f` carries the weight `Wt = w·sin(2θ)^{-γ/2}`, and the third
`θ`-derivative of the shifted slice carries `w·sin(2θ)^{(2-γ)/2}`; the pointwise identity
`mixed 1 1 (∂_θθf) = sin(2θ)·∂_θ³(D_zf)` therefore converts one into the other. -/

/-- The elementary real-power identity behind the conversion. -/
theorem slot11_rpow_alg {γ s Y w : ℝ} (hs : 0 < s) :
    (s * Y * (w * s ^ (-(γ / 2)))) ^ 2 = w ^ 2 * Y ^ 2 * s ^ (2 - γ) := by
  have hs0 : 0 ≤ s := le_of_lt hs
  have hX : (s ^ (-(γ / 2))) ^ 2 = s ^ (-γ) := by
    rw [← Real.rpow_two (s ^ (-(γ / 2))), ← Real.rpow_mul hs0 (-(γ / 2)) 2]
    congr 1
    ring
  have hY : s ^ 2 * s ^ (-γ) = s ^ (2 - γ) := by
    rw [← Real.rpow_two s, ← Real.rpow_add hs 2 (-γ)]
    congr 1
  calc (s * Y * (w * s ^ (-(γ / 2)))) ^ 2
      = (s ^ 2 * Y ^ 2) * (w ^ 2 * (s ^ (-(γ / 2))) ^ 2) := by ring
    _ = (s ^ 2 * Y ^ 2) * (w ^ 2 * s ^ (-γ)) := by rw [hX]
    _ = w ^ 2 * Y ^ 2 * (s ^ 2 * s ^ (-γ)) := by ring
    _ = w ^ 2 * Y ^ 2 * s ^ (2 - γ) := by rw [hY]

/-- **The integrand identity of the `(1,1)`-slot.**  On the open quadrant, the squared weighted
`(1,1)`-slot of `∂_θθf` is `w²·(∂_θ³(D_zf))²·sin(2θ)^{2-γ}`. -/
theorem slot11_sq_eq {α : ℝ} {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (Work.Spaces.mixed 1 1 (Work.Spaces.pthIter 2 f) z θ * Work.Spaces.Wt α z θ) ^ 2
        = (Work.Spaces.w z) ^ 2
            * (Work.Spaces.pthIter 3 (Work.Spaces.DzIter 1 f) z θ) ^ 2
            * Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α) := by
  intro z θ hz hθ hθ'
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [hθ', Real.pi_pos])
  have hkey := slot11_rpow_alg (γ := Work.Spaces.gam α) (s := Real.sin (2 * θ))
    (Y := Work.Spaces.pthIter 3 (Work.Spaces.DzIter 1 f) z θ) (w := Work.Spaces.w z) hs
  rw [slot11_mixed_eq hf z θ hz hθ hθ']
  rw [show Work.Spaces.Wt α z θ
      = Work.Spaces.w z * Real.rpow (Real.sin (2 * θ)) (-(Work.Spaces.gam α / 2)) from rfl]
  exact hkey

end Work.FTS.EllipticEst.H2W
end
end
-- ===== merged: Submission.Work.FTS.LocDataExt.LocG5 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocDataExt

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The radial bound for the far summand -/


/-! ## The jet bound for `zfarR L` on all of `[L,∞)` -/


/-! ## The pointwise majorant of the `ℋ⁵`-integrand of `locG`, and the membership -/

/-- The localised perturbation as the sum of its far and bump parts (pointwise). -/
theorem locG_split (α L β : ℝ) :
    Work.FTS.LocData.locG α L β (Work.FTS.LocData.hLoc α)
      = fun z θ => (-(α / Work.Spaces.c α) * zfarR L z) * Work.Spaces.Gam α θ
          + (β * Work.FTS.LocData.bumpZ z) * Work.Spaces.Gam α θ := by
  funext z θ
  rw [locG_eq_locR_Gam]
  change locR α L β z * Work.Spaces.Gam α θ
    = -(α / Work.Spaces.c α) * zfarR L z * Work.Spaces.Gam α θ
      + β * Work.FTS.LocData.bumpZ z * Work.Spaces.Gam α θ
  rw [locR_apply]
  ring




/-! ## The order-`5` deliverable -/


end Work.FTS.LocDataExt
end
end
