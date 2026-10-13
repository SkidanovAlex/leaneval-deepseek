import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.H2W.AeProof.AeSigma.AeHkMemU
import Submission.Work.FTS.EllipticEst.AeS1.DzAgmonClean
import Submission.Work.FTS.EllipticEst.H2W.AeProof.AeSliceMomentFinite
import Submission.Work.FTS.EllipticEst.Endpt.boxIntegrable_pzPsi
import Submission.Work.FTS.EllipticEst.Endpt.boxIntegrable_pzIter2Psi
import Submission.Work.FTS.EllipticEst.Endpt.integrableOn_fstar_pzIter2
import Submission.Work.FTS.EllipticEst.Endpt.sliceBdd_of_hmB
import Submission.Work.FTS.EllipticEst.moment_relation
import Submission.Work.FTS.EllipticEst.H2W.PsiSlices.AeBasic
import Submission.Work.FTS.EllipticEst.remov.wsAux
import Submission.Work.FTS.EllipticEst.remov.SourceBound.sliceTendstoZeroOfMoment
import Submission.Work.FTS.EllipticEst.Honest.HonSliceLimitZero
import Submission.Work.FTS.EllipticEst.sliceLimitLeftExists
import Submission.Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo
import Submission.Work.FTS.EllipticEst.H2W.SliceEtaFacts

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

/-- **The left trace of a slice of a weak level-`0` datum vanishes almost everywhere.** -/
theorem weakEndLimitLeftClean (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 0 F Ψ) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Filter.Tendsto (fun θ => Ψ z θ) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
  sliceLeftTendstoClean α Ψ F (aeData_of_ellWeakPos hα hα4 h)

end Work.FTS.EllipticEst.H2W.AeLeftClean
