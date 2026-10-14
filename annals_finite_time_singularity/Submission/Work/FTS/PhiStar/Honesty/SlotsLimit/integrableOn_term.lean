import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.SliceAux
import Submission.Work.FTS.EllipticEst.SliceDecompDefs
import Submission.Work.FTS.EllipticEst.ThetaSliceIdent
import Submission.Work.FTS.EllipticEst.ThetaU.OpenSliceDefs
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.H2.ModalSol.Defs
import Submission.Work.FTS.H2.STBasic
import Submission.Work.FTS.H2.Transport1Aux
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.OpenPkg.ProdOpen.Tools1d
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.WProductRule
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.dthU_Gam
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.mixed_sq_integrableOn
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
import Submission.Work.Stability.CutFactorFderivZero
import Submission.Work.StabilityFar.Profile.exists_Fstar_add_ge
-- ===== merged: Submission.Work.Blocks.SmoothHalfAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.HalfU

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

/-! ## The half-strip and its smoothness class -/

/-- The half-strip `(0,∞) × (-1, π/2+1)` of the smoothness class `SmoothHalf`. -/
def U : Set (ℝ × ℝ) := Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)

theorem isOpen_U : IsOpen U := isOpen_Ioi.prod isOpen_Ioo

theorem mem_U {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) :
    (z, θ) ∈ U := ⟨hz, hθ⟩

theorem Iθ_subset_Ioo : Work.Spaces.Iθ ⊆ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1) := by
  intro θ hθ
  rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
  exact ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

/-- Membership of a point of the closed quadrant with `z > 0` in the half-strip. -/
theorem mem_U_of_Iθ {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Work.Spaces.Iθ) : (z, θ) ∈ U :=
  mem_U hz (Iθ_subset_Ioo hθ)

/-- **The smoothness class of the half-strip**: `f` is smooth on `U = (0,∞) × (-1, π/2+1)`.

This is the second conjunct of `Work.FTS.EllipticEst.SmoothHalf`; it is separated here
because the per-`z` estimates only use the half-strip smoothness (the smoothness of the
angular slices at `z = 0` recorded by the first conjunct of `SmoothHalf` is not needed for
the *slice* estimates at a fixed level `z > 0`; the iterates `D_z^j f`, `∂_θ^i f` inherit
their slice smoothness at `z > 0` from `HalfAn` alone). -/
def HalfAn (f : ℝ → ℝ → ℝ) : Prop := ContDiffOn ℝ ⊤ (Function.uncurry f) U



theorem HalfAn.contDiffAt {f : ℝ → ℝ → ℝ} (h : HalfAn f) {z θ : ℝ} (hy : (z, θ) ∈ U) :
    ContDiffAt ℝ ⊤ (Function.uncurry f) (z, θ) :=
  ContDiffOn.contDiffAt h (isOpen_U.mem_nhds hy)

/-! ## Closure under the partial derivatives -/

theorem HalfAn.pz {f : ℝ → ℝ → ℝ} (h : HalfAn f) : HalfAn (Work.Spaces.pz f) :=
  Work.Spaces.contDiffOn_uncurry_pz isOpen_U h

theorem HalfAn.pth {f : ℝ → ℝ → ℝ} (h : HalfAn f) : HalfAn (Work.Spaces.pth f) :=
  Work.Spaces.contDiffOn_uncurry_pth isOpen_U h

theorem HalfAn.Dz {f : ℝ → ℝ → ℝ} (h : HalfAn f) : HalfAn (Work.Spaces.Dz f) := by
  have hfun : Function.uncurry (Work.Spaces.Dz f)
      = fun p : ℝ × ℝ => p.1 * Function.uncurry (Work.Spaces.pz f) p := by
    funext p; rcases p with ⟨z, θ⟩; rfl
  rw [HalfAn, hfun]
  exact contDiffOn_fst.mul h.pz

theorem HalfAn.Dth {f : ℝ → ℝ → ℝ} (h : HalfAn f) : HalfAn (Work.Spaces.Dth f) := by
  have hfun : Function.uncurry (Work.Spaces.Dth f)
      = fun p : ℝ × ℝ => Real.sin (2 * p.2) * Function.uncurry (Work.Spaces.pth f) p := by
    funext p; rcases p with ⟨z, θ⟩; rfl
  rw [HalfAn, hfun]
  have hsin : ContDiffOn ℝ ⊤ (fun p : ℝ × ℝ => Real.sin (2 * p.2)) U :=
    (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn
  exact hsin.mul h.pth

theorem HalfAn.DzIter {f : ℝ → ℝ → ℝ} (h : HalfAn f) :
    ∀ j : ℕ, HalfAn (Work.Spaces.DzIter j f)
  | 0 => h
  | j + 1 => (HalfAn.DzIter h j).Dz

theorem HalfAn.DthIter {f : ℝ → ℝ → ℝ} (h : HalfAn f) :
    ∀ i : ℕ, HalfAn (Work.Spaces.DthIter i f)
  | 0 => h
  | i + 1 => (HalfAn.DthIter h i).Dth

theorem HalfAn.pthIter {f : ℝ → ℝ → ℝ} (h : HalfAn f) :
    ∀ m : ℕ, HalfAn (Work.Spaces.pthIter m f)
  | 0 => h
  | m + 1 => (HalfAn.pthIter h m).pth

theorem HalfAn.mixed {f : ℝ → ℝ → ℝ} (h : HalfAn f) (j i : ℕ) :
    HalfAn (Work.Spaces.mixed j i f) := (h.DthIter i).DzIter j

/-! ## Smoothness of the angular slices at a level `z > 0` -/

theorem HalfAn.slice {f : ℝ → ℝ → ℝ} (h : HalfAn f) {z : ℝ} (hz : 0 < z) :
    SliceSmooth (fun θ => f z θ) := by
  have hp : ContDiffOn ℝ ⊤ (fun t : ℝ => (z, t)) (Set.Ioo (-1) (Real.pi / 2 + 1)) :=
    contDiffOn_const.prodMk contDiffOn_id
  have hmap : Set.MapsTo (fun t : ℝ => (z, t)) (Set.Ioo (-1) (Real.pi / 2 + 1)) U :=
    fun t ht => ⟨hz, ht⟩
  have hcomp := h.comp hp hmap
  simpa [SliceSmooth, Function.comp_def, Function.uncurry] using hcomp





/-! ## Locality on the half-strip -/

theorem Dz_congr_on {g g' : ℝ → ℝ → ℝ}
    (h : Set.EqOn (Function.uncurry g) (Function.uncurry g') U) :
    Set.EqOn (Function.uncurry (Work.Spaces.Dz g)) (Function.uncurry (Work.Spaces.Dz g')) U := by
  intro y hy
  have hp := Work.Spaces.pz_congr_of_isOpen isOpen_U h hy
  show y.1 * Work.Spaces.pz g y.1 y.2 = y.1 * Work.Spaces.pz g' y.1 y.2
  rw [hp]

theorem Dth_congr_on {g g' : ℝ → ℝ → ℝ}
    (h : Set.EqOn (Function.uncurry g) (Function.uncurry g') U) :
    Set.EqOn (Function.uncurry (Work.Spaces.Dth g)) (Function.uncurry (Work.Spaces.Dth g')) U := by
  intro y hy
  have hp := Work.Spaces.pth_congr_of_isOpen isOpen_U h hy
  show Real.sin (2 * y.2) * Work.Spaces.pth g y.1 y.2
      = Real.sin (2 * y.2) * Work.Spaces.pth g' y.1 y.2
  rw [hp]


/-! ## Commutation identities on the half-strip -/

/-- One step of the commutation: `∂_θ (D_z g) = D_z (∂_θ g)` at a point of the half-strip. -/
theorem pth_Dz_apply {g : ℝ → ℝ → ℝ} {y : ℝ × ℝ} (hy : y ∈ U) (hg : HalfAn g) :
    Work.Spaces.pth (Work.Spaces.Dz g) y.1 y.2 = Work.Spaces.Dz (Work.Spaces.pth g) y.1 y.2 := by
  have h2 : ContDiffAt ℝ 2 (Function.uncurry g) y := (hg.contDiffAt hy).of_le (by norm_num)
  have h1 : Work.Spaces.pth (Work.Spaces.Dz g) y.1 y.2
      = y.1 * Work.Spaces.pth (Work.Spaces.pz g) y.1 y.2 := by
    show deriv (fun θ' => y.1 * Work.Spaces.pz g y.1 θ') y.2
      = y.1 * deriv (fun θ' => Work.Spaces.pz g y.1 θ') y.2
    rw [deriv_const_mul_field]
  have h3 : Work.Spaces.pth (Work.Spaces.pz g) y.1 y.2
      = Work.Spaces.pz (Work.Spaces.pth g) y.1 y.2 :=
    (Work.Spaces.pz_pth_comm (f := g) h2).symm
  have h4 : Work.Spaces.Dz (Work.Spaces.pth g) y.1 y.2
      = y.1 * Work.Spaces.pz (Work.Spaces.pth g) y.1 y.2 := rfl
  rw [h1, h3, h4]

/-- On the half-strip, the angular derivative of the `j`-th `D_z`-iterate of `Φ` is the
`j`-th `D_z`-iterate of its angular derivative. -/
theorem pth_DzIter_eqOn {Φ : ℝ → ℝ → ℝ} (hΦ : HalfAn Φ) (j : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.pth (Work.Spaces.DzIter j Φ)))
      (Function.uncurry (Work.Spaces.DzIter j (Work.Spaces.pth Φ))) U := by
  induction j with
  | zero => intro y hy; rfl
  | succ j ih =>
    intro y hy
    have hs : HalfAn (Work.Spaces.DzIter j Φ) := hΦ.DzIter j
    have hstep : Function.uncurry (Work.Spaces.pth (Work.Spaces.Dz (Work.Spaces.DzIter j Φ))) y
        = Function.uncurry (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter j Φ))) y :=
      pth_Dz_apply hy hs
    have hcongr : Function.uncurry (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter j Φ))) y
        = Function.uncurry (Work.Spaces.Dz (Work.Spaces.DzIter j (Work.Spaces.pth Φ))) y :=
      Dz_congr_on ih hy
    show Function.uncurry (Work.Spaces.pth (Work.Spaces.DzIter (j+1) Φ)) y
        = Function.uncurry (Work.Spaces.DzIter (j+1) (Work.Spaces.pth Φ)) y
    rw [show Work.Spaces.DzIter (j+1) Φ = Work.Spaces.Dz (Work.Spaces.DzIter j Φ) from rfl,
        show Work.Spaces.DzIter (j+1) (Work.Spaces.pth Φ)
          = Work.Spaces.Dz (Work.Spaces.DzIter j (Work.Spaces.pth Φ)) from rfl]
    exact hstep.trans hcongr

/-- `D_θ` can be moved across any iterate of `D_z`, on the half-strip. -/
theorem Dth_DzIter_comm_eqOn {f : ℝ → ℝ → ℝ} (h : HalfAn f) (b : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.Dth (Work.Spaces.DzIter b f)))
      (Function.uncurry (Work.Spaces.DzIter b (Work.Spaces.Dth f))) U := by
  induction b with
  | zero => intro y hy; rfl
  | succ b ih =>
      intro y hy
      have hc : Work.Spaces.Dz (Work.Spaces.Dth (Work.Spaces.DzIter b f)) y.1 y.2
          = Work.Spaces.Dth (Work.Spaces.Dz (Work.Spaces.DzIter b f)) y.1 y.2 :=
        Work.Spaces.Dz_Dth_comm (((h.DzIter b).contDiffAt hy).of_le (by norm_num))
      have hpz := Work.Spaces.pz_congr_of_isOpen isOpen_U ih hy
      show Work.Spaces.Dth (Work.Spaces.Dz (Work.Spaces.DzIter b f)) y.1 y.2
          = Work.Spaces.Dz (Work.Spaces.DzIter b (Work.Spaces.Dth f)) y.1 y.2
      rw [← hc]
      show y.1 * Work.Spaces.pz (Work.Spaces.Dth (Work.Spaces.DzIter b f)) y.1 y.2
          = y.1 * Work.Spaces.pz (Work.Spaces.DzIter b (Work.Spaces.Dth f)) y.1 y.2
      rw [hpz]

/-- The iterates of `D_θ` can be moved across any iterate of `D_z`, on the half-strip. -/
theorem DthIter_DzIter_comm_eqOn {f : ℝ → ℝ → ℝ} (h : HalfAn f) (b i : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DthIter i (Work.Spaces.DzIter b f)))
      (Function.uncurry (Work.Spaces.DzIter b (Work.Spaces.DthIter i f))) U := by
  induction i with
  | zero => intro y hy; rfl
  | succ i ih =>
      intro y hy
      have hDth : Work.Spaces.Dth (Work.Spaces.DthIter i (Work.Spaces.DzIter b f)) y.1 y.2
          = Work.Spaces.Dth (Work.Spaces.DzIter b (Work.Spaces.DthIter i f)) y.1 y.2 :=
        Dth_congr_on ih hy
      have hstep : Work.Spaces.Dth (Work.Spaces.DzIter b (Work.Spaces.DthIter i f)) y.1 y.2
          = Work.Spaces.DzIter b (Work.Spaces.Dth (Work.Spaces.DthIter i f)) y.1 y.2 :=
        Dth_DzIter_comm_eqOn (h.DthIter i) b hy
      show Work.Spaces.Dth (Work.Spaces.DthIter i (Work.Spaces.DzIter b f)) y.1 y.2
          = Work.Spaces.DzIter b (Work.Spaces.Dth (Work.Spaces.DthIter i f)) y.1 y.2
      rw [hDth, hstep]

/-- `D_θ^i (D_z^j f) = D_z^j D_θ^i f` at a point of the closed quadrant with `z > 0`. -/
theorem DthIter_DzIter_eq_mixed {f : ℝ → ℝ → ℝ} (h : HalfAn f) (j i : ℕ) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.DthIter i (Work.Spaces.DzIter j f) z θ = Work.Spaces.mixed j i f z θ :=
  DthIter_DzIter_comm_eqOn h j i (mem_U_of_Iθ hz hθ)


/-! ## The slice identities

These are the ports of `Work.FTS.EllipticEst.ThetaSliceIdent` (and of `SliceAux.sliceV_DzIter`)
to the half-strip, where the identities are available at every level `z > 0`. -/









/-! ## The integrability layer -/


private lemma measurable_Wt_right (α z : ℝ) :
    Measurable (fun θ : ℝ => Work.Spaces.Wt α z θ) := by
  have hsin : Measurable (fun θ : ℝ => Real.sin (2 * θ)) :=
    Real.measurable_sin.comp (measurable_const.mul measurable_id)
  have hpow : Measurable (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) :=
    hsin.pow_const _
  have : Measurable (fun θ : ℝ => Work.Spaces.w z *
      (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) := measurable_const.mul hpow
  simpa [Work.Spaces.Wt, Work.Spaces.wTheta] using this


private lemma w_ne_zero_of_pos {z : ℝ} (hz : 0 < z) : Work.Spaces.w z ≠ 0 := by
  have h1 : (1 + z) ^ 2 ≠ 0 := pow_ne_zero 2 (by linarith)
  have h2 : z ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hz)
  rw [Work.Spaces.w]
  exact div_ne_zero h1 h2




end Work.FTS.EllipticEst.HalfU

namespace Work.FTS.EllipticEst


end Work.FTS.EllipticEst
end
end
-- ===== merged: Submission.Work.EllipticEst.ModalSolution.bslOp_ibp =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.EllipticEst.ModalSolution

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## Slices of `C²` functions -/

/-- The `z`-slice of a `C²` function on a product of sets is `C²`. -/
theorem contDiffOn_slice_z_two {G : ℝ → ℝ → ℝ} {s t : Set ℝ}
    (hG : ContDiffOn ℝ 2 (Function.uncurry G) (s ×ˢ t)) {θ : ℝ} (hθ : θ ∈ t) :
    ContDiffOn ℝ 2 (fun z => G z θ) s := by
  have h1 : ContDiffOn ℝ 2 (fun z : ℝ => (z, θ)) s :=
    contDiffOn_id.prodMk (contDiffOn_const (c := θ))
  exact (hG.comp h1 (fun z _ => ⟨by assumption, hθ⟩)).congr (fun z _ => rfl)

/-- The `θ`-slice of a `C²` function on a product of sets is `C²`. -/
theorem contDiffOn_slice_θ_two {G : ℝ → ℝ → ℝ} {s t : Set ℝ}
    (hG : ContDiffOn ℝ 2 (Function.uncurry G) (s ×ˢ t)) {z : ℝ} (hz : z ∈ s) :
    ContDiffOn ℝ 2 (fun θ => G z θ) t := by
  have h1 : ContDiffOn ℝ 2 (fun θ : ℝ => (z, θ)) t :=
    (contDiffOn_const (c := z)).prodMk contDiffOn_id
  exact (hG.comp h1 (fun θ _ => ⟨hz, by assumption⟩)).congr (fun θ _ => rfl)

/-! ## `Lzero` on a slice -/


/-! ## The radial part of `bslOp`, the weight, and the integrands -/

/-- The radial part `Rz α Ψ = -(α²z²∂_zzΨ + α(5+α)z∂_zΨ)` of `bslOp α`. -/
private def Rz (α : ℝ) (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => -(α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ
    + α * (5 + α) * z * Work.Spaces.pz Ψ z θ)

/-- The weight `w(z,θ) = z^{(5-α)/α} cos θ`. -/
private def weight (α : ℝ) (p : ℝ × ℝ) : ℝ := p.1 ^ ((5 - α) / α) * Real.cos p.2

private def DI (α : ℝ) (u φ : ℝ → ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun p => u p.1 p.2 * Work.Elliptic.bslOp α φ p.1 p.2 * weight α p

private def DJ (α : ℝ) (u φ : ℝ → ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun p => Work.Elliptic.bslOp α u p.1 p.2 * φ p.1 p.2 * weight α p

/-- The integrand of the difference of the two sides. -/
private def DD (α : ℝ) (u φ : ℝ → ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun p => DI α u φ p - DJ α u φ p

/-- The radial contribution to `DD`. -/
private def Drad (α : ℝ) (u φ : ℝ → ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun p => (u p.1 p.2 * Rz α φ p.1 p.2 - Rz α u p.1 p.2 * φ p.1 p.2) * weight α p

/-- The angular contribution to `DD`. -/
private def Dang (α : ℝ) (u φ : ℝ → ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun p => (u p.1 p.2 * Work.Elliptic.Lzero φ p.1 p.2
    - Work.Elliptic.Lzero u p.1 p.2 * φ p.1 p.2) * weight α p

/-- `bslOp = Rz + Lzero`, hence `DD = Drad + Dang` pointwise. -/
theorem DD_eq (α : ℝ) (u φ : ℝ → ℝ → ℝ) (p : ℝ × ℝ) :
    DD α u φ p = Drad α u φ p + Dang α u φ p := by
  simp only [DD, DI, DJ, Drad, Dang, Rz, Work.Elliptic.bslOp_apply]
  ring

/-! ## Continuity of the required pieces on the open quadrant -/

theorem isOpen_Q0 : IsOpen Work.FTS.EllipticEst.Q0 := Work.FTS.EllipticEst.isOpen_Q0

/-- `tan θ` is continuous on the open quadrant. -/
theorem continuousOn_tan_quad :
    ContinuousOn (fun p : ℝ × ℝ => Real.tan p.2) Work.FTS.EllipticEst.Q0 := by
  rw [show (fun p : ℝ × ℝ => Real.tan p.2) = fun p => Real.sin p.2 / Real.cos p.2 from by
    funext p; rw [Real.tan_eq_sin_div_cos]]
  refine ContinuousOn.div ((Real.continuous_sin.comp continuous_snd).continuousOn)
    ((Real.continuous_cos.comp continuous_snd).continuousOn) ?_
  intro p hp
  have hp2 : p.2 ∈ Set.Ioo 0 (π / 2) := (Work.FTS.EllipticEst.mem_Q0.mp hp).2
  exact (Real.cos_pos_of_mem_Ioo ⟨by linarith [hp2.1, Real.pi_pos],
    by linarith [hp2.2]⟩).ne'

theorem contDiffOn_pthIter_two {Ψ : ℝ → ℝ → ℝ}
    (hΨ : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry Ψ)
      Work.FTS.EllipticEst.Q0) :
    ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.pthIter 2 Ψ)) Work.FTS.EllipticEst.Q0 := by
  have h := Work.FTS.LocData.contDiffOn_pth isOpen_Q0
    (Work.FTS.LocData.contDiffOn_pth isOpen_Q0 hΨ)
  simpa only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero] using h

theorem contDiffOn_pzIter_two {Ψ : ℝ → ℝ → ℝ}
    (hΨ : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry Ψ)
      Work.FTS.EllipticEst.Q0) :
    ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.pzIter 2 Ψ)) Work.FTS.EllipticEst.Q0 := by
  have h := Work.FTS.LocData.contDiffOn_pz isOpen_Q0
    (Work.FTS.LocData.contDiffOn_pz isOpen_Q0 hΨ)
  simpa only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero] using h

/-- `Lzero Ψ` is continuous on the open quadrant for `Ψ` smooth there. -/
theorem continuousOn_Lzero {Ψ : ℝ → ℝ → ℝ}
    (hΨ : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry Ψ)
      Work.FTS.EllipticEst.Q0) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.Lzero Ψ p.1 p.2)
      Work.FTS.EllipticEst.Q0 := by
  have hpth : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.pth Ψ)) Work.FTS.EllipticEst.Q0 :=
    Work.FTS.LocData.contDiffOn_pth isOpen_Q0 hΨ
  have hpth2 : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.pthIter 2 Ψ)) Work.FTS.EllipticEst.Q0 :=
    contDiffOn_pthIter_two hΨ
  have hcont : ContinuousOn (fun p : ℝ × ℝ => -(Work.Spaces.pthIter 2 Ψ p.1 p.2)
      + (Ψ p.1 p.2 / Real.cos p.2 ^ 2 + Real.tan p.2 * Work.Spaces.pth Ψ p.1 p.2)
      - 6 * Ψ p.1 p.2) Work.FTS.EllipticEst.Q0 := by
    have h1 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pthIter 2 Ψ p.1 p.2)
        Work.FTS.EllipticEst.Q0 := hpth2.continuousOn
    have h2 : ContinuousOn (fun p : ℝ × ℝ => Ψ p.1 p.2) Work.FTS.EllipticEst.Q0 :=
      hΨ.continuousOn
    have h3 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pth Ψ p.1 p.2)
        Work.FTS.EllipticEst.Q0 := hpth.continuousOn
    have hcos : ContinuousOn (fun p : ℝ × ℝ => Real.cos p.2) Work.FTS.EllipticEst.Q0 :=
      (Real.continuous_cos.comp continuous_snd).continuousOn
    have hcosne : ∀ p ∈ Work.FTS.EllipticEst.Q0, Real.cos p.2 ≠ 0 := by
      intro p hp
      have hp2 : p.2 ∈ Set.Ioo 0 (π / 2) := (Work.FTS.EllipticEst.mem_Q0.mp hp).2
      exact (Real.cos_pos_of_mem_Ioo ⟨by linarith [hp2.1, Real.pi_pos],
        by linarith [hp2.2]⟩).ne'
    have hdiv : ContinuousOn (fun p : ℝ × ℝ => Ψ p.1 p.2 / Real.cos p.2 ^ 2)
        Work.FTS.EllipticEst.Q0 :=
      h2.div (hcos.pow 2) (fun p hp => pow_ne_zero 2 (hcosne p hp))
    have hmul : ContinuousOn
        (fun p : ℝ × ℝ => Real.tan p.2 * Work.Spaces.pth Ψ p.1 p.2)
        Work.FTS.EllipticEst.Q0 := continuousOn_tan_quad.mul h3
    exact ((h1.neg).add (hdiv.add hmul)).sub (h2.const_mul 6)
  refine hcont.congr (fun p hp => ?_)
  show Work.Elliptic.Lzero Ψ p.1 p.2 = -(Work.Spaces.pthIter 2 Ψ p.1 p.2)
    + (Ψ p.1 p.2 / Real.cos p.2 ^ 2 + Real.tan p.2 * Work.Spaces.pth Ψ p.1 p.2)
    - 6 * Ψ p.1 p.2
  have hp1 : p.1 ∈ Set.Ioi (0 : ℝ) := (Work.FTS.EllipticEst.mem_Q0.mp hp).1
  have hp2 : p.2 ∈ Set.Ioo 0 (π / 2) := (Work.FTS.EllipticEst.mem_Q0.mp hp).2
  have hcosne : Real.cos p.2 ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [hp2.1, Real.pi_pos],
      by linarith [hp2.2]⟩).ne'
  have hslice : ContDiffOn ℝ Work.Stability.smoothOrder (fun θ' => Ψ p.1 θ')
      (Set.Ioo 0 (π / 2)) :=
    Work.FTS.LocData.contDiffOn_slice_θ hΨ hp1
  have hdiff : DifferentiableAt ℝ (fun θ' => Ψ p.1 θ') p.2 :=
    (hslice.differentiableOn Work.FTS.LocData.smoothOrder_ne_zero).differentiableAt
      (isOpen_Ioo.mem_nhds hp2)
  rw [← Work.Elliptic.pth_tan_mul Ψ p.1 p.2 hcosne hdiff]
  rfl

/-- The weight is continuous on the open quadrant. -/
theorem continuousOn_weight (α : ℝ) :
    ContinuousOn (weight α) Work.FTS.EllipticEst.Q0 := by
  have h1 : ContinuousOn (fun p : ℝ × ℝ => p.1 ^ ((5 - α) / α))
      Work.FTS.EllipticEst.Q0 :=
    (continuous_fst.continuousOn).rpow_const
      (fun p hp => Or.inl (ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hp).1))
  have h2 : ContinuousOn (fun p : ℝ × ℝ => Real.cos p.2) Work.FTS.EllipticEst.Q0 :=
    (Real.continuous_cos.comp continuous_snd).continuousOn
  exact h1.mul h2

/-- The radial integrand is continuous on the open quadrant. -/
theorem continuousOn_Drad (α : ℝ) {u φ : ℝ → ℝ → ℝ}
    (hu : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry u)
      Work.FTS.EllipticEst.Q0)
    (hφ : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry φ)
      Work.FTS.EllipticEst.Q0) :
    ContinuousOn (Drad α u φ) Work.FTS.EllipticEst.Q0 := by
  have hpzu : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pz u p.1 p.2)
      Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.LocData.contDiffOn_pz isOpen_Q0 hu).continuousOn
  have hpz2u : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pzIter 2 u p.1 p.2)
      Work.FTS.EllipticEst.Q0 := (contDiffOn_pzIter_two hu).continuousOn
  have hpzφ : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pz φ p.1 p.2)
      Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.LocData.contDiffOn_pz isOpen_Q0 hφ).continuousOn
  have hpz2φ : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pzIter 2 φ p.1 p.2)
      Work.FTS.EllipticEst.Q0 := (contDiffOn_pzIter_two hφ).continuousOn
  have hu' : ContinuousOn (fun p : ℝ × ℝ => u p.1 p.2) Work.FTS.EllipticEst.Q0 :=
    hu.continuousOn
  have hφ' : ContinuousOn (fun p : ℝ × ℝ => φ p.1 p.2) Work.FTS.EllipticEst.Q0 :=
    hφ.continuousOn
  have hRzφ : ContinuousOn (fun p : ℝ × ℝ => Rz α φ p.1 p.2) Work.FTS.EllipticEst.Q0 := by
    have heq : (fun p : ℝ × ℝ => Rz α φ p.1 p.2)
        = fun p : ℝ × ℝ => -(α ^ 2 * p.1 ^ 2 * Work.Spaces.pzIter 2 φ p.1 p.2
            + α * (5 + α) * p.1 * Work.Spaces.pz φ p.1 p.2) := by
      funext p; simp only [Rz]
    rw [heq]
    exact (((continuousOn_const.mul (continuous_fst.continuousOn.pow 2)).mul hpz2φ).add
      ((continuousOn_const.mul continuous_fst.continuousOn).mul hpzφ)).neg
  have hRzu : ContinuousOn (fun p : ℝ × ℝ => Rz α u p.1 p.2) Work.FTS.EllipticEst.Q0 := by
    have heq : (fun p : ℝ × ℝ => Rz α u p.1 p.2)
        = fun p : ℝ × ℝ => -(α ^ 2 * p.1 ^ 2 * Work.Spaces.pzIter 2 u p.1 p.2
            + α * (5 + α) * p.1 * Work.Spaces.pz u p.1 p.2) := by
      funext p; simp only [Rz]
    rw [heq]
    exact (((continuousOn_const.mul (continuous_fst.continuousOn.pow 2)).mul hpz2u).add
      ((continuousOn_const.mul continuous_fst.continuousOn).mul hpzu)).neg
  have hprod : ContinuousOn
      (fun p : ℝ × ℝ => u p.1 p.2 * Rz α φ p.1 p.2 - Rz α u p.1 p.2 * φ p.1 p.2)
      Work.FTS.EllipticEst.Q0 := (hu'.mul hRzφ).sub (hRzu.mul hφ')
  exact hprod.mul (continuousOn_weight α)

/-- The angular integrand is continuous on the open quadrant. -/
theorem continuousOn_Dang (α : ℝ) {u φ : ℝ → ℝ → ℝ}
    (hu : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry u)
      Work.FTS.EllipticEst.Q0)
    (hφ : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry φ)
      Work.FTS.EllipticEst.Q0) :
    ContinuousOn (Dang α u φ) Work.FTS.EllipticEst.Q0 := by
  have hu' : ContinuousOn (fun p : ℝ × ℝ => u p.1 p.2) Work.FTS.EllipticEst.Q0 :=
    hu.continuousOn
  have hφ' : ContinuousOn (fun p : ℝ × ℝ => φ p.1 p.2) Work.FTS.EllipticEst.Q0 :=
    hφ.continuousOn
  have hLφ : ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.Lzero φ p.1 p.2)
      Work.FTS.EllipticEst.Q0 := continuousOn_Lzero hφ
  have hLu : ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.Lzero u p.1 p.2)
      Work.FTS.EllipticEst.Q0 := continuousOn_Lzero hu
  have hprod : ContinuousOn
      (fun p : ℝ × ℝ => u p.1 p.2 * Work.Elliptic.Lzero φ p.1 p.2
        - Work.Elliptic.Lzero u p.1 p.2 * φ p.1 p.2) Work.FTS.EllipticEst.Q0 :=
    (hu'.mul hLφ).sub (hLu.mul hφ')
  exact hprod.mul (continuousOn_weight α)

/-! ## `bslOp` vanishes where its argument vanishes in a neighbourhood -/

/-- Every term of `bslOp α Ψ z θ` is a derivative (in `z` or `θ`) of a slice of `Ψ`, so if `Ψ`
vanishes on a neighbourhood of `(z,θ)` then `bslOp α Ψ z θ = 0`. -/
theorem bslOp_eq_zero_of_eventually_zero (α : ℝ) {Ψ : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : ∀ᶠ q in 𝓝 (z, θ), Ψ q.1 q.2 = 0) :
    Work.Elliptic.bslOp α Ψ z θ = 0 := by
  obtain ⟨V, hVU, hVopen, hzθV⟩ := mem_nhds_iff.mp h
  have hVz : ∀ᶠ z' in 𝓝 z, (z', θ) ∈ V :=
    (hVopen.preimage (continuous_id.prodMk continuous_const)).mem_nhds hzθV
  have hVt : ∀ᶠ θ' in 𝓝 θ, (z, θ') ∈ V :=
    (hVopen.preimage (continuous_const.prodMk continuous_id)).mem_nhds hzθV
  have hevZ : (fun z' => Ψ z' θ) =ᶠ[𝓝 z] (fun _ => 0) :=
    hVz.mono (fun z' hz' => hVU hz')
  have hevT : (fun θ' => Ψ z θ') =ᶠ[𝓝 θ] (fun _ => 0) :=
    hVt.mono (fun θ' ht' => hVU ht')
  have hevTtan : (fun θ' => Real.tan θ' * Ψ z θ') =ᶠ[𝓝 θ] (fun _ => 0) :=
    hVt.mono (fun θ' ht' => by
      have h0 : Ψ z θ' = 0 := hVU ht'
      simp [h0])
  have hevZ2 : (fun z' => Work.Spaces.pz Ψ z' θ) =ᶠ[𝓝 z] (fun _ => 0) := by
    filter_upwards [hVz] with z' hz'
    have hmem : ∀ᶠ z'' in 𝓝 z', (z'', θ) ∈ V :=
      (hVopen.preimage (continuous_id.prodMk continuous_const)).mem_nhds hz'
    have hev : (fun z'' => Ψ z'' θ) =ᶠ[𝓝 z'] (fun _ => 0) :=
      hmem.mono (fun z'' hz'' => hVU hz'')
    rw [show Work.Spaces.pz Ψ z' θ = deriv (fun z'' => Ψ z'' θ) z' from rfl,
      Filter.EventuallyEq.deriv_eq hev]
    simp
  have hevT2 : (fun θ' => Work.Spaces.pth Ψ z θ') =ᶠ[𝓝 θ] (fun _ => 0) := by
    filter_upwards [hVt] with θ' ht'
    have hmem : ∀ᶠ θ'' in 𝓝 θ', (z, θ'') ∈ V :=
      (hVopen.preimage (continuous_const.prodMk continuous_id)).mem_nhds ht'
    have hev : (fun θ'' => Ψ z θ'') =ᶠ[𝓝 θ'] (fun _ => 0) :=
      hmem.mono (fun θ'' hθ'' => hVU hθ'')
    rw [show Work.Spaces.pth Ψ z θ' = deriv (fun θ'' => Ψ z θ'') θ' from rfl,
      Filter.EventuallyEq.deriv_eq hev]
    simp
  have hval : Ψ z θ = 0 := hVU hzθV
  have hpz0 : Work.Spaces.pz Ψ z θ = 0 := by
    rw [show Work.Spaces.pz Ψ z θ = deriv (fun z' => Ψ z' θ) z from rfl,
      Filter.EventuallyEq.deriv_eq hevZ]
    simp
  have hpz20 : Work.Spaces.pzIter 2 Ψ z θ = 0 := by
    rw [show Work.Spaces.pzIter 2 Ψ z θ = deriv (fun z' => Work.Spaces.pz Ψ z' θ) z from rfl,
      Filter.EventuallyEq.deriv_eq hevZ2]
    simp
  have hpth20 : Work.Spaces.pthIter 2 Ψ z θ = 0 := by
    rw [show Work.Spaces.pthIter 2 Ψ z θ = deriv (fun θ' => Work.Spaces.pth Ψ z θ') θ
      from rfl, Filter.EventuallyEq.deriv_eq hevT2]
    simp
  have hpthtan : Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ = 0 := by
    rw [show Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ
        = deriv (fun θ' => Real.tan θ' * Ψ z θ') θ from rfl,
      Filter.EventuallyEq.deriv_eq hevTtan]
    simp
  rw [Work.Elliptic.bslOp_apply]
  simp only [hpz20, hpz0, Work.Elliptic.Lzero, hpth20, hpthtan, hval]
  ring

/-! ## The two one-variable IBP identities, applied to the slices -/

/-- The radial identity, applied to the slices of `u` and `φ` at the angle `θ`. -/
theorem radial_slice_zero (α : ℝ) {u φ : ℝ → ℝ → ℝ} {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hu2 : ContDiffOn ℝ 2 (Function.uncurry u) Work.FTS.EllipticEst.Q0)
    (hφ2 : ContDiffOn ℝ 2 (Function.uncurry φ) Work.FTS.EllipticEst.Q0)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) (hg0 : ∀ z, z ∉ Set.Icc a b → φ z θ = 0) :
    ∫ z in Set.Icc a b, (u z θ * Rz α φ z θ - Rz α u z θ * φ z θ)
        * z ^ ((5 - α) / α) = 0 := by
  rw [show (∫ z in Set.Icc a b, (u z θ * Rz α φ z θ - Rz α u z θ * φ z θ)
        * z ^ ((5 - α) / α))
      = ∫ z in Set.Icc a b, ((fun z' => u z' θ) z
          * (-(α ^ 2 * z ^ 2 * deriv (deriv (fun z' => φ z' θ)) z
              + α * (5 + α) * z * deriv (fun z' => φ z' θ) z))
          - (-(α ^ 2 * z ^ 2 * deriv (deriv (fun z' => u z' θ)) z
              + α * (5 + α) * z * deriv (fun z' => u z' θ) z)) * (fun z' => φ z' θ) z)
          * z ^ ((5 - α) / α) from by
    apply setIntegral_congr_fun measurableSet_Icc
    intro z hz
    simp only [Rz, Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero, Work.Spaces.pz]]
  exact radial_ibp_zero (α := α) ha hab (contDiffOn_slice_z_two hu2 hθ)
    (contDiffOn_slice_z_two hφ2 hθ) hg0

/-- The angular identity, applied to the slices of `u` and `φ` at the radius `z`. -/
theorem angular_slice_zero {u φ : ℝ → ℝ → ℝ} {c d : ℝ} (hc : 0 < c) (hcd : c < d)
    (hd : d < π / 2)
    (hu2 : ContDiffOn ℝ 2 (Function.uncurry u) Work.FTS.EllipticEst.Q0)
    (hφ2 : ContDiffOn ℝ 2 (Function.uncurry φ) Work.FTS.EllipticEst.Q0)
    {z : ℝ} (hz : z ∈ Set.Ioi 0) (hg0 : ∀ θ, θ ∉ Set.Icc c d → φ z θ = 0) :
    ∫ θ in Set.Icc c d, (u z θ * Work.Elliptic.Lzero φ z θ
        - Work.Elliptic.Lzero u z θ * φ z θ) * Real.cos θ = 0 := by
  have h := angular_ibp_zero (f := fun t => u z t) (g := fun t => φ z t) hc hcd hd
    (contDiffOn_slice_θ_two hu2 hz) (contDiffOn_slice_θ_two hφ2 hz) hg0
  refine (setIntegral_congr_fun measurableSet_Icc ?_).trans h
  intro θ hθ
  simp only [Work.Elliptic.Lzero, Work.Spaces.pth, Work.Spaces.pthIter_succ,
    Work.Spaces.pthIter_zero]

/-! ## The main theorem -/

theorem bslOp_ibp (α : ℝ) {u φ : ℝ → ℝ → ℝ}
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) Work.FTS.EllipticEst.Q0)
    (hφ : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry φ))
    (hφc : HasCompactSupport (Function.uncurry φ))
    (hφs : tsupport (Function.uncurry φ) ⊆ Work.FTS.EllipticEst.Q0)
    (h1 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => u p.1 p.2 * (Work.Elliptic.bslOp α φ p.1 p.2)
        * (p.1 ^ ((5 - α) / α) * Real.cos p.2)) Work.FTS.EllipticEst.Q0)
    (h2 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (Work.Elliptic.bslOp α u p.1 p.2) * φ p.1 p.2
        * (p.1 ^ ((5 - α) / α) * Real.cos p.2)) Work.FTS.EllipticEst.Q0) :
    (∫ p in Work.FTS.EllipticEst.Q0, u p.1 p.2 * (Work.Elliptic.bslOp α φ p.1 p.2)
        * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
      = ∫ p in Work.FTS.EllipticEst.Q0, (Work.Elliptic.bslOp α u p.1 p.2) * φ p.1 p.2
        * (p.1 ^ ((5 - α) / α) * Real.cos p.2) := by
  classical
  obtain ⟨a, b, c, d, ha, hab, hc, hcd, hd, hbox⟩ := box_of_compactSupport hφc hφs
  have hsm_u : Work.FTS.EllipticEst.SmoothOpen u :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall u).mpr hu
  have hsm_φ : Work.FTS.EllipticEst.SmoothOpen φ :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall φ).mpr (fun n => (hφ n).contDiffOn)
  have hbox_sub : Set.Icc a b ×ˢ Set.Icc c d ⊆ Work.FTS.EllipticEst.Q0 := by
    rintro ⟨z, θ⟩ ⟨hz, hθ⟩
    rw [Work.FTS.EllipticEst.mem_Q0]
    exact ⟨lt_of_lt_of_le ha hz.1, lt_of_lt_of_le hc hθ.1, lt_of_le_of_lt hθ.2 hd⟩
  have hbox_meas : MeasurableSet (Set.Icc a b ×ˢ Set.Icc c d) :=
    measurableSet_Icc.prod measurableSet_Icc
  -- ### the integrands
  have hint_Drad : MeasureTheory.IntegrableOn (Drad α u φ) (Set.Icc a b ×ˢ Set.Icc c d) :=
    ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
      ((continuousOn_Drad α hsm_u hsm_φ).mono hbox_sub)
  have hint_Dang : MeasureTheory.IntegrableOn (Dang α u φ) (Set.Icc a b ×ˢ Set.Icc c d) :=
    ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
      ((continuousOn_Dang α hsm_u hsm_φ).mono hbox_sub)
  -- ### `D` vanishes off the box
  have hzero : ∀ p ∈ Work.FTS.EllipticEst.Q0 \ (Set.Icc a b ×ˢ Set.Icc c d),
      DD α u φ p = 0 := by
    rintro ⟨z, θ⟩ ⟨hpQ, hpB⟩
    have hφ0 : φ z θ = 0 :=
      hbox (z, θ) (fun hm => hpB ⟨⟨le_of_lt hm.1.1, le_of_lt hm.1.2⟩,
        ⟨le_of_lt hm.2.1, le_of_lt hm.2.2⟩⟩)
    have hev : ∀ᶠ q in 𝓝 (z, θ), φ q.1 q.2 = 0 := by
      have hpB' : ¬ (z ∈ Set.Icc a b ∧ θ ∈ Set.Icc c d) := fun hh =>
        hpB (by simp only [Set.mem_prod]; exact hh)
      have hcases : z < a ∨ b < z ∨ θ < c ∨ d < θ := by
        by_contra hcon
        have h1 : a ≤ z := le_of_not_gt (fun h => hcon (Or.inl h))
        have h2 : z ≤ b := le_of_not_gt (fun h => hcon (Or.inr (Or.inl h)))
        have h3 : c ≤ θ := le_of_not_gt (fun h => hcon (Or.inr (Or.inr (Or.inl h))))
        have h4 : θ ≤ d := le_of_not_gt (fun h => hcon (Or.inr (Or.inr (Or.inr h))))
        exact hpB' ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
      rcases hcases with h | h | h | h
      · filter_upwards [(isOpen_Iio.prod isOpen_univ).mem_nhds
            (show (z, θ) ∈ Set.Iio a ×ˢ Set.univ from ⟨h, trivial⟩)] with q hq
        exact hbox q (fun hm => absurd hm.1.1 (not_lt.mpr (le_of_lt hq.1)))
      · filter_upwards [(isOpen_Ioi.prod isOpen_univ).mem_nhds
            (show (z, θ) ∈ Set.Ioi b ×ˢ Set.univ from ⟨h, trivial⟩)] with q hq
        exact hbox q (fun hm => absurd hm.1.2 (not_lt.mpr (le_of_lt hq.1)))
      · filter_upwards [(isOpen_univ.prod isOpen_Iio).mem_nhds
            (show (z, θ) ∈ Set.univ ×ˢ Set.Iio c from ⟨trivial, h⟩)] with q hq
        exact hbox q (fun hm => absurd hm.2.1 (not_lt.mpr (le_of_lt hq.2)))
      · filter_upwards [(isOpen_univ.prod isOpen_Ioi).mem_nhds
            (show (z, θ) ∈ Set.univ ×ˢ Set.Ioi d from ⟨trivial, h⟩)] with q hq
        exact hbox q (fun hm => absurd hm.2.2 (not_lt.mpr (le_of_lt hq.2)))
    have hbsl : Work.Elliptic.bslOp α φ z θ = 0 := bslOp_eq_zero_of_eventually_zero α hev
    simp only [DD, DI, DJ, hφ0, hbsl, mul_zero, zero_mul, sub_self]
  -- ### the angular integral vanishes
  have hAng : ∀ z ∈ Set.Icc a b, (∫ θ in Set.Icc c d, Dang α u φ (z, θ)) = 0 := by
    intro z hz
    have hz1 : z ∈ Set.Ioi (0 : ℝ) := lt_of_lt_of_le ha hz.1
    have hg0θ : ∀ θ, θ ∉ Set.Icc c d → φ z θ = 0 := fun θ hθ =>
      hbox (z, θ) (fun hm => hθ ⟨le_of_lt hm.2.1, le_of_lt hm.2.2⟩)
    have hang := angular_slice_zero hc hcd hd (hu 2) ((hφ 2).contDiffOn) hz1 hg0θ
    have hstep : (∫ θ in Set.Icc c d, Dang α u φ (z, θ))
        = z ^ ((5 - α) / α) * ∫ θ in Set.Icc c d, (u z θ * Work.Elliptic.Lzero φ z θ
            - Work.Elliptic.Lzero u z θ * φ z θ) * Real.cos θ := by
      rw [← MeasureTheory.integral_const_mul]
      exact setIntegral_congr_fun measurableSet_Icc (fun θ _ => by
        simp only [Dang, weight]; ring)
    rw [hstep, hang, mul_zero]
  have hAbox : ∫ p in (Set.Icc a b ×ˢ Set.Icc c d), Dang α u φ p = 0 := by
    rw [Measure.volume_eq_prod]
    rw [MeasureTheory.setIntegral_prod _ (by rwa [Measure.volume_eq_prod] at hint_Dang)]
    rw [show (∫ z in Set.Icc a b, ∫ θ in Set.Icc c d, Dang α u φ (z, θ))
        = ∫ z in Set.Icc a b, (0 : ℝ) from
      setIntegral_congr_fun measurableSet_Icc (fun z hz => hAng z hz)]
    simp
  -- ### the radial integral vanishes
  have hRad : ∀ θ ∈ Set.Icc c d, (∫ z in Set.Icc a b, Drad α u φ (z, θ)) = 0 := by
    intro θ hθ
    have hθ' : θ ∈ Set.Ioo 0 (π / 2) :=
      ⟨lt_of_lt_of_le hc hθ.1, lt_of_le_of_lt hθ.2 hd⟩
    have hg0z : ∀ z, z ∉ Set.Icc a b → φ z θ = 0 := fun z hz =>
      hbox (z, θ) (fun hm => hz ⟨le_of_lt hm.1.1, le_of_lt hm.1.2⟩)
    have hrad := radial_slice_zero (α := α) ha hab (hu 2) ((hφ 2).contDiffOn) hθ' hg0z
    have hstep : (∫ z in Set.Icc a b, Drad α u φ (z, θ))
        = Real.cos θ * ∫ z in Set.Icc a b, (u z θ * Rz α φ z θ - Rz α u z θ * φ z θ)
            * z ^ ((5 - α) / α) := by
      rw [← MeasureTheory.integral_const_mul]
      exact setIntegral_congr_fun measurableSet_Icc (fun z _ => by
        simp only [Drad, weight]; ring)
    rw [hstep, hrad, mul_zero]
  have hRbox : ∫ p in (Set.Icc a b ×ˢ Set.Icc c d), Drad α u φ p = 0 := by
    rw [Measure.volume_eq_prod]
    rw [MeasureTheory.setIntegral_prod _ (by rwa [Measure.volume_eq_prod] at hint_Drad)]
    rw [MeasureTheory.integral_integral_swap (μ := volume.restrict (Set.Icc a b))
      (ν := volume.restrict (Set.Icc c d)) (f := fun z θ => Drad α u φ (z, θ))
      (by
        rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
        exact hint_Drad)]
    rw [show (∫ θ in Set.Icc c d, ∫ z in Set.Icc a b, Drad α u φ (z, θ))
        = ∫ θ in Set.Icc c d, (0 : ℝ) from
      setIntegral_congr_fun measurableSet_Icc (fun θ hθ => hRad θ hθ)]
    simp
  -- ### assemble
  have hgoal : ∫ p in Work.FTS.EllipticEst.Q0, DD α u φ p = 0 := by
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero isOpen_Q0.measurableSet hbox_sub hzero]
    rw [setIntegral_congr_fun hbox_meas (fun p _ => DD_eq α u φ p)]
    rw [MeasureTheory.integral_add hint_Drad hint_Dang]
    rw [hRbox, hAbox]
    ring
  have hfinal : ∫ p in Work.FTS.EllipticEst.Q0, DI α u φ p
      = ∫ p in Work.FTS.EllipticEst.Q0, DJ α u φ p := by
    have hsub : (∫ p in Work.FTS.EllipticEst.Q0, DI α u φ p)
        - ∫ p in Work.FTS.EllipticEst.Q0, DJ α u φ p = 0 := by
      rw [← MeasureTheory.integral_sub (f := DI α u φ) (g := DJ α u φ) h1 h2]
      exact hgoal
    linarith
  exact hfinal

end Work.EllipticEst.ModalSolution
end
end
-- ===== merged: Submission.Work.EllipticEst.RegQ.DzWeak.SliceCalc =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.EllipticEst.RegQ.DzWeak

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The pointwise angular integrand of `Ptheta` -/


/-! ## The slice form of the two-variable angular iterate -/




/-! ## Clairaut and commutation, on the open quadrant -/

/-- Clairaut for the second angular derivative and the radial derivative:
`∂_θ² ∂_z f = ∂_z ∂_θ² f` on the open quadrant. -/
theorem pthIter_two_pz_eqOn {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Set.EqOn (Function.uncurry (Work.Spaces.pthIter 2 (Work.Spaces.pz f)))
      (Function.uncurry (Work.Spaces.pz (Work.Spaces.pthIter 2 f)))
      Work.FTS.EllipticEst.Q0 := by
  intro y hy
  have h2pf : ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.pth f)) y :=
    ((hf.pth).forall 2).contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hy)
  have hEqon : Set.EqOn (Function.uncurry (Work.Spaces.pz (Work.Spaces.pth f)))
      (Function.uncurry (Work.Spaces.pth (Work.Spaces.pz f)))
      Work.FTS.EllipticEst.Q0 :=
    fun y' hy' => Work.Spaces.pz_pth_comm
      ((hf.forall 2).contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hy'))
  show Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.pz f)) y.1 y.2
      = Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.pth f)) y.1 y.2
  calc Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.pz f)) y.1 y.2
      = Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.pth f)) y.1 y.2 :=
        (Work.Spaces.pth_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 hEqon hy).symm
    _ = Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.pth f)) y.1 y.2 :=
        (Work.Spaces.pz_pth_comm h2pf).symm


/-! ## The pointwise weight algebra of the `j = 0` slice group -/




/-! ## A.e. congruence on the angular interval -/






end Work.EllipticEst.RegQ.DzWeak
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cert.boxIntegrable_DzIter_layer =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Cert

open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

theorem boxIntegrable_DzIter_layer (α : ℝ) (k : ℕ) {F : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F)
    (hmem : Work.Spaces.HkMem α k F) (j : ℕ) (hj : j + 1 ≤ k) :
    ∀ a b : ℝ, 0 < a → a < b →
      MeasureTheory.IntegrableOn (Function.uncurry (fun s θ : ℝ =>
        (Work.Spaces.pz (Work.Spaces.DzIter j F) s θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) (Set.Icc a b ×ˢ Work.Spaces.Iθ) := by
  intro a b ha hab
  -- `[a,b] ⊆ Iz = [0,∞)` because `0 < a`.
  have hsub : Set.Icc a b ⊆ Work.Spaces.Iz :=
    fun x hx => Set.mem_Ici.mpr (le_trans (le_of_lt ha) hx.1)
  -- **The majorant**: the `ℋ^k`-integrand, integrable on the box.
  have hM : MeasureTheory.IntegrableOn
      (Function.uncurry (fun s θ : ℝ => Work.Spaces.HkIntegrand α k F s θ))
      (Set.Icc a b ×ˢ Work.Spaces.Iθ) :=
    Work.FTS.EllipticEst.integrableOn_box_of_slice
      (g := fun s θ : ℝ => Work.Spaces.HkIntegrand α k F s θ)
      (hF.continuousOn_HkIntegrand α k)
      (fun z θ => Work.Spaces.HkIntegrand_nonneg α k F z θ)
      ha hab
      (fun s hs => hmem.1 s (hsub hs))
      (hmem.2.mono_set hsub)
  -- **Continuity of the target integrand on the open quadrant.**
  have hsinpos : ∀ p ∈ Work.FTS.EllipticEst.Q0, 0 < Real.sin (2 * p.2) := by
    intro p hp
    obtain ⟨-, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hcont : ContinuousOn (fun p : ℝ × ℝ =>
      (Work.Spaces.pz (Work.Spaces.DzIter j F) p.1 p.2) ^ 2
        * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta))) Work.FTS.EllipticEst.Q0 := by
    refine ContinuousOn.mul ?_ ?_
    · exact (((hF.DzIter j).pz).continuousOn).pow 2
    · exact ((Real.continuous_sin.comp
          (continuous_const.mul continuous_snd)).continuousOn).rpow_const
        (fun p hp => Or.inl (by
          intro h0
          have h0' : Real.sin (2 * p.2) = 0 := h0
          have h := hsinpos p hp
          rw [h0'] at h
          exact absurd h (lt_irrefl (0 : ℝ))))
  -- **A.e. strong measurability** of the target on the box.
  have hle : (volume.restrict (Set.Icc a b)).prod (volume.restrict Work.Spaces.Iθ)
      ≤ (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ) := by
    rw [MeasureTheory.Measure.prod_restrict, MeasureTheory.Measure.prod_restrict]
    exact MeasureTheory.Measure.restrict_mono (Set.prod_mono hsub subset_rfl) le_rfl
  have hAE : AEStronglyMeasurable (Function.uncurry (fun s θ : ℝ =>
      (Work.Spaces.pz (Work.Spaces.DzIter j F) s θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))))
      (volume.restrict (Set.Icc a b ×ˢ Work.Spaces.Iθ)) := by
    have h := (Work.Spaces.aesm_of_continuousOn_Qd (fun p : ℝ × ℝ =>
      (Work.Spaces.pz (Work.Spaces.DzIter j F) p.1 p.2) ^ 2
        * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta))) hcont).mono_measure hle
    rwa [MeasureTheory.Measure.prod_restrict] at h
  refine hM.mono' hAE ?_
  -- **Pointwise bound on the box** by the `(j+1)`-slot of the `ℋ^k`-integrand.
  refine MeasureTheory.ae_restrict_of_forall_mem
    (measurableSet_Icc.prod (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)) ?_
  intro p hp
  obtain ⟨hp1, hp2⟩ := hp
  have hspos : 0 < p.1 := lt_of_lt_of_le ha hp1.1
  have hS : 0 ≤ Real.sin (2 * p.2) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hp2.1], by linarith [hp2.2, Real.pi_pos]⟩
  have hGnn : 0 ≤ (Work.Spaces.pz (Work.Spaces.DzIter j F) p.1 p.2) ^ 2
      * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)) :=
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hS _)
  simp only [Function.uncurry_def]
  rw [Real.norm_of_nonneg hGnn]
  exact le_trans
    (Work.FTS.EllipticEst.pz_DzIter_sq_mul_sin_le_term j hspos hp2)
    (Work.Spaces.sq_le_HkIntegrand_z α k F p.1 p.2 (j + 1) hj)

end Work.FTS.EllipticEst.Cert
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cert.moment_relation_layer =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cert

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## Two elementary inputs of the assembly -/

/-- A predicate which holds on the open interval `(0, π/2)` holds almost everywhere on
`Iθ = [0,π/2]`: the two endpoints form a null set. -/
private theorem ae_imp_of_mem_Ioo {p : ℝ → Prop} (h : ∀ θ ∈ Set.Ioo 0 (π / 2), p θ) :
    ∀ᵐ θ ∂(MeasureTheory.volume), θ ∈ Work.Spaces.Iθ → p θ := by
  rw [MeasureTheory.ae_iff]
  refine MeasureTheory.measure_mono_null (t := ({0, π / 2} : Set ℝ)) ?_ ?_
  · intro θ hθ
    have hθI : θ ∈ Work.Spaces.Iθ := by
      by_contra hc
      exact hθ (fun h' => absurd h' hc)
    have hpθ : ¬ p θ := fun hp => hθ (fun _ => hp)
    rw [Set.mem_insert_iff, Set.mem_singleton_iff]
    by_contra hcon
    have hcon1 : θ ≠ 0 := fun h => hcon (Or.inl h)
    have hcon2 : θ ≠ π / 2 := fun h => hcon (Or.inr h)
    rw [Work.Spaces.Iθ, Set.mem_Icc] at hθI
    exact hpθ (h θ ⟨lt_of_le_of_ne hθI.1 (Ne.symm hcon1), lt_of_le_of_ne hθI.2 hcon2⟩)
  · have hset : ({0, π / 2} : Set ℝ) = ({0} : Set ℝ) ∪ {π / 2} := by
      ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
    rw [hset]
    exact MeasureTheory.measure_union_null (MeasureTheory.measure_singleton 0)
      (MeasureTheory.measure_singleton (π / 2))

/-- Pointwise absorption of the angular weight `sinθcos²θ` by the angular weight
`sin(2θ)^{-η}` of the hypothesis `hbox`: for `θ ∈ Iθ = [0,π/2]` and every `y ∈ ℝ`,

  `|y · sinθcos²θ| ≤ (1/2) (y² · sin(2θ)^{-η} + 1)`.

Indeed `sinθcos²θ ≤ sin(2θ)/2` and `sin(2θ) ≤ sin(2θ)^{-η/2}` for `0 ≤ sin(2θ) ≤ 1`, so
`|y·sinθcos²θ| ≤ (1/2)|y| sin(2θ)^{-η/2}`, and `2ab ≤ a² + b²` with `a = |y| sin(2θ)^{-η/2}`,
`b = 1` gives the claim. -/
private lemma abs_mul_sinCos2_le_half (y θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) :
    |y * Work.Elliptic.sinCos2 θ|
      ≤ 1 / 2 * (y ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) + 1) := by
  have hθ0 : 0 ≤ θ := hθ.1
  have hθ1 : θ ≤ π / 2 := hθ.2
  have hs0 : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ0 (by linarith [Real.pi_pos])
  have hc0 : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [Real.pi_pos]) hθ1
  have hc1 : Real.cos θ ≤ 1 := Real.cos_le_one θ
  have hσ0 : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])
  have hσ1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one (2 * θ)
  have hsc0 : 0 ≤ Work.Elliptic.sinCos2 θ := by
    rw [Work.Elliptic.sinCos2]; exact mul_nonneg hs0 (pow_nonneg hc0 2)
  have hsc_le : Work.Elliptic.sinCos2 θ ≤ 1 / 2 * Real.sin (2 * θ) := by
    have hmul : Real.sin θ * Real.cos θ * Real.cos θ ≤ Real.sin θ * Real.cos θ * 1 :=
      mul_le_mul_of_nonneg_left hc1 (mul_nonneg hs0 hc0)
    rw [Work.Elliptic.sinCos2, Real.sin_two_mul]
    nlinarith [hmul]
  have h1 : |y * Work.Elliptic.sinCos2 θ| ≤ 1 / 2 * |y| * Real.sin (2 * θ) := by
    rw [abs_mul, abs_of_nonneg hsc0]
    calc |y| * Work.Elliptic.sinCos2 θ
        ≤ |y| * (1 / 2 * Real.sin (2 * θ)) := mul_le_mul_of_nonneg_left hsc_le (abs_nonneg y)
      _ = 1 / 2 * |y| * Real.sin (2 * θ) := by ring
  have hσle : Real.sin (2 * θ) ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2)) := by
    rcases eq_or_lt_of_le hσ0 with h0 | hpos
    · rw [← h0, Real.zero_rpow (by rw [Work.Spaces.eta]; norm_num)]
    · have hkey : Real.sin (2 * θ) * (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) ≤ 1 := by
        have h := Real.rpow_le_one hσ0 hσ1
          (by rw [Work.Spaces.eta]; norm_num : (0 : ℝ) ≤ 1 + Work.Spaces.eta / 2)
        rwa [Real.rpow_add hpos, Real.rpow_one] at h
      rw [Real.rpow_neg (le_of_lt hpos), ← one_div,
        le_div_iff₀ (Real.rpow_pos_of_pos hpos _)]
      exact hkey
  have hsq : (|y| * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2))) ^ 2
      = y ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    rw [mul_pow, sq_abs]
    congr 1
    rw [← Real.rpow_natCast (Real.sin (2 * θ) ^ (-(Work.Spaces.eta / 2))) 2,
      ← Real.rpow_mul hσ0]
    congr 1
    push_cast
    ring
  have hA : 2 * (|y| * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2))) * 1
      ≤ (|y| * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2))) ^ 2 + 1 ^ 2 :=
    two_mul_le_add_sq _ 1
  rw [hsq] at hA
  have hA' : 2 * (|y| * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2)))
      ≤ y ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) + 1 := by
    nlinarith [hA]
  have h3 : 1 / 2 * |y| * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2))
      ≤ 1 / 2 * (y ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) + 1) := by
    nlinarith [hA']
  calc |y * Work.Elliptic.sinCos2 θ| ≤ 1 / 2 * |y| * Real.sin (2 * θ) := h1
    _ ≤ 1 / 2 * |y| * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2)) :=
        mul_le_mul_of_nonneg_left hσle (by positivity)
    _ ≤ 1 / 2 * (y ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) + 1) := h3

/-! ## The moment relation -/

theorem moment_relation_layer (u : ℝ → ℝ → ℝ)
    (hu : Work.FTS.EllipticEst.SmoothOpen u)
    (hbox : ∀ a b : ℝ, 0 < a → a < b →
      MeasureTheory.IntegrableOn (Function.uncurry (fun s θ : ℝ => (Work.Spaces.pz u s θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) (Set.Icc a b ×ˢ Work.Spaces.Iθ))
    (hsl : ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn (fun θ : ℝ => u z θ * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    Work.Elliptic.Fstar u b = Work.Elliptic.Fstar u a
      + ∫ s in Set.Icc a b, (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.pz u s θ * Work.Elliptic.sinCos2 θ) := by
  have hb : 0 < b := lt_trans ha hab
  have hIθ_meas : MeasurableSet Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]; exact measurableSet_Icc
  -- ### joint integrability of `∂_z u · sinθcos²θ` on the box `[a,b] × Iθ`
  have hcont : ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.pz u p.1 p.2 * Work.Elliptic.sinCos2 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    ((hu.pz).continuousOn).mul (by unfold Work.Elliptic.sinCos2; fun_prop)
  have hBsub : Set.Icc a b ×ˢ Work.Spaces.Iθ ⊆ Work.Spaces.Iz ×ˢ Work.Spaces.Iθ :=
    Set.prod_mono (fun x hx => le_of_lt (lt_of_lt_of_le ha hx.1)) subset_rfl
  have hmono : (volume.restrict (Set.Icc a b)).prod (volume.restrict Work.Spaces.Iθ)
      ≤ (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ) := by
    rw [MeasureTheory.Measure.prod_restrict, MeasureTheory.Measure.prod_restrict]
    exact MeasureTheory.Measure.restrict_mono hBsub le_rfl
  have hAE : AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.Spaces.pz u p.1 p.2 * Work.Elliptic.sinCos2 p.2)
      ((volume.restrict (Set.Icc a b)).prod (volume.restrict Work.Spaces.Iθ)) :=
    (Work.Spaces.aesm_of_continuousOn_Qd _ hcont).mono_measure hmono
  have hEq : (volume.restrict (Set.Icc a b)).prod (volume.restrict Work.Spaces.Iθ)
      = volume.restrict (Set.Icc a b ×ˢ Work.Spaces.Iθ) := by
    rw [MeasureTheory.Measure.prod_restrict]; rfl
  have hGint : Integrable (fun p : ℝ × ℝ => (Work.Spaces.pz u p.1 p.2) ^ 2
      * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)))
      ((volume.restrict (Set.Icc a b)).prod (volume.restrict Work.Spaces.Iθ)) := by
    rw [hEq]
    exact hbox a b ha hab
  have hdom : Integrable (fun p : ℝ × ℝ => 1 / 2 * ((Work.Spaces.pz u p.1 p.2) ^ 2
      * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)) + 1))
      ((volume.restrict (Set.Icc a b)).prod (volume.restrict Work.Spaces.Iθ)) :=
    (hGint.add (integrable_const 1)).const_mul (1 / 2)
  have hInt : Integrable
      (Function.uncurry (fun s θ : ℝ => Work.Spaces.pz u s θ * Work.Elliptic.sinCos2 θ))
      ((volume.restrict (Set.Icc a b)).prod (volume.restrict Work.Spaces.Iθ)) := by
    refine Integrable.mono' hdom hAE ?_
    rw [MeasureTheory.Measure.prod_restrict,
      MeasureTheory.ae_restrict_iff' (measurableSet_Icc.prod hIθ_meas)]
    refine Eventually.of_forall fun p hp => ?_
    have hb' := abs_mul_sinCos2_le_half (Work.Spaces.pz u p.1 p.2) p.2 hp.2
    show ‖Work.Spaces.pz u p.1 p.2 * Work.Elliptic.sinCos2 p.2‖
      ≤ 1 / 2 * (Work.Spaces.pz u p.1 p.2 ^ 2 * Real.sin (2 * p.2) ^ (-(Work.Spaces.eta)) + 1)
    simpa only [Real.norm_eq_abs] using hb'
  -- ### the fundamental theorem of calculus along the radial slices
  have hftc : ∀ θ ∈ Set.Ioo 0 (π / 2),
      u b θ - u a θ = ∫ s in Set.Icc a b, Work.Spaces.pz u s θ := by
    intro θ hθ
    have h := Work.FTS.EllipticEst.DzIter_slice_FTC_open hu 0 ha hab.le hθ
    simp only [Work.Spaces.DzIter_zero] at h
    rw [show (∫ s in Set.Icc a b, Work.Spaces.pz u s θ)
        = ∫ r in a..b, Work.Spaces.pz u r θ from by
      rw [intervalIntegral.integral_of_le hab.le, MeasureTheory.integral_Icc_eq_integral_Ioc]]
    exact h
  -- ### the chain of equalities
  have e1 : Work.Elliptic.Fstar u b - Work.Elliptic.Fstar u a
      = ∫ θ in Work.Spaces.Iθ, (u b θ - u a θ) * Work.Elliptic.sinCos2 θ := by
    simp only [Work.Elliptic.Fstar]
    rw [show (fun θ : ℝ => (u b θ - u a θ) * Work.Elliptic.sinCos2 θ)
        = fun θ => u b θ * Work.Elliptic.sinCos2 θ
            - u a θ * Work.Elliptic.sinCos2 θ from by
      funext θ; ring]
    rw [MeasureTheory.integral_sub (hsl b hb) (hsl a ha)]
  have e2 : (∫ θ in Work.Spaces.Iθ, (u b θ - u a θ) * Work.Elliptic.sinCos2 θ)
      = ∫ θ in Work.Spaces.Iθ, (∫ s in Set.Icc a b, Work.Spaces.pz u s θ)
          * Work.Elliptic.sinCos2 θ := by
    refine MeasureTheory.setIntegral_congr_ae hIθ_meas ?_
    refine ae_imp_of_mem_Ioo fun θ hθ => ?_
    rw [hftc θ hθ]
  have e3 : (∫ θ in Work.Spaces.Iθ, (∫ s in Set.Icc a b, Work.Spaces.pz u s θ)
        * Work.Elliptic.sinCos2 θ)
      = ∫ θ in Work.Spaces.Iθ,
          (∫ s in Set.Icc a b, Work.Spaces.pz u s θ * Work.Elliptic.sinCos2 θ) := by
    refine MeasureTheory.setIntegral_congr_fun hIθ_meas fun θ _ => ?_
    exact (MeasureTheory.integral_mul_const (Work.Elliptic.sinCos2 θ)
      (fun s => Work.Spaces.pz u s θ)).symm
  have e4 : (∫ θ in Work.Spaces.Iθ,
        (∫ s in Set.Icc a b, Work.Spaces.pz u s θ * Work.Elliptic.sinCos2 θ))
      = ∫ s in Set.Icc a b, (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.pz u s θ * Work.Elliptic.sinCos2 θ) :=
    (MeasureTheory.integral_integral_swap (μ := volume.restrict (Set.Icc a b))
      (ν := volume.restrict Work.Spaces.Iθ)
      (f := fun s θ : ℝ => Work.Spaces.pz u s θ * Work.Elliptic.sinCos2 θ) hInt).symm
  have hkey := e1.trans (e2.trans (e3.trans e4))
  linarith [hkey]

end Work.FTS.EllipticEst.Cert
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Endpt.moment_chain_pz =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Endpt

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-! ## A continuous function all of whose interval integrals vanish is zero -/

/-- If `V` is continuous on `(0,∞)` and `∫_s^w V = 0` for all `0 < s ≤ w`, then `V ≡ 0` on
`(0,∞)`: the primitive of `V` starting at `z/2` has both derivative `V z` and derivative `0`
at `z`. -/
theorem eq_zero_of_forall_intervalIntegral_eq_zero_of_continuousOn {V : ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (hint : ∀ s w : ℝ, 0 < s → s ≤ w → ∫ r in s..w, V r = 0)
    (hcont : ContinuousOn V (Set.Ioi 0)) : V z = 0 := by
  set a : ℝ := z / 2 with ha
  have ha0 : 0 < a := by rw [ha]; linarith
  have haz : a < z := by rw [ha]; linarith
  have hsub : Set.uIcc a z ⊆ Set.Ioi 0 := by
    rw [Set.uIcc_of_le haz.le]
    exact fun x hx => lt_of_lt_of_le ha0 hx.1
  have hInt : IntervalIntegrable V volume a z := (hcont.mono hsub).intervalIntegrable
  have hsm : StronglyMeasurableAtFilter V (𝓝 z) volume :=
    hcont.stronglyMeasurableAtFilter isOpen_Ioi z hz
  have hderiv : HasDerivAt (fun w => ∫ r in a..w, V r) (V z) z :=
    intervalIntegral.integral_hasDerivAt_right hInt hsm
      (hcont.continuousAt (isOpen_Ioi.mem_nhds hz))
  have hev : (fun w => ∫ r in a..w, V r) =ᶠ[𝓝 z] (fun _ : ℝ => (0 : ℝ)) := by
    filter_upwards [isOpen_Ioi.mem_nhds haz] with w hw
    exact hint a w ha0 (le_of_lt hw)
  have hderiv0 : HasDerivAt (fun w => ∫ r in a..w, V r) 0 z :=
    hev.hasDerivAt_iff.mpr (hasDerivAt_const z 0)
  exact hderiv.unique hderiv0

/-! ## The moment chain -/


end Work.FTS.EllipticEst.Endpt
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.AeU2.ofReal_HkSq_eq_lintegral =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.AeU2

set_option autoImplicit false

/-! ## The collapse of the level-`0` integrand

At `k = 0` the second (mixed) sum of `Work.Spaces.HkIntegrand` is empty, so the integrand is the
single square `(g z θ · w z / sin(2θ)^{η/2})²`, whose weight square is `w z ^ 2 · sin(2θ)^{-η}`.
The angular factor is exactly `Work.FTS.EllipticEst.sEta`. -/

/-- **The level-`0` `ℋ^k`-integrand is a single weighted square.**  For `θ ∈ Iθ`,
`HkIntegrand α 0 g z θ = (w z)² · (g z θ)² · sEta θ`.  (The hypothesis `θ ∈ Iθ` is used only to
know `sin (2θ) ≥ 0`, so that `(sin(2θ)^{η/2})² = sin(2θ)^η`.) -/
theorem HkIntegrand_zero_eq (α : ℝ) (g : ℝ → ℝ → ℝ) {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 0 g z θ
      = (Work.Spaces.w z) ^ 2 * (g z θ ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
  -- the empty mixed sum, and the single `D_z`-slot at `i = 0`
  rw [show Work.Spaces.HkIntegrand α 0 g z θ
      = (g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 by
    simp [Work.Spaces.HkIntegrand]]
  -- unfold the angular weight `sEta`
  rw [show Work.FTS.EllipticEst.sEta θ
      = (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) from rfl]
  have hs : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hη : (0 : ℝ) < Work.Spaces.eta := by rw [Work.Spaces.eta]; norm_num
  have hη2 : (0 : ℝ) < Work.Spaces.eta / 2 := by linarith
  -- `(sin(2θ)^{η/2})² = sin(2θ)^η`
  have h2 : ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
      = (Real.sin (2 * θ)) ^ (Work.Spaces.eta) := by
    rcases eq_or_lt_of_le hs with h | h
    · rw [← h, Real.zero_rpow (ne_of_gt hη2), Real.zero_rpow (ne_of_gt hη)]
      norm_num
    · rw [sq, ← Real.rpow_add h (Work.Spaces.eta / 2) (Work.Spaces.eta / 2)]
      congr 1
      ring
  rw [mul_pow, div_pow, h2, div_eq_mul_inv, ← Real.rpow_neg hs]
  ring

/-- **`HkSq α 0 g` as a double `∫⁻` against the radial weight and `σ`.** -/
theorem ofReal_HkSq_eq_lintegral (α : ℝ) (g : ℝ → ℝ → ℝ) (hg : Work.Spaces.HkMem α 0 g) :
    ENNReal.ofReal (Work.Spaces.HkSq α 0 g)
      = ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
          * (∫⁻ θ in Work.Spaces.Iθ,
              ENNReal.ofReal (g z θ ^ 2 * Work.FTS.EllipticEst.sEta θ)) := by
  -- Step 1: the outer Bochner integral over `Iz` is the `lintegral` of its `ofReal`
  -- (`HkSq` is the iterated Bochner integral of the nonnegative integrand `HkIntegrand`).
  have hboch : ENNReal.ofReal (Work.Spaces.HkSq α 0 g)
      = ∫⁻ z in Work.Spaces.Iz,
          ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g z θ) :=
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal hg.2
      (Eventually.of_forall fun z =>
        integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 0 g z θ)
  rw [hboch]
  -- Step 2: pointwise in `z ∈ Iz`, the inner Bochner integral is the `∫⁻` of the collapsed
  -- integrand, and the `z`-weight is a constant that comes out of the angular `∫⁻`.
  refine MeasureTheory.lintegral_congr_ae
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => ?_)
  have hnn_inner : 0 ≤ᵐ[volume.restrict Work.Spaces.Iθ]
      fun θ => Work.Spaces.HkIntegrand α 0 g z θ :=
    Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 0 g z θ
  have hA : ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g z θ)
      = ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 g z θ) :=
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hg.1 z hz) hnn_inner
  have hB : (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 g z θ))
      = ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
          * ENNReal.ofReal (g z θ ^ 2 * Work.FTS.EllipticEst.sEta θ) :=
    MeasureTheory.lintegral_congr_ae
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ => by
        show ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 g z θ)
          = ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
            * ENNReal.ofReal (g z θ ^ 2 * Work.FTS.EllipticEst.sEta θ)
        rw [HkIntegrand_zero_eq α g hθ, ENNReal.ofReal_mul (sq_nonneg _)])
  have hC : (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
        * ENNReal.ofReal (g z θ ^ 2 * Work.FTS.EllipticEst.sEta θ))
      = ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
        * ∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal (g z θ ^ 2 * Work.FTS.EllipticEst.sEta θ) :=
    MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  show ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g z θ)
      = ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
        * ∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal (g z θ ^ 2 * Work.FTS.EllipticEst.sEta θ)
  rw [hA, hB, hC]

end Work.FTS.EllipticEst.H2W.AeU2
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.Slot11Src.aesm_pth_sq_int =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W.Slot11Src

open MeasureTheory
open scoped Real Topology

/-!
## Almost everywhere strong measurability of `w(z)² ∫_θ (∂_θG z θ)² sin(2θ)^{2-γ}`

For a source `G` which is `C^∞` on the *open* quadrant `Q0 = (0,∞) × (0,π/2)`
(`Work.FTS.EllipticEst.SmoothOpen`), the function

`z ↦ w(z)² · ∫_{Iθ} (∂_θG z θ)² · sin(2θ)^{2-γ(α)}`

is almost everywhere strongly measurable for the Lebesgue measure restricted to
`Iz = [0,∞)`.

The `θ`-integrand is continuous on `Q0`: the factor `(∂_θG)²` because `∂_θ` preserves
`C^∞` on the open quadrant (`SmoothOpen.pth`), and the weight `sin(2θ)^{2-γ}` because
`sin(2θ) ≠ 0` on `(0,π/2)` (an `rpow` with a positive base is continuous for *any* real
exponent).  So the product function is a.e. strongly measurable for the product of the
restricted measures (`Work.Spaces.aesm_of_continuousOn_Qd`), and integrating out the
`θ`-variable (`AEStronglyMeasurable.integral_prod_right'`) gives a.e. strong measurability
of the `z`-integral.  Multiplying by the continuous function `w²` (continuous on `Ioi 0`,
which is co-null in `Iz`) preserves this.
-/

/-- The weight `w` is continuous on the open half-line `(0,∞)`. -/
private theorem continuousOn_w : ContinuousOn (fun z : ℝ => Work.Spaces.w z) (Set.Ioi (0 : ℝ)) := by
  show ContinuousOn (fun z : ℝ => (1 + z) ^ 2 / z ^ 2) (Set.Ioi (0 : ℝ))
  exact ((continuous_const.add continuous_id).pow 2).continuousOn.div
    (continuous_id.pow 2).continuousOn
    (fun z hz => pow_ne_zero 2 (ne_of_gt (by simpa using hz)))

theorem aesm_pth_sq_int (α : ℝ) {G : ℝ → ℝ → ℝ} (hG : Work.FTS.EllipticEst.SmoothOpen G) :
    MeasureTheory.AEStronglyMeasurable
      (fun z : ℝ => (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.pth G z θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  -- The square of the angular derivative is continuous on the open quadrant.
  have hpth : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.pth G p.1 p.2) ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    (hG.pth).continuousOn.pow 2
  -- The weight `sin(2θ)^{2-γ(α)}` is continuous on the open interval.
  have hφc : ContinuousOn (fun θ : ℝ => Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α))
      (Set.Ioo 0 (Real.pi / 2)) := by
    have hsin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo 0 (Real.pi / 2)) :=
      (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
    refine hsin.rpow_const (fun θ hθ => Or.inl ?_)
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2]))
  have hcont : ContinuousOn
      (fun p : ℝ × ℝ => (Work.Spaces.pth G p.1 p.2) ^ 2
        * Real.rpow (Real.sin (2 * p.2)) (2 - Work.Spaces.gam α))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    hpth.mul (hφc.comp continuous_snd.continuousOn (fun p hp => hp.2))
  -- Hence it is a.e. strongly measurable for the product of the restricted measures ...
  have hprod : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => (Work.Spaces.pth G p.1 p.2) ^ 2
        * Real.rpow (Real.sin (2 * p.2)) (2 - Work.Spaces.gam α))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ hcont
  -- ... and integrating out the `θ`-variable preserves this.
  have hint : MeasureTheory.AEStronglyMeasurable
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.pth G z θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    MeasureTheory.AEStronglyMeasurable.integral_prod_right'
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
      (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ) hprod
  -- The prefactor `w²` is continuous on `(0,∞)`, which is co-null in `Iz = [0,∞)`.
  have hw : MeasureTheory.AEStronglyMeasurable (fun z : ℝ => (Work.Spaces.w z) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have h := (continuousOn_w.pow 2).aestronglyMeasurable
      (μ := MeasureTheory.volume) measurableSet_Ioi
    rw [MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := (0 : ℝ)))] at h
    exact h
  exact hw.mul hint

end Work.FTS.EllipticEst.H2W.Slot11Src
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.HonDifQuotBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Honest

set_option autoImplicit false

/-! # The mean-value bound for the `z`-difference quotient of an honest pair

The honest class `Hon` gives `C^∞`-smoothness of `Ψ` on the *open* quadrant only.  On the
interior of the quadrant the slices are therefore as smooth as one wishes, and the second-order
Taylor bound

  `|(Ψ z θ - Ψ (z - hh) θ) / hh - ∂_zΨ(z,θ)| ≤ ∫_{z-hh}^{z} |∂_z²Ψ|`

holds.  Since `hh < z/2` the interval `[z - hh, z]` is contained in `[z/2, z]`, which is the
form stated (the wider interval is the one that will be available later, when `∂_z²Ψ` is only
known to be a measurable function).

The proof is the two-step mean-value argument: `ξ ∈ (z - hh, z)` with
`(Ψ z θ - Ψ (z-hh) θ)/hh = ∂_zΨ(ξ,θ)` (Lagrange), and then `∂_zΨ(z,θ) - ∂_zΨ(ξ,θ) = ∫_ξ^z ∂_z²Ψ`
(Fundamental theorem of calculus), bounded by the integral of the absolute value over the
enlarged interval.
-/



/-! ## Generic slice facts for `C^n`-functions on an open subset of `ℝ × ℝ` -/



/-! ## The mean-value bound -/


/-! ## The honest difference-quotient bound -/


end Work.FTS.EllipticEst.Honest
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.HonDifQuotTendsto =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest


end Work.FTS.EllipticEst.Honest
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.HonEnergyDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Honest

set_option autoImplicit false






end Work.FTS.EllipticEst.Honest
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.HonSliceL1 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Honest

set_option autoImplicit false



end Work.FTS.EllipticEst.Honest
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.PthCore.contDiffOnOneExtension =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Extending a `C¹` function on `(0, π/2)` with vanishing boundary values to `[0, π/2]`

`Work.FTS.EllipticEst.Honest.PthCore.contDiffOnOneExtension`: if `f` is `C¹` on the open
interval `(0, π/2)`, has vanishing one-sided limits at the two endpoints, and the one-sided
limits of `deriv f` at the endpoints exist, then `f` has a `C¹` extension `g` to
`[0, π/2]` with `g 0 = g (π/2) = 0`, agreeing with `f` (together with its derivative) on
the open interval.

The extension used is the *piecewise linear* one:

`pthOneExt A B f x = if x ≤ 0 then A * x else if x < π/2 then f x else B * (x - π/2)`,

with `A`, `B` the one-sided limits of `deriv f`.  It is `C¹` on the open neighbourhood
`(-1, π/2 + 1)` of `[0, π/2]`; at the two junction points the derivative is computed by
l'Hôpital's rule (`HasDerivAt.lhopital_zero_nhdsGT/LT`), which is the formal substitute for
the mean value theorem here.
-/

namespace Work.FTS.EllipticEst.Honest.PthCore

open Filter Set
open scoped Topology

/-- The extension of `f` from `(0, π/2)` to `ℝ`: linear with slope `A` to the left of `0`,
`f` itself on `(0, π/2)`, and linear with slope `B` to the right of `π/2`. -/
noncomputable def pthOneExt (A B : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  if x ≤ 0 then A * x else if x < Real.pi / 2 then f x else B * (x - Real.pi / 2)

/-- Candidate for the derivative of `pthOneExt A B f`: the slope `A` on `(-∞, 0]`, `deriv f`
on `(0, π/2)` and the slope `B` on `[π/2, ∞)`. -/
noncomputable def pthOneExtDeriv (A B : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  if x ≤ 0 then A else if x < Real.pi / 2 then deriv f x else B

lemma hpi_half_pos : (0 : ℝ) < Real.pi / 2 := by linarith [Real.pi_pos]

variable {A B : ℝ} {f : ℝ → ℝ}

lemma pthOneExt_of_nonpos {x : ℝ} (hx : x ≤ 0) : pthOneExt A B f x = A * x := by
  simp only [pthOneExt, hx, ↓reduceIte]

lemma pthOneExt_of_mem {x : ℝ} (hx : x ∈ Ioo 0 (Real.pi / 2)) :
    pthOneExt A B f x = f x := by
  simp only [pthOneExt, not_le.mpr hx.1, hx.2, ↓reduceIte]

lemma pthOneExt_of_ge {x : ℝ} (hx : Real.pi / 2 ≤ x) :
    pthOneExt A B f x = B * (x - Real.pi / 2) := by
  simp only [pthOneExt, not_le.mpr (lt_of_lt_of_le hpi_half_pos hx), not_lt.mpr hx, ↓reduceIte]

lemma pthOneExt_zero : pthOneExt A B f 0 = 0 := by simp [pthOneExt]

lemma pthOneExt_pi_half : pthOneExt A B f (Real.pi / 2) = 0 := by
  rw [pthOneExt_of_ge le_rfl]; ring

lemma pthOneExt_hasDerivAt_of_neg {x : ℝ} (hx : x < 0) :
    HasDerivAt (pthOneExt A B f) A x := by
  have hev : pthOneExt A B f =ᶠ[𝓝 x] (fun y : ℝ => A * y) := by
    filter_upwards [isOpen_Iio.mem_nhds hx] with y hy
    exact pthOneExt_of_nonpos hy.le
  simpa using ((hasDerivAt_id x).const_mul A).congr_of_eventuallyEq hev

lemma pthOneExt_hasDerivAt_of_pi_half_lt {x : ℝ} (hx : Real.pi / 2 < x) :
    HasDerivAt (pthOneExt A B f) B x := by
  have hev : pthOneExt A B f =ᶠ[𝓝 x] (fun y : ℝ => B * (y - Real.pi / 2)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
    exact pthOneExt_of_ge hy.le
  have h1 : HasDerivAt (fun y : ℝ => y - Real.pi / 2) 1 x := (hasDerivAt_id' x).sub_const _
  simpa using (h1.const_mul B).congr_of_eventuallyEq hev

lemma pthOneExt_hasDerivAt_of_mem {x : ℝ} (hx : x ∈ Ioo 0 (Real.pi / 2))
    (hdf : DifferentiableAt ℝ f x) : HasDerivAt (pthOneExt A B f) (deriv f x) x := by
  have hev : pthOneExt A B f =ᶠ[𝓝 x] f := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    exact pthOneExt_of_mem hy
  exact (hdf.hasDerivAt).congr_of_eventuallyEq hev

/-- The extension is differentiable at `0`, with derivative the (one-sided) limit `A` of
`deriv f`; l'Hôpital's rule supplies the right derivative, the left one is linear. -/
lemma pthOneExt_hasDerivAt_zero (hdf : DifferentiableOn ℝ f (Ioo 0 (Real.pi / 2)))
    (h0 : Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 0)) (hA : Tendsto (deriv f) (𝓝[>] (0 : ℝ)) (𝓝 A)) :
    HasDerivAt (pthOneExt A B f) A 0 := by
  have hmem : Ioo (0 : ℝ) (Real.pi / 2) ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT hpi_half_pos
  have hder : ∀ᶠ x in 𝓝[>] (0 : ℝ), HasDerivAt (pthOneExt A B f) (deriv f x) x := by
    filter_upwards [hmem] with x hx
    exact pthOneExt_hasDerivAt_of_mem hx (hdf.differentiableAt (Ioo_mem_nhds hx.1 hx.2))
  have hone : ∀ᶠ x in 𝓝[>] (0 : ℝ), HasDerivAt (fun y : ℝ => y) (1 : ℝ) x :=
    Eventually.of_forall fun x => hasDerivAt_id' x
  have hne : ∀ᶠ x in 𝓝[>] (0 : ℝ), (1 : ℝ) ≠ 0 := Eventually.of_forall fun _ => one_ne_zero
  have hfa : Tendsto (pthOneExt A B f) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    h0.congr' (by
      filter_upwards [hmem] with x hx
      exact (pthOneExt_of_mem hx).symm)
  have hga : Tendsto (fun y : ℝ => y) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id'.mpr nhdsWithin_le_nhds
  have hdiv : Tendsto (fun x => deriv f x / (1 : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 A) := by
    simpa using hA
  have hlhop := HasDerivAt.lhopital_zero_nhdsGT hder hone hne hfa hga hdiv
  rw [hasDerivAt_iff_tendsto_slope_left_right]
  refine ⟨?_, ?_⟩
  · have hev : (fun _ : ℝ => A) =ᶠ[𝓝[<] (0 : ℝ)] slope (pthOneExt A B f) 0 := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      have hAy : A * y / y = A := by
        rw [mul_comm A y, mul_div_cancel_left₀ _ (ne_of_lt hy)]
      rw [slope_def_field, pthOneExt_of_nonpos hy.le, pthOneExt_zero, sub_zero, sub_zero, hAy]
    exact (tendsto_const_nhds : Tendsto (fun _ : ℝ => A) (𝓝[<] (0 : ℝ)) (𝓝 A)).congr' hev
  · refine hlhop.congr' ?_
    filter_upwards with x
    rw [slope_def_field, pthOneExt_zero, sub_zero, sub_zero]

/-- The extension is differentiable at `π/2`, with derivative the (one-sided) limit `B` of
`deriv f`. -/
lemma pthOneExt_hasDerivAt_pi_half (hdf : DifferentiableOn ℝ f (Ioo 0 (Real.pi / 2)))
    (h1 : Tendsto f (𝓝[<] (Real.pi / 2)) (𝓝 0))
    (hB : Tendsto (deriv f) (𝓝[<] (Real.pi / 2)) (𝓝 B)) :
    HasDerivAt (pthOneExt A B f) B (Real.pi / 2) := by
  have hmem : Ioo (0 : ℝ) (Real.pi / 2) ∈ 𝓝[<] (Real.pi / 2) := Ioo_mem_nhdsLT hpi_half_pos
  have hder : ∀ᶠ x in 𝓝[<] (Real.pi / 2), HasDerivAt (pthOneExt A B f) (deriv f x) x := by
    filter_upwards [hmem] with x hx
    exact pthOneExt_hasDerivAt_of_mem hx (hdf.differentiableAt (Ioo_mem_nhds hx.1 hx.2))
  have hone : ∀ᶠ x in 𝓝[<] (Real.pi / 2), HasDerivAt (fun y : ℝ => y - Real.pi / 2) (1 : ℝ) x :=
    Eventually.of_forall fun x => (hasDerivAt_id' x).sub_const _
  have hne : ∀ᶠ x in 𝓝[<] (Real.pi / 2), (1 : ℝ) ≠ 0 := Eventually.of_forall fun _ => one_ne_zero
  have hfa : Tendsto (pthOneExt A B f) (𝓝[<] (Real.pi / 2)) (𝓝 0) :=
    h1.congr' (by filter_upwards [hmem] with x hx; exact (pthOneExt_of_mem hx).symm)
  have hga : Tendsto (fun y : ℝ => y - Real.pi / 2) (𝓝[<] (Real.pi / 2)) (𝓝 0) := by
    have h0' : Tendsto (fun y : ℝ => y) (𝓝[<] (Real.pi / 2)) (𝓝 (Real.pi / 2)) :=
      tendsto_id'.mpr nhdsWithin_le_nhds
    have hc : Tendsto (fun _ : ℝ => Real.pi / 2) (𝓝[<] (Real.pi / 2)) (𝓝 (Real.pi / 2)) :=
      tendsto_const_nhds
    simpa using h0'.sub hc
  have hdiv : Tendsto (fun x => deriv f x / (1 : ℝ)) (𝓝[<] (Real.pi / 2)) (𝓝 B) := by
    simpa using hB
  have hlhop := HasDerivAt.lhopital_zero_nhdsLT hder hone hne hfa hga hdiv
  rw [hasDerivAt_iff_tendsto_slope_left_right]
  refine ⟨?_, ?_⟩
  · refine hlhop.congr' ?_
    filter_upwards with x
    rw [slope_def_field, pthOneExt_pi_half, sub_zero]
  · have hev : (fun _ : ℝ => B) =ᶠ[𝓝[>] (Real.pi / 2)] slope (pthOneExt A B f) (Real.pi / 2) := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      have hBy : B * (y - Real.pi / 2) / (y - Real.pi / 2) = B := by
        rw [mul_comm B (y - Real.pi / 2), mul_div_cancel_left₀ _ (sub_ne_zero.mpr (ne_of_gt hy))]
      rw [slope_def_field, pthOneExt_of_ge hy.le, pthOneExt_pi_half, sub_zero, hBy]
    exact (tendsto_const_nhds : Tendsto (fun _ : ℝ => B) (𝓝[>] (Real.pi / 2)) (𝓝 B)).congr' hev

lemma pthOneExt_deriv_of_neg {x : ℝ} (hx : x < 0) : deriv (pthOneExt A B f) x = A :=
  (pthOneExt_hasDerivAt_of_neg hx).deriv

lemma pthOneExt_deriv_of_mem {x : ℝ} (hx : x ∈ Ioo 0 (Real.pi / 2))
    (hdf : DifferentiableAt ℝ f x) : deriv (pthOneExt A B f) x = deriv f x :=
  (pthOneExt_hasDerivAt_of_mem hx hdf).deriv

lemma pthOneExt_deriv_of_pi_half_lt {x : ℝ} (hx : Real.pi / 2 < x) :
    deriv (pthOneExt A B f) x = B := (pthOneExt_hasDerivAt_of_pi_half_lt hx).deriv

/-- On the neighbourhood `(-1, π/2 + 1)` of `[0, π/2]` the derivative of the extension is the
explicit candidate `pthOneExtDeriv`. -/
lemma pthOneExt_deriv_eqOn (hdf : DifferentiableOn ℝ f (Ioo 0 (Real.pi / 2)))
    (h0 : Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 0)) (h1 : Tendsto f (𝓝[<] (Real.pi / 2)) (𝓝 0))
    (hA : Tendsto (deriv f) (𝓝[>] (0 : ℝ)) (𝓝 A)) (hB : Tendsto (deriv f) (𝓝[<] (Real.pi / 2)) (𝓝 B)) :
    EqOn (deriv (pthOneExt A B f)) (pthOneExtDeriv A B f) (Ioo (-1) (Real.pi / 2 + 1)) := by
  intro x _
  rcases lt_trichotomy x 0 with hlt | heq | hgt
  · rw [pthOneExt_deriv_of_neg hlt]
    simp only [pthOneExtDeriv, hlt.le, ↓reduceIte]
  · subst heq
    rw [(pthOneExt_hasDerivAt_zero hdf h0 hA).deriv]
    simp only [pthOneExtDeriv, le_refl, ↓reduceIte]
  · rcases lt_trichotomy x (Real.pi / 2) with h2 | h2 | h2
    · rw [pthOneExt_deriv_of_mem ⟨hgt, h2⟩ (hdf.differentiableAt (Ioo_mem_nhds hgt h2))]
      simp only [pthOneExtDeriv, not_le.mpr hgt, h2, ↓reduceIte]
    · subst h2
      rw [(pthOneExt_hasDerivAt_pi_half hdf h1 hB).deriv]
      simp only [pthOneExtDeriv, not_le.mpr hpi_half_pos, lt_irrefl (Real.pi / 2), ↓reduceIte]
    · rw [pthOneExt_deriv_of_pi_half_lt h2]
      simp only [pthOneExtDeriv, not_le.mpr (lt_trans hpi_half_pos h2), not_lt.mpr h2.le, ↓reduceIte]

/-- `pthOneExtDeriv A B f` is continuous on the neighbourhood `(-1, π/2 + 1)`. -/
lemma continuousOn_pthOneExtDeriv (hderiv : ContinuousOn (deriv f) (Ioo 0 (Real.pi / 2)))
    (hA : Tendsto (deriv f) (𝓝[>] (0 : ℝ)) (𝓝 A))
    (hB : Tendsto (deriv f) (𝓝[<] (Real.pi / 2)) (𝓝 B)) :
    ContinuousOn (pthOneExtDeriv A B f) (Ioo (-1) (Real.pi / 2 + 1)) := by
  intro x _
  rcases lt_trichotomy x 0 with hlt | heq | hgt
  · have hval : pthOneExtDeriv A B f x = A := by
      simp only [pthOneExtDeriv, hlt.le, ↓reduceIte]
    have hev : (fun _ : ℝ => A) =ᶠ[𝓝 x] pthOneExtDeriv A B f := by
      filter_upwards [isOpen_Iio.mem_nhds hlt] with y hy
      have hy' : y ≤ 0 := hy.le
      simp only [pthOneExtDeriv, hy', ↓reduceIte]
    exact ((continuousAt_const : ContinuousAt (fun _ : ℝ => A) x).congr hev).continuousWithinAt
  · subst heq
    have hval : pthOneExtDeriv A B f 0 = A := by
      simp only [pthOneExtDeriv, le_refl, ↓reduceIte]
    have hcont : ContinuousAt (pthOneExtDeriv A B f) 0 := by
      rw [continuousAt_iff_continuous_left'_right']
      refine ⟨?_, ?_⟩
      · have hev : (fun _ : ℝ => A) =ᶠ[𝓝[<] (0 : ℝ)] pthOneExtDeriv A B f := by
          filter_upwards [self_mem_nhdsWithin] with y hy
          have hy' : y ≤ 0 := hy.le
          simp only [pthOneExtDeriv, hy', ↓reduceIte]
        have h := (tendsto_const_nhds : Tendsto (fun _ : ℝ => A) (𝓝[<] (0 : ℝ)) (𝓝 A)).congr' hev
        unfold ContinuousWithinAt
        rw [hval]
        exact h
      · have hev : (fun x => deriv f x) =ᶠ[𝓝[>] (0 : ℝ)] pthOneExtDeriv A B f := by
          filter_upwards [Ioo_mem_nhdsGT hpi_half_pos] with y hy
          simp only [pthOneExtDeriv, not_le.mpr hy.1, hy.2, ↓reduceIte]
        have h := hA.congr' hev
        unfold ContinuousWithinAt
        rw [hval]
        exact h
    exact hcont.continuousWithinAt
  · rcases lt_trichotomy x (Real.pi / 2) with h2 | h2 | h2
    · have hev : (fun x => deriv f x) =ᶠ[𝓝 x] pthOneExtDeriv A B f := by
        filter_upwards [isOpen_Ioo.mem_nhds ⟨hgt, h2⟩] with y hy
        simp only [pthOneExtDeriv, not_le.mpr hy.1, hy.2, ↓reduceIte]
      exact ((hderiv.continuousAt (Ioo_mem_nhds hgt h2)).congr hev).continuousWithinAt
    · subst h2
      have hval : pthOneExtDeriv A B f (Real.pi / 2) = B := by
        simp only [pthOneExtDeriv, not_le.mpr hpi_half_pos, lt_irrefl (Real.pi / 2), ↓reduceIte]
      have hcont : ContinuousAt (pthOneExtDeriv A B f) (Real.pi / 2) := by
        rw [continuousAt_iff_continuous_left'_right']
        refine ⟨?_, ?_⟩
        · have hev : (fun x => deriv f x) =ᶠ[𝓝[<] (Real.pi / 2)] pthOneExtDeriv A B f := by
            filter_upwards [Ioo_mem_nhdsLT hpi_half_pos] with y hy
            simp only [pthOneExtDeriv, not_le.mpr hy.1, hy.2, ↓reduceIte]
          have h := hB.congr' hev
          unfold ContinuousWithinAt
          rw [hval]
          exact h
        · have hev : (fun _ : ℝ => B) =ᶠ[𝓝[>] (Real.pi / 2)] pthOneExtDeriv A B f := by
            filter_upwards [self_mem_nhdsWithin] with y hy
            have hy' : Real.pi / 2 ≤ y := hy.le
            simp only [pthOneExtDeriv, not_le.mpr (lt_trans hpi_half_pos hy), not_lt.mpr hy',
              ↓reduceIte]
          have h :=
            (tendsto_const_nhds : Tendsto (fun _ : ℝ => B) (𝓝[>] (Real.pi / 2)) (𝓝 B)).congr' hev
          unfold ContinuousWithinAt
          rw [hval]
          exact h
      exact hcont.continuousWithinAt
    · have hval : pthOneExtDeriv A B f x = B := by
        simp only [pthOneExtDeriv, not_le.mpr (lt_trans hpi_half_pos h2), not_lt.mpr h2.le,
          ↓reduceIte]
      have hev : (fun _ : ℝ => B) =ᶠ[𝓝 x] pthOneExtDeriv A B f := by
        filter_upwards [isOpen_Ioi.mem_nhds h2] with y hy
        have hy' : Real.pi / 2 ≤ y := hy.le
        simp only [pthOneExtDeriv, not_le.mpr (lt_trans hpi_half_pos hy), not_lt.mpr hy',
          ↓reduceIte]
      exact ((continuousAt_const (y := B) : ContinuousAt (fun _ : ℝ => B) x).congr
        hev).continuousWithinAt

/-- `pthOneExt A B f` is differentiable on the neighbourhood `(-1, π/2 + 1)`. -/
lemma differentiableOn_pthOneExt (hdf : DifferentiableOn ℝ f (Ioo 0 (Real.pi / 2)))
    (h0 : Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 0)) (h1 : Tendsto f (𝓝[<] (Real.pi / 2)) (𝓝 0))
    (hA : Tendsto (deriv f) (𝓝[>] (0 : ℝ)) (𝓝 A))
    (hB : Tendsto (deriv f) (𝓝[<] (Real.pi / 2)) (𝓝 B)) :
    DifferentiableOn ℝ (pthOneExt A B f) (Ioo (-1) (Real.pi / 2 + 1)) := by
  intro x _
  rcases lt_trichotomy x 0 with hlt | heq | hgt
  · exact (pthOneExt_hasDerivAt_of_neg hlt).differentiableAt.differentiableWithinAt
  · subst heq
    exact (pthOneExt_hasDerivAt_zero hdf h0 hA).differentiableAt.differentiableWithinAt
  · rcases lt_trichotomy x (Real.pi / 2) with h2 | h2 | h2
    · exact (pthOneExt_hasDerivAt_of_mem ⟨hgt, h2⟩
        (hdf.differentiableAt (Ioo_mem_nhds hgt h2))).differentiableAt.differentiableWithinAt
    · subst h2
      exact (pthOneExt_hasDerivAt_pi_half hdf h1 hB).differentiableAt.differentiableWithinAt
    · exact (pthOneExt_hasDerivAt_of_pi_half_lt h2).differentiableAt.differentiableWithinAt

theorem contDiffOnOneExtension {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioo 0 (Real.pi / 2))) (h0 : Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)) (h1 : Filter.Tendsto f (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) (h0' : ∃ L : ℝ, Filter.Tendsto (deriv f) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds L)) (h1' : ∃ L : ℝ, Filter.Tendsto (deriv f) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds L)) : ∃ g : ℝ → ℝ, ContDiffOn ℝ 1 g (Set.Icc 0 (Real.pi / 2)) ∧ g 0 = 0 ∧ g (Real.pi / 2) = 0 ∧ (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), g θ = f θ ∧ deriv g θ = deriv f θ) := by
  obtain ⟨L0, hL0⟩ := h0'
  obtain ⟨L1, hL1⟩ := h1'
  have hdf : DifferentiableOn ℝ f (Ioo 0 (Real.pi / 2)) := hf.differentiableOn (by norm_num)
  have hderiv : ContinuousOn (deriv f) (Ioo 0 (Real.pi / 2)) :=
    hf.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl
  refine ⟨pthOneExt L0 L1 f, ?_, pthOneExt_zero, pthOneExt_pi_half, ?_⟩
  · have hU : ContDiffOn ℝ 1 (pthOneExt L0 L1 f) (Ioo (-1) (Real.pi / 2 + 1)) := by
      rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl,
        contDiffOn_succ_iff_deriv_of_isOpen (n := 0) isOpen_Ioo]
      refine ⟨differentiableOn_pthOneExt hdf h0 h1 hL0 hL1, fun h => by simp at h, ?_⟩
      rw [contDiffOn_zero]
      exact (continuousOn_pthOneExtDeriv hderiv hL0 hL1).congr
        (pthOneExt_deriv_eqOn hdf h0 h1 hL0 hL1)
    exact hU.mono fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  · intro θ hθ
    refine ⟨pthOneExt_of_mem hθ, ?_⟩
    have hev : pthOneExt L0 L1 f =ᶠ[𝓝 θ] f := by
      filter_upwards [isOpen_Ioo.mem_nhds hθ] with y hy
      exact pthOneExt_of_mem hy
    exact (hev.symm.deriv_eq).symm

end Work.FTS.EllipticEst.Honest.PthCore
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.SharpHardyCosWeight =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-! # Sharp weighted Hardy inequality with a `cos²(2θ)`-weight

The target lemma `SharpHardyCosWeight` is the sharp `L²`-Hardy inequality for the singular
weight `sin(2θ)^{-(2+η)}` on `Iθ = [0, π/2]` in which the leading singularity is produced by
`cos(2θ)²` (i.e. `cos²(2θ) sin(2θ)^{-(2+η)} = cot²(2θ) sin(2θ)^{-η}`):

`∫_Iθ f² cos²(2θ) sin(2θ)^{-(2+η)} ≤ (1+η)^{-2} ∫_Iθ f'² sin(2θ)^{-η} + C ∫_Iθ f² sin(2θ)^{-η}`.

* `CosSqWeightIntegrable`: the `cos²(2θ)`-weighted integrand is (interval-)integrable.
* `HalfSharpHardyCos`: the left-half `(0, π/4)` version of the inequality, obtained from the
  already proved `Work.Elliptic.half_sharp_hardy` together with the pointwise bound
  `cos² ≤ 1`.
* The right half `(π/4, π/2)` is obtained from the left half by reflection
  `θ ↦ π/2 - θ` (the identities `rA_cos`, `rB`, `rD` below), and the two halves are glued
  by `intervalIntegral.integral_add_adjacent_intervals`.
-/




end Work.FTS.EllipticEst.Honest
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.ZBoxAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Honest

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-! ## The weights, the integrand and the majorant coefficient -/








/-! ## Elementary facts about the angular data -/







/-! ## The pointwise shape of the `ℋ⁰`-integrand and the slicewise integrability -/




/-! ## Joint and slicewise continuity of `∂_z²Ψ` -/




/-! ## A.e. strong measurability on the box -/


end Work.FTS.EllipticEst.Honest
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.barLimSlices =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Honest

set_option autoImplicit false
set_option maxHeartbeats 1000000









/-- **One-sided limit from an integrable derivative.** -/
theorem exists_tendsto_nhdsWithin_Iio_of_integrableOn_deriv {a b : ℝ} (hab : a < b)
    {f f' : ℝ → ℝ} (hf'm : MeasureTheory.AEStronglyMeasurable f' volume)
    (hderiv : ∀ x ∈ Set.Ioo a b, HasDerivAt f (f' x) x)
    (hint : MeasureTheory.IntegrableOn f' (Set.Ioc a b)) :
    ∃ L : ℝ, Filter.Tendsto f (nhdsWithin b (Set.Iio b)) (nhds L) := by
  obtain ⟨m, ham, hmb⟩ : ∃ m, a < m ∧ m < b := ⟨(a + b) / 2, by linarith, by linarith⟩
  have hgt : ∀ᶠ x in nhdsWithin b (Set.Iio b), a < x :=
    nhdsWithin_le_nhds (isOpen_Ioi.mem_nhds hab)
  have htail : Filter.Tendsto (fun x => ∫ t in x..b, f' t)
      (nhdsWithin b (Set.Iio b)) (nhds 0) := by
    have hf'_int : MeasureTheory.Integrable (Set.indicator (Set.Ioc a b) (fun t => ‖f' t‖)) volume := by
      rw [MeasureTheory.integrable_indicator_iff measurableSet_Ioc]
      exact hint.norm
    have key := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (μ := volume) (l := nhdsWithin b (Set.Iio b))
      (F := fun x : ℝ => Set.indicator (Set.Ioc x b) f')
      (f := fun _ => (0 : ℝ))
      (bound := Set.indicator (Set.Ioc a b) (fun t => ‖f' t‖))
      (by filter_upwards with x
          exact hf'm.indicator measurableSet_Ioc)
      (by filter_upwards [hgt] with x hax
          filter_upwards with t
          by_cases ht : t ∈ Set.Ioc x b
          · have ht' : t ∈ Set.Ioc a b := ⟨lt_trans hax ht.1, ht.2⟩
            rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht']
          · rw [Set.indicator_of_notMem ht, norm_zero]
            exact Set.indicator_nonneg (fun t _ => norm_nonneg (f' t)) t)
      hf'_int
      (by
        have haeb : ∀ᵐ t ∂(volume : MeasureTheory.Measure ℝ), t ≠ b := by
          rw [MeasureTheory.ae_iff]
          simpa using (MeasureTheory.measure_singleton b)
        filter_upwards [haeb] with t htb
        by_cases hbt : t < b
        · have hev : ∀ᶠ x in nhdsWithin b (Set.Iio b), t < x :=
            nhdsWithin_le_nhds (isOpen_Ioi.mem_nhds hbt)
          refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
          refine hev.mono (fun x hx => ?_)
          show (0 : ℝ) = (Set.Ioc x b).indicator f' t
          rw [Set.indicator_of_notMem (fun hmem => absurd hmem.1 (not_lt.mpr (le_of_lt hx)))]
        · have htb' : b < t := lt_of_le_of_ne (not_lt.mp hbt) htb.symm
          refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
          refine Filter.Eventually.of_forall (fun x => ?_)
          show (0 : ℝ) = (Set.Ioc x b).indicator f' t
          rw [Set.indicator_of_notMem (fun hmem => absurd hmem.2 (not_le.mpr htb'))])
    rw [MeasureTheory.integral_zero] at key
    refine Filter.Tendsto.congr' ?_ key
    filter_upwards [hgt, self_mem_nhdsWithin] with x hax hxb
    rw [intervalIntegral.integral_of_le (le_of_lt hxb)]
    exact MeasureTheory.integral_indicator measurableSet_Ioc
  refine ⟨f m + ∫ t in m..b, f' t, ?_⟩
  have hdiff : Filter.Tendsto (fun x => (f m + ∫ t in m..b, f' t) - ∫ t in x..b, f' t)
      (nhdsWithin b (Set.Iio b)) (nhds ((f m + ∫ t in m..b, f' t) - 0)) :=
    (tendsto_const_nhds (x := f m + ∫ t in m..b, f' t)).sub htail
  rw [sub_zero] at hdiff
  refine Filter.Tendsto.congr' ?_ hdiff
  have hgtm : ∀ᶠ x in nhdsWithin b (Set.Iio b), m < x :=
    nhdsWithin_le_nhds (isOpen_Ioi.mem_nhds hmb)
  filter_upwards [hgtm, self_mem_nhdsWithin] with x hmx hxb
  have hcont1 : ContinuousOn f (Set.Ioo a b) :=
    fun y hy => (hderiv y hy).continuousAt.continuousWithinAt
  have hcont : ContinuousOn f (Set.Icc m x) :=
    hcont1.mono (fun y hy => ⟨lt_of_lt_of_le ham hy.1, lt_of_le_of_lt hy.2 hxb⟩)
  have hInt : IntervalIntegrable f' volume m x := by
    rw [intervalIntegrable_iff]
    refine hint.mono_set ?_
    intro t ht
    rw [Set.uIoc_of_le (le_of_lt hmx)] at ht
    exact ⟨lt_trans ham ht.1, le_trans ht.2 (le_of_lt hxb)⟩
  have hFTC : ∫ t in m..x, f' t = f x - f m :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (le_of_lt hmx) hcont
      (fun y hy => hderiv y ⟨lt_trans ham hy.1, lt_trans hy.2 hxb⟩) hInt
  have hIx : IntervalIntegrable f' volume x b := by
    rw [intervalIntegrable_iff]
    refine hint.mono_set ?_
    intro t ht
    rw [Set.uIoc_of_le (le_of_lt hxb)] at ht
    exact ⟨lt_trans (lt_trans ham hmx) ht.1, ht.2⟩
  have hadd : (∫ t in m..b, f' t) = (∫ t in m..x, f' t) + (∫ t in x..b, f' t) :=
    (intervalIntegral.integral_add_adjacent_intervals hInt hIx).symm
  rw [hadd, hFTC]
  ring



end Work.FTS.EllipticEst.Honest
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.sliceInterp =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

local notation "σ" => Work.FTS.EllipticEst.AngSecond.sig

/-! ## 1. Elementary facts about the weight `σ θ = sin(2θ)^{-η}` -/

private lemma sig_nonneg_of_mem {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ σ θ :=
  Work.FTS.EllipticEst.AngSecond.sig_nonneg hθ

private lemma sig_eq_thEta : σ = Work.FTS.EllipticEst.thEta := rfl

private lemma integrableOn_sig : IntegrableOn σ Work.Spaces.Iθ := by
  rw [sig_eq_thEta]
  exact Work.FTS.EllipticEst.integrableOn_thEta.1

private lemma sig_zero_left : σ 0 = 0 := by
  rw [Work.FTS.EllipticEst.AngSecond.sig, show (2 : ℝ) * 0 = 0 by ring, Real.sin_zero]
  exact Real.zero_rpow (by rw [Work.Spaces.eta]; norm_num)

private lemma sig_zero_right : σ (Real.pi / 2) = 0 := by
  rw [Work.FTS.EllipticEst.AngSecond.sig,
    show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
  exact Real.zero_rpow (by rw [Work.Spaces.eta]; norm_num)

/-- Set integral over `[a,b]` is the interval integral. -/
private lemma setIntegral_Icc_eq_intervalIntegral {f : ℝ → ℝ} {a b : ℝ} (h : a ≤ b) :
    (∫ x in Set.Icc a b, f x) = ∫ x in a..b, f x := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le h]

/-- The weight is invariant under the reflection `θ ↦ π/2 - θ` of `Iθ`. -/
private lemma sig_pi_div_two_sub (θ : ℝ) : σ (Real.pi / 2 - θ) = σ θ := by
  rw [Work.FTS.EllipticEst.AngSecond.sig, Work.FTS.EllipticEst.AngSecond.sig,
    show 2 * (Real.pi / 2 - θ) = Real.pi - 2 * θ by ring, Real.sin_pi_sub]

/-- `[a,b]` and the open interval agree almost everywhere. -/
private lemma Icc_ae_eq_Ioo (a b : ℝ) : Set.Icc a b =ᵐ[volume] Set.Ioo a b := by
  have hpair : volume ({a, b} : Set ℝ) = 0 :=
    Set.Finite.measure_zero (by simp) volume
  have hpairab : ∀ᵐ x : ℝ, x ∉ ({a, b} : Set ℝ) := by
    rw [MeasureTheory.ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using hpair
  filter_upwards [hpairab] with x hx
  refine propext ⟨?_, ?_⟩
  · intro h
    rw [Set.mem_Icc] at h
    rw [Set.mem_Ioo]
    exact ⟨lt_of_le_of_ne h.1 (fun hc => hx (Or.inl hc.symm)),
      lt_of_le_of_ne h.2 (fun hc => hx (Or.inr hc))⟩
  · intro h
    rw [Set.mem_Ioo] at h
    rw [Set.mem_Icc]
    exact ⟨le_of_lt h.1, le_of_lt h.2⟩

private lemma Iθ_ae_eq_Ioo :
    Work.Spaces.Iθ =ᵐ[volume] Set.Ioo (0 : ℝ) (Real.pi / 2) := by
  simpa only [Work.Spaces.Iθ] using Icc_ae_eq_Ioo 0 (Real.pi / 2)

private lemma Ioo_subset_Iθ : Set.Ioo (0 : ℝ) (Real.pi / 2) ⊆ Work.Spaces.Iθ :=
  fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩

private lemma abs_sub_le_abs_add_abs (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  rw [abs_sub_le_iff]
  constructor <;> linarith [le_abs_self a, neg_le_abs a, le_abs_self b, neg_le_abs b]

/-- On the left quarter `(0, π/4]` the weight is dominated by the power `(4θ/π)^{-η}`
(Jordan's inequality). -/
private lemma sig_le_pow_left {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ Real.pi / 4) :
    σ θ ≤ ((4 / Real.pi) * θ) ^ (-(Work.Spaces.eta)) := by
  have hs : (4 / Real.pi) * θ ≤ Real.sin (2 * θ) := by
    have h := Real.mul_le_sin (x := 2 * θ) (by linarith) (by linarith [hθ1, Real.pi_pos])
    calc (4 / Real.pi) * θ = 2 / Real.pi * (2 * θ) := by ring
      _ ≤ Real.sin (2 * θ) := h
  have hpos : 0 < (4 / Real.pi) * θ := by positivity
  have hz : (-(Work.Spaces.eta)) ≤ 0 := by rw [Work.Spaces.eta]; norm_num
  rw [Work.FTS.EllipticEst.AngSecond.sig]
  exact Real.rpow_le_rpow_of_nonpos hpos hs hz

/-! ## 2. The mass of the weight on `Iθ` and on its two extreme quarters -/

/-- `∫_0^{π/4} (4θ/π)^{-η} dθ = 25π` (in the factored form). -/
private lemma integral_majorant_left :
    (∫ θ in (0 : ℝ)..(Real.pi / 4),
        (4 / Real.pi) ^ (-(Work.Spaces.eta)) * θ ^ (-(Work.Spaces.eta)))
      = 25 * Real.pi := by
  have hlt : (-1 : ℝ) < -(Work.Spaces.eta) := by rw [Work.Spaces.eta]; norm_num
  rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl hlt)]
  have hzero : (0 : ℝ) ^ (1 - Work.Spaces.eta) = 0 := by
    refine Real.zero_rpow ?_
    rw [Work.Spaces.eta]; norm_num
  rw [show -(Work.Spaces.eta) + 1 = 1 - Work.Spaces.eta by ring, hzero, sub_zero]
  have hcoef : (4 / Real.pi) ^ (-(Work.Spaces.eta)) = (Real.pi / 4) ^ (Work.Spaces.eta) := by
    rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ 4 / Real.pi),
      ← Real.inv_rpow (by positivity : (0 : ℝ) ≤ 4 / Real.pi) Work.Spaces.eta, inv_div]
  rw [hcoef]
  have hcomb : (Real.pi / 4) ^ (Work.Spaces.eta)
      * ((Real.pi / 4) ^ (1 - Work.Spaces.eta) / (1 - Work.Spaces.eta))
      = (Real.pi / 4) / (1 - Work.Spaces.eta) := by
    rw [mul_div_assoc', ← Real.rpow_add (by positivity : (0 : ℝ) < Real.pi / 4),
      show Work.Spaces.eta + (1 - Work.Spaces.eta) = 1 by ring, Real.rpow_one]
  rw [hcomb]
  have hden : (1 : ℝ) - Work.Spaces.eta = 1 / 100 := by rw [Work.Spaces.eta]; norm_num
  rw [hden]
  ring

/-- `∫_0^{π/4} σ ≤ 25π`. -/
private lemma integral_left_le :
    (∫ θ in (0 : ℝ)..(Real.pi / 4), σ θ) ≤ 25 * Real.pi := by
  have h44 : (0 : ℝ) ≤ Real.pi / 4 := by positivity
  have hσi : IntervalIntegrable σ volume 0 (Real.pi / 4) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le h44]
    refine integrableOn_sig.mono_set ?_
    intro x hx
    exact ⟨hx.1, by linarith [hx.2, Real.pi_pos]⟩
  have hmi : IntervalIntegrable
      (fun θ : ℝ => (4 / Real.pi) ^ (-(Work.Spaces.eta)) * θ ^ (-(Work.Spaces.eta)))
      volume 0 (Real.pi / 4) :=
    (intervalIntegral.intervalIntegrable_rpow'
      (by rw [Work.Spaces.eta]; norm_num : (-1 : ℝ) < -(Work.Spaces.eta))).const_mul _
  have hmono := intervalIntegral.integral_mono_on_of_le_Ioo h44 hσi hmi
    (fun x hx => by
      have h1 := sig_le_pow_left hx.1 (le_of_lt hx.2)
      rwa [Real.mul_rpow (by positivity : (0 : ℝ) ≤ 4 / Real.pi) (le_of_lt hx.1)] at h1)
  rwa [integral_majorant_left] at hmono

/-- The two halves of `∫_{Iθ} σ` are equal (reflection symmetry of the weight). -/
private lemma integral_right_eq_left :
    (∫ θ in (Real.pi / 4)..(Real.pi / 2), σ θ) = ∫ θ in (0 : ℝ)..(Real.pi / 4), σ θ := by
  have h := intervalIntegral.integral_comp_sub_left (a := 0) (b := Real.pi / 4) σ (Real.pi / 2)
  rw [show Real.pi / 2 - Real.pi / 4 = Real.pi / 4 by ring, sub_zero] at h
  rw [← h]
  exact intervalIntegral.integral_congr (fun x _ => sig_pi_div_two_sub x)

/-- **The total mass of the weight**: `∫_{Iθ} σ ≤ 200`. -/
private lemma sig_integral_Iθ_le_200 :
    (∫ θ in Work.Spaces.Iθ, σ θ) ≤ 200 := by
  have h2 : (∫ θ in Work.Spaces.Iθ, σ θ) = ∫ θ in (0 : ℝ)..(Real.pi / 2), σ θ :=
    setIntegral_Icc_eq_intervalIntegral (a := 0) (b := Real.pi / 2) (by positivity)
  rw [h2]
  have hπ4 : (0 : ℝ) ≤ Real.pi / 4 := by positivity
  have hσ1 : IntervalIntegrable σ volume 0 (Real.pi / 4) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hπ4]
    refine integrableOn_sig.mono_set ?_
    intro x hx
    exact ⟨hx.1, by linarith [hx.2, Real.pi_pos]⟩
  have hσ2 : IntervalIntegrable σ volume (Real.pi / 4) (Real.pi / 2) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith [Real.pi_pos])]
    refine integrableOn_sig.mono_set ?_
    intro x hx
    exact ⟨by linarith [hx.1, Real.pi_pos], hx.2⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals hσ1 hσ2, integral_right_eq_left]
  have := integral_left_le
  linarith [this, Real.pi_le_four]

/-- **The mass of the weight on the left quarter**: `25 ≤ ∫_{[0,π/8]} σ`. -/
private lemma sig_integral_left_ge_25 :
    25 ≤ ∫ θ in Set.Icc (0 : ℝ) (Real.pi / 8), σ θ := by
  have hsub : Set.Icc (0 : ℝ) (Real.pi / 8) ⊆ Work.Spaces.Iθ := by
    intro x hx
    exact ⟨hx.1, by linarith [hx.2, Real.pi_pos]⟩
  have hstep : (∫ θ in Set.Icc (0 : ℝ) (Real.pi / 8), (2 * θ) ^ (-(Work.Spaces.eta)))
      ≤ ∫ θ in Set.Icc (0 : ℝ) (Real.pi / 8), σ θ := by
    refine MeasureTheory.integral_mono_of_nonneg ?_ (integrableOn_sig.mono_set hsub) ?_
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
      exact Real.rpow_nonneg (by linarith [hθ.1]) _
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
      have hs : Real.sin (2 * θ) ≤ 2 * θ := Real.sin_le (by linarith [hθ.1])
      rcases eq_or_lt_of_le hθ.1 with h | h
      · subst h
        rw [mul_zero, Real.zero_rpow (by rw [Work.Spaces.eta]; norm_num)]
        exact sig_nonneg_of_mem (hsub ⟨le_refl 0, by linarith [Real.pi_pos]⟩)
      · rw [Work.FTS.EllipticEst.AngSecond.sig]
        exact Real.rpow_le_rpow_of_nonpos
          (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [hθ.2, Real.pi_pos])) hs
          (by rw [Work.Spaces.eta]; norm_num)
  have hval : (∫ θ in Set.Icc (0 : ℝ) (Real.pi / 8), (2 * θ) ^ (-(Work.Spaces.eta)))
      = 100 * (2 : ℝ) ^ (-(Work.Spaces.eta)) * (Real.pi / 8) ^ (1 - Work.Spaces.eta) := by
    have hred : (∫ θ in (0 : ℝ)..(Real.pi / 8), (2 * θ) ^ (-(Work.Spaces.eta)))
        = ∫ θ in (0 : ℝ)..(Real.pi / 8),
            (2 : ℝ) ^ (-(Work.Spaces.eta)) * θ ^ (-(Work.Spaces.eta)) := by
      have hae : (fun θ : ℝ => (2 * θ) ^ (-(Work.Spaces.eta)))
          =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) (Real.pi / 8))]
          (fun θ : ℝ => (2 : ℝ) ^ (-(Work.Spaces.eta)) * θ ^ (-(Work.Spaces.eta))) := by
        filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioc] with θ hθ
        exact Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (le_of_lt hθ.1)
      rw [intervalIntegral.integral_of_le (by positivity), intervalIntegral.integral_of_le (by positivity)]
      exact MeasureTheory.integral_congr_ae hae
    rw [setIntegral_Icc_eq_intervalIntegral (a := 0) (b := Real.pi / 8) (by positivity), hred,
      intervalIntegral.integral_const_mul,
      integral_rpow (Or.inl (by rw [Work.Spaces.eta]; norm_num : (-1 : ℝ) < -(Work.Spaces.eta)))]
    have hzero : (0 : ℝ) ^ (1 - Work.Spaces.eta) = 0 := by
      refine Real.zero_rpow ?_
      rw [Work.Spaces.eta]; norm_num
    rw [show -(Work.Spaces.eta) + 1 = 1 - Work.Spaces.eta by ring, hzero, sub_zero]
    have hden : (1 : ℝ) - Work.Spaces.eta = 1 / 100 := by rw [Work.Spaces.eta]; norm_num
    rw [hden]
    field_simp
  rw [hval] at hstep
  have h2η : (1 / 2 : ℝ) ≤ (2 : ℝ) ^ (-(Work.Spaces.eta)) := by
    have h1 : (2 : ℝ) ^ (-(1 : ℝ)) ≤ (2 : ℝ) ^ (-(Work.Spaces.eta)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by rw [Work.Spaces.eta]; norm_num)
    rw [Real.rpow_neg_one] at h1
    simpa only [one_div] using h1
  have hπ8 : (1 / 2 : ℝ) ≤ (Real.pi / 8) ^ (1 - Work.Spaces.eta) := by
    have hpos : (0 : ℝ) < Real.pi / 8 := by positivity
    have hle1 : Real.pi / 8 ≤ 1 := by have := Real.pi_lt_four; linarith
    have hexp : (1 : ℝ) - Work.Spaces.eta ≤ (1 : ℝ) / 2 := by
      rw [Work.Spaces.eta]; norm_num
    have h1 := Real.rpow_le_rpow_of_exponent_ge hpos hle1 hexp
    have h2 : (1 / 2 : ℝ) ≤ (Real.pi / 8) ^ ((1 : ℝ) / 2) := by
      rw [← Real.sqrt_eq_rpow]
      rw [Real.le_sqrt (by norm_num) (by positivity)]
      nlinarith [Real.pi_gt_three]
    linarith [h1, h2]
  nlinarith [hstep, h2η, hπ8]

/-- **The mass of the weight on the right quarter**: `25 ≤ ∫_{[3π/8,π/2]} σ`. -/
private lemma sig_integral_right_ge_25 :
    25 ≤ ∫ θ in Set.Icc (3 * Real.pi / 8) (Real.pi / 2), σ θ := by
  have hsym : (∫ θ in Set.Icc (3 * Real.pi / 8) (Real.pi / 2), σ θ)
      = ∫ θ in Set.Icc (0 : ℝ) (Real.pi / 8), σ θ := by
    rw [setIntegral_Icc_eq_intervalIntegral (a := 3 * Real.pi / 8) (b := Real.pi / 2)
        (by linarith [Real.pi_pos]),
      setIntegral_Icc_eq_intervalIntegral (a := 0) (b := Real.pi / 8) (by positivity)]
    have h := intervalIntegral.integral_comp_sub_left (a := 3 * Real.pi / 8)
      (b := Real.pi / 2) σ (Real.pi / 2)
    rw [show Real.pi / 2 - Real.pi / 2 = 0 by ring,
      show Real.pi / 2 - 3 * Real.pi / 8 = Real.pi / 8 by ring] at h
    have h2 : (∫ x in (3 * Real.pi / 8)..(Real.pi / 2), σ x)
        = ∫ x in (3 * Real.pi / 8)..(Real.pi / 2), σ (Real.pi / 2 - x) :=
      intervalIntegral.integral_congr (fun x _ => (sig_pi_div_two_sub x).symm)
    rw [h2, h]
  rw [hsym]
  exact sig_integral_left_ge_25

/-! ## 3. Two fundamental-theorem-of-calculus facts for a `C²` slice -/

/-- The oscillation of `u'` about its value at `π/4` is bounded by the total variation of `u''`. -/
private lemma abs_deriv_sub_center_le (u : ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (hint : IntegrableOn (fun θ => |deriv (fun t => deriv u t) θ|) Work.Spaces.Iθ) :
    ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |deriv u θ - deriv u (Real.pi / 4)|
        ≤ ∫ θ in Work.Spaces.Iθ, |deriv (fun t => deriv u t) θ| := by
  have hIoo : IsOpen (Set.Ioo (0 : ℝ) (Real.pi / 2)) := isOpen_Ioo
  have hd1 : ContDiffOn ℝ 1 (deriv u) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hu.deriv_of_isOpen hIoo (m := 1) (by norm_num)
  have hle : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  have hgi : IntervalIntegrable (fun x => |deriv (fun t => deriv u t) x|) volume 0 (Real.pi / 2) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hle).mpr (by simpa [Work.Spaces.Iθ] using hint)
  have hIeq : (∫ x in (0 : ℝ)..(Real.pi / 2), |deriv (fun t => deriv u t) x|)
      = ∫ x in Work.Spaces.Iθ, |deriv (fun t => deriv u t) x| := by
    rw [intervalIntegral.integral_of_le hle, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
    rfl
  intro θ hθ
  have h4 : Real.pi / 4 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have huIcc : Set.uIcc (Real.pi / 4) θ ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    intro x hx
    rw [Set.mem_uIcc] at hx
    rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨by linarith [h4.1, h1], by linarith [h2, hθ.2]⟩
    · exact ⟨by linarith [hθ.1, h1], by linarith [h2, h4.2]⟩
  have hFTC : (∫ x in (Real.pi / 4)..θ, deriv (fun t => deriv u t) x)
      = deriv u θ - deriv u (Real.pi / 4) :=
    intervalIntegral.integral_deriv_of_contDiffOn_uIcc (hd1.mono huIcc)
  have hkey : ∀ {a b : ℝ}, a ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      b ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) → a ≤ b →
      |∫ x in a..b, deriv (fun t => deriv u t) x|
        ≤ ∫ x in Work.Spaces.Iθ, |deriv (fun t => deriv u t) x| := by
    intro a b ha hb hab
    calc |∫ x in a..b, deriv (fun t => deriv u t) x|
        ≤ ∫ x in a..b, |deriv (fun t => deriv u t) x| :=
          intervalIntegral.abs_integral_le_integral_abs hab
      _ ≤ ∫ x in (0 : ℝ)..(Real.pi / 2), |deriv (fun t => deriv u t) x| :=
          intervalIntegral.integral_mono_interval ha.1.le hab hb.2.le
            (Filter.Eventually.of_forall
              (fun x => abs_nonneg (deriv (fun t => deriv u t) x))) hgi
      _ = ∫ x in Work.Spaces.Iθ, |deriv (fun t => deriv u t) x| := hIeq
  rcases le_total (Real.pi / 4) θ with hlt | hlt
  · rw [← hFTC]; exact hkey h4 hθ hlt
  · have h2 : deriv u θ - deriv u (Real.pi / 4)
        = -(∫ x in θ..(Real.pi / 4), deriv (fun t => deriv u t) x) := by
      rw [← hFTC, intervalIntegral.integral_symm (a := θ) (b := Real.pi / 4)]
    rw [h2, abs_neg]
    exact hkey hθ h4 hlt

/-- The second-order Taylor identity with remainder, centred at `π/4`. -/
private lemma taylor_identity_center (u : ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2))) :
    ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), ∀ φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      deriv u (Real.pi / 4) * (φ - θ)
        = (u φ - u θ) - ∫ s in θ..φ, (deriv u s - deriv u (Real.pi / 4)) := by
  have hIoo : IsOpen (Set.Ioo (0 : ℝ) (Real.pi / 2)) := isOpen_Ioo
  have hu1 : ContDiffOn ℝ 1 u (Set.Ioo (0 : ℝ) (Real.pi / 2)) := hu.of_le (by norm_num)
  intro θ hθ φ hφ
  have huIcc : Set.uIcc θ φ ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    intro x hx
    rw [Set.mem_uIcc] at hx
    rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨by linarith [hθ.1, h1], by linarith [h2, hφ.2]⟩
    · exact ⟨by linarith [hφ.1, h1], by linarith [h2, hθ.2]⟩
  have hFTC : (∫ s in θ..φ, deriv u s) = u φ - u θ :=
    intervalIntegral.integral_deriv_of_contDiffOn_uIcc (hu1.mono huIcc)
  have hc : ContinuousOn (deriv u) (Set.uIcc θ φ) :=
    (hu.continuousOn_deriv_of_isOpen hIoo (by norm_num)).mono huIcc
  have hii : IntervalIntegrable (deriv u) volume θ φ := hc.intervalIntegrable
  have hic : IntervalIntegrable (fun _ : ℝ => deriv u (Real.pi / 4)) volume θ φ :=
    intervalIntegrable_const
  have hsub : IntervalIntegrable (fun s : ℝ => deriv u s - deriv u (Real.pi / 4)) volume θ φ :=
    hii.sub hic
  have hsplit : (∫ s in θ..φ, deriv u s)
      = (∫ s in θ..φ, deriv u (Real.pi / 4))
        + ∫ s in θ..φ, (deriv u s - deriv u (Real.pi / 4)) := by
    rw [← intervalIntegral.integral_add hic hsub]
    exact intervalIntegral.integral_congr (fun s _ => by ring)
  rw [hsplit, intervalIntegral.integral_const] at hFTC
  simp only [smul_eq_mul] at hFTC
  linarith [hFTC]

/-! ## 4. The pivot bound -/

/-- **The pivot bound.**  Given the pointwise Taylor inequality relating `c (φ - θ)` to
`u φ - u θ`, the total-variation bound `A` for `u' - c` on the two extreme quarters of `Iθ`
and the mass lower bounds `≥ 25` on those quarters, the pivot satisfies `c² ≤ 12 A² + P`. -/
private lemma pivot_bound (u : ℝ → ℝ) (c A : ℝ) (hA0 : 0 ≤ A)
    (hkey : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 8), ∀ φ ∈ Set.Ioo (3 * Real.pi / 8) (Real.pi / 2),
      c ^ 2 * (Real.pi / 4) ^ 2 ≤ 3 * (u φ) ^ 2
        + (3 * (u θ) ^ 2 + 3 * (Real.pi / 2) ^ 2 * A ^ 2))
    (h0int : IntegrableOn (fun θ => (u θ) ^ 2 * σ θ) Work.Spaces.Iθ)
    (hQ1 : 25 ≤ ∫ θ in Set.Icc (0 : ℝ) (Real.pi / 8), σ θ)
    (hQ2 : 25 ≤ ∫ θ in Set.Icc (3 * Real.pi / 8) (Real.pi / 2), σ θ)
    (hP : 0 ≤ ∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 * σ θ) :
    c ^ 2 ≤ 12 * A ^ 2 + ∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 * σ θ := by
  have hsub1 : Set.Icc (0 : ℝ) (Real.pi / 8) ⊆ Work.Spaces.Iθ := by
    intro x hx
    rw [Set.mem_Icc] at hx
    exact ⟨hx.1, by linarith [hx.2, Real.pi_pos]⟩
  have hsub2 : Set.Icc (3 * Real.pi / 8) (Real.pi / 2) ⊆ Work.Spaces.Iθ := by
    intro x hx
    rw [Set.mem_Icc] at hx
    exact ⟨by linarith [hx.1, Real.pi_pos], hx.2⟩
  set Q1 : ℝ := ∫ θ in Set.Icc (0 : ℝ) (Real.pi / 8), σ θ with hQ1def
  set Q2 : ℝ := ∫ θ in Set.Icc (3 * Real.pi / 8) (Real.pi / 2), σ θ with hQ2def
  set J1 : ℝ := ∫ θ in Set.Icc (0 : ℝ) (Real.pi / 8), (u θ) ^ 2 * σ θ with hJ1def
  set J2 : ℝ := ∫ θ in Set.Icc (3 * Real.pi / 8) (Real.pi / 2), (u θ) ^ 2 * σ θ with hJ2def
  set P : ℝ := ∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 * σ θ with hPdef
  have hQ1pos : 0 < Q1 := by linarith
  have hQ2pos : 0 < Q2 := by linarith
  -- ## Step A: integrate the pointwise inequality over the right quarter in `φ`
  have hstepA : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 8),
      (c ^ 2 * (Real.pi / 4) ^ 2) * Q2 ≤ 3 * J2
        + (3 * (u θ) ^ 2 + 3 * (Real.pi / 2) ^ 2 * A ^ 2) * Q2 := by
    intro θ hθ
    have hbase : Integrable (fun φ => 3 * ((u φ) ^ 2 * σ φ))
        (volume.restrict (Set.Icc (3 * Real.pi / 8) (Real.pi / 2))) :=
      (h0int.mono_set hsub2).const_mul 3
    have hKK : Integrable (fun φ => (3 * (u θ) ^ 2 + 3 * (Real.pi / 2) ^ 2 * A ^ 2) * σ φ)
        (volume.restrict (Set.Icc (3 * Real.pi / 8) (Real.pi / 2))) :=
      (integrableOn_sig.mono_set hsub2).const_mul _
    have hsum : Integrable (fun φ => (3 * (u φ) ^ 2
        + (3 * (u θ) ^ 2 + 3 * (Real.pi / 2) ^ 2 * A ^ 2)) * σ φ)
        (volume.restrict (Set.Icc (3 * Real.pi / 8) (Real.pi / 2))) :=
      (hbase.add hKK).congr (by
        filter_upwards with φ
        simp only [Pi.add_apply]
        ring)
    have hσi : Integrable (fun φ => (c ^ 2 * (Real.pi / 4) ^ 2) * σ φ)
        (volume.restrict (Set.Icc (3 * Real.pi / 8) (Real.pi / 2))) :=
      (integrableOn_sig.mono_set hsub2).const_mul _
    have hle : (fun φ => (c ^ 2 * (Real.pi / 4) ^ 2) * σ φ)
        ≤ᵐ[volume.restrict (Set.Icc (3 * Real.pi / 8) (Real.pi / 2))]
        (fun φ => (3 * (u φ) ^ 2
          + (3 * (u θ) ^ 2 + 3 * (Real.pi / 2) ^ 2 * A ^ 2)) * σ φ) := by
      rw [Measure.restrict_congr_set (Icc_ae_eq_Ioo (3 * Real.pi / 8) (Real.pi / 2))]
      refine ae_restrict_of_forall_mem measurableSet_Ioo (fun φ hφ => ?_)
      exact mul_le_mul_of_nonneg_right (hkey θ hθ φ hφ)
        (sig_nonneg_of_mem (hsub2 ⟨le_of_lt hφ.1, le_of_lt hφ.2⟩))
    have h := integral_mono_ae hσi hsum hle
    have hIntL : (∫ φ in Set.Icc (3 * Real.pi / 8) (Real.pi / 2),
        (c ^ 2 * (Real.pi / 4) ^ 2) * σ φ) = (c ^ 2 * (Real.pi / 4) ^ 2) * Q2 := by
      rw [MeasureTheory.integral_const_mul, hQ2def]
    have hEq : (∫ φ in Set.Icc (3 * Real.pi / 8) (Real.pi / 2),
          (3 * (u φ) ^ 2 + (3 * (u θ) ^ 2 + 3 * (Real.pi / 2) ^ 2 * A ^ 2)) * σ φ)
        = (∫ φ in Set.Icc (3 * Real.pi / 8) (Real.pi / 2),
          3 * ((u φ) ^ 2 * σ φ)
            + (3 * (u θ) ^ 2 + 3 * (Real.pi / 2) ^ 2 * A ^ 2) * σ φ) := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun φ _ => ?_)
      ring
    have hIntR : (∫ φ in Set.Icc (3 * Real.pi / 8) (Real.pi / 2),
          3 * ((u φ) ^ 2 * σ φ)
            + (3 * (u θ) ^ 2 + 3 * (Real.pi / 2) ^ 2 * A ^ 2) * σ φ)
        = 3 * J2 + (3 * (u θ) ^ 2 + 3 * (Real.pi / 2) ^ 2 * A ^ 2) * Q2 := by
      rw [MeasureTheory.integral_add hbase hKK, MeasureTheory.integral_const_mul,
        MeasureTheory.integral_const_mul, ← hJ2def, ← hQ2def]
    rw [hIntL, hEq, hIntR] at h
    exact h
  -- ## Step B: integrate the result over the left quarter in `θ`
  have hstepB : ((c ^ 2 * (Real.pi / 4) ^ 2) * Q2) * Q1 ≤ 3 * J2 * Q1 + 3 * Q2 * J1
      + (3 * (Real.pi / 2) ^ 2 * A ^ 2) * (Q1 * Q2) := by
    have hbase : Integrable (fun θ => (3 * J2) * σ θ)
        (volume.restrict (Set.Icc (0 : ℝ) (Real.pi / 8))) :=
      (integrableOn_sig.mono_set hsub1).const_mul _
    have hIi : Integrable (fun θ => (3 * Q2) * ((u θ) ^ 2 * σ θ))
        (volume.restrict (Set.Icc (0 : ℝ) (Real.pi / 8))) :=
      (h0int.mono_set hsub1).const_mul _
    have hBi : Integrable (fun θ => ((3 * (Real.pi / 2) ^ 2 * A ^ 2) * Q2) * σ θ)
        (volume.restrict (Set.Icc (0 : ℝ) (Real.pi / 8))) :=
      (integrableOn_sig.mono_set hsub1).const_mul _
    have hsum : Integrable (fun θ => (3 * J2
        + (3 * (u θ) ^ 2 + 3 * (Real.pi / 2) ^ 2 * A ^ 2) * Q2) * σ θ)
        (volume.restrict (Set.Icc (0 : ℝ) (Real.pi / 8))) :=
      (hbase.add (hIi.add hBi)).congr (by
        filter_upwards with θ
        simp only [Pi.add_apply]
        ring)
    have hσi : Integrable (fun θ => ((c ^ 2 * (Real.pi / 4) ^ 2) * Q2) * σ θ)
        (volume.restrict (Set.Icc (0 : ℝ) (Real.pi / 8))) :=
      (integrableOn_sig.mono_set hsub1).const_mul _
    have hle : (fun θ => ((c ^ 2 * (Real.pi / 4) ^ 2) * Q2) * σ θ)
        ≤ᵐ[volume.restrict (Set.Icc (0 : ℝ) (Real.pi / 8))]
        (fun θ => (3 * J2 + (3 * (u θ) ^ 2 + 3 * (Real.pi / 2) ^ 2 * A ^ 2) * Q2) * σ θ) := by
      rw [Measure.restrict_congr_set (Icc_ae_eq_Ioo 0 (Real.pi / 8))]
      refine ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
      exact mul_le_mul_of_nonneg_right (hstepA θ hθ)
        (sig_nonneg_of_mem (hsub1 ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩))
    have h := integral_mono_ae hσi hsum hle
    have hIntL : (∫ θ in Set.Icc (0 : ℝ) (Real.pi / 8),
        ((c ^ 2 * (Real.pi / 4) ^ 2) * Q2) * σ θ)
        = ((c ^ 2 * (Real.pi / 4) ^ 2) * Q2) * Q1 := by
      rw [MeasureTheory.integral_const_mul, hQ1def]
    have hbase2 : Integrable (fun θ => 3 * ((u θ) ^ 2 * σ θ))
        (volume.restrict (Set.Icc (0 : ℝ) (Real.pi / 8))) :=
      (h0int.mono_set hsub1).const_mul 3
    have hc2 : Integrable (fun θ => (3 * (Real.pi / 2) ^ 2 * A ^ 2) * σ θ)
        (volume.restrict (Set.Icc (0 : ℝ) (Real.pi / 8))) :=
      (integrableOn_sig.mono_set hsub1).const_mul _
    have hKy : Integrable (fun θ => (3 * (u θ) ^ 2 + 3 * (Real.pi / 2) ^ 2 * A ^ 2) * σ θ)
        (volume.restrict (Set.Icc (0 : ℝ) (Real.pi / 8))) :=
      (hbase2.add hc2).congr (by
        filter_upwards with θ
        simp only [Pi.add_apply]
        ring)
    have hKK : Integrable (fun θ =>
        ((3 * (u θ) ^ 2 + 3 * (Real.pi / 2) ^ 2 * A ^ 2) * Q2) * σ θ)
        (volume.restrict (Set.Icc (0 : ℝ) (Real.pi / 8))) :=
      hKy.const_mul Q2 |>.congr (by
        filter_upwards with θ
        ring)
    have hE1 : (∫ θ in Set.Icc (0 : ℝ) (Real.pi / 8),
          (3 * J2 + (3 * (u θ) ^ 2 + 3 * (Real.pi / 2) ^ 2 * A ^ 2) * Q2) * σ θ)
        = (∫ θ in Set.Icc (0 : ℝ) (Real.pi / 8),
            (3 * J2) * σ θ
              + ((3 * (u θ) ^ 2 + 3 * (Real.pi / 2) ^ 2 * A ^ 2) * Q2) * σ θ) := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
      ring
    have hE2 : (∫ θ in Set.Icc (0 : ℝ) (Real.pi / 8),
            (3 * J2) * σ θ
              + ((3 * (u θ) ^ 2 + 3 * (Real.pi / 2) ^ 2 * A ^ 2) * Q2) * σ θ)
        = 3 * J2 * Q1 + (∫ θ in Set.Icc (0 : ℝ) (Real.pi / 8),
            ((3 * (u θ) ^ 2 + 3 * (Real.pi / 2) ^ 2 * A ^ 2) * Q2) * σ θ) := by
      rw [MeasureTheory.integral_add hbase hKK, MeasureTheory.integral_const_mul, ← hQ1def]
    have hE3 : (∫ θ in Set.Icc (0 : ℝ) (Real.pi / 8),
            ((3 * (u θ) ^ 2 + 3 * (Real.pi / 2) ^ 2 * A ^ 2) * Q2) * σ θ)
        = Q2 * (∫ θ in Set.Icc (0 : ℝ) (Real.pi / 8),
            (3 * (u θ) ^ 2 + 3 * (Real.pi / 2) ^ 2 * A ^ 2) * σ θ) := by
      have heq : (fun θ : ℝ => ((3 * (u θ) ^ 2 + 3 * (Real.pi / 2) ^ 2 * A ^ 2) * Q2) * σ θ)
          = fun θ : ℝ => Q2 * ((3 * (u θ) ^ 2 + 3 * (Real.pi / 2) ^ 2 * A ^ 2) * σ θ) := by
        funext θ
        ring
      rw [heq, MeasureTheory.integral_const_mul]
    have hE4 : (∫ θ in Set.Icc (0 : ℝ) (Real.pi / 8),
            (3 * (u θ) ^ 2 + 3 * (Real.pi / 2) ^ 2 * A ^ 2) * σ θ)
        = (∫ θ in Set.Icc (0 : ℝ) (Real.pi / 8),
            3 * ((u θ) ^ 2 * σ θ) + (3 * (Real.pi / 2) ^ 2 * A ^ 2) * σ θ) := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
      ring
    have hE5 : (∫ θ in Set.Icc (0 : ℝ) (Real.pi / 8),
            3 * ((u θ) ^ 2 * σ θ) + (3 * (Real.pi / 2) ^ 2 * A ^ 2) * σ θ)
        = 3 * J1 + 3 * (Real.pi / 2) ^ 2 * A ^ 2 * Q1 := by
      rw [MeasureTheory.integral_add hbase2 hc2, MeasureTheory.integral_const_mul,
        MeasureTheory.integral_const_mul, ← hJ1def, ← hQ1def]
    have hE6 : (∫ θ in Set.Icc (0 : ℝ) (Real.pi / 8),
          (3 * J2 + (3 * (u θ) ^ 2 + 3 * (Real.pi / 2) ^ 2 * A ^ 2) * Q2) * σ θ)
        = 3 * J2 * Q1 + 3 * Q2 * J1 + (3 * (Real.pi / 2) ^ 2 * A ^ 2) * (Q1 * Q2) := by
      rw [hE1, hE2, hE3, hE4, hE5]
      ring
    rw [hIntL, hE6] at h
    exact h
  -- ## Step C: divide by `Q1 Q2 ≥ 625` and use `J1, J2 ≤ P`
  have hJ1le : J1 ≤ P := by
    rw [hJ1def, hPdef]
    refine MeasureTheory.setIntegral_mono_set h0int ?_ ?_
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      exact mul_nonneg (sq_nonneg _) (sig_nonneg_of_mem hx)
    · filter_upwards with x hx
      rw [Set.mem_Icc] at hx
      exact ⟨hx.1, by linarith [hx.2, Real.pi_pos]⟩
  have hJ2le : J2 ≤ P := by
    rw [hJ2def, hPdef]
    refine MeasureTheory.setIntegral_mono_set h0int ?_ ?_
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      exact mul_nonneg (sq_nonneg _) (sig_nonneg_of_mem hx)
    · filter_upwards with x hx
      rw [Set.mem_Icc] at hx
      exact ⟨by linarith [hx.1, Real.pi_pos], hx.2⟩
  have hdiv : c ^ 2 * (Real.pi / 4) ^ 2 ≤ 6 * P / 25 + 3 * (Real.pi / 2) ^ 2 * A ^ 2 := by
    have hQpos : 0 < Q1 * Q2 := mul_pos hQ1pos hQ2pos
    have hb1 : 3 * J2 * Q1 ≤ (3 * P / 25) * (Q1 * Q2) := by
      have h25 : J2 * 25 ≤ P * Q2 := mul_le_mul hJ2le hQ2 (by norm_num) hP
      nlinarith [h25, hQ1pos.le]
    have hb2 : 3 * Q2 * J1 ≤ (3 * P / 25) * (Q1 * Q2) := by
      have h25 : J1 * 25 ≤ P * Q1 := mul_le_mul hJ1le hQ1 (by norm_num) hP
      nlinarith [h25, hQ2pos.le]
    have hmain : ((c ^ 2 * (Real.pi / 4) ^ 2) * Q2) * Q1
        ≤ (6 * P / 25 + 3 * (Real.pi / 2) ^ 2 * A ^ 2) * (Q1 * Q2) := by
      nlinarith [hstepB, hb1, hb2]
    refine le_of_mul_le_mul_right ?_ hQpos
    nlinarith [hmain]
  -- ## Step D: `(π/4)²` to `π²/16`, using `π² ≥ 4`
  have hPI : c ^ 2 ≤ 12 * A ^ 2 + P := by
    have hpi2 : (4 : ℝ) ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
    have hπ : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
    have hL : (c ^ 2 * (Real.pi / 4) ^ 2) * (16 / Real.pi ^ 2) = c ^ 2 := by
      field_simp
      ring
    have hmul := mul_le_mul_of_nonneg_right hdiv (by positivity : (0 : ℝ) ≤ 16 / Real.pi ^ 2)
    rw [hL] at hmul
    have hR : (6 * P / 25 + 3 * (Real.pi / 2) ^ 2 * A ^ 2) * (16 / Real.pi ^ 2)
        ≤ P + 12 * A ^ 2 := by
      have h1 : (3 * (Real.pi / 2) ^ 2 * A ^ 2) * (16 / Real.pi ^ 2) = 12 * A ^ 2 := by
        field_simp
        ring
      have h2 : (6 * P / 25) * (16 / Real.pi ^ 2) ≤ P := by
        have heq : (6 * P / 25) * (16 / Real.pi ^ 2) = 96 * P / (25 * Real.pi ^ 2) := by
          field_simp
          ring
        rw [heq, div_le_iff₀ (by positivity : (0 : ℝ) < 25 * Real.pi ^ 2)]
        nlinarith [hpi2, hP]
      nlinarith [h1, h2]
    linarith [hmul, hR]
  linarith [hPI]

/-! ## 5. The main theorem -/

theorem sliceInterp (u : ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (h0 : MeasureTheory.IntegrableOn
      (fun θ => (u θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iθ)
    (h2 : MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun t => deriv u t) θ) ^ 2
        * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn
      (fun θ => (deriv u θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iθ ∧
    (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ)
      ≤ 10000 * ((∫ θ in Work.Spaces.Iθ,
            (u θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ)
        + (∫ θ in Work.Spaces.Iθ, (deriv (fun t => deriv u t) θ) ^ 2
            * Work.FTS.EllipticEst.AngSecond.sig θ)) := by
  have hIoo : IsOpen (Set.Ioo (0 : ℝ) (Real.pi / 2)) := isOpen_Ioo
  have hcont : ContinuousOn (deriv u) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hu.continuousOn_deriv_of_isOpen hIoo (by norm_num)
  have hd1 : ContDiffOn ℝ 1 (deriv u) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hu.deriv_of_isOpen hIoo (m := 1) (by norm_num)
  have hd2cont : ContinuousOn (deriv (fun t => deriv u t)) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    contDiffOn_zero.1 (hd1.deriv_of_isOpen hIoo (m := 0) (by norm_num))
  have hAbs : IntegrableOn (fun θ => |deriv (fun t => deriv u t) θ|) Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.integrableAbsOfSqSeta hd2cont
      (by simpa [Work.FTS.EllipticEst.AngSecond.sig, Work.FTS.EllipticEst.sEta] using h2)
  set A : ℝ := ∫ θ in Work.Spaces.Iθ, |deriv (fun t => deriv u t) θ| with hAdef
  set E : ℝ := ∫ θ in Work.Spaces.Iθ, (deriv (fun t => deriv u t) θ) ^ 2 * σ θ with hEdef
  set P : ℝ := ∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 * σ θ with hPdef
  set c : ℝ := deriv u (Real.pi / 4) with hcdef
  have hAnn : 0 ≤ A :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun x _ => abs_nonneg (deriv (fun t => deriv u t) x))
  have hEnn : 0 ≤ E :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun x hx => mul_nonneg (sq_nonneg _) (sig_nonneg_of_mem hx))
  have hPnn : 0 ≤ P :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun x hx => mul_nonneg (sq_nonneg _) (sig_nonneg_of_mem hx))
  have hWnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, σ θ :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun x hx => sig_nonneg_of_mem hx)
  -- ## the pointwise and Taylor facts
  have hpt : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |deriv u θ - c| ≤ A := by
    intro θ hθ
    simpa only [hcdef, hAdef] using abs_deriv_sub_center_le u hu hAbs θ hθ
  have hty := taylor_identity_center u hu
  -- ## Cauchy–Schwarz: `A² ≤ (π/2) E`
  have hA2 : A ^ 2 ≤ (Real.pi / 2) * E := by
    have hst := Iθ_ae_eq_Ioo
    have hAint : IntegrableOn (fun θ => (deriv (fun t => deriv u t) θ) ^ 2 * σ θ)
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) := h2.mono_set Ioo_subset_Iθ
    have hint1 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
    have hCint : IntegrableOn (fun θ => |deriv (fun t => deriv u t) θ|)
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) := hAbs.mono_set Ioo_subset_Iθ
    have hdom : ∀ z ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        abs (|deriv (fun t => deriv u t) z|) ≤
          Real.sqrt ((deriv (fun t => deriv u t) z) ^ 2 * σ z)
            * Real.sqrt ((fun _ : ℝ => (1 : ℝ)) z) := by
      intro z hz
      have hσ1 : 1 ≤ σ z := Work.FTS.EllipticEst.AngSecond.one_le_sig hz
      have hsq : (0 : ℝ) ≤ (deriv (fun t => deriv u t) z) ^ 2 := sq_nonneg _
      have h1 : Real.sqrt ((deriv (fun t => deriv u t) z) ^ 2 * σ z)
          = |deriv (fun t => deriv u t) z| * Real.sqrt (σ z) := by
        rw [Real.sqrt_mul hsq, Real.sqrt_sq_eq_abs]
      have h2 : (1 : ℝ) ≤ Real.sqrt (σ z) :=
        (Real.le_sqrt (by norm_num) (by positivity)).mpr (by simpa using hσ1)
      have h3 : abs (|deriv (fun t => deriv u t) z|) = |deriv (fun t => deriv u t) z| :=
        abs_of_nonneg (abs_nonneg _)
      simp only [Real.sqrt_one, mul_one]
      rw [h3, h1]
      nlinarith [abs_nonneg (deriv (fun t => deriv u t) z)]
    have hcs := Work.FTS.EllipticEst.AngSecond.abs_setIntegral_le_sqrt_mul_sqrt
      (s := Set.Ioo (0 : ℝ) (Real.pi / 2))
      (A := fun z => (deriv (fun t => deriv u t) z) ^ 2 * σ z)
      (B := fun _ : ℝ => (1 : ℝ))
      (C := fun z => |deriv (fun t => deriv u t) z|)
      hAint hint1 hCint
      (fun z hz => mul_nonneg (sq_nonneg _) (sig_nonneg_of_mem (Ioo_subset_Iθ hz)))
      (fun z hz => zero_le_one) hdom
    have hL : abs (∫ z in Set.Ioo (0 : ℝ) (Real.pi / 2), |deriv (fun t => deriv u t) z|) = A := by
      rw [abs_of_nonneg (MeasureTheory.setIntegral_nonneg measurableSet_Ioo
        (fun x _ => abs_nonneg _)), hAdef]
      exact MeasureTheory.setIntegral_congr_set hst.symm
    have hR1 : (∫ z in Set.Ioo (0 : ℝ) (Real.pi / 2),
        (deriv (fun t => deriv u t) z) ^ 2 * σ z) = E := by
      rw [hEdef]
      exact MeasureTheory.setIntegral_congr_set hst.symm
    have hR2 : (∫ z in Set.Ioo (0 : ℝ) (Real.pi / 2), (1 : ℝ)) = Real.pi / 2 := by
      rw [MeasureTheory.setIntegral_const, MeasureTheory.measureReal_def, Real.volume_Ioo,
        ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
      simp
    rw [hL, hR1, hR2] at hcs
    have hsq : (Real.sqrt E * Real.sqrt (Real.pi / 2)) ^ 2 = E * (Real.pi / 2) := by
      rw [mul_pow, Real.sq_sqrt hEnn, Real.sq_sqrt (by positivity)]
    calc A ^ 2 ≤ (Real.sqrt E * Real.sqrt (Real.pi / 2)) ^ 2 :=
          pow_le_pow_left₀ hAnn hcs 2
      _ = E * (Real.pi / 2) := hsq
      _ = (Real.pi / 2) * E := by ring
  -- ## the pointwise Taylor inequality on the two extreme quarters
  have hkey : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 8),
      ∀ φ ∈ Set.Ioo (3 * Real.pi / 8) (Real.pi / 2),
      c ^ 2 * (Real.pi / 4) ^ 2 ≤ 3 * (u φ) ^ 2
        + (3 * (u θ) ^ 2 + 3 * (Real.pi / 2) ^ 2 * A ^ 2) := by
    intro θ hθ φ hφ
    have hθI : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
    have hφI : φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨by linarith [hφ.1, Real.pi_pos], hφ.2⟩
    have hle : θ ≤ φ := by linarith [hθ.2, hφ.1, Real.pi_pos]
    have ht : c * (φ - θ) = (u φ - u θ) - ∫ s in θ..φ, (deriv u s - c) := by
      rw [hcdef]
      exact hty θ hθI φ hφI
    have huIcc : Set.uIcc θ φ ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
      intro x hx
      rw [Set.mem_uIcc] at hx
      rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨by linarith [hθI.1, h1], by linarith [h2, hφI.2]⟩
      · exact ⟨by linarith [hφI.1, h1], by linarith [h2, hθI.2]⟩
    have hcont1 : ContinuousOn (fun s => deriv u s - c) (Set.uIcc θ φ) :=
      (hcont.mono huIcc).sub continuousOn_const
    have hii : IntervalIntegrable (fun s => deriv u s - c) volume θ φ :=
      hcont1.intervalIntegrable
    have hInt : |∫ s in θ..φ, (deriv u s - c)| ≤ (φ - θ) * A := by
      have hmono : (∫ s in θ..φ, |deriv u s - c|) ≤ ∫ s in θ..φ, A := by
        refine intervalIntegral.integral_mono_on_of_le_Ioo hle hii.abs intervalIntegrable_const ?_
        intro s hs
        exact hpt s ⟨by linarith [hθI.1, hs.1], by linarith [hs.2, hφI.2]⟩
      rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
      exact (intervalIntegral.abs_integral_le_integral_abs hle).trans hmono
    have hφθpos : 0 < φ - θ := by linarith [hθ.2, hφ.1, Real.pi_pos]
    have h1 : |c| * (φ - θ) ≤ |u φ| + |u θ| + (φ - θ) * A := by
      have h3 : |c * (φ - θ)| ≤ |u φ - u θ| + |∫ s in θ..φ, (deriv u s - c)| := by
        rw [ht]
        exact abs_sub_le_abs_add_abs _ _
      rw [abs_mul, abs_of_pos hφθpos] at h3
      have h4 : |u φ - u θ| ≤ |u φ| + |u θ| := abs_sub_le_abs_add_abs _ _
      linarith [h3, h4, hInt]
    have hπ4 : Real.pi / 4 ≤ φ - θ := by linarith [hθ.2, hφ.1, Real.pi_pos]
    have h5 : |c| * (Real.pi / 4) ≤ |u φ| + |u θ| + (Real.pi / 2) * A := by
      have h6 : |c| * (Real.pi / 4) ≤ |c| * (φ - θ) :=
        mul_le_mul_of_nonneg_left hπ4 (abs_nonneg c)
      have h7 : (φ - θ) * A ≤ (Real.pi / 2) * A := by
        have h8 : φ - θ ≤ Real.pi / 2 := by linarith [hθI.1, hφI.2]
        exact mul_le_mul_of_nonneg_right h8 hAnn
      linarith [h1, h6, h7]
    have hsq1 : (|c| * (Real.pi / 4)) ^ 2 ≤ (|u φ| + |u θ| + (Real.pi / 2) * A) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h5 2
    have hsq2 : (|u φ| + |u θ| + (Real.pi / 2) * A) ^ 2
        ≤ 3 * (u φ) ^ 2 + 3 * (u θ) ^ 2 + 3 * (Real.pi / 2) ^ 2 * A ^ 2 := by
      have h8 : (|u φ| + |u θ| + (Real.pi / 2) * A) ^ 2
          ≤ 3 * ((u φ) ^ 2 + (u θ) ^ 2 + ((Real.pi / 2) * A) ^ 2) := by
        nlinarith [sq_nonneg (|u φ| - |u θ|), sq_nonneg (|u θ| - (Real.pi / 2) * A),
          sq_nonneg (|u φ| - (Real.pi / 2) * A), sq_abs (u φ), sq_abs (u θ)]
      nlinarith [h8]
    have hlhs : (|c| * (Real.pi / 4)) ^ 2 = c ^ 2 * (Real.pi / 4) ^ 2 := by
      rw [mul_pow, sq_abs]
    linarith [hsq1, hsq2, hlhs]
  -- ## the pivot bound
  have hpiv : c ^ 2 ≤ 12 * A ^ 2 + P := by
    have h := pivot_bound u c A hAnn hkey h0 sig_integral_left_ge_25
      sig_integral_right_ge_25 hPnn
    rw [← hPdef] at h
    exact h
  -- ## the pointwise domination of `(u')²`
  have hσmeas : Measurable σ :=
    Measurable.pow_const (Real.measurable_sin.comp (measurable_const.mul measurable_id)) _
  have hms : volume.restrict Work.Spaces.Iθ
      = volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    Measure.restrict_congr_set Iθ_ae_eq_Ioo
  have haesm1 : AEStronglyMeasurable (deriv u) (volume.restrict Work.Spaces.Iθ) := by
    rw [hms]
    exact hcont.aestronglyMeasurable measurableSet_Ioo
  have haesm : AEStronglyMeasurable (fun θ => (deriv u θ) ^ 2 * σ θ)
      (volume.restrict Work.Spaces.Iθ) := (haesm1.pow 2).mul hσmeas.aestronglyMeasurable
  have hbdae : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      (deriv u θ) ^ 2 * σ θ ≤ (2 * A ^ 2 + 2 * c ^ 2) * σ θ := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    have hσnn : 0 ≤ σ θ := sig_nonneg_of_mem hθ
    rcases eq_or_lt_of_le hθ.1 with h | h
    · subst h
      simp only [sig_zero_left, mul_zero, le_refl]
    · rcases eq_or_lt_of_le hθ.2 with h2 | h2
      · subst h2
        simp only [sig_zero_right, mul_zero, le_refl]
      · have hp := hpt θ ⟨h, h2⟩
        have hx : (deriv u θ - c) ^ 2 ≤ A ^ 2 := by
          nlinarith [hp, sq_abs (deriv u θ - c), abs_nonneg (deriv u θ - c), hAnn]
        have hbd : (deriv u θ) ^ 2 ≤ 2 * A ^ 2 + 2 * c ^ 2 := by
          nlinarith [hx, sq_nonneg (deriv u θ - c - c)]
        exact mul_le_mul_of_nonneg_right hbd hσnn
  have hbdint : IntegrableOn (fun θ => (2 * A ^ 2 + 2 * c ^ 2) * σ θ) Work.Spaces.Iθ :=
    integrableOn_sig.const_mul _
  have habs : IntegrableOn (fun θ => (deriv u θ) ^ 2 * σ θ) Work.Spaces.Iθ := by
    refine hbdint.mono' haesm ?_
    filter_upwards [hbdae, ae_restrict_mem measurableSet_Icc] with θ h1 h2
    rwa [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sig_nonneg_of_mem h2))]
  -- ## assembly
  have hint_le : (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 * σ θ)
      ≤ (2 * A ^ 2 + 2 * c ^ 2) * (∫ θ in Work.Spaces.Iθ, σ θ) := by
    have h := integral_mono_ae habs hbdint hbdae
    rwa [MeasureTheory.integral_const_mul] at h
  have hfin : (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 * σ θ) ≤ 10000 * (P + E) := by
    have hW : (∫ θ in Work.Spaces.Iθ, σ θ) ≤ 200 := sig_integral_Iθ_le_200
    have hpiv' : c ^ 2 + A ^ 2 ≤ 13 * A ^ 2 + P := by linarith [hpiv]
    have h3 : 2 * (∫ θ in Work.Spaces.Iθ, σ θ) * (c ^ 2 + A ^ 2)
        ≤ 2 * 200 * (13 * A ^ 2 + P) := by
      nlinarith [hW, hpiv', hWnn, sq_nonneg c, sq_nonneg A]
    have h4 : 2 * 200 * (13 * A ^ 2 + P) ≤ 2 * 200 * (13 * ((Real.pi / 2) * E) + P) := by
      nlinarith [hA2, hEnn, hPnn, hAnn]
    have h5 : 2 * 200 * (13 * ((Real.pi / 2) * E) + P) ≤ 10000 * (P + E) := by
      have hπ : Real.pi ≤ 3.15 := Real.pi_lt_d2.le
      nlinarith [hπ, hEnn, hPnn, Real.pi_pos]
    linarith [hint_le, h3, h4, h5]
  exact ⟨habs, hfin⟩

end

end Work.FTS.EllipticEst.Honest
end
-- ===== merged: Submission.Work.FTS.EllipticEst.SrcBnd.GsrcPthTwo =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-
Copyright: work module for the Elgindi finite-time singularity project.

# `GsrcPthTwo`: the second `θ`-derivative of the angular source

`Mine.Gsrc α F Ψ = F + α²z²∂_z²Ψ + α(5+α)z∂_zΨ` is the angular source of the equation
(PolarBSL).  The two top-slot estimates of the elliptic chapter need its iterated
`∂_θ`-derivatives, expanded over the three summands: this file proves the order-`1` and
order-`2` cases

  `∂_θ (Gsrc α F Ψ)   = ∂_θ F   + α² ∂_θ (z²∂_z²Ψ) + α(5+α) ∂_θ (D_zΨ)`,
  `∂_θ²(Gsrc α F Ψ)   = ∂_θ²F   + α² ∂_θ²(z²∂_z²Ψ) + α(5+α) ∂_θ²(D_zΨ)`

on the open quadrant `Q0 = (0,∞) × (0,π/2)`, for `SmoothOpen F` and `SmoothOpen Ψ`.

The mathematical content is only the linearity of `∂_θᵏ` over a *three-term* linear
combination.  The proof tool is the induction `pthIter_three_lin` below: since `deriv` is
totalised, the identity is claimed only where all three summands are differentiable in
`θ`, which `SmoothOpen` (i.e. `C^∞` on the open quadrant) supplies through the slices
(`SmoothOpen.curry_θ`), and the induction is carried by `Filter.EventuallyEq.deriv_eq`
along with `deriv`-additivity on the three differentiable slices.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.SrcBnd

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## Elementary `∂_θ`-calculus on the open quadrant -/

/-- The `θ`-slice of a `∂_θ`-iterate of a `SmoothOpen` function is differentiable at every
interior angle. -/
theorem differentiableAt_slice_pthIter {F : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen F)
    (i : ℕ) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    DifferentiableAt ℝ (fun θ' => Work.Spaces.pthIter i F z θ') θ :=
  (((smoothOpen_pthIter hF i).curry_θ hz).differentiableOn (by simp)).differentiableAt
    (isOpen_Ioo.mem_nhds hθ)

/-- **Three-term `∂_θ`-linearity.**  On the open quadrant the iterated `∂_θ`-derivative of a
linear combination `f + a·g + b·h` of three `C^∞` functions is the corresponding combination
of the iterated derivatives. -/
theorem pthIter_three_lin {f g h : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (hh : Work.FTS.EllipticEst.SmoothOpen h)
    (a b : ℝ) (i : ℕ) :
    ∀ z θ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      Work.Spaces.pthIter i (fun z t => f z t + a * g z t + b * h z t) z θ
        = Work.Spaces.pthIter i f z θ + a * Work.Spaces.pthIter i g z θ
          + b * Work.Spaces.pthIter i h z θ := by
  induction i with
  | zero => intro z θ _ _; rfl
  | succ n ih =>
      intro z θ hz hθ
      have heq : (fun θ' : ℝ => Work.Spaces.pthIter n
            (fun z t => f z t + a * g z t + b * h z t) z θ')
          =ᶠ[𝓝 θ] (fun θ' => Work.Spaces.pthIter n f z θ' + a * Work.Spaces.pthIter n g z θ'
            + b * Work.Spaces.pthIter n h z θ') := by
        filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
        exact ih z θ' hz hθ'
      have hdA := differentiableAt_slice_pthIter hf n hz hθ
      have hdB := differentiableAt_slice_pthIter hg n hz hθ
      have hdC := differentiableAt_slice_pthIter hh n hz hθ
      have hp : HasDerivAt (fun θ' : ℝ => Work.Spaces.pthIter n f z θ'
            + a * Work.Spaces.pthIter n g z θ' + b * Work.Spaces.pthIter n h z θ')
          (deriv (fun θ' : ℝ => Work.Spaces.pthIter n f z θ') θ
            + a * deriv (fun θ' : ℝ => Work.Spaces.pthIter n g z θ') θ
            + b * deriv (fun θ' : ℝ => Work.Spaces.pthIter n h z θ') θ) θ :=
        ((hdA.hasDerivAt.add (hdB.hasDerivAt.const_mul a)).add
          (hdC.hasDerivAt.const_mul b))
      simp only [Work.Spaces.pthIter_succ, Work.Spaces.pth]
      rw [heq.deriv_eq]
      exact hp.deriv

/-- Multiplication of a `SmoothOpen` function by the radial factor `z²`. -/
theorem smoothOpen_zsq_mul (G : ℝ → ℝ → ℝ) (hG : Work.FTS.EllipticEst.SmoothOpen G) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * G z θ) := by
  change ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ => z ^ 2 * G z θ)) Work.FTS.EllipticEst.Q0
  change ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => p.1 ^ 2 * G p.1 p.2)
    Work.FTS.EllipticEst.Q0
  exact ((contDiffOn_fst (𝕜 := ℝ) (s := Work.FTS.EllipticEst.Q0)).pow 2).mul
    (show ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => G p.1 p.2)
      Work.FTS.EllipticEst.Q0 from hG)

/-! ## The second `θ`-derivative of the angular source -/

/-- **The order-`2` `∂_θ`-expansion of the angular source.**  For `F` and `Ψ` of class `C^∞`
on the open quadrant and every interior point,

  `∂_θ²(Gsrc α F Ψ) = ∂_θ²F + α² ∂_θ²(z²∂_z²Ψ) + α(5+α) ∂_θ²(D_zΨ)`. -/
theorem GsrcPthTwo {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    ∀ z θ, 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) →
      Work.Spaces.pthIter 2 (Work.FTS.EllipticEst.Mine.Gsrc α F Ψ) z θ
        = Work.Spaces.pthIter 2 F z θ
          + α ^ 2 * Work.Spaces.pthIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
          + α * (5 + α) * Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) z θ := by
  intro z θ hz hθ
  have hg : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
    smoothOpen_zsq_mul _ (hΨ.pzIter 2)
  have hh : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.DzIter 1 Ψ) := hΨ.DzIter 1
  have hmain := pthIter_three_lin hF hg hh (α ^ 2) (α * (5 + α)) 2 z θ hz hθ
  exact hmain

end Work.FTS.EllipticEst.SrcBnd
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.SrcBnd.SlotIntegrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.SrcBnd

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-! ## Preparatory lemmas -/

/-- The uncurried angular slot `w(z)² · (∂_θ^n f(z,θ))² · σ(θ)` is continuous on the open
quadrant, for `f` smooth on the quadrant and `σ ∘ snd` continuous there. -/
theorem continuousOn_slot {f : ℝ → ℝ → ℝ} {σ : ℝ → ℝ} (n : ℕ)
    (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hσc : ContinuousOn (fun p : ℝ × ℝ => σ p.2) Work.FTS.EllipticEst.Q0) :
    ContinuousOn (fun p : ℝ × ℝ =>
      (Work.Spaces.w p.1) ^ 2 * ((Work.Spaces.pthIter n f p.1 p.2) ^ 2 * σ p.2))
      Work.FTS.EllipticEst.Q0 := by
  have hw : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) Work.FTS.EllipticEst.Q0 := by
    have hfun : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by
      funext p; rfl
    rw [hfun]
    refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2) (fun p hp => ?_)
    exact pow_ne_zero 2 (ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hp).1)
  have hfθ : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pthIter n f p.1 p.2)
      Work.FTS.EllipticEst.Q0 := (smoothOpen_pthIter hf n).continuousOn
  exact (hw.pow 2).mul ((hfθ.pow 2).mul hσc)

/-! ## The abstract integrability step -/


/-! ## The requested slot integrability -/


end Work.FTS.EllipticEst.SrcBnd
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.TT.Slot11.ZsqAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.TTSlot11Aux

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## The open-quadrant ingredients

Everything in this section is stated for data which are `C^∞` on the open quadrant
`Q0 = (0,∞) × (0,π/2)` (the class `Work.FTS.EllipticEst.SmoothOpen`) and is used at a point
`(z,θ)` of `Q0`.  All the statements are in the *internal* shape
`∀ z θ, 0 < z → 0 < θ → θ < π/2 → …` of the chapter. -/

/-- `z² ∂_z² Ψ = D_z² Ψ - D_z Ψ` at every point of the open quadrant, for `Ψ` which is `C^∞`
there.  (The open-quadrant counterpart of `Work.FTS.EllipticEst.Cert.DzAux.zsq_pzIter2_eqOn`,
which is stated for `SmoothNbhd`.) -/
theorem zsq_pzIter2_eq_open (Ψ : ℝ → ℝ → ℝ) (hΨ : SmoothOpen Ψ) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ
      = Work.Spaces.DzIter 2 Ψ z θ - Work.Spaces.Dz Ψ z θ := by
  have hd1 : DifferentiableAt ℝ (fun z' => Ψ z' θ) z :=
    (hΨ.hasDerivAt_slice hθ hz).differentiableAt
  have hd2 : DifferentiableAt ℝ (fun z' => Work.Spaces.pz Ψ z' θ) z :=
    (hΨ.hasDerivAt_slice_pzIter 1 hθ hz).differentiableAt
  exact Work.FTS.EllipticEst.zsq_pzIter2_eq Ψ hd1 hd2

/-- Two functions agreeing on the open quadrant have the same iterated `D_θ`-derivatives
there.  (Locality of `D_θ`; no smoothness is needed.) -/
theorem DthIter_congr_open {F G : ℝ → ℝ → ℝ}
    (h : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 → F z θ = G z θ) (i : ℕ) :
    ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.DthIter i F z θ = Work.Spaces.DthIter i G z θ := by
  induction i with
  | zero => intro z θ hz h1 h2; exact h z θ hz h1 h2
  | succ n ih =>
      intro z θ hz h1 h2
      have heq : (fun θ' => Work.Spaces.DthIter n F z θ')
          =ᶠ[𝓝 θ] (fun θ' => Work.Spaces.DthIter n G z θ') := by
        filter_upwards [isOpen_Ioo.mem_nhds (show θ ∈ Set.Ioo 0 (π / 2) from ⟨h1, h2⟩)]
          with θ' hθ'
        exact ih z θ' hz hθ'.1 hθ'.2
      simp only [Work.Spaces.DthIter_succ, Work.Spaces.Dth, Work.Spaces.pth]
      rw [heq.deriv_eq]

/-- Two functions agreeing on the open quadrant have the same mixed derivatives there. -/
theorem mixed_congr_open {F G : ℝ → ℝ → ℝ}
    (h : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 → F z θ = G z θ) (j i : ℕ) :
    ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.mixed j i F z θ = Work.Spaces.mixed j i G z θ :=
  SmoothOpen.DzIter_congr (F := Work.Spaces.DthIter i F) (G := Work.Spaces.DthIter i G)
    (DthIter_congr_open h i) j

/-- The iterated `D_z`-operator is additive for `-` on the open quadrant for `SmoothOpen`
data.  (The subtraction counterpart of `Work.FTS.EllipticEst.SmoothOpen.DzIter_add`.) -/
theorem DzIter_sub_open {F G : ℝ → ℝ → ℝ} (hF : SmoothOpen F) (hG : SmoothOpen G) (j : ℕ) :
    ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.DzIter j (fun z θ => F z θ - G z θ) z θ
        = Work.Spaces.DzIter j F z θ - Work.Spaces.DzIter j G z θ := by
  induction j with
  | zero => intro z θ hz h1 h2; rfl
  | succ n ih =>
      intro z θ hz h1 h2
      have heq : (fun z' => Work.Spaces.DzIter n (fun z θ => F z θ - G z θ) z' θ)
          =ᶠ[𝓝 z] (fun z' => Work.Spaces.DzIter n F z' θ - Work.Spaces.DzIter n G z' θ) := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
        exact ih z' θ hz' h1 h2
      have hd1 : DifferentiableAt ℝ (fun z' => Work.Spaces.DzIter n F z' θ) z :=
        ((hF.DzIter n).hasDerivAt_slice ⟨h1, h2⟩ hz).differentiableAt
      have hd2 : DifferentiableAt ℝ (fun z' => Work.Spaces.DzIter n G z' θ) z :=
        ((hG.DzIter n).hasDerivAt_slice ⟨h1, h2⟩ hz).differentiableAt
      have hd : deriv (fun z' => Work.Spaces.DzIter n F z' θ - Work.Spaces.DzIter n G z' θ) z
          = deriv (fun z' => Work.Spaces.DzIter n F z' θ) z
            - deriv (fun z' => Work.Spaces.DzIter n G z' θ) z := deriv_sub hd1 hd2
      simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
      rw [heq.deriv_eq, hd]
      ring

/-- The iterated `D_θ`-operator is additive for `-` on the open quadrant for `SmoothOpen`
data. -/
theorem DthIter_sub_open {F G : ℝ → ℝ → ℝ} (hF : SmoothOpen F) (hG : SmoothOpen G) (i : ℕ) :
    ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.DthIter i (fun z θ => F z θ - G z θ) z θ
        = Work.Spaces.DthIter i F z θ - Work.Spaces.DthIter i G z θ := by
  induction i with
  | zero => intro z θ hz h1 h2; rfl
  | succ n ih =>
      intro z θ hz h1 h2
      have hθ : θ ∈ Set.Ioo 0 (π / 2) := ⟨h1, h2⟩
      have heq : (fun θ' => Work.Spaces.DthIter n (fun z θ => F z θ - G z θ) z θ')
          =ᶠ[𝓝 θ] (fun θ' => Work.Spaces.DthIter n F z θ' - Work.Spaces.DthIter n G z θ') := by
        filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
        exact ih z θ' hz hθ'.1 hθ'.2
      have hd1 : DifferentiableAt ℝ (fun θ' => Work.Spaces.DthIter n F z θ') θ :=
        (((hF.DthIter n).curry_θ hz).differentiableOn (by simp)).differentiableAt
          (isOpen_Ioo.mem_nhds hθ)
      have hd2 : DifferentiableAt ℝ (fun θ' => Work.Spaces.DthIter n G z θ') θ :=
        (((hG.DthIter n).curry_θ hz).differentiableOn (by simp)).differentiableAt
          (isOpen_Ioo.mem_nhds hθ)
      have hd : deriv (fun θ' => Work.Spaces.DthIter n F z θ' - Work.Spaces.DthIter n G z θ') θ
          = deriv (fun θ' => Work.Spaces.DthIter n F z θ') θ
            - deriv (fun θ' => Work.Spaces.DthIter n G z θ') θ := deriv_sub hd1 hd2
      simp only [Work.Spaces.DthIter_succ, Work.Spaces.Dth, Work.Spaces.pth]
      rw [heq.deriv_eq, hd]
      ring

/-- The mixed operators `D_z^j D_θ^i` are additive for `-` on the open quadrant for
`SmoothOpen` data. -/
theorem mixed_sub_open {F G : ℝ → ℝ → ℝ} (hF : SmoothOpen F) (hG : SmoothOpen G) (j i : ℕ) :
    ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.mixed j i (fun z θ => F z θ - G z θ) z θ
        = Work.Spaces.mixed j i F z θ - Work.Spaces.mixed j i G z θ := by
  intro z θ hz h1 h2
  have hcongr := SmoothOpen.DzIter_congr
    (F := Work.Spaces.DthIter i (fun z θ => F z θ - G z θ))
    (G := fun z θ => Work.Spaces.DthIter i F z θ - Work.Spaces.DthIter i G z θ)
    (fun z θ hz h1 h2 => DthIter_sub_open hF hG i z θ hz h1 h2) j z θ hz h1 h2
  have hadd := DzIter_sub_open (hF.DthIter i) (hG.DthIter i) j z θ hz h1 h2
  simp only [Work.Spaces.mixed]
  exact hcongr.trans hadd

/-- **`D_z^b` commutes with the mixed operator on the open quadrant**:
`mixed m i (D_z^b f) = mixed (m+b) i f` there, for `f` which is `C^∞` on the open quadrant.
This is the open-quadrant counterpart of the case `a = 0` of
`Work.Spaces.mixed_comm` (which is stated for `SmoothNbhd`). -/
theorem mixed_DzIter_open (f : ℝ → ℝ → ℝ) (hF : SmoothOpen f) (m i b : ℕ) :
    ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.mixed m i (Work.Spaces.DzIter b f) z θ
        = Work.Spaces.mixed (m + b) i f z θ := by
  intro z θ hz h1 h2
  have hloc := SmoothOpen.DzIter_congr
    (F := Work.Spaces.DthIter i (Work.Spaces.DzIter b f))
    (G := fun z θ => Work.Spaces.mixed b i f z θ)
    (fun z θ hz' h1' h2' => SmoothOpen.DthIter_DzIter_eq_mixed hF b i hz' ⟨h1', h2'⟩)
    m z θ hz h1 h2
  rw [show Work.Spaces.mixed m i (Work.Spaces.DzIter b f) z θ
      = Work.Spaces.DzIter m (Work.Spaces.DzIter b (Work.Spaces.DthIter i f)) z θ from hloc]
  rw [← Work.Spaces.DzIter_add_right m b (Work.Spaces.DthIter i f)]
  rfl

/-! ## The commutation `z²∂_z²(mixed m i f) = mixed m i (z²∂_z² f)` -/

/-- **The commutation `z²∂_z² (D_z^j D_θ^i f) = D_z^j D_θ^i (z²∂_z² f)` on the open quadrant.**

For `f` which is `C^n` on the open quadrant `(0,∞) × (0,π/2)` for every finite `n` (the class
`Work.FTS.EllipticEst.SmoothOpen` of `Submission/Work/FTS/EllipticEst/OpenQDefs.lean`), every
`j i : ℕ`, every `z > 0` and every `θ ∈ (0, π/2)`,

  `z² · ∂_z² (mixed j i f) (z,θ) = mixed j i (fun z θ => z² · ∂_z² f z θ) (z,θ)`,

where `mixed j i f = D_z^j D_θ^i f = Work.Spaces.DzIter j (Work.Spaces.DthIter i f)` and
`pzIter 2 = ∂_z²` (`Work.Spaces.pzIter 2`).

This is the open-quadrant counterpart of `Work.FTS.EllipticEst.Cert.DzAux.zsq_pzIter2_mixed`,
which is stated for `Work.Spaces.SmoothNbhd` (`C^ω` on a neighbourhood of the *closed* quadrant)
— strictly stronger than the hypothesis here.

Route: `z²∂_z²` commutes with `D_z = z∂_z` (`[z∂_z, z²∂_z²] = 0`, a direct product-rule
computation) and with `D_θ = sin(2θ)∂_θ` (Clairaut, the coefficient is independent of `z`); hence
`z²∂_z² (D_z^j D_θ^i f) = D_z^j (z²∂_z² (D_θ^i f)) = D_z^j D_θ^i (z²∂_z² f)` at the point.
Equivalently, follow `Cert.DzAux.zsq_pzIter2_mixed`: use `z²∂_z²ψ = D_z²ψ - D_zψ` (product rule,
for a `C²` function on the open quadrant), and the facts that `D_z^j` and `D_θ^i` are additive on
the open quadrant and commute with each other there (`Work.Spaces.DzIter_add_right`,
`Work.Spaces.DthIter_DzIter_eq_mixed_open` in
`Submission/Work/FTS/EllipticEst/SliceDecompDefs.lean`, and the local counterparts of
`Dz_sub_eqOn`/`mixed_sub_eqOn`/`mixed_congr`, which in `Cert/DzPsiAux.lean` are stated for
`SmoothNbhd` and must be redone for the open class with `ContDiffAt`/`ContDiffOn` on the open
quadrant — the pointwise calculus `Work.Spaces.pz_congr_of_isOpen`, `pth_congr_of_isOpen`,
`Work.Spaces.deriv_deriv_fst_snd` of `Submission/Work/Spaces/mixed_comm.lean` is available). -/
theorem zsq_pzIter2_mixed_open (f : ℝ → ℝ → ℝ)
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (m i : ℕ) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.mixed m i f) z θ
      = Work.Spaces.mixed m i (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ) z θ := by
  have hF : SmoothOpen f := smoothOpen_of_forall hf
  have hA : SmoothOpen (Work.Spaces.mixed m i f) := hF.mixed m i
  -- the left-hand side is `D_z²(mixed m i f) - D_z(mixed m i f)`, which is
  -- `mixed (m+2) i f - mixed (m+1) i f`
  have hL : z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.mixed m i f) z θ
      = Work.Spaces.mixed (m + 2) i f z θ - Work.Spaces.mixed (m + 1) i f z θ := by
    rw [zsq_pzIter2_eq_open (Work.Spaces.mixed m i f) hA hz hθ]
    have e1 : Work.Spaces.DzIter 2 (Work.Spaces.mixed m i f) z θ
        = Work.Spaces.mixed (m + 2) i f z θ := by
      show Work.Spaces.DzIter 2 (Work.Spaces.DzIter m (Work.Spaces.DthIter i f)) z θ = _
      rw [← Work.Spaces.DzIter_add_right 2 m (Work.Spaces.DthIter i f)]
      rw [show 2 + m = m + 2 from by omega]
      rfl
    have e2 : Work.Spaces.Dz (Work.Spaces.mixed m i f) z θ
        = Work.Spaces.mixed (m + 1) i f z θ := by
      show Work.Spaces.DzIter 1 (Work.Spaces.DzIter m (Work.Spaces.DthIter i f)) z θ = _
      rw [← Work.Spaces.DzIter_add_right 1 m (Work.Spaces.DthIter i f)]
      rw [show 1 + m = m + 1 from by omega]
      rfl
    rw [e1, e2]
  -- the right-hand side, term by term
  have hR1 : Work.Spaces.mixed m i (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ) z θ
      = Work.Spaces.mixed m i (fun z θ => Work.Spaces.DzIter 2 f z θ
          - Work.Spaces.Dz f z θ) z θ := by
    refine mixed_congr_open ?_ m i z θ hz hθ.1 hθ.2
    intro z θ hz' h1 h2
    exact zsq_pzIter2_eq_open f hF hz' ⟨h1, h2⟩
  have hR2 : Work.Spaces.mixed m i (fun z θ => Work.Spaces.DzIter 2 f z θ
          - Work.Spaces.Dz f z θ) z θ
      = Work.Spaces.mixed m i (Work.Spaces.DzIter 2 f) z θ
        - Work.Spaces.mixed m i (Work.Spaces.Dz f) z θ :=
    mixed_sub_open (hF.DzIter 2) hF.Dz m i z θ hz hθ.1 hθ.2
  have hR3 : Work.Spaces.mixed m i (Work.Spaces.DzIter 2 f) z θ
      = Work.Spaces.mixed (m + 2) i f z θ :=
    mixed_DzIter_open f hF m i 2 z θ hz hθ.1 hθ.2
  have hR4 : Work.Spaces.mixed m i (Work.Spaces.Dz f) z θ
      = Work.Spaces.mixed (m + 1) i f z θ :=
    mixed_DzIter_open f hF m i 1 z θ hz hθ.1 hθ.2
  rw [hL, hR1, hR2, hR3, hR4]

end Work.FTS.EllipticEst.TTSlot11Aux
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.TT.Slot20Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.TT

set_option autoImplicit false

/-! ## The quantities -/





/-! ## Elementary facts about the weights -/

theorem sig2_eq (α θ : ℝ) :
    Work.FTS.EllipticEst.Mine.sig2 (Work.Spaces.gam α) θ
      = (Real.sin (2 * θ)) ^ ((2 : ℝ) - Work.Spaces.gam α) := rfl

theorem sig4_eq (α θ : ℝ) :
    Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) θ
      = (Real.sin (2 * θ)) ^ ((4 : ℝ) - Work.Spaces.gam α) := rfl

theorem sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) := by
  rw [Work.Spaces.Iθ] at hθ
  exact Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩


theorem w_nonneg (z : ℝ) : 0 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w]; exact div_nonneg (sq_nonneg _) (sq_nonneg _)




/-! ## Nonnegativity of the three quantities -/


theorem L2Sq_nonneg (g : ℝ → ℝ → ℝ) : 0 ≤ Work.Spaces.L2Sq g :=
  integral_nonneg fun _ => integral_nonneg fun _ => sq_nonneg _



/-! ## Weight comparisons on the open angular interval -/

/-- `1 ≤ sEta` on the open interval. -/
theorem one_le_sEta {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    1 ≤ Work.FTS.EllipticEst.sEta θ := by
  rw [Work.FTS.EllipticEst.sEta]
  exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos (sin_two_pos_of_mem_Ioo hθ)
    (Real.sin_le_one (2 * θ)) (by rw [Work.Spaces.eta]; norm_num)


/-- `σ₂ ≤ sEta` on the open interval. -/
theorem sig2_le_sEta (α : ℝ) (hα4 : α ≤ 1 / 4) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.FTS.EllipticEst.Mine.sig2 (Work.Spaces.gam α) θ ≤ Work.FTS.EllipticEst.sEta θ := by
  rw [sig2_eq, Work.FTS.EllipticEst.sEta]
  refine Real.rpow_le_rpow_of_exponent_ge (sin_two_pos_of_mem_Ioo hθ)
    (Real.sin_le_one (2 * θ)) ?_
  have hη : Work.Spaces.eta = 99 / 100 := rfl
  rw [hη, Work.Spaces.gam]; linarith

/-- `σ₄ ≤ sEta` on the open interval. -/
theorem sig4_le_sEta (α : ℝ) (hα4 : α ≤ 1 / 4) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) θ ≤ Work.FTS.EllipticEst.sEta θ := by
  rw [sig4_eq, Work.FTS.EllipticEst.sEta]
  refine Real.rpow_le_rpow_of_exponent_ge (sin_two_pos_of_mem_Ioo hθ)
    (Real.sin_le_one (2 * θ)) ?_
  have hη : Work.Spaces.eta = 99 / 100 := rfl
  rw [hη, Work.Spaces.gam]; linarith




end Work.FTS.EllipticEst.TT
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.TT.WeakDescent =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.TT

set_option autoImplicit false

/-- The diagonal-honesty integrand `z ↦ z ∂_z∂_θθΨ` is smooth of every finite order on the open
quadrant as soon as the same holds for `∂_θθΨ`: it is `D_z (∂_z (∂_θθΨ))`, and `SmoothOpen` is
closed under `D_z` and `∂_z`. -/
theorem smoothOpen_diagHon {Ψ : ℝ → ℝ → ℝ}
    (hB : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pthIter 2 Ψ))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry
      (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  have h2 : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 Ψ) :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall (Work.Spaces.pthIter 2 Ψ)).mpr hB
  have hDz : Work.FTS.EllipticEst.SmoothOpen
      (Work.Spaces.Dz (Work.Spaces.pthIter 2 Ψ)) :=
    Work.FTS.EllipticEst.SmoothOpen.Dz h2
  have hfun : Work.Spaces.Dz (Work.Spaces.pthIter 2 Ψ)
      = fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ := rfl
  rw [hfun] at hDz
  exact (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hDz


end Work.FTS.EllipticEst.TT

end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.ThetaU.OpenSliceIdents =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.ThetaU

set_option autoImplicit false

variable {f : ℝ → ℝ → ℝ}

/-! ## Differentiability of the angular slices of `C^∞` data -/

/-- The `θ`-slice of a function that is `C^∞` on an open set is differentiable at every point
of that set. -/
private lemma differentiableAt_slice_θ {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hG : ContDiffOn ℝ smoothOrder (Function.uncurry G) V) {z θ : ℝ} (hy : (z, θ) ∈ V) :
    DifferentiableAt ℝ (fun θ' => G z θ') θ :=
  ((hG.contDiffAt (hV.mem_nhds hy)).comp θ (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt
    (by norm_num)

/-! ## Congruence of the angular iterate on an open set -/

/-- `LopIter` respects agreement on an open set: if `u = v` on an open `V`, then so do all the
angular iterates.  (The operator `L u = sin(2θ)·u'` is local, so this is the induction
`deriv_congr` step.) -/
theorem LopIter_congr_of_isOpen {u v : ℝ → ℝ} {V : Set ℝ} (hV : IsOpen V)
    (h : Set.EqOn u v V) (i : ℕ) :
    Set.EqOn (Work.FTS.EllipticEst.LopIter i u) (Work.FTS.EllipticEst.LopIter i v) V := by
  induction i with
  | zero => exact h
  | succ i ih =>
      intro θ hθ
      have hev : Work.FTS.EllipticEst.LopIter i u =ᶠ[𝓝 θ]
          Work.FTS.EllipticEst.LopIter i v := by
        filter_upwards [hV.mem_nhds hθ] with θ' hθ'
        exact ih hθ'
      rw [Work.FTS.EllipticEst.LopIter_succ, Work.FTS.EllipticEst.LopIter_succ]
      show Real.sin (2 * θ) * deriv (Work.FTS.EllipticEst.LopIter i u) θ
        = Real.sin (2 * θ) * deriv (Work.FTS.EllipticEst.LopIter i v) θ
      rw [hev.deriv_eq]

/-! ## Clairaut: `∂_θ` commutes with every `D_z`-iterate -/





/-! ## The angular iterates of the slices -/




end Work.FTS.EllipticEst.ThetaU
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.SourceBound.pzBoxIntegrableOfSlice =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov.SourceBound

open scoped Real Topology Interval
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false


end Work.FTS.EllipticEst.remov.SourceBound
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.SourceBound.pzSliceHonestOfBox =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov.SourceBound

set_option autoImplicit false

/-! ## A fundamental-theorem-of-calculus bound valid on the closed interval

The slice bound `pzSliceFtcBound` of the sibling file `SourceBound/pzSliceFtcBound.lean` is stated
for `z ∈ (a,b]`.  The honesty statement `pzSliceHonestOfBox` needs it at *every* `z ∈ [a,b]`,
in particular at the left endpoint `z = a`; the proof below is that of `pzSliceFtcBound` with the
hypothesis `hz` weakened from `z ∈ Ioc a b` to `z ∈ Icc a b` (the interval intgeral is taken over
the whole of `[a,b]`, which contains both `z` and `z₀`). -/



end Work.FTS.EllipticEst.remov.SourceBound

end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.SourceBound.sliceShiftedDecomposition =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The shifted slice decomposition

`sliceShiftedDecomposition`: differentiating the elliptic equation `bslOp α Ψ = F` in the
radial variable `z` and rearranging gives, at every point `(z,θ)` of the open quadrant,

  `Lzero1 (∂_zΨ z ·) θ - α(5+α)·∂_zΨ(z,θ)`
    `= ∂_zF(z,θ) + α²·∂_z(z²∂_zzΨ)(z,θ) + (α²+5α)·z·∂_zzΨ(z,θ)`.

Since `bslOp α Ψ = -α²z²∂_zzΨ - α(5+α)z∂_zΨ + Lzero Ψ`, the content is (i) the commutation
of `∂_z` with the angular operator `Lzero` (`pz_Lzero_eq`, via Clairaut/Schwarz
`Work.Spaces.pz_pth_comm` and the locality lemmas `pz_congr_of_isOpen`/`pth_congr_of_isOpen`)
and (ii) the elementary product rule for the two radial terms.  The source `F` is only known
to agree with `bslOp α Ψ` on the open half-line, so `∂_zF` is computed from that local
equality (`Filter.EventuallyEq.deriv_eq`).
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov.SourceBound

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Auxiliary vocabulary and elementary facts -/

/-- `tan θ · g` as a two-variable function: the angular factor of `Work.Elliptic.Lzero`. -/
private def tanMul (g : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => Real.tan θ * g z θ

/-- `∂_z` commutes with multiplication by `tan θ`. -/
private lemma pz_tanMul (g : ℝ → ℝ → ℝ) :
    Work.Spaces.pz (tanMul g) = tanMul (Work.Spaces.pz g) := by
  funext z θ
  simp only [tanMul, Work.Spaces.pz]
  rw [deriv_const_mul_field]

/-- `ContDiffAt`-form of `SmoothOpen` at an interior point of the open quadrant. -/
private lemma smoothOpen_contDiffAt_two' {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    ContDiffAt ℝ 2 (Function.uncurry f) (z, θ) :=
  (hf.forall 2).contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds
    (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩))

/-- `SmoothOpen` of `(z,θ) ↦ tan θ · Ψ z θ` (the angular factor `tan` is smooth on the
open quadrant). -/
private lemma smoothOpen_tanMul {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    Work.FTS.EllipticEst.SmoothOpen (tanMul Ψ) := by
  change ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry (tanMul Ψ))
    Work.FTS.EllipticEst.Q0
  rw [show Function.uncurry (tanMul Ψ)
      = fun p : ℝ × ℝ => Real.tan p.2 * Ψ p.1 p.2 from rfl]
  have htan : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Real.tan p.2) Work.FTS.EllipticEst.Q0 := by
    have hs : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => Real.sin p.2) Work.FTS.EllipticEst.Q0 := by
      change ContDiffOn ℝ Work.Stability.smoothOrder (Real.sin ∘ Prod.snd)
        Work.FTS.EllipticEst.Q0
      exact Real.contDiff_sin.comp_contDiffOn contDiffOn_snd
    have hc : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => Real.cos p.2) Work.FTS.EllipticEst.Q0 := by
      change ContDiffOn ℝ Work.Stability.smoothOrder (Real.cos ∘ Prod.snd)
        Work.FTS.EllipticEst.Q0
      exact Real.contDiff_cos.comp_contDiffOn contDiffOn_snd
    have hne : ∀ p ∈ Work.FTS.EllipticEst.Q0, Real.cos p.2 ≠ 0 := by
      intro p hp
      obtain ⟨-, h1, h2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
      exact ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, h1], h2⟩)
    have hdiv : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => Real.sin p.2 / Real.cos p.2) Work.FTS.EllipticEst.Q0 :=
      hs.div hc hne
    refine hdiv.congr (fun p _ => ?_)
    rw [Real.tan_eq_sin_div_cos]
  have hΨ' : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Ψ p.1 p.2) Work.FTS.EllipticEst.Q0 := hΨ
  exact htan.mul hΨ'

/-! ## Commutation of `∂_z` with the angular operator `Lzero` -/

/-- `∂_z ∂_θ² Ψ = ∂_θ² ∂_z Ψ` on the open quadrant (two instances of Clairaut). -/
private lemma pz_pthIter_two_eq {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ
      = Work.Spaces.pthIter 2 (Work.Spaces.pz Ψ) z θ := by
  have hV : IsOpen (Work.FTS.EllipticEst.Q0) := Work.FTS.EllipticEst.isOpen_Q0
  have hp : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩
  have h1 : Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.pth Ψ)) z θ
      = Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.pth Ψ)) z θ :=
    Work.Spaces.pz_pth_comm (smoothOpen_contDiffAt_two' hΨ.pth hz hθ)
  have heqon : Set.EqOn (Function.uncurry (Work.Spaces.pz (Work.Spaces.pth Ψ)))
      (Function.uncurry (Work.Spaces.pth (Work.Spaces.pz Ψ))) Work.FTS.EllipticEst.Q0 := by
    intro p hp'
    obtain ⟨hz', hθ'1, hθ'2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp'
    exact Work.Spaces.pz_pth_comm (smoothOpen_contDiffAt_two' hΨ hz' ⟨hθ'1, hθ'2⟩)
  have h2 : Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.pth Ψ)) z θ
      = Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.pz Ψ)) z θ :=
    Work.Spaces.pth_congr_of_isOpen hV heqon hp
  show Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.pth Ψ)) z θ
      = Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.pz Ψ)) z θ
  rw [h1, h2]

/-- `∂_z ∂_θ(tan θ · Ψ) = ∂_θ ∂_z(tan θ · Ψ)` on the open quadrant. -/
private lemma pz_pth_tanMul_eq {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.pz (Work.Spaces.pth (tanMul Ψ)) z θ
      = Work.Spaces.pth (tanMul (Work.Spaces.pz Ψ)) z θ := by
  have hp : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩
  have hC2 : ContDiffAt ℝ 2 (Function.uncurry (tanMul Ψ)) (z, θ) :=
    ((smoothOpen_tanMul hΨ).forall 2).contDiffAt
      (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hp)
  rw [Work.Spaces.pz_pth_comm hC2, pz_tanMul]

/-! ## The differentiated `Lzero`-slice -/

/-- **The derivative of the `θ`-slice of `Lzero`.**  The derivative at `z` of
`z' ↦ Lzero Ψ z' θ` is `Lzero1` applied to the slice `t ↦ ∂_zΨ(z,t)`. -/
private lemma hasDerivAt_Lzero_slice {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    HasDerivAt (fun z' => Work.Elliptic.Lzero Ψ z' θ)
      (Work.FTS.EllipticEst.Lzero1 (fun t => Work.Spaces.pz Ψ z t) θ) z := by
  have htanmul : Work.FTS.EllipticEst.SmoothOpen (tanMul Ψ) := smoothOpen_tanMul hΨ
  have hd1 : HasDerivAt (fun z' => Work.Spaces.pthIter 2 Ψ z' θ)
      (Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ) z :=
    (hΨ.pth.pth).hasDerivAt_slice hθ hz
  have hd2 : HasDerivAt (fun z' => Work.Spaces.pth (tanMul Ψ) z' θ)
      (Work.Spaces.pz (Work.Spaces.pth (tanMul Ψ)) z θ) z :=
    htanmul.pth.hasDerivAt_slice hθ hz
  have hd3 : HasDerivAt (fun z' => Ψ z' θ) (Work.Spaces.pz Ψ z θ) z :=
    hΨ.hasDerivAt_slice hθ hz
  have hsum : HasDerivAt (fun z' => -(Work.Spaces.pthIter 2 Ψ z' θ)
        + Work.Spaces.pth (tanMul Ψ) z' θ - 6 * Ψ z' θ)
      ((-(Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ)
        + Work.Spaces.pz (Work.Spaces.pth (tanMul Ψ)) z θ) - 6 * Work.Spaces.pz Ψ z θ) z :=
    (hd1.neg.add hd2).sub (hd3.const_mul 6)
  have hval : ((-(Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ)
        + Work.Spaces.pz (Work.Spaces.pth (tanMul Ψ)) z θ) - 6 * Work.Spaces.pz Ψ z θ)
      = Work.FTS.EllipticEst.Lzero1 (fun t => Work.Spaces.pz Ψ z t) θ := by
    rw [pz_pthIter_two_eq hΨ hz hθ, pz_pth_tanMul_eq hΨ hz hθ, Lzero1_slice_eq]
    rfl
  rw [hval] at hsum
  refine hsum.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun z' => ?_))
  rfl


/-! ## The decomposition -/

theorem sliceShiftedDecomposition {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hk : 2 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) :
    ∀ z, 0 < z → ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Work.FTS.EllipticEst.Lzero1 (fun t => Work.Spaces.pz Ψ z t) θ
          - (α * (5 + α)) * Work.Spaces.pz Ψ z θ
        = Work.Spaces.pz F z θ
          + α ^ 2 * Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
          + (α ^ 2 + 5 * α) * (z * Work.Spaces.pzIter 2 Ψ z θ) := by
  intro z hz θ hθ
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  -- `F` agrees with `bslOp α Ψ` on a neighbourhood of `z` along the slice `θ`
  have hloc : (fun z' => F z' θ) =ᶠ[𝓝 z] (fun z' => Work.Elliptic.bslOp α Ψ z' θ) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    exact (h.eq z' hz' θ hθ.1 hθ.2).symm
  have hpzF : Work.Spaces.pz F z θ = deriv (fun z' => Work.Elliptic.bslOp α Ψ z' θ) z := by
    show deriv (fun z' => F z' θ) z = deriv (fun z' => Work.Elliptic.bslOp α Ψ z' θ) z
    exact hloc.deriv_eq
  -- the three summands of `bslOp`, differentiated along `z`
  have hd1 : HasDerivAt (fun z' => z' ^ 2 * Work.Spaces.pzIter 2 Ψ z' θ)
      (Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) z := by
    have hdiff : DifferentiableAt ℝ (fun z' => z' ^ 2 * Work.Spaces.pzIter 2 Ψ z' θ) z :=
      (((hasDerivAt_id z).pow 2).mul (hΨ.hasDerivAt_slice_pzIter 2 hθ hz)).differentiableAt
    exact hdiff.hasDerivAt
  have hd2a : HasDerivAt (fun z' => z' * Work.Spaces.pz Ψ z' θ)
      (1 * Work.Spaces.pz Ψ z θ + z * Work.Spaces.pzIter 2 Ψ z θ) z := by
    have h2 : HasDerivAt (fun z' : ℝ => Work.Spaces.pzIter 1 Ψ z' θ)
        (Work.Spaces.pzIter 2 Ψ z θ) z := hΨ.hasDerivAt_slice_pzIter 1 hθ hz
    exact (hasDerivAt_id z).mul h2
  have hd2 : HasDerivAt (fun z' => z' * Work.Spaces.pz Ψ z' θ)
      (Work.Spaces.pz Ψ z θ + z * Work.Spaces.pzIter 2 Ψ z θ) z := by
    refine hd2a.congr_deriv ?_
    ring
  have hd3 : HasDerivAt (fun z' => Work.Elliptic.Lzero Ψ z' θ)
      (Work.FTS.EllipticEst.Lzero1 (fun t => Work.Spaces.pz Ψ z t) θ) z :=
    hasDerivAt_Lzero_slice hΨ hz hθ
  have hbsl : HasDerivAt (fun z' => Work.Elliptic.bslOp α Ψ z' θ)
      (-(α ^ 2) * Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
        + -(α * (5 + α)) * (Work.Spaces.pz Ψ z θ + z * Work.Spaces.pzIter 2 Ψ z θ)
        + Work.FTS.EllipticEst.Lzero1 (fun t => Work.Spaces.pz Ψ z t) θ) z := by
    have h1 := hd1.const_mul (-(α ^ 2))
    have h2 := hd2.const_mul (-(α * (5 + α)))
    have hsum := (h1.add h2).add hd3
    refine hsum.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun z' => ?_))
    change Work.Elliptic.bslOp α Ψ z' θ
      = -(α ^ 2) * (z' ^ 2 * Work.Spaces.pzIter 2 Ψ z' θ)
        + -(α * (5 + α)) * (z' * Work.Spaces.pz Ψ z' θ) + Work.Elliptic.Lzero Ψ z' θ
    rw [Work.Elliptic.bslOp_apply]
    ring
  have hkey : Work.Spaces.pz F z θ
      = -(α ^ 2) * Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
        - (α * (5 + α)) * (Work.Spaces.pz Ψ z θ + z * Work.Spaces.pzIter 2 Ψ z θ)
        + Work.FTS.EllipticEst.Lzero1 (fun t => Work.Spaces.pz Ψ z t) θ := by
    rw [hpzF, hbsl.deriv]
    ring
  rw [hkey]
  ring

end Work.FTS.EllipticEst.remov.SourceBound
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.high_slice_chain_slots =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `high_slice_chain_slots`: the high angular slots of `Ψ` are controlled by `|F|_k`

The target is the estimate

`∑_{j ∈ Icc 3 (k+1)} ∫_z w² ∫_θ (∂_θ^j Ψ)² sin(2θ)^{2j-4-γ} ≤ C · HkSq α k F`

for data of the weak class `EllWeakPos α k F Ψ`, `0 < α ≤ 1/4`, `k ≥ 2`, under the single
norm hypothesis `‖∂_θ²Ψ‖_{k-1} ≤ D ‖F‖_k`; the constant `C` depends only on `k` and `D`.

The mathematically essential point (`NOTES_high_slice_chain_FALSE.md`) is that the *sharp*
expansion of `D_θ` (`dthCoef`) has no `∂_θ^0`-term as soon as `D_θ` has been applied once
(`dthCoef_succ_zero`); hence `∂_θ^jΨ` (`j ≥ 3`) is a triangular combination of the
`D_θ`-slots `D_θ^r(∂_θ²Ψ)`, `1 ≤ r ≤ j-2`, of the *sibling* function `∂_θ²Ψ` — exactly the
slots whose `w² sin(2θ)^{-γ}`-masses are the summands of `HkSq α (k-1) (∂_θ²Ψ)`.  The
`j = 2` summand (the pure `γ`-slot of `∂_θ²Ψ`) is deliberately absent from the sum: it is
*not* controlled by `HkSq`, which is what made the sibling `high_slice_chain` false.

The two analytic/syntactic pieces are proved in the sibling modules

* `remov.high_chain_sum_self` — `∑_{m ∈ Icc 1 K} ∫_z w² ∫_θ (∂_θ^m v)² sin(2θ)^{2m-γ}
  ≤ C_K |v|²_{H^K}` for `v` smooth on the open quadrant with `HkMem α K v` (constant
  independent of `α`).  (The same statement is proved by the colleagues of
  `remov.high_chain_sum`; the `_self` copy is used here because the import cone of that
  module is temporarily broken by an unrelated, in-flight file of another area,
  `Submission.Work.EllipticEst.EllHyp_hkMem_V_fts`.  The statement is unchanged.)
* the reindexing `j = m + 2`, i.e. `∂_θ^{m+2}Ψ = ∂_θ^m (∂_θ²Ψ)`, which is proved locally
  below (`high_slice_sum_reindex_local`) so that this file's import cone stays clean.

Here we only assemble: `HkMem α (k-1) (∂_θ²Ψ)` is obtained from the given
`HkMem α k (∂_θ²Ψ)` (`EllWeakPos.memB`) by the open-quadrant descent
`Work.FTS.EllipticEst.TT.HkMem_descend_open`, the squared norms are compared with
`HkNorm`-bounds, and the two norms are matched by the given hypothesis.
-/

namespace Work.FTS.EllipticEst.remov

open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- The open quadrant `(0,∞) × (0,π/2)`; the regularity class of `EllWeakPos.smooth`. -/
abbrev Qd2 : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)

theorem isOpen_Qd2 : IsOpen Qd2 := isOpen_Ioi.prod isOpen_Ioo

/-! ## Elementary `HkNorm`/`HkSq` bookkeeping -/

/-- `HkSq` is the square of `HkNorm`. -/
theorem HkSq_eq_HkNorm_sq (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.HkSq α k f = (Work.Spaces.HkNorm α k f) ^ 2 := by
  rw [Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α k f)]

/-- A bound of `HkNorm`s at possibly different orders gives the corresponding bound of
`HkSq`s. -/
theorem HkSq_le_of_HkNorm_le {α : ℝ} {k l : ℕ} {f g : ℝ → ℝ → ℝ} {D : ℝ} (_hD : 0 ≤ D)
    (h : Work.Spaces.HkNorm α k f ≤ D * Work.Spaces.HkNorm α l g) :
    Work.Spaces.HkSq α k f ≤ D ^ 2 * Work.Spaces.HkSq α l g := by
  rw [HkSq_eq_HkNorm_sq, HkSq_eq_HkNorm_sq]
  calc (Work.Spaces.HkNorm α k f) ^ 2
      ≤ (D * Work.Spaces.HkNorm α l g) ^ 2 :=
        pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α k f) h 2
    _ = D ^ 2 * (Work.Spaces.HkNorm α l g) ^ 2 := by ring

/-! ## Finite-order smoothness of `∂_θ` -/

/-- The partial `θ`-derivative of a function that is `C^{n+1}` on the open quadrant is `C^n`
there.  (`Work.Spaces.contDiffOn_uncurry_pth` is the corresponding `C^∞` statement, which is
*not* applicable: in the `ContDiff` notation `⊤` denotes analyticity `ω`, while the class of
`EllWeakPos` is finite-order smoothness.) -/
theorem contDiffOn_uncurry_pth_fin_Qd {G : ℝ → ℝ → ℝ} {n : ℕ}
    (h : ContDiffOn ℝ (n + 1) (Function.uncurry G) Qd2) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pth G)) Qd2 := by
  have key : ∀ (z θ : ℝ), (z, θ) ∈ Qd2 →
      Work.Spaces.pth G z θ = fderiv ℝ (Function.uncurry G) (z, θ) (0, 1) :=
    fun z θ hzθ => Work.Spaces.pth_eq_fderiv
      ((h.differentiableOn (by norm_num : (n + 1 : WithTop ℕ∞) ≠ 0)).differentiableAt
        (isOpen_Qd2.mem_nhds hzθ))
  have hfd : ContDiffOn ℝ n (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p) Qd2 :=
    h.fderiv_of_isOpen isOpen_Qd2 (m := n) (by norm_num)
  have hcomp : ContDiffOn ℝ n (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) (0, 1)) Qd2 :=
    hfd.clm_apply contDiffOn_const
  refine hcomp.congr (fun p hp => ?_)
  obtain ⟨z, θ⟩ := p
  exact key z θ hp

/-- `∂_θ²Ψ = pthIter 2 Ψ` is `C^n` on the open quadrant for every `n` as soon as `Ψ` is. -/
theorem smooth_pthIter_two (Ψ : ℝ → ℝ → ℝ)
    (h : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ) Qd2) :
    ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pthIter 2 Ψ)) Qd2 := by
  intro n
  have h1 : ContDiffOn ℝ (n + 2) (Function.uncurry Ψ) Qd2 := h (n + 2)
  have h2 : ContDiffOn ℝ (n + 1) (Function.uncurry (Work.Spaces.pth Ψ)) Qd2 := by
    have := contDiffOn_uncurry_pth_fin_Qd (n := n + 1) h1
    simpa using this
  have h3 : ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pth (Work.Spaces.pth Ψ))) Qd2 := by
    have := contDiffOn_uncurry_pth_fin_Qd (n := n) h2
    simpa using this
  exact h3

/-! ## The reindexing of the high angular slots -/

/-- `∂_θ^{m+n} f = ∂_θ^m (∂_θ^n f)`. -/
theorem pthIter_add_local (m n : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pthIter (m + n) f = Work.Spaces.pthIter m (Work.Spaces.pthIter n f) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Nat.succ_add, Work.Spaces.pthIter_succ, ih, Work.Spaces.pthIter_succ]

/-- The on-the-nose exponent bookkeeping of the reindexing `j = m + 2`. -/
theorem two_mul_add_two_sub_four (m : ℕ) (α : ℝ) :
    2 * ((m + 2 : ℕ) : ℝ) - 4 - Work.Spaces.gam α = 2 * (m : ℝ) - Work.Spaces.gam α := by
  push_cast
  ring

/-- **Reindexing the high angular slots.**  For `k ≥ 2` the sum over `j ∈ Icc 3 (k+1)` of the
high angular slots of `Ψ` is the sum over `m ∈ Icc 1 (k-1)` of the same slots of
`v = ∂_θ²Ψ`: the substitution is `j = m + 2`, and on matched indices
`pthIter (m+2) Ψ = pthIter m (pthIter 2 Ψ)` while
`2 * ((m+2 : ℕ) : ℝ) - 4 - gam α = 2 * (m : ℝ) - gam α`. -/
theorem high_slice_sum_reindex_local (k : ℕ) (hk : 2 ≤ k) (α : ℝ) (Ψ : ℝ → ℝ → ℝ) :
    (∑ j ∈ Finset.Icc 3 (k + 1), ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter j Ψ z θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (2 * (j : ℝ) - 4 - Work.Spaces.gam α)))
    = (∑ m ∈ Finset.Icc 1 (k - 1), ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter m (Work.Spaces.pthIter 2 Ψ) z θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (2 * (m : ℝ) - Work.Spaces.gam α))) := by
  have himage : (Finset.Icc 1 (k - 1)).image (fun m => m + 2) = Finset.Icc 3 (k + 1) := by
    have h := Finset.image_add_right_Icc (α := ℕ) 1 (k - 1) 2
    have h2 : (k - 1) + 2 = k + 1 := by omega
    rw [show 1 + 2 = 3 from rfl, h2] at h
    exact h
  have hinj : Set.InjOn (fun m : ℕ => m + 2) (↑(Finset.Icc 1 (k - 1)) : Set ℕ) :=
    fun a _ b _ hab => Nat.add_right_cancel hab
  rw [← himage, Finset.sum_image hinj]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [pthIter_add_local m 2 Ψ, two_mul_add_two_sub_four m α]

/-! ## The target -/

theorem high_slice_chain_slots (D : ℝ) (hD : 0 < D) :
    ∀ k : ℕ, 2 ≤ k → ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ →
      Work.Spaces.HkNorm α (k - 1) (Work.Spaces.pthIter 2 Ψ) ≤ D * Work.Spaces.HkNorm α k F →
      α ^ 2 * Work.Spaces.HkNorm α (k - 1)
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ)
          + Work.Spaces.HkNorm α (k - 1) (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
        ≤ D * Work.Spaces.HkNorm α k F →
      (∑ j ∈ Finset.Icc 3 (k + 1), ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
            ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter j Ψ z θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (2 * (j : ℝ) - 4 - Work.Spaces.gam α))
        ≤ C * Work.Spaces.HkSq α k F := by
  intro k hk
  obtain ⟨C0, hC0pos, hC0⟩ := high_chain_sum_self (k - 1)
  refine ⟨C0 * D ^ 2 + 1, by positivity, ?_⟩
  intro α F Ψ hα hα4 hpos h1 h2
  -- the regularity of `v = ∂_θ²Ψ` on the open quadrant, at every finite order
  have hsmooth : ∀ n : ℕ, ContDiffOn ℝ n
      (Function.uncurry (Work.Spaces.pthIter 2 Ψ)) Qd2 :=
    smooth_pthIter_two Ψ (fun n => hpos.smooth n)
  -- `HkMem` descends from the given order `k` to the order `k-1` of the chain
  have hmemK : Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 Ψ) := hpos.memB
  have hmemL : Work.Spaces.HkMem α (k - 1) (Work.Spaces.pthIter 2 Ψ) :=
    Work.FTS.EllipticEst.TT.HkMem_descend_open (Nat.sub_le k 1) hsmooth hmemK
  -- the angular chain at level `k-1`, uniform in `α`
  have hchain := hC0 α (Work.Spaces.pthIter 2 Ψ) hα hsmooth hmemL
  -- the reindexing `j = m + 2`
  have hreindex := high_slice_sum_reindex_local k hk α Ψ
  -- the norm hypothesis, squared
  have hsq : Work.Spaces.HkSq α (k - 1) (Work.Spaces.pthIter 2 Ψ)
      ≤ D ^ 2 * Work.Spaces.HkSq α k F := HkSq_le_of_HkNorm_le hD.le h1
  rw [hreindex]
  refine le_trans hchain ?_
  refine le_trans (mul_le_mul_of_nonneg_left hsq hC0pos.le) ?_
  have hnn : 0 ≤ Work.Spaces.HkSq α k F := Work.Spaces.HkSq_nonneg α k F
  nlinarith [hC0pos, sq_nonneg D]

end Work.FTS.EllipticEst.remov
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.pzSinCos2_rectIntegrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!

# Integrability of `∂_zΨ · sinθcos²θ` on the radial rectangle `(r, z₁] × Iθ`

This is the Fubini/Tonelli bookkeeping step that turns an *honest* slice integrability of the
second `z`-derivative of the source into joint integrability of the first `z`-derivative against
the angular weight `sinCos2 θ = sinθ cos²θ`.

The hypotheses are exactly the two "honest" consequences of the weak positivity class produced
by the sibling target `remov/hkMemSliceAbsIntegrable`:

* `hsl` : every angular slice `θ ↦ |∂_z²Ψ(z,θ)| sinθcos²θ`, `z ∈ [r,z₁]`, is integrable;
* `hFint` : the iterated integral `z ↦ ∫_{Iθ} |∂_z²Ψ(z,θ)| sinθcos²θ` is integrable on `[r,z₁]`.

(Without `hsl`/`hFint` the statement would be *false*: the Bochner integral of a non-integrable
nonnegative function is `0`, so a hypothesis stated with such an integral carries no information —
see `NOTES_pzMulSinCos2RectIntegrable_FALSE.md` for the machine-checked counterexample of the
naive form.)

The proof:

1. `Fubini–Tonelli` (`Work.FTS.EllipticEst.integrable_prod_ae`) applied to the *nonnegative*
   source `g z θ = |∂_z²Ψ(z,θ)| sinθcos²θ` gives joint integrability of `g` on `(r,z₁] × Iθ`;
   a.e. strong measurability comes from continuity on the open quadrant
   (`aesm_uncurry_restrict_open`), the slice hypothesis from `hsl` and the iterated-integral
   hypothesis from `hFint` (up to the null difference between `Icc` and `Ioc`).
2. `Integrable.integral_prod_right` then makes `θ ↦ ∫_r^{z₁} ‖∂_z²Ψ(s,θ) sinθcos²θ‖ ds`
   integrable on `Iθ`.
3. The elementary slice FTC bound `remov/SourceBound/pzSliceFtcBound` bounds the weighted first
   `z`-derivative by `‖∂_zΨ(r,θ) sinθcos²θ‖ + ∫_r^{z₁} ‖∂_z²Ψ(s,θ) sinθcos²θ‖ ds` for every
   `z ∈ (r,z₁]` and every interior angle, and the first summand is integrable by `hBr`.  Hence
   the slice `θ ↦ ∂_zΨ(z,θ) sinθcos²θ` is integrable (`Integrable.mono'`) for *every*
   `z ∈ (r,z₁]`.
4. The same dominating function is independent of `z` and integrable in `θ`, so the outer
   integral `z ↦ ∫_θ ‖∂_zΨ(z,θ) sinθcos²θ‖ dθ` is bounded by a constant, hence integrable on the
   bounded interval `(r,z₁]`; `integrable_prod_iff` concludes.

-/

namespace Work.FTS.EllipticEst.remov

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

private theorem sinCos2_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.Elliptic.sinCos2 θ := by
  rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
  have hs : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [Real.pi_pos])
  have hc : 0 ≤ Real.cos θ := Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith) hθ.2
  rw [Work.Elliptic.sinCos2]
  positivity

private theorem continuous_sinCos2 : Continuous Work.Elliptic.sinCos2 :=
  Real.continuous_sin.mul (Real.continuous_cos.pow 2)

theorem pzSinCos2_rectIntegrable {Ψ : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {r z₁ : ℝ} (hr : 0 < r) (hrz : r < z₁)
    (hBr : MeasureTheory.Integrable
      (fun θ : ℝ => Work.Spaces.pz Ψ r θ * Work.Elliptic.sinCos2 θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hsl : ∀ z ∈ Set.Icc r z₁, MeasureTheory.IntegrableOn
      (fun θ : ℝ => |Work.Spaces.pzIter 2 Ψ z θ| * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ)
    (hFint : MeasureTheory.IntegrableOn
      (fun s : ℝ => ∫ θ in Work.Spaces.Iθ,
        |Work.Spaces.pzIter 2 Ψ s θ| * Work.Elliptic.sinCos2 θ)
      (Set.Icc r z₁)) :
    MeasureTheory.Integrable
      (Function.uncurry (fun z θ : ℝ => Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ))
      ((MeasureTheory.volume.restrict (Set.Ioc r z₁)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))
  := by
  -- `(r,z₁]` and `[r,z₁]` carry the same measure (they differ by the null set `{r}`).
  have hIocIcc : MeasureTheory.volume.restrict (Set.Ioc r z₁)
      = MeasureTheory.volume.restrict (Set.Icc r z₁) :=
    MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioc_ae_eq_Icc
  -- the radial measure of the bounded interval `(r,z₁]` is finite
  haveI hfinμ : MeasureTheory.IsFiniteMeasure (MeasureTheory.volume.restrict (Set.Ioc r z₁)) :=
    ⟨by rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
        Real.volume_Ioc]
        exact ENNReal.ofReal_lt_top⟩
  -- the angular weight is nonnegative on `Iθ`
  have hsrc_nn : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      0 ≤ Work.Elliptic.sinCos2 θ :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
      (fun θ hθ => sinCos2_nonneg_Iθ hθ)
  -- the angular slices of the source are a.e. strongly measurable
  have hcont_src : ContinuousOn
      (fun p : ℝ × ℝ => |Work.Spaces.pzIter 2 Ψ p.1 p.2| * Work.Elliptic.sinCos2 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    ((hsm.pzIter 2).continuousOn.abs).mul
      (continuous_sinCos2.comp continuous_snd).continuousOn
  -- continuity of the uncurried integrand on the open quadrant
  have hcont_pz : ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.pz Ψ p.1 p.2 * Work.Elliptic.sinCos2 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    ((hsm.pz).continuousOn).mul
      (continuous_sinCos2.comp continuous_snd).continuousOn
  -- ## Step 1: joint integrability of the nonnegative second-derivative source
  have hgInt : MeasureTheory.Integrable
      (Function.uncurry
        (fun z θ : ℝ => |Work.Spaces.pzIter 2 Ψ z θ| * Work.Elliptic.sinCos2 θ))
      ((MeasureTheory.volume.restrict (Set.Ioc r z₁)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    refine Work.FTS.EllipticEst.integrable_prod_ae ?_ ?_ ?_ ?_
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with z hz
      exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
        (fun θ hθ => mul_nonneg (abs_nonneg _) (sinCos2_nonneg_Iθ hθ))
    · exact Work.FTS.EllipticEst.aesm_uncurry_restrict_open _ hcont_src (le_of_lt hr)
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with z hz
      exact hsl z ⟨le_of_lt hz.1, hz.2⟩
    · rw [hIocIcc]
      simpa only [MeasureTheory.IntegrableOn] using hFint
  -- ## Step 2: the radial integral of the second derivative is integrable in `θ`
  have hIntZ : MeasureTheory.Integrable
      (fun θ : ℝ => (∫ z in Set.Ioc r z₁, |Work.Spaces.pzIter 2 Ψ z θ|)
        * Work.Elliptic.sinCos2 θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    have hraw := hgInt.integral_prod_right
    refine hraw.congr (Filter.Eventually.of_forall (fun θ => ?_))
    show (∫ z in Set.Ioc r z₁, |Work.Spaces.pzIter 2 Ψ z θ| * Work.Elliptic.sinCos2 θ)
      = (∫ z in Set.Ioc r z₁, |Work.Spaces.pzIter 2 Ψ z θ|) * Work.Elliptic.sinCos2 θ
    rw [MeasureTheory.integral_mul_const]
  have hA2 : MeasureTheory.Integrable
      (fun θ : ℝ => ∫ s in r..z₁, ‖Work.Spaces.pzIter 2 Ψ s θ * Work.Elliptic.sinCos2 θ‖)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    refine hIntZ.congr ?_
    filter_upwards [hsrc_nn] with θ hθ
    show (∫ z in Set.Ioc r z₁, |Work.Spaces.pzIter 2 Ψ z θ|) * Work.Elliptic.sinCos2 θ
      = ∫ s in r..z₁, ‖Work.Spaces.pzIter 2 Ψ s θ * Work.Elliptic.sinCos2 θ‖
    rw [intervalIntegral.integral_of_le hrz.le]
    rw [← MeasureTheory.integral_mul_const]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    show |Work.Spaces.pzIter 2 Ψ z θ| * Work.Elliptic.sinCos2 θ
      = ‖Work.Spaces.pzIter 2 Ψ z θ * Work.Elliptic.sinCos2 θ‖
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hθ]
  -- ## Step 3: the dominating angular function is integrable
  have hA1 : MeasureTheory.Integrable
      (fun θ : ℝ => ‖Work.Spaces.pz Ψ r θ * Work.Elliptic.sinCos2 θ‖)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hBr.norm
  have hH : MeasureTheory.Integrable
      (fun θ : ℝ => ‖Work.Spaces.pz Ψ r θ * Work.Elliptic.sinCos2 θ‖
        + ∫ s in r..z₁, ‖Work.Spaces.pzIter 2 Ψ s θ * Work.Elliptic.sinCos2 θ‖)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hA1.add hA2
  -- ## Step 4: the slice FTC bound, a.e. in the angle
  have hbound : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      ∀ z ∈ Set.Ioc r z₁,
        ‖Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ‖
          ≤ ‖Work.Spaces.pz Ψ r θ * Work.Elliptic.sinCos2 θ‖
              + ∫ s in r..z₁, ‖Work.Spaces.pzIter 2 Ψ s θ * Work.Elliptic.sinCos2 θ‖ := by
    filter_upwards [Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo
      (p := fun θ : ℝ => θ ∈ Set.Ioo (0 : ℝ) (π / 2)) (fun θ hθ => hθ)] with θ hθ
    intro z hz
    exact Work.FTS.EllipticEst.remov.SourceBound.pzSliceFtcBound hr hrz.le
      ⟨le_rfl, hrz.le⟩ hsm hz hθ
  -- ## Step 5: every angular slice of `∂_zΨ · sinCos2` in the rectangle is integrable
  have hsliceAll : ∀ z ∈ Set.Ioc r z₁, MeasureTheory.Integrable
      (fun θ : ℝ => Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    intro z hz
    have hzpos : 0 < z := lt_trans hr hz.1
    refine MeasureTheory.Integrable.mono' hH ?_ ?_
    · refine Work.Spaces.aesm_slice_of_continuousOn_Qd
        (fun p : ℝ × ℝ => Work.Spaces.pz Ψ p.1 p.2 * Work.Elliptic.sinCos2 p.2)
        hcont_pz hzpos
    · exact hbound.mono (fun θ hθ => hθ z hz)
  -- ## Step 6: a.e. strong measurability of the uncurried integrand
  have hAESM : MeasureTheory.AEStronglyMeasurable
      (Function.uncurry (fun z θ : ℝ => Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ))
      ((MeasureTheory.volume.restrict (Set.Ioc r z₁)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.FTS.EllipticEst.aesm_uncurry_restrict_open _ hcont_pz (le_of_lt hr)
  -- ## Step 7: the outer integral is integrable (bounded by a constant on a bounded interval)
  have hout : MeasureTheory.Integrable
      (fun z : ℝ => ∫ θ, ‖Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ‖
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      (MeasureTheory.volume.restrict (Set.Ioc r z₁)) := by
    refine MeasureTheory.Integrable.mono' (MeasureTheory.integrable_const (α := ℝ)
      (∫ θ, (‖Work.Spaces.pz Ψ r θ * Work.Elliptic.sinCos2 θ‖
        + ∫ s in r..z₁, ‖Work.Spaces.pzIter 2 Ψ s θ * Work.Elliptic.sinCos2 θ‖)
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))) ?_ ?_
    · exact hAESM.norm.integral_prod_right'
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with z hz
      have hb : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
          ‖Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ‖
            ≤ ‖Work.Spaces.pz Ψ r θ * Work.Elliptic.sinCos2 θ‖
              + ∫ s in r..z₁, ‖Work.Spaces.pzIter 2 Ψ s θ * Work.Elliptic.sinCos2 θ‖ :=
        hbound.mono (fun θ hθ => hθ z hz)
      have h1 : MeasureTheory.Integrable
          (fun θ : ℝ => ‖Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ‖)
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) := (hsliceAll z hz).norm
      rw [Real.norm_of_nonneg (MeasureTheory.integral_nonneg_of_ae
        (Filter.Eventually.of_forall (fun θ => norm_nonneg _)))]
      exact MeasureTheory.integral_mono_ae h1 hH hb
  -- ## Conclusion: Fubini for the (not necessarily nonnegative) integrand
  refine (MeasureTheory.integrable_prod_iff hAESM).2
    ⟨MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc hsliceAll, hout⟩

end Work.FTS.EllipticEst.remov
end
-- ===== merged: Submission.Work.FTS.H2.ModalSolR.angularEigenIdentity =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Topology

open MeasureTheory

namespace Work.FTS.H2.ModalSolR

/-!
# `Work.FTS.H2.ModalSolR.angularEigenIdentity`

The `m`-th angular Dirichlet eigenfunction of the `α = 0` Biot–Savart operator

`Lzero Ψ = -∂_θθΨ + ∂_θ(tan θ · Ψ) - 6Ψ`

is `eFam m θ = cos θ · C^{(3/2)}_{2m+1}(sin θ)`, with eigenvalue `lam m = 2m(2m+5)`
(`Work.FTS.PhiStar.Gegenbauer.eFam_Lzero`).  The pairing of `Lzero` against the weight `cos θ`
is self-adjoint on functions supported away from the endpoints, so for `φ` compactly supported
inside the open quadrant `Q0 = (0,∞) × (0,π/2)` and every `z`

`∫_{Iθ} eFam m θ · (Lzero φ)(z,θ) · cos θ = lam m · ∫_{Iθ} eFam m θ · φ(z,θ) · cos θ`.

The proof localises the `θ`-integral to an interval `[c,d] ⊂ (0,π/2)` outside which the slice
`θ ↦ φ z θ` vanishes (`Work.EllipticEst.ModalSolution.box_of_compactSupport`), applies the
integration by parts identity `Work.EllipticEst.ModalSolution.angular_ibp_zero` there, and
identifies `Lzero (eFam m)` with `lam m · eFam m` pointwise.
-/

/-! ## Auxiliary facts -/

/-- The `θ`-slice of a jointly smooth function is smooth. -/
private lemma contDiff_slice {φ : ℝ → ℝ → ℝ}
    (hφ : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry φ)) (z : ℝ) (n : ℕ) :
    ContDiff ℝ n (fun θ : ℝ => φ z θ) := by
  have h : ContDiff ℝ n (Function.uncurry φ) := hφ n
  have hs : ContDiff ℝ n (fun θ : ℝ => (z, θ)) :=
    (contDiff_const (c := z)).prodMk contDiff_id
  have hcomp := h.comp hs
  have hfun : (Function.uncurry φ) ∘ (fun θ : ℝ => (z, θ)) = fun θ : ℝ => φ z θ := by
    funext θ
    exact Function.uncurry_apply_pair φ z θ
  rwa [hfun] at hcomp

/-- `eFam m = cos θ · C^{(3/2)}_{2m+1}(sin θ)` is `C²` (indeed smooth). -/
private lemma contDiff_eFam (m : ℕ) :
    ContDiff ℝ 2 (Work.FTS.PhiStar.Gegenbauer.eFam m) := by
  have hg : ContDiff ℝ 2 (Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1)) :=
    (Work.FTS.PhiStar.Gegenbauer.contDiff_gC (2 * m + 1)).of_le (by norm_num)
  exact Real.contDiff_cos.mul (hg.comp Real.contDiff_sin)

/-- An integral over `Iθ` of a function vanishing off `Set.Icc c d ⊆ Iθ` is the integral over
`Set.Icc c d`. -/
private lemma setIntegral_Iθ_eq_Icc {h : ℝ → ℝ} {c d : ℝ} (hc : 0 ≤ c)
    (hd : d ≤ Real.pi / 2) (h0 : ∀ θ : ℝ, θ ∉ Set.Icc c d → h θ = 0) :
    (∫ θ in Work.Spaces.Iθ, h θ) = ∫ θ in Set.Icc c d, h θ :=
  setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Icc
    (fun _ hθ => ⟨hc.trans hθ.1, hθ.2.trans hd⟩) (fun θ hθ => h0 θ hθ.2)

/-- `Lzero`, written with the one-variable derivatives of the slice (restatement of
`Work.Elliptic.Lzero_eq_deriv` with the binder names used below). -/
private lemma Lzero_eq_expanded (φ : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Elliptic.Lzero φ z θ
      = -deriv (deriv (fun θ' : ℝ => φ z θ')) θ
        + deriv (fun θ' : ℝ => Real.tan θ' * φ z θ') θ - 6 * φ z θ := by
  first
  | exact Work.Elliptic.Lzero_eq_deriv φ z θ
  | simpa only [] using Work.Elliptic.Lzero_eq_deriv φ z θ

/-- The eigenfunction relation `Lzero (eFam m) = lam m · eFam m`, written with the binder names
used below. -/
private lemma eFam_Lzero_expanded (m : ℕ) {θ : ℝ} (hθ : Real.cos θ ≠ 0) (z : ℝ) :
    -(deriv (deriv (Work.FTS.PhiStar.Gegenbauer.eFam m)) θ)
      + deriv (fun θ' : ℝ => Real.tan θ' * Work.FTS.PhiStar.Gegenbauer.eFam m θ') θ
      - 6 * Work.FTS.PhiStar.Gegenbauer.eFam m θ
      = Work.FTS.PhiStar.Gegenbauer.lam m * Work.FTS.PhiStar.Gegenbauer.eFam m θ := by
  have h := Work.FTS.PhiStar.Gegenbauer.eFam_Lzero m hθ z
  rw [Work.Elliptic.Lzero_eq_deriv] at h
  first
  | exact h
  | simpa only [] using h

/-- If a slice vanishes identically off `Set.Icc c d` then so does `Lzero` of it: every term of
`Lzero` is a derivative (or the value) of a function which is locally `0` there. -/
private lemma Lzero_eq_zero_of_eq_zero_off_aux {φ : ℝ → ℝ → ℝ} {z c d θ : ℝ}
    (hv : ∀ θ' : ℝ, θ' ∉ Set.Icc c d → φ z θ' = 0) (hθ : θ ∉ Set.Icc c d) :
    Work.Elliptic.Lzero φ z θ = 0 := by
  have hnb : ∀ᶠ θ' in 𝓝 θ, θ' ∉ Set.Icc c d :=
    (isClosed_Icc.isOpen_compl).mem_nhds hθ
  have h2 : deriv (deriv (fun θ' : ℝ => φ z θ')) θ = 0 := by
    have hpt : ∀ θ' : ℝ, θ' ∉ Set.Icc c d → deriv (fun θ'' : ℝ => φ z θ'') θ' = 0 := by
      intro θ' hθ'
      have hev : (fun θ'' : ℝ => φ z θ'') =ᶠ[𝓝 θ'] (fun _ => (0 : ℝ)) := by
        filter_upwards [(isClosed_Icc.isOpen_compl).mem_nhds hθ'] with θ'' hθ''
        exact hv θ'' hθ''
      rw [hev.deriv_eq]
      exact deriv_const θ' 0
    have hev2 : (fun θ' : ℝ => deriv (fun θ'' : ℝ => φ z θ'') θ')
        =ᶠ[𝓝 θ] (fun _ => (0 : ℝ)) := by
      filter_upwards [hnb] with θ' hθ'
      exact hpt θ' hθ'
    rw [show deriv (deriv (fun θ' : ℝ => φ z θ')) θ
        = deriv (fun θ' : ℝ => deriv (fun θ'' : ℝ => φ z θ'') θ') θ from rfl,
      hev2.deriv_eq]
    exact deriv_const θ 0
  have h3 : deriv (fun θ' : ℝ => Real.tan θ' * φ z θ') θ = 0 := by
    have hev3 : (fun θ' : ℝ => Real.tan θ' * φ z θ') =ᶠ[𝓝 θ] (fun _ => (0 : ℝ)) := by
      filter_upwards [hnb] with θ' hθ'
      rw [hv θ' hθ', mul_zero]
    rw [hev3.deriv_eq]
    exact deriv_const θ 0
  rw [Work.Elliptic.Lzero_eq_deriv]
  change -deriv (deriv (fun θ' : ℝ => φ z θ')) θ
      + deriv (fun θ' : ℝ => Real.tan θ' * φ z θ') θ - 6 * φ z θ = 0
  rw [h2, h3, hv θ hθ]
  ring

/-- `θ ↦ Lzero φ z θ` is continuous on any `[c,d]` with `0 < c ≤ d < π/2`: there it is the sum
of the continuous second derivative of the slice, the product `tan θ · (slice)'` (a product
rule expansion), and `-6` times the slice. -/
private lemma Lzero_continuousOn_aux {φ : ℝ → ℝ → ℝ} {z c d : ℝ}
    (h2 : ContDiff ℝ 2 (fun θ : ℝ => φ z θ)) (hc : 0 < c) (hd : d < Real.pi / 2) :
    ContinuousOn (fun θ : ℝ => Work.Elliptic.Lzero φ z θ) (Set.Icc c d) := by
  have h1 : ContDiff ℝ 1 (fun θ : ℝ => φ z θ) := h2.of_le (by norm_num)
  have hdd : Continuous (deriv (deriv (fun θ : ℝ => φ z θ))) :=
    (ContDiff.deriv' (n := 1) h2).continuous_deriv_one
  have hd1 : Continuous (deriv (fun θ : ℝ => φ z θ)) := h1.continuous_deriv_one
  have hcos : ∀ θ ∈ Set.Icc c d, Real.cos θ ≠ 0 := by
    intro θ hθ
    refine ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩)
    · linarith [Real.pi_pos, hc, hθ.1]
    · linarith [hd, hθ.2]
  have hprod : ∀ θ ∈ Set.Icc c d, deriv (fun θ' : ℝ => Real.tan θ' * φ z θ') θ
      = (1 / Real.cos θ ^ 2) * φ z θ + Real.tan θ * deriv (fun θ' : ℝ => φ z θ') θ := by
    intro θ hθ
    have hsd : HasDerivAt (fun θ' : ℝ => φ z θ') (deriv (fun θ' : ℝ => φ z θ') θ) θ :=
      ((h1.differentiable (by norm_num)).differentiableAt).hasDerivAt
    have hm := (Real.hasDerivAt_tan (hcos θ hθ)).mul hsd
    have hfun : (Real.tan * fun θ' : ℝ => φ z θ') = fun θ' : ℝ => Real.tan θ' * φ z θ' := by
      funext θ'
      first
      | rfl
      | simp only [Pi.mul_apply]
    rw [hfun] at hm
    exact hm.deriv
  have hcont : ContinuousOn (fun θ : ℝ =>
      -deriv (deriv (fun θ' : ℝ => φ z θ')) θ
        + ((1 / Real.cos θ ^ 2) * φ z θ + Real.tan θ * deriv (fun θ' : ℝ => φ z θ') θ)
        - 6 * φ z θ) (Set.Icc c d) := by
    have hA : ContinuousOn (fun θ : ℝ => deriv (deriv (fun θ' : ℝ => φ z θ')) θ)
        (Set.Icc c d) := hdd.continuousOn
    have hB : ContinuousOn (fun θ : ℝ => deriv (fun θ' : ℝ => φ z θ') θ) (Set.Icc c d) :=
      hd1.continuousOn
    have hC : ContinuousOn (fun θ : ℝ => φ z θ) (Set.Icc c d) := h2.continuous.continuousOn
    have hcos2 : ContinuousOn (fun θ : ℝ => 1 / Real.cos θ ^ 2) (Set.Icc c d) :=
      continuousOn_const.div (Real.continuous_cos.continuousOn.pow 2)
        (fun θ hθ => pow_ne_zero 2 (hcos θ hθ))
    have htan : ContinuousOn Real.tan (Set.Icc c d) :=
      Real.continuousOn_tan.mono (fun θ hθ => hcos θ hθ)
    exact (((hA.neg).add ((hcos2.mul hC).add (htan.mul hB))).sub
      (continuousOn_const.mul hC))
  refine hcont.congr ?_
  intro θ hθ
  dsimp only
  rw [Lzero_eq_expanded, hprod θ hθ]

/-! ## The main computation -/

/-- The eigen-identity, localised to an interval `[c,d] ⊂ (0,π/2)` outside which the slice of
`φ` vanishes: since `Lzero` is self-adjoint for the weight `cos θ` on functions supported
inside `(0,π/2)` (and `Lzero (eFam m) = lam m · eFam m`), the pairing against `eFam m`
factors out `lam m`. -/
private lemma angularEigenIdentity_of_vanishes {φ : ℝ → ℝ → ℝ}
    (hφ : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry φ))
    (m : ℕ) {z c d : ℝ} (hc : 0 < c) (hcd : c < d) (hd : d < Real.pi / 2)
    (hv : ∀ θ : ℝ, θ ∉ Set.Icc c d → φ z θ = 0) :
    (∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ
        * Work.Elliptic.Lzero φ z θ * Real.cos θ)
      = Work.FTS.PhiStar.Gegenbauer.lam m
        * ∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ * φ z θ
          * Real.cos θ := by
  have hslice2 : ContDiff ℝ 2 (fun θ : ℝ => φ z θ) := contDiff_slice hφ z 2
  have hfam2 : ContDiff ℝ 2 (Work.FTS.PhiStar.Gegenbauer.eFam m) := contDiff_eFam m
  have hzero : ∀ θ ∈ Set.Icc c d, Real.cos θ ≠ 0 := by
    intro θ hθ
    refine ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩)
    · linarith [Real.pi_pos, hc, hθ.1]
    · linarith [hd, hθ.2]
  -- the integration by parts identity on `[c,d]`
  have hIBP := Work.EllipticEst.ModalSolution.angular_ibp_zero
    (f := Work.FTS.PhiStar.Gegenbauer.eFam m) (g := fun θ : ℝ => φ z θ)
    hc hcd hd hfam2.contDiffOn hslice2.contDiffOn (fun θ hθ => hv θ hθ)
  -- the two integrands agree on `[c,d]`
  have hEqOn : Set.EqOn
      (fun θ : ℝ =>
        (Work.FTS.PhiStar.Gegenbauer.eFam m θ *
            (-(deriv (deriv (fun θ' : ℝ => φ z θ')) θ)
              + deriv (fun θ' : ℝ => Real.tan θ' * φ z θ') θ - 6 * φ z θ)
          - (-(deriv (deriv (Work.FTS.PhiStar.Gegenbauer.eFam m)) θ)
              + deriv (fun θ' : ℝ => Real.tan θ' * Work.FTS.PhiStar.Gegenbauer.eFam m θ') θ
              - 6 * Work.FTS.PhiStar.Gegenbauer.eFam m θ) * φ z θ)
          * Real.cos θ)
      (fun θ : ℝ =>
        (Work.FTS.PhiStar.Gegenbauer.eFam m θ * Work.Elliptic.Lzero φ z θ
          - Work.FTS.PhiStar.Gegenbauer.lam m
            * (Work.FTS.PhiStar.Gegenbauer.eFam m θ * φ z θ)) * Real.cos θ)
      (Set.Icc c d) := by
    intro θ hθ
    dsimp only
    rw [Lzero_eq_expanded, eFam_Lzero_expanded m (hzero θ hθ) z]
    ring
  have hKey : (∫ θ in Set.Icc c d,
        (Work.FTS.PhiStar.Gegenbauer.eFam m θ * Work.Elliptic.Lzero φ z θ
          - Work.FTS.PhiStar.Gegenbauer.lam m
            * (Work.FTS.PhiStar.Gegenbauer.eFam m θ * φ z θ)) * Real.cos θ) = 0 :=
    (setIntegral_congr_fun measurableSet_Icc hEqOn).symm.trans hIBP
  have hKey' : (∫ θ in Set.Icc c d,
        (Work.FTS.PhiStar.Gegenbauer.eFam m θ * Work.Elliptic.Lzero φ z θ * Real.cos θ
          - (Work.FTS.PhiStar.Gegenbauer.lam m
            * (Work.FTS.PhiStar.Gegenbauer.eFam m θ * φ z θ)) * Real.cos θ)) = 0 := by
    rw [← hKey]
    refine setIntegral_congr_fun measurableSet_Icc ?_
    intro θ hθ
    dsimp only
    ring
  -- integrability on `[c,d]`
  have hInt1 : IntegrableOn
      (fun θ : ℝ => Work.FTS.PhiStar.Gegenbauer.eFam m θ * Work.Elliptic.Lzero φ z θ
        * Real.cos θ) (Set.Icc c d) :=
    (((hfam2.continuous.continuousOn.mul
      (Lzero_continuousOn_aux hslice2 hc hd)).mul
        Real.continuous_cos.continuousOn)).integrableOn_Icc
  have hInt2 : IntegrableOn
      (fun θ : ℝ => (Work.FTS.PhiStar.Gegenbauer.lam m
        * (Work.FTS.PhiStar.Gegenbauer.eFam m θ * φ z θ)) * Real.cos θ) (Set.Icc c d) :=
    (((continuousOn_const.mul
      (hfam2.continuous.continuousOn.mul hslice2.continuous.continuousOn)).mul
        Real.continuous_cos.continuousOn)).integrableOn_Icc
  have hsplit : (∫ θ in Set.Icc c d,
        (Work.FTS.PhiStar.Gegenbauer.eFam m θ * Work.Elliptic.Lzero φ z θ * Real.cos θ
          - (Work.FTS.PhiStar.Gegenbauer.lam m
            * (Work.FTS.PhiStar.Gegenbauer.eFam m θ * φ z θ)) * Real.cos θ))
      = (∫ θ in Set.Icc c d, Work.FTS.PhiStar.Gegenbauer.eFam m θ
            * Work.Elliptic.Lzero φ z θ * Real.cos θ)
        - ∫ θ in Set.Icc c d, (Work.FTS.PhiStar.Gegenbauer.lam m
            * (Work.FTS.PhiStar.Gegenbauer.eFam m θ * φ z θ)) * Real.cos θ :=
    integral_sub hInt1 hInt2
  have hB : (∫ θ in Set.Icc c d, (Work.FTS.PhiStar.Gegenbauer.lam m
        * (Work.FTS.PhiStar.Gegenbauer.eFam m θ * φ z θ)) * Real.cos θ)
      = Work.FTS.PhiStar.Gegenbauer.lam m
        * (∫ θ in Set.Icc c d, Work.FTS.PhiStar.Gegenbauer.eFam m θ * φ z θ
            * Real.cos θ) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Icc ?_
    intro θ hθ
    dsimp only
    ring
  have hA : (∫ θ in Set.Icc c d, Work.FTS.PhiStar.Gegenbauer.eFam m θ
        * Work.Elliptic.Lzero φ z θ * Real.cos θ)
      = ∫ θ in Set.Icc c d, (Work.FTS.PhiStar.Gegenbauer.lam m
        * (Work.FTS.PhiStar.Gegenbauer.eFam m θ * φ z θ)) * Real.cos θ := by
    have h1 : (∫ θ in Set.Icc c d, Work.FTS.PhiStar.Gegenbauer.eFam m θ
          * Work.Elliptic.Lzero φ z θ * Real.cos θ)
        - ∫ θ in Set.Icc c d, (Work.FTS.PhiStar.Gegenbauer.lam m
          * (Work.FTS.PhiStar.Gegenbauer.eFam m θ * φ z θ)) * Real.cos θ = 0 := by
      rw [← hsplit]
      first
      | exact hKey'
      | simpa only [] using hKey'
    exact sub_eq_zero.mp h1
  -- transfer both integrals from `Iθ` to `[c,d]`
  have htrans1 : (∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ
        * Work.Elliptic.Lzero φ z θ * Real.cos θ)
      = ∫ θ in Set.Icc c d, Work.FTS.PhiStar.Gegenbauer.eFam m θ
        * Work.Elliptic.Lzero φ z θ * Real.cos θ :=
    setIntegral_Iθ_eq_Icc hc.le hd.le (fun θ hθ => by
      rw [Lzero_eq_zero_of_eq_zero_off_aux hv hθ]
      ring)
  have htrans2 : (∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ * φ z θ
        * Real.cos θ)
      = ∫ θ in Set.Icc c d, Work.FTS.PhiStar.Gegenbauer.eFam m θ * φ z θ
        * Real.cos θ :=
    setIntegral_Iθ_eq_Icc hc.le hd.le (fun θ hθ => by
      rw [hv θ hθ]
      ring)
  rw [htrans1, htrans2, hA, hB]

/-! ## The eigen-identity -/

theorem angularEigenIdentity {φ : ℝ → ℝ → ℝ}
    (hφ : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry φ))
    (hφc : HasCompactSupport (Function.uncurry φ))
    (hφs : tsupport (Function.uncurry φ) ⊆ Work.FTS.EllipticEst.Q0) (m : ℕ) {z : ℝ} (hz : 0 < z) :
    (∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ
        * Work.Elliptic.Lzero φ z θ * Real.cos θ)
      = Work.FTS.PhiStar.Gegenbauer.lam m
        * ∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ * φ z θ * Real.cos θ := by
  obtain ⟨a, b, c, d, ha, hab, hc, hcd, hd, hbox⟩ :=
    Work.EllipticEst.ModalSolution.box_of_compactSupport hφc hφs
  refine angularEigenIdentity_of_vanishes hφ m hc hcd hd ?_
  intro θ hθ
  by_contra hne
  have hmem : (z, θ) ∈ Set.Ioo a b ×ˢ Set.Ioo c d := by
    by_contra hcon
    exact hne (hbox (z, θ) hcon)
  exact hθ ⟨le_of_lt hmem.2.1, le_of_lt hmem.2.2⟩

end Work.FTS.H2.ModalSolR
end
-- ===== merged: Submission.Work.FTS.H2.ModalSolR.thetaMomentCompactSupport =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.ModalSolR

/-- `box_of_compactSupport` in the form used below: a `φ` with compact support contained in the
open quadrant `Q0` vanishes identically in `z` outside some compact interval `[a,b]` with
`0 < a`. -/
private theorem exists_vanishing_interval {φ : ℝ → ℝ → ℝ}
    (hφc : HasCompactSupport (Function.uncurry φ))
    (hφs : tsupport (Function.uncurry φ) ⊆ Work.FTS.EllipticEst.Q0) :
    ∃ a b : ℝ, 0 < a ∧ a < b ∧ ∀ z : ℝ, z ∉ Set.Icc a b → ∀ θ : ℝ, φ z θ = 0 := by
  obtain ⟨a, b, c, d, ha, hab, hc, hcd, hd, hbox⟩ :=
    Work.EllipticEst.ModalSolution.box_of_compactSupport hφc hφs
  refine ⟨a, b, ha, hab, fun z hz θ => ?_⟩
  have hz' : z ∉ Set.Ioo a b := fun h => hz ⟨le_of_lt h.1, le_of_lt h.2⟩
  by_cases hθ : θ ∈ Set.Ioo c d
  · exact hbox (z, θ) (fun hp => hz' hp.1)
  · exact hbox (z, θ) (fun hp => hθ hp.2)

theorem thetaMomentCompactSupport {φ : ℝ → ℝ → ℝ}
    (hφ : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry φ))
    (hφc : HasCompactSupport (Function.uncurry φ))
    (hφs : tsupport (Function.uncurry φ) ⊆ Work.FTS.EllipticEst.Q0) (m : ℕ) :
    HasCompactSupport (fun z => ∫ θ in Work.Spaces.Iθ,
        φ z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) ∧
      tsupport (fun z => ∫ θ in Work.Spaces.Iθ,
        φ z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) ⊆ Set.Ioi 0 := by
  obtain ⟨a, b, ha, hab, hvanish⟩ := exists_vanishing_interval hφc hφs
  -- the angular moment vanishes for every `z` outside the compact interval `[a,b]`
  have key : ∀ z : ℝ, z ∉ Set.Icc a b →
      (∫ θ in Work.Spaces.Iθ, φ z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ)
        = 0 := by
    intro z hz
    have hfun : (fun θ : ℝ => φ z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ)
        = fun _ => (0 : ℝ) := by
      funext θ
      rw [hvanish z hz θ]
      ring
    rw [hfun]
    simp
  refine ⟨?_, ?_⟩
  · exact HasCompactSupport.intro' isCompact_Icc isClosed_Icc fun z hz => key z hz
  · have hsupp : Function.support
        (fun z => ∫ θ in Work.Spaces.Iθ,
          φ z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) ⊆ Set.Icc a b := by
      intro z hz
      by_contra h
      exact (Function.mem_support.mp hz) (key z h)
    intro z hz
    have h1 : z ∈ Set.Icc a b := closure_minimal hsupp isClosed_Icc hz
    exact lt_of_lt_of_le ha h1.1

end Work.FTS.H2.ModalSolR
end
-- ===== merged: Submission.Work.FTS.OpenPkg.DzIter_le_WlInf_open =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-
# `|D_z^b f| ≤ 100 |f|_{𝒲^{4,∞}}` in the open-quadrant class

For a function `f` which is `C^∞` on the *open* quadrant `(0,∞) × (0,π/2)` (the class
`Work.FTS.EllipticEst.SmoothOpen`) and of class `𝒲^{4,∞}`, the iterated radial operator
`D_z = z ∂_z` is bounded by `100 |f|_{𝒲}` at every *interior* point `(z,θ)`, `z > 0`,
`0 < θ < π/2`, for `b ≤ 4`.

The proof is the open-quadrant instance of `Work.FTS.H2.WPQ.DzIter_le_WlInf`: expand
`D_z^b` with the Stirling numbers of the second kind via the half-line version
`Work.FTS.OpenPkg.DzIter_eq_sum_scoef_open` (`|z^j ∂_z^j f| ≤ |f|_𝒲` supplies the
coefficients), sum the (nonnegative) coefficients with `abs_sum_scoef_mul_le`, and use
the Bell number bound `bell b ≤ 100`.  The open-quadrant expansion is what makes the
argument available with only interior smoothness: the `z`-slices of a `SmoothOpen`
function are `C^∞` on `(0,∞)` only, which is exactly the input of the Stirling
expansion there.
-/

open scoped Real

namespace Work.FTS.OpenPkg

theorem DzIter_le_WlInf_open {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hfm : Work.Spaces.WlInfMem α 4 f)
    {b : ℕ} (hb : b ≤ 4) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    |Work.Spaces.DzIter b f z θ| ≤ 100 * Work.Spaces.WlInf α 4 f := by
  have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hz' : z ∈ Set.Ioi (0 : ℝ) := hz
  -- the Stirling expansion of `D_z^b` on the open half-line
  have hslice : ContDiffOn ℝ Work.Stability.smoothOrder (fun z' => f z' θ) (Set.Ioi 0) :=
    smoothOpen_slice_z hf hθ
  have hDz : Work.Spaces.DzIter b f z θ
      = ∑ k ∈ Finset.range (b + 1),
          (Work.Spaces.scoef b k : ℝ) * (z ^ k * Work.Spaces.pzIter k f z θ) :=
    DzIter_eq_sum_scoef_open hslice b z hz'
  -- the coefficients: `|z^k ∂_z^k f| ≤ |f|_𝒲` for `k ≤ b ≤ 4`
  have hsum := Work.Spaces.abs_sum_scoef_mul_le b (Work.Spaces.WlInf α 4 f)
    (fun k => z ^ k * Work.Spaces.pzIter k f z θ)
    (fun k hk => Work.Spaces.zpz_le_WlInf hfm (le_trans hk hb) hzI hθI)
  have hbell : (Work.Spaces.bell b : ℝ) ≤ 100 := by
    exact_mod_cast Work.Spaces.bell_le b hb
  have hW : 0 ≤ Work.Spaces.WlInf α 4 f := by
    rw [Work.Spaces.WlInf]
    exact add_nonneg (Work.Spaces.wlZSum_nonneg α 4 f hfm)
      (Work.Spaces.wlThSum_nonneg α 4 f hfm)
  calc |Work.Spaces.DzIter b f z θ|
      = |∑ k ∈ Finset.range (b + 1),
          (Work.Spaces.scoef b k : ℝ) * (z ^ k * Work.Spaces.pzIter k f z θ)| := by rw [hDz]
    _ ≤ (Work.Spaces.bell b : ℝ) * Work.Spaces.WlInf α 4 f := hsum
    _ ≤ 100 * Work.Spaces.WlInf α 4 f := mul_le_mul_of_nonneg_right hbell hW

end Work.FTS.OpenPkg
end
-- ===== merged: Submission.Work.FTS.OpenPkg.Mixed_le_WlInf_open =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Mixed_le_WlInf_open`

Pointwise control of every mixed derivative `D_z^b D_θ^a f` (`1 ≤ a`, `a + b ≤ 4`) inside the
*open* quadrant by the `𝒲^{4,∞}`-norm, for `f` of class `SmoothOpen` (i.e. merely `C^∞` on the
open quadrant `(0,∞) × (0,π/2)`).

The angular summands of the `𝒲^{4,∞}`-norm control `(z+1)^k ∂_z^k D_θ^j f · sin(2θ)^{-α/5} /
(α + sin 2θ)`; `Work.Spaces.pz_Dth_sup_bound` turns this into the unweighted pointwise bound

`|z^k ∂_z^k D_θ^j f| ≤ |f|_𝒲 · (z+1)^{-k} (α + sin 2θ) sin(2θ)^{α/5}`   (`1 ≤ j`, `k + j ≤ 4`).

Combining this with the Stirling expansion of `D_z^b` in the genuine smooth order on the open
half-line (`Work.FTS.OpenPkg.DzIter_eq_sum_scoef_open`, which is exactly the open-quadrant form
of the expansion) and `Work.Spaces.abs_sum_scoef_mul_le` (the total coefficient mass is the Bell
number `bell b ≤ 100` for `b ≤ 4`) gives the stated bound with constant `100`.
-/

open scoped Real

namespace Work.FTS.OpenPkg

theorem Mixed_le_WlInf_open {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hfm : Work.Spaces.WlInfMem α 4 f)
    {a b : ℕ} (ha : 1 ≤ a) (hab : a + b ≤ 4) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    |Work.Spaces.mixed b a f z θ| ≤ 100 * (Work.Spaces.WlInf α 4 f
      * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) := by
  have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hb4 : b ≤ 4 := by omega
  -- the angular factor is nonnegative, and so is the whole bound
  have hsin0 : 0 ≤ Real.sin (2 * θ) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi <;> linarith [hθ.1, hθ.2, Real.pi_pos]
  have hY : 0 ≤ (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) :=
    mul_nonneg (by linarith) (Real.rpow_nonneg hsin0 _)
  have hW : 0 ≤ Work.Spaces.WlInf α 4 f := by
    rw [Work.Spaces.WlInf]
    exact add_nonneg (Work.Spaces.wlZSum_nonneg α 4 f hfm)
      (Work.Spaces.wlThSum_nonneg α 4 f hfm)
  have hM : 0 ≤ Work.Spaces.WlInf α 4 f
      * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := mul_nonneg hW hY
  -- the pointwise bound for the individual `z^k ∂_z^k (D_θ^a f)`-terms
  have hbound : ∀ k ≤ b, |z ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter a f) z θ|
      ≤ Work.Spaces.WlInf α 4 f
        * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) :=
    fun k hk => Work.Spaces.zpz_Dth_le_WlInf hα hfm ha (by omega) hzI hθI
  -- the Stirling expansion of `D_z^b` in the genuine smooth order on `(0,∞)`
  have hsmooth : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun z' => Work.Spaces.DthIter a f z' θ) (Set.Ioi 0) :=
    smoothOpen_DthIter_slice_z hf a hθ
  rw [Work.Spaces.mixed,
    DzIter_eq_sum_scoef_open (h := Work.Spaces.DthIter a f) hsmooth b z hz]
  have hsum := Work.Spaces.abs_sum_scoef_mul_le b
    (Work.Spaces.WlInf α 4 f
      * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
    (fun k => z ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter a f) z θ) hbound
  refine le_trans hsum ?_
  calc (Work.Spaces.bell b : ℝ)
        * (Work.Spaces.WlInf α 4 f
          * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
      ≤ 100 * (Work.Spaces.WlInf α 4 f
          * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast Work.Spaces.bell_le b hb4) hM

end Work.FTS.OpenPkg
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.integrableOn_term =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty.SlotsLimit

open MeasureTheory Set Filter
open scoped Real Topology

local notation "Q0" => Work.FTS.EllipticEst.Q0

/-! ## Two bookkeeping lemmas about the `ℋ^k`-integrand

Both are the "one-sided Tonelli" facts behind the integrability of the single terms of
`HkIntegrand`: `HkMem α k h` supplies the angular integrability at each `z ∈ Iz` and the
integrability of the outer integral, `SmoothOpen h` supplies the joint a.e. strong
measurability (continuity on the open quadrant, the boundary being null), and Tonelli
(`Work.Spaces.integrable_prod_of_iterated`) upgrades these to the product-integrability of
the integrand.  The second lemma restricts the product measure — which is carried by
`Iz ×ˢ Iθ`, hence by `Q0` — to the open quadrant. -/

/-- The `ℋ^k`-integrand of a function which is `C^∞` on the open quadrant and in `ℋ^k` is
integrable for the product of the restricted Lebesgue measures on `Iz` and `Iθ`. -/
private theorem integrable_HkIntegrand_prod {α : ℝ} {k : ℕ} {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α k f) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k f p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  refine (Work.Spaces.integrable_prod_of_iterated
    (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
    (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    (G := fun z θ => Work.Spaces.HkIntegrand α k f z θ)
    (fun z θ => Work.Spaces.HkIntegrand_nonneg α k f z θ)
    (Work.Spaces.aesm_of_continuousOn_Qd _ (hsm.continuousOn_HkIntegrand α k)) ?_ hmem.2).1
  rw [MeasureTheory.ae_restrict_iff' (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici)]
  exact Eventually.of_forall fun z hz => hmem.1 z hz

/-- The `ℋ^k`-integrand is integrable over the open quadrant `Q0 = (0,∞) × (0,π/2)`: the
product measure of `Iz ×ˢ Iθ` dominates the restriction of the planar Lebesgue measure to
`Q0`, since `Q0 ⊆ Iz ×ˢ Iθ`. -/
theorem integrableOn_HkIntegrand_Q0 {α : ℝ} {k : ℕ} {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α k f) :
    MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k f p.1 p.2)
      Q0 := by
  refine (integrable_HkIntegrand_prod hsm hmem).mono_measure ?_
  rw [MeasureTheory.Measure.prod_restrict]
  exact MeasureTheory.Measure.restrict_mono
    (Set.prod_mono Set.Ioi_subset_Ici_self Set.Ioo_subset_Icc_self) le_rfl

/-- **The angular weight of the mixed slots is continuous on the open quadrant.**  (The
`i = 0` counterpart is `Work.FTS.EllipticEst.continuousOn_wdivsin_Q0`.) -/
private theorem continuousOn_Wt_Q0lit (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2) Q0 := by
  have hsinpos : ∀ p ∈ Q0, 0 < Real.sin (2 * p.2) := by
    intro p hp
    obtain ⟨-, h0, h1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hw : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) Q0 := by
    have hfun : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by
      funext p; rfl
    rw [hfun]
    refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2) (fun p hp => ?_)
    exact pow_ne_zero 2 (ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hp).1)
  have hth : ContinuousOn (fun p : ℝ × ℝ =>
      (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2))) Q0 :=
    ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
      (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      = fun p : ℝ × ℝ => Work.Spaces.w p.1
          * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)) := by
    funext p; rfl
  rw [hfun]
  exact hw.mul hth

/-- **Each term of the level-`k` integrand is integrable over the open quadrant.**  For `h` smooth
on `Q0` and `h ∈ ℋ^k`, the `(j,i)`-term of `HkIntegrand α k h` — that is
`(mixed j i h · termWeight α i)²` — is integrable over `Q0`, under the same guard as the
corresponding summand of the integrand (pure: `i = 0`, `j ≤ k`; mixed: `1 ≤ i`, `i + j ≤ k`).
The proof combines the honest iterated integrability supplied by `HkMem α k h` with
Tonelli (both domains differ by the null boundary on which the integrand vanishes) and the joint
a.e. strong measurability coming from the smoothness of `mixed j i h` and of the weight. -/
theorem integrableOn_term (α : ℝ) (k : ℕ) {h : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen h) (hmem : Work.Spaces.HkMem α k h)
    (j i : ℕ) (hij : (i = 0 ∧ j ≤ k) ∨ (1 ≤ i ∧ i + j ≤ k)) :
    IntegrableOn (fun p : ℝ × ℝ =>
        (Work.Spaces.mixed j i h p.1 p.2 * termWeight α i p.1 p.2) ^ 2)
      Work.FTS.EllipticEst.Q0 := by
  -- ### The pointwise domination by the full integrand
  have hFsq : ∀ z θ : ℝ, (Work.Spaces.mixed j i h z θ
      * termWeight α i z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α k h z θ := by
    intro z θ
    rcases hij with ⟨rfl, hjk⟩ | ⟨hi1, hijk⟩
    · -- pure slot `(j,0)`
      have htw : termWeight α 0 z θ
          = Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) := by
        simp [termWeight]
      rw [Work.Spaces.mixed_zero_right, htw]
      exact Work.Spaces.sq_le_HkIntegrand_z α k h z θ j hjk
    · -- mixed slot `(j,i)`, `1 ≤ i`
      have hne : i ≠ 0 := by omega
      have htw : termWeight α i z θ = Work.Spaces.Wt α z θ := by
        simp [termWeight, hne]
      rw [htw]
      exact Work.Spaces.sq_le_HkIntegrand_mixed α k h z θ i j hi1 hijk
  -- ### A.e. strong measurability: the term is continuous on the open quadrant
  have htwc : ContinuousOn (fun p : ℝ × ℝ => termWeight α i p.1 p.2) Q0 := by
    rcases hij with ⟨rfl, -⟩ | ⟨hi1, -⟩
    · rw [show (fun p : ℝ × ℝ => termWeight α 0 p.1 p.2)
          = fun p : ℝ × ℝ => Work.Spaces.w p.1
              / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2) from by
        funext p; simp [termWeight]]
      exact Work.FTS.EllipticEst.continuousOn_wdivsin_Q0
    · have hne : i ≠ 0 := by omega
      rw [show (fun p : ℝ × ℝ => termWeight α i p.1 p.2)
          = fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2 from by
        funext p; simp [termWeight, hne]]
      exact continuousOn_Wt_Q0lit α
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => (Work.Spaces.mixed j i h p.1 p.2
        * termWeight α i p.1 p.2) ^ 2)
      (MeasureTheory.volume.restrict Q0) :=
    ((((hsm.mixed j i).continuousOn).mul htwc).pow 2).aestronglyMeasurable
      Work.FTS.EllipticEst.isOpen_Q0.measurableSet
  -- ### Integrability by domination
  refine (integrableOn_HkIntegrand_Q0 hsm hmem).mono' haesm ?_
  exact Eventually.of_forall fun p => by
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hFsq p.1 p.2

end Work.FTS.PhiStar.Honesty.SlotsLimit
end
