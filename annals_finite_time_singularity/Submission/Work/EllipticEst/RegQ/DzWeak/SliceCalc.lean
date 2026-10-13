/-
Copyright: work module for the Elgindi finite-time singularity project.

# Slice calculus for the level-1 angular integrability of `D_z U`

This module collects the *generic* conversions between the two-variable operators
`D_θ`, `D_z`, `∂_z`, `∂_θ` and the one-dimensional iterates `Dth1Iter` acting on a `θ`-slice,
together with the pointwise weight algebra that identifies the `j = 0` slice group
`Work.FTS.EllipticEst.sliceGroup α k 0 f z ·` with `w(z)²` times the angular integrand of
`Work.FTS.EllipticEst.Ptheta α k` applied to the slice `θ ↦ f z θ`.

Everything here is `sorry`-free and generic: the results are used by
`Submission/Work/EllipticEst/RegQ/DzWeak/level1_integrable.lean` and by the sibling lemmas
about the extraction of the individual `HkIntegrand` summands.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.SliceDecompDefs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.DzAmgm.DthIterDzCommOpen
import Submission.Work.FTS.LocData.Defs

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

/-- The pointwise angular integrand whose integral over `Iθ` is
`Work.FTS.EllipticEst.Ptheta α m u = ∫ u² sin(2θ)^{-η} + ∑_{i=1}^m ∫ (D_θ^i u)² sin(2θ)^{-γ}`. -/
def PthetaIntegrand (α : ℝ) (m : ℕ) (u : ℝ → ℝ) (θ : ℝ) : ℝ :=
  (u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
    + ∑ i ∈ Finset.Icc 1 m,
        (Work.Elliptic.Dth1Iter i u θ) ^ 2 * Work.FTS.EllipticEst.sGam α θ

/-! ## The slice form of the two-variable angular iterate -/

/-- The two-variable iterate `D_θ^i`, evaluated at `(z,θ)`, is the one-dimensional iterate
`Dth1Iter i` of the `θ`-slice at `z`. -/
theorem DthIter_eq_Dth1Iter_slice (i : ℕ) (G : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.DthIter i G z θ = Work.Elliptic.Dth1Iter i (fun θ' => G z θ') θ := by
  induction i generalizing z θ with
  | zero => rfl
  | succ n ih =>
      simp only [Work.Spaces.DthIter_succ, Work.Elliptic.Dth1Iter_succ, Work.Spaces.Dth,
        Work.Spaces.pth, Work.Elliptic.Dth1]
      have hfun : (fun t => Work.Spaces.DthIter n G z t)
          = (fun t => Work.Elliptic.Dth1Iter n (fun s => G z s) t) := by
        funext t; exact ih z t
      rw [hfun]

/-- The one-dimensional iterate does not see a constant factor. -/
theorem Dth1Iter_const_mul (c : ℝ) (i : ℕ) (u : ℝ → ℝ) :
    Work.Elliptic.Dth1Iter i (fun θ => c * u θ)
      = fun θ => c * Work.Elliptic.Dth1Iter i u θ := by
  induction i with
  | zero => rfl
  | succ n ih =>
      funext θ
      rw [Work.Elliptic.Dth1Iter_succ, Work.Elliptic.Dth1Iter_succ]
      rw [ih]
      rw [show Work.Elliptic.Dth1 (fun θ => c * Work.Elliptic.Dth1Iter n u θ) θ
          = Real.sin (2 * θ) * deriv (fun θ => c * Work.Elliptic.Dth1Iter n u θ) θ
          from rfl]
      rw [show Work.Elliptic.Dth1 (Work.Elliptic.Dth1Iter n u) θ
          = Real.sin (2 * θ) * deriv (Work.Elliptic.Dth1Iter n u) θ from rfl]
      rw [deriv_const_mul_field]
      ring

/-- `D_θ^i` commutes with multiplication by the radial variable. -/
theorem DthIter_mul_fst_var (i : ℕ) (A : ℝ → ℝ → ℝ) :
    Work.Spaces.DthIter i (fun z θ => z * A z θ)
      = fun z θ => z * Work.Spaces.DthIter i A z θ := by
  induction i with
  | zero => rfl
  | succ n ih =>
      funext z θ
      rw [Work.Spaces.DthIter_succ, Work.Spaces.DthIter_succ]
      rw [show Work.Spaces.DthIter n (fun z θ => z * A z θ)
          = fun z θ => z * Work.Spaces.DthIter n A z θ from ih]
      rw [show Work.Spaces.Dth (fun z θ => z * Work.Spaces.DthIter n A z θ) z θ
          = Real.sin (2 * θ) * deriv (fun θ' => z * Work.Spaces.DthIter n A z θ') θ
          from rfl]
      rw [show Work.Spaces.Dth (Work.Spaces.DthIter n A) z θ
          = Real.sin (2 * θ) * deriv (Work.Spaces.DthIter n A z) θ from rfl]
      rw [deriv_const_mul_field]
      ring

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

/-- `∂_z` commutes with every iterate of `D_θ` on the open quadrant. -/
theorem pz_DthIter_eqOn {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (k : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.pz (Work.Spaces.DthIter k f)))
      (Function.uncurry (Work.Spaces.DthIter k (Work.Spaces.pz f)))
      Work.FTS.EllipticEst.Q0 := by
  intro y hy
  have hz : 0 < y.1 := (Work.FTS.EllipticEst.mem_Q0.mp hy).1
  have hcomm := Work.FTS.EllipticEst.DzAmgm.DthIterDzCommOpen f hf k hy
  simp only [Function.uncurry] at hcomm
  have hleft : Work.Spaces.Dz (Work.Spaces.DthIter k f) y.1 y.2
      = y.1 * Work.Spaces.pz (Work.Spaces.DthIter k f) y.1 y.2 := rfl
  have hright : Work.Spaces.DthIter k (Work.Spaces.Dz f) y.1 y.2
      = y.1 * Work.Spaces.DthIter k (Work.Spaces.pz f) y.1 y.2 := by
    rw [show Work.Spaces.Dz f = fun z θ => z * Work.Spaces.pz f z θ from rfl,
      DthIter_mul_fst_var]
  rw [hleft, hright] at hcomm
  exact mul_left_cancel₀ (ne_of_gt hz) hcomm

/-! ## The pointwise weight algebra of the `j = 0` slice group -/

/-- The `j = 0` slice group of `f` is `w(z)²` times the angular integrand `PthetaIntegrand`
of the slice `θ ↦ f z θ`. -/
theorem sliceGroup_zero_eq_w_sq_PthetaIntegrand (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ)
    {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.FTS.EllipticEst.sliceGroup α k 0 f z θ
      = (Work.Spaces.w z) ^ 2 * PthetaIntegrand α k (fun θ' => f z θ') θ := by
  have h1 : Work.FTS.EllipticEst.sliceGroup α k 0 f z θ
      = (f z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        + ∑ i ∈ Finset.Icc 1 k,
            (Work.Elliptic.Dth1Iter i (fun θ' => f z θ') θ * Work.Spaces.Wt α z θ) ^ 2 := by
    rw [Work.FTS.EllipticEst.sliceGroup]
    simp only [Nat.sub_zero, Work.Spaces.DzIter_zero]
    rw [show (∑ i ∈ Finset.Icc 1 k,
          (Work.Spaces.mixed 0 i f z θ * Work.Spaces.Wt α z θ) ^ 2)
        = ∑ i ∈ Finset.Icc 1 k,
            (Work.Elliptic.Dth1Iter i (fun θ' => f z θ') θ * Work.Spaces.Wt α z θ) ^ 2 from
      Finset.sum_congr rfl fun i _ => by
        rw [show Work.Spaces.mixed 0 i f = Work.Spaces.DthIter i f from rfl,
          DthIter_eq_Dth1Iter_slice]]
  rw [h1, PthetaIntegrand, Work.FTS.EllipticEst.rad_term_eq hθ z (f z θ)]
  rw [Finset.sum_congr rfl (fun i _ =>
    Work.FTS.EllipticEst.mix_term_eq hθ α z
      (Work.Elliptic.Dth1Iter i (fun θ' => f z θ') θ))]
  rw [← Finset.mul_sum, ← mul_add]

/-- Pulling a constant factor out of the `Ptheta` integrand. -/
theorem PthetaIntegrand_const_mul (α : ℝ) (m : ℕ) (c : ℝ) (u : ℝ → ℝ) (θ : ℝ) :
    PthetaIntegrand α m (fun θ' => c * u θ') θ = c ^ 2 * PthetaIntegrand α m u θ := by
  rw [PthetaIntegrand, PthetaIntegrand, mul_add, Finset.mul_sum]
  congr 1
  · rw [mul_pow]; ring
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [congrFun (Dth1Iter_const_mul c i u) θ]
    ring

/-- The angular integrand of the slice of `D_z U` is `z²` times that of the slice of `∂_z U`. -/
theorem PthetaIntegrand_Dz (α : ℝ) (m : ℕ) (U : ℝ → ℝ → ℝ) (z θ : ℝ) :
    PthetaIntegrand α m (fun θ' => Work.Spaces.Dz U z θ') θ
      = z ^ 2 * PthetaIntegrand α m (fun θ' => Work.Spaces.pz U z θ') θ :=
  PthetaIntegrand_const_mul α m z (fun θ' => Work.Spaces.pz U z θ') θ

/-! ## A.e. congruence on the angular interval -/

/-- Two functions agreeing on the *open* interval have the same `D_θ`-iterates there. -/
theorem Dth1Iter_congr_Ioo {g h : ℝ → ℝ}
    (hgh : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), g θ = h θ) :
    ∀ (i : ℕ) {θ : ℝ}, θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      Work.Elliptic.Dth1Iter i g θ = Work.Elliptic.Dth1Iter i h θ := by
  intro i
  induction i with
  | zero => intro θ hθ; exact hgh θ hθ
  | succ n ih =>
      intro θ hθ
      have hmem : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ 𝓝 θ := isOpen_Ioo.mem_nhds hθ
      have hev : (fun θ' => Work.Elliptic.Dth1Iter n g θ')
          =ᶠ[𝓝 θ] (fun θ' => Work.Elliptic.Dth1Iter n h θ') := by
        filter_upwards [hmem] with θ' hθ'
        exact ih hθ'
      rw [Work.Elliptic.Dth1Iter_succ, Work.Elliptic.Dth1Iter_succ]
      simp only [Work.Elliptic.Dth1]
      rw [hev.deriv_eq]

/-- `IntegrableOn Iθ` transfers along an equality that only holds on the open interval
(the two endpoints of `Iθ` are null). -/
theorem IntegrableOn_congr_Ioo {f g : ℝ → ℝ}
    (h : MeasureTheory.IntegrableOn f Work.Spaces.Iθ)
    (hfg : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), f θ = g θ) :
    MeasureTheory.IntegrableOn g Work.Spaces.Iθ := by
  have hae : f =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ] g := by
    rw [Work.FTS.EllipticEst.restrict_Iθ_eq_restrict_Ioo]
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    exact hfg θ hθ
  exact h.congr hae

/-- The a.e. form (on `Iθ`) of the Clairaut identity `∂_θ² ∂_z f = ∂_z ∂_θ² f`. -/
theorem pthIter_two_pz_ae_eq {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    {z : ℝ} (hz : 0 < z) :
    (fun θ => Work.Spaces.pthIter 2 (Work.Spaces.pz f) z θ)
      =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      (fun θ => Work.Spaces.pz (Work.Spaces.pthIter 2 f) z θ) := by
  rw [Work.FTS.EllipticEst.restrict_Iθ_eq_restrict_Ioo]
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
  exact pthIter_two_pz_eqOn hf ((Work.FTS.EllipticEst.mem_Q0 (z := z) (θ := θ)).mpr
    ⟨hz, hθ.1, hθ.2⟩)

/-- The a.e. form (on `Iθ`) of the commutation `∂_z D_θ^k = D_θ^k ∂_z`. -/
theorem pz_DthIter_ae_eq {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) (k : ℕ)
    {z : ℝ} (hz : 0 < z) :
    (fun θ => Work.Spaces.pz (Work.Spaces.DthIter k f) z θ)
      =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      (fun θ => Work.Spaces.DthIter k (Work.Spaces.pz f) z θ) := by
  rw [Work.FTS.EllipticEst.restrict_Iθ_eq_restrict_Ioo]
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
  exact pz_DthIter_eqOn hf k ((Work.FTS.EllipticEst.mem_Q0 (z := z) (θ := θ)).mpr
    ⟨hz, hθ.1, hθ.2⟩)

/-- The pointwise `D_θ`-iterate of a slice, as an operator on the slice. -/
theorem DthIter_slice_apply (k : ℕ) (G : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.DthIter k G z θ
      = Work.Elliptic.Dth1Iter k (fun θ' => G z θ') θ :=
  DthIter_eq_Dth1Iter_slice k G z θ

end Work.EllipticEst.RegQ.DzWeak
