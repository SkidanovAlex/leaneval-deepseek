import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllSol.ClassC
import Submission.Work.FTS.EllSol.PkgK5.tracesK5
import Submission.Work.FTS.EllipticEst.EllHyp_certificates
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.RPFresh.straight_transfers
import Submission.Work.FTS.H2.HQ.Glue
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.LocData.zero_slice_locG
import Submission.Work.FTS.LocDataExt.Zfar5
import Submission.Work.FTS.Nonlinear.N4Fields.angmul_field_smooth
import Submission.Work.FTS.StrongEps.EpsLimitDefs
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.KsAux
import Submission.Work.FTS.StrongPersist.L3Rhs.L3RhsNstarBlock
import Submission.Work.FTS.StrongPersist.SP6.F0SixYblk
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_RegExport.RXB.l12dens_weighted_bound
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.H2W.asliceMomentEq
import Submission.Work.SolutionDelivery.DatumOdd
-- ===== merged: Submission.Work.FTS.EllSol.PkgK5.vopTransferK5c =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.PkgK5

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Smoothness of the residual and the slice data -/

/-- **`EllResid α g Φg` is `C^∞` on the open quadrant** for a source `g` of the class `C` and a
straightened unknown `Ψ̂ = ellShift α g Φg` smooth there: `Ξ = Ψ̂ − Ḡ(α,g)·sin 2θ`, and both
summands are smooth (`ClassC` supplies the all-order smoothness of `F_*(g)` and `HkMem α 7 g`,
i.e. precisely the hypotheses of `smoothOpen_negGbarSin_classC`). -/
theorem vopcK5c_resid_smooth {α : ℝ} {g Φg : ℝ → ℝ → ℝ} (hα : 0 < α)
    (hC : Work.FTS.EllSol.ClassC α g)
    (hX : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.EllSol.ellShift α g Φg)) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.EllResid α g Φg) := by
  have hG := smoothOpen_negGbarSin_classC (α := α) (g := g) hα hC.reg hC.fsm hC.mem
  refine Work.FTS.EllipticEst.SmoothOpen.congr
    (Work.FTS.EllipticEst.smoothOpen_add hX hG) ?_
  intro z θ _ _ _
  rw [Work.FTS.EllSol.EllResid_eq_ellShift_sub_Gbar_point]
  simp only [Work.FTS.EllSol.ellShift_apply]
  ring

/-- **The angular slices of the radial iterates are `C^∞`** on `(0,π/2)`.  This is the
smoothness hypothesis consumed by `divSinK5` (whose interface asks for `C^∞` in the honest
order `Work.Stability.smoothOrder`). -/
theorem vopcK5c_slice_smooth {Ξ : ℝ → ℝ → ℝ} (hΞ : Work.FTS.EllipticEst.SmoothOpen Ξ)
    (j : ℕ) {z : ℝ} (hz : 0 < z) :
    ContDiffOn ℝ Work.Stability.smoothOrder
      (fun θ : ℝ => Work.Spaces.DzIter j Ξ z θ) (Set.Ioo 0 (Real.pi / 2)) := by
  have h1 : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (Work.Spaces.DzIter j Ξ))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    fun n => (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp (hΞ.DzIter j) n
  have h2 : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.DzIter j Ξ)) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    intro x hx m _
    exact h1 m x hx m le_rfl
  exact Work.FTS.LocData.contDiffOn_slice_θ (s := Set.Ioi 0) (t := Set.Ioo 0 (Real.pi / 2)) h2 hz

/-! ## Piece 1 : the layer transfer of `∂_θ²` -/

/-- **The `∂_θ²`-slots of the residual from those of the straightened unknown.**  Since
`Ξ = Ψ̂ − Ḡ(α,g)·sin 2θ` and `∂_θ² (R(z)·sin 2θ) = −4 R(z)·sin 2θ`, on the open quadrant
`∂_θ²Ξ = ∂_θ²Ψ̂ + 4·(Ḡ·sin 2θ)`; the layer is in `ℋᵏ` (`layer_HkMem_target_of_smoothOpen`) with
`|Ḡ·sin 2θ|_{ℋᵏ} ≤ C|g|_{ℋᵏ}` (`layer_Gbar_HkNorm_le_SmoothOpen`), and `ClassC.mem` gives
`HkMem α 7 g`, hence `HkMem α k g` for `k ≤ 5`. -/
theorem vopcK5c_pth2_transfer :
    ∀ k : ℕ, k ≤ 5 → ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (g Φg : Fn), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllSol.ClassC α g →
      Work.FTS.EllipticEst.SmoothOpen (Work.FTS.EllSol.ellShift α g Φg) →
      Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 (Work.FTS.EllSol.ellShift α g Φg)) →
      Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 (Work.Elliptic.EllResid α g Φg)) ∧
      Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 (Work.Elliptic.EllResid α g Φg))
        ≤ C * (Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 (Work.FTS.EllSol.ellShift α g Φg))
              + Work.Spaces.HkNorm α k g) := by
  intro k hk5
  obtain ⟨CG, hCG0, hGle⟩ :=
    Work.FTS.EllipticEst.Cert.GbarLayer.layer_Gbar_HkNorm_le_SmoothOpen k
  refine ⟨Real.sqrt 2 * (1 + 4 * CG), by positivity, ?_⟩
  intro α g Φg hα hα4 hC hX hmemX
  have hα1 : α ≤ 1 := by linarith
  have hgn : Work.Spaces.HkMem α k g :=
    Work.FTS.EllipticEst.TT.HkMem_descend_open (by omega) hC.reg.forall hC.mem
  -- the layer `Ḡ(α,g)·sin 2θ`, in both signs
  have hNsm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (-Work.Elliptic.Gbar α g z) * Real.sin (2 * θ)) :=
    smoothOpen_negGbarSin_classC (α := α) (g := g) hα hC.reg hC.fsm hC.mem
  have hGsm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Elliptic.Gbar α g z * Real.sin (2 * θ)) :=
    Work.FTS.EllipticEst.SmoothOpen.congr
      (Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl (-1) hNsm)
      (fun z θ _ _ _ => by ring)
  have hGmem : Work.Spaces.HkMem α k
      (fun z θ => Work.Elliptic.Gbar α g z * Real.sin (2 * θ)) :=
    Work.FTS.EllipticEst.Cert.GbarLayer.layer_HkMem_target_of_smoothOpen α hα hα1 k g hC.reg hgn
  have hGle' : Work.Spaces.HkNorm α k
      (fun z θ => Work.Elliptic.Gbar α g z * Real.sin (2 * θ)) ≤ CG * Work.Spaces.HkNorm α k g :=
    hGle α g hα hα1 hC.reg hgn
  -- the pointwise identity `∂_θ²Ξ = ∂_θ²Ψ̂ + 4·(Ḡ sin 2θ)`
  have hpoint : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pthIter 2 (Work.Elliptic.EllResid α g Φg) z θ
        = Work.Spaces.pthIter 2 (Work.FTS.EllSol.ellShift α g Φg) z θ
          + 4 * (Work.Elliptic.Gbar α g z * Real.sin (2 * θ)) := by
    intro z θ hz hθ0 hθ1
    have hE : Work.Elliptic.EllResid α g Φg
        = fun z θ => Work.FTS.EllSol.ellShift α g Φg z θ
            + (-Work.Elliptic.Gbar α g z) * Real.sin (2 * θ) := by
      funext z θ
      rw [Work.FTS.EllSol.EllResid_eq_ellShift_sub_Gbar_point]
      simp only [Work.FTS.EllSol.ellShift_apply]
      ring
    rw [hE, Work.FTS.EllipticEst.RPFresh.pthIter_add_on_Q0 hX hNsm 2 z θ hz hθ0 hθ1,
      congrFun (congrFun (Work.FTS.EllipticEst.RPFresh.pthIter_two_radial_sin
        (fun z => -Work.Elliptic.Gbar α g z)) z) θ]
    ring
  refine ⟨?_, ?_⟩
  · -- membership
    refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α k ?_
      (fun z hz θ hθ => (hpoint z θ hz hθ.1 hθ.2).symm)
    exact Work.FTS.EllipticEst.HkMem_add_open hX.pth.pth
      (Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl 4 hGsm) hmemX
      (Work.FTS.LocData.HkMem_const_mul α k 4 hGmem)
  · -- norm
    have heq : Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 (Work.Elliptic.EllResid α g Φg))
        = Work.Spaces.HkNorm α k (fun z θ => Work.Spaces.pthIter 2
            (Work.FTS.EllSol.ellShift α g Φg) z θ
              + 4 * (Work.Elliptic.Gbar α g z * Real.sin (2 * θ))) := by
      rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm,
        Work.FTS.EllipticEst.HkSq_congr_open α k hpoint]
    rw [heq]
    have htri := Work.FTS.EllipticEst.HkNorm_add_le α k hX.pth.pth.forall
      (Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl 4 hGsm).forall hmemX
      (Work.FTS.LocData.HkMem_const_mul α k 4 hGmem)
    have h4 : Work.Spaces.HkNorm α k (fun z θ => 4 * (Work.Elliptic.Gbar α g z
        * Real.sin (2 * θ)))
        ≤ 4 * (CG * Work.Spaces.HkNorm α k g) := by
      rw [Work.FTS.EllipticEst.HkNorm_const_mul α k 4 hGsm.forall]
      have h2 : |(4 : ℝ)| = 4 := by norm_num
      rw [h2]
      exact mul_le_mul_of_nonneg_left hGle' (by norm_num)
    have hB0 := Work.Spaces.HkNorm_nonneg α k (Work.Spaces.pthIter 2
      (Work.FTS.EllSol.ellShift α g Φg))
    have hG0 := Work.Spaces.HkNorm_nonneg α k g
    calc Work.Spaces.HkNorm α k (fun z θ => Work.Spaces.pthIter 2
          (Work.FTS.EllSol.ellShift α g Φg) z θ
            + 4 * (Work.Elliptic.Gbar α g z * Real.sin (2 * θ)))
        ≤ Real.sqrt 2 * (Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2
              (Work.FTS.EllSol.ellShift α g Φg))
            + Work.Spaces.HkNorm α k (fun z θ => 4 * (Work.Elliptic.Gbar α g z
                * Real.sin (2 * θ)))) := htri
      _ ≤ Real.sqrt 2 * (Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2
              (Work.FTS.EllSol.ellShift α g Φg)) + 4 * (CG * Work.Spaces.HkNorm α k g)) :=
          mul_le_mul_of_nonneg_left (add_le_add le_rfl h4) (Real.sqrt_nonneg 2)
      _ ≤ Real.sqrt 2 * (1 + 4 * CG) * (Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2
              (Work.FTS.EllSol.ellShift α g Φg)) + Work.Spaces.HkNorm α k g) := by
          have hkey : Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2
                (Work.FTS.EllSol.ellShift α g Φg)) + 4 * (CG * Work.Spaces.HkNorm α k g)
              ≤ (1 + 4 * CG) * (Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2
                (Work.FTS.EllSol.ellShift α g Φg)) + Work.Spaces.HkNorm α k g) := by
            nlinarith [hB0, hG0, hCG0]
          calc Real.sqrt 2 * (Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2
                (Work.FTS.EllSol.ellShift α g Φg)) + 4 * (CG * Work.Spaces.HkNorm α k g))
              ≤ Real.sqrt 2 * ((1 + 4 * CG) * (Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2
                (Work.FTS.EllSol.ellShift α g Φg)) + Work.Spaces.HkNorm α k g)) :=
                mul_le_mul_of_nonneg_left hkey (Real.sqrt_nonneg 2)
            _ = Real.sqrt 2 * (1 + 4 * CG) * (Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2
                (Work.FTS.EllSol.ellShift α g Φg)) + Work.Spaces.HkNorm α k g) := by ring

/-! ## Piece 2 : the abstract `V`-slot -/

/-- **The `V`-slot from the `∂_θ²`-data of the residual.**  On the open quadrant
`V(Ξ) = ∂_θΞ − 2 sin²θ·(Ξ/sin 2θ)`; `thetaPoincareOpenTrace` controls `Ξ`, `∂_θΞ` by `∂_θ²Ξ`,
`divSinK5` controls `Ξ/sin 2θ` by `∂_θΞ`, and `HkMul_ang_le` the angular multiplier `2 sin²θ`.
The slice-smoothness hypothesis is the interface of `divSinK5`. -/
theorem vopcK5c_core (k : ℕ) (hk : 1 ≤ k) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (Ξ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.SmoothOpen Ξ →
      (∀ j : ℕ, j ≤ k → ∀ z : ℝ, 0 < z →
        Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j Ξ z θ)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
        Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j Ξ z θ)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) →
      (∀ z : ℝ, 0 < z → ∀ j : ℕ, j ≤ k → ContDiffOn ℝ Work.Stability.smoothOrder
        (fun θ : ℝ => Work.Spaces.DzIter j Ξ z θ) (Set.Ioo 0 (Real.pi / 2))) →
      Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 Ξ) →
      Work.FTS.VocabO.HQo α k (Work.FTS.EllipticEst.Vop α Ξ) ∧
      Work.Spaces.HkNorm α k (Work.FTS.EllipticEst.Vop α Ξ)
        ≤ C * Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 Ξ) := by
  obtain ⟨Cd, hCd0, hdiv⟩ := divSinK5 k hk
  obtain ⟨Cp, hCp0, hpo⟩ := Work.FTS.EllSol.VopAux.thetaPoincareOpenTrace k
  obtain ⟨Ca, hCa0, hang⟩ := Work.Blocks.HkMul_ang_le k
  have hCa0' : (0 : ℝ) ≤ Real.sqrt Ca := Real.sqrt_nonneg Ca
  refine ⟨Real.sqrt 2 * (1 + 2 * Real.sqrt Ca * Cd) * Cp, by positivity, ?_⟩
  intro α Ξ hα hα4 hsm htr hsl hmem
  have hα1 : α ≤ 1 := by linarith
  have htr0 : ∀ z : ℝ, 0 < z → ∀ j : ℕ, j ≤ k →
      Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j Ξ z θ)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
    fun z hz j hj => (htr j hj z hz).1
  have htr1 : ∀ z : ℝ, 0 < z → ∀ j : ℕ, j ≤ k →
      Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j Ξ z θ)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) :=
    fun z hz j hj => (htr j hj z hz).2
  -- ## the Poincaré estimate on `Ξ`
  obtain ⟨hmemΞ, hmempthΞ, hleΞ, hlepthΞ⟩ := hpo α Ξ hα hα4 hsm.forall htr hmem
  -- ## the division estimate
  obtain ⟨hmemQ, hleQ⟩ := hdiv α Ξ hα hα1 hsm hsl htr0 htr1 hmempthΞ
  have hQsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Ξ z θ / Real.sin (2 * θ)) :=
    Work.FTS.EllipticEst.RPFresh.smoothOpen_div_sin hsm
  -- ## the `sin²θ` multiplier
  have hSsmem : Work.Spaces.HkMem α k
      (fun z θ => Real.sin θ ^ 2 * (Ξ z θ / Real.sin (2 * θ))) :=
    ((hang α (fun z θ => Ξ z θ / Real.sin (2 * θ)) hα hα1 hQsm).2.2 hmemQ).2.2.1
  have hSsq : Work.Spaces.HkSq α k (fun z θ => Real.sin θ ^ 2 * (Ξ z θ / Real.sin (2 * θ)))
      ≤ Ca * Work.Spaces.HkSq α k (fun z θ => Ξ z θ / Real.sin (2 * θ)) :=
    ((hang α (fun z θ => Ξ z θ / Real.sin (2 * θ)) hα hα1 hQsm).2.2 hmemQ).2.2.2
  have hSsm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Real.sin θ ^ 2 * (Ξ z θ / Real.sin (2 * θ))) :=
    Work.FTS.Nonlinear.N4Fields.smoothOpen_angMul (a := fun θ => Real.sin θ ^ 2)
      (by fun_prop) hQsm
  have hTsm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (-2 : ℝ) * (Real.sin θ ^ 2 * (Ξ z θ / Real.sin (2 * θ)))) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl (-2) hSsm
  have hTsmem : Work.Spaces.HkMem α k
      (fun z θ => (-2 : ℝ) * (Real.sin θ ^ 2 * (Ξ z θ / Real.sin (2 * θ)))) :=
    Work.FTS.LocData.HkMem_const_mul α k (-2) hSsmem
  have hSnorm : Work.Spaces.HkNorm α k
      (fun z θ => Real.sin θ ^ 2 * (Ξ z θ / Real.sin (2 * θ)))
      ≤ Real.sqrt Ca * Work.Spaces.HkNorm α k (fun z θ => Ξ z θ / Real.sin (2 * θ)) := by
    have h1 : Real.sqrt (Work.Spaces.HkSq α k
        (fun z θ => Real.sin θ ^ 2 * (Ξ z θ / Real.sin (2 * θ))))
        ≤ Real.sqrt (Ca * Work.Spaces.HkSq α k (fun z θ => Ξ z θ / Real.sin (2 * θ))) :=
      Real.sqrt_le_sqrt hSsq
    have h2 : Real.sqrt (Ca * Work.Spaces.HkSq α k (fun z θ => Ξ z θ / Real.sin (2 * θ)))
        = Real.sqrt Ca * Real.sqrt (Work.Spaces.HkSq α k
            (fun z θ => Ξ z θ / Real.sin (2 * θ))) :=
      Real.sqrt_mul (x := Ca) (le_of_lt hCa0) _
    rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm]
    exact le_trans h1 (le_of_eq h2)
  have hTnorm : Work.Spaces.HkNorm α k
      (fun z θ => (-2 : ℝ) * (Real.sin θ ^ 2 * (Ξ z θ / Real.sin (2 * θ))))
      ≤ 2 * (Real.sqrt Ca * (Cd * (Cp * Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 Ξ)))) := by
    rw [Work.FTS.EllipticEst.HkNorm_const_mul α k (-2) hSsm.forall]
    have h1 : (|(-2 : ℝ)|) * Work.Spaces.HkNorm α k
        (fun z θ => Real.sin θ ^ 2 * (Ξ z θ / Real.sin (2 * θ)))
        = 2 * Work.Spaces.HkNorm α k
          (fun z θ => Real.sin θ ^ 2 * (Ξ z θ / Real.sin (2 * θ))) := by norm_num
    rw [h1]
    have h2 : Work.Spaces.HkNorm α k (fun z θ => Ξ z θ / Real.sin (2 * θ))
        ≤ Cd * (Cp * Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 Ξ)) := by
      calc Work.Spaces.HkNorm α k (fun z θ => Ξ z θ / Real.sin (2 * θ))
          ≤ Cd * Work.Spaces.HkNorm α k (Work.Spaces.pth Ξ) := hleQ
        _ ≤ Cd * (Cp * Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 Ξ)) :=
            mul_le_mul_of_nonneg_left hlepthΞ (le_of_lt hCd0)
    calc 2 * Work.Spaces.HkNorm α k (fun z θ => Real.sin θ ^ 2 * (Ξ z θ / Real.sin (2 * θ)))
        ≤ 2 * (Real.sqrt Ca * Work.Spaces.HkNorm α k (fun z θ => Ξ z θ / Real.sin (2 * θ))) :=
          mul_le_mul_of_nonneg_left hSnorm (by norm_num)
      _ ≤ 2 * (Real.sqrt Ca * (Cd * (Cp * Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 Ξ)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hCa0') (by norm_num)
  -- ## the pointwise identity
  have hpoint : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.FTS.EllipticEst.Vop α Ξ z θ
        = Work.Spaces.pth Ξ z θ
          + (-2 : ℝ) * (Real.sin θ ^ 2 * (Ξ z θ / Real.sin (2 * θ))) := by
    intro z θ hz hθ0 hθ1
    have hcos : Real.cos θ ≠ 0 :=
      ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ1⟩)
    have hsin : Real.sin θ ≠ 0 :=
      ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos, hθ1]))
    show Work.Spaces.pth Ξ z θ - Real.tan θ * Ξ z θ = _
    rw [Real.tan_eq_sin_div_cos, Real.sin_two_mul]
    field_simp
    ring
  -- ## smoothness, membership and norm
  have hVopsm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.EllipticEst.Vop α Ξ) :=
    Work.FTS.EllipticEst.SmoothOpen.congr
      (Work.FTS.EllipticEst.smoothOpen_add hsm.pth hTsm)
      (fun z θ hz hθ0 hθ1 => (hpoint z θ hz hθ0 hθ1).symm)
  have hVopmem : Work.Spaces.HkMem α k (Work.FTS.EllipticEst.Vop α Ξ) :=
    Work.FTS.EllipticEst.HkMem_agreeOnQ hVopsm
      (fun z θ hz hθ0 hθ1 => (hpoint z θ hz hθ0 hθ1).symm)
      (Work.FTS.EllipticEst.HkMem_add_open hsm.pth hTsm hmempthΞ hTsmem)
  refine ⟨⟨hVopsm, hVopmem⟩, ?_⟩
  have hsqeq : Work.Spaces.HkSq α k (Work.FTS.EllipticEst.Vop α Ξ)
      = Work.Spaces.HkSq α k (fun z θ => Work.Spaces.pth Ξ z θ
          + (-2 : ℝ) * (Real.sin θ ^ 2 * (Ξ z θ / Real.sin (2 * θ)))) :=
    Work.FTS.EllipticEst.HkSq_congr_open α k hpoint
  have hnormeq : Work.Spaces.HkNorm α k (Work.FTS.EllipticEst.Vop α Ξ)
      = Work.Spaces.HkNorm α k (fun z θ => Work.Spaces.pth Ξ z θ
          + (-2 : ℝ) * (Real.sin θ ^ 2 * (Ξ z θ / Real.sin (2 * θ)))) := by
    rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm, hsqeq]
  rw [hnormeq]
  have htri := Work.FTS.EllipticEst.HkNorm_add_le α k hsm.pth.forall hTsm.forall
    hmempthΞ hTsmem
  calc Work.Spaces.HkNorm α k (fun z θ => Work.Spaces.pth Ξ z θ
        + (-2 : ℝ) * (Real.sin θ ^ 2 * (Ξ z θ / Real.sin (2 * θ))))
      ≤ Real.sqrt 2 * (Work.Spaces.HkNorm α k (Work.Spaces.pth Ξ)
          + Work.Spaces.HkNorm α k (fun z θ => (-2 : ℝ) * (Real.sin θ ^ 2
              * (Ξ z θ / Real.sin (2 * θ))))) := htri
    _ ≤ Real.sqrt 2 * (Cp * Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 Ξ)
          + 2 * (Real.sqrt Ca * (Cd * (Cp * Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 Ξ))))) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg 2)
        exact add_le_add hlepthΞ hTnorm
    _ = Real.sqrt 2 * (1 + 2 * Real.sqrt Ca * Cd) * Cp
          * Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 Ξ) := by ring

/-! ## The assembly -/

/-- **The `V`-slot from its two pieces.**  Everything else is the dissection of the residual
(smoothness, traces via `Ψ̂`, and the arithmetic of the constants); the conclusion is literally
the frozen target. -/
theorem vopcK5c_assembly
    (hB : ∀ k : ℕ, k ≤ 5 → ∃ C : ℝ, 0 < C ∧
      ∀ (α : ℝ) (g Φg : Fn), 0 < α → α ≤ 1 / 4 →
        Work.FTS.EllSol.ClassC α g →
        Work.FTS.EllipticEst.SmoothOpen (Work.FTS.EllSol.ellShift α g Φg) →
        Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 (Work.FTS.EllSol.ellShift α g Φg)) →
        Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 (Work.Elliptic.EllResid α g Φg)) ∧
        Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 (Work.Elliptic.EllResid α g Φg))
          ≤ C * (Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 (Work.FTS.EllSol.ellShift α g Φg))
                + Work.Spaces.HkNorm α k g))
    (hV : ∀ k : ℕ, 1 ≤ k → ∃ C : ℝ, 0 < C ∧
      ∀ (α : ℝ) (Ξ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
        Work.FTS.EllipticEst.SmoothOpen Ξ →
        (∀ j : ℕ, j ≤ k → ∀ z : ℝ, 0 < z →
          Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j Ξ z θ)
            (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
          Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j Ξ z θ)
            (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) →
        (∀ z : ℝ, 0 < z → ∀ j : ℕ, j ≤ k → ContDiffOn ℝ Work.Stability.smoothOrder
          (fun θ : ℝ => Work.Spaces.DzIter j Ξ z θ) (Set.Ioo 0 (Real.pi / 2))) →
        Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 Ξ) →
        Work.FTS.VocabO.HQo α k (Work.FTS.EllipticEst.Vop α Ξ) ∧
        Work.Spaces.HkNorm α k (Work.FTS.EllipticEst.Vop α Ξ)
          ≤ C * Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 Ξ))
    (k : ℕ) (hk : 2 ≤ k) (hk5 : k ≤ 5) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (g Φg : Work.FTS.Galerkin.Fn), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllSol.ClassC α g →
      Work.FTS.StrongGlobal.IsBslSolPos α g Φg →
      Work.FTS.EllipticEst.SmoothOpen Φg →
      Work.FTS.EllipticEst.TT.EllWeakPos α k (Work.Elliptic.orthSource g)
        (Work.FTS.EllSol.ellShift α g Φg) →
      Work.Spaces.HkMem α (k + 3) (fun z θ => z ^ 2 * Work.Spaces.pzIter 2
        (Work.FTS.EllSol.ellShift α g Φg) z θ) →
      Work.Spaces.HkMem α (k + 2) (Work.Elliptic.orthSource g) →
      Work.FTS.VocabO.HQo α k (Work.Construction.Vop (Work.Construction.PhiTil α g Φg)) ∧
      Work.Spaces.HkNorm α k (Work.Construction.Vop (Work.Construction.PhiTil α g Φg))
        ≤ C * (α ^ 2 * Work.Spaces.HkNorm α k
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.FTS.EllSol.ellShift α g Φg) z θ)
            + Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 (Work.FTS.EllSol.ellShift α g Φg))
            + Work.Spaces.HkNorm α k g) := by
  obtain ⟨CB, hCB0, hB'⟩ := hB k hk5
  obtain ⟨CV, hCV0, hV'⟩ := hV k (by omega)
  refine ⟨CV * CB, mul_pos hCV0 hCB0, ?_⟩
  intro α g Φg hα hα4 hC hsol hsmo hweak hAh hFmem
  -- ## the straight unknown is smooth and carries the traces
  have hXsm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.EllSol.ellShift α g Φg) :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hweak.smooth
  have htrX := tracesK5 k hk α g Φg hα hα4 hC hsol hsmo hweak hAh hFmem
  have htrΞ := residTracesK5 k α g Φg hα hα4 hC hXsm htrX
  -- ## the smoothness of the residual and of its slices
  have hΞsm : Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.EllResid α g Φg) :=
    vopcK5c_resid_smooth (α := α) (g := g) (Φg := Φg) hα hC hXsm
  have hslice : ∀ z : ℝ, 0 < z → ∀ j : ℕ, j ≤ k → ContDiffOn ℝ Work.Stability.smoothOrder
      (fun θ : ℝ => Work.Spaces.DzIter j (Work.Elliptic.EllResid α g Φg) z θ)
      (Set.Ioo 0 (Real.pi / 2)) :=
    fun z hz j _ => vopcK5c_slice_smooth hΞsm j hz
  -- ## the two pieces
  have hBk := hB' α g Φg hα hα4 hC hXsm hweak.memB
  have hVk := hV' α (Work.Elliptic.EllResid α g Φg) hα hα4 hΞsm
    (fun j hj z hz => htrΞ j (by omega) z hz) hslice hBk.1
  rw [Work.FTS.EllipticEst.Vop_PhiTil_eq]
  refine ⟨hVk.1, ?_⟩
  -- ## the arithmetic of the constants
  have hA0 : (0 : ℝ) ≤ α ^ 2 * Work.Spaces.HkNorm α k
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.FTS.EllSol.ellShift α g Φg) z θ) :=
    mul_nonneg (sq_nonneg α) (Work.Spaces.HkNorm_nonneg α k _)
  have hCVnn : (0 : ℝ) ≤ CV := le_of_lt hCV0
  calc Work.Spaces.HkNorm α k (Work.FTS.EllipticEst.Vop α (Work.Elliptic.EllResid α g Φg))
      ≤ CV * Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 (Work.Elliptic.EllResid α g Φg)) :=
        hVk.2
    _ ≤ CV * (CB * (Work.Spaces.HkNorm α k
            (Work.Spaces.pthIter 2 (Work.FTS.EllSol.ellShift α g Φg))
          + Work.Spaces.HkNorm α k g)) :=
        mul_le_mul_of_nonneg_left hBk.2 hCVnn
    _ = CV * CB * (Work.Spaces.HkNorm α k
            (Work.Spaces.pthIter 2 (Work.FTS.EllSol.ellShift α g Φg))
          + Work.Spaces.HkNorm α k g) := by ring
    _ ≤ CV * CB * (α ^ 2 * Work.Spaces.HkNorm α k
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.FTS.EllSol.ellShift α g Φg) z θ)
          + Work.Spaces.HkNorm α k
            (Work.Spaces.pthIter 2 (Work.FTS.EllSol.ellShift α g Φg))
          + Work.Spaces.HkNorm α k g) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        linarith [hA0]

theorem vopTransferK5c (k : ℕ) (hk : 2 ≤ k) (hk5 : k ≤ 5) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (g Φg : Work.FTS.Galerkin.Fn), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllSol.ClassC α g →
      Work.FTS.StrongGlobal.IsBslSolPos α g Φg →
      Work.FTS.EllipticEst.SmoothOpen Φg →
      Work.FTS.EllipticEst.TT.EllWeakPos α k (Work.Elliptic.orthSource g)
        (Work.FTS.EllSol.ellShift α g Φg) →
      Work.Spaces.HkMem α (k + 3) (fun z θ => z ^ 2 * Work.Spaces.pzIter 2
        (Work.FTS.EllSol.ellShift α g Φg) z θ) →
      Work.Spaces.HkMem α (k + 2) (Work.Elliptic.orthSource g) →
      Work.FTS.VocabO.HQo α k (Work.Construction.Vop (Work.Construction.PhiTil α g Φg)) ∧
      Work.Spaces.HkNorm α k (Work.Construction.Vop (Work.Construction.PhiTil α g Φg))
        ≤ C * (α ^ 2 * Work.Spaces.HkNorm α k
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.FTS.EllSol.ellShift α g Φg) z θ)
            + Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 (Work.FTS.EllSol.ellShift α g Φg))
            + Work.Spaces.HkNorm α k g) :=
  vopcK5c_assembly vopcK5c_pth2_transfer vopcK5c_core k hk hk5

end Work.FTS.EllSol.PkgK5
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5Aux2.L12_epsRHSP_zero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5Aux2

/-!
# `L₁₂` of the projected right-hand side `epsRHSP` vanishes at `z = 0`

The scheme's right-hand side is, by definition,
`epsRHSP α ρ ε Φs E g τ = P₀ (J_ε (epsWP α ρ ε Φs E g τ))` (`epsRHSP_eq_Pz_Jeps_epsWP`), and the
projection is `P₀ f = f − (L₁₂ f 0 / pzNorm) • b` with `b = bump` and `pzNorm = L₁₂ b 0`
(`pzNorm_pos`).  The `l12` clause of the source class is therefore automatic:

  the projection identity `X = P₀ X + (L₁₂ X 0 / pzNorm) • b`

is pure algebra, and it lets us run the standard computation `L₁₂(P₀ X)(0) = 0` in the direction
that the present hypotheses support.  Indeed `PZeroAux.L12_add_mul_ae` (linearity of `L₁₂(·)(0)`
in the a.e. slice-integrability setting) applied to `f = P₀ X` and `h = b` gives

  `L₁₂ X 0 = L₁₂ (P₀ X) 0 + (L₁₂ X 0 / pzNorm) · L₁₂ b 0`,

and `L₁₂ b 0 = pzNorm`, so the second summand is `L₁₂ X 0` and `L₁₂ (P₀ X) 0 = 0`.

The two hypotheses of the statement are exactly the two integrability certificates that
`L12_add_mul_ae` needs for `f = P₀ X`: the density of `P₀ X` on `(0,∞)` (`hdens`) and the
θ-slices of `P₀ X` a.e. (`hslice`).  The corresponding certificates for the correction profile
`b` are unconditional (`PZeroAux.integrableOn_L12dens_bump`,
`PZeroAux.integrableOn_slice_bump`). -/

theorem L12_epsRHSP_zero {α ε τ : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hdens : MeasureTheory.IntegrableOn
      (Work.Construction.L12dens (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g τ)) (Set.Ioi 0))
    (hslice : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      MeasureTheory.IntegrableOn (fun θ : ℝ => Work.Spaces.K θ *
        Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g τ r θ / r) Work.Spaces.Iθ) :
    Work.Construction.L12 (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g τ) 0 = 0 := by
  -- the unprojected, mollified pre-mollified right-hand side
  set X : ℝ → ℝ → ℝ :=
    Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.StrongEps.epsWP α ρ ε Φs E g τ) with hX
  have hpz : Work.FTS.StrongEps.pzNorm ≠ 0 :=
    ne_of_gt Work.FTS.StrongEps.PZeroAux.pzNorm_pos
  -- the θ-slices of the correction profile are integrable at every `s > 0`
  have hbs : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      MeasureTheory.IntegrableOn
        (fun θ : ℝ => Work.Spaces.K θ * Work.FTS.StrongEps.bump s θ / s) Work.Spaces.Iθ :=
    (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr
      (Filter.Eventually.of_forall fun s hs =>
        Work.FTS.StrongEps.PZeroAux.integrableOn_slice_bump hs)
  have hB : MeasureTheory.IntegrableOn
      (fun s : ℝ => ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.K θ * Work.FTS.StrongEps.bump s θ / s) (Set.Ioi 0) :=
    Work.FTS.StrongEps.PZeroAux.integrableOn_L12dens_bump
  -- the projected right-hand side is `P₀` of `X`, definitionally
  have hPzX : Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g τ = Work.FTS.StrongEps.Pz X := by
    rw [hX]
    exact Work.FTS.StrongEps.epsRHSP_eq_Pz_Jeps_epsWP α ρ ε Φs E g τ
  -- `P₀ X` plus the correction profile reassembles `X`
  have hfun : (fun z θ => Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g τ z θ
        + (Work.Construction.L12 X 0 / Work.FTS.StrongEps.pzNorm)
          * Work.FTS.StrongEps.bump z θ) = X := by
    funext z θ
    rw [hPzX, Work.FTS.StrongEps.Pz_apply]
    ring
  -- linearity of `L₁₂(·)(0)` at the two admissible pieces
  have hlin := Work.FTS.StrongEps.PZeroAux.L12_add_mul_ae
    (f := Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g τ)
    (h := Work.FTS.StrongEps.bump)
    (c := Work.Construction.L12 X 0 / Work.FTS.StrongEps.pzNorm) hslice hbs hdens hB
  rw [hfun] at hlin
  -- `(L₁₂ X 0 / pzNorm) · pzNorm = L₁₂ X 0`
  have hc : (Work.Construction.L12 X 0 / Work.FTS.StrongEps.pzNorm)
        * Work.Construction.L12 Work.FTS.StrongEps.bump 0 = Work.Construction.L12 X 0 := by
    rw [show Work.Construction.L12 Work.FTS.StrongEps.bump 0 = Work.FTS.StrongEps.pzNorm from rfl]
    exact div_mul_cancel₀ _ hpz
  linarith

end Work.FTS.StrongEps.E5Aux2
end
-- ===== merged: Submission.Work.FTS.StrongEps.RhsCont =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The general brick -/

/-- **The fake-time continuity of an equation's right-hand side, from joint `C¹`.**

Let `F` be a family which is jointly `C¹` on the open quadrant times `Icc 0 T`, and which solves
`∂_τ F z θ = R z θ τ` (within `Icc 0 T`) at every point of the open quadrant.  Then for every
`(z,θ)` of the open quadrant the function `τ ↦ R z θ τ` is continuous on `Icc 0 T`.

Proof: the τ-slice `s ↦ F z θ s` is `C¹` on `Icc 0 T` (restriction of the joint regularity), its
within-derivative is continuous there (`ContDiffOn.continuousOn_derivWithin`), and at every
`τ ∈ Icc 0 T` that within-derivative is `R z θ τ` (uniqueness of the within-derivative, the point
being in the interval). -/
theorem continuousOn_rhs_of_contDiffOn_one {F : Fam} {R : ℝ → ℝ → ℝ → ℝ} {T : ℝ}
    (hT : 0 < T)
    (hreg : ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => F p.1 p.2.1 p.2.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Icc 0 T))
    (heq : ∀ z θ τ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) → τ ∈ Set.Icc 0 T →
      HasDerivWithinAt (fun s => F z θ s) (R z θ τ) (Set.Icc 0 T) τ) :
    ∀ z θ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      ContinuousOn (fun τ => R z θ τ) (Set.Icc 0 T) := by
  intro z θ hz hθ
  have hsU : UniqueDiffOn ℝ (Set.Icc 0 T) := uniqueDiffOn_Icc hT
  -- the τ-slice is `C¹` on the interval
  have hslice : ContDiffOn ℝ 1 (fun s : ℝ => F z θ s) (Set.Icc 0 T) := by
    have h1 : ContDiff ℝ 1 (fun _ : ℝ => (z : ℝ)) := contDiff_const
    have h2 : ContDiff ℝ 1 (fun _ : ℝ => (θ : ℝ)) := contDiff_const
    have h3 : ContDiff ℝ 1 (fun s : ℝ => s) := contDiff_id
    have hlin : ContDiff ℝ 1 (fun s : ℝ => (z, (θ, s))) := h1.prodMk (h2.prodMk h3)
    have hcomp : ContDiffOn ℝ 1
        ((fun p : ℝ × ℝ × ℝ => F p.1 p.2.1 p.2.2) ∘ (fun s : ℝ => (z, (θ, s))))
        (Set.Icc 0 T) :=
      hreg.comp hlin.contDiffOn (fun s hs => ⟨hz, hθ, hs⟩)
    exact hcomp.congr (fun s _ => rfl)
  refine (hslice.continuousOn_derivWithin hsU le_rfl).congr (fun τ hτ => ?_)
  exact ((heq z θ τ hz hθ hτ).derivWithin (hsU.uniqueDiffWithinAt hτ)).symm

/-! ## The two instances on the proof path -/

/-- **`hcont` of `EpsLimVolterraP` for a regular `P₀`-solution**: the continuity in the fake time
of the projected scheme's right-hand side.  The inputs are the joint `C¹` of `EpsRegP` and the
scheme's equation `IsEpsSolP`. -/
theorem continuousOn_epsRHSP_of_regP {α ε T : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E_ : Fn → Fn}
    {g₀ : Fn} {g : Fam}
    (hT : 0 < T) (hsol : IsEpsSolP α ρ ε T Φs E_ g₀ g)
    (hreg : EpsRegP α ρ ε T g) :
    ∀ p : ℝ × ℝ, p ∈ Work.FTS.EllipticEst.Q0 →
      ContinuousOn (fun s : ℝ => epsRHSP α ρ ε Φs E_ g s p.1 p.2) (Set.Icc 0 T) := by
  intro p hp
  obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  have h := continuousOn_rhs_of_contDiffOn_one (F := g)
    (R := fun z θ τ => epsRHSP α ρ ε Φs E_ g τ z θ) hT hreg.1
    (fun z θ τ hz hθ hτ => hsol.2 z θ τ hz hθ hτ)
  exact h p.1 p.2 hz ⟨hθ0, hθ1⟩


end Work.FTS.StrongEps
end
end
