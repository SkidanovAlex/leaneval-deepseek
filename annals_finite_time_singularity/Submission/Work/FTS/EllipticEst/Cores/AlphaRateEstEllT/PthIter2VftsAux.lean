import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.RegQ
import Submission.Work.FTS.EllipticEst.Cores.AlphaDzDthDefs
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.Cores.DiagEstEllT.StraightMem
import Submission.Work.FTS.EllipticEst.Cores.DiagEstEllT.FiniteFacts
import Submission.Work.FTS.EllipticEst.Cores.DiagEstEllT.VMem
import Submission.Work.FTS.EllipticEst.Cores.DiagEstEllT.HkIntegrand_add_le_of_contDiffOn
import Submission.Work.FTS.EllipticEst.Cores.DiagEstEllT.HkMem_of_add_dominated_open
import Submission.Work.FTS.EllipticEst.Cert.GbarLayer.Target
import Submission.Work.FTS.EllipticEst.Cert.FstarSin_mem
import Submission.Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0
import Submission.Work.FTS.EllipticEst.UopHk.L12_contDiffOn_reg
import Submission.Work.FTS.EllipticEst.HkSq_congr_open
import Submission.Work.FTS.EllipticEst.RPFresh.straight_transfers
import Submission.Work.FTS.LocData.HkMem_const_mul
import Submission.Work.FTS.EllipticEst.Cores.AlphaRateEstEllT.HkSq_add_le_of_contDiffOn_le
import Submission.Work.FTS.EllipticEst.RegQ.pth_EllResid_pointwise_smoothQuad
import Submission.Work.Elliptic.bslOp_add

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cores.AlphaRateEstEllT

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# Auxiliary lemmas for `PthIter2Vfts_le_honest`

This module collects the auxiliary results used by the `∂_θθ`-transfer of the trace-free class
`EllHypT` (`Submission/Work/FTS/EllipticEst/Cores/AlphaRateEstEllT/PthIter2Vfts_le_honest.lean`):

* the finite-smoothness closure of `ℋ^k` (`HkIntegrand_add_le_domain`,
  `HkMem_add_of_contDiffOn_le`), for summands that are only `C^k` on the open quadrant;
* the pointwise `∂_θθ`-identities of the straightening
  (`pthIter2_EllResid_eq_fts`, `pthIter2_Vfts_eq_fts`);
* the honest membership `∂_θθΞ ∈ ℋ^k` under the orthogonality condition
  (`HkMem_pthIter2_EllResid_fts`), from `Gsing α F = -(15/4) F_*(Ψ)`.
-/

/-! ## The finite-smoothness closure of `ℋ^k` -/

/-- **Subadditivity of the `ℋ^k`-integrand at every point of the domain**, for summands that are
`C^k` on the open quadrant.

`Work.FTS.EllipticEst.Cores.DiagEstEllT.HkIntegrand_add_le_of_contDiffOn` gives the inequality at
interior points; on the two boundary lines `z = 0` and `sin 2θ = 0` the integrand of *every*
function vanishes, so the inequality holds there trivially. -/
theorem HkIntegrand_add_le_domain (α : ℝ) (k : ℕ) {f g : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ k (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hg : ContDiffOn ℝ k (Function.uncurry g) Work.FTS.EllipticEst.Q0) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k (fun z θ => f z θ + g z θ) z θ
        ≤ 2 * Work.Spaces.HkIntegrand α k f z θ + 2 * Work.Spaces.HkIntegrand α k g z θ := by
  intro z hz θ hθ
  have hz0 : (0 : ℝ) ≤ z := hz
  have hθ0 : (0 : ℝ) ≤ θ := hθ.1
  have hθ1 : θ ≤ Real.pi / 2 := hθ.2
  rcases lt_or_eq_of_le hz0 with hz' | hz'
  · rcases lt_or_eq_of_le hθ0 with hθ' | hθ'
    · rcases lt_or_eq_of_le hθ1 with hθ'' | hθ''
      · exact Work.FTS.EllipticEst.Cores.DiagEstEllT.HkIntegrand_add_le_of_contDiffOn α k hf hg
          z θ hz' hθ' hθ''
      · subst hθ''
        rw [Work.Coercivity.HkIntegrand_eq_zero_of_sin_eq_zero α k
            (fun z θ => f z θ + g z θ) z (Real.pi / 2)
            (by rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]),
          Work.Coercivity.HkIntegrand_eq_zero_of_sin_eq_zero α k f z (Real.pi / 2)
            (by rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]),
          Work.Coercivity.HkIntegrand_eq_zero_of_sin_eq_zero α k g z (Real.pi / 2)
            (by rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi])]
        norm_num
    · subst hθ'
      rw [Work.Coercivity.HkIntegrand_eq_zero_of_sin_eq_zero α k
          (fun z θ => f z θ + g z θ) z 0 (by simp),
        Work.Coercivity.HkIntegrand_eq_zero_of_sin_eq_zero α k f z 0 (by simp),
        Work.Coercivity.HkIntegrand_eq_zero_of_sin_eq_zero α k g z 0 (by simp)]
      norm_num
  · subst hz'
    rw [Work.Spaces.HkIntegrand_zero_z, Work.Spaces.HkIntegrand_zero_z,
      Work.Spaces.HkIntegrand_zero_z]
    norm_num

/-- **`ℋ^k` is closed under addition** for data that are `C^k` on the open quadrant. -/
theorem HkMem_add_of_contDiffOn_le (α : ℝ) (k : ℕ) {f g : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ k (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hg : ContDiffOn ℝ k (Function.uncurry g) Work.FTS.EllipticEst.Q0)
    (hmf : Work.Spaces.HkMem α k f) (hmg : Work.Spaces.HkMem α k g) :
    Work.Spaces.HkMem α k (fun z θ => f z θ + g z θ) := by
  have hsum : ContDiffOn ℝ k (Function.uncurry (fun z θ => f z θ + g z θ))
      Work.FTS.EllipticEst.Q0 :=
    (hf.add hg).congr (fun p _ => rfl)
  refine Work.FTS.EllipticEst.Cores.DiagEstEllT.HkMem_of_add_dominated_cont α k
    (Work.FTS.EllipticEst.Cores.DiagEstEllT.continuousOn_HkIntegrand_of_contDiffOn hsum α)
    hmf hmg ?_
  intro z hz
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
  exact HkIntegrand_add_le_domain α k hf hg z hz θ hθ

/-- Subadditivity of the square root. -/
theorem sqrt_add_le_honest {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  rw [Real.sqrt_le_iff]
  refine ⟨add_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y), ?_⟩
  have h1 := Real.sq_sqrt hx
  have h2 := Real.sq_sqrt hy
  nlinarith [Real.sqrt_nonneg x, Real.sqrt_nonneg y]

/-! ## The `θ`-calculus of the straightening -/

/-- **A radial factor times `sin 2θ` is `C^m` on the open quadrant** as soon as the radial factor
is `C^m` on `(0,∞)`. -/
theorem radial_sin_contDiffOn {R : ℝ → ℝ} {m : ℕ}
    (hR : ContDiffOn ℝ m R (Set.Ioi (0 : ℝ))) :
    ContDiffOn ℝ m (Function.uncurry (fun z θ => R z * Real.sin (2 * θ)))
      Work.FTS.EllipticEst.Q0 := by
  have hRz : ContDiffOn ℝ m (fun p : ℝ × ℝ => R p.1) Work.FTS.EllipticEst.Q0 :=
    hR.comp contDiffOn_fst (fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).1)
  have hsin : ContDiffOn ℝ m (fun p : ℝ × ℝ => Real.sin (2 * p.2))
      Work.FTS.EllipticEst.Q0 :=
    (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn.of_le le_top
  exact (hRz.mul hsin).congr (fun p _ => rfl)

/-- **`∂_θ²Ξ = ∂_θ²Ψ + (1/α)·sin 2θ·L₁₂(F)`** on the open quadrant, in the honest class: the
residual is `Ψ` minus a *radial* factor times `sin 2θ`, so differentiating twice in `θ` only
produces `∂_θ²(sin 2θ) = -4 sin 2θ` and the `-(1/(4α))` prefactor turns into `1/α`. -/
theorem pthIter2_EllResid_eq_fts (k : ℕ) (hk : 2 ≤ k) :
    ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.EllHypT α k F Ψ →
      ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        Work.Spaces.pthIter 2 (Work.Elliptic.EllResid α F Ψ) z θ
          = Work.Spaces.pthIter 2 Ψ z θ
            + (1 / α) * (Work.Elliptic.L12 F z * Real.sin (2 * θ)) := by
  intro α F Ψ hα _ h z θ hz hθ0 hθ1
  have hmain := (Work.FTS.EllipticEst.RegQ.pth_EllResid_pointwise_smoothQuad α hα F Ψ
    h.quadPsi).2 z θ (by linarith) hθ0 hθ1
  rw [hmain]
  ring

/-- **`∂_θ²V = ∂_θ²Ξ - 4·Ḡ·sin 2θ`** on the open quadrant, in the honest class. -/
theorem pthIter2_Vfts_eq_fts (k : ℕ) (hk : 2 ≤ k) :
    ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.EllHypT α k F Ψ →
      ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        Work.Spaces.pthIter 2
            (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ
          = Work.Spaces.pthIter 2 (Work.Elliptic.EllResid α F Ψ) z θ
            + (-4 * (Work.Elliptic.Gbar α F z * Real.sin (2 * θ))) := by
  intro α F Ψ hα hα1 h z θ hz hθ0 hθ1
  have hpt : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := ⟨hz, hθ0, hθ1⟩
  have hΨc : ContDiffAt ℝ 2 (Function.uncurry Ψ) (z, θ) :=
    ((Work.FTS.EllipticEst.RPFresh.contDiffOn_uncurry_of_smoothOpen
        (Work.FTS.EllipticEst.Cores.DiagEstEllT.honest_smoothOpen_Psi h) 2).contDiffAt
      (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hpt))
  have hGc : ContDiffAt ℝ 2
      (Function.uncurry (fun z θ => Work.Elliptic.Gsing α F z * Real.sin (2 * θ))) (z, θ) :=
    (radial_sin_contDiffOn
      ((Work.FTS.EllipticEst.Cores.DiagEstEllT.honest_Gsing_cDiff hα hα1 hk h).1 2
        (by omega))).contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hpt)
  have hadd := Work.Elliptic.pthIter_two_add Ψ
    (fun z θ => Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ hΨc hGc
  have hscal : -4 * Work.Elliptic.Gsing α F z
      = (1 / α) * Work.Elliptic.L12 F z - 4 * Work.Elliptic.Gbar α F z := by
    simp only [Work.Elliptic.Gsing, Work.Elliptic.Gstar]
    field_simp <;> ring
  rw [hadd, Work.FTS.EllipticEst.RPFresh.pthIter_two_radial_sin (Work.Elliptic.Gsing α F),
    pthIter2_EllResid_eq_fts k hk α F Ψ hα hα1 h z θ hz hθ0 hθ1]
  simp only []
  linear_combination (Real.sin (2 * θ)) * hscal

/-- **`∂_θ²Ξ ∈ ℋ^k`** in the trace-free class, under the orthogonality condition.

The orthogonality condition `OrthCond (Ψ + Gsing α F · sin 2θ)` identifies the singular term,
`Gsing α F = -(15/4) F_*(Ψ)` and hence `L₁₂(F) = 15α F_*(Ψ) + 4α Ḡ` on `(0,∞)`
(`DiagEstEllT.honest_Gsing_eq_neg_fstar_Psi`); both layers `F_*(Ψ)·sin 2θ`
(`Cert.HkMem_Fstar_sin_open`) and `Ḡ·sin 2θ` (`Cert.GbarLayer`) are honestly in `ℋ^k` and are
`C^k` on the open quadrant, so the sum decomposition
`∂_θ²Ξ = ∂_θ²Ψ + (1/α)(L₁₂(F)·sin 2θ)` of `pthIter2_EllResid_eq_fts` gives the membership. -/
theorem HkMem_pthIter2_EllResid_fts (k : ℕ) (hk : 2 ≤ k) :
    ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.EllHypT α k F Ψ →
      Work.Elliptic.OrthCond (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) →
      Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 (Work.Elliptic.EllResid α F Ψ)) := by
  intro α F Ψ hα hα4 h hOrth
  have hα1 : α ≤ 1 := by linarith
  have hFsm : Work.FTS.EllipticEst.SmoothOpen F :=
    Work.FTS.EllipticEst.Cores.DiagEstEllT.honest_smoothOpen_F h
  have hFmem : Work.Spaces.HkMem α k F := h.regF.2.1
  have hΨso : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.Cores.DiagEstEllT.honest_smoothOpen_Psi h
  have hL12sm : ContDiffOn ℝ k (Work.Elliptic.L12 F) (Set.Ioi (0 : ℝ)) :=
    Work.FTS.EllipticEst.UopHk.contDiffOn_L12_k α k F hα hα1 hFsm hFmem hk
  have hGbar_sm : ∀ m ≤ k, ContDiffOn ℝ m (Work.Elliptic.Gbar α F) (Set.Ioi (0 : ℝ)) :=
    (Work.FTS.EllipticEst.Cores.DiagEstEllT.honest_Gsing_cDiff hα hα1 hk h).2
  -- ### the orthogonality identity and its algebraic consequences
  have hgs : ∀ z ∈ Set.Ioi (0 : ℝ),
      Work.Elliptic.Gsing α F z = -(15 / 4) * Work.Elliptic.Fstar Ψ z :=
    Work.FTS.EllipticEst.Cores.DiagEstEllT.honest_Gsing_eq_neg_fstar_Psi hα h hOrth
  have hL12id : ∀ z ∈ Set.Ioi (0 : ℝ),
      Work.Elliptic.L12 F z = 15 * α * Work.Elliptic.Fstar Ψ z
        + 4 * α * Work.Elliptic.Gbar α F z := by
    intro z hz
    have h1 : -(1 / (4 * α)) * Work.Elliptic.L12 F z + Work.Elliptic.Gbar α F z
        = -(15 / 4) * Work.Elliptic.Fstar Ψ z := by
      have h' := hgs z hz
      simpa only [Work.Elliptic.Gsing, Work.Elliptic.Gstar] using h'
    have hcancel : -(4 * α) * (-(1 / (4 * α)) * Work.Elliptic.L12 F z)
        = Work.Elliptic.L12 F z := by
      field_simp
    have hL : -(1 / (4 * α)) * Work.Elliptic.L12 F z
        = -(15 / 4) * Work.Elliptic.Fstar Ψ z - Work.Elliptic.Gbar α F z := by
      linarith
    have hmul : Work.Elliptic.L12 F z
        = -(4 * α) * (-(15 / 4) * Work.Elliptic.Fstar Ψ z
            - Work.Elliptic.Gbar α F z) := by
      rw [← hcancel, hL]
    rw [hmul]
    ring
  have hFstar_cd : ContDiffOn ℝ k (Work.Elliptic.Fstar Ψ) (Set.Ioi (0 : ℝ)) := by
    have hG : ContDiffOn ℝ k (Work.Elliptic.Gsing α F) (Set.Ioi (0 : ℝ)) :=
      (Work.FTS.EllipticEst.Cores.DiagEstEllT.honest_Gsing_cDiff hα hα1 hk h).1 k (by omega)
    have hG' : ContDiffOn ℝ k (fun z => -(4 / 15) * Work.Elliptic.Gsing α F z)
        (Set.Ioi (0 : ℝ)) := contDiffOn_const.mul hG
    refine hG'.congr (fun z hz => ?_)
    have h1 := hgs z hz
    linarith
  -- ### the two layers are `C^k` and honestly in `ℋ^k`
  have hmemFstarSin : Work.Spaces.HkMem α k
      (fun z θ => Work.Elliptic.Fstar Ψ z * Real.sin (2 * θ)) :=
    Work.FTS.EllipticEst.Cert.HkMem_Fstar_sin_open α k Ψ hα hα1 hΨso h.memPsi
  have hmemG : Work.Spaces.HkMem α k
      (fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ)) :=
    Work.FTS.EllipticEst.Cert.GbarLayer.layer_HkMem_target_of_smoothOpen α hα hα1 k F hFsm hFmem
  have hsm15 : ContDiffOn ℝ k
      (Function.uncurry (fun z θ => 15 * α * (Work.Elliptic.Fstar Ψ z * Real.sin (2 * θ))))
      Work.FTS.EllipticEst.Q0 :=
    (contDiffOn_const.mul (radial_sin_contDiffOn hFstar_cd)).congr (fun p _ => rfl)
  have hsm4 : ContDiffOn ℝ k
      (Function.uncurry (fun z θ => 4 * α * (Work.Elliptic.Gbar α F z * Real.sin (2 * θ))))
      Work.FTS.EllipticEst.Q0 :=
    (contDiffOn_const.mul (radial_sin_contDiffOn (hGbar_sm k le_rfl))).congr (fun p _ => rfl)
  have hmem15 : Work.Spaces.HkMem α k
      (fun z θ => 15 * α * (Work.Elliptic.Fstar Ψ z * Real.sin (2 * θ))) :=
    Work.FTS.LocData.HkMem_const_mul α k (15 * α) hmemFstarSin
  have hmem4 : Work.Spaces.HkMem α k
      (fun z θ => 4 * α * (Work.Elliptic.Gbar α F z * Real.sin (2 * θ))) :=
    Work.FTS.LocData.HkMem_const_mul α k (4 * α) hmemG
  have hmemL12sin : Work.Spaces.HkMem α k
      (fun z θ => Work.Elliptic.L12 F z * Real.sin (2 * θ)) :=
    Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α k
      (HkMem_add_of_contDiffOn_le α k hsm15 hsm4 hmem15 hmem4)
      (fun z hz θ _ => by
        rw [hL12id z hz]
        ring)
  -- ### the sum with `∂_θ²Ψ` and the transfer to `∂_θ²Ξ`
  have hmemDiv : Work.Spaces.HkMem α k
      (fun z θ => (1 / α) * (Work.Elliptic.L12 F z * Real.sin (2 * θ))) :=
    Work.FTS.LocData.HkMem_const_mul α k (1 / α) hmemL12sin
  have hsmDiv : ContDiffOn ℝ k
      (Function.uncurry (fun z θ => (1 / α) * (Work.Elliptic.L12 F z * Real.sin (2 * θ))))
      Work.FTS.EllipticEst.Q0 :=
    (contDiffOn_const.mul (radial_sin_contDiffOn hL12sm)).congr (fun p _ => rfl)
  have hsmΨpth2 : ContDiffOn ℝ k (Function.uncurry (Work.Spaces.pthIter 2 Ψ))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.RPFresh.contDiffOn_uncurry_of_smoothOpen
      (Work.FTS.EllipticEst.RPFresh.smoothOpen_pthIter hΨso 2) k
  have hmemSum : Work.Spaces.HkMem α k (fun z θ => Work.Spaces.pthIter 2 Ψ z θ
      + (1 / α) * (Work.Elliptic.L12 F z * Real.sin (2 * θ))) :=
    HkMem_add_of_contDiffOn_le α k hsmΨpth2 hsmDiv h.memDth2 hmemDiv
  refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α k hmemSum (fun z hz θ hθ => ?_)
  exact (pthIter2_EllResid_eq_fts k hk α F Ψ hα hα1 h z θ hz hθ.1 hθ.2).symm

end Work.FTS.EllipticEst.Cores.AlphaRateEstEllT
